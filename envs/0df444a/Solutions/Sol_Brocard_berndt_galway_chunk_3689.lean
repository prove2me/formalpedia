-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3689
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T10:23:33.319057+00:00
-- url     : https://prove2.me/submissions/e48fb6d1-01c8-4932-a20a-6c399fde9ad3

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 663309352 ≤ n < 663489208 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 663310602 1250 663309352 663309401
    0x3080705060108031303080a0201060b040603140702120a030203060a030f140c09041a0a1e020d1b022503060c0f08060d21030207050105040609051606140328 69
    0x110440d00a5440940303920b04180c06c0d900c0c3d4804130781c400d80b10071017550769611001410502c40400f03040200302a843c001131441c0151035502040000070710040841d04111000d190110a40059070b2100c1c0051400603240d81c5c404001c500074580c203400c040d00d10008244240200310740c481c08410304100d00e0b010b6a200c030b2050810b02c10703d100d0a80c0c0040548100c00841c40c3d60030084111144d000103aa0340c00304207200041c03181d148982c1c00000496805800007941014654030740103061911560001c10701020184880094071a40c0d00020001041061109901e0000075002441c0155820003420812100b180001800302c40303003a400700001c5528940011018a400501e64820503001220145104c85003c49444120361000b504014103501b4030210010440034814244903e1058030006400e2800f802c15920b42407074500041d0300440f4410043c0219944807840603d00d0b02e003114441d0726602c40045a91082d00000e03902c00804403801c909103d8413500e500030084002401c071852810320303070 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 663311852 1250 663310602 663310619
    0x20c030715060806131a04051b0604140d031709011a010509130b0d0f060b010e0607050c060913052e260309120105040b010f050f10020313030807050601 67
    0xb1520607001c140d0088000101080000318640034080e00c504802000e00c5401e40c050503800c14140c7d82620994040035a02c91614101d4002c049134a6048540d07034141458190520024007065001501070030701e840c4480c0406024105100f103624050403011858034009102c28000c1c5241d21613090741040b4240540602e5000f0742c112050301001406540d2611480058880501004c45025421000c460710001c0420518140c3d60b01d075601c43e904c0441c0d4440c0100004050552800e0070038443d10f8104503480010b480011000d940c0c170015107881c0c1e111212030b0001015450b18891544126080c01d0401442150052b082d4002e464804000440c50500342c0e4452044652805110980e00c0650610400c07100100c01c0d010480481c0b000b1a4a00400c80d030204040d01d4031055403516036916241404100111030b00701c54050a59500c0c0060040d140400095401c0c0103140e0300b900500c42c001400c0c13410781c42441180e084000f90001502029a00d1504004039801540147c4540c010135001044102 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 663313102 1250 663311852 663311861
    0x3020705070608010b0d0b1504060908010e0606060712021603140f16090911060a0f020c18010e04151d19030e150c060a0f0c030c090b090d0204020c030715 68
    0x14901c0c001c0d9030800300c03101c0c20a8001c150180500d6480080d603203020000236031090090000d04074646d5501c40030783c94214503e007566188a05000641c001008004154445000b50f0700c0c0960002090782183c110703180141c1c1001013044590300150400380010050040f1001e450b4031601c0108200c4260340713140e80e42561254213950003007145480360a0200300610702d0350020504a40107c1183d0720300106040050312541c00000603030701203290b8020f008606501030000c0b4024030410303038005005007841d000601c90032105001d0382800e0440f4a002c10140a4850302d0340384128a550000c01c00310f604998401286096a0b0165000744564960580c1002c03103042290b44096040c2c882040c011802401c11544101219100703c030404148002e038160601003101c01e019003104c2c04009010f10080800f1000e40310a0b02e220f10a05040010b680c50280c0c6c4210548100c0307654002294031800075000242802c41c800001940c024000308004200e018003100409425102c0c18094112107800070444040e01c = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 663314352 1250 663313102 663313109
    0x15020c010c03080c0a050d050a0501051c0f03050c010e160f050607050d11100504060501030b06010203120a020309010b060f13080d0207030206031806040c0305071d010506090f0d030302070507060801 87
    0x54100f10204244c040d1500240207280c45504165081c04c1070003007804200c800495106500d141c8520040025040c05161a80c8851030b1138281005109030b0f86950041b80f400b050018208000002d8144a110080d8807000384810000c2c25a0440244083c06104050703140c01815100140064001201c1c60000d08031900329138050081d01c45035082150a07944400c00d826003d05501580030f105031004040d01c074071440b40e886201700040c0ea5042d41040c001400c001090f050565100700030303070161745050521281c0d009081a0015035240d491000d10f83c050304c071280f0090340105022413106000c520341406080640c1e000c400c4404a242e64090007030396500e00007103150141e00415000d0008d801d02d40b004560095034541d25480910308191600d02e0200120b80981d00c0720703001c0d0011b00800000f800090014061144008541000540294070030541031103094400c4500003130344580c9440d600344c040b01070900100064a055924140a0080c2d071201c51704036002c1c01411404580180104841e6040c0d = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 663315602 1250 663314352 663314357
    0x6100807050a17010b0a090906050705030408121008030703090e0702010908030f061c1110020309010207260601060f09080a171b030f0904060f120305130f15020c010c03 74
    0x9180f0340001c03402595100380319034003255250003000e80c05403150b41c0c2c000700800050000241404e41801c20508641e000b40c01d075000c01400b00140400b09640301d0603640d00558031541d1091546a40519540e040001d80c413400150102041d44828160061143c50486011480c1101c0e140c0d1131040c200c2c203d9840d03400080c0050720034004900e0f0a50346104880d40200007030f040740b040d90b210b4000c140c400050003004540d6030a414207000c1d07990030074442c4180e1440e220f0004504251103000040d4850f1018042c90500d00100b8440c054140c8600000030400300000c008c0d14465610f4807401009140e0702541103001c1800c4010008480d000040e001450035002240c0900c0c00540d41000c4180c0d91041c1241700c0c40002140c03002c19001c2080c4018680c5460007488195214059001d00065808640c08050f02e00307065881080840310364000049002c1d8980381c542c0c1d407144500d454008528417600b201c40c1e98440c445020a60144220221101104580844140b005000b004441c01d01d03480800800 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 663316852 1250 663315602 663315619
    0xc020c010801080a1a0a11120a0c1706040903020a08070c05030f0f070b03040f020a060f1202090321040e070509040e010c0f0323100905090d0c120e060c0610080705 72
    0x903121501c682c10080740c0901240c146511800c91907d42c026403680c456019003a000d1000590482c0305240b0101d070941402144580d14401c0488000401065940590340300c0e101c0c8410548288100002a5848000c103034a864480c100003009038501e000e40342c082c1c4140c03c01c41a82500008010404040801c024041581090001d209a800140c000c4460004060807940103a8402c16070001070601507980469170309144c0002450f4031400321003142d00d14030401511540e070f1408123802d003c000c0c1c4001d000003901d4030003900000d5403296904c100162440710b030a002c00310b41d1000003446409000c81e418001600c81503159401c03a03810305011000b01d80c9041800c1d03020341c003a0f0003032988405859801d00c100903020000c00035041040710070400081146c1403c0c80001040c0c03203181d03048852840144159111150041c11146030404003034004000b00c58420415807140c4114030001e4400b071301250310b4100842d880c5070b50300000c1d00c0c0400305500000010419010015100c012290000c004c01d9 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 663318102 1250 663316852 663316883
    0xc0605010905060f45070305150604050d080a05090d03080105090604050f1503011d060a1401030804030b040f060c020c01030b010e0d0f060b12151b040b0a02010f0c020c010801080a 79
    0x405e40100540030300d0341400c1500700181001d80580641c2d00c1740300715440100c2c40303142803a620311901c4030030032200388111000d00c8240034a4440201c00e10075554088070b000d90b2010070080907074480c0100b0b1481c6a020b00a070302d042e0b040660080485040303480a84040700c01c0d8848208000903500d044900700c44041034080000d1240c8091601518201c0025000207002c0f40e4182c413400201e03141a1034140c01d42d02640c24003400480702c1c811071a0504603490b0b0a011035041d503403401c0d07440c819844050140301b005030200c2d0a11600704644010240d112000b005800180e0501035250071400d07591a001c20f250551803c42d40d4000d03802d0740c5000340014071003840611982c0d98002034042c0e25000792003c42c4d858200d94201e80f110044049195652001000350107400030394210512070007408a4026a40402c20b008055811020344060b034040000d00d50b00d507131160000f240100704040c0c0d02d0210324240310000d03080e1600455503142c00348081c0da0707a40700c82c1e0300d074106682d44d100600c80041008600d140040d = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 663319352 1250 663318102 663318169
    0x90501150c2d020f0406060806190b030709031e03020705012a050a0c0807080303130f020a140f0307081e0f030a02010f05130302100c0c0605010905060f 67
    0x200c024402c2a81000080c45001c50410740c0c0c5550000040394680c014200e000d6180200c2040c1003c1e004550030300009050180c010208203010b80894018169440f00c0c00600c1205984440500030380ba81841d1a4500103074000c003030565611040d81c40364018501520311a440740104c0c82c1040c0c25400400c811445d003001103605403201410341d40d0000980210502c0c420303c05a6103400b080c010002000c51084a04041145204039031001b030b40d42c0d0025004000d402d0021041c0c9a08c00700d002c003520b1440f0407a09141002b0b10903c58000c1d0300044c0398401180c40040d4940810b05408181c5d0318007050b4012100341945c0e0001402100e0281c0d0105a4040c582000010002d00c100c00c3c500545110800d199086071450304900c2181340035035141d5041d41d01444c454442d6139400421010101d0b0802001d85020307440703d40307021410030b80c1034450880030703160380c02040004441d60b48035904105560350f4a1150005003401c3e208280304050b8100036a925150022524409085903038245042c400c3c401d030071 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 663320602 1250 663319352 663319367
    0x3031b070c030803072607180e070e0a0b0a0320070f02060702030f070303080601031a010c030c110307090b030d0314011e0b070503090301150b0d0e0c04060611010609050115 76
    0x181006c0022256807450199980e0381c842d580c040240d8154605814400009492400c000c40803403010043e6045c1044400f20000c0d2183c0c01c602182080c0c2403a50a400c04654035000c183c2100c05403040004050b40d00651651051404c202d8064601d020116010040f91080c41000e0020b0500f0b00780030311210140c540f00b0000c1c2160f91000341100d602c201408003150600c03445a1080c0c0200b820705041085558140c082c5162201d80386075103500a41c40e80c5d0000c0c2203c441848007404116122440d8000c000b161070b107075417000710000c00300c60364580c3d520060000342042400b000e0203805110910408140240280140780f41843c43c00c807503a0b070074800b140303204401c448924018950300d51000607801506000815805028001469403200750b0700c14142918019030545a0090000740208038000400059900c107208070000443c03940360b61806649000c414040d055070251030202d00282140c0c0220880d800018031600a010107960380c000541221f80074420703200300015401d4198201482041d1 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 663321852 1250 663320602 663320611
    0x50406050c0f0601060f17070f0302030403110f03070317150d05010f052409010b1605012003011d09030a03111b031c020c1504080f070503031b070c030803 68
    0x2150b4030048100700151a240003a44590089800c0d00810681d00d80e01005075850221040003a45403401c0c203201c01800204561524001c03d903010011a040500c506144101c5420074401ca03401000c5500116443c1d620800c8120007140d44825401c00c00707204800303100e11840a0000505404ea40c0d0310a01003082c4c0c4000c0111351f25541c805205881212911030140142c0444440000030b0594860080c4a188041d560f180302e586070744010450f9040c0442222296041c6d495001c141d0000c2c2d02e440c9026020088000310202550440f02d062402c800340514101c9400060a1072501140c1d0014405c0710420f40b8411310070b0f00200300318a0000c1c0281c210308181c4049000c80c500c2c1c60740203901c890301240214811f244a810001b0441d84014144028404100c1d03041e00441c5040781000d041a519016866510b044240ba0b40010782449440c0040c0c0d00110081003145585085074a05592a6841119090107482042c0c006982000c0c40005031809103030700041861166056454034600ca800090 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 663323102 1250 663321852 663321877
    0x20c0108041106030408070b07020304030213090b0403140d0221011502070501031a060c160b0f040504050402010e1c050d09050306190f02040605070c090203280212090c090a02030705040605 83
    0x1291000043c8e008080300c3c03003050356a01440c2c80d14114410845850240101b070101d1f1800c0c01c03400c0c40840c81e240e001541065040c2011030400000ba45071400314022820381d01411480442d01454111070448504045043d402c8486180d03030301c415030100503000090500c001a402000c084c8605d50007603102500d0350320382c0c01c0342501108a0000040b90b50344012000903083d0000c48030070400d042c00da40c080c8084c08031140e281e424030081004c540310b0740c0074a04c5224070503621140800e0559005400740280c00b02d01034040b00320f0740311034a503101d8207071001074086500c2d1048403031b0181050f01c509050001d850008000d07003425140c1340d0600c1d86048109281e05e00c165039801030011060502d20080c030052245894450f1140c03040c1c1407a0025003119031044c90498010000c106041025001200051840168080c0264081c02042c0d00078007440003000c2130100c800d03051201d02580001d000480c0407003124815419a14071443c1d1040c0d00040d0b40a02c0410740510080c05268000e1f00a04000203940 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 663324352 1250 663323102 663323107
    0x1509020609100c0c080d051804020f040f03050f011404031d0910091b020d0810180b030d030c0e1c0b0a1e0c0903110f040615020c0108041106030408 65
    0x30703400e0b8564640c51001c0f503100d080203410003500f44521001000c0d1940a05031034000d440014109200d8081a86040c1220700180b440325a582d50581c0c80e01c0b01401c00c12500c540c2c603124913400b8824680410303503951103108010004290305003e0901420000074058840ba1240e036410f481c41010700d003101d00010f000880d03035a2680c6581003010300c0b8203042c182c1d42101e00e03c0c028040d0b080b1049030208a20038ad4443e0140c0b4101c42d0001110000b6612900d00301e02c3d01e640c1c842c803422040a03103400481e2100d0ba000034800d0700c031049030015003081c2001c03070507102001c600c54015400c55128092480109510055031101072400c842c1c00001000030b80b090021001031170382d400020480441d0100d840030740c0c0d01565035001450b094690203441e154617042001105109010380700c9201c9100052003503130403051100c25604c8540442022000c0580b007444100e0b00c0759181d4003850b01c0240d0380c00061150111109141d80b04000d0f5034080c50300080c1c03101818001600740803003944010015034611208 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 663325602 1250 663324352 663324367
    0x150b0708120403031d0f0703030522030c0302040e06150f0a0512010e06010b0a140307050c0a050708300306191e2c1f030f06050f010315090206 63
    0x1c000100e100314401c1d50300081030b06141803220400b0046243c041080d84c1304010460302850f0000e1100107a903010309100d600c030140c14001049900310b142154050105403c800810480b81901807000c0c0c038400c9505002c0314110011881c0d880c50126100606030030b0703d0240d407a083c182a102d4809664002c2c0c4441d02894444000c01e00003200550f0b10f809a80d0742d82d2441441480c01c1c85418098002054640d2408900c81002440e00c001c24001d0010101c000000c01c42ca14001d0701241c02c0386048209130340780c81d020350610a271503070b070a441850860300642e00c0682540354009103031480c140700b50502002c01900542e03903003010b81000308403641143c84043c44104020440444034003e00c04a06c01d0700c2120940c022000003c00113134030001c0821078450151424854188000640c00124000c1c00e000369a07005607003007080c007000c005094258134400d001c42400303105401d2400c070038010071003800a030303c51202011100c9024440a80801a0521091005c9101d9045042c090340010005401c011a = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 663326852 1250 663325602 663325627
    0x90602090303042304060e0a0f091707030207050306090307081606110304030f0305060d03030e0a08041508241e1801050306060d021f03060e130213150b0708 69
    0x15044203104d070980802c405100052480107000007801030341d0901815240248201c03815201070203000105417665201c16211889078494500c00740c01240c8088802a1151075078420740c009241a8018096644082402e00707000075034a026403061002903180c02d03210344031030025800401090034600e11aa01c01c4010803c036010780e007401135020f00780c260341c3c0c280351402800344000d084444091504040030443c4039500d88145461440c1c00d03080200f1380d8072a01048c4d03420301c40c090000800d150404580810382c0c0c04505501c0c101e8050b5910ac001341520b07100e4210701841c418030b10355162202030804180031820b00c03030300030b0710100c00048410f401c040c2e4960000b401e00685c4446d016151925034010403283c5404c201d20b0350801e400b50790f1000d0602a50b008900800d848605048209906140640c803041c841c1d8031020046c050a0703100f501038144665092154100303918103078403400b68242189201c041c030344a03014122101032010002545003021210290b041500d050300c7c10002488100e15144 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 663328102 1250 663326852 663326857
    0x50c0703030519020a03170a0912030e160506031b0c03040b030f130b010e180a05010b030c010801061b08070b07020c120d0c0809041506050901120c12090602090303 72
    0x5101c1d4681c00d4581d02555107010b02c920030b80344a001107600039003400010a42060240b81504e050421040e81d56480070034000c044e045078070000f400742e0080070340d4440d803c2d030503030014500d81c103800c065914024150084000e03411540c010594805401c1010170405810a1740070b050000c1c00d40c1215040503030140d9181e0a54016911030200c1c03403800010005021a48000141e0151224a09441050039902c900d9007000050040001840302e440100340441c903407000003580c0350500000c0b10000c2030b103490450301a14011500f83c1c003911034201560740d650f018081c1076058401715941d00c01010fa0200b03180640f0b0304900d41c1512503d0341040480702007503504881502c2007010b034006004014981d001d1190865851804260b0350704180c51084496a10202c0303514400e0704008225240d864000c0000e000308075a801c1ba040340008183c0c0054280d40143c040c1c10038103005d0302c414104240d9402e89400703031090ad801e58000181504d170310030341d4a0035036031140c284c10f4005d4100504261000010a2440c1d = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 663329352 1250 663328102 663328109
    0x303090c03080a0327060504230f0705010c0503180118060509091f0e0a06050307080d03110918090f0106062c090103081c09140f01061503020703050c07 67
    0x182e80000d10700c0c0425007500a20702050019010040c012a1150301c00001680400c00102415141e02c04034017409000d400b000c0140c121140d0310088a07030102e840c66038a2942c0117000c11a4054000000f40c41d6000b44c02c4445500c0c0c11001031031500d1041c21042441e0240c5c0d14085050020803d80c02461401070710800e80a406582c68050b40d8a175160f00300301070031100503c080038101859403030384a0701d000c82c83c01c0b00440d00c10054038096615403c10580160030103030051760b018803914a001491210000d02254507101c107403001c1200120b6841140080c2c402e50702c2e00d6800400d8110440f0341c2c010242031455010407800151991f001c80d1000d507509403480b0790300000000e10412000c0319680100042c8424034a0090181e20141150101080b1f0391081440007500030480070412001a00103c841c40409141310302c0100060a100c0c940031080040d2080d0a200038420200d003c4107083d0148500410f8820b00d1480a80400c01c10004402a500c0400107e0812406203c40102d500e82080801d000c0d = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 663330602 1250 663329352 663329363
    0x80103140f0a080c010b030703150b04091b0f060e0619030207061b09080102120708041401020c01022a1b03030706153611070b1306180b0f040303090c03 67
    0x143d10130712102c40e080d00d03640050140319070040750b8208001040f0510001c5209040d0b070707001c141c518103003001400408843d80f001d00b20512a07008500440c00e40c0d04500d098581e58050018402d480314000c03950744100820321500035004200606c5003800c00c080508110a0920b0058135200040e035446080d80c0b1011040482d0294480081141c83e03041120813025001e450021424032521032400701030080301030845424040300346e02103018418140003030748290354000000d5550b10248070f8964000d40c4042c4041010340b003d04859050140c0c000104142c80018000402e009a400742c00324403510b041c40c1e45140d262000b0010300c1c0c0066490300a003d02280c4501e00070021a180016014440c41d1618840c10b0075165044103404800074180c003500b450a241d0720015445c001500e4040d1680325659014040b58100c0701002580b008071200c0c2e4040a00c15602230101c035902c044013030b1a511010000400130443c02000600208860f0020f81d8003d000c1d2130003240301403e81d2241002444241c005862 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 663331852 1250 663330602 663330607
    0x6041d010611030a2c0a0b1818070e04291f0c1122020304110108130323040b070c050d030912050c040c020102090108090102030601080103140f0a08 65
    0x49422900c01e00c100c0b40e8180c0550301e404c088480c0280446140b04480c0782d195048500c8041d2007000659004039100301800030240e0646500c2c80104a4004070b110070118109020810801e0070041c4149240b001044081d8000b5210350200b0b5540726000b1101e250855075507003100040514079900e80c40c0b40d82c0002c04001440118109112803410060380d00d10740c1c481c0807080591700c2da030300503001d111041e00b0080c0306520f0806180011450309400114240040141e003103500e640455038000c60082d03105c0c91184030b9030800707800150f900075000c031102c030365500c0d1050a001c04240203560146107441c100507003100a4801c800b601b035454000f0303040044a002c02103595001c12401d00c00c407a019040485146c140c0021540d40185201e0480c0111001c640146040f0000c003c0104495140540010b0050211072001c65000703000b500071000343e500060700394021540004d018400c690003041c0603074807160103a00b1611805480241c00414441b54420b0703c80484546400340200080c551040700040d6 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 663333102 1250 663331852 663331859
    0x180426160501060b1602010c030329130c0503010b0a0201020f040920031005060a0e0307060f0f03020f0703050c0f010c0503250e0f030c060c0102131e03020f06041d01 73
    0x2400c40b840d0381c04c203a1140508004c806100b225848000900c0b550910386a00c411005107000c5000d809001c030800301d01c85104c021031401c201c0346405c4400400060b1180802a416000b00206864107000d203c400725808000502100200c400200403c0420340009490185115034410556129600c40c41b0810b544070340134141034600440301030409480f5031786941142003800150751601d9042c46030500c101000a942d0116900680381e588000030000c0c151070381c8540c0c0b481e01030f29144a2403100300000f030b41c2c4170714a4002d600a2094407500354030317806480d081c00580d075001c3d50158485001051030744212603070b9405c8403009001d4001c52160607680d440e12414941400301c030b00c0c0071942203e07030410016009000d28a920a04118058004403504503e01e24000040390400c0b00b2070350b60039003003540016a5601c2010540003000c0b903808c0c0c0c3e161040074036954030000100c01024072861401a00358001000540740001072521404001068585026039940b268940d5000301c01e00e094000c4070420040 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 663334352 1250 663333102 663333113
    0x90a0317040b0f19110d0c170304060b040e0d02120307050705070605130f0305100510170c0f0d02060a080406110403120f0f0e0409080405191418042616 67
    0x14680c290304000c051500d4191005883c0d00c104280382e030030131420407182c0c000e22000e504108c103101981a4215a68202818103c6c050000c0c140300c2da0045051640e051340d071240000d5910b40b01003c543c0903009514a0451382c4200c2d0380b0250583c01002800d0000c400460303402d00110000304802d40f0f4640d070710580d03040000c100014a500150008010301020004158081081100500803010002c1c6070756485c505518121066040b9a1407050041010000140300140504400c04220750038044416007400700200c0f02c1d843d20000b5003001d0300307001600165024106054015100b80400705a001c481d448003545a0032603030041c1d9030403c0742032022042581001740d9800c54085882c101101680150700070b40341303400b42030290740155560741c00d9409100c0c6080c16503003e03110040c20a20070005120741c0350f404481350700482c03100113030070380901c4000d2400ea40f0a4142c086003041c07128080e56035440707030300b1f002d20541c02483c51103031180611425800301e50020203002c0d500c0702022481e007800f401c10 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 663335602 1250 663334352 663334387
    0x90f0601091109010516060f1e0912050f04090c08010302090702060907120804050a03030c020901080a03020a1103150420040e0304030602030709030816021302090a0317040b0f 77
    0x200546440c280180750b503200000c660030643d0030f00304540d64503d81c103540e5a1000c80500d000d081c9510305000201d03c03804035004000005100b240c030188410405070755100701c0d00030840c014000000030705550881030080c2d0191007566031850f1040d040980d04c0b580e08066403041c580781000200b108005104600c1d00004494100295100a00c400e2428441c9e00382c2c1c030042c81c028140e00c8400703c004201041180c008940142c0009040309040740c3c0e503850098020f0482c6503080f80b103528000300100f00c402e000030700c08584641641c000d01102c10f16880d0042000d80342c80e10141c05014800445142000c440840c5000e81c0c491200030404544c2002c0c100e007040e01030141944610f04050725036071000000410780341601d40043c0300581d01d444452080e9040c4126500c003c204150224920903120074500000010300d000340d0742d200d00d0a42402c0c1c41c2e002ca1045050050713100030404001c0c030105041c8486401107100301204207103010745545071007500d600580030103450b607003000484d000241820040d = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 663336852 1250 663335602 663335609
    0x3010e0103062306152206020106080a17030402040204052d030f030301150e09040606091425021213050406080a021302030a060b0a08100605031e04050c09090f0601 72
    0x381441c1c0102c00c00c009045640548668440d440500c400f01e9505c1004080383c44410304444080c00c6004801818021031460f84204005940303401c8002848000c0031800c2103000e507019000d408411b142a0009076141c102403c00e070b030465424000800c003038407141000c034001c409280700c4100d04540d080b01d81c10000900d8100c14001c0d048004680c1501a0000c15030f415910030030380641c0c641c0304c80f40c0201c4403a5024101c60303034007080002c00e21060081c584d00a030706441210b00140460b0001f0300c2c9000001c0070545212600e038030460000c61810b41d08c848044001700c00340c419506003002c12030304140c5542100d000f915031444106010003062a2603c1340304014030104010b05180d01c003c0d000582c4002c1562188a08030f50008001410000c0b42e030710000c00341080b40c00d815150051840c00900142e01201e03401881e09080764081040c90003101030300c2c4140c2c0701c603d400070302d40f8000c014600c0c0702d02c001d401114280320780444d43c2000d6440081e49803003034200c40020001d4012125802e460a14103a0 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 663338102 1250 663336852 663336881
    0x1140a06060903020906180f010f0b040b04360e0f06040314181005191805191a0316080f040201030b1810050f040e1b120303010e010306 60
    0x450070003005400c000c03a4800c89404440e402c4040c0c0da6100420040482c0d801d00d142c4032140d0300708000c619007812007498180c03100404c0b0034074015240c5070030086600c128000c10141d1041404108002251050b0584100780c00f00145060407554904014141d21001d415104681d240c4c0001402108204051014030100500074034050a2a44000c0c0c5004c260642c0140700060000d044881e2644208030031010400141c02c04406041000300207250342c01039252005c00b5400880700d0301e0203600c0b804158003d07044180210181c2032038041003010501400009500c500541c200c0041c0412104041c486030320b411013500350780c1c4d16218940c2c200100324a82d180c000d0115041c10703c600c00815001440d4002d9083c2000a0b44800d1030340040e1482c0103100b11034510500c60010061001211440801213030000d680354000300581720100801d80718007900700e02240e031140440710300d8003500044005c00c101c0080c01040b44914031041450441d80300340c005800c13401d1414010000c0101a108910314080c0300c0 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 663339352 1250 663338102 663338111
    0x4120f26044b15020c15070206040c050d110108092b03181a0403050c0604050109140d051e0405060706050601020d0311071211010c02011a0102060108030a0f050d0c0201140a 76
    0x30b81d6140103451250085440141c1c4c0400c00c00b0030941d00b08100040850111034070070440c03801e010001d5480400302c4046a110801e40f10000d1b450600d4280d42a8003540a040c0340d0380c20000070011100100b0050050405d03220b154040380314480072043c00500c8501e68802514410546030300039007030f604001d4402001c030320540181c40c007143e401d04002c681030300c201030601641d03110760608580b68002e10455800a020341c03c01d10041001c1544120b2015206d286c4981c203040b51002402d494150a5a10201180040003071008130036440d100012034107403ea49050600da110303c007103006c41c1c00084044418648d6a070078880e00350307010085507009044d10b20b4144500c60100c08403211a02400600908038103143c51804401c0f03008074030f600048484200200130547c081a0000c0c0602414070100001c03005920501080e5403011513030b01d050b5840c14008600d41486014112108151100c80404208051060165110b1a40034082c0b1003491640045240c0e48145804012443d0242c103108985260 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 663340602 1250 663339352 663339503
    0x9091011040f0f0e0a090309030c0e0907240e031c080103052b0e0f040e010207060e061614040b0703092d050f0a09020304120f2604 58
    0x1c41c4c40280e889410244082081c41c3c0d203140681351031000f80c000400d00c11881d8000b00d03c840c07001c0c80d654800c030075410848880641d03481440b0b600c41c1905003440c2498410f6280b02d44000e0081c4060328101101904492402a90320302045503141040718400006070010700400901408000400540781c0200c03950b60f2841c21074031190300c042c440c3e0207003c0038000b00d20240349050761024080c0940400150091106904205100d4000c1d4045074048560510702010b40d0a00b0400040c124841e40c030794103101e211550100e8059915003d09a03c03030000035002c21010524200c04405060310307612039180e50700321a061441441d40d4030b0940c10900d49905030100c101050a40003d00c10003103031800d45001000c6410a070100e00322264580010a0f0a8000030070b004c02c00c004489080b101d81965601c1c21810300d01e996080b62519400c4441c20f0664081000095000010981d50381c0c000d032107075081c2c810345c2040c403036000001d03908164105005075403401c0c90b942d0000d5605000030070012040c05101c80c502c8 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 663341852 1250 663340602 663340619
    0xc0e07020703170d05091f06140603040215190f0509090403050309070801140402031510211a0417041a1b0f0c0103110703020a0209091011040f0f 64
    0xd05200180000e020045034040e4020b483c41280c0c4094034668050040d854103402e100d41d51008440507080c1d0f0000a642d0345a20596441400103490710b51112045160780141004020780018100380c1c4d00200609400944801800051106820141d4120a08030901402a02d120b1682d84200c0510508000c0d0001c0d680e10180440e44c4603900d818500e40300d4450f01c1046140401c10740150341c56610384221680a811a0810144a00d20031411140c000200c0ea9108a00301c005030380444250100c850b00b800324403491a01410702c8044550308902d01038003070301e84110300d00004140f0400c03030080a00340010b014000142684001800741001d18152506c40510b4110340600001c04001c0300100b042c19a11000081c1807075218200c3c2c0031030780718004a040311604c40305a1409680424641511104011352003405d8402013901070300035140d91142c0d502408040000240b5200c40f50013101d285d082881c8a43c481c0d403080300003902c0c4e80c03910395040c024014054005071b0031805c40c0380c813240b0b0200003a54 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 663343102 1250 663341852 663341863
    0x60918010317040b1605010b060408011406061606090f080d0906060b09010c0311190302061801060e0c03060a030c080a060b040506030a030c060f1e0b010903112b0b040c0e0702 77
    0x17108240040b80d40c00c0c90411500428460000c039602c030200103800107580c039054224004400210b00105141c1e1030f5481040198403d01130b4a86030000000b40c040040b0360707660700110045014124104030703c0b40381d5a81c509191f01c520160225143d0b00e0740200c0902c071580c4200c4001e084014001031501825130000b0305041c680160007070070400c10805d0f1101b000410301c81c600c0100c01c580c8109241ca1000c1c90b01a454090031241041c0c1c0c2c090302c43c00d601d0440030501504003110b0310001d110085413280c505c00f030056071000300480c2e0884c3c0e021000000040380b107038008004102c0d40001c0c0035010760529284d03042c3c80c00110410f03c900e042c0341c107101c4190b8002c01c5402540740d0500b40721541d40390728540240604981d40003400c480d850692220610704801826014419070031000700400038880f401901d8070f031010300010b4441700d40085400d90303505041c18526407503a0810b40c19004c41c0c0f0b8811143d18060b611000864081c504101071208224148802501511503504107042620746400000d607640c = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 663344352 1250 663343102 663343117
    0x3120305090d120902280e09030915370207090b060405010f2c01080a1406040f0209040603061a0a06080705210f0402030d0e0a050609060918010317040b 67
    0x280d0340c0d206801159550444c881b411402ea01140420311300e11307861803414400c40e2040801044102002400d00c0c10302100311080008020106e00540c00c501081a1160300108114203980000380811031021046203503108040309112090816040f0a5500070300340641a40326202c041e040071327072030b81c025a0b0307410030b85064400070300e00240d0316014020210b0b091403d4501a0680c0c940141041d00c0b03038140306c20f801c40101c0082e2100d0b02c0d0781c9c40320300c8031404840107030381d09450340c89001c00441c64a01d07241c0c00000e402d0030758110140c01e140d44200044d04aa411303500c21100c2c5a5204d03012803242c3c450607400d050010044900044480ca040c4001e0b0110701c1c020700302c0040100010700d000100d030b01c2d03e00004941041080941a62034684090b541d80308080e20164481e1048440304120203100359034090b004000640410340f55840c04040c0106600b058175816800901032000807161746800306900c200d414010389115041d451070900000200d810702c0503410050b0300b001306005103040700003240c014 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 663345602 1250 663344352 663344387
    0x405060d020f0c0307030e120a061a040204060203030118020a080705071502030702150a0b010c02130905011b090605070308060913120509010e03070509181603120305090d 75
    0xd9a0052000c00300034414a100311a6004022400380d80281d00040a0f201942c401e44402c000e100040040211280362030485840d42e600ca00c3e43c2d08006040c0740c206a142c1c50141e104c02403d48980750010702a40c02c150417000040e030001c00104100d580540e4400300e401c0390418218034000f8100d00041541703500070190801c0c0000000c4050402148250059000c11010701c215200d0512a10080d1120b110151804031200c0d150302050a140c80c0e0f10506030041d205844131034910002ea0b0034401e2103d07070040e101d8005980c0e421101c0100f0000c1c0507403456503041e032085090354466031201034000c0d03000d034110404104003400b007140040c0d00000b425420001c00c03106042941d4980509000c400c880c0c0d00020040000401d10740b1109421001425860400341c85244c2c10840341c005055507508103224055028007000085220500705080d2005000007000035241240c00d085d42d4042c0c1ca11680c0e01c1250500411168410100e51622503103402145900143c54001d01d41c00c0000e10011518880b0180f = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 663346852 1250 663345602 663345607
    0x1b04141620010207030801290417030c06040303090203121e030c090a0e01140409020d0f08130f0501081e0114060c06130204381c0f0323040506 63
    0x581e6001c10440100003030344000941d80e4000a03c1d006202d145c0038032950100b0080503c858059a241c1c0000031051b008031090542414078002c1581d20b4420300440c188003d0204200764a40544c0501074507103d64081c0d01d000c96506124410f252401c81500e01500842c0d60510442820302402841841b4090100300034649a8403130700740c282120b100d1003018a43c820207220001898401603070156040b01c1c200c0d0960f90314107407440103100c20ba40420b180250311011403181400010082044800c81c3d03409541424204100d103404100c269000d5041100c1120043c0400c00081d80e000c001580c3c40015026030304c49100742c201c00580c0010b8107018510308a0501c1c04800d19548541064403110404001100c0e6075040c450a1060b014542d136800340e014500b45042d101d4420303a00b00304080f207004203500503554a02c10746d50300319100c064030305101d9120040010500308005039204020000740200e0282c4240c5c4e50784e02d0050250400d060365203281c95005d500c0c8800e40100c40c0265801c603002940c0340c56 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 663348102 1250 663346852 663346877
    0x906202809080d0f090603090b0606070807080c06010e101233020409111213081c020d0c020105010f060c05010f02270f220b031b041416 60
    0x651454082d00005850320a8645031a402079000300740810390b00b80f603180e1040c40f9884010803420b45941034400b40c0007a240b003001c00c815060040060084900440d05a42080d109640b480320a904c00c0c1640030385680810010f00002090700340494021500d00d041c003009519010f542c1010780c64408001e440b0380a034884000c2140e2072a112061811215441000140c5403d00d6003c0290060f000c0c0749152442c18183c0140307451500b04641c80a400c0403140c200ea0360310b40300c002002e12000a41103410100c148070500c04000c94441d03c0820711210003002d621994615500c0307040320802c00081c41107a0401004000d40603180c121601520103628100d188820203080441c00b510580268150762031000034a40806080240c001b0070704c4600804000e00e001c18074042122891000b2003095225130b01001080d8a504002d0185048039141440441c0c2c0260f04000203051403104a00940014281840d4461518251207941c901d0b48002d9445a001d003498280501904640b004000611840c551460f = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 663349352 1250 663348102 663348107
    0x1e120109020d0b060d061403070b04051011010c032405090606090103090c0f08121314040e0a06020d0608061b160b010306020706110a02120a1209062028 67
    0x1003c403e80081d1009503500c000e81196402403149104040e040c007003e4040b5030642c9004901c43c0b04a0301351034181c6090604100802401c2500449d000c0d061007000041c000340b0450070b00580300300300c1c0f140d10000703543c082104807412180050b20354400d16121803c414080d40d0389400540e600401d045d1030301d0b6101e44038400160024607000d640507022010315103002548100c96103070a03086c1c5100805580002802a030185641e0141e03c401c80d480220312241030010f04003500350441c41010003000400e540c00d051001900306000410142d6246400007440d450100c09402030300b00030141c1000402461400381240e1103a01040c041e0014500b00000d25030100f00003038941c860005410007104082c5594910b03081000390301c080da0403601d981c281164a00140c5031241904d00e41c40907030b0040c040407909200060019400350120383c0c00d1140e00c0c1e004c030725025050f1003801110303841418001007483d05580701000c50145529040c4072500d0802c100d01d801220134038030b041d007200111052181080b030140d05 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 663350602 1250 663349352 663349361
    0xa120908030403060603030e12060403142a0705010e06070b040203120f0c07120f0f082209050a2a0c0f06050402011707200703020d081e120109020d 65
    0x1840c4034407000ca008424080d00740d000408881c403c3c3c40301c00c040711400c0c00340b2569620403680203016030000d2000a000c28000d20340865a41520079140b46410011721340c201c0003600d074400b6142580118810705100c1041000250301400090914501c140718501c00942d1900c52a140140204c000e1004101192402c00c8203801c000b198003129a142c0b551511003940c1500520455025803140c0d80d40040c014421a0481000d00c0d0098652581400b00b41c844a9003806404800c886040b0104425040061010000114102c000b0800b030101c92a00501d0310940d0b4002c0c0a1440003454181c83e84002100740390841b1841c41d400440300380f40c900c0040d094030755002400c8003078000308012031100c0402000e82d2001d44100e1013600e807242c00f207145841000c10080304a40050205c0c21109038102041c0c20b260003807051440440807580c0322074a03640031882d001101c600413224010040f075000c007024a488030280d008198400106e0030070a90614100c403500c010700c80c0b110318030303400205a00005c040340c00 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 663351852 1250 663350602 663350609
    0xf090b13091a150a120c0806041802041e0501080d051e040806010e0402040e0a030e010c140313180b03030901080925060e030c09060909030d0609200c0a1209 69
    0xf80c040803441c0d00840c00d181d80c009844200020400945e0311602030a501c20000882c00e2991400c03110f944041c1400024a81902c00301c10b170710b07400381c0d1480050703880307000e401000610049004816171302582d81c501a6030044c1c21580c503130382184c100850460790000070b644865103c00341e298113090200c00c240d002c0b485150041c22890240300000700b04800d105170450b014501c00d4034100f04400b040d03010280c0b184d04900300100041c2580b44514500d40c0700b55030703240d01d80e4015a0044445c0400d5401c0034910307404502d82642180070302808101c00704034101d02e4445418044000d019541d800800251240704034034500c0d051101c840e01007224280704002881d4444200076000c3c00e064004070140c18000d044e48205c1001030142c0300c1c22101c900340800c8004000e41c014003510144e444900400c81c01d400002c10b221181d1109200d0034440401900500300100415540010a1b803008403441e01020381041820a608000b003100007444203000030f8000c0003640000d01040142464201200d0518160f032 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 663353102 1250 663351852 663351859
    0x60403080709090c020102091507051002090307120f03020105011d06060d240e090d1b0212060703050a0c080103050a030f050c1203090601090e03370f090b13091a 71
    0x64400613aa40550090002081c121010000300c0045850354086110314840181700c0c1d040240c50240c00b80721600a08020350780281907400d010344580040340d0390f80381c445050300ea085000c9120014180c0a21a50f4050822a1100c11184460074907066088802504c001c0c0603400c0016100304498a030b82c00748100f00c01c01030b0120840741040d8040e4080e8811805030b90300040e03800001c280c0c1c0300b500003000c82c000c1c86c0340c0c2c40d4038104050101d40600f001100481c1a41c000218550090b48158180003a520410741620002401d041104410003183e450300211018014890010700110340c00140402150b036040c501080c183c00501000c0346c6500541c044041140b207500c0354801291402c1c40507500c500b001c20200d455503a62081400142c0d01010340c540a140c0041003c2d141d11550b4002c40d0003010124030107601d0504903200034910032a46104424001014814810103141d444003500005214407070543e420540380ea501880c0024042c451303a0308a690f2960300e00701d0003050840d10b0030b0407003008 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 663354352 1250 663353102 663353111
    0x2190e01170a200306090f0a060213030f0c08151b0c150109060e0c03040f02090c09060415110a051c0c0b010602061b04031203020a0c02040e101d06040308070909 71
    0x100d43c400600c0114541492007406840000303082c20000080c91240340045074010b282c80000c54646800a41c0310482c0300340075072846000800032403a0ba018404485e8400c41502007244d1030280d2041c00d02c511884504c11949080003801403104c0c1389420382c3c0b1503c6200c00250350340d01c0250407003450000c008100f0b01640003400d0000420640c2c0d41d0050b411a014102c000c202c83e5541224541c65110803200200a036502040010142c00c050080903881302009214034034103919200080d1007604503502c0041c442d8015003103a486a07a0044c1d1101d040d108840c028150301502d560340a480f629000362603040c10152008181809108070080c80000e81c00c203c0101d610350710f030755000b03403210022215180b641c108901c8180e8100c1c00e0f00215412a604010203034032109100200318040d40c002ca242804000341c2e0303a51440540e0303551207545003054811004182010080a076036060f2400254440c0400000c008590b405010100c1c3c1164087d90600e080400c6e60b59020054401e003600d500483c0b28680341 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 663355602 1250 663354352 663354383
    0x60409060501030819210c0908010504050a141506040e10021209070e041203020f09060c1f06050f0f0102031207090608010b030114090c04080a0302010902190e01170a 73
    0x20006107081e1700340418103000386003100301c1501c81030280711941103501d203556071407070329034103194050044c2c01c1862070401c80b007555035048103094400c1620242c034203800019011081003030f01c565012a50482901800b001540b103144e0030b1480e500181002c2c040d81e00e40e1204c1d0281e1b00180304595003a4020581152100240c0702c2c4042c1544080b60041100e00c188080881d6490000420900c1a54004501258001c400a0850194000800c400710b40402800324040d156500c802a051710069000202486a4074080b00c0900705100c02c0e03480c158131b00d400410300c07894440c840c42d62803402c2d00b9600304d0106020100101d26510805659442441400e824410601c0d8030502d1401110035030795a000381170741c03a8071701080030340b200f80b240744105042c288048000c1d081c81c4510982c8088071055503418680e407403070468103011440d80c0480c0140d54030312240045151000031134100e00c460100b940c0c03090b82490911020240b06002e9685d800104030003241880750300300901ca10299000200350319204c0c0 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 663356852 1250 663355602 663355613
    0xe0f0d05040e01050301291c060c120606091406070602070c06020c0402210601111606020f01060501020a020112020d06030633140a0801060e011503020405010203090906040906050103 80
    0x709014000b80b118034000000346900d014050b11849451500c1d103140300c107036082500018844039060341504020114207203400070100c1403002038614015200401c291500c4600103086002c4800d0130340041e0b1402c001805500d500c0362440c01075501c141d00c0508910001000100c01d03010b0000000c011500000d007030800c105a0902c001c04543c01c1d0b801b10b9002c8016482048181d004020052007803800c2441c00340d01c040c241c2d0400503003044041c14045101601c0d11201d07814242c2c40589400d000203645000c0148a0b4100300b034000f0500042c0080110702d040000007500c4503041300010781088080009100800d80c1a812201000120741080240c140d40740340010180c510424180c1054948410b1a1034034104d02d0607403088401410003204c901030810300c101d2615010504202e401800f541c5000c60189002d100b060302401240c4850344113903140c50300c410582403160000b030003018010700033001140d800006031501800c1c105c0f981c09039540e80e00f0124004124044c00a84100d0505000205019 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 663358102 1250 663356852 663356857
    0xf1b0602040612060b070206091f0e03150915060102071d060f040e07090c03090203060f0f0903071106032e0f0510080c07060902030a0317150904060e0f0d05 69
    0x7160b6460380000526441c0001c0c084034801d00c0392144042c0d040000724018907180d40240300c4480d00a258100301c1c1181d00044420352140140d11000ca001c818580b070092074200203441c9900c0b2518006440c901c0c208030302d01d403a6501444082c0410380c2080100e00168002e00c0440007030001403003040d207003913080600b0b0a1091410f44006005030022070810440d41000e01a0501d5800001c0091941d549005404802000c40c0d14100d41015618400440140e4040c400705000ea10003010428203800c0801e1401c40510700940407031400d60042102c40c0009605c080790f84100c00c0c1c112005500d0f6961800e181070280441c0c110b13404024040c218002c080720940302c041058518074007000c24056140d400380a14001d0340701907000031410325030000700c1d50031850000701000c5205100100702c0c40d105601003442c200c03480808401141401c0c0690f1221110325403929401100224641020006007010804600d00940082d0407103484201042415804100d0000e045244a04903098a0b02101e402407054 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 663359352 1250 663358102 663358109
    0x150c01140403170a0207121d131a0d0f1b03151a0f06160f0501020703021b010509090708130804080109261c06150c03030e0109120f1b060204 62
    0x518030b0000c10b44a030300a1080d5071811f5402100c019905032802816075041148035001c01c040807500f0f40c4107202c0e4807032005222841d0040303d000700d09040716804040c02d50030169015030094100c0c0c10544040750301c24031981c1c10075030084038075500500d00040c1c401900b0790540005d40000046051409000e00c07552100d07040e004107055a0344125001c0e0100701c00f288010b40c0c0142d01c03010030312400403800d14044103000c07410310400c25500741c030714280c1d40d0381d082e600110307000d80c056004135200f11204200ca2558202d4100241b03400e6180510703d80006401020113401081000580000180100c08180086840a821003100c42d101c0d0740d1000494080c090030001124400a007401e255061241800c07540890001441c00340d04240c2200e882c43c01445d412181159809d03129040000c454180d407030f1120400c222a030f2101c0f0304c4025824050f040d03030b0315200c00d10b100c2da14014004000c202c2104181c0241c0050b40381409002e841e40c1011102c981142c1e200f108032990498a90007000010342c0248101e = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 663360602 1250 663359352 663359387
    0x12110d050301060e030601230d02040c050405010801091104090203070203090301050f060319050c0d0512120a06140a3807050706021501030609030302120a2009150c01140403 76
    0x5a4100d0341410b4441c0d00a200d21819404a1150b008c5107042c0403a0030288042c001d84201c408811a80000b0180c408440c80c96010070000501408603503031020510740504044842409184190b002603600c5125621401c00d91940c04070110782454400d20803a900104010001e00c401d044c507000c003450b4140203803001882441031889031010700700d898090000b5190090040d101491484040c480114020380f401c0390b27513000c0d40f42105241c0b100315011340038201d08080a10814075040c0714060899003603030007981c5100c81400c1c16140c03554a003095101070ba404024010200c4613481f40810100038501c41451040c100580684041120700d00a0076446000d10219814280d40388030a0b078aa01c8110400307806a04441c0051020408540080c1480c038400d10300146802c019010790104404291644226161141c806014462107030510358500c00d00c01c4a03091902c512180019080c042004609484a00202d20b03200b81c1e01c02980442040c1907595003041448c909032400030702442c55102e102e80c4 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 663361852 1250 663360602 663360617
    0x302191e0f05010c02130b0a0b0304060606030b0d080d09080d020a11061f1a040b0c1c02010c05042108072a0b090904050115120c08160312110d05030106 67
    0xc0b290f204d6140d83c0001c94024250305c11403401d2121032000740180300c40305a08111012070004404803250006c0d4807450180d40300203142401c00a004090f200c182509a00c1007100c6001000898111b204a0300407440c86075002801082620740701129000b65030510b07078860b10104a00039001c0d007100b0039031445080708058848540c1c9885003000c040c210120243c141400442080c4100b200000e408424800380195050030507170346000e0304109038030034440c804840d003041c00314034107408514445a65102c0c003400244104410014000c1c0940200c0c0b051342c40c2c0084107242d101040c4494020750400d0350700030300304e144e60304441d08080c8141c00101104910210744042c40410285194203d1001d4910444005207840443c90401c5081e640c050420344442d540c0b52040c1007510340300c96141c0d004250f58980c0c90420031940c00c02c25810700c6244d1019400f90408119800543c50214040060b01d0303104208001d0340103040c80465500c03090752400e40c4103100340402c06c641d4039000b101860494085035210305 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 663363102 1250 663361852 663361859
    0xa0f0b062704062907060203070e1008010e2d0a050709120b010312171029160302070803030c0912011407080901110d020d0b030a0c0302191e0f 63
    0x422a6207502c40c03083c804c00090907050841075603101030400d44040b61039107801c114040e00c0300401c03648195003881c08a5008007000e03515041c4a410b07142008214200700c13003291b142c012908440760b0014074124070341d12241d051400781580901c4c030398a07c1840100c9200d0070301d000e18180004001c00d8401c01d001c28444c042c005103080d003a20000040b60340c8201c0c160138503440d6683d8540503076800040d0400348a02ea01010407402c44400201e07100f103114803103590380d2618007080c1704d8511034140a0389100340e00316140d0041e21012001203031711a0070650041d031240026828100c4c204015034110305024040042401070107003101000d0f04030b082d01200c04145006040406034201c852042c03008658000b2000000c03d5a07006103c8268885d80c144d0000c01e407000802030380d0341181e00070103c2284641c0d0100e260742c800d65443c07041ca090f441d016802400f40403030607203441010491500c0000d110b40ba408101001414254000d680148052005004001c2403131081d808400103900400c0c240d60034458000 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 663364352 1250 663363102 663363109
    0x40c12050c04091d1c0e03030a030b0f03010b0d0f020613060c020f0607033006030f210212070512160b0718051c0b040f0b011d0a0f0b0627 61
    0x9000e814402009044050b201e4100c03200c15020408201e051004940c2c013800252000d000410021209e0f0f900041c1142d001c0c02000028051865520f000f40e150000c40304081c0c0702c60542c01a602d42089804003843d040e0302c00a034062041400c410350f001e001c52400a0401d800c2154001c1c514400ca4140481407040c10900c83d80e4080e04102070001058407014255075000740b9011468a0542c003030030704070142d4080307102041c1c1324507620444071110388190180600c100c6103111603c0d031a012542440e90b10140340029a035100755015404141400102281004400c0001c103807001005060640c035980c9a5100f1500e1703104624044d10705518003400a654244100804070305c041c48000071585036810107080c04080b0b030f010aa141c40311100042000045805a030409100d035104424550192445251031b280c990010f0740a010340c80b1003034891101e0608003800f020b6006101c80300010f0400c0b602c03255080513102510340355070410800580404403160205880100d64601d8011610068108052 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 663365602 1250 663364352 663364391
    0x102160b0106171b0c070302090c0d0b0a06050a14042103021608060705070c080111070507060806130e1e06241503040305070804090c1e0905040c12050c0409 69
    0xb4020410004811421440030b94003420561781104112a1169140d60100300300c00c100351410340d45040702250500c00281180201e031140c503c25038260020364a02130000d811405089081030500c154000308075120001c140c11b9070002d10b11600d424482d109900c4002d0300380d8031600810743c018012040c079014003585240000c0c0c00c8603550030060515540d0a842280c841d081b154040b50882280440005c02400c24001c400f00c4a079100041c035903500007032601c213241003500d07808003046c040d06608206903a071302c3c40e4103074002c00c0260101040c0f101a03e140b46d030400b600c0124140c1d03a4000648528242500001c10603c1414090a80303000ca0a103841c604000d820214815540031121500c5030580901010295803c540300f03003400e03810881c00b07640f083c0090300700340c200380c1105a90342c0e0031803400c9521071091640c1c00b40b180c034241100701181c1801070200600d80074440c000ca403145041c403e058401d00000c0c04c00380c482c0c0405c100c14100700707865050580c014030500707280d603050403056030405103d0312a = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 663366852 1250 663365602 663365611
    0x201020a03080a021b060a06150503040312060e040327031e05070503030a030207110d031704030e0d030c060c1107180204090608030304050d0806030c0603090102160b010617 76
    0x621032503509580488540354010118124241c00307003d42c6512a29084841c0c40445801c00584840e140c100480f40841d902a4041c1060160020314459a55004070481313800c1500751038429000c0340300c0c0d000c00c03010309416030100c1c4076282e8410400c410f055100c842900401000d100d00b22881d040c890102e10540d03280d01000d4803a54481c41210306003484071403280455031049080c1d0314560707515400603065400403009840032030380025500d0300f0800540d10070b0320005011500704070b1040c104e0f00c000340600c00003001c1d031102503010030110b800e05004101018402100900e8465042c070035244c010980d4541c0441111410b041c064090103140c0168480c2803840314130001406142d123000292035017000f2284c54200d05c3e9a0800c40418403050724000d61014042040c000c541e2410280b9182d460410006120030800c09488240502544c01207107928102d01d048461700e840c1d03198101d1041c0244511a940b01c40154510074041c05c03c000368105504941194598444200c102d4043d104050021038 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 663368102 1250 663366852 663366857
    0x204050f12190f0506090316081c0609090218040f080304031404032a0b0912150112150212070309081303050f12070c05011412070314130201 62
    0x680040322400c10040040c0710307400080849001800c01000b0701d04041d1496020748521a80344910424401c003003000540114800c0000c514010f80800c1040c0c2050040300010201c1400086002d14050136188060ba41c1d1000c1e80100316440d580c0f201c001c02800c0d41e8404074010760300c0c2ba10755490350449009091089400600303502c0504070541d2a1041907200500880610040041d1180001900b402030400380d13218000303605c0c40010301c540107549202160481d080f00d141d0404d050103000842020351700071450a8500b100c0f2078082c44111030928076981829154030448100004403d41c080010400b440e0064022401860040c4401000d0348502c0780e240304181f01c004046651280b080c2c1c884000f582c0a14a0340c1e04242d134482601240000d03076401503400b0f44c44400400f001c03038401c1c061070416021800034580b4040d801d95400003170003240d00c11075041c81507068650700202c00c0c0f4800c5481300e11103003282d861240b80c4508080c000b01419505000122500f1001402c02c802c0340c6094550150143c = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 663369352 1250 663368102 663368119
    0x12040506030622050a0c0905030105060d120909051003031b08090904030314071701060903020a15051605011505010806130c050c070e010302100c120e030c0a06030915020405 76
    0x180c05003c1e000b0b14501c1c8452140700c9001c0b81c40d0340c100161143e10f000e0320590101144000041c50010201c502c65008031348640d01d0141804150358403041d80c200c900d90b00044028107070030078003019a44180c050303000103e19410303c400c11031040300039000314042c3d9200c0d441c0c03181034110b0399840a14002250800510041c42004400050b2500001c07a81e03016111780380100f509030030318209402c4968143d90407004250010410301c0c00c81c8145000d40d014116a2501400492660f0001060920b1234400d0403001c80703103161031070101407041044500d000c0300f102105550b1000d620f0f0040c02021072504147c0040c0c0000000b01d59503100d040003d0059034000e0510f001c66804001c040000c00f170043d80340003440070412010652400901150004129144102d00c83e5131450052100e4140c001e0400c101700001071030a02d0019400d407034000c5140c05585060140b00c610040071900e882080c0c3c1381151f00610220000440943c5604141c0481d4030501d090014045071400382d43c2640a107014199002440 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 663370602 1250 663369352 663369361
    0x30b1f0b04091512030c0b0f150609030a0803010605030f13020d03180f1503050108030304080412050a051209040f0e030910140301080a02100804030215040609060c050c1204050603 79
    0xe82103c1c1c1403100c0030040c03840490f5640c0c14840142c0c00c9560440110301e5414103c414014040074503a448041c12101d0845c0e031070684a40d500b080c1c09165140c1c415500818032100035103003003015054941d070003c501d95480d44c680d10b0183c1141c100321001e07400f091071a4000782128400703104080c85582d0251400340b403030400e90350070b40340b07072034000d481d9030003124881c00002c5c07001050b0090380c0c018541c401c1202600d64407014010709580050f04001d403e68002c000703200004074940100c43c00c42d1101c40c022040c80e046443c2c000e050200c0800041e10303a01c51100400301c1c080410005090007402181c5c00c200140148a491060307452442451356030343c00900040f903d601f04812107000c0c3c000756142c00e5410200101d092141c40d0402c1c0c000d44426440180868214181a96505130200003401c1c10b13001443c280e41c0095462181e015a401da040daa4400704c1d0400105030800250244d00500134010710f100f13800c1c02002c6411600009490344103180c1541002d10034001142c0239a18007070859440c0d0743d40c = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 663371852 1250 663370602 663370619
    0x607050703050c0601031b0602060112120504090509010c08090d020607050a020f0f0d020106120b01140d0602070609020f040e12034803010b1c0b0a030b1f0b04 70
    0x12403058040c00303402c012030102964203001c2d46020f0f510aa03030803c0300c1103401480750b4000c69990030207000d550054006010344900140c80d1003409a01000b81400e50883c2d01044442d07010b00c2d408401c64178185800d000a2010640201041074a5075803407450321341d146401c640d5190700075082c1902503040407011407441442080180350010080c0121101034000c003c9503458441c0d5500c0140c65908203040c00354181e030f8203001c0e03140281140000e08080e054030b920354810080040c450600360250100b080307525034490020001c040c54000f0340c00c42d2141d5450400b180600304107041244219810710300007025141a02c94070312811a07110007001e00424180382804140e101500050140300001c60603820500c01c010840107400410345400034504e02c4800400c2000045d01241010320403d000604c140d081e10800e450750b88048881c02c030f054a180e0920389004103404881f1070f4201414070360100078000320100150240c1c00100003440c580083c0c40028404015500030003048040030041088500c6 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 663373102 1250 663371852 663371857
    0x1203022a010b0121151d09060a021908100b030f0601080a020f070f02120f03190e090a090c0302041d0c060702090c130e070c050c0f03070b130f080a051e060705 70
    0x10000d450004665160350301e92030510186d0100c0002d00c1820010401c441c18207001150300800103070b030150304020043c140ca4192401040070b000c00c2181c480c00003805110322070120402070808048142d42c80c140921100035403041112802d010072020700100d850303940709100300c0d50444043c0d0031039820401d80780d450408400c00782000f40d80c400c0341001040c140c0c078002e01041a921500c10010740d1344100100500d440310030b8180442c1d040c08080c1c6112940c82e283d4003034082c0e01000808000071149610304d00b0544030152a00061740041ca03007082d480f01c002190030703d100752101c04003c581c960405481000101e2092032802900040300b040800d0f4000d14102c05000819241d2001d071044545900c1041801141100d5160028000500c502c0c1070040c18013040c0d03e6581c0c00e480c0f2051000d564808a035456600c0d2103003000801c8000b5461001c6850865142d01424142070040e41d880e58441c0c2080e030390f4007040350a50b654054909150300d6140c80da101ca154060030f81c4054070855079030794019152034 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 663374352 1250 663373102 663373121
    0x901090f0609020c010902120f030f09030a1b0f0e010b191b030206040b010e071706040b04061805090d020a02010c230609010615020a1203022a010b0121 67
    0xd480e14000b1598004500241c14034442110001a1440550040100780080000000020b41208a10030405100401101c4400403503464403070ba90074920000c24074009410794081d03c46a000d04481251108400d030380340403152120510345699490301d102d24a1944280700d000c616640801200c00b030001241c5040500c4412410200c1c03085c45a41c240700b1802c0161582140141c0200c000c03c020015440c1e01c030ba001d4204441b14a5541c5010758028100385010240444404041030008206507101d03000710b100101c01600030710205603139840440140e08032204111285040200003030400e040002c141c13050100e00e60081c980e00040c0d40040d5400e0440c1c2e1010f0b01d00c50740c4a40f00504000814070020072452400c80200020704d0900e15036400c41d81c1c1500035600d0b81480c045440c0c10700307038005a04840280c2104000e64400030362039081e4001c0c40f0f40c09054180c0020241188030509a00e00c0c181e00c2100960002e0002d018814011902009c40850007800500c0c00e60304c0700c103105450360180d02e84c03 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 663375602 1250 663374352 663374381
    0xa120504020a1e05030105150105030f04110406031a06012105070512010803071103030405030a08090d06050c07050c0604031a04050a08040b1309061401050a0e090112020103051302090109 82
    0x3558450010318108241080b01c0b102c0c1030083d403400c10080c2070910403554080b0300c1c038100d040513030315100000340a03201c06090251a00d844001140c18883c040c00244440240240100100c5589107071104a440d40110f0081d210040000001c4265000e00800c90034a441110b22130080c100d1071410000401028000f03800700b0030244a0550a0031580e81c10b01d010f00701c414025030300d0783c13140d10b01003141d42e81154509e0300941090004200d213440c00109004030300e5010b50840d407240340c0b50020404002036101c018103a68140b0041c010412400c20003494880d01901c01d030340900040380c06000c1c0511440c0b000400c0f5a00790540041c0024100c40e041c0d80040c0300710251601d611258035203040942081e001401c0c1d290000441d03c2011890001d41ca0003400ba10a0520145182441d01005420740e00742c0207060260000f266000d240c4500000ca680d020000d1014600756102e0401100c0e945503120200c3c0428606000706500f01c03400814000050342c000c024500707503804c0c40c48400103800d0780d25003845c1 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 663376852 1250 663375602 663375619
    0x90b0c040e04120c1a01051903050304050618030307030806090f01060e01031a090f0105040608151f0801060b0a03050906101806120b061011190314031e07050a12050402 74
    0x240084845c2c0041016080f0340c44c05950504040124102c01001c40c443c0300c1c03104140810000e0340c04410307581200e604460080d00c0707503514401c2c0b03006407005030182503240c00005401000c060304510068000c01c41a1910401542d4001710311020341e000380901d0010444401c0c604819621a8000442040005104041c508841c0010410200007075038a0703030105003e40c00601c00c0d828980309890041242100505150020324064010140081c22111044407034100114031054080c4081e0004d00c14032000300445940c4000314401500041d9041c00043e0800020403406280080c595008003040000c05407013515000b04a0701d180020222592096101c03680010b03090145a860000903000310180c09003480c10320f040203150082c0c041e002050101595459140d2100011b03150b000da1542103280c03000c541030b810156040921940d001807102d40c000200001140840d203144031483c901d6403681c0d91604e8500061b00e60340150070546001808035009010407000035000240c101d4000f03407081c20f = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 663378102 1250 663376852 663376877
    0x1a07050921010b0402070c120f0c030602040e0a06061d030f01020a0c0212120414060702060703021b0109050105070b040c050a0b19020c010512042103090b0c040e0412 73
    0x4003110006400e120301c011a406400c0c14180703080c003a10111500c11281181350506076595801d00c41400c1c02522813007668148841c04101031708113031301040d513000b410302c0b2007030380c2d50b0718100d80a94001d0052303d8119503107102083c01c072001400b50009640440d203c141c031865080c10044665010300b40120742c0342c4955016503038101803e01c000c041040555849400c290183e0050102c003110007240001c40307034814401c82c503008240c2016102a500d54103e81012001c9a0340000e03158011480081e52081001960b00300301030b0006a4044000b02001c030382e192681c0040015143e01c0010300c152804588200301a0340042c0d85824800ea00c180318002441a55407544045031003402907801080d1a9000000c21049500d06180401880b4415100400e050b103e018002004c50003801d448000e0000d882c80417504108041c080e050010444d40d09812a045000c44001c0c050200c2003070a5032120617190101d0400c440400c21070f015a19a0008400701391143d80d100041d91a64a03041c8080048546100 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 663379352 1250 663378102 663378109
    0xe13050a0209150a1a040b03070504031b06080901050c0a03090204020d060303050a1106090a060f020d0f021305120a0b0915070f11160302010e13060e160c1a070509 72
    0x1d038000c20b00185043c00c0e81e09840140005800302d5000002550394054141c0928185c440c2150150f809074502c4540729211203506840d1401250030007001608513542c8000b425540c0f4040b80e00b110155130792400a501c81d0b1905a0882e81d0580e685813800d5010030010004602036040071519502c050001071820014403005d0b0100d40700343c1c00c1200082e100142554a250b03114047c210425807000c00351484d4182101d04664404140c00014101e948603400b1603241d001690660b00b1042c0140e009200011040b9100ea000f940304041101819400001c08140ca00f89585059010310120300100b07235030861500c5000280f0f800800d80300d000e00c9201011488003819108050084d244e03500c0d030f107a00c0f140780000a00340a9580c544c10a02c1d0740a071b20302001c0d80c902c01032007074100c80d020f08009943d05040004503040c5020009030300030450400300000784891a0300c43c140d2080c440603022100310050887c00301c640e0f05070540080c041c1c00c0e40c08401c0120b0402020060b0f0841d00b141091440d091005012 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 663380602 1250 663379352 663379369
    0x151e09050603071214070f0801081902130c080a0c020c03190c080304030b04020915030c13110f250206030109110d0f0e060c13030b06030106031703100506040e13050a02 74
    0x50384910200d0009011038144c01ca8024147d201c0b1906102050750705148095680c0c40c640c3c111a0103180d681603070102507440350103044011f5101008140b00d06581c90a01a1105606031852541c452912070f2154000e0300c086400b00305000002d0140c06500107010401c2041540302c5400d4881c04c4540d40005100d00b010801030000b1886680940312038a01401000000f94005025418a148800350624a41e0b40411140302c00c2e44102c50300c4c40040c0c102d810f102c0040200c40218010754000180c0c00d8250b150820280c50780307811a6032052046007814650301300c1c00101642c02500a50f042c001804101c60311b4200702180300c07041c48014148075020507520240d54a14008115482d035980b414407130342c003052018503400201e54840d2440c0202d002180000c3c0c0d8001d2002034021815100070a90a0380c081d0800b030004c540017038403144112003101c000c07e1316610075159007030700d0201000c0000345401d03c0c40c10354080b03407a40c0004101542ea00d9070100440c1590b08812241030084e14031400060b99003458 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 663381852 1250 663380602 663380621
    0x12020f070b19020a090b03100f06090e10050102061b12070903050c01020f0c01030b01090b0d0e2107082104060501141206072106151e090506030712 65
    0x4420031801c201110b040e141c4200d01c00d909407070b4010481c0c00900743e080707950001200c04100b29945d4079950210340d400300c070860b90071048940509003000510198061010415106240f030911548d031a0a0724020812909100700340c0941c0003103000501603203000e58814145840c3c00c4090703240c42c88281c1c41c1e0030000411111040030030f000850a10a01000b0800c1000c440000e0005185002c0346240c96540c0b0007625030300b60b040513150f05031400164030031603c601c000c05070031508545a801841d003003c081c0c5800305111f1401c0c46000c0f001c0c810b02034035030700764080141c002c0461840c0c200161a51010341e80000c141800c03e00d10910300d0207038410050a107500c40c1d8000c1d81c002075254141842844082c01343e81040e8401d5049814240042102040e0726411601c14100b04d910b41400b06450480712880c1302e03440380c1041c41c0040001e1500207104612042c030300c941e40e451140301c0982c1c2e10800392416130041f11000a42d030b444180594203000c0000c41d0001c40034140a981141e26140d144184c505082 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 663383102 1250 663381852 663381863
    0x11010c05010c0c030f08090604022b0807030201050f0c07030c1406070306030b06040908090d060b0d060501050901050607081e09040c0e030705010c021c0206070b040302010905070812040612020f07 86
    0x440800a155100d8120185d50082c0d02d000c4034107080c02200310f42e5070100940068800c1c01d502c076021104411490103480c1002085103c110b101c001418241001d412500c8141c0155003020300040c5025500c2c035115214850a868441c00d104203500d00311140d40d40600308075140880030005d050700440400c100351250072145e40c00300720302d820751520b008070755405001e180c00341d030510400c0740001e80408195078495000b500c1143c1010a41d0600a0240100084041e0000c140d02c007800181300c002d4200506072941131f5107441d0a640e03074005001203441032140190000710140907041010b4017a95070f204001c00708000080c2000c0103500050300300c1d940c40345072001003400d801c280d003054102445094002c11003400d200661007500d4001c68a84c944c0c07032090300c44203144a90440c0855542100303031003800e50031402900ca1032601317260180c000c2441d103c00361741c40c0c86408030000d044000081d0005280c0c0380c00c1384003400c00303242c60030540d5615520051981115002d000605005c2501c002400303c0c0c60190 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 663384352 1250 663383102 663383117
    0x60412120306140a1415030708090f0c0d060f150b0403030e1002150a090b01181a060a030c051c0209010815010509010e0d1208072a11010c05010c 64
    0x904080d003114207942c00811002c11000740f2503507a603031301541e11003102c003c03030944461400200000390000b685100d0715001600040203008203142c0c0500258031509038581150f944001c00e540c0d05a07070f07204041c0000c2e400180c510000b000610b080e00041c44a000c0791002190101d01d40501c00c0c480701603500118010f800201e030070018151711900000c2c00010aa429542c20441000d00948810300b060a000b0040c2007500414a64405540454505504007201488650311488200c54031120b1900643c1207074100320f204480511400110151800000d04682c80d0003c6404140c0c0642081c440640c1880030a003d032404038001000c60018070044940e005a6441d50343c0f001409020f4040c0407890000d081c55444916030f6001000c4074030890003402c08028604800c0009a02004000c0d4001c003248000c03501c00d00020340182c02c60307006203083d40710044942c141c042c20104041e41c0420f003900060450440d000801e140104060803280c062601c1242402d040e140c0f1030075103030040c41200004500 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 663385602 1250 663384352 663384383
    0xd050106020607030b0445060903111f0e03070f0f021503162a0501050103022b0b060613080d0e0a06020606100306051206010f050a050102060f06060412 67
    0x25104550030044125000c01c24101491a117102000b1100503141900c501f00c1c003e0030041b52070616640071909141403000c80000a4030700400500046403084000c40d00303242055040140215082d00426484080384110020064060b00500a48800c10803907000800503000410144102e00300014055844822449442d1040c07000200211a205900c070740300380203014160350a022000107812103817a0054002c04900c2100c01c82c9142142c410503900503005000040080641080c4d040302d008490243d80d103d8002848220500c0f02c0303140c4c040080c0c00055140000d08021455500188040d081f5414250300760043c0c4d031a1615078004c0c0c0c1090303001c0480d41a01c40c0e40021076549092082d1488400c8501d461070195643d400030b0001803040307080ba0450964684603501c040300400006010340d40048070a00040e445807804c1c0200e204040c00082d01080346d05094483d10121501a4008c203001d036214024803002e60000b40c240ca038031482c00c00c40014098140c00b00c0104c064020104117400401 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 663386852 1250 663385602 663385607
    0xb0409091a16030b0f0628051614150903040f0515160f0804090c03061403030f0d09020d080d0c081005060c070b0309010b0a080a0c05150d050106020607 67
    0x3074100142040d03a00c078200841030b02d8402840a00481074100070407080008400107451149207070103142c01480100300141d1034101541c4110885060000c0b051034500510030440d014401c100800a070500e15410360400104000c3c4500131806920003074800039101c0e007200c1082800c09491041039070707101040500030460484200c00040c0011140300c0c43c01150581030301c1007809801101849404d80f64624014070443c1c0c004034110380c3e4440683c1e03030749540700c06002d4010716012511400007860950041458020301440d0030300b8000090046050021100e80c0071030640c41190304800068440c0d0f40ca000580343d40388040046e51041a4080d140c103006000002210b107141410000c11210300f051106800d04045a101500c8003030362040e039a8100c40c001a482c015680d800002d50040010402100080c107501c44d0001407011030b0750701009540d809201d90f41c2d0840c036001600800003000100442c0c6841c812410105040451050170600b0320540c403411503900340e0080d0050380200040000c4542e = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 663388102 1250 663386852 663386873
    0x9061809020409061a070201080c07060209030a08191106040b130f0b070813020d02062b060f0807080c04050a09020d030e0112090f0b0903040f03051c0305010b030403180b040909 78
    0x105170341841c180040c54000a2014502520001186100141101c18000c03160102c501e007801c00340464071a0212480d04980c035600c080c89001c0307100005400c00001503c100908c00312618820010f0505482c0ca444200e030050b0003038050036200120455480c0055048085015914062541d625283c68800d4001d420f82c10018043c019600c0c4103200c4070b006030741b810540186181c0544405da16071540600e05071b28861031440c00c2d0b450101d08003011481c035030584c04c0f100550f0750a4045041442d40d40b040340e80c1c3c3d08140e00810101c5e800c00f445450b044c1c00c00b50300c080c6d8030608400380411200000d80115451456529096000400f651510305040d40c12100b200d41c5010924000c1141070813589600090900029000b803280070b0000c0410803014007007050b0380c00f0382114102c902405a480c80c0090f940d0780384e401268000c050803480c40101501a00c6074604039142608820b103195100c1d58200c8040c07400141002a04032049000b041c1480400003500c090719245400007540d83c0035041c081d0045 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 663389352 1250 663388102 663388139
    0x1209010207050907080a1a011d01030f020d020304050106090c08010e060a24080601090807031b15020604110a12020f030109140304060e040b0f010809030705060c03250906180902040906 81
    0x144120031081f441d0768420361b082800d221641e0106201d04a41d001200070309841748014100700e00100707240c03105a9095004601a0344200c000300181980c564900342a580401e181c1000300c0c0000b0010801604945505940207a00a0a0b18112a2568500d038450b0358441e20900768103104010140c0103603000340d81c990b008103003400d000b09000e161208031035840c80a40002000f0124500c0f01e004084a186008406001e9981d0014003503100d03000001c0d505c0c14101d03403d45295410000e1042142000c003083c1c0141ca014980344491015503800340301d00d9401055000390107660f03c0c1070050101d210400000c00301014030016540d110300d0241d0080c030300c8004245007841286403001c2d140c8103594121104c0c05128003820f00c003846680344108103085000300c000281c40c90096008108050300c180009500c1181c070340e550f03502c00106003d11221804111086280850900503040c070045001e00000590114603010204215440e0f8541200703982040c1d100300d100c551600400c2c480b1800201909071103 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 663390602 1250 663389352 663389381
    0x311090705090d0b01031412220302061603260f091005090d020f07081e0a0c0b0a03050c16031107031e0203060115021b12031c0e0106081209010207050907080a 70
    0x44241c19886201d044c443e9040c09c4e034440300c4810031100607002600c080300080d50000c000c15140c5506020076220403501003001c0380001d20020541d0345403040028101d40c0c456440f540340d80307207503503c0068006070007003c0c0c064007480c40399800d10309804416015040c841c800050140c600716020b40310203450060112480d107500c0d0018882400026000591a49480b040040c0000e040903408515030804081038409080d041d480e2201103108241240101549400c43d5030801c2141e07201c3c103090005000d15081c0105107103d215811002c0f0b44a030600721a00c0342000300382d0300c4145d070342d075151251394429002c0701c25415066881a02545401d010707a500506800e07031010031b0046207400003903c0380700b07603c0712120100c070040c8490b00030f458000485040d07020380b008403036543d852260b0481204030301d10807c252141c100343c2001010b1206005101c11a84904020080c00c2000f80350500203030030401300d460461258200c002a6566488021402080d950301c8030103c50800c81a9070060710500070107001b0 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 663391852 1250 663390602 663390613
    0xc0a0b0105040e0a020925090f0f030b190f1e0f0e1510030c0605030402040605060a090b0d09170a020f010902060412151a0414010311090705090d0b010314 68
    0x1010318001c141203003013513411500360541c5d54800c20003e1460764900610b9400d41819641c1b01452600b103c02401038402c00c4e203904c1c2c03400e031340c8016090144020b40401400c240301040410000166407084440204009401151500c0350a44403030071128000c0184500c08880783e00d400064016218048071002c0b8141c051040a0121003a036a60f0306000740d030190049407400002d0300109000b50240e0103103a02c103444907102680c1700001003041c2c0094074180c1c411860050000755525003101110781c0e84c0b80d10f407600035038140340c5450101d9640003880c090649a07106d4005100088506100c41030703a04014040d80e40300d8400400013450142c08202c01005685007030741c1000944c7d101030566007200c0046104000300c400a20b400c601600d0748000011002d41449000447c0c0c0790071f84060104600c043d54200900d608440c40280780c48001c0c40050301101040304106000e08004c02c1e0f26238401404e04006140045440200e0301d000e00c00718003039420205000c014410008000b0340d074002c03400d11800608 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 663393102 1250 663391852 663391871
    0x190227041104030b04030e0303031501020d1701150c0501150e010f12020907030b0a0f081612020111030421020405070509011418060c03030403111b0609060f0c0a0b010504 75
    0x148580b241e0701000d825240720b0800501094881da100810314680541520744905110580e055402c001026030f070b000d0300411150a002520644000d94035899400440b0040d91801e050602c070203194600c00070820050071840d1000c00c2c001d014000228022248196203a8a45004490907003c181c00c403000b00442d1080070400c1e4240354254042043e01195040b070f00380c4400e4030590003401040802038000740d802c0c50000364641055203400c120b07210f80341690180d0003400b201141024050284c0040001c079050ba40001d0751050780740d2102136203443c088900c1e19403246019058a29509413003d510440c103000314045040501a00e9000a403d00b0b042d82081c1a020020f0400e001c102d81c40d8940020200c1c018640041e4401c6002d01503c4c0540407507500c60b801260302d07449910846090380810748a04460130014070000f4200a4072000c000e92540752441d0a0402c0182d90148000343d074805000e02c003001c06e28002c03500903c0c84814100003020305030130318940301002c0f1a050340000c0c804c0b4504440364 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 663394352 1250 663393102 663393131
    0x408090103060605070b0f131a040210030c1d21030304030f0c11150f0a0c02030622061112070320090d060209150c07030c080307170319022704 63
    0x50760020800741c40e560488d5683c648503214000045000380c1040800d818031440c04d1034805055008600948500d0100480740806509a0f0304800c10800040d226515a0052070a100f85030780ca140c2008140601c40001200d080206850409a154040e0400800c0c0010180c1081401c0d03d03011141c00e04110040c10b0f0b4507042d02045d01070380001e0141550892011800f2682c03000c8960310b022603d007050b140c02c6000f0b0010000860100100d0092117004045421100300f0201094080e62141d042d40048049941b1107001e01444891a208400e0501100c0da000c0d400404491040c00c841e5800a81560050f800000d284002c1c203082c19980e10410035041584c0750325010349105030b0810030150f43c031410400481e920030300d4a4062011030740d0200c0c1e07611148802158020440e4080e071814000c85840b084841d844c0e00c19140024403021052100301080c4800c640034582c0083d03c2076824119175160303a461410303070f03120310f02e03c5445c0150741c11030307402c2032030f100e804201f9107101a0350400c4410700c0b41818 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 663395602 1250 663394352 663394373
    0x1503011502070909110126010f03031209020f120f0a0809041a0a090b010e090c1e0906070b090f06012402010b0609091b120a0b120d080c040e040809010306060507 71
    0x26981004218031013104001c500b861f50100141c1c0070160741c0300d2982e40751a4003d00ea00706000031000103a48000103080003200380a03880c400b6800130003580302c4100d01d80030040b114030080c9801c0c040d03000c2c81154444583d4140000d0310068001e2446035590a4100f0802084541c1d180b01e03503407194500c8608013402e03242d00c0f0514040d26141c00001450503070401c01a17074039002000ca0701d5404003034202000741111080001c0e0810808000011081d122210364604039401110300c0981c0140c0d0921400b0b0220b01d50500e442d030402c102d11305485529601404950900400740c1091150301c102c4846699400010001c00c0c59030b164600c001c12903031081c4800194180305111443d441030240d00042400329040c3c024103200740806603c0c8554400b80e0840b83c25101404403008100b03585024003294150521a80c0c4090541c000c20181c07111000e034800c281c0b00c900f03019001c0407180300d0034480410710a1764191501e010f140254644de031220443c03000101030b682030360003540411a040c0003800014500e00e04 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 663396852 1250 663395602 663395633
    0x1060c0c1e181a10020a050316020103060506040b07060506040b040c1716080402060d0b360c031311030109050c0a1203020714031c1205060402091503061503011502070909 75
    0x20703450111301c4880c2040745009880f039000b07882c50100140d071404c000c0c40c080c800c0155610070f032030600000e80d0750300c02c0001c1130040748603040002404000c11310005540c3d510032603001c04000c0001540e042e1140200d421200d140365803001040303000c44900802500c2d406141c1e1b110b4103030107015a0800c960800180341000150000b40070780340104072307000521015005000ea0800241a8100ca05145034819000042548120b282c01d0b4800c480350070142e2001c1481407140700807184051958454424001034134080c0301e03040c0c508000c0c01203441e649503000c7c00385815007800b8500070310511640c0030400410802580c401700160320001145000243c0114036a01141c00c811441c0c07030311403509000301c0d0074030000761118280c401e0014503104d40d040c0c00500c00d0086e007044030810407040d0394103800c2c4030491040041042d4071440380300e05000000310680c020b50740a42c0140502c010b111011b050070410750001c3e0002e40026402007440c100d066070400240009001204080c44210030f603840794000b0080110 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 663398102 1250 663396852 663396859
    0xf030e0601060f050f04030605040b04060e03030c090d0c05030303150f0906010e061803101b090503100b04060e040506090f060f0402040c0c0506040507050a050a080601060c0c1e181a 80
    0x391605c03400b90110988009541050080c811807030300c1d2034403c000300c1040b5811180e2a18080c2c1c602d2803c040003003507d205808680510b0719082c0c110301040002c19039903d007282c4042c0700c0038011402c1e031018030280d8040e5210011200c50700ea00f127010441c2c40d01c102a00c0c140140c04290420450b07030782c0582000002e42d015186207030b8504c01d0782c015050f00c40d41c0114080d050301c2600c90301a02401d0a620455002400d83d0a58003049409142220362550074071401340d250b4423402c0e0300c6100d18a030b5031240301c6540d0000c01c0007600ca55118500740d08a801250300fa59550804010007500103000d0154185000294003e44403d1801c07000b04000c0c0d40010f0006400703140e41d98100010903004240c90f80c90030740c00204035461445c003460900c1c1e852100d800740b07500440306e0314030001d00340c200401c400c401e13110b10b040035280c0303603003020021100c142c42400242d9004004400c0040c4241c902c040b0032583c84040003001d502c15003040d280c81d2007041840840611240303840348417803602c80d940c051181c0750326044 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 663399352 1250 663398102 663398107
    0x1005090f04020f13030f0201082409091f02040302190303230702030307060b031b0a090c1407120315081507110f0105150411030f0a1b0f030e0601060f05 67
    0x1c1c0c42c40c0744280140a213034034100d01000400f00500c403502e9600d100c82c92007661355091a0f80c8200e4aa00700020f111110040c4101480800c1c50600c0c20b0801140e006814400b00c44051411420000401c03000b0f16003003501030350028040c029400c0181d6101914100c030501c4000c11407960764010401742600e0307094460282c0810140644255841c100c60705940c000b4201d94460100d03007000d0004041a0f45040d00c00e20400c0d020a002c0c5e030002e0007840b06101c000703101450341480d010255000e00150400380041194881c200010904141c001e822854000d000c011200004104041c0403101540c034120b4000300712100803c055440010034109201c42003c004095031100002074900b40b007850b0129880e401030090302a01c1850540c4128031817550725009840000158003400102c6040400001800c0030400028444554090302280c01c052a40b5001400500703c840081242c80d034010000c0009642d85090340ea400e40c0b5005440410040a000d080a940340040280160114815070411312402 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 663400602 1250 663399352 663399367
    0x50a0204210609020d03201c0e040b0a06050c0d030b151e0c150105120604032007060809061f060c020604051003091406071d24091005090f0402 63
    0xa4000c0f840032507018281c050b01d00910b14003d03015040941c40d0044c1501c03280303440a1901000160b01c120f10794010202002c6114401046860800300c0c041190402e4903510901007540328400010003c00043d40d80c1ea80710081010100c2c2820007111528003014100352162800d42d40b6030340c81841540480a40c1d564820188140d9100841d500a03282c040003030106000108640200b070110b2650040d00550056a898000704600d520940c0c0f5080303e59486400000c0c002806041c070751168803c4400324401c01c10100719003070300d0082d658002100044c0701f8028040c1c4900100541030b08540480307134003442e82079440040582c81c0c480344140710410062070f13031903820741d02c4c1c41d41201c0240401410b400100c00d0440006809004c002c0c078101d5801036102507691640502040150044c541070f9660310360f04507481900c0100d840400319540d801028050510001035802c402560000381000d40316440729950803c00062121801c85001413007401c01c143d181d07564030202c01100554040303400581b126003 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 663401852 1250 663400602 663400613
    0x41203030f050a151a121e0717090d020a06020904060906080d080106050c0a060209060d0f1b030c0e1c0506070504030b060a0b070311031e0706050a020421 68
    0x8042071505007035031030700041c44010000d9421001401c4d007115024101d496580b043d02c04215068003170b44803860414042481e0b507010b489880360b0481c02e0750f040f0140303000d00c882c1010418081503e0120120f00004050300144c07a610340f4a40c1d1050410b0050b110f46100b0307020203912064160002400207a000814580b2560385601c440060300c42c190f02004041e8541caa9281d8810318204105c010400910002414610136000c45007020015000781507a402155100310107074101d0fa40c6c1680c030a4007446510112240c620aa1414407440c040100340004441804150821200d0003001014100111080d41030b0300070091403c549015110041c2c5840c020194030054500c00c0ea006040b8054103050010b81a031101c054426680100d4201105480e01c00402050080c58416080400400c0c4038800c00710340140e045044074684075007502e14262204d0124201260806140349000c60701140e28000d10003070748242c2d80d1000704503d045203018184201c4074041c3c0c0380913080810b40740110062804115 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 663403102 1250 663401852 663401861
    0x50a09201c090311100218030a0503120a06030b04050307140c1819090b070e310902120a05060a020702150f0c060c0306040c02010c050a110106030c0e0412030903020304120303 77
    0x10018041e5201400c646003d01702a501000720b9140041110443d009a0315001ca1015016070744240210b1615000a0056200328001000c0b00200b80e2703141c1d000008644a9000144520304c6400a0341c0d6604480c41c045400c400540c603200003a81c04248801d105e510341c050748d00000c1d815408102c0460341c80c4803800c04500f03240060100141d04001d0020200b001d1048014001c10503503e40e00412580c090900c9034103e20740000f0350f0010040304100c3d18140d801c90440300842046200800c843c07209401042c40040071258035882c2e039000c80c000c1424040c5c24010340b0b0f00041c07120400d51510300160001443c81134821021404c6040002e442c00c101c002c103030102c400c0f0102801c01d03151103142c80079080526070070480b20340e401682802c881803a014818417500c0e0300441280c40f0f19052000402044543c4940001d030b01e4015035030f0303800120104440d035501308000c00301000d000c14140340503c0d1981d9032030070307524a94042c14108540000040d801200391401e0726801d01c00308003c0031481c01d0440181 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 663404352 1250 663403102 663403127
    0x1106150901261b0102060c09010507030e012c180c04031227030c09050403141c020d0b210705040b04020d1401050a0b0a2106050a09201c0903 62
    0x2e204103079030840d02d04080102044030420903000d0f140d640d03884035070b140d102d40300d071a2392140055020480c0f40d00081c042c0d45044840070040c5804098502800103260300590304142545042c03c1801c00401246803d100c9154524610b104100280c10103096100980c00b403400028a2081c001c034019201c54451f1303c0d01c2c03c040310a800130715020b0550300c503d00400240c41c00103a032601c03007007280450314180038025640143d40c0f50341ea1003d1183d410b0055000368010b6842a0002150050510405034607400600031001d40310000007944188003040204d0520020141a81d000714141c05025000e030100704d4508490090380c011629500800024000303214505951745620700d09000122200c12207200751b410f9030406c1e40c809680381d880d2060303c040c5000d00164100000c00d560341c45025850090b14041216101c41404120540c036030b0002504114240c020f4002c4c2566050081304105241480c0c05506801400040c900205006180c901185001090481c0c580398a0140b042500c40c81c00f15016 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 663405602 1250 663404352 663404429
    0x1060507170a0201230403030c0f081b09120601141012050a02040f060507031404141c0519030f0315050103090212060c0a0201050612150a0b101106150901 68
    0x5604846280c40e170049415035007a40024540301510841c40d0140d0700050388940030ba1101c05181d074540045039807490303c110305c031402017000788519070180e1580c54144884c102080c010b008198101160f600558150041413846004107501d154071340d580100220b01142c0042c01c01042642e2001512400707403041d076004955100070034400003061903001010307280c03080c401d0791101c03004510070701c0500150083d80502141c0d800806000f00072460403604642c2d4582480c408001c0b2241c1c00d444e41420400d03080c0600780c18200807202e4100305907000c1c0514640390b003903003820001d5201010b00513695400c980119410306558400a0007950303205000102c000c11854100c503200e14008031103080d6030b00300c070b042a8003540c2801c02007062490002c209840c034440d080300800360000780008450078440003422070040240d4961180a030343c3ca03411b41c0010314075100d481da00b928807480c522651400030020034505c92294002c02c2041d903a0355404030350781110b000074032066040c4483e28604c000e040303440c88030141 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 663406852 1250 663405602 663405641
    0x20a2907031e0908101a0a0e0414030a0206061513030507090b040905283002010c08150f0604033e010f030902091e01060507170a0201 59
    0x406501c528156020002c80c2c1a000b1002409401640c08003514010f40015810030300c2c0d00d0b1140c09040d48a20011203043c1d00030303a0024003400c080f07410440329400c00c09205081c541003006000d20014181c04541884004500d41081e41c0d200944404015084c40e100d00320000a03144254001800d9a044400c012400f440f03030350b603031314029580d4042445054803131420b042d507550851078113200d840e000d01c0d000030150170703081d491401c2c0500130403126005020200c03000c4105404245000310700040400d00c4a8601c040307404090440801d0103101c450b0000316030514481d250b0199008c0030b52038100032100320454500d515400040c0c86801c1898009810a0700400e001050043c0da100000c2481210340c1188003121242401e142e09052a402c0c4c490110440401008154460420791884000c80d1800168502d4a035000594030001030751140b101010040c1c51840c0024000c1c40180100f4803402e02c14680132070782e41c0e513038000c58056003102c41c3c02d80301282c0c4240c9076000390015103150154111012 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 663408102 1250 663406852 663406867
    0x206041106121608010b0f07060b01090f0b0c01050f070c260a0816230702150f07050d031509050901020d0608030d1401140409030e0310020405030613020a29 69
    0x3c0554a40048100007800150000440c401d03000c0442d40c0c03c1da803100310755241600036200d003006000c2a40f03a4504101c41c804000608101418080000e031003407010180e65501070018407401e41d8800b9060040280c06c1006100441d030f04000b50104050784070744082c690513510030500c50f2591008094024404000591103152607101c200383c2c3c401c000085010075a03034140c4008448240521420454800c1c0008840350aa035000021700038507440103148980c119490000d1940c01d4000c1450b406510f5000310b1b082042180901003985184601d141c10084500600044240d22010380709094950ba907031404100d551000390111040c1c40e501601c00d1007850380da560300542c5d0f9031100313280c1c060741e41c6090400040700c0c510140c114100c900c0300c41d000071044404010040100440d1008070705122038101000c0281e1804d00c28900c1090050341c0040c4c440f441c0c0010705042c003d00030a0940600d0040c0034580040ea40c1f6003103102036915501c9001c4168803a40044403104003e2041101c05050100d00b44 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 663409352 1250 663408102 663408121
    0x2060a02070f0e09060f1012150f050f0c0a0e10080105031606050316020f0d0e0a06080c180a1701020409060b0702031213030c0b030a06080d020604110612 68
    0x7100711020103000e03159181d92604200036a400a84100c519500580702003210034120006480d084910740c00030301c01082e502d000946407441e8500048610300c0b9806075031490381c50980b040780034008041c07500380401d05e44030316900b142403001030144003100c0e4042402d0414520441e20a1130801002d8488040c0f8070f002400a01154000d108691080c070640000c41c1400002d80300d034a00b120a0343d200c003402d41c2c0b207190f800d80506041c10048001c6100b40039540e41a000c081100e02c1104000d030311010140c41d5400103100c82c1c22000d410000a200e4445c050100c80d40020048540342c0000e1845032007800c141600040d03907403409912a80040420080030b20001034194024411030355001010071242d03644007002c40b000e010303c801c041d6050300000080e04038034a900008002140c4620740c954040c540300d6070381c60342c194401d0700407186089012017007011460741480354801604c416001841548032040d0b0082d0749103001407000704080100c0b0044040c0d40c48001c02c0c2c0f00c1103400c5401e0701130949440042c1 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 663410602 1250 663409352 663409363
    0x408010501050f060712080a09120e030c01052502030a02030d030506040c11030715020f0c03091309200315040501091a07050f031f0305101a1804060902060a02 70
    0x2c051062014014019803840c0c031408403022907501c1100101000c0710440b00703840c10301d402403c81b420079484240c842c0014051040f0401580380503203601032a048103c040c1850300c01054806410300504008865000c03c4a07400c0300c02074a15440d0b11114900b0500c08a03081188d1705d00001e4040c03040d1328041d101d843c2c254100d20300c69102076408000d42902514129140440e20b05651039980042100301e0201d001840d26a0b0392201e0900050701d00210108084030680c807900b0701d1305054101103804869880c102008a4090007084401d0000032280c2c0c448803d44047e80304080d8400000291b010304a07102801120f82112102d072841002d880e16003407490180400301c9049403902a4446902140c1c600c10000500275241e698406084c40400350480034070754000351400341c0644110005200041074042c098001e035101e48050001a0001002d140564940c51010f8075550b070100460700954559414402039010800c1304244145c030350341400c5004003040f650103900301000140e074503009600003d2 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 663411852 1250 663410602 663410609
    0x3030408100b0f090a0c0905270f01050906190305100219111f09020d0f051c0c0201030507050706050f01150804082a010207050127030e040f020d020408010501 70
    0x30240040c40c0c0d500200824612184200c84c1d0040014001c80d80130041580041a2030400c2e0a048900945510000304000388034444610340742d00002812182c04045041640c000c07458040301c000755414000000d00f241c000610023030080741c43e0440b00600d5242c046048004503000020b850080c42044a9940a90b2003203c0c109090038620304c0410400348104942981007a80b0401b500e124100108a00000b031221640c10740000d440e040e400003d40c0d00c00c21091901e9100d9076041504060910744181404041c4040744041194104103141668101d5108141d4550918001503555200340040d5814091818060072440c41d0070104283ca0383c00e1046241a5000540c00c80d100342c100c3c0d103041350013000c1154014940e1200340306002c080d11030b146584084690985001c00207a4202900a00326040071005481d80d80d1030341d20381c0001c81d01811180c4121400e04502005800d91614082e29100c41425014040c4d40d89500c00c502c0c140055040c1c82c08156244400d40d41c4a81d1043e50b103020701804e00 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 663413102 1250 663411852 663411883
    0x310031401060f050f09040305090a050310050f011a070807060608011a030f032511061c0b09090d0f020127051203040b0a09020303092701092c030903030408 69
    0xda003c10741e890014071002d200d117070003030006282d40d0710f980c0c08803003a0704000002a0480808400480d04d59024041ca072014150f007000000c90340b518501e50b480365081030388503140901c4ca240783c488891801000710368a4036080720205654514034078100703000b04240ea000b04e03070a5184ca1840f043d80c03150401506014034003102110820050f08143c0c3e1703100d100c6c03c00c03008100e0806089902000c1c034004080505240a441c5040415507032034003144c4107912800a040b100d042c3c01914180e990a6482001400002a1070700c1405181c040c0805580b1000d407502c0106001d114003083c10041c1c401d4005041c0b0240c00200c0092002d0040d040c03600c1e913800d507201222140140c0900101000e140300560b4403464102e40050456103600c000c440007080724100c240e0701400100005485a00c0383c504c8134080b0319000840783c0445d00bc0d01d04072084100181c1184118504148410401604250414a41d04e5010301d0420381c80940301c101c2491417140c0300100b501400b0202e00046d541c01e000c01d40041468090 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 663414352 1250 663413102 663413129
    0x31e030403020f030910030f02120c0c060921070c031b080601080d020307030c0807020919050603012f070b150108100605040311060c010504050303011d1b031003140106 74
    0x4070f10311030300c07402980c0c5131640103140481c400700d1071807282d00240402500c0032030042c41c1c803a1500f0100c0f5048000c131f807001d254500005400001036000c000d420381c8400010003a0091441168100c261109004130381844443c0114990041c0404c0c002d407040110350105600303001101c01c41c1490440c2a25100c1c08465004001c000110880042040d00c19107403554050351507c4440d0ba0182c60440c9410420759807903806006400050300c0c0d031110140213450b1a0460900c1c0302c0200e069005030b50b0010311341c501a03410401c8503041b2154000154075042c0a1820f800324105e40707088989094015404085c1051840a040c00b2903e40c0e0070440001c40301007a6510102650342d1100d040c40900300384034040020398100000c2010550001120808060041566150246d84c020b25801d4071025a802d032a41d400000c010803072642c14441c0c40e028101c03951005060342c50b00e00f011940482400d100d0000207603002002484c0c045000e85440b019580c000460500810410902c900802c1e0902a101e07c0c039810 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 663415602 1250 663414352 663414373
    0xb0a031110110a080a0512090a064a060c03090105090307170d180c14240705031314130207050c0d050102090a0303030f060b0913020c031e03040302 65
    0xc0c003202c622640007440100050b803580ea483c89015400100a441080802d02c240c0d90915a1001680c0c002c102c0200209641426400c1000894031140400c944500c22045002d12149601c003000b071820700076441200e00c00d0f1212403842080740c0301c2c2c3c100f64407500403d030800c8495010500994017601d0240e0003000b681d50b41042c1c095a9100742d8001601034139880c119810b040785c150008040410201c0004170303100111820038017402c204140200d60112280d41c040c070066412248650a284007101e03840d0b40c1c03403500c1c2052920010034403a8994048000903143c81400f000300b0840310f00405011107952481d9031082a55681c58054810314071075908480808010b64550080c0e8071001c1d003000150042d000e11900b002444009103a04a80554081c01409484d607280c494540045000391004120303400d94013a00411101580c000805003801880803510315100d15450301c140b0355030034100613039501c100300b1050b285001d0b0b02c00005001080e4840104071102c42400356000380d100e9003c23110101c1d807 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 663416852 1250 663415602 663415607
    0x14070e04180b010315050f04111504030b040b15061606150f061e2c0306010b090a05041119050c0607030b0f031c0f050d0e0309010908010b0609010804060b0a031110 72
    0x8081c0d07010010304c00c015000c9404166221004646008010550341a0b100c82c05020074a1360400d50068030f1502030030741044103208142400c02e902c59130360303240600b0b00c094510c0052454010a80c500100031114240c18042104592021901c2d11002c407403050b500f07071744000c2c09020b411035000c0e843c00145800340c00213030001c20005038485201e068440d140346030442200351364503d641d1a00d03501d11509502d50400203031414840c542c080d040c0f107400d080d56604803005108281d149503020740c0c0a0341c64400002c0d00d40c440d0380c0542e880303040441c140314040302103403a084420340a01c943c842e00314000c1000340416a038065001c1d042c51201030790728111038601e5004141d110b286020310bc1d5240301c00b01c001119000e208185040c4000c1c41030400b40d0070b11501c90040c2e001c4030407144d001c0d40366600000b40e0b10803030341e0081c07420310050014000a0001004010100d4002e014144604e03050103200c0300803c04000f29900543c12413075014081c02146903a0381080650405001c1d0b4007402810b02e40450825a40b = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 663418102 1250 663416852 663416861
    0x120c0e150f180405060121170a0513060504030b0c0304200105070609050c031c0504050d02010c140105042006090607050115080d0207060314070e04180b010315 70
    0x8404502404505508820700c003034401520452640288515500000d0b14000120359000d41d0003240144020740c141091002c141104201040c20200d4010300f080014040d00030003011840103a920700e03100e0390b040000359050b0060035400150000ca003400400c6c0d080c0c0c4040038000b100d004480c2082c2c01c2c0c41e14100c010f400e110940c0c020f44108102c1403c0c0301400f100d607100f44111501071400920b0981c03207843d50422101001c6081b03510b038003c11a074441c14a420000a00c800c50445440a0440c903414405841845140f040b58001c0c1403401440742968004e45941d080790342c1003400a001442040480d6001700300440d801c8900001400351190801882e45a6104601018150f01d1500008108100711500710705403c680d0b0f9034a400d090121070301c15850303c0300103146000040040c2d181c80c4001a00f41450707600b00e182014582400e000d6004039a00d0100d40046880c00c1501004181c10f0129014010240c0c0046241c0c81c981800380401079032600c203034120390040c10071006040201d4021010b85 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 663419352 1250 663418102 663418111
    0x60a0c0e030c040b0109170102190219030e0d122d0c0303050c09040e0d030b09100501080403030e03042c0601020d12090506040b150f030d030c03060e01120c0e 70
    0x60380105070b030004a050035800800454414107060102d40c7d540e6591a8040d624040c0c030304034503500895200381e520925429804010b51030b0028000c40d1642002c1030115440140c00074003041b486002410494031070381003e51a46400500c40380d400210620f000e014544894280740ba594113112580d007011850807210010217807540d554504128250310210050640507011001528007082400603582c1c442c070494404119507009040d00441072000039080310f500c0001940944d100c50100f040d03544c00c1c1403621058800900b001c41c0d10741c9950404500415140c411505988000580800c0c4003d690781d29a0808034401d00e40004e00660034501603010405842d00c4d0b025034820281d401c1c0c0c403405034541140c10310a1040008949000740c8072a450004150750070703111a5400c00c1407007090020440414600d14064825101c200800400710f0741e02d4459011480826a48400c0c0002c80d6100b0f40140c0c1c0100080042c186855850300440d07903001d07403440402c49030380b2000d10000440202c0100600d104 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 663420602 1250 663419352 663419359
    0x20f011403011a0c0d0206010f0e090601061101020c060f060f0a080d140705031c0f02090109030809010926010e0f070302040209011b11040c09082505060408060a0c0e 73
    0x569203010b50100e0080300c1282030000e02c500130b2190800112040101c4440c191503030b4010015035140180040c550709143d04004202c0f2403950030058100400514581102c1051401141715100000b000b4024080d2002c880b19600802007800000c0340911840d60203850202c03145105c01b0724a00400c80e60348044d10a4840c80c0e00220042010316014000f040c176507901c801030080c5090304980d505c9041d944945154a00d0b05401800528002010310800d8200204190304510b400d40c1100064040d42003444002c01080000400300d0060b445400d0305401010029406480f800d20904860721810280c84071425541c0390481c1401c00400c00207030010303401c403040d01030489a401d5400b4007019500c814011030502c0b818540341e13445080240045403030f403805100b1a244541848041000381c842c15004c1c0d00c100a400030f018032070b1201c08a20034450022002c1c0410300c2c80c1c44802c4000c80200329a0006600903000b180014400c00c0210b0402d1040b0007245007081941c020510507a0070150b10340b1410340 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 663421852 1250 663420602 663420607
    0x50102072309090c090a380919090c031704030c0605090301110309030a030e210309070312050c010f18022707020c0102010b0f0d020904210507020f0114 67
    0x1514140780111540100c440340a44d40001c90900c08952844410750340c00041903a240894180240c00340c1c1040c08452200b0000050314084440001054151040d141c1c8288050000700d01c0c111900034065142140240051244922904000903000a148001d071405010081644c190030759030005c883c01c2c0da510900c01421182071170009c440c5500145007007a059940c6118030048041108050351180c117401002356036450007140d0003426a22a280b0200d181d030300c0420003500d500442c0034a4404000c4021000d82c40b40d1b900001c2901e002c03403603480502200546444a4099070303111000740a2000c1902c02442180c40810a110841c1d620300343d111000400c81039240014640881e02d01c0c07078000341015409400d00742030708400240f1425212400540c0c0860304185055030207001e5184ea000e4200c0d00c03040c0d0f08e0910300118a5428014500a01c0b441d981d4001500b0002c02e800014401603410807400000401103601901a900400d016441010355090001c01503109605154900100708203e60 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 663423102 1250 663421852 663421919
    0xa0b0d1a090c0705010f0228031e0e0102040902040b040501080c0301060801060e12061614031006110a1208100e1302010509030a051624050708071a0a0605010207 71
    0x440b0740c00c12407044695541726103070762007120240d0000c0c0c1034980e40e0030324015100320340712103030103500600a2100c0305160030f00d42842544c0c00000e003050001c0e082d800c00866500360807c2490300911842d04000d1103541b01050100b20580020003800940300f00b0380303c0c80801d445900006019020920424001441081c014442d240c46040a0101d000014240074040d00c150340d803075402d01c44200c40c01d43c181001b0a8a03003e000c1d5114031400480c1c0e840c48040703072460400900c074013034984503801420f040c48181d41c1151b101110402106d000b03140c000201c600c20b10740d485001003000d10182e5011418200703034031000c1000c80302e0041f0705001c2d806503070b161007201d2420f030b0042da502d42040813030703e51500403e010440407900a0101e800d2981c034040103129071a0400078180900c00b4616050014074290103d40c1020350340041c222403595401003c4151541c00524001243c14070805c41f44102042220a00c4003444441d0004000c1c1c4000340c0a4500b00c5803600708604074203070a129140805171003c0c00700c8 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 663424352 1250 663423102 663423121
    0x1020a020624060f0712120510121202030c070b0403150c02030a0e0a0902041d152823130203070518030a0f08070b01050a0f09051003020a0b0d1a09 65
    0x130400d02c13110480260601c075940c2c4840c10403081d01d989210220740d44c008000c200294900c82d0b168400b4024510001c40c5061180c0c45448004880001b01040034194104031518003c1040e070340b544500d0f0307085070346403911030741c4c4880d0b541c001c1c2c48116040145207035174030076414040c0240711180c08581e0044d810202c170701804945907410310f50000d420842000e404590342c01240004c00c050701070b0906010b120889007101e2000d40c03074020168a0140e24900309206e917642d445205440e00105004401c00c6810050810450b90819521240030890000307800840c14076080c1d50307024403000c111803254285100c60621800c4e80300454540c40022001c10194003071200e10b40050032113081c09012100c4084060740c48001a0000000a844291010807554200101ca01d41e040c05071005585411480e403502d200420b0700c500c280201044103440f1800100b0401114101d4401903400420600800360f8402c0483c0050344404185126141000511030303054015400c0440d6000010b0450b290664480340c21 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 663425602 1250 663424352 663424357
    0xc170601020d0f120e070906060e0402030c0702090405190f051c091208090a030308160e0f0d050a050a1b141f0207121208070314160207050d0501020a02062406 70
    0x903071304030b2903441790681c0a80e03400700300d810082c028195002808a00300640030708092003810226224030b0040041041804056066880035641a9005440c0307850b80e1410f28281a00c0200c01d201c1c2c4800c1120b00c070184003280e0140a1042e00034130942d071110803000d110b0003a4075100354000011821010301000050156405402d580b40640c3c84503080400c3e1070700081441100b5071003500000e5803002440058201e680c05600f42d5281400c24005440300c050100781002c4ca25501c0601c1003003100e0a4000740903060044150b5540d01c8415a08042c0302490442c0c40f43c003500944c80b554031321902000c07a000320b2154480c02c45540040441d4070040ca92001c50040d00c100d10342d01011401107050000e0483d40c080054001e052090600c0720301c2091941d0028624039000342000b08050030040c4502480e81c503640c0d4150011341d102d942c1e03580c01410020591500b84140d00158011030205546c4040c02010750203407500083c0e0740d01340ca1483c0c4444204911613961944c0540114a109080303820034600302d0300 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 663426852 1250 663425602 663425627
    0x90c12150411130303090b07050c04090f02060304030f0e0109060806120313080a03080a0204031e030203040b0a020604061404052e18020306011e1412010c170601020d0f 74
    0x20071201580700076040c4a402600746007880c0500001c3c248209a00704c21901c02501650072014106026610f4030780d503075034507400803a0180c1d030385103954001e011040000306281500680056031341e040520300202000315040544000410b8007048440940c1300f074582604442e803daa450315a0b0302d42c0820010100081510300c4140e04c02000030340c400014242401000b401c0c4c00004d0140c12032282000f5002d5000140007902c014030400060001810a1a40c3d13a00c818140d05410000d808a2a05070b16501c03881e0001401c040c00450010704a540c0090f00321312a0b8407540e0140180c040c028941c210550065034010070340c0c4c00c11040070340035213002d155141d100342036107044143c0d60b86007049440440d1a8000103118202c481c00310038003503045c108030711801404030049030303044610324070f1115030005180d0054070a072410041c0c141841d941c0d003000c142007280124000301312010700031002400c01c940c006840200f000040c000a101980003007030307030220341003241c42c3c80401d0344070a0022520b102c4901e0 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 663428102 1250 663426852 663426859
    0x20310140310050702071d06100c020420040305070506120402014416050409020d020403020a08060f1302091b1b1e0a0f0803040309090e0606090c1215 66
    0x140d1468001d02c140601401a82e80350041d104060914407409440525510500c1c151035100c020f20061b80c440060804211001e49000100c070512407000030040e01410488000c02c0c24070902c5d80e1001c0f45214001e10441e88501d044523619540c42d4180f02d910700070805014a8039801c00001405540518920306503240119162040c041c00b40e160101e02c0000d0144000518090840d02d80b0080d48070500b803508040600c41d041e1240c085024000c0981c40786000303d9078015004a00c402d000442501960080c5034014810207aa03030f10b8010440d91403208a4002d0011400301002c1500f100c5c08410851031a034010307206009540c0c4011841e030b240c00328400c0301859030004016080d845070b05c1e075a200380d601081102601c07100c144803a500301d000080c4022100d4941140700418001805803902d54403a950086401d900c1c0d039942d0400b035070020703025400400d40c0303030506c260440000808100d0314440ca0040702d01007515100d4900c03503580d90060000700035043c0c0301c003404200307906440115029a424000c = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 663429352 1250 663428102 663428113
    0xd08030f040804090228021c03020c030c0703050109022404030b06011224050a08071502070807080307061805060a0902060d0911090901091203020c01060b0a0c060e010203101403 78
    0x526014080b6400301c1d190307814001001013a00d00c2d40d6021801c100d880351580c4024203184011251000c0d40c04c2c40c1c8d0030b44e5400c2c90360001e0f8604110360180f007640c4017a046901500e4134250b0ba41840d80c013030250741804074451070400030005102089060030701e009480100384d29052a0641c0d0f5030b005200000341850381032180030813504d000c0000354010014450b44809401000700314459001c0d29800e01c1e42c008601c0b5021038042440700c0e8100040200440b00a07018040780c031541603205a05040103038004840710701550b84041a084000001054180c0c802c2c0d000f0400303840c43e11460005440070050007400c8ad004400442c0507141e0381d8001e0850f1500007000746180c48400311401007101d030042d4040310900181d811011030b0b0b2611808441c1e1144200e0000d001d901159910145502c8071514003c0c1415408aa00c42e0400002d50205010304040c800380d0b5916000a1000344c8041840b030742c110381e05414602e450110394410700035a030041d840c81c528809006c2c203242c43c0e5030760303c0c000152050701845035 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 663430602 1250 663429352 663429359
    0x1003030f180b09040c08011802031312020322030c05010c03030b120f013b100204030b1602010c05030606090d170c06070801031109420d08030f040804 66
    0x81e241900003002e03100e034826a00d880d02d40c03c0c0815030300c0c2c410266041c86030000042002451204a50201d142031220040e0340b59142c183c60300b40c13000302c0f54014000c0e4080300e10011003140c0000c000d00002d621034005074210010f504240100d003c140c0802014202c0104003001036500444c2c440c0300d607621038100400c10517034140110382005500584500c580d4080810040c40850a2041a00d2580000d000c3c8041107100190050b440b6110490210000b070720b80801c41d003114052140e1055080010410f650b62a1749080150102c81e003620744926580e03a15016528480c014441c03202d1200981c0c0b1003178210b6842074200711840d080081499000760039141c424001130110043c00b00e9014181c450a80c0307404410031542e1401e40b008000b4018040200018008104412400b4040c3c000071546404039941e03200d80c080280c0c01c4460100034807100c12075500701c4103803112040711042001b0703486101d850804504100f0540382090019100c000f0800100b03000c501c540700c0030390740140a6015070b40307015034 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 663431852 1250 663430602 663430637
    0x12727060c030c0201050c1608070f030207051e1806030a02060f030103050c0a03051f0e15040b06030a03050906070c0b0a080f010b190e030f0d0e09010602061003030f 73
    0x5490211141580ca04070100d10341d4140c0b140c3c44500c00da9100030001850010216002449032215840c1c0a0f44001408070400ca1030344200c42c3c02690008540d2840740c9070303140c042c2d580c10081c05034501c510218005020800040c209400380010020700700407a0180c1c100e0329101c6a040034000307980500400a101002d61074460042c00c5221031001c00958a600d542066400c040c82031680a100e000204800c00c041280054101711082d03051000250744c5480802d444c0c000c20010007100c03845d000308000c00402400131107405202e24008c1035044c03c40c1c2e942100301610740a072808010040b80045c014942d9034100403010b845120f201d140d8a442d20b548400c01c001c15a0050803500000070f00fa40300b08400e2800368bd0300b803801450802855414502022050502c40c104210301c00201702210100c0038403642c0410a104e03003440c5d00c40940f0381c4030072502c10040c101c0d4248280c01d8000d0748000c000180451000406a00c1450749203180d43c48176045036000ca40c00100c403208241040304080d11007403200c0 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 663433102 1250 663431852 663431921
    0x501020c0d0525151d2a0405060303041e0504050a0c09140303070f140f070609080d080402062215030b062a10060b04080114060a0603230a0b03060127 66
    0x80d86c1301c0c44100d148448518640100c80e0000658051400c020911100351000000d90b029903071003850f81014030000a21311003480d040d607403144c2c1d4818204000d0003078140241d40800011105a59450080b540721120010060f40a0724002d4240e03008100c14030210709007140b08001d46105800546590140c3d103102d904c1c0c076861039034940f6540c0100d01c04100d4503070800003c030f000b000210054100700a1903d009001c20700001c0010b4007440c00010810800d40150114000c100e41c02191002d0003610b0300000c840104240c0c00704d41c01320745412111303403e40c0341c80420b80304162804020918071010059090802041c480e01d040b4441c883c148001841c1d2105000e000702401e00b402040380c5031481e1440407800d41b01d200c1c103110384001c0340b10248851510b0300a541c00075560541000314001750001d0307905540c440d02c16800900c0c010403800b40034820505400c20f000c40007048045806590301c480c071081962600b90f0b0004450128050040149200e981087c40716000c450044050760b440d44072000d0008 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 663434352 1250 663433102 663433123
    0x907050301120f201c020303040e06190b1c0917251b060f02071a13030b310b0703020714100f0c0909090501020c0d0525151d 55
    0x50740100307241561350030b100c85002d240390a201240078440410342c0200c0e481c0d01c1031b400356105161103100010110f80f40c0300920b61030f5182c01c240700c18020382c2d98002c0e928103411041d03911070007480304000d1000e182c5070b601510355080d400c540380c0c0701c4d01c01c602c4600c0e080ba60b119254007400d503603a03500c86106c0354903008064454140655000240d0241d40340350b5011601d03503602b1400c2401542e10000c00f9150b40054010162002203445c1c03144200a510769442d68098841031b1141a0659500401004600b4400c107000e25004095100704600c040302c0041c1e18080d115140e140c41e10b058240801050b140300c125a0442007508005241007819102c0c03440169000c040389416521000e8000c0e01058203200340f04010380307001c0041140c00d0000000801404541c031032900419100c0d000070040c03040c00e50450300c0203c11380b400c40301c20f41c042d40400b80141d1c01c801c00e9010400c5030080c0002c9216a506003400380301d98003885020030109904044001421030200940484042800c4507451507801c005c1c0d510103 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 663435602 1250 663434352 663434393
    0xc06090706050c0c0f0f0d121b030e0f01210b0306010902070503030c0711090a0c1107050d0f05010f02190e010201060b04030813090203010603150f08060f0405010b0301020a0e0f0907050301120f 85
    0x42024088d0060032003181c0104001c0303c491900c0e55100440d81c80302d1410309111041382c00c4112200a00012505250009070314100011841901d9071800a15405060f00d10401e406481241c3e0382d411200089028480c2d001d4126042000000d01007030031030005005161290184044035449540424442030044801540280d070350b81c500f2150035042a40520400005c0006203411420321022034041c9075440001480429440d401c401041030039044802600c80c1800c0454880c14021040b2100b00d200504500200c2c010441d450340551060041e03000f9120440f10551806103144d40341c0d18036602c04a20f040d482c100340d81010400d008507000841c0240990754002c2040c160103071804102d40c0ca1030b80620503d00c1a0701c020042207001240256100c002201f2282241e600c6080080c054182ca80005030703d9440021640c0c220b981103c41015030007401d070703031540190103160103002075010145c0f02100491000d1004001909009140785100c6110705102e40c017000c800c0da10281609401446403d9 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 663436852 1250 663435602 663435623
    0x20a11010f1a0f060c03031f0905010e1302060d0905070515161b0e0709061e1d01020703020a090f151202040b0f060c06090706050c0c0f0f0d 62
    0x8a264090040c44a410001401000070765602440000281903600c50b80e030040c800301d04070000554401c070960b0a4541d60340181c9980e440c0071500f1402c903e0480084c1c54004040d80008900403520f407007228140c590a842060791500c2c1d06e14017043c1703022026800c0303a00007402c00c92168507030242e000700700c1c005110340c3c0102911400c06082100c180e07100e90440d4041441400302503004465484001c3d81180c0043e004142503450b1082c0415581d0141c1080f920804400113110645d2303481000034045511903a6096210200300300c0c038107000007004280c1c1002550349400b031082c1030780d000c02d1300e10000014011100c049039030344d02244103401d241d40a4805155114002c000c4410359000e1620000a014910418141004044044813040d41000381c05269580c410031101d807908901d00107004002400c26843d0b1808400b91517894004a50b41c00c0701e8003d8440010f07829000d202566200c030b03000c50103401070000f0441880000114405002c1d0b1007070444180d01c2d12511000003869405015000104 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 663438102 1250 663436852 663436877
    0x1113050105091302090402092d060108072c12150603012409021c06170c011404050405041a01060504090e0c060904020315120102040614131710020a 65
    0x1a50507401440c1d091403561041040c001661405e0441c0e40c8503904442d5400c00e5115041440100078514034441c5c2c02400f010f42180042480600d03076072040509903140c001c96500d40b0340440d41e41240031501c0d140c000a0400c20489004800744210381c041c0c010740717031b40350740e181c00c002c010319042c4041d40000f0005250f005102203800c0038021203402c80d0941001c00c000032912540d034491800e4074440c2c003c425a000c212040c078806d20700307040889041c60311010300200b900c450320200c4011044206042e148030b5044d8040f610f500802c0506c1d1110110310300941850f03d040c00340405480010821a84040c071200100c050200303c4100c01d004c0d00450307503119281d60500100c41c04441103c40004400c2d4400075640045035a800200d80400505072405a2642c072a4104a2006040316640541c01100c00ba01e000001105501810886003555926245112844450410340c400c8800114614280400c24000a0700d80c5035190268001c070001c170b82c0c1445c9054003a4080b40c0001082100107500d075514003 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 663439352 1250 663438102 663438109
    0x30c0e07120213030201091e0e0a0902040f14161e0e18060306090601142206060e1e090a0e0a0b010b031b0a1e0201090803040602030f01080a0b010e041113050105 71
    0x3d201905e001239882c2240031035207003007071422103540c842d03041c05401000c001001e54145800c45d9958541c040c4c0148080100402180f003d48110801d419050580f8800a08801d000c80c50308100d11149484a9aa41c84038680c114480c45020342502c0c1402042c0c8000b408507180c002c0307900309088d11034284007003c0c1814003c060400c04e0203045603081c0c0e0300c450700500240b030000f60b1302d191140d0100d070305085035408819044407100003408502c4010303150060020321a904805c2821003424221101c01c1c0e042090700c02150048200d0250f1604034602100103040c82c28941d006542c000015400c42d40324646d0707580c0304070941e1400d070400b4045140100a0207040300d00031190708140c5034404155400e00b0400c0038000d0500084a00030004001040b491040300c1c1d00030740c002c8036140c0d0440c0c2450354924240c00e002000c4c0d401a42c0c0c001d5500310b540300000e009240403d0b101021540185000410391900c00000064040a00241d5822115000305045a581c00a422809409145020070958580700c00c0 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 663440602 1250 663439352 663439367
    0x3010b09091303091e030510050108010e0a0302100b040e0a081801031e0510080a050a05060105090c04121a04050d020601050f0d081c02041e0609030c0e07120213030201 74
    0x61685200c03a0b100c4a40010707411050311401e6411000c820300200244001d40303a00c42440e0360004e4024080e515030041880e00759081141641c500c03c0003840341a1910344004e80d9001c800c5009001608940c10164183c84141c000d0901c0d07603001000884c00014000c0c00c00c0c106040d060045032202800243d25000005408030140e18060901f0100907900031030780480840081c013410400c000d83e48900140e000c2c40d090b9481405802a0401c4031131024040c9005541d0740b854000981d000d00c9110000030b0103180460340341e40306101851281e400e01d0320741a501c01148802150403140ca14803403d441180e44841002140300c2c40c003400042c200040e40d000068100401038003c58010034640325142e41e1a2a092a4030125503032110000b50b80d82e244221640006149000d0714002600008001072b48107022020708280105121001041c00d81c6d07154240c5469000e4800142058803d500401100700c0c17840c2c1b056401741c140c0c20403101001d00da0b0442000c0341d100809400c46981007100600655900449 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 663441852 1250 663440602 663440611
    0x40906060e0103031214010509060d06060b2106010906050a050f070b0109051803090d060605030a030503040308090703201306030606090f02121303020f010507120b0d030c020913050303010b0909 85
    0x101003240d04644410342e40c1b044814050366000b0036290000c00e503241c80300b2218822441e003100041004070745990384181e20f54401e1152070070f00100000c02e4a010b00c00425504c1c081c070416110261101e1420000741e90300d0300141c44590902400b40129078038010200010f0118134400da079603140c1c643c10303d003d21049400250180d400c0e00620810944061000001c5903026003080701c2421800c07549241043c05045a40c0203141c140c02401210300405030064042e50055209480e400d00c155202c4040a03a16500d03844054041c01e0711080282a6042c00d101d43c29038100c0c0540204045140704581d03405071403186e4011552595a00740421030403804d4030030002080100801075142c52450440c2600c00c80d005402c101a00c01622421003c15008100c4c210700c00011400901c4a8a4980300203012a1036088003071603072604100c1c50b801304e864601500802d8541c07540710480c040e0429000c1c4000c400d4001c1883c2c20b00b006030f841c0e1030301181d4100060350003070840c411403907580e15103c018020342150140 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 663443102 1250 663441852 663441887
    0x1103190203040c06031d010906050403170403080106050711030f0708011b0815030a0516051005070506070f09080f01052403151b2116050f09040906060e010303 70
    0x40c000042c203d0f46400044071540d24000c00e11301d607188512480c07090f02061030036096213066024810020b40740c00c0705205a00a46850400a4031a10802d4110804480013030008440304014000325002e40043c0101c51f0141f1070901002d03004202007850250000e500703581d136900c0078004000c0c0e80c1d003d0091140c0c03021185d0580f0f040100034603014250150141400440e4100340742044000e131001c11a401105411074221510002c8802c0b0424403890ba501582e400b6501000741403440354003038000c89109952100080040340e603108402c88510600e46500c504200480340700103264071007000243c051010490000800c0c1c01c00c0326071046250701c00040b039207844c1400c03c0b400e0300c0340e0390105040b0000703041e5207403141507640e91090600009640b0216003032121401b05031a03036500c890040e0310a81500b032071921026511803051000501c200d00e1001c80000b407040020040707641030900500295400500007260b040004d42d1820142c407100d07000421188550b100420030b050307200528214040282 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 663444352 1250 663443102 663443107
    0xd0318141c0206070209040b150d0308150a0b031009050609090d0c15020d0c020606030a0c261b031606090605161a061003021201050d0c03050111031902 67
    0x1031010625240140d401244058070800e000c00c00c2d900d403c02241d00c215401800c110f014a480d00d8000c075500780c03d45401032555040e501c208030f40d041c01c50a0f0369a5a400d9211001640d0300c0b41a626003a402808006400640001e000509116968061806141c0002c8a1049242410444401c94a0041103148110505400e0128804011588031401da5042ca03281c50000d00c1814580b5040d140301c4107048010f4800100204905610790002c85074402903030964415485000400d9628400030401400c0103011309020442d0703103002c51005003c151086048801074000364a1541007100214980fa00c04544440300303d00d0f4901406241030207400c5008090f121424060b00a01860300741c005c84042c424001001081403c140c805008074a9002081d4456085010841d55060303209440d454001c5010013400f4a05034064002e48000810466050b15070360704e4141000720114915034142d5135400d12810105c0030590a01480b03001082181260307a0324206643d403e003009903040c3c0038400d0f49106 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 663445602 1250 663444352 663444389
    0x1514013c05040c140d1a0306040b0606090a1e0911040f03031404120606090c03061409070e090405060717040302060a0b1512100902040503070e0c090d0318 68
    0xe10006005a45040e54009081e0110b00400d0383c050b500c84004202e44000071441e546030fa901a00b2a800301070006c078260f82210440b20605584500130b48004005850030341c0043c0d5a81005000341c001d0103001003d03080c03000d50347c8040380e4035100c01c002640b8810b02001c1060141c100a4046d040c0c40c000f00061891900c1e00d03200c0401c4440e121800010100070b01048214111280da6003510302402015a82d101088404e06d41403004051318030030400c0c0d131030412110143d098003e104820464840021b0f1010014450040112b83c0d03500071714402c1400310300e04c10940d0307a4a074010a0f5101c1c921850086c00d9508003083c0241616007170314402000c1c8400f20042000003540451072030b8000c001c0e0100803820300300b0540090040f280159a8018981004c01c0400c1306000b803900c1e19008803446100e01881c0c945805444060384900e024494265000d03400030841c1e20540880c465021031b106100c01e040074260400110440c0c030741142075001600a262803130150f46500702c0300c0018000d83d0302c1c4503044001c = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 663446852 1250 663445602 663445709
    0x9090307050d030902031c1e0207080c01081906080a1e1a18030c01145a01060206060a0311221503031404060507151401 53
    0x85100c607a0080584410002c0d017152010481d4079200041402c0100000e00c03410802058491744c076600c010f00d00c6800c445112201e0001c2040c0050700c4d030040c00342c149094000015a0805400f0b44a04005148041500003424492140700041d0a40704042e00b882a090b003080c0807030002e1043c4071001c9001842c00c5e00c0014210b05810b10592490440d200006e544442000c144901c20505c4040301d0301000424480095040d070081800d82180c0105190b9500d0300c00001c588000c2040c0700c000c40d845482e15011440070981c0c0d1900440c0c50000f440d0301d44a40302c40103115059150004c003603030301c00460b00520403950140001da41c09002070b0703180c0404074515181c030b5070a8892000110300880380280382181103a0800300182129080002c00e000480c3c0c1300044608001c000d100640c00900b420f802022010003440c201c404031388117903907400d0500c20103490728000703804843c03a840c1c40f443d5200c0a01c0c050410035000d49000301002c1e10080c40600088100c12140d000d903210b2103190521286882c01c2810 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 663448102 1250 663446852 663446863
    0x1b2b02010525050c0d05030a15030b1810060308040e01050619050d09060e160b072604080609150105030c060d020a0c230709020f0316180e01050909030705 68
    0x5180516400201901c00a40f4244503456540c199070054040c01d00c0c01542003030080d4060311820200304078028015030710b503070358841d54040103006a0100b40030800400c601d0b030307240c50840f9100055611001a0600c0b880031520f055104440f02c0002003001c100400005111500601e01514003903e41b240d05110544150609103421092003404200042c1c4054203500c0310700f0503035000c03008012104074451403503900c4100c2490a02c1120f441c8201198200c40b1105803200560f01050081e82c5019110000c626a104007000091420701031100217113542040090b1030159110300c0140403540307100030405440c490143c1140d40203a21400f15030406403034030021120794000b007140068039044440e004880c0750740d00030005041401281021900f10341942c0304414065080c6040720081941d59100c041030740500080ad0300070703890500002c7d15210004510f0001d0710315601d42031004a00303101212802c43c800340c10485080005800500c07543c00d1503051543c2081c44000218186526640d840342d1b04c0 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 663449352 1250 663448102 663448141
    0x306050c0f0d0911130905010507022b140d02090f011d012f030d05060a1401080901060b040807050102100203040803130f0c030602031e070909021b2b020105 69
    0x40303607155840c030240b10720044490380769140149017040030140721102c48090416007200b5150f55282a020908a43c00003a1150b010016285a0403001441600e0803220384035042c2c1c149c041c0b0040c074482003002280740c801082540c0300c0003401070302c54001005000f0084140311103141400429101e002e041d4003109da503c9954202441c0a8801840122001ca42440d11054042c2d80709904002c502048078040040e296403d4441e4080000380d031050100700014415105e02401c2d00b900b4600c09400303521505546500c03003400d80000c03800ca0741c0e4030700c500543e600a038800745c00340c0c2101105102d02d46e41071042490b0f10f02440400e5081d420a921000c0e41840041e0948001181601906040204840f03c0c0c2002130341002d801c103209546d07402d1140281d401203812071440710317a8517101200091031242d018002c0750250b40306103213141003000d000d000754800071000c055003c114605814040c010011349003080307001442c2d85540c0e6007a80791119101a030086203c02d690401040044082030780c00c0c2008031 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 663450602 1250 663449352 663449377
    0xf050636030c0d020a0323030a1a090f06010e06040b04170708060106030209010e0915040e030702040908070501050c040b0702010f050403050d0306141203070605060a08160306050c0f 80
    0x101180000c0646184194446142c031805010300c42680d9540105078a21002c1c042d0711070741107100c010031044d828210365035110300000710244003107440098590f0065211604510240c0b00c6d1008074000514051340407500503010f51508010442103503440b81c164120340c0420764620f410306003400145034084c080e5014490004814404c804d51528041100000414508041c0c0e006540c440340c2c001c010b5800b0b0030245002ca41e03002c0d114422414091038181c0728540c40c0300030013604200c070400c00c03000c0d104400c041c89151100303000c2403015a0796840341c07038403041c841c283c8030341d5543c2180707440d40c29500000e02c00b040d1840e040c4010401c51100c41c0c00c651f00c4550900e0b004601c40b40080c001da078075000c3d0b500098020b106611142420540541c0100280c5100300084d60b50404501c003044002000c041c04501160001c0c003d043c0000c0e8a43c01403500402c0042c4403500441d03c2c1c2030705500d81701d0ba000362030f88004041d940030014001c040c40366a8022918281203440c041c4903005040700381c425204404036 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 663451852 1250 663450602 663450691
    0x20301060b09240f070302010605030118110904170c030c100516050f040f090f1a010906121d1509060103210201060803032a072303160f0506 62
    0x10020b250108071613507140b80d13107403035900d44c103050400030300915450040d203000350300c0c015150b801a01122003c40700f01d0f50120707100b086415804280042e0070030140c0120303a990200000d40c2400407108002e440d00008880c0110744030040c03054568684074890702101d0141d440c150501c4107850f020707080c0c100705030310504000d6540c500707509003183d01d42315551040d8500c040b004d1000c10302401540040b050808440d00512908030801e4400108000007440d0501041c5420000c01003240a406102c1000301400800241840c4131044100e44000b41c001840c203c2e00003491003c042d846c5c0d40c607515000102e0600134421581144e80b40d503030980d030f4841c0c1c42c20b10f84940d0034076a496500c01d4104030302921100055a441b414060b014601020400403139103088030054a00c0c007010f40090301070b110780c0c1d43c200c4004140300c1c42540d201c4003041803400d0f030608580020462041041041503401c20700d0b600c00d541d405800c007010304040b400d001014040200d0a51541c1d00c8041e100e0110340500079090590400300d0 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 663453102 1250 663451852 663451909
    0xc17180d0506070f1e0906020f07140418060507090f09090c090509011506020f07060e030309060a050706111e210a0603020306040804091103010305030a0c030e06030f04020301060b09 80
    0x100c5c0d100030b22081800d09045000c0b100c2003264814002d03030441d1850340032543d040035411481d54803034a0f43c1c016036980300354002d0010154034280c1c02003010745c00e810300e0800e80f480050321307040300f41c4000b12441004241a071030300304000501601c1e91801003010301d0040000d0380e556540c0b03000d01490380c8036060780e075500c0d0b80100d0700e42242948151003102d0380ca409207000aa440c0c01c01394640000310301d848000d024001c00011440e0181e081d80d440c240700203000d50710781400c9204011168004030040781c1000024070151000500b0744c031480040302a030036009601c55040d000c4d41c403010007a031492010070ba4404d120805001c650025400b00000000c0c005900f02d40d55000450010007060344045c0d450310031340301480184410742000340142c500b081c2080c0404410082e40402d07074482131100921315403041040090003413040d0109100c903846854540354805076900068940d030800e1f555044801421011b0004600d024800c4000501c15031020504102c0d0010001d0b041c0f0700007250030807403190104900c0 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 663454352 1250 663453102 663453107
    0x12010e1005100c030210061a0d061d010302030106060f0f0c150c030b030712080f07051005090309100807090317090910080f0613080a0c17180d0506070f 67
    0x4400740801a1240801c010b40301c02c018102c41c02184141c02500601c0c1c1e400320b40b03e0103030240034151880e0b142030040440c0c0c0b45000e80d0040e80a076000c046a44d0742c8210200b020728144500c550003c4980120f0300140d410350040600b103440590014060040c2c51001c0c40d000c5400815400c8002d016061036075001401e03003005910422384108610403246001c022029640e05a03202944a000a034200d0b2038054688010b19203030b00003110043d08032a0305010140346540d45c2c07001440c2c03030307031061003600d1003d170481d00000c0c2500d100340c4241c140c41d000840d032a82d00341040f4161240039003107450540710b0390410042c0944846c191740406030001100300f802142518000044a01c141000b070300d007448528100c400e0507000c0744135004103c23031130290300c400103400c4c0c40000340c407802400d8070250b50840e1a026960302d034096010304822001e1090f030481c004d01140207200b41904400003078025656443d40200344642200030403143c94401c144100400d000f1810016403941c0c4000309090040c3d840002e883e05 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 663455602 1250 663454352 663454381
    0xa1a0d02120304091d03070b220b010308040303030c030605060f0c071517011a0d02070f0b010e011e030c0603180602030c12060907021c0507060e06070807020312010e 73
    0x210711510000800040042d0281e1180c44480802c0103500d00580300c45200a44a00c40c150000d0f214000310310200b034010855060542d00400c45001c03081c10071281d13903102140320209a00a640840010904109068150050a0b109141032508201140c00c120000380035014004822040940c0400c00340f002103010020314010b032080460510441d50030540c01420401c2003031900540505041c00000c9551514410f0785041c001d201a9a042c1030352141103c000f500003240076140b480e04400280040b07a042c50829010b010703080201200d0f036050224695503c0c0309001c0c00000240100010400702d030072800400142d45030f40c07801003112941c3c1e40030a8100a00b0100140c00c6520002c203214960305400d0003004810202c0c2d0b41d40304156143c03002c00c02900002c0b104180035800a42e07044003405a002c002d110301e413125040450821441e501d9850403642d4003e0451400d500c0402400307080c0c0d41290030305920901c244015841c09101d42e030042c005072010f119014011100d580891100b404a13005c = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 663456852 1250 663455602 663455629
    0x1b0503090109150504020f1002060109020708190f03050907030206030609150a060f0906050a0e09070201020c03130509010f180510121109150f0f030313060809060a1a0d02 75
    0xc3c480e410591100e201c81c000d0006480032445062941c0d01d0b04a1410400c3c2451451103068015001c141c2c6881d03800e8000c2d40c05101c0440359076108000c02c00c030765001d0200782040b100300fa540d203034035810420001034108d038409001d0094582c40400100016034800f02240c3d84040c060f614a81a5110012030041e8225224180d65002c3c2c004640890115800309182d1910340711661039801166460f0415902481148894000500c0c0b1480150541c1084044150401d600c0c0c070006141c00710710282d541c1545c008070004c03c0d040d002001c00b0044d524041c280707a805056013441c1c24100c1450302008001e040011000c80315031a80300c0c1c00103106100b89028500c0141a0384c07503031168440c000d01c2c00d0401885496072080c401c50986010585080c51501103007030b2004040c0191a80c40010010081440300c2102c0d82c9a042c8001c01c901c0302c12004c60b0340180024800f503182c504230380c03d200d0003042c14803d00508150000d0b00e085980312013a4460503110040030410744124591244600200b6414084c00c81e = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 663458102 1250 663456852 663456863
    0x50613090224340807050a060218031002190f210e0d030e1e010908070606180b0d1106120f0a0b0a0503070e0c070c03051b041b0503090109 61
    0x1518041c00c858070318010040032400c1c60358050f40500701c1400b04009102140d09501000480380080d0000b11000b00611200f4011804c0fa509046695926426a407202442d60803034400300902000500b000c000c00f200a0502c0101941001c2540e00c05507081002d003000501000100d9200f020707018001c5101c600b111159000460000c083d46102070054440041143d5a911981d082c026140d4420f114009010040320040c10080003181500c0c4590402c1c4941019695602c1034544002242d40c4010007089100340c101164007490078000011b440310350321017040b81c02d0511080c50304940d02d22400503525944464a2241d10a10790045030740c0e400b5412083e04010310501c00c1c09088158120342d1413003041c140342c082c44840c0c0590103015844020b03109503505030f400402d00707100200c0c0c0c03170302201e0703011501400807800c0a40310f840e0221030240d141e1069134250480480e62924219070400c44420100c01d440034440300301c18110500c440000640d001c01044004004521425400e401c500744184d0400c = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 663459352 1250 663458102 663458149
    0x80a020d02150c1608012a11072405070b2410110d09060212182d0105090d0f021903060b090f0106050d020a050403120309150506130902 60
    0x4410f19525605804e0f180c0059007a8600050410014000e154109052000e20224100020081441401c0220304c1c503043c0b00003011860700c5003108014100c001d0600503540056103d2060b047c419100e41070300c0460030040c1c10070008002c42d880f401c1e40358015003480010086045100c3c1c03500550300c00b0354401c03a40701c0384800ca203941456011941a0303080500406a0780494154401910380300603610070340b8056000a1724040801038510301a252401702c0122480200c200362002420030f800364982d400d01e018a2841d0302021100e09403540183c0102800e003245800981c1000404c83c1e10030b650024080d440b001001001c5499490807411000c140f6040359030842d49a180c10806010b482d942980a05c09450000300d054040b0b148440c102c6101e9114540b4005805a0307402c0694070218007401444400c103c00000140004a0150048100d40e80058083d44910703261030010024044c005c0c81505190030f103d10340c1d542c0c074220010360300300c4103001030460748600c00715824001c100041580403901c0d = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 663460602 1250 663459352 663459367
    0x12010303080f0609270109020a0618062102070f0c0f060809010c05040e10031a07081302150913020c0a02030d0c17070219080c040606030501080a020d0215 68
    0x4000401e00034091800301102c99507404060000d44801100e80466884440e103071182640b040d145041c00d132401800000c02c0401a40d0082004010260302c0701001410b01c044100d5140a0307004004050040742c03400704d40c1c9041052441d03216520301202016500d60008000341042221001074030096130042d0381c50301465507180c3e5400003006910034074010620f07250000e010001c042c4144141e00f002515071074101030402101101c1d0500061420b9120040c02074041b000c45da03d5802210a07440409920440c0d00d400e40e0000d00c0d02ea0054003c80d402100e41c48107000517030380c485c42d006d01d5100d50003000307888451520001e246407104195080c03800d44001106c2c46041d5005c100d590300c050003902100c000000c014000c9485075228200070306503d1240b014a0705911600d002402110b00040c08083d1300005504130080134000d69110004540c490714051516040c1070091b03800804c0903080800140d03241102d50f0303465180d00e00000307100f604071542c0c0b1011583d032117660300100341a01d5504c5803104c00 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 663461852 1250 663460602 663460607
    0x1912050705300f0403091701091109090a14010204030204090c1e0b0d0c0c0503030a0c020c060f0412020102070305030703050711040e0c01030b2116060504270212010303 74
    0x724154405035500c0c1000e41d9058142c03503100e150590400103000c2e000da882c500c01100025001e04110104004410001841c62400c5004010901c0040000640020302d10f890380d11108040c103082c1c0141b10407030030003c02c0304000c00c07903030703141a002541c5200074941001c03c2402403081d600000d5000340351115a406201000d0b010030162992801000000018400c0740d289419491003140041d41e010092150038025903004010010300508100700d1041141c0e451900395002212400c00540d6580320398200c25030304001a41c0f41c4803094508601d040700d94031200320f60b0f1146004604da2044558500e1045900c00c02003400150340000a4a44980d070500e40282640e129070002d403869088030460000c5071506120703101070004070714018969401d4610040d40036001009500b40d00c0f0041092460008120b80710303008545201c0009450303022444918150316500ca90414002c02074280001d0283d4105580010419500f861070000a2111500220041c2c8100d840d4a1003440c1c030880008100354 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 663463102 1250 663461852 663461857
    0x1240c03201605040504080f0a020c0a151d060a0e0f031c020706022b0e04020d0c180e010509040507210203010c2102070f06111b0708031912050705 65
    0x1040b0281092029507840c00c02059803c141c5024160340c2081041c42c7c841e03c4120000e0000801c01d00559000c2e43e14540040d802d600c0c958030040440c9002d01c00d120710a5807000c0c040303030015001d4001503100c035100d0000c5065405098620b0040c00420442c000459075401056044040c0c0181100c00c03900000034602260f110091907031001d031040082c003203000ca00100d0b0345582c0c0e1305800780448100c080441034061407140882a2070a01046069241a580701d0340000c00303401100d184041004c0042602c002c0035001d154040da0307088904584240b19200c041c2c84040c0c1100d104450075609500e07141000c5040c02c4503a80684156100e04103100e0b0f02903050009040207900840c004c12400190340c07802d840034071000340d0980d0325103120520024600c059501601c400c4e8001c107280c001040d2165114011211020504103072480041280c103142070925a40ca0280c15201000e40015450003011998a00425810b65420b4481c42c4124011500c92414000d0603510305030280f02a0511304406011343c1d = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 663464352 1250 663463102 663463123
    0x609050d1e08090a0f0509040b0703020c0a0804050f0402090d230715080c0c0d2f0106240807142505101404080901050f0403060e0601240c0320 63
    0xd044030b100008154040c40c5d400000c503140906034030703071650340c44e41da110441c0d50060045007455400d100c0e00701d000d04100b0001d038041d0720038050b160b40c860074101040003c2070360340031191103240100001c0440d0340f101118000195401088c14542d200d218408102c0c41d680e50410700070b42d00c40d40c400041d00e1144518020584001922030800c00d07242c0516004680c40f903080c00308403581c4103c004c500c0c0c49103d004150401003070364901d142d444610b403904524801d0300407001d04ea80c0e0344503030701804641030900c50f903403507100d82844410710301000450140040c0302c02441001071010107201c503078030404124100d404002804840f5101d08251281204280407180e80541d105d2245241050303e0349074500c103010314103c0810707509505645542d0b440e0303015808004a2410404240907813094002c110380a40081c500c00e24011520403100480140b40000c164005440ea1807428403d01001401e202d044641302000d140c030180210044c10243d0740c0783c407081107100d003240300e503501200524008039020308031 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 663465602 1250 663464352 663464359
    0x1c021b010911060306100f090b0a0207090e01020a02060103060c03060b0f030403031d190203070f0f1802040609030f0507170a0201020c15040e041e11040506010201060609050d1e0809 80
    0x42c0510703009024a0780011200240c01040c01c0c00b0b440700240c0140c00c4026103246900c6c01450207501c840c28408160021002d020240e800b120040c08100c1c0300b800b4607101207121000841c00c1c00742c0710710025a141010320014000e41e9079102c0c0ca500b145c0c0329400c141e0140102e2509070f691070b2120070400003268002c0301d00381c00181c1b800c4260b00301040c0c0c240e900214413900000620016000da650445680c040000882c1d03d40708000002814100c080d0a4100400318007441032203403441d01d200040c02d10102c00301ca80c4071910401c010b00145030000358240030f4a4014a444d601e000d81850401d18098060b0000404410645c4807111715060001e01c0c2c0104c14401e90a0303c0c20010500288010b4019405010381c504005003c00c0c003031048031080540d0b00c18001c0610f240c4100c44400c2c03207022880c0c1c60314165843e900010f02100a81010b0250302c0c0c02810a01c002c004252130304030010150b403418050207100b0518104500140954509000c19040303914410f6000ca017800d282070803a95124001803400b = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 663466852 1250 663465602 663465623
    0x708160e0a06141c0510150e101a0903011406120102070b04020d03020a2018060307150e060315100c1a04230f06090a03051c021b0109 59
    0x1d0108038007a000890700d012018071090715003502046042c81c11401041111007210312404040740f000c01c12002101e606401c00511010700d00340d00d4100752143e4104c40695401c10082c420041d24214418044808800c0300240c840c0458103025041c0c0301e1108140e40c03560810540225182c02c4c0201d1030b0151004454220720f21500c485070500742e026000015000f001d00000080140c1403031440c2d1000f207446071041e1a14130f04107a03241004505140f404c1c800d002200d02c803150150070039070929480341c01c00d80724040040c584040040d0380e4a403580201115010302182460016018084181d01c0708402030a2546030303e400d540d1000e564681c0001144601c00b4811a00030301402601000440c2c4d400c580200b40340d240705024060305000c082d0040f500d08050f04924800f02501c440040940703c1402d0182c11040d84ca01c8400d4a480b070b0141040800360050b43c038400010f07400404a0b100110041c202c4840c817050280018001d010340c3d040050701c5a5000d0100c80181010f40c072500307005114418514 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 663468102 1250 663466852 663466861
    0xc090312030c021902031207080f0706020901080609010e070c230102091c0b01030f080904090b070206090f0705041122090e0109080315030703060c02010e0601050d030915020708160e 80
    0x85003140c1302ca01a4160704040104c080d006420700080030313894015031080d45000d0b4002d13607503d0a6842140180c0340c1070b6001c510714034150780c00703400c03103402c01c0d012140d48400354144513180c0c1c154030018102c2001e00200003ca48108443d0110501e00c0511140074445200d88010700746001c1d500c44d9400602c1101d00035054084e40350001c000c44200c0790000d01c40740141e800c50303071070380108603072005e05840c1a9418094a80295036034007a6220f49071103035040310003a04114501038940280030300f01c801311b5040614020b0700100c0006510742107420072200880c000c2d0003000e030301081c2e204040c0036085e84094610310340e5440b0311408081c0201c07031450b0800c00c0807107000c41c0300340c1c00ca490070600185905020404903502e440e0710001e07900900c000605481d0034580e2075039050111019001c4000150751225150b510460042c44424010b00c0165182807041c203050742d00410f245214007428440321a500480186d640c4204040400342103d041100c1c903006e100910401c0c01c03c0b051085105292a400005 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 663469352 1250 663468102 663468133
    0x1204150212031605030c040305011104030b0609040206030a090201120e1c05181219061b030b130914032701020c0d0b0604020f070b07080105180a0c090312030c02 71
    0x140d00c81d1250400c001c044103000e141c03c0704c1c2c581c006842440051001d01011000c01c90070320514410703048101000c0e40d91455468049881c010091003a8400e450080801025031035030340880307030f100f0b140420026000001c1d00c010b0f2030307956410200e20251032410f0300030640c4910000d1070702030f121507086012a141f17400075070888140c0304003035465420108000d8010380d14240314030004005c1c0e00c0d403000d551509052030b01488005c0c6c40782d001903800a480b1809035552052040c0c01a11040985c6000d0024160303100c003044041405030502e240c82c6507a901c1c503030117020039021300080c20300b00c1c5400d8a548424260015224040403459081c3c401c00341c0f88429250342c000a080401100c005e0030140d06091152614035802400030401500305800700700340e1411020907401000d0351341c45201501c54500f4180001865010160800e41c0554218107107040920350b540089503000b000490041006441d90b0001c40d4004030a61000b440760302c101c01040030b41c03901038215285204050342211151381c11408030 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 663470602 1250 663469352 663469357
    0x9060e10030309060f03022106100e03061902040f0603090507090504151e112106091f0e04230304062708160305070e01030809060a021204150212 64
    0xa0105100c00d00403c0b1390340c05004420188200da0034014101882149000f411001110464440d902140100416403a10311142030003d003940c0340100042e100303240826a9000098000c02c1c41d0b51940d152605844200d404031006489100703408101c10f41d49140150140000301d804403850b015210001c2540e18851154604c80c0d9009020045202e43c00103042009160480c18400190000d0444100361200360051184002c841213040d07949140b2441c4142024a03007800089400c49100140081c81d07903034220181d0810400c0041e00c0b40c8019400340c05198420350b522080001e4003013810002840355009142c07400c1110501448150034126407080c0d181e101c2e44c042c2c1804510325000d84101c90880b1000540140107031782d501301100b903c950901c1e1410503070314002080b203d60020280704000085c8a680000d100940b048003181d419641c9a080038010044039502481c2c010a5042440744200b1101c80e0081550000c603603241c0d1182c07804100c0c12001c2c10002c000d440380f2a0751521200b0210704 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 663471852 1250 663470602 663470609
    0x110a0201080a0e0106081903080a020a050703140409090b040501180213020904230103140d140f2106040b0d081e07050f03090108070e030d080604020708030109060e10 73
    0x11a011660768004245000703201e40d4040900e04d40d69110081650344040082e0428001c2c01d050221030301e140740c40c00404100004003d842040d005100803450784d900182900ea440b5418140102c601e080c1e44e40030130180c01a507000301200b030b0800011000b030202603410036001f54040c034000e000300c20784040310701d03200082e040009411500a244002000c54590f014011613134000300045a2007031060780202484000014462400305000010400c001e201480a03c3e0f440082001c1c1c542c100540b940900f41d0841e0f6030410b14400030000b40c0e91800c01e80101180c41c440080f16031041d1803850451682003e5008481041c0101c1c60101d110a00d85001c0c2008480c40c1c3e440340100d46031201c100c0c111000319555131645407940d4000c0c400c0e14005030061000c0b881c11607150006544408000700014001040075208005100e65403146427025280420f249202c14a0303820003003116115440400d0007840745102c0984001404400400d5403c420b400c802c007110706240d000780d400c8e212003004d04001c0d0214070 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 663473102 1250 663471852 663471857
    0x1f0c030f020c0a05061b0a12021c05120415020d0915020909011401050708030f0a0b01050901082a0d020d061707060c02010302070602031e0903040b0f03150a030b07110a0201 76
    0x118100645e25060008040082d40190351140c41c2c2c400a03482032400c03100c84411200006c00c0b040c2d140100350704000c1e140100700d460211804500c140382001d4100d00c2404030142440d5044000a002d0045150b0f04240903a85075404642e1502c8045682c002481c00c0c400803281903d18031000c0c04040070720f0080c0d548141c001082113070aa481d01e8003e802103110b00d2a0141400414006200071801c004081c600c200c001101c0e101c045c0c90005080005c5074801c001c01e606000d41030200c0f00c0c00341d030b00a41a07a0701041130210035180401c04d90070315590b07400c54912500300c15400120b0032580720040d00038098001e01c00d00144a000c1d00d0310305058920020f520700c00e0039540810010809248501c1c7d011400701d006040051503c01d6949900b02a6030044030420103184400c20042d041c403510000041d400a809070255040c281400100c000318804d804081c0140034011000c42e00e807441800311f07c400801c00522102c00940c1e60701c1c141c04d550508640e0517001c9058581c00c04114900071440000495050307 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 663474352 1250 663473102 663473119
    0x303040b0705150f040b060d080f092b141216030306050d0f12110c0f0307050a0303020105090714030d080a0b030114061309051b1f0c030f020c 63
    0x40c9112003a041800203481d94800c1000307640030721225141c442d00620800c0b078049242c1c0b506040c00c24003c5000307030070b91b1300508920000c000071841c03400a80705043c8156403919a24036440c00001c2540b1800702c0c4450402e1036920703103030224a5082040c0d060352880340300034040d44a90042496150030840c28410350300340c0e042000c0320f1801c00c0108012140ba2280c05d00045950726040810325483e2280c40490b900c100742c0c00a1800c1c028480c4aa28074551036240c2600410790b81c01159444e01500e0003050300602128420004a5809002d4000030b08405800042510366070b0800074003070441a103c09030707103000300362011030385418101001080b0034015008040301c0c000c518044607034110003405501d0042d074640c048806540c0a026140c05142602c00001c0079042c10402c01c410014400c25984c0d01e01c0c5040c1e07000300003400c00708400e00c1000a0b89540c1410364021300c0420b820302e00f4903104c10745914484074013683d000d40050022035410f0085d0340c0c0c0418801d00706000e9964440c40c440301e03a8440c42c072 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 663475602 1250 663474352 663474359
    0x6040b0703140d060603050c090d06022104080301033e130f0504050c180c1b06040f330b030304080a0c0e0a111b03071703070f0e030304 60
    0x20004020140c801d241c603450242d0a0b050380085a00059102c00c0419107481040003c02da05010707503508405d0720490380d480e044500780000c041c200795100c001c020680118070040100d151040e02c0005411800c015403c500d440e20713060f002c5030300902003190b0842a40e0030a4081c83d500725400d001034040e501400945c88414164070303504001c0700c00c406d50300101209800408034264001e02d00c4c4004003a00104050070545011404c118461050b1805071094a01e102c0440d0070015602e03811080b21018607940c1d8071042440351960900c56520800d91241030280002c100c1001c0c80b070b044107802102045c61400300548400c01d21484800c1c4800e040c581803041c0c4030740c20143d9020b040019030007400c4030314180c0d54072060750411480481c1a5885090068108801c016170403545a006061500800000b42481040c9006010720140e40d044032000c894888480c110030000c42d50079070b40210200c1e10000034074096803803a80c0b00b12454030001710b020b00003800060141e43d00001d08000100130b18140f03400d = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 663476852 1250 663475602 663475619
    0x406020a082a0d02010606080907060302030a061a03040311060402060d0518121e130315090b0f01060f080105030601120206040306050703020702190503030f0d1b1d0f0604 75
    0x80441070001400d0100107200103120320074600b4284544981c00303802e61140c1810f0180c2142c02c60780c0a0000e00104404000e489a0080b03403e80542d9824140180c07281c943e01c2e603a4008210603000688042450020b15000c4013400010314844c1788265034400c500c000100855440745810b0b1030094000c3c0702030180c00e002145039000503902c00890202034044204802c1524a000d02d040c5400f200d18000140c104034107070240c100f100c2e500302c100660915000e00d08084218452003440302404459001d078050f45560b0301c40d00f10301c511580000303000920b030604541610004c0c1081c4a8274000c5500d00004503441402100180d04035003009001c0e140c0c44c1c1c6070152000030f890640e58101c6c0d11400401001c00011154400d0740e0080030155030046e00d5850620500090b180d0707401001e600d0441e090010001603074004215a030a40450b0b0341280c0310101d421603000500920812100381c80ca401075110303951580074070135810075260a81d01164910b40d060900c407a8615080c01141c20030b0301000144107591 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 663478102 1250 663476852 663476857
    0x617010603110411120f16090315150f0b040509130506070f031d06060306010501020f0309040f090203011e1808041406193506010e0f040c0507050d02030406020a08 72
    0x1342004070f89003945061814043c100c2c00c50b00f0040410544042c050307085204590012444806d040c2040c4240c11516100a2135440d60440c0b000203031114814401ca04d2020314000c000c042480303c003004c4a848014201d032640003409064064001c44e400210803100c0c5440c440f004a0b08400a05a02e450b0070104581000740c47e9140414180c4800c00741441c07450000078664103a0010010341003904240013010308008041c3d110904552207040042d04041000c022101d42802c02c0f14006001c003851000030014003a80d25000c0e45c0b6520309009414070480d81c0607610350010360f600040004024498040c40c049a8031000034000c0c0a0071f003c14402c0c0e128045104450050080000f13080140140e603070340d5001c00c040d01c0a40054908640c1c5013080c10003090b880040030700a401a9641a04e007900c0502e0114020000ca041000000f09000720f9201c0742c041e10301c83d41000e403043c00000e006240c050b0569100341000c540602c200101203189070b05c0403041d80c041d00c603160b000d810340c0c0c10607448442454 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 663479352 1250 663478102 663478121
    0x806090f011a0f10052208060a1e0b0d12180915030b0c04090204060c030e010309030c02060d0e0607050c071211120c0603041a28200a020106170106031104 68
    0x100d0300b001040f4081d0b400111040d046c980c0742480f5480581030040325820b04202074040800e29080000305000c1141104241070701407451388000071403a01c1c0c4000142c681000d0300014140d2041c0020841c4c820347d0085126807008008000e05685030760350101801110381c151000c00700016040c506100144c03040c21041d41140d110380032117007230a49400503c0300b20791050f030140300441c2e07814a0749010580c00c880007020031442402d08100341401524007500982c6a414003e04c030b058000341c5d4103c201c0303080c0e00c030301c3c800b40d50381040b18014644100040e100354030410b07c003581840344640000f140c1080342c0101ca1001e0744008640109140762040c0301c002d004084c0e00c04020300a914107000d0a0301c0f18405944118090054154643d000d805101c60742c61014040c0c5902a020f0100100762440801880c002d000303080c0000a602c280010640c00c0d603030b801e00040c1e641050000360dc0350059905412010503a0990b01c0c074110200d5100310043e00304e402c4c41c8001840550001410041c0d440d1035840304c502c0 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 663480602 1250 663479352 663479357
    0x6051801020a061805070b130509070513030b07020c06041401050f070b0f0103020a051807050a020a0b010305070501030e030307020a060b0f10030912020111031f0806090f011a0f10 79
    0x40b0700042c2e0340c180c00c0e550010310311503078000c103080200240312040040100821010941518120700b241031020f1795460b40c0038031401134121802140940d48075038116410f90843c00890706001e601d0b85850701c02500c09031f9220f00140b25402c1c11050360326107281140c04842c611160310500e400400015202038001481c042031404023445101c0200341107082a40c4034200000000409604506c10044030510039009280203580c24010021010810726560b5040702081c00d2580d10741c404d810003280f5140e0103c1c8001c01441c0742c1c000000400c0300010302d1200b9078400f40c07800c3c400440c030a5001e65590208031503050050b809002036a020800ba940288076410300038107003201c005401d00100d40741c04039190801300080c1e6900003202c00d21035074000c9003500040e0740c0300078003601d42c004003000c0303890001070508120302c140043c0c0e048807910380084002c000d00c82081507945502d069140280c07107042c40003094406508050803120741036004007841204140080c45e5110700b968210034000751001c984080c0f000d = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 663481852 1250 663480602 663480613
    0x1a0304110d080715180807020904150f05091009050a03050c0a08030712110405010e0f19030812060a0608040605070e062b0b0609061602040906050604150605180102 72
    0x124142c08000e001c030500030b0784400c08121108046400711903610850f004225001e003041400168020202c46c1d80d160103c0301c8021580311401c00003164500030780241486480d20010b0318515a894100354882e4500a054030080104640140d0580341c201c01300a00c01e42003d8030820010340248060030311240c900c1c00b29078074070111307660750301245e841600d40c08003080c06103074443d058076002d01441c5054501d00c0034881c1840d29090002c0c001d00c0401c0c4000d881036400883c4405140c440588032240d050181205600d1541c2e02d08107181c4942c01074100f100380f4071000000038400d003040301c6003004403212070b0b4406c0c12540c0c2c0c0c0c0d00c50300e00518000e00b1010400107501e003036022a560b94406001c1c0c240d02d29400c843d0380005180b0030f44010499001b0f1094160400c0e082e000b00c0c0e54ac02c0c0541e040b6140541d800c0707a03180000411038040da000e440d0025400303454480b00c02c0c01e00042c0d6000a100d03400940742008802d4410740307006402c03421403043d0000580300b001540020361180074a4400c0ca02c041c0120351 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 663483102 1250 663481852 663481879
    0x1410020109150504121e05070609050d05040512030f03011403031306210b130902150a0e041406032a031c022b030b0f060309060603071a030411 63
    0x558031003402c4015810551a94103101c00d1150a40c00a0f2606141d410300380e1402e134071840c940320b042c65180854400c0c4200400d1410901006410010300160703c001503921407007485001903d950803e000c4c060107044035050590591000004481181c4004546141141e1a02d2600c418220032110002e4160009000441409400c4020074018100c192200c40640d04481c0e10390314041b0301c40c0c03034000c001e6042c0a03200c038160700c40c0550b65000c8010090b0100b040b1040340041814804c80070940031401d100003848400c801d03440b90340d44d6145036003120300b480442c069003030307840c4030704420f03211203078560840190031504a140c180c0c0f107219025425140d49450794140700290502c480b0300305a103c1344040c094042a001c0e4103100d0b034694480300e4501c0c50002982d0540809981c6441c880d0781c0d06142e900c03004100240d442d030030070095604e401052a81e42e0302d01402c4850700c8407000e4485a000c1d11a40f0f070f0104a219083d820307040d20354911004181190b41c4c584500445441d10b20f5444d8000102d108202c = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 663484352 1250 663483102 663483113
    0x504081006050909010c091202220c0311120f1008070306051e04030503011a041203020a05060c270f03060c0a0801150804080a0e040e0a06060f1410020109 68
    0x103803100320100000540d1900e8141030207074004000741301d01c1499140450180900e0340000342c1c07409480200c14041010516031002c680826514200e000180e9010540c140204107550080042000c190790248207a01070381040303001c24041d1015143d20550350034000341c0c1030318400700b52580c0310700c841c1d0070200700999a400090619485400503541d0548803010031011480c500503194a50481e482c40380d40b14602600e004006010601603020308064580c081c811400304c0d9021381c0c0203040311031550ba0740d050f15858040e581380b6145104507054041d900004880c580f000060f40d10b1407030305410480d00341187c2c2d4031001910b280c580c0300d9903218500215440107030704c04100d854818404145c441b1b940b20070580e000740c10010140d02c200c001c00142802000d109521189698000d82e01c0442e0a0711241010340607100d40c00c105651039001071804102004203800055640c000c80e0042c0b1040200320384440312412101c0550240c070000600040d02c410f02803d200f00340c0541c4103803d03c00060041030f25030340c4 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 663485602 1250 663484352 663484363
    0x20a06090504050108120915071e030201050a061a09011106040b1f030210050d18030201050106120e03040e091009061e050f0604050601021905070807050a030c03020d03050408 77
    0x4040094251501400340b401c0500c0340c10b01400b031100042894008940d18418a0300c10b2803050b50140f28180d4401600c010f180059840c00356000d540006004925004070521a0a100c400d40c0190b0030480441d542d41c000b031103904244d981110072b240071480807a09035561507010702011030411052219141e04280241321844c00743e0300c100c02501c05410410001e2200c812480b04200d440400400d08100503503410203d084240720905005884040189114004004201040154094038919101016810740c800303816541d80742c9690210200b4a01900308480c42e092a444580d841048103100280070180e520764001c2d10b00c000c0301c00b403031220492035043c2c4d18140d10459040d920f8591040c42c01c590401885400c0d906c80c0010071071890620214000018058085400b581c2e13140c003ca00d0a0741f0903c500c1700d1103800c1e03140e00c15800d4400d1429694850031031207180200d0117800e2010038149001d80b00c05e000c80303410040001c00c050854013040041c0c2c13840d9204405101c010000000c13520401d002 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 663486852 1250 663485602 663485609
    0xa05040801180c05011701050409020612090f210304020d050f0d0f03050708130f05010e030c150f09030d020a020a0c140118080d030917161703070e0d0609020a 70
    0xd4002d9030500600d04410036800c1a081a1305100d51501d00304015000c0d621943e045071700c1100d0108a03600c0701e0010840d24072980290b00345034600c103410170051080014410002030f482e901107031a0a552101c00c070514040d4480c0c2e802030100200045805803820401c000c020a0040d415910f0f00405a40c40a00c0d044010304248041031011248000c4280c1500c90154400c071070b4206807000f8035015002e20302d801541c2038010200480161840305011096001e000d4481c44113080b25910944260840da4a0250040341c000400d54000011b0981c04042485d501070300c0b5884c002e50500320851000d80c0690001c1302680110300c240310041c1c01161107941c2c420002c0030000c040180c00c41c6003d00041c41500316844010b00d25461840c02c011a4000040d0303031407010f1940c507000a00301407078a0300007a440300048600c100110041402004035540950320001148120800d078201c92a8505448103808110b454001181c0210318041d5141004458812400e11170f0b8800246c102e2650700160300400b4540 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 663488102 1250 663486852 663486881
    0x50306030709141b040506070303020c0f0706030b12030915070512041d060f150703030b0a090203060a06030e062707031506240f050d0e0109060b0d0b010b0a05040801 73
    0x2014420300c18000d0102d5000304c032290784a41e00e018145000702d070891150f07060041c01c044c0d000030110811030f02441400708128207482540c840d955030304001005810f05510b0540300e9600040c0310071002c0c41c000121841c500c400ba180c0d00e48003ca0444200c0d05800c0300d2030640e018010307804e1000d4030781100b80040c4046c0c0b03540002c1c0d036032186c80ca036087e18507201c0041115006009504540c00caa58a54920401a0f4007040d41142d4400484c80c044019002ea1128039410109081d00407034a280c581e005107102e80f10650f4294010380c0e03a58422000c2c3c540d035501c1c0324a1038010710003140800c050340c40d0400704140344840032410135403140e0141d483c1403038070740c03099a001e060f001d44840c2403c1607020b08070062401c0386c0a5901044824804040b50100c45510014080c036403450130a1680100e040d0380c3d40880d4500d04001d0200c001c030100b40030780103409040f20303418605001440145072130b03011f0b410407039005400486540c1c240751200d14103a002c01c00c802c0c140304003030000260300c0c2000d004030301c030703001d41003 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 663489208 1106 663488102 663488141
    0x12030831020637080609010605040302041d0a03020c0a0812182101020a02190b070309060213081b030d120507090b0d0b0f03060105030a03050306030709 67
    0x4405a43d5004402c03100f0300d100301c0c51030020b4541110b0b4560305100d6480700c0800403622024080c003000700760b0070310081c40941030943c4500d00c0b070482c14000e0711100e42101300c441d2030540440313412001a03204c0f03014050300c0c1c1010944880100140401000e1448140203807040601420980151518030054501519540d68580c08042859081c1000c01044503010326400303540301818003005031007240034681660140c00c446080c52900300f1940314a43e1200101200a401c008100b500c8064083c8400391400368840380074001448010300030884003460450514050f4400e080c810700c00d420010b10a412560401407103e00d81c8100040000d10760703170781081500e030700c50075070013042c403802001c42c2119820311079070b008070304c0c020080303030340103080c443d04d104055070350509008190f0140c100d48500300029010342c01450300600010192105640ca07481d0f00010cc50125210381e0b503194a4 = true := by decide +kernel

theorem cover : BRFrame.Cov 663309352 663489208 := by
  have h0 := BRFrame.cov_init 663309352
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663309352 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663309352 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663309352 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663309352 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663309352 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663309352 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663309352 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663309352 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663309352 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663309352 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663309352 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663309352 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663309352 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663309352 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663309352 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663309352 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663309352 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663309352 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663309352 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663309352 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663309352 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663309352 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663309352 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663309352 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663309352 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663309352 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663309352 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663309352 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663309352 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663309352 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663309352 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663309352 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663309352 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663309352 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663309352 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663309352 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663309352 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663309352 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663309352 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663309352 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663309352 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663309352 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663309352 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663309352 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663309352 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663309352 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663309352 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663309352 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663309352 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663309352 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663309352 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663309352 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663309352 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663309352 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663309352 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663309352 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663309352 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663309352 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663309352 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663309352 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663309352 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663309352 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663309352 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663309352 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663309352 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663309352 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663309352 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663309352 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663309352 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663309352 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663309352 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663309352 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663309352 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663309352 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663309352 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663309352 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663309352 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663309352 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663309352 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663309352 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663309352 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663309352 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663309352 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663309352 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663309352 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663309352 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663309352 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663309352 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663309352 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663309352 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663309352 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663309352 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663309352 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663309352 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663309352 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663309352 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663309352 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663309352 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663309352 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663309352 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663309352 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663309352 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663309352 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663309352 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663309352 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663309352 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663309352 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663309352 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663309352 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663309352 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663309352 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663309352 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663309352 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663309352 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663309352 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663309352 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663309352 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663309352 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663309352 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663309352 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663309352 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663309352 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663309352 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663309352 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663309352 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663309352 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663309352 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663309352 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663309352 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663309352 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663309352 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663309352 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663309352 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663309352 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663309352 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663309352 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663309352 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663309352 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663309352 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663309352 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663309352 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663309352 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663309352 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663309352 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 663309352 ≤ n) (h2 : n < 663489208) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
