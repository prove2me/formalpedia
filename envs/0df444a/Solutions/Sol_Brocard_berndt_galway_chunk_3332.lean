-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3332
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T09:21:12.641989+00:00
-- url     : https://prove2.me/submissions/6fa9c579-d7b6-4d04-a657-15bb02742789

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 599100719 ≤ n < 599280575 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 599101969 1250 599100719 599100721
    0x50306041a070e091501032007120908100b041d210c07090e0a02040203100f08011e020c0f03040915050405041101140904090b0a050a051005190b030a02030612030403030804030305 79
    0x641e01c0307904000c100c040c2c41c04600c824041d00704c810234040d500a100c204e4551484040001ca002e02400d603550440d21480040c201176140071100001500501c19200c1d03006079074203605a642d04414000b14541c0c4d40344001440d1520400310070981034041882013002c01c0b00c09010041103140300140d09010340b0040d040100f190b21400d40850314008089500039401800401006010b04004565404071068102400c0c8074942d1030a12030300300c884100c0d242035104c45400122840007070700e800038041200260100d032041d14030440202d0540e0480e80080c140d55407201c6804200400907510240a0081198204130505260b03442d16216403452821a061100c202e400c0100e41e6900d00070b03079a40541c09403080c02703c100c0303502c0c0684241134200c1e000b07210145481d020030071040380d5210760307072241088244e103280309070901d810090000d21f0750510420381002a00c01080d4160040095401940d02c0d032005a128141001005103071407080c6102002a40240010004a58800724030394002d074240c03d00040e5 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 599103219 1250 599101969 599102011
    0x50309040b010909090501021903050c07170c0706020c030111040815061203070510180203060f0604021e0409061205030901140c06070c11030d14030907050306041a070e09 75
    0xd030700c9007544442e84c194505140003083c020107400425501c051800d02e40d0000c080078509030111502a0380981d40c810003031100000080252031038a002d403469140d03090805020300000d62502d4032940101c80143c00400d11403415003000d0003400d4902850f4140345007803600b003407509503545a2040c0a180100030b44004102e56881c0c0801c2184840715540659030340d50040d00b04107a07202400220401507919015503103070359503140c10700110700c140d0081c060489030f02c4181380c88401d040e001c1c0440340c0c050340c20403105503040c41d1140d410f0803040200f80110b4a45141241c9402260b0259001d6141504101c014200161002c4112445406e007400c040f40708101190402d03296010341005408284694014444150b41210035000b07a60311682c001f28450084006040c0c54407103040114000c210080043e01c0c0c030451a20285500c11507501c02c40e802103540d4400a85052020340d030658403103514945c0683d100048280d000c0d801f903090304ac4540a64000e001181500c0c1c00100b441a4100b241d15003148 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 599104469 1250 599103219 599103227
    0xc1509121506030d08040f0f060209060c0601030c080319030504081309150b0a0909091a01030320010c08070c3206011202030309060a090f23010804050309040b01 71
    0x310420040101d400800c019140e203a00c100301950307442c0c401d1103103851480394644280c0c00365120301e07400070640c0c2908001c4d40d41e05880c0341031480d00300c0b6103a4003801754013403c1d00c0e210044c200c5844404002c00807545181864105a100c5800c0042103400420580340764504181c11140810420b20780000c40740c1d19400d00050b14010b041928060012a9500049110103600802d19002607515040b011a696409030425441107000c0300000c90540d80d0b0400040c4c5095100405490151401c80f0b814800d4100d40306010b0310136002180030646072a050001a1000702103034288903c2c0e08005c01607100c90f064090030000d001402c203003c00151085000030049450700c000040b443c01c40c0761a1b03c0402c0c40d0300980e480810182d22002912801000040400d18544201032840e00170303020b1454100c40c0000c2c000103a000600ca0380620000d080e0028110840410010043c440801c0310f41801380552038600f9110f018200d000e0400050740140800729402100321441c0d10f20884000035107c4484006a03 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 599105719 1250 599104469 599104489
    0x121003020406094502040b03010c030617070305210d0c03020a030b0301060302060409231f0e0601090603020a0e0910080607080403050f0a03061e03020f030c1509 71
    0xa410509100d800036140c140c0d500209850768451030582503030074450200745059000740000d003003e400311260200044103102e201940050001c0c1022481f0340c80c2102003429503800204040001c0d9980c00700700030b900f40f4041c1420141a014015140f03851460722104d0b9200480c0490a181750340c81003000c0d501c4483d010445038101c80140d07003072001c3c90000e10041c00a40007900e886002c41e01b895144ca0740f034a010707c259429654010040d0342007900b0844040001d20700d030507440310901108603c0407100001c1c00b011600c622001785004140318544481540708030115441400801c2040b01400800c2c0c2c1c108021b80151682450f0058580f4000e03002200c04400c80001141c101f00e0f030700280801503100030400402d0b03031000004c9854503298500c00300c40302d000454018001030402d0014007107840001d40108101c103014038009c2111600d072024003a0f03441d9206c50440300d808a015003001142480014088800000c6006c1c5c8610740d110801701d0040803411048410500300041c0200e010358651905c1 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 599106969 1250 599105719 599105723
    0x1030213090f060b09100614030c04080729121303090f08030c0d1106010303052b0906060f1a0304020a170a050c060f19270306140903121003 62
    0x200600e11000d04103c001841d480700a54002e00301c08002412005aa0207090308481c1180c0e02c4014403c0110740700000f5400c06003c2050810041000007660042007203140f000e0a407004a0b0784505141da9089411500c2064a4519035441405401004848104070560090100040c03d20b48034182c40c0440f4000c5464006090740380b8540400b00c1c065030000040c10f180041e11007150307501284514181c0700c040b032015260b070b4036510400061000038803c03006010905c0900c004002400c4656200c4080c1100743c51210b02d4803039440c2c90200a221280c0940c00c000c003003142400710528100010300f10030120700c1813070101481001000c41c3c11901c4a200c0385000303141c2030a1016118460b031101c40d481d514030280680e56442064540b41e201c0c0b50032011110260800c1d04294505046144c101c41d150001303060100c00e2002da00e1481d01648002c1c2d00f500d05088201c10520800d0b411171400504070380304a4001c10120f4205410058400c2d000070031512848841203080300c1030768a03d10a00814803540e000 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 599108219 1250 599106969 599106983
    0x2103040c0b13051309020f132903010b0906010f0309080910020d080a1a01080a180302011b090e04110d05190201030b031f0e07051909051b030103021309 67
    0x12262a40e91004800b8081e600100e5203010318080288440c400da80803000080d60015240c03086060b1403a0182c00c2c51307003100c9000b1000c070300b00400c00794846000c03d400901d406d00c4040106151301d10f160078421008149421070f000e040c60f06000000800680d885481c02052681d92607000b020b00103d502980c509641c002c1031440003010303420009444550891180c00030a00d0140412000d41080c0034140111040d0412410351007004001101c90b41800342004c0e091558600800007115a8122211480c3d4026000440c05c44400c500f900c410724181602c0c04200040740100303000c0f42403100f0030700d138000fa0060980c5541003000f500046034651110001451031085a4104044e81042014a0308090003620200401c1440c0000c0c10f031102843c1ca0006c40d80d0095034004082401640d1040550b84a0341040b540781030b40350404100f11107000e45081c4411200910200a4003400b8009e07982d005200b0000700c29402013401c64540340d4041070000038400c042001d03498100e58219404940b4490b0003000d = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 599109469 1250 599108219 599108227
    0x1e050103240f0311060c0a0602070804091a01091421071d090105070531051306090c0c05150903070b01090b10030b0a090510080d0816022103040c0b 65
    0x600c0404440796100448194000d003c048800c5c1c40c021040d10600f10102c8054045403045550b420700079441a042103401030070a200205a0013018895030400da52040000814020214005801c903e215486004031000c140d214100548035054251000e91341c104620880300350410119090440682010300030001c46031400d4008a00660858022840c62008020030344822100726a2881900e400703101c1c030340968400c1080010341690604580840000c402803094580d80040c0080c0740040c0f072500c03560703103d140a00040949100c8c0d0001403500303060a040215266440986031210410648040c0e4488800203010300400e0003100c40d104d9009212003a1036844906203c0103118002155006000c42d81014240c10702034071803030400a1b00204007a61312441c2900c0c00e00500002410b000d06198540b1001840300c401f00070075102000e845d10343d0801490101034010b2100c00401d4501d0456120f010244030071280c00e086408001e00b404942541c950340c41c00d0002c58000154461014050009 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 599110719 1250 599109469 599109479
    0x1a0901121410020c100b01030b06090f150c01091b050102150a06050904030302041e0b030105060a09030803040c05150a08040803092a130212060f0d0609030e01091e05010324 76
    0x45895181c170310050804118504110004404442c007040c940e80e002001001100142d18007032242c4500c008008200403001103c070150500160003900c1c090b18240c1d1258440d40c20003088100c82c9040100562006404500c1e01000035691000c4203440d02400312080d01207003054565401c0310002d810083c0c600d00c0c517800c00c3e2030b00500a43c401c1c800d0310441d1720054500c10a60341c0b0404080100c81e801c212680c2540d00f00000c0002652281110700d00780510100f0001c0012005005144920f00070442805024601000d100c40c840c2c4d500d0b190032000d80700b04020218590006007031030708160011401601c940d00c0d4070380c45180c03809501e0407090b10f0680c640300d5019500c491001c4051940183c1e0700042607400c40382a007040e80101d060b145001c8105c200041d1a904181c0c0d40d0021051004011001403502500c5910882e1070009c41a000a070111041c203003256003000d0300100510340101c03149480d01c1446848610002c440c0030707850405843e80f1440040c54019100d110300300040c0e95900c04115691 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 599111969 1250 599110719 599110723
    0x10306330e0f090a1e0b0a020306040e06040f060c030e030304050a050f0708100e2406012d08040c0f17010b0a0e0408030c07151a0901121410020c 64
    0x38480c001c0000d01203030005010b00c1c5110724060042000c00000d069a00861707480e000440e40d41d02c01484d6040c0030400e82c3d40070035000030007a4010458010010f0f0340707044c04024403041c0c8014540d02800b5034420400c4c0710025484030003003404190000e0000a03800002c20044000d0810041980c01030302c00802840b040c4803011031075613060b9108501710740c81c00100c3d4103126101c810520401181350031032030540e800080160400f2207100108825600c00040d12240718003034032100503808540458000c104981941c2090881c1560511402d45d00400702800f000c451859118182810030840c0002c042001c024100d50400003a0425141000000f0703241c0a0544018034500b5504117650b003420300d185c0c518140f021504056610703244030088075035030715181c1200c3c41c0c2c00a00102003004007044400e001c50528409c0009018600c103000c182201b452000d04207d10000c0e40031845440820300400842202e0040c1d90314140e0300030740d00d03028031452041d45d60030048100c180c42003c0c0c0c0001226034000b400 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 599113219 1250 599111969 599112071
    0xc0602010c20100e03130308040f06080f040809010309021c1a010302030717100f050708060a08210702031015060309080301171908041418010306 64
    0x1a82e0340c0c04102a01c58100250844140c1c0e4a01c0b2940001d04480c803e002241c010490741031101e021a03140c0800000100741c406e1040d8805d54182c0b5022a06004420f40031036020010113241c0f07400001410060300c0000d60301e07400f078030081090b000040c401c0c0c0c041c0d0094110110341030300149a0150742102c1c2081207810f124111003100d1144002410b10710034038040b01740605813500039009281090400100502c3c04910214015240c45102e400541081c071500401011094421021529041110002e0201c0c00040d00141c0b00e500c42d94024048501300117006800700c0c003100c0400b9400152240c000441d48500c000103500750042003180084800c1c0c6400c14102c048058002c40301c4141c0e00c003800c80032035003c0314009081c01000c00042080d60040280e07890302d55110815a00322010a00701d007242240c080c002150b045802080810400000700c02031201e010055451485128400c000603804800500005142681e120081d141d60340c2440408000c0f02e90390b120104c15907080303108107810401 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 599114469 1250 599113219 599113241
    0x15213803060414120c030d0228030219030c020a03050a12020c0106050102280f03050c031210050409052107150e01050a020c1b04110409020c011d0307060b0d0c060201 73
    0xf141c4d00b00b0810031041c10080f0303103600c00c1040186042481d620020f0001c1e5000303100740c15600110340d02c0e03110120348002e0080c031040c810b03441c0141d403010007840c258900203c01c1441c1083c58079280401c5440fa8021034419945071b40362624590b41c031401401038035008611101036541d02e02c04541c0c00c0b10100154080b20580b0400d800300c40f880b14201e00340400381041d0100582c62905807490080010785a810340900903032207800d0a5081030320002d640d80c0346400103c04080d12010150621120030f032800c40100242009a50502980400c2c0e02d80320b5541c00300c1c014080740300c0903504c00c0c0d050586210b01502d000a610454002c0400e04d8200c41501418004451074000c0d46488085412100644219480c4c661890060b1842c031050060164070b5a07010314055402035118841c091100400e01c0c001c2010f44511140180c0b5800d04240d0142141c4032040c6030001464412040c0070141030000a90700394541c4860301240200510300400c01c802500745009041941510001c238080303406411540c20b103030b = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 599115719 1250 599114469 599114473
    0xf04030303061d22050c0919050105090c040e060303070501020a0f02010b040515010e040b091006020c030d02070510110604030306090e0a020a06051315213803060414 73
    0x5030141146101d0540c06540610031303040d1250803540c942c2480706070100c096005e40b00f42d80c41000c0c2d481c08a551000c045404404800e00c0c007241316806006441081d02414090b1000382261501030a901044e100c3c80c021030004100040c001a4140d40c10411a0a4598844001c2d07403070f030385100c0b40600055810303c448400740d4209035010078107003030070301c034407817140d216000e680a844601c04015100803220380308030343d00292520102c68081d203d048555015001c4001641d5006207411002818014076020140c42600301c04201d00010b5130000e52a02070390002c403800000301010540544418103c0194050a80190400c000505406034056012a542032a06004030b50560007036684446e01590b009500414041e01030256911841c003604024000d40a07042c0d031716489403203aa40078203015003101c0008000d03802102400560b0304c40d10302c034079038100010702c0079030350b0000d4100c42280c01c228110300c96409540a40c01d5a0a00c10b002501c012020b8156911410b05041a80a5403016148050b080c = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 599116969 1250 599115719 599115749
    0xd110a02030316111f091407051e0906090c07060608150c0a02061504060f0308030a0c1d1507211808070e0606040b030a1a042f0f0403030306 62
    0xf41c040c8070391078a4224008050100f10f003d0b0000c0081c80c220301c1004800c8607a540760241c000480d40051030445188480040c440185000200140080c441c40e103d0011030003048102010b17102c2000e070700e070400011a88a07019580300c0000c0d02039030040710400740c03402e030500c8800180e0420215142040421041610b60195621a03060750381b841703640a4200141e00000006211f0382190045111700c0f1030040010501596424124090300700941007a2000d20f4004103006a20780d09100300e160041d0941000300030490350441c99004031440c1581c440c0140c035500ba8030350050388108200c410050344207801c0050f250100c000e00748041407425132180812403c0046450300b142c441d4007035007280c15010003071130054181013489401039070203000c480c0c1100d814000450085410409075100f15450302d800070b0115001c800c0c0840c000705080e0854000d921b880ca4a04075000d00303100e1400d05010b000d101d050240910b00c01a200c130700c60354024250422001c10040209689900540c0845600c0d10fa08508 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 599118219 1250 599116969 599117011
    0x10905120a03150602030a18080a0b0603060717040f0204110a0f0f111e011803051206100906080426040306060911031b040503010203010e01091d030f0d110a020303 72
    0x3d00500e40100c41c05644244800b003d00c1e4030403105248034580e0b0800c0032800c903599404441c5001000130301168820514800c00c213150604004142e030000309890040f11403500690807a02040c4040d01c05400d241380c100350781e010342d00ca80d000040f084446448603962800b0203003005040c540003843c140c0004444100101c50307140f05251141240191b070015100001a4000400d2075110a00120b6000d5499100d03035020844049001c440c5640691141c0da640c00d01c9003805003140b8070080c5400e108140f000f140712409580304800d4020340d040c90420714081c3c1c03194102031460481d9209440d038070f2000925a004001500d0025000300c0e88107840901c0200c1c0c40300300ca01c00f5a850424805005a000d1002800310b02800f90a01d200c80490714240e86056240c001182c2a42e009030881c00c03149402c0001005030480381c2c130965080c250305402c0c0ca04d084800035680e035102e10821080c4015104041801001c0e01400d6000f000c0c41603060051913070300e0b02210400717912a08111003c0054814003603070210 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 599119469 1250 599118219 599118251
    0xf0b0f13021e031c050c06010f081009030315061d011706011b0b13140307020a05240d1a19030602030703020d0c0c0b060a050a09020309010905120a03 66
    0x1045a070300401411802001074540d035100506a100503915100300c4003a18000c07210300144a11100c1e0039503c072507550b0703490b4840381d2814006a0002032482c511600404c104103011482c981102512031000c03400300c0f06400c0c01c50140c07940130403c159000100b040014529000600409010820001030b252060b0302401911007509880c0e00341c484500d05c3d030004c2d55542c800d0480c0114841c0c2088214469000c6440c0c81d00c204030201e038040d518000e070350a5481840705002003004094035a000a40c5050401da020a891075503030f1250f2070188601c02c074050141912074200400b014620f02020b03031a85000c5403130070042d00441d032a0b0f0102041d040d4220a072400c01e29003070172000c0050321241428501d5075072a1030096000418a10815509200c0c50001e03001600035113070000080e40e2821105600380c00e0a10f10302401034503080c8243c0903010104400c1e2680e058282c21500c1d00d200050300c2e13a60700b07a6038034054450950f0041545c020301c0000c1c401c040024010b03080e07820b0a13039020400c400d01d01620b80 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 599120719 1250 599119469 599119501
    0x10b0118030b01260f0c1903050c2e0203090f0312030c0f0d0501060c03090602010b030a0813080115090b090408031911031603050a150501080c04030f0b0f 68
    0x2910300b01c00c042c010300450070404040b06020051944210a1074030682440b800c0241c1040841c10a0f004102c900140d0328040f4100f1880c0c0c001030700300c0f02c4041c0ca196a02ca50b1154001c901d14054045880c00450310000d1400d0745504210480075107109000440c0b000351240d015203100d900c41d01002490300742a0a0000d00e0842e075010a43d074180c9191180d00d000e440b990045e00300420f03d1041044070355440034041c002e1600804941d140c8142c0c00b800c5140251044000d90415811a0701d842151041c1d9940040e0b0807007801d0700010030b03c1e0b0318020380c000c2c03400a18903504420080c1d82400000f900e1140c102e20581d046500e0f400d010413441c6285810030510b90820303600a03050150910104e40c0034100ca228807a006040c2450010b000c01031912502c105030030440c2c2c016070b205100c00c1c9030b8001941602400380e00c0101c001042006405038900ca880342403660150904000e2500005214010801d080301e010315040181810314028074034181641c8042101c040e904001d0071004101c0d1502035000074 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 599121969 1250 599120719 599120723
    0x11b081803011b0c032a0f030206090a0302190302030730021506091f24030b0306040b07050409020412031101090c03151409010b04140c07080d0b060c010b011803 71
    0x4103074004c15102103030001841061300c05062080400c007004000481d150026141c458030304280a00c0701c50a02a00f040001003021145410070030381e1600080c1d021a002840b2103100c6048500000103040880c03a42c0103074080100070110900a0003000c482412004810b2240c103100c402003c0c00d00c0f2030480c0c0b40c9100506460b00c00003160081780c004d01e049001c0c903a10990440b0800701d510300c1c40480b0055003190341e010f0306c0d880b030300705404088400c54410f00c41c400500500b0706000d000f05000100780d4501000340050940c036401c1700814640d5200f60100c07401000c0784241951a00d0b181c0100d480307081c4a41e00c048001c502c10314034000240c0410b01800140300c1d0400c0d143c0008600d19120015414100f500b007a100c1543c0c0c1245d00c2c2c20001c45040c02d030048401c0d100005218110301e040c40222514070000c1600301024100300602918004c048814a55018401c551100d03841c8143c000580f03410b503101c035400784022070100340f20201507100e10340c141000d030f0700c98240307a80c454840f0080340d03d54000 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 599123219 1250 599121969 599121977
    0x15050d0302030a141908060901050d48090c0305070c030311040b070303090204050f04080a260103080d0b0108011404112124010e011b081803011b 64
    0x100140d94001d4000c12580813800f54880c0c0b406610a5905128002043c035080c08144480103016050038100c0425001d1324050310140b00717044142c1c48074030805a080342d2031400700e89280091240500c07004110700d480f2940680d250364800f401c840e05330149456018080e055498105240f529921902070903004506544460440d030b00e41e0380702200509488c1135803000c201c000f001f0018140f0240320007003c2c40c90299a00103980c1d142c1c0e00c100400d40e01c0c060074a603030705a4403005010106100070700b111005d860a04210442c05c0c10304a000456011841c01110105100c41c00001403290b840002e001c8005154401c2200d0603003007006540f803100c20302640c0d913445490682c0c401d550501d0703442002a003803000c00e078070b007000c0340c14032108800c030844007204601c1c0410806109450712080808102e40b1059040b0013140d03001342d40000d1116041002e1031341041242c6100e00c00b000c900304041417885400102082d0b4a00e4100c130000604030300e8810031806980307000d2400c882da000c10400d6507001da0340c40da1 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 599124469 1250 599123219 599123227
    0x60a060e010506071a0702030c12070308010e0a060801020a050c060a0c080a1517031b010911100c0204110a110303040b04060e030c15150f030604060c030e0f0115050d030203 76
    0x41c0203d5070042e403002c95a894003e0303e0f504015581c0261513115403440d9004540d41c085000299042954140129056040c24003444001076041140c060642d003488026074500d43d289241d540142066610014031544000340d038000c180e600000070002e0030400c00c1207480c1c9449410145084405028100c000584c0100c08200c0c11001c0750030001034400c428103043c2c24103440d005000e0302007050364100201343c0c0c000201d80c50845075220303108684440600080014030025201c2c100e1040399141c1e26480740d0307040300100b411140680c840342c0703245802a00c1008019011100a107a41c0d004000c0400071031203401c816a40d8620000840f441070394000480c0249890b1641d40341c5c06810390b4090040c8070b001c1480f50111403070003008580c0b004c2200c3c0360610310506020174269804c10071080102c1c000c18a010494070345480c0080c2c03154001c1d0380800b0000f08030701c8400c000c5004181000011100d400b5902c841d40b1f40c031074150040910043c200703010546076550b500070048610b00d00301c030050160308140 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 599125719 1250 599124469 599124479
    0x4030903080306010302090307080c0102121207033206040e0d051602030f060403030c1704021c1e06020301080d0f09060f120f14011406180a030c0e09060a060e01 71
    0x403001d15040b03c0103040160a2124100019040240c6600961031650160f001e4103a80c1d07904004403d0f03a1701c030460b0141c2c50200c0300803c100340341400070140818503850b41c1b41e0100440c8074441c00ca001c103c0103042940306034202c010400c12143c040d100c01e0700c61030401080034070410001c1110b00380031205031a010314101d00743c28010340c0e8561035807043c0e906005442175008032840074030609105903c0f0741e9000450354808003000d054250590030440c00c41700140204030041e1188a0f40a22940444420810100ea189020704208110341003005241d00709602080400407690055410784400700305481411040340c00443c0c10000201421000030907050f4100001c901403440d601d2070600d60315100b000c10000c0c807085c038140c0c1c0c400018145003940ea403d5048581d0074458403640541208084402c440d0581030000302e0070b02600072102600c078086c09101c0842e681d00041000115444200c03190000e13a542c2c181c544072030381101e1401285c0203030350020b10030f40c0c11413145c441511120745005075964200 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 599126969 1250 599125719 599125733
    0x714060c160203030408061e07030c090e1b13080c0301020f03010521030703111c0503070f20061b130603090f231005090712020a0e0f01030303060b0304030903 70
    0xc500283c2e094081003002141d025424003459200310b40d0704444010070800c0c002204c5031140c3c02441c0000700343c6081d8086040560003001e20048480c2c00400c0c403c981c80f1481402ca000190004d400c1e102c1100040400c02c40800d9860a0102e44001e01038480c031025031030906090340709448034519110b104000602251074a84940076031a41c12000040b0701d1004094074a14690210005030702144170344044030854a0f0411205c82c6410000350070380025908500054014000030302060b007849407448500944d0341c4141c2c500350548d0940308195001603070480e42a6207600041d600b811642c040e80c00075440d41090031046920343c00360303140c0000460340f82c038204400a140034801202ca10200c0340b10752000c076034419040020604006a44044560b0302d5521520302000400c0880007641000c08000c1d04030303008107040003200c44501e40e10304a040188000360880c08140c010f0710048400c082404204a00d10300268186c900c681c0701001100c0e00c0c0c13a4410090300049400400144c0d42d11001e000081c08 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 599128219 1250 599126969 599127007
    0x30403030c020a08160c170a080d2004080706050310120f020603040b0a05010504090b0417070506010e0a06092d0f020c030d050604060303020a110303040e0c0714060c 73
    0x2180305903414204140c2d1a01c00550081700800c0e0705155500b514000d101c2d010405400400e0340310301d44000544140d60481d00c680c01c21601818420b03010621142003542c6030800039030315502c0e480d10311a00b48445030489060700540191401c2d80304054020811a0049040b80d005131400c0e8240c001c458580205180100a038020449171055507440030801a203404000d10700951003008000d5141c5401480001250070503400103204508203682d0070301050350700c451181c00a40002816080041000113002d00b40310303411006085218220002518041c40313000c10303001e049120b90030b009840e6a8011642901c0340450024000035800da01803103805104811039001ca02e40d81d00108402d012011072404076005111743c8082034200082001c04c211503403040d07940c00074040301c0801c101815500c00950300c207100c0c0b40c018010810900381242580e001c10a0350300030007860800c13500764605442104c01641200e5801c44580c04d04c5c5002c0008140d000c1001842144648100c60921400305000c544000c1 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 599129469 1250 599128219 599128241
    0x11070503070812030a1806090201020f06103c1a0f04090c02100e0a0501110313031b020d120f0305010e1f0b12100b0708120711010614180c03040303 65
    0x303070310446c0b400c20802c0308441a40c1ca901a46c400214010a40000780c10080300d15201480340e048241040301b030380e0326122410140d031030404154500201d0141450300101000c40c40520110a19031200b050903403143d02042561001495501b509480e800f082c0b490340184003000c94255018003003408100420741c42140181d41520448034138652010200342102c0a90a40741e840390000d041080900800340119002103144d0804141b851400708820030b45070591a80080401c00022074811554050304c02029100e9001007440000381410314042031055070403139030b11000c07e80e200d081c44c03001c600a100d03285c100d89060b03a081d1031580d590289144880320f280c0d0960700d000c01085000c0b42d040f402c4400f8041c1c400d00c082c004c4915052603518001c075003807541d11004200c4800c04c05031002a0300c0c0700a03607180240e808120542925030b02000e0355100707070310312082507290700e80500000c0044903501c070400480000d0b981540d200c002244e480124030000c68003041110000c10106000901c81d5104013200c0c4 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 599130719 1250 599129469 599129471
    0x1212100e011a30150306130204200c03030a05090a02010215060a031505010515180f130203070c02010e0105041d040206070b0907030303110a1b15060611070503070812030a 75
    0x901c000000c5800c045000c0c009281d441d90311040204059144c500c09100c00d40071801403031a0703e80007031075103002038035103038024003481e01c40740084600d04184001c80e03d8081154441c80d182d0300007029459480e0401c80d014045903040002080e030080d40410f1800b02c0f980c041c1c2c0503000708281d201d11b001c4007080103004184c000c2da0000d40000800c7d02c400310203aa01100317140201c0c0951420040007000941810501100d46003005144512a10441c400c01052000d039041003c0e45070381000a03600142104200d003d0038000800c022459901c1040801098400d0300c9890324004c03001d0044900c0c0c00f440c040e01400912000f189075500f08251441039105100500c95440c204603599112117000f401c0d2203800195000b0b100a000b003541500821400a511900d01c0e8140340c1d11060017032000d0201048400c4180d0259802800c0c4161400a0b0818401c1c117403003031003041c0e910b210040c826418200007400318018544041410714006c211034040318090303030007444039800304625440c01c1e61000e01011001d03 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 599131969 1250 599130719 599130757
    0xb0f06061b07170d050a0e0301020d02070305031b1c02030c0732150105010c020a0911090a083004050901032405011a07051212100e011a 60
    0x8103924840d441c1100c00020050041c65107061052a0160f441c00b0040040d038101c8600300058641c410159004241e80d45032004110210b180801c0c02071080d07400124109000086540600d504840118010b0350300d070040e2503c20304031401c2e4003094000c105102d41c2e008481e07035098418065a03000385410402d40c800c03d070b113040103c0d075400c0c2c51081142d00d00c034241809a0004a10741051603c0f082c45c44448101800700442c2400100810181c14010345051043d5001c240b410f5441b00d485101c00307000c040c8000c0200d000040d0301c46a15400c100d41307007032083c10a14400b0030202004100e450003600c3c0c1e80b400c43c080301d190188140826203203606065200e201404001025940c01c583c0600840c014401d030042c48220520541d000e00d030401015040d2400c00c80104040100034407000e550807030620341c0e180c50f800d103072505a08244102d03d56003500c0e940400d007100f01d50104c840075030240c0f050f080f0503031450b580c484503a42c43c0c0001b440743c0654144142c08022210700c14100400001003284042d9203030b = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 599133219 1250 599131969 599131987
    0x1209030504090f0b0102150c0702040903021e0102041a070f030c0f15020a030f0506010e1002010e120a030605030d020606010e0a12050109050118172101170c04090b0f0606 75
    0x1103078403544203a00821303151500212956010302c010014001050f022185034070300f62003141c201e413213162002400307660385800050516100b40140152602150900320102841d113441d14041d40060060300e0100004011500f03840300184201c4080da0742c0043d005200c050161415160706d00c2c110030070381d40700d030f28549140000b804200c090310300500b00341e0300161203110f030110040c00ca82c910708a4407070380d80c80e00003030011030782e001483c0c905881ca007103c0070055043c801c0301c106d02400390000c043c240340c030071481c0802c501e214400107010003000302d54041181c00d50700c03c02c060b0358014404032503015070003c03808a505944180712882a0100182440880c2130f618a04426029141501590981d658110310000c010f000c1c090b045015500b11114000e07007100351038007440d03848034070000e401208001402a8442140b2000031005040560b503c848940e5151081d14a0401003404520507002e41d05580804c0d160503c94117119503003100c034041240e80d4036001d040070f01d940074140c95409030042c440600 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 599134469 1250 599133219 599133221
    0xf0304030c0b030a1b051e16120e0303040e040210090b18041b1d09010609090e0f01090804090e01050c1b1606030204050307170a15090f0f0b16120903050409 69
    0x10b210f050f20b0395481da03511044480c90100000c0c0b4400503035547c4081106152600c071600b48590600d0b0054800322071100640419202054070b03004c825054040445d00049030485480c4146c4514002c1e1180031610380e0031102111000c201380242003401d41c00788460500445050070f12145050302420010740b84503200f0101002141c1151720b00700140c03403c4071010400030b0680e040c12401d0015900e40c5059418030b40f018210f0f10b100d001d80141640d8a80300c9084010040003d0081420024020001c0c05000d0401c14810390160003601c020758280f1085a01041c014400d41c2e11860300d100c002803d10721440100f041c00050680e500035184140c40c08000c010540e00c0501c0b00808243d2070060b0307241e1601d07040c54108541940b04400d0f010301c81000284610002c11108000c3e07501c80055007a000c2c02c04ca0000091040c80030140c000743c00c01c241c020030061410300440942d07010390000c0383c0b150783d0b2554504513101a0010b020010b80c001d03080114020030b640001c48207510030b040c003e05058031841410 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 599135719 1250 599134469 599134511
    0x2151804050f01210615060e010908070515040b12011d011d06130f020301050310090203120f0412030e01110105040309060503090c120a4422080f0304030c0b030a 71
    0xb8501300b0741018100a041d41100d00040a90400c2c20041c052b1440e150010340c80c0c00f211701c10107000d421548029941900400d00b1580a4242c4400a94844543d28008010702400f40250005188c200050100440e0100c483c02d048a044140110000d00800140c082e107010180001d90451020240c004841c2c11070300400e00c40c0320a070f000050b180c1d0324010406185c40b12075941c02c1201482d06042d500561400310b1000c400129602d1101d0783c0341d00e168069031540c440c03a4458046055002400402c0591084491819a200340ea8520302d84840799141c500721001a5001000305441120400c441d50040010310b0303000c03030450183c1d182e803030780c5002103280132090801c00b1400382c01c02c4443c174040040750080030340c2003040c0c0403080c01c40e034003401c692143c5105e900084242800c1092748030518108a070b4119021580c0c0140034400c1c1209110300060740302943d0103605003e005809200c9030035600007081e10308607034000c040590440d00d0706070000b00540c005851810400d03103911001901d40038440c100 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 599136969 1250 599135719 599135741
    0xe030303090109050705120309090c07080406180f0b0d0b0102010e01061206110c101109040c051c2d0902210d0903080d02031302151804050f012106 65
    0x480e2544481c5021401c010203600f20521512180080c080701d050000181c880c89c91081d2002055034480e591000f07078074010244010004200043d001c034040b0350111041c4282c130b4100032000140d58881020303010240b150b00400e800708909000303e4000a0040d08040350241f810300000a45882d0324105600f0740761f0b5074000c5511150b9800064081095500c190b0300068608010641060ba0071000f80d910f8070380600b0a801c941c0d03192052075038001c2e14541202c0d60600001c10401c400f20390303890041d005400145149041b888010005018a5000d000d401505a8550810f851100101d00b9070000300e502c0701420b0f80c001d9900d04881c0010317110041c8011726a20918041034200360b014034020303e0018030071090010005844410000264240190340c420610300c44003507102e95a0b05110f221b200c0e54079170040e51202801040e40c000c000c4400c002d00c00700c450040c1140e502d1038020240415031304160f44520341021a900100910b107001003a81a00e41d5010900c035554000700c0e11028252542e0b1412 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 599138219 1250 599136969 599136971
    0x303340203070b18040b090c03100e100602010b1e04150f0b120a06060c0204090501021c0e010b04020315040e120d050f0906040c1a0405030106031101141314010e0303030901 76
    0x2c16000c1c010130210200e2109044506000d00042c000201c2c3e81c44001810311a44a0400b0021581000340104030401410008146005500c0c0c140005501e03c080c5201300c8026510301030414495013403060580d050039074494100801c0c0401300c4d05200c0245039851041303d48001046010603a901003ca0300c0005103040451940c55a1081d074641800c84070241145e0140351800030100a510f8101c002424130347c0c0c041b100010311407554102540640b00d030000380c1c804211800b090708440c0100e5444842c2a103d090020410303045000306000417448103071003128050302c0094180903103150a4001046400c20002640c04080d4800b0129116400c4082411481074881082042410003090040e902440d010018860f506181d10b032031510103464001c9424403486000102c3c14103115108031002400064020003c0c00d07640d0070021255504401920300090162840681d812701c20f1058445ca0b00035070301c0c1e580442c0e00d490381800c04e040c41d03c060341d41407080d100f00104c40d40d541400510b201e6243c80700 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 599139469 1250 599138219 599138227
    0xc13050103030e0a0807091e1401151d24030a050f0609070f0e0418030305041a1e0712050412110d0504050d0c09290303340203070b 58
    0xb5000c2c2c80c2d4020b00242c240140c2588004100715040050300c0c0007203e02c9030354005140300c1c0b80c90340003044944007803011083c54100000c8078010010950b500e07048803440c007020542e4207000401140d15680303658440314010803205c1a11703030904d492107040c039985403c149400503e8103400301c2814143c2040780c400d0300081d43c80c001c10500c1003410039107076840003044600d01c485181090000c1c006000b51aa40d600304000c181500319242c603240d02c00103103241900c800c1c06803007019160003406084111401c81d02d540e5261205184160300c500c1e00d50040c1c0c0011b40c9035100c0b0540c500c44407580c000c0140400c080000484005000c10003a12407140900d0144012044103000d0f050090710801c3c0c4108459025480901d001c81042c4c2d02c6002d9405030303101154040400300140c00d00c1058261650401c54205141c01c40309161010300706001d0349003008a1294985507200f22042648030b0103028000b070140303000740400b0703100310703400101e0b46c0030001e8507880c840c411410700d801082c94a080394000450380c620002d = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 599140719 1250 599139469 599139473
    0x180f0b0d060605040f170a050601090c030b03010b03030405120c04090f020102011506120b0a170303060910050d1707050a030e010306050a18050c0f0c0c0a050402130608090c13050103 80
    0x1008203005842c2a051403407a051500e00001600856442120200050301a5980d00c002041c030201d0345035500f29040300d000e542c40b08004001090ba4101c514046840d048444d0902d08040c001c1d151051070041c05582002d2a0005214194201d0200000d0502481d2034004059481c4c1c406c2c000554002c0200c800c80d125584006400c4819813101500c803d4400f1a040110990120b04820082c1e596440452410b2481000c2190400230340c002848481c0d4070b09612280d4180000518803a4100301c0d141ca04a45403e0031822800800b13014030754205070b41258075008226041c9100700500c09410180b480c181c1c150315040d042a1010004800040d0500b40300c3c03505603850b005034006402e044502d4041c0303e14210483c13000104075100355840f651100e0000d02c100040c003042d147c141c050892640d035035490143d4440d8841440101c0c980c0320321407107107010031941028800e640310a100c0600e00c1c00c61302e09041c0c0550703d6490080c21108144283c0012600c00d817203a05040c107825003e4400460254114 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 599141969 1250 599140719 599140721
    0x6070203090a06030513080f0409050f061c051903110a050601090b030c1c030203042403050f0601120e0c2d032b03111602040b01020606030a03180f0b0d 67
    0x20f03900082c1003509240c00d0091142e55181d0003442d6980c0620200c0d5a01789620075141a4081d03688030b1010b4a291200300810407900c2c0600a1040e40211016a2500c0d44c1d902c10702c06030026144041d0290f8050281443c0c8040030012200c1c855001e401c1c00c2d40c0c1e10110b054102c1c54048040400c86040d00244010050b0341584e0040340308004048029008000d1805c001c141564204101e10501111901c80d00c030605009108440244c440124408180b8045c10780c09002d02d0342807000c2e440043d26110000302402450070600e401080142d48003021900c8550400c4c014040d04070a0cc2901d01130001d80105950303400c048182c01e407485440408401510103d07080703c80c405e4004240c000e41044102005100c850b02208103818054648045e00d403200600450003041d000c003620100100000d0360440480307e081800070320034421a81488489140001203850741c0094402d030703405034071040c0441d000038020a01c640200b9110706d14034010030754a8181e442409841d6100420003c2d000841002e00909 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 599143219 1250 599141969 599141989
    0x118110715090311071505030415050106050714010501060c020603060f130b030105012412090f060b030d2a0201020c040c1707050a1b02010201021e04090e01112a0607020309 76
    0x7500c0c000d0b0406502e0040749070006e1049200308001c003d03001002a0400030040010300e18203540706010089581c488170050701030342c40340f01b043d50328582c000800017803030b001402118107a90803030742c900c1c986190300d509200880d080580040d500c488440c03540b81043e150107035108010241c00d0b402049542210080c1821035106800218202503c07082140b04c511580710442030041540c60031010200486d0719801c01820341c0303c1d00a20341050f240e900c03c18007880350000380ea142c50450030b0740c2e12845840001d84a4025140450200c00d001c200000701c00383e080f420403005c0c5070040c01510f0021801c440044c00b281c04003410400464180c00d00306401e42d0415021a52220050900300e1402d0040b0102034502000c10a684010030ba80714070460459100b901600c8401c6801e800e000500602c461040300260000e0080e002d43c01d24058001d000e07030405000e4104400b0680390759500d058204071030035000381c40710505210040c00c103103420403640c03404100b075074400e41c0705a0186490f11902410030581c3e00e1 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 599144469 1250 599143219 599143247
    0x20f0109081b0c150304030908060c07150b010c06020f090a03050615010503040c0e130213140c040518060117070c0308130b0609091c020304051801181107150903 71
    0x803015061001980790341050484020f400121130b5102e940d94541103881c190540c0140d0a280a084184441c420144010340f04c0180b003038440451a40c0404104821102002a070034005004110b030340c000700741168020106400705850031440d20340c2c8040401e941540350745c0100c0700e961105040003103000d400c110000c500300003440e1091450516466403d03800e0302502801c1c020700025000318420b010a52440151f01b940900401895041c00400000600c10300644014290700280029400400d103003c44050712001000c1103e0a034080403480c1600000a0159043c02141b0301d180d11a0082050100d129003060b6039000c0034104549802403401d2009045045400c0480d1051000070301c014150302d41c420410385034003107507035104da03201454448208030715020300904004c0d00700040e034048010410fa40c4c041d00d07004443d03400c400190303440300e400b481580c861610f07003000d203107806a10750004071904000b514021709058490700c40301c030030241c8035240ba460540da860400003051b42104001c06514 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 599145719 1250 599144469 599144473
    0x1d07050312040b340803090d020d2c060f031608010e010605161209330c15050c121305060a1107050706020a2d1101020f0109081b 57
    0x24a072070305044a0380101c68000003200130240080501129031550700c80c03204950a40001e414000742030244403980181e038601118001e956841e85041e000107510040004503580b090002c524003180d61850401d107955003d43d450004d407240c281076445901400202d050301a400d5902d0078003807540000000c600e20142c0911a0034001003202c08e1569208074119107490400b05c0c1c1d91071044001c1ca40b14032110030000c2408007640401160180e00c180d526040d11540d0748511400c050407441c0041c40200c0d0f00c051413103171106400400099100304072211f0060311583c0040e074016441c81114061f50402c94841907403d80c0456004c0d0700c0e14007400180d40140ea812900c51040a1a0721502c2e00d4050041c000f00049854002044c0324251030421030310745580207801d40d81c0c010b8903058000c1d154001401306582e02d504c0054009100103041d22584896102c0d004d0400400e500c5542e00c840504114850034158000c008004280c03520070700034440800e109e40c000c40d6030390044584c0022245145480090300b6 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 599146969 1250 599145719 599145727
    0xb070201061e140d0203010b0a0306021308010e07030201110307050d02150705130918060e030304140d02061518090604051b0102100e1903080402040b010f0503040204090302011d07050312 82
    0x1070045010442100f0b0b038130307840c1c0c000d8070b4004280500322440c4404e4103e1250b0b400041404050381c058403820300240c2080000d26500d034030712800ea501907044002140c120f10010001980621070030004914404141d9050503095118941041c180e00072410142c1c020014642801c050084603660001030f5003442420044010741e81290303501a406442081c950315140c02e07010844400320313031921941c41002400066114402661690003d45085a0b408164401502402c4010400f020000f66550041c18155079440f81240d0b07099881c01400d0700300c2c3c900c54441303444582400c1c000c2c4c440d111020040455052034506140741406001480340928000c02c0c00c040d4980e4045850500401c2242020551991000c88681014658980c0e032000f10420308000c001c040d00455000c0c41107008440810050001e140107490841101382007a0001d4010800030b40140f81613484078000d035000344000a4005d0307c1140303440101c22103541c91010b6501020f0200007034502041864400d00f10594100c1c18 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 599148219 1250 599146969 599146979
    0xd0512010f06051803100f0209090a0204030b0a0203130f20041b0c0204180302150f071202070609050607090e0a0b030a02130e2a0108070e0d0204090b070201061e 71
    0x404c0c001e26201c0f0040210344d582030041590200400800951801810440050080b004100035806440854055042c05c0001048800e003842990102c0c1d03088203408070642e0f1201900b800a42c00203113a0343d0084c4020840d440400d142030180e0380d00c2c5105000c03240d50300c2c060424907500001501c540a03c07850070000d40c418000f5440340910340c141c02a00b40954443d01501c000b41c080d09180321071307540d501c81c10b0360201c0074564001041c84c400e22000048202c1e44c0c0b6015009850100c0880d989404156000401000318410341d0040140f213018410000b1034081c1030b034440e070030728006503440000a0100d010510540029282c007035040742404030200022400c1402198880340001000391180c81404454442940c45402500000a064040d1001c010003200c0400340051039040400a142d00c82410351050750042d00c80720300a507100c0c2c44140c4040c2c0c0003010400c03a1485800e08036000f640364502d50340058903400701c9a010700c8154001003403d904001c05a42c09640900300504110520241044 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 599149469 1250 599148219 599148227
    0xa060f061805161803080f12010909050607081f03140c030708060606090a1706010f0509070206190b03011a011106070e01051e0c07031511030604020c0a02030d0512010f06 75
    0x4050315a0500780c000c0070b03426000118859180c5c0c000340c00d0710070000d403800040c00f10034010200501c080c00180c000c0e0340c842111604030703522a4001070856100c103000c518407900840c45076a0001901002c141107a203038508605004496038000c40310446050501292a40c00340a0074044600540c000d2a003d840c01c841d45a8a0f103000c2c0c80280140c00004003404692110344150f03018203181c028005868811482455a8000034030441b9003001111a0106140c9410076002c0d01400e0640d0007001251502030a000d00d81d000b5420480c68a540c404110815481c01c0c0034485907070062407180354024511a00240555203000314864031034101d4420811421341020241803402d2081c6462900c0c0c0c41580c14090030740c0700c0d0019180381c0c2035010a803441c1c0c0c420b00085142c140c0b4414842c031902e4581550010040c1d808810620203d14402d000080890a160b400741401140c1c3c0802c40321003054540209003481210f1003c1c5001440008090006546c041d810500401614840e01041d5141a070010 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 599150719 1250 599149469 599149501
    0x423120a02030733050906030403020c011824030b03070617100b0301140105040509180f03040609030618080a0c0506010f140f010c05030f0c10091a0403020a060f061805 74
    0x10b07413030364800f24091035030ba100d43d00b6078441d6000138101c0c0d542c074180743c2000380d9a80454400c150010b0313082c01006e080c003d034041100c01200d0a0703000000e401c0a00710441002c0c07005640700d1104043d520982442c4658003000b11100800d2507807544040b42d0024200e0b00f40008004010002d5114080d004203c424984e00449044540019400c556055054012a8607105640c001ca602c08981d44c01d01c8000e0440d145520202c1c0748800c22158408100311049482e8055441003802040c06510304001045c1030b6007014804482250801000034080d80e910100d81c0c200c0002e160008039500643d2040041c2009540e015203100024500340a1810300100885a14084041d00841e140109181903074003a900309840280c0c03000903251228068848207016810015010515215001d00c142c50303141c142c030500501c03907005038984e1003444080e000080b5103900608220704621034008400045803203132040c0141e40c5042000401c5075480d00c0141030300340c191400c00b28000f40c50310040c0000c10018002c0c00c = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 599151969 1250 599150719 599150789
    0x90a0b0a050f0d020408030a09060e19051507060c02010603150603110d05010219050c100e10020a1e0c1208240f04020d050405010509070b0423120a020307 68
    0x11a0f4490020722140041c0c0195401a0700c01d100108841d0740b038075002122281070381d501e40c0c0c524240307400d1b140030804914140d6015074107043e4170a40502003801e0020580560303841d0303074004500d0000c090350740c2011911801d901000603507482074107004020050701d10700c00b0b07600030b460140400b81c2540c81e000c0c002c0c994542082e11903082010050208142074040d10910303a40100780e45007410b101c400c050820b84c401da0340b9109074001e100b5042c101258900c2038201d0350726944003c000b100d640c0405c080003035020400b20800d001d450b6007034202180154005d01c0819510755140c3d6924126031400717070603501905541c001401144801c010440e0031400822203500d162410602ca40b0900401180700030030f0051440da085400024103004190198201500a41c0b040008101d01c0e9a001042d6407600f109001c1c01c3c2045030208420880e410300302c9070003001039204410f1700042c1e100750400516004c89024540517250040d000d40da0035860306009050041c800d20180b41340454009030000380d915042085 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 599153219 1250 599151969 599151997
    0x11030a0c060f171504050c040b071106040f2c0c0306011d0307030b040c060c0512030a1d06090f0c0312070510050f0f0603011a24040b090a0b0a05 64
    0x1c0040c2c0d8490794a00703901d80400c0b100d08000b8200300700400080b00100200b103020304d0602010482240d4614100c5080b20042504a420b0017041e0b6910104602e06004c5a41d10400c00e000c0441c10b903816410400040c00c200d0001520385000310780440707400390034002044600c07075401d04008030045034500702e80d0700120900c0d00c460441c40801e000300d900d200710700c1c11301d81601c42d085002c420002c80000003401a0b000b548010f41860742e40d03004580c0f140c248240185240c020454141201044901079900b296032003002241401651a190f913400c1306000400040d54408401d00c4017a010170b02408c0480400d4001800c2170907052004a944c4172080c40318082c45a030300084503014000280100046075022000610540c182000000c46460b002d0b154100507889a0700490440d1405208190314061b88018014110310044d08000c00d80004201268001003140171101c498100e4000400207420f00c20741c0140c0b0b45444600380440f01d0207030303045880c8858040041d040c01c183c0007001e680100d9400b01c8 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 599154469 1250 599153219 599153237
    0x9041508161a0a11030c030c01060e16080903090405131a060109060c1e060204080616080a0c050c1e010b0d0b042604030302070911070210030c0314040f11030a0c06 72
    0xf8040380c407030403d8601c0c0980741c003020603003100d980c6000c0018850a0040402404500c0d110710a4218090080d500780c0c80c410380c01c220f200101c0d40543d8040e030b8401d8600b030980341007120050220301502e404485d40b01010204500350810420400c250202d0040600d24521441c6000701c0080d0509441e4081e040a004283d44008108400f444070030b5402c450744c04214a8070603692600101030742040c0980d144900814000800c1c203144602262206031503580c40406944400e1030310001019007400000411808000001900d00100100501080d80b05080301030030b0000451103003190704c00c0c0000b03842000d14540c10808100c8800c049034029400080010003000c400c6d641030b103030161981c00380c0f40f0860042000401c0c0364021a100085607118601407000b250702183c0c81c50300e41f0a070134009601c81d9081c05402582d9100e0b601c02050605142000a0807120102003e08000003c413000c07110011482c0102040002d52340b100880b030755082e80107049040060380c0386220b205090081c8410840c80310303 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 599155719 1250 599154469 599154487
    0xa0b040209150a230406050d11030f100603060b032d0702010507020c0a050303070f0602040f17010b100206130203120703020c090705130b0f09041508161a 68
    0x6411100c6524000707080122115100400010a40200040501141c24140c241c4c00d01c1101c4400d99030541400e105043c40c160074202d043c1d0300f43d0030840141d01e401d0b580b51109014031034040e000314000c1d00c4031140c0c0d0006150806004160340d01d1504520b04160422108110008118080e00d0b0052201d94048814030f82d5400003000000c0800c15038402008442c007442009601980030380c0c0651910760944150401c26400e00030f1090452054a4041e48204104000704010420700444d00e80f01e4103006d4178050781c5000f10703030a0004c65040b08216164114090b0f0100d0001d00c5413881c0e0300f4040e2551003401d005030390060f4a5140003041d5030200c0743c6250740f0703004655040c04140c2c80c0c0b00241c0300c034645580b024180259122040d81b481c501442d00c030700210301040e00400681c0c03c1c464407000005e11a41c1000360060341a041100c2d03c0003001070501000b409030f03486003e41e40b030381403101203442c440d01c0c40d1844140c40d1508145022190748401c034020301c0782c40c0744a864582c004848640103540d0708605 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 599156969 1250 599155719 599155721
    0x30405060c10062c070909091403040b0918070c12050409021201060f110303190f06062102040506192706020d03051e130803040f0212030309060a0b04 66
    0x2000302020b00354a050808142d889040302d0505140d54100d4150135402c0c0c019071080c0d42140262032403004503103504801c00c1030480300c2d0000c2c2c4140c0e11800c1d041c9071480d0700f04e5006155400c030f50001c0600490204540010342024583c07404810039005100540d8240606c0c082c2400014041c090300180c0d24046000089001e101200d0040000386011035a50b154035001c010046001e0103200d00040317100b012441c00314422112030400c00da0f101c01440c41c50b01d45071400410a1110440b00003099269150301c0311107603141c0304000080940b5203481c84441100c1500100c0c1c204000b1084510317900c144010300450315400107032055600e10f05081400d000c10140d00742c48541c03105945482c0d20441d84640c100e1104020100e00440d401c58084030a038580c2aa02a000d640085651080380b03440c101c021511030003010121500000402084c1c084190380da00d50b40345943c4101c03002c5e901c60641401600031400c007169082c4070b52940801650450400312541a200c040c068130301903829458090341c040c1355030f031 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 599158219 1250 599156969 599156983
    0x110c0d030c03020a0b0a0f06061d10020124060311041512020f03040507060e030316020d0f080a080609241504050d03030b0f060a02073501050612010b0102030405060c 73
    0x40c981c01d2585007171a03001000d4107000c500c0b85401f41c242440040d01c58010100a81d039100061040311f202c105010a02c015150803241d580b0843d0748403c24020101013100d810031400d10000e80d070380e414138101003015043e02c0b400fa100803944e0404110802100c1c0070850b42541221452401010301130700001000c000c0d0041403206944180700005003c1044400241c4a0417144187c64441c042c02c0e001c0c007010744900800450200b4400d1403648400140b410440d1540d41034407030440d800200714580c03640c00c2a90428140300d0080303628001849498605482081d922401050300e100103d804011242c0d18002e402c035000d80540d4803103c3c0c4000d0710b08504203031005450301a14040f11014281001006032002004090158030500d003a001641400070882c0c1c4400360a800500c40c0c00d00c0d04819000b000904074144e151f880126000c4107401541c450070396186040400085407a003021030030030000b04491340955000b603250007140c81c00b590b00030054604030b40d03041b0b83d01c641380d4001c0b480b40c0382403000c = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 599159469 1250 599158219 599158223
    0x1005040c170307060c02070b0714030d050f040308060306250c0210030c0e150702010f0e03010c110d0816031805010603061e021e0a022b110c0d030c03020a 68
    0x54149440407440c0c001000d040c40a001d11424010000804030a03070321007856000300444050b00300511b070007042c0024210150b00c62114100c0f0315001915180b0000c54000740c41d2324440503074003024041456404500160000c00c12405420242030240400281d10021071130000240c640c0800120164007d0030510740054028180f4228154140f0004004020500d580030110f0312014040344c0b10305240543d407680c4c611041c0d0081c45c01e400703900195424990201c6040410956100401c02901e0a0286003101400794075400f56501441a1081c10206000c0c03500081106c1d0341c04014115007a00b0001903910000d050000e5070100180701081d5540086c0805441903080010020811506503c203002c0b03a5643c5080b050b441000415040c2a445080d10008541d182000d14154001740c01d0010850701c0294012030b0050324a42410410700035445803101c0c3e128005102c2c0d0304c40c440d000040e151341c0c2c0ca442c9001c2e040780040440000c40d00da070500009406c1194104c20365003018005c100b940e00941e = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 599160719 1250 599159469 599159489
    0xf12040f02130f060f08071a130b030105091608070e060c061905060a060815040603050604111309021509041509020d2d05150d21080601021005040c 65
    0x1c1d80082c04020340310907000340083c075152400024000b9040d4041005544445000e450018a01110900d002c1c801c0c0c1d40240c0440410098a0490300200861000401115100c1ca0b260742c0741c0000c000d02984024072064a0014000171200c3d40c65100042c103501000b40d06212030010b1018001c14880e000d80358400b00341d44039100c1400b1191044140480884884210031f0125645680610103072090074803a00000c00e44010114000031081c0150180303845000d000011b005540351901c51502400b0313103080c0c903502c406040010b101c0c181340d0300346004030300441030500c4040041c2d4041400810b60303004400c82d10002040001031951030b60002c035504404019040842d507220018a0000e601940d03031064074916104896055101440e03403110580191980341103d8944001c10f5805400024280465407000750009020380e99440043d0b04494000d4103003403484240302c6490711400030161039407030600507840c0c10014540c1c2c0c0085c600043e40c0400300081019102c6150000788240a504801201 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 599161969 1250 599160719 599160739
    0x14030609130524040204110702090a0b030316080909010e0114090a1121091f0e10020f0d050a1401120305071205031f080c191206060302030f030f12040f02 68
    0x803800ba003c009014034001c6904110484059900050501c0380440c003c2d0401484c0d800225429001d501c41c42095030041e05a910349038a111881d10391880040084034550f4000c1960500c50405000540c05800e24500c03001d040d50510304154030610310802d201c3e01c29000d060021303224038800e4004210041c02407080c0345d101d4800d40c03907100010314401e003180e14500700c0030005441254001a40104441000c07008403006600030000800750400284005251103652980b406418a40c4000e10b0700240400740c2980341e807405a10041a1140541101d9000b401c20051600d04850206032a0440e480d102c50002c10a01500c1c05940601403460080d0400c0d0518221801c107581180080d8886e4201d001c90160000f6443d204145025140c041e60741145d00c038007006841030038210094406407065011140c1e03001c3d1b0b03400ca61041810b01080071076605844003410000c41c241003010000c8800c4080141d81000004411005070307000d0140d00007451305800c0c000c00c1c2800411b8064001132078001e0110100 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 599163219 1250 599161969 599162023
    0x30525030c080c011e2015010e01082109190801060308030402040b1002120903030f04080d0f08090a030804170d090507080a24060b07060c140306091305 67
    0x5074102c1010701d0380490501e42042d11345c02000307610600e1364001d079102d130704c18039120b4100b28100c10a240120b0140b8400c8114111140e130741050f155000300010640d0300c203150b041990244c00d003680712440040502512442d4110700108205954007801c06030340354004020101004a0288025030240c07025510303049011003030001190040d0310850094a040c4104a00c0c4424088413000b05614100160004542c00c1c6c045e0345da03c401400351607001000c8a04203070ba800348044803580240c0c403120007680501880b24280d074102a000c0d040351942d040c400024500865090b46484410400904018801340003a0400c000300b005002c581001e02d4007075455482003240d280040036101c500ba61544100480020800400540040380701c1d40140c0000c050303500b2591070480c1032041d8050007101b40e220301e408524003400002070030465010b50000f00304261a1000502042d0380103a000381040000c000b000b00d01c1e21150521a04080c3e0010280e8044e1903500b415401c0011058807545030306607550b05450 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 599164469 1250 599163219 599163223
    0x102160e0402360c0910080f0a1e0209010201020d062d05030d050f0706150e0c0a0903031b05011a120a02090f10050a090f1401030525030c08 62
    0x32203180b00f510102c1ca00290480d4590b81e6221800c0300d880d64003203402580a5508010300300c65004621501c4280c1004011030018940d01c8103144c0310300000300081e040001c1143c0302c0310001d03040a042901044030840320350f402e180e00941c4003c5110070765000034071400341e83d00c00d5040310700c41e00700c100303040240c19203030605100e2086064507208805950080c407144501e0b5144510310403240020010803003000f40010a40b003d412040b03c05903050405e00041d008906130b4024031005070aa422107050392410103640201030100034003040100c0c08144001d100c0315421804070b4098913054100401015107041c40311200c1d02d00590020502c0d420280d0902c10f1055140c9134841c910000c03030b001403802d555440800d9581c070310341502030350200c0e111002c289904415045c150304085002040c581083d2658080348400300c0c01d030300c01d002c803075035446030480c0c10703c8140300300c0801d44040e02c4a22103e500d0b50b2100366841b4100d40495100c00703403044440001c0b03035580621600556011502d442241d40e500c03440c0b5 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 599165719 1250 599164469 599164471
    0x4150e090912040909020127060215060d0305030406020d0606030f0e1207080304051002120a242d09060801110313060906020405030a0b070f0c080301090b0102160e 72
    0x280c05218950082030aa4001061030024845200002d9081501c0c00054001800d6920750690512608005982c7c00e540500c900054404429028a8600345454002882d0514201079a04c18140e05000d01c112035071000c600c002d1580d003618000d43c0b6502d460034444000c1c4525418068400e140250004486816820026200c00300300030400040480010031078503021600c03a52501003000300008000108040046c5410078004c8085510340c07007032008035000f2680400503045007107081c0010887c6c41c404600600340a892011410342882a40c001d51000410142c06004400080180c440805130104200c00130380e07a00440c00e001c0626581c406c3d01e0300909482c000c030003071035091000081c0002c544200701c84c002d0400080c01c0380c01011a840e00310040002c1c1204441c6181c0802001503540e40420106002c58081c1140711100e05001e00048d003995032440c94542400500c0c840744010500440550b411211800c402146600721000101c4c144010f0301d8040d40304010340000842c080886007401 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 599166969 1250 599165719 599165747
    0x60607021c0f120906091802070210120b0d030e01201f0e03030c0703050901020a0204050103061401060806060702120a1b0306060806190b01120513030305010b03040203030a0c080415 80
    0x200212214200c00311340d061460b00901010401c44c02c000c01200324501030340302102054400c010f003808070070350000341b030541d415421700c000603400c640e0010026503038032a0700c0c1544012101c86031280c45566026090300d0102071114140002e50414085000410342c3c0b440e070040d05039003334036155007100a404454155101400b40c0552400c2c520800500001048071700490079080703803500340b0886d6507040f83c5c50750245c04901d045008416800e0010303110f07802118080e612401001c43d481d01030801540d16010160701010400031280d00303021241e25041d00729040107030169242c500240c94807040382d251500360303840109204075060000c0c0203c10030f180e110003a644658006c0c844a41d031155480c0d0b4552095496220090340500c0c80c101e41640d0b0783c40b02d0304050060408003010315038006002e0403640c040b164010940d1040c130f8076104042e41841454050840203020034114102500400d651340141c146050510031b108d100d080501041da800d90f002801216001142d904a51400500101440c80d030 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 599168219 1250 599166969 599166983
    0x140a0305101a060301030b130c0e0a050402100f05040512011409010b03100b0105030609180a0606060f0305040b0f0414032214150d02071403030726060607021c0f 71
    0x102c66038614040f0704890490790004401d0740700341c41e94501e002802d140d9040480741c00102000008001105403800d900c108028030000a441c90a40107000301c003a00d8900c400108589085c032880015001800d40d0b00b6904140c604080041003001454010b0044204407140315100c3c0c0200090b41c0415004a241007a094056420017001406c000e0107441032520303410701145003800001c10300d040c2080f45c1c560040c1d1405000740009030300348115003030002c030403c01d444203a1910810f0007410303044800035208008500e4108004d1905480d80c001600300075043c20041035100d000b04080c401041c903002c0c180d600c040142d980d266070084503500d0094548500c041c030b180b03003030707000261303050151400e0fa5011402a1900c3c202c00c501c1583c0404a80c081e909005155900384056000b048980c10102103901402c40103682da0704000101410b440c0d03c1c2429002c540c0304840e0310f00c01d03403c1d81058003134124a05440003134448280d480013400b9030002010100a07002101002014002c922a0b21000d031401095 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 599169469 1250 599168219 599168261
    0x1181509210522090605030a12080a0b041d120405010203031302150406170a0c0c0f1b0902120105030f250b0c2a0d110f04020403050d0207050406060801140a030510 72
    0x14036031900c5040b2009032142c0700604120f2700c507034044c4d00c11552040010310009203180b00d46000408403514010003107150900c040c1640d900d0b07c41000b15410741c400c10b4071624202454040002e60701d00c00201009811045d0a003241c0c119152084411000d940d8902c605403a80d8483c140100300611200b08801c4407468400400c508210512495911280a98515440d6600c68a0702c0d4080d00035046d0481d1344554060b110b20400220705005c501074040f00d10050780e101d083c0420703c0d03103485c0181c000511903005946415107510b0001001c001010640050302c0e0030f080e82072002045421079510001003d200000d03a684201000304107002d40f00c540040c0c5c21100603070750318003014118903c0c3d005500200304081c201c0104030600007640940c0d40003032152803071035082c3c1c0c042402d9030440d40c404c83e4145c0c4410002228071b50144041030242400351420004686406001884040107128603000101442c1c0304c070415460f413a250101130b50b0004200c03550650000003401c02007090800310390062507038403 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 599170719 1250 599169469 599169479
    0xf09010612020f09061201180b0603070b070b0c0c060c07142e0612030c020307080c030607030c230306010f0c080703030b0111011815092105220906 65
    0x1026079015140c01504048a12030303080240043d01c04040d00080c0c0c0403c060b00c1c0441c00550900071781d0342c030603480f8030150414041d40c0382496a01350f015280d903210b90000007043c070880c3c800e10113440308250032000180082c2c80f1186a52000c2c8038000c0300010a0280c94200019066403d000349003151141c1c10201d4079a9281071444d1325075545112030b0801650b062201d807007070217219000c406408400b0000040903542c0380f80c50f140c00c9524171021008125201d2004080d49400d0100100034050301c405400d007512804002501c4140c010910003d0540e2102440d6401d032007201e8038007003020b0800b40444513440000c1440340da41c000315070303090024900b11000440700b8800c4601440483c1c2c48503031203040140681c1e09802030300b0541c0551741040358032814040c02c00c90074000c45807803101e00203450b092520507003401b0103405c5032104400c400d2828100f10200091084940c20044060701e20400c5606d845c403002210244141d150b0444117200032090201c41c0c4060050800442e19074510030800c20b582c3d1 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 599171969 1250 599170719 599170739
    0x8090105071409060906071a070903050d0815090405010504060b01031806180804031115120601111c021b0f0904120c023304080718020d050f090106 65
    0x803518600041c07080302d24000154041d80141040c2c001c003e00c40c9040c51000c4c1e000c203105400240040c0c60070700c12030100e90540100030500903000403640c9000300f1031034196102d00b50356a8049041004000c41c0382c00145000480303081032030f483c20b80188040550b040c24182203000e04401e072421303202680350003440030300303507020344180c2048003101c2e40c082401000701d07240c10008181000d64030f01851060711403031001640e180d008101841c0308403c41480c1107568420711584541403078624110140c00c01200c04261550b961143e440310007440c0c03000344103070045140343c14080c1c007400060b50384030305c1080e500d503a5030042400e1202450310101c1e0115400c102040020f00a60b413001c0ca50041c00031004a000319044c42c03181c4458075450b09103d807440102c1e9000c5082d04640c503039804650504204401d651100840c1d00c07110005010702c2107030520741400340040d01d0b014240301d00b261582c9100a1008008030310b070180c910504901d903040203580351250725225000401c8a99200315440c00c2804542000c01c = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 599173219 1250 599171969 599171971
    0x5070906050d060911060f0a110a1104090302150705040305011b1e030207080a21090b0a090203010905060a0c14040312080a020d0504150e0c0f01050913061508090105 73
    0x1004024a82e8a651621200014a50000e040c1c40c0c1c20340e507004d1002d00c1d844920045c0403d000d42e0040d180e135044da85000a02404500c442504603400110181c004078200d8101f444044031b044400103101d069625003603161201c0080c06503155201901084040742d0400c0c094000c4900400c020b00015941d070036183c0050484250351008120503040440d4032407140c03021000b503a10f85040040c80e100b11600d9044c95a00603a0184000500078003000c0c170401c08112400102c08810740d800c4c012303a41980e035602100310004190401266032500010203542d825002520000e81000c01d503490303070034848011805000301018000c0480e0050165a0182048000f15022a50001c00b056000003100d1030843c0e880314054000c50301d0700d4080c84040151000380c825140910301c5800089442c007100c07081c4030299080303c081240d054020ba030141e00345844850f869842c03840b003481d00d15600c0c084040001c21410380c400303000350b141b03240c41d10200d01040c51180c18000c0480c1625a40c3c05580c1e034440301e500340c1d08 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 599174469 1250 599173219 599173229
    0x80a0b06030f04030813050a05010204060f08160809011103040803270a0221010c021b061c020a051213051002032413151509080d0e0a0515030405070906 67
    0x342110016020921900320540c2080d01541b50003441c1c00180c45d9240b400308064000c0d035090358001000c01042e034000345140c2d01d003401070a10b080340785030070000404050105010001800303a9000059580c4500398040e4440d800080141901c07030030a42403044941c0c0084500c04000903102085e42c0b440394403080100b0ba41c104110080c105500c0c694244140d2000d82107260000425280d40303084058800c3c0200d0708400540e50060582c0d107240b000484003001d9403809140684420440000c1000e44c4138803007503c4620441000da900c0c401010122050700c181484001c04010b24814400000500d8081200d00c0340144203e540a4021044400c12440180c3d0103030703482d501d07982d04920458510165400444001010030210340003008412059886c1060f518918040100c8207110b001d01e10080c01c010f4812501e070581401d810105250760b5030140c00e404405000008103080407079921000d0040241c40e0180800000c56001d00b05002280c105070307800c840728000c00c01d000c100c0b05410700c590b01c200d03a = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 599175719 1250 599174469 599174491
    0x30409150609240201181a101d090a05070605070303061a180d060501080717010e0c120a020d06321605042c0a05100605090301140106080a0b0603 64
    0x1102a4004200034008001e43c042d55241d0070b00d03d50119021300501907490043d030501070b0a000b11103c0c8070041c0e200904403900c00d1410740c030501030100c201c5010b101201c40707440d4400498440724085803030202c022a008041d882481c80c00300b0f0840c0c0c045c015015040c805c2d1410b100f1903803605107114030b840b11002054210b0005204540100000d1008903422080c00b601c112001251625101e0554030f01748c0000410f030384402d000300008003000c113030710b00c07003406550082000100c901d04c1c454560380d50004507882110303c5400d8090802090015104039035005100c180d8019003443d0a1000d0266001000020304d590b01e080f94600710490980f00c0c06c9907003203e01c500382d030380c40c0b86000c034091030300c4082c1c401000002e102c00300c0c842d80b41355244010700c06040d440304100c80d2103841030503483d0700c0149600c01881c2024207020a038101030300311509a03407182c20520b13291103400021a00400fa8a2118140382144000009080e5001f00405020310641002806400140c6d801e000451200761103a903249 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 599176969 1250 599175719 599175749
    0x4020105070204090303140108010c200601030224030f07080a0e060412210905010b1002070b0d2306130b010c020405040c030c06031a09010302060d0e030903030409150609 75
    0x14600f41d84031280c03540c0b2070308002982040703400b000a444c4100740c0001002d60740d1580410701e52034100c04420804012022038882981c00084020349589044c0300081c040c0014014075110000d4041403100c04c4400d10300029124906500114030f14181960f2500c081402d4502103100c1032814090022403114100040036280c0f15684c40031801e80c15262180100114440802c0ca1100c0304840310506101c885c202242074401070620500311550800840e10038000c42e03020400c10354010440d02c0848000c4800c08d9100d0311110445400b824040e00c04084003200d2a044d07221100f6140c054070300950f81a90482152481500712004071a0030720449408500380c560f418006103000d40200b030384144200340c1c0068044d074a60b6503449545494000c58042900c0711305005110800c034007500d001190440d5003070502e524580201d84644248005042020b0f00c50191402c0200c0030021103d007446c015040380e5885540740c003220001c140d44252650b8400c0d203800c0c0014000c1c811060030050301da40050404007 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 599178219 1250 599176969 599176973
    0x10f120b071805030a0f200a09020306030c060a0f02160602250b0c06041103070b0f18030d200c090c2104080408100e0607032d020a090e0402010507 65
    0x10707921031550152020811141c001c00e07140c07010700c05c0c0e0307003400d100700c0c01009100348624010000340024440c1403600110760342ca4801c2c5a41c0c034074008049a90700303040140e4070340b50240480e0601ca0b90300d0803141c00982c0003031010303c03469019a00300c2070f85940d5801c1e24060a400e444040c4a081a40710b1080140c2c0329a18001c0d244140051111441031500c8010803240d40d14030340380401750048001600c0311f4000c00204030500151100c0b002d40540201c010b00704a030704200101d101030003050f080c6560703c1400310b080790b01c0c200203441c0951150380007411207285081c4810001c0c1401c0f02d9180c280d010548c840c040e20040e90b000201d4040c4c20314024858905070b503402c0300809541c1c2001241042e490820813513001448144141c55010314090080955941d0505007101e113004d00d402144000c007483d24058284110001c12031607003003a42480d0206000c0c0301e45520a030001c5002030384442d403c4401c80d180311f0b01c00e260740c0144114400743d141d251031180d80707541014043c0b50440303011340410300400420300 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 599179469 1250 599178219 599178227
    0x40b0303041505090d1a07021c1d09010801021b060f06100c1403040906050904030804022101140919080a2a030c020306060d1104020c15040803010f120b07 68
    0x40960031440c1c071078107009184c030000c5d540e030f0f040c05c000f0748820f1961480c6810b821505404603500c170b00140010f0913440003510720004914142e0720b01804000c000c5804900300d11101c0b40b000d1501200500c525525611407603090300070351126058036440c1c9801985130284a00c080341003403040c240720065103001d42d110810301000d01403c0822204100c500c1986600080c55218580d40e4810800001c58690b41082c00741001c8030312903084288581c032080200000241d00041e4241d102c0d6047e100411420300928500004000d60030001410b54207100c500c08511540b00310291180005001b1100340c50381d201c03c841010136401c84060403420080052991043c000c00c1c880d0000e1f4408080b920350303020703821a010000e83c11290110005000329000c00c003980740801c0b074590000c1c401c642011000146030307607070509080351202103400781d0740100c1d41d0301c3c0070601480f19041e504400c052154692800c0d18140189034005d009007442c2c44c490f41700110351804484110740846610440c4a90300d500d49001c259 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 599180719 1250 599179469 599179499
    0x91401230f040201030b0a091e1b141c0f050a0207030f08100512030304051204120201120207050a14070b040b0f03060d0503300c0403150b04090c060e040b030304 71
    0xf07414036071940d403030903120740714420701e81c0c014501c40800140b000451400014254201c0c1d00580c00d0300c0c188400c2c0443c0c0540003003080c011645a080c00030f00b0416080c0c009256018451803c42440304482d040c103021041e94001040d00703180c8180c2001142d4804066000300c0c000c08402400107118545c0c80b4035218020540c00303410050080251403169a21000a2810214965445000e800100900003008410014000410384580100741010709000e106450840388843c013030304011030941c0820340507070310360304841e00241c011040c0c1d0b040d0507640c10401d08500e00050044110320070031100081c07021510003500c00b80d6030380d81103840c644040c1403031a1003190409088154031550118110000a404000400c17504807640c0b81e00d0030340c0310807055400c6840e1084144003050720703000042146011150040b1401d49600c1104000e40e03603400e40000c40100010941e094010785130400d003106004594054404031111544c0305804903184000707100640711003501a58040e4011b01040c0865403d4624032 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 599181969 1250 599180719 599180723
    0x501020c0a0609150c0501020711010e090114060706091a01030c06030903020a061a0a08010e0123130507090c03020702040c051c0b060c1e0f0f070b0f040504091401230f04 75
    0x15035144d80b141b508a90000c2c80840c1e4a0092103210582d550b0419800400030034211900102589806050090801071995880c81444000390359010406640d014084140d0400940000e20048a800c2440c6440030702090f103208440000000d032441c440d0087c50051603041e40074004810007559000042c1000c201c15071920314081c1c00d142041d0b16504000402800060004509106c0c03180ca41c3e421142d203819215481205442c551015040340361020350070120384000e0b00d42c07914060070503600700911600b051031440d080078040074655926402900825008031402c0040d41840041070381c0c01c0c442c00783c2e4011100100a1540059111684050b5a43c003010b00164942400059014286492080c0d049000b4001101d030b802410020800c200e07a002480c8000c09131240039101e0150303220994841c80d060207400103421031908820400b65001044068010b0085030520b00c2e01e42c0600300840182d050a40c43c100c524082c402c200d06400c41058181c800d11180380d2901d5050700c54004000b001 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 599183219 1250 599181969 599181977
    0x6030f06081005040312290301140903031f081c0210140a05010807030206192f060a150b2d04031703060108072d02070501020c0a060915 60
    0x58016801e01241000410b01d030b400150524280c90050300c20940026441c081c1e0b450071100d0811840411045148050072007007511160000c0000640900141c021003d9041031010501074030000c000042d41c050340340400f041c2c207040b5403220402d2101d5114420494541d03c00c030a41c108640d207141da5107011600520560703503004810b40910080c0c800c8104608603c940c0346007003003da05154400c09001d481d80e0000b4207441481c64000480034000d01c0d82d11000b0100c1802e01c90402405010b50304180e40c003049100c181c0b8401424440b58082d240c0071540d005018003c0094400c012500c03508285180710345440c0b007843c0c00d2542c0e040362500b041e0305040c84041c80361081185a2001e0500d0b044450baa81c84566840e811482c2c9aa0030201110701c003401071401303001f449601c3c2c0e0404003240c3c0c4041030380340c5265000286c0d4100c01d01c082e802104014400e40c2015078002655000c11080d0a6400c01e03000c4410480b841c800740b1004080c1441001c00149140c03405110701102d51721841304100e001e00e0 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 599184469 1250 599183219 599183231
    0xf130309032021120d020702090f0604051f0b0703030f0e0120040302060d0b03150705040f0b0405030d08060102100615030605010e10050c03130f03020a05030a050706030f 75
    0x5941840601d0b030220341e006503550004601c10502e80203000d11005040ca0003a11480119010303074541d00d100324070300c90010030004078a034203030728903241c0c1a80c885c6178008010080300c4c10b2101a000e0303007100682d0790346c1c042e9040c00000b40b02c0342c0d00301940c2244010345849034490640f43c88007107000c83d04665011070425454190b4141041124010490f407440c280000158600d0102b4200c51b0074584180d590011070803c0c00304002503600c4206803044415a0300c030109113200e038803001a082c46095010780c00413641000a002c1c1d030f21752000152013903c140c44240c201d4036842d0b03520059030b40118801c10354140e01542c2d1004030f00d8442d00419800c1700043c0100d410002a14030500e041c0c81483d0090030701c0501803292420b9107681402290010301c420b0801c000600381003030105000301a030100e0441840000101c207454035004008446080054200005401c0d0f02c070720140031900340d0340c84180d210303d203401c4000c240c5103008158108103540c4200280319107071030098103030003030000980003c0103075682d80 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 599185719 1250 599184469 599184473
    0x90601180914161403010504111c0b10030b1c02031c0309170327160b0c0114091903090506030a0209100203130504020717070804080d03050f13030903 66
    0xc041c4002105070705041601c2031501c5401103107030070a0340000404112100107030030642d45060f070461b411750750140d601003041c10a070700342c9200c944100107128004000b4404003680b481403c0e8400301d0360b0f03d000c03241d4040180f20b1105c00c4017a60b120581b102e46c0320030070b400501c2041b641c550507002e4040c406400d595417046140521005407034504000300c0401e4440042e0010814002244001c0460f0007100900718144002311100070518000c4e00e003010041c003000401c0d00382003085617940e601441d16032000d140c0e403501e0820003550170900b00c01d07220798203021000750040c03103400040c1c0c4502d41a40051499000b00e07041c10001c0b00080d401a81030194198000c60180c8900000f54465502c10001603610346180041c03001240c00b04598804640050020070424599100c1101c02c8600032a005038580807035080194451981e9244500060b00008080301007000100261049582030390a0710443d004005040d41520703011108005000e00c8007000481c0c00042e10120000e480c0245880700d8025242c2d = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 599186969 1250 599185719 599185721
    0x2100b030706020d180b0418050a05101205010b060f1809130209100e0406050103112d01050c0a0f0b0112021c0f06060f180615050c0a0b040602040e0a0203060906011809 74
    0x10fa005845070703149112521520622300e002d100d4200e40d0220007005180340080c4403480d6001540a4404034110400e984000e101094111191004c8010700c129503a01c0607894500781c507072081d81801c2c0c40401c0501d440c032981c507003600007920503884490085100300d030740d0b0b081040c48800109801c40c007640720000400c0d1070b002c14150501c80c43c42860009499415030400100050044c0d542c28851080b80c1c2d002c82d8413800210210702c40c0a103800c0c180c85a249440010381e4a40030b0034002e0180e0344900c102d0303042403002d080007407030740f49004024159160340c9405d2008042c00f541c4101179080079007400c00301c03908103940101c200201d0161005100d8092036903a8982500d401d9071200c3c210011100d02400310b100001050316042e10401000c00031a8980150107a281401d0200c08003803003008545140e940c1e000b030005081c0203603c1400e0321010716007454144020341080c00343d00c5030985418000b4624481c0c520031640503060090000c1151350b118401142c1c140b1550605408580c040b1500040211079 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 599188219 1250 599186969 599186977
    0x207021f05071a07120203100e04050601033005092d040b0d0203062e181d3705010207050105070c0f030e03120a02100b030706020d180b 60
    0x655410742e550b9010f003010242c000035107908030b8840c1d04403001d202c2c0300c1d50031080f403078100c0707076442030260320f9558544104005150b03e900c041e9196490908100400902203202810b0300d1003041141f140d034a0f45136021404110024807004030587e1300b01c070810942c0c0608040d0080d0300001701050f00c64100000032501c088d08061001c2074454000200c1c080720300d07050084030120403080d01c44e60965031061300000d9881102400300001164656810201c140340c940407581c41c020752042842d0100d40e01d9442c440400340410410700c1207480c06c8126200502098040c05c21018500c1c000d0265501d21031340d0507042d90b200025495040d001044080040c5180900303106550701810005840b50941d04005080d40e10040c415401c000e541001c08000402e40000341440c190185400c03082e0f0134039000402d2500104150007c4041801f08610085da0380c0060442c1c032018200d5828446070000c0400e0658445080c010003025802090f607070025039100d084080801c440c54911100107680c2c1e000e01d0784140e40 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 599189469 1250 599188219 599188279
    0x8070f1b14030f0c0a0905040f02090f070e0604050a15090f0602011415030d0c080c0102030f09150903031f0b0f032401140706090c080303061302040503060a020702 72
    0x40d180c02500102e01c1c0c14442201e201064002070009082c0034000a11070412030f01415035003556134004036040c04801107103030746015405001c160940c14049414106801c084545000017408042001003a0812406440450b04050b0001c507201e0304060100004520204882c0704000e015140041e01c0c00300020643c00802e00345d00000b441011850905a20303c100800100400c001c2d400c20302100d071030005a010f41440c0d0380c9403000c0d401c5d506c0d1a0400452003145040c1d40c80350300220a1040c0095450b1001e40600520800c075864410403e910f008a02c0c401ca50103000380c8c005100107030b120b0400540c01c20301c03e03540803c09003a564603a00341e05141d1b00700c089900c41e15503021041110804402d00d14808030000000c43c604000c060000082034024510422011940c1c042011403c0080c182c1210785c02c0c540c000c540091158039007282c19500d80045900c54032410754800214100d0030b86100f2142034520103400b400c40f03943d844440700c01075804100d041360804d40046405d45201c00865403954501 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 599190719 1250 599189469 599189489
    0x705041208070515100f0503010b180705040315050a18020a0501030506060702040603080a0917031e0c01020d1b17010b0c1e010608120f09120f0d0e03010e060408070f1b 74
    0x10707040851486c40854640c10090080e0300d04848003800b9500d03100c2c3d803000c01c08200062002540d60140464460280b85e20040040e145550344101d02c080c0d5403c2075110307651004041003401503601c0d107048050b0241c4030207034206000107c01d101c1c6512a0300420b80c0300501400440c0380501c13a50100d0120b41d010f5200b070303031001404141202c0b459801881c400082401000c1002400080c0103080e031288100250070278040c01c800308a02c00c113104d100c107880b041c0c00007100854403041c00c0411103016040d51403601038003000c0081007150700c0d4010540081a521a01b00e400e14580c20b00403060301c1c9a1000c0c41301001071003030070311020780708410007017850441c2520390002c40d09a1400e5001071502c0f000d05000d00307000505201d4100318540e00d105490340c03030004503044074007072034425455030404403610866485400b80b10075503104036400c041152038103001600200010848114507544501c070660b0014401c903000c020300000700d00302850300b410950150300c00b19a0030031100c101d50301d00a1158442a0302c4 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 599191969 1250 599190719 599190751
    0x603010b060d05041b0503070b0904060b0d0b1302030c160f080a1707080103030e043801090509060d031223010923060409030201020f0a0305010302090705041208070515 74
    0x42005c1140c02042075141c1c40803112a4140000a41c0b641c4042c022891824008201a00a5641c030341000c002040703840f0902e96108e019004520181c10b240c699503004040e40140a03001c12802c0c801c4070311a42d00500598204190102003c400307901c807500a0302c90781d14100005020032110b000810030500390752542d0340105590f58032502145070051800d024800102d00402c003003900440b41071414901110b00044072009c0001b4180c018440340b0000c40c0c051500e8601030a202c020741d80c583c0c0803400907200c100d00c00303a6540070003055503030445400390000511200c4500181c09015480000d1321300003800700b5104024129003d00d882d841c0605041c011811004110b04000d40c0310781c3c48a09400e01c4455008411504a00d0300d10b80e0190015000320b070b507881d0241c2818401e41c1030310168040002a00d91320a040b020044c0601020f01017a0b110f5000c40001c83c46480c05401200c0403102009410300301c16901d515000001c0d080907506450314050240941c0709902c078550140c0c882c6030424410180 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 599193219 1250 599191969 599191973
    0x30a0215031905040c060e01020f15011a07050a02150f031e090a050a17040902030a0605100206010303020a110d1415070e0f04050702011514011403041a0603010b060d0504 75
    0x50449500800c400c82c2c0d260109103c0440c05280f80481074466030300b041521001c05000413403400c40341c01c00340c4602e4003603480d004040c814250341881c100c0340041849115100c0c0320036007080c2481441e170014030540c04050340300014240302d0103e034003d04400c405076062440e02075030a00c2560088810380024002280c41000401143c1e20058001d41140300600f007840107666490b035070311043d006c041d10280707030400f0350030108214008481c0a0411a00150746900305000b1920252003140540343c418404802a039400c0c0788005100703412250558001c0003e00840c0d260140058014450a5001038010302c03c40c000c43c540d0b6040000b80b1415900501c800e5a210329103600d841c6c07001e04940c0030400e0601c00e1404135566070602c40c030201e108603800601c80e00c0b4060140c2c010802051160901d0a091500040c003808034403031294202c00a884010f2800751030440d0410340e220131035000b400c0700780490071000f060030410b89059201c80b001d80005036a80c2c98000181351a0442041c51910741c0e02e0f0b10170401 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 599194469 1250 599193219 599193241
    0xb1902010c08060d150f020c0703050c0105031b090301180b0601032409050a090f030519140a050c0708190c05030f06133e10090b09030a021503 63
    0x10149480c60140c40c00e0420000051000482c68800307000d10343c08907603070b000380f00c0b40741d014003086906986c0466594600d010041d86402103484107440d82e000d51540c1500c2075001d041201c0c070a0440356804112814035a481c2101900080c000d950503640c0d0300340070440340040000d01207005015204540c1c241c940400010203641c555810029091000340b0b074005942c29290b5203409030b0b400d0340d201003010b580703203a50000180703080800a407440b14184800d005068000d0000c180c1440c0ca1004610001d180b001e0540e41011100541c5e00600b0003000b0030b800041c03148014019020542c415688903075aa010500c0c81c0c2910130310b00d40303004821205d8120400c030701090484010030301540505003000d030880c0f8054031414000c1804820078100c85001e001c101e042c0c0c41a528055103008150b2240c503114036400714854803520a07004d00002182441803615145408100c0c1020303a940d280c00c1a420304840c0c0070690811008240c040c400c50790620700584d42d019035090b15080340540c254907803070302c00c022603 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 599195719 1250 599194469 599194481
    0x10e1f0609051003060308032814071701080c090414060a0f0c0c120c0c0807060f080915070320040305010207061107030516020a0918050f030408250b190201 69
    0x4800e140c541081000001c80c86e0058175402030409c0d4028000c031031100c0300c04d80b100614203142c0283d9450f24803180b04a51000300d0140c0280c000d0703519085144000741c080c0707450420a01941c1c0040d4070a01700000f052410716403a95000d80b150b95001400c10400c0c01035032034200250303400240691076404908400d80b0340d1080b1070820900e85800400012241c0b64450000b0550030114100100d2441260500010180344401407403400b089075982c6554000041800e00c403c08480005510303600441e0044400042d1542003c159100340a00c41e161910140c00400000d0141032400c1d00d0440d80900c294070b110040c000940c001c800142c8d441000b8503240013140e05400413030f002e654043c0100400301e035200090b52048501018005010400c40c00040c02c3d103296540000f51050801c0d16a13021810b1020b00c09000d14030800886001a0b03031041d20b99140d005030701510700268411110303006000e0b01404078191480c188001400742d05e445249007042c0358801090b180d8102015004003040702c0c0c0c240b10300 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 599196969 1250 599195719 599195749
    0x1080a02070b01140f12010f06170c0f0a1a03010e090f030304061509050118060f0b0d0b0a030b0403050c0d140403020103050601091e030203071a03010e1f060905 71
    0xc610300459607541203481c80041c02941c028580310080d05a030b644503121800e01c5640300030000351000816001c114040e145448000f40c64504082e800a40c415507010603e0b03908540c40083c00b88480c004007441401089100c0459000c00060307400542090410f00042810350f142443d240d40350306003038500c0c2e00700c0000340c0011000c1e484050b04101e04035011069a030002d502420204003090050580f4220392903d4105c01c0240e072402c0c00000c0c100d030441d40f28021980741080180041941c80f00014810701c1d042c812482c010308108810600c503140e5600c17910000c0c0c0000c2c034040741d0603100e07251010707592000c441c200c011410010394040c0044081001e82c160740342c0741c42d100320807070314012551500d8020b03888003e041c5038994000c6001680160b00b824050044211340c2e07410031070040320014500c081403101780d02a01440e0380103e040d0b842d00c41115906071120a086140d0307441d000d50080e0b40d65008000b40001d1a25142c940308552500140340000c021940e02d06280c54281010412180001008 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 599198219 1250 599196969 599196971
    0x4060306031a28020c010f0c1101060f05130609050405010b01080114211e070501030c0206060604031101110a030806010908030c07030303050a0b06070c03060b0607050a0807020f180601080a 83
    0x801008844410069503c3c0103450388014890001800070006030060301250b84465003020142003204096900c42140c10001c0c0e80e8280301401d1541c0a81e003201c80900461400741d00851061000e4141001c0708034010004003c002482d982d42c0480314201ca02c1920200c40907516051070390300a690005d4498090015100c070041c0c6500c1c02d5000030882c521142c40314010012076121008408018424455201e5040306889003502031409071030f440320300340c4c051580400e07c1d01c1d0503051503d20014015102e050094021480c042c10f41e201c1c0381d10004601032980c10032004a286030700c461001c1c01046080c0e8400e4441c0d400300c2c10580b00151284449401c002c03910742c0240419584813200040c5102140e4060a0005d6140c039044503402c0507044140c449904400000341c1a81084242d0b40c50400f264000c4a0400130064900d0400619120b2060060003991001035400d0100e080100180902d0b8402450030104060b95004541c10010580e02138110645101c2005003950f003061072a40e000e4400c802c = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 599199469 1250 599198219 599198221
    0x100212040b0f0f1303270e01080c0a140f0324070e01120506010311040605040305070b19050a0233180a06110702181b090108040219090204060306031a 66
    0x150070100d0342c401410070581070303501d24a02e0103060142e02505101000303440410341d640391b090b250350346400940c454451a0602c1c00000110601e0101e0314004c410360040c410a43c0c6441c2007030010080c0d0600210541c0301545600c4482c80b0343d01000103100c94491000e8641c0043c0c100040354224503002000c05041c0104110b02e500700780c2e40840414403a0700000c0c000509174444c00c0048004041183e105d14510000040210300c29030880050000c40340b1480840300c010b031701e07185119094001d400c45903184105400041018038040ca0240030440e2043c41281c000f0395403c0d010260300c1d03005280f14080c06c03004c80700c0701c6408814465000d0f0b2000d9154112035803038480400d4942c2c3c0d0181a540545500da541500301312400c00b10089507112030b002031450040416000010140f00000d80b40d07110003a60303061000042e42004002d0f111100d1058441c64074999660f02807041e01043c40202c4010414120008a417070040391010340003070102c41e500060101c0c01c500c2c0030b4004250f815202082102050 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 599200719 1250 599199469 599199481
    0x23030f0103110d03140d0e07090e210307051b07030807061b050f07020f0301050702010209030d020703020603190902131b051603050913060311090f04110909100212040b0f 75
    0x600c001e0005c08032040500e6490282130800c0d00280144504007015005030500041d044141e40c010308580c014940c02c2c1d549080c00b110303010300001c40c1040c0b9008404003d00010700c00d10b0050001d00703c5152503c14200074000d0410507d400c2c200281c104a407852008600c030400d200c418410303403d0840074201102c18400d00c40302e0180c480e029424080c1041000010824210745501b05115442c8002500a00c468140741a01a0103500218095400303841501c140e6003003148005002e20440741c0290240749540c5502c40000050425982c008481d035440e900042c0050700c680390380c004207040541c400515803000001c091664119081c0b0402000030600c4001943c601c04080b28075502d0340360a100e9a10b543c11004111a000b0842950350b0348e924104002040c44200b050319402c803401140c820f40c0c86e5480f88185a802d500a070f41c090301180c5100c0c020241ea080c00354007190064441e604452208003404c100b4016a44854007044800f049203052000300880580c00c1f5800180380601203d580c6011 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 599201969 1250 599200719 599200727
    0x301090f0b011d01020a0b1008011b08041e080a080103030806060f0f07110a03050c03070902190c0302030f181e1e0d080a0804050606040204080d23030f0103110d03 72
    0x4810f2551445012400143e4903070007001800c1c4944d512201c01307102442c101400080301c1440b4480c0e00269400e280014007841881c0054007400551030f25400c0760f41d180c41d00c0c0d00182d810f8400501540346103408085000c10011005406040d5107a1750b20203e03903045289c010440c0c01d002e01601d0190384207210752a440d54410b4203841812403683e190b40d407a0846424250300d03c20400c0d40568000b15440c102000340407012a41010f195000c0e011505c3c159075440900089100d428441080046401b08e90128584120440f80c800c50103407044030300f03003035600100540d42d600c148030222415a84810280207410302c01c03d284500c18820a20360425a0510080b50204016004808078204001c8000480d6690707150880103143c0c10600042c0c6a40e000070024120030b000b40c8050350740b84102d00c005400d0b481c1c14002c131002c4c0c1d00031102900d000d04217000c081c0c0300000040040c104502c500e2440c491004610405103214015400e2054440e503d0340c00c0915210902c4c0c0c4466010300e050704002e030086504 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 599203219 1250 599201969 599201987
    0xf0304050f0609121e0406090e010e22150f061d0f040318030c03060203091605031b040b040c0c031205010e0c0304030509190614090f10050d110301090f0b01 69
    0xf89444c041d50b0380703070396114655120710102e40c46080e41d5002c1004580150b02c01c01a000b55880c402640e0b10990300c4880030908210105c0d05e01043c3c88080c124407020f140c13038186140c0c110307105003220398800c0516482d5030151040c208001a200c3d036581c0c010082c010002c400c2c40080c04400c441c1c0700060501c0030040520f18402080a018044102030140d00f5040c0c503100d8400039900706a04c482d801d601d0b442c0143c042e600036501e00320248108070b482e100302030b80000d00d0720403644010020510756900c1540c0c42c500f10584041d0b1a400f50380c40e00281c40c551168007607142c840b0116a1082421030341881c0107410003120b60428030070186007600502030740540b40aa650004030b80040b540c3c072641c4a00c0d00f2140c40c86414841604039680c001c4000050a5100038127054a1003516025403203224100c00340e0941c081c01503400d07401010550071040038200040071604003507241c5400c505c1c2400c14140801070b40e00054170f0204041c00000100490b1300c040c401c141807080c02502c244942c8103035500003050f602d1 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 599204469 1250 599203219 599203243
    0x603030a0e03190c0f05100f030c21090209011a040608060a050d050106080f030a0903082203080405010305101d09010f06080705040605010c0b2a0f0304050f0609 71
    0x1c90808401c0d080e039003005038500da91101c120102c140480742c41c02ca0208501446444100c0a01c1807012900b46030a040700c0c21001429500d000e900000c81c0c000300c2c00303001c015a404e001d00001a80c42d40c0030800070090b00c00401c20009001c50189420700c14403186400c160300103058003180b00030350720a000a060450f4203c420a02c2c00240540703a98002a242d6030140d070141da44646500d814008120301900003a04440b014030546030b01502e40e101c2e0395200d1140036034240004a07502030610018960311f000e4810030307045034012448032500421525901e04607820030740364071358003140400996038036020780769102078000c64a8450341d241640a02c18240071810003141e0729030690000e00100380035804600d000c3d10406d014416a0395801001b40c81d10403c0c0a40c60250b81000404280355003d440e281c1d80c1564456141005603444844003551440f4603c0181400c64078100403044010246003d00041c0b05400320300d0350380b414240b170042e00e025030303900d8162650307000502000310511002c035070340f10049 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 599205719 1250 599204469 599204477
    0x52a07110108061e03030f070506060114162a170d03020403020d0204181e0201091a120405070e0705180f0907050f040f12120201110a21110903010c080603030a 70
    0x40c030b500002030940c001c0d510f40420347c5a010907100c0c00d000002402a00628007a00c49950203281802c0b050840d20a40311000d00c046540c3c90644002600490700c45003864402d00c414140c0c03081c11107030140b1441150f1084288456000e01d501c10320b1810b1142d10602c440508045142600d5940452801020518060b100d59034880310b4140c001d114030200c1c00c8007640310400144000803085451009500b49100764000390600c01c0102e842c54203005403030078100c0c48200690810316402c4401c21142802841103513217010700200010900b02e80c40340c090280009458840d00c0d003003401040508088c54030840761145000e01008141d5803100300103070740c000d41e641c6042039480c0340d5000c00d19000c0c8100c3d44440d4003201c007041e001400003c0c040030025000d215021201599980301c4080342a11081090011401c0003000b02c3c0040070b0048400302c1c20900c810890a4a51002444440458040042442802100088251b504c1c942880b903680302c0178460802100600300000803e50700c1c00b4240031030041c0 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 599206969 1250 599205719 599205769
    0x70f08100203340917150907331b0204020310120507050108070c1109060a0806070201150602070e01030b0a1b0e10031a04052a0711010806 61
    0x150f0000e455031003c0e601e1450f98040078540b81c0780c6581004005000300c1c000850000010031524003084007100c42403100c00041103120080041005241c01c09084085103208202d0002101c040318809080c460000c100d520050a482d00c400800d04c00914440b03008105001d403400354240c1c45000100c0e581078050368010384035503c902141ca4501d215800200321464220340d040c080000004000c0309844080c0e80d81403030307074440600564a203049924010501303c011a0f02c000b1034244521003a038010401040b007030741c041e40d5540c0c25050210541da1070005135158039a000200c440080040020700080c40100901443c00501058240060000925900d110800f20314640301e5034109483e00f000d0f810b00450400d011010141024580d6000d03a40501c2600c5412000d00d4040d00c910b281801d0b12160f2029881c2da0f1204101c02008020490740d2150345c8140b0190340c2407101c24884140440c1010345136030b02c03503241c2040908920021111410401041d00f001010f4448415441080300000800c041d1 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 599208219 1250 599206969 599206981
    0x61a0a0f020c1c060c050910080402130903030b090108032a03070209101a0906090d060914030d1d070605070804081203040b0a090209071d06030f0108070f08100203 72
    0x804400d840b48a50009003801540382034002412020b40c15481340c1c808003c50841e03a40306507401d000c3c3e203140c250302c100c21410181000d8042c0d102503601c688000c20b020341010003101040f044500c440020740000350380304101e89180c1008100e05015000c400002d508281c01c41d14040145034490395007070f404050060110124000800668100c1e560041c20302010745886064044a06050b00c1900c020800504000d02c03080303444000c40e0f0000380090101490000c0d01001e0002d1280421421280b050345c4182400100742c4d07064441941c444503034082d5540c0c1500c060b8290656403800780c603900380400b442c1182900343d400119001100e803182000381d120006400c000c000b500842d4818103480c01600c1c0c80c1002205880019131080d032003003c01c0358564944150050440709000d17002500031480f040402c245034000e241c0e010407408034280301500140c602001c203140d1303003080e6602c1c01980030100051180b03803424401440549801c883c1404014500b07410307a682d036640c2d00c107841032469001001c0f80c0 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 599209469 1250 599208219 599208223
    0x110d050705040905101427150601050c060127060e0103032105011503060e0f0106120e100b0102070e13030c03051b0c010207090c0c1106070b0405060703061a0a0f02 72
    0xa00180da030810590303a400200c2c403501c00f0200d40c1510200e0b1280a0145030740f01c00402100c0ca9900d950090010440d20b40c0723172658010300500340606100090204c4481c025040242a001c0c211640c0003801441d40030b2004010010700007050104c03035080c14020710815241d0b040d40c07811039070103141600d4407440c2060b5420703112180c070345103191241c1040c0011442c200b014500b4500d40c5000e990411000e0f944902c0c0480412090325006e800035101801049403030712802c884015030a010400003240c45902c07000a14141803039000202181d02c034108000951380503c0a1030042c0340240007020707140741c424004d02e82e120004600034240240e000880c400e1601c510103036130203001c09031440840500c907500c10f940d69420800105005214420000c6180c2c0711a01400c09114244d0f16920b031010261b50382d100b1888040ea00c0d154002c041071100c2000b24801e0022203002d140100081c2115081c4042c000302510816048500c0c0201010381050000914070700300c8605021901d0682100445440228 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 599210719 1250 599209469 599209483
    0x321030b1203090913140f0c04020f090405224202030703020702040504050f07170304090b0402090306010b3612010902060a0f0801090902030c2713110d050705040905 73
    0x3d1b151079030610f44080f20360790001c2c0b441030b5050804221108001424100710a0344102a140004041c040c011400241495000550402261814045104818481d0320890304100342c0c1074803102c112003240000aa80c80720020340c2c1c40c040d107041c0c0c0c3c021380d8040d03071000d201440c03400303440d403440d50020000382d0f6503100340d0540b01d04641c01002400507041500342950780d03542c46500c61000e0b000b0301c400010750010380b208144404410001960915103002c1342403004010003500c4e580c101c0d40070440211550b50030b00685010f000e404000c19140d8000f60307901303400e5030144c11110405104100b910500c000c80000140054501110802103c00911204902500c901e1900940200002c65500b102079080200e206400c020341d078442d14107a03030701e04088040d5019007901a40680005c0c0706543c41e0b050501000058452405602420201d8941c00701e142c07800480b0080003400880e01107404200c801400400b04180480740c0d502d034900a6160b80791181c115102d040c0c03103680d58000c1c110411006000708 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 599211969 1250 599210719 599210723
    0x10525020d0b071205040203060106050c0304081002071e2004021b030d0c0c02130509030c060103050a15050f06040b010c171b060106050a030b0a0321030b1203090913 73
    0x34007401180380ca1040c00000741d8041012034055039030011503c06501c1007510450b0001c00034001c692a002041c0e96650055421f410a40800c00c004660504104002444203003a000d005a50b080c5c1380c20a045150300000004103104809040c02010840c810200d0f440103484c2c10b0650900c0d051900000c0c001e00c68210b40e403144400f0040c244520070800701c00340441c0111043c0034011090b0000c4101c07100e03c10301c3c600940c0048498654151586d2660009038481d407503000301d03460b00e0504001107280c090264030440f0550701c1168208100022500c1001100e0321031a804c0c40a424a90100f04007607038010030784c0740950768401c00b00c61268491801c11320b49940044c503002c20b40301c5c00c0e0040c048035849106a9664040550340b0300c5000c960000307415040b07861685d00c941c01d102e04036404401130001c403032032941e026052130b50100100d817818803910300110031103d813a107540240c02d002038191015000c1c058803621180f60810ba90714404421139920041c12665102982d481c28507002c0c0c042e11901c40 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 599213219 1250 599211969 599211979
    0x306010c02190f15080a11070c0b040302011e0c0f0203101112010b0c031606060e0a29030307030c02150c030307121e1a1e041a01052502 60
    0x1800d24071004403420441035406843c0c0c1042a50349550007400951403520840c4000707085040025141e8010344e000e030171025141600c0c180380c240c0c00d484a0005207040e801c2491902d000040801c110340e0000c81b500c1001c1000c020204881c08484000352441081e028042c040e110026010720031036605112120543c208032008200c26801c0505190340c51b0044c000030500341481d0790020881c00e43d070704151240714141c007004510740405004e18240307125242c030b0110f4035192910004504000380040e0782e0710912000384001040240c42c03039003020b0304c1d0212101094a0300c558154144940b004812030301d2054150401500040c12880400c2e01e41d40654215410400082064229034802000442c01144941d86034205e2264068101c42243d04121070030b0044202c185000d130080e070b502e030445170034511181d4404d030002418a01103138102011525800040c00820702d002140d00e8907201d03160102c0c0610444078484843d000010b070051040403ca03442c0b424000c281c48100e41d405910940401307501500b = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 599214469 1250 599213219 599213239
    0x61b0c100509010f0b0406030b0121060207061b0c0201350112050f0d0801050d060914010b1e0306040b192a032306030a050703140706050703080c0306010c02 69
    0x2000e64000d10134110b20702c821609201084c0c22900d0103001e001c0640340c0001c00c04069903e480058071701240c94402008800c0000405840401c41510142c82804c0c0038130303c017088400402c0d80786401c0d4002904118203104850701c0440261742c0c0800d09428582500c2c100345403c248041246440144442d40000d18040c071600218204054a200f15072413841541152652050070f800641c882c10701070640c200159401004005c0d6140c0f00c003080a00301d00600c00000c42100a072074902c0394854102075050142e466070045611410000d034480c488041400f580e0418170541e40000c0d40303413000a8000713401080b0301404114600385140c808034000700d0802d410040070065084240c1c0741a50a8003950b609205c1d10300b1110558042e0003066142180b110444440c0541e402c142e0408120140c88980c051041c910850006a010449000910f02503201800c0202c1d03802851480c1459039002441005030610903900040e4002c010250000c442024140e160b503100c8004aa000c0501d2102a600c80c130312803 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 599215719 1250 599214469 599214481
    0x1805070311030136030311031003020907020f100c140a08160305040f02040905031b0a20030d03090201020c0904030e1302040b120408090604080f010b03061b0c1005 72
    0x8400405407102540240403030200300c09122100c00703c07055140714114188081d8001c1070100c9000c01c0e50540701382400160040e0702d400b40820754204603503801d02030780c4944050055180518040703920214510042c081c0d91400705459841e249030b011a07445854803049414103442c0505480a07445031280700f019150f420309240100300ca1000d40d11101003102010084110f1072090065501c1190000c0200003983c000f982804000e141c0d0050540302c0380030074819a8a542c007200d580aa040250500901f9656003d0408081c81c10f50525010140c0140e14803041d1151004503d20045210908001032648040d00050342440e804800302e9074071400c0c4408000030150000c140001c0c2040c252151070005405100d070380c040344294051400b496030240309104815401240e055030180c402e094990810200e4000b04000707070426000380c2544e4200404004410409100301f40514600324010812420b00c8010b0303540040c000b404502d0302a100284601c00f100c0204000c5141c0c40d000c2c0010001d41c58a4 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 599216969 1250 599215719 599215733
    0xf060a0507030e1008041b050a1202010306080c1c06020f030f010e07023403050102120412180b0c150115140301140405070c05190c120f020418050703 66
    0x180000b18042442909210414101000301100001d074a8448a415840c0e0b078451018451161403804244c243d03d00020500d6154102d42c0341c01880184a130141c43c0c11188005000d8504c1d98010080300d50200b00184110303039500b4002c41c0908142540b000c0034100707505000000c2e22814101c2c0c080c1c003400200b80702043e09020302460488040051228007600c403008100d86a159018a80d12450344440e01041e002c0ca04922203080420480200da010302d940366541402da0300041c1840344900761141c200000d0000005000095032000e1800c000e03da00c1d01803005108101d5400741000c850404075480c1101c00b41000103000600402c00c4581181d030351000204860a12081d40d80d0005d580e050380000540f90300010b403810b80d0f0182101800d841c81c04010b00000303120060400080200e10395501e00490780c180860300b10344030109200100d4804030b0900c40180c1c00c0c0f0340e00211541c1300040291002c5810521810703800da43c111404504815000c8464540440b020340280c2140101c01c000000c110740 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 599218219 1250 599216969 599216977
    0x30103020f12191403070f060b03070503070801020717031e130f0b090c1005030105120327100c030e040914010c05180f010c030804060f02120910020c03180f060a05 72
    0x100c2c00d0080284c07102c01c113066849000d420301c0102018811108440054525004a500200003600712410207a5503400240b0b800d40c1a03100d04c581e81d60005a001c14803204ca402401e541510080300d40c03035410122203d00e0104521003604080600a001084802800084808061343c0001200c52080041c0c181082c0080d42a41e01c40054800d40c1c9410076281407058500e00f524426484807821a03281006022090102c9030003074503107003c104141c0c2042c1000a4003c007909070729500111031848880c052122484049040405001402181d60300182d40642e0314040c07060f017035030007003070b0f0b50164544025120009200c0954070b50a02d80f0309043da0ba4820003400301210840a40e44180708004103100900e44005001c40c00160781c09001400710b4001c03a60b050700a4807a040000e4034015500b145001ca03080010b440100304456802d025504804105840740140303008021450f21903500c0541f541c074071480e141010302c0c085101c1801560750310701c1d011100948000d0300003599158542d4008150341c1c8 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 599219469 1250 599218219 599218223
    0x9050a0611151e0a1829040c0305010b180705221d130503161712060f0114220e0106170c030613050603030702100f1101050c030103020f1219 62
    0xa503902c000781c4c410b010381c0248003040102c040c1e00c9460b103070306032920030300c8440080045500c04e03459001c0c14145600d5840c1e0078420b5000d0300c4488800c03420b602d407182c252242d4005051003441d000d00c1c50311078202500f2101c3d8000b0424201141e54510707060151108280d000302808103009000800213071002964500c41d80008507098010f440c6c1e172100c2c2c442c800300c03050f2a0082c03c103901c180207254464001c0300c20095007a01441d02d1600288445503554400d900420300c009537100800144141d608140641c010280001d00b02016000000354096a55000d890b00c03003222030103900d03014020302e03003040000005403c48200c41c0c5032940c0c40f000701600d41c001171039241a040c040e445c001640c0c00094825039005e070f0001001d04c00c0000e444410702003d00b0f0083c05980d41404204041d100503a50454030060813400ca40b40e40c20310407013007400546482c001450080c8107034100000c03c50b8600200e800c0301d0540354121130b680403142140b004100001c90b040c90129481c0308171001112104c00364201200c94074 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 599220719 1250 599219469 599219521
    0xf0a060b090f012706200a0f0c0e01030501021201271512060c1107081504082106030105160c1511040b270d0f17040617010609050a061115 61
    0x11b584a00f2218242003c44c1004650001c2c01c0c0d031000a06225010803841d07000b494220381039526034295001c1c40c1000e82c81160716079070000c6d514010b6400d0983c60360040030b000d019000a1001c0f10780d040302000705401c8418507181d54101403845091039001070360143c084011b00780c91803d0b00345055801072240134810000310711000300f03070504100000369400c207884107680030b0101050841100000404090402c4620080034495401141e07440c45c41510314040d401105040380c10308406060031560054141c0c81c0102d0310310040c0c41c4030b58010b0b40640b8440d500c6005003202d811003101400051000004c41600f001c40020b00240c48201131015000201ca00c00c4d01c1481140b0040180200700700110300242c010300640c00840200b08410042c0d101c0034042d464401e0206000402851568004c0e04410007003000c000c4105c8140d5140d0040c01d025040500300502640c1c1020001100084640b04180411a100001800385241405004000400d00c401c2484030704050702800c104c80c0003520380000070 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 599221969 1250 599220719 599220737
    0x11a03030301050d080310030f060c0906050f04030f15140f1f1202030709020a051b0c010e090c070b01060e03150610030c18030305030f0a060b090f012706 68
    0x14500802101e048420013000744000303140a996002a83c0c000030300b000f4a04001c0703000040400c10305881e0301e4010380300700400111941e0b80700c0081c11115490f001103080041c2446100e0800d000f480440301600e0b00407000f800180305601c1d1242d0b9501142100c1c0070394034104048101c50000210130540101403400c0031a403030f81c0c1d40c02c0043d0715000c5541c1a200c200c001120b402c00210201d820030b000c0d52400541510f01d22620340f15001c1c10707a4405002c1000045000482114444110b0141d203105661600030703124038026400020b0080008600d0184111540004221100c443c4009c449040d580581082080c0d82e440350090300889000d00918003901030b00300e01312001114500e80510a001c01005010280c40032802100200902d480c00010300828030724061a07050ba00286000a500c0303561199924030740003250a0142c0d5002e0310345d4060606000082c00308034a034806860001406450f406030003410103004844c0403100340c0c40081e03410f600b9120744055140f283d908000340d605c5134a4007002 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 599223219 1250 599221969 599222021
    0x1101110c060c010608071410080c07140601061d03060f0c070f0302010c1101181401111b19080904050c070b040b070f110a0b07051207050a02060f0415050c0c01020a0201 74
    0x80d001d070300b1001f40d0f840148040d2074000305e03008015042e000502030301060f003801e03059a00c0000100800d0390300c410389d5100000412400358003010302c002034440428402c28805e2140003203591440003030700311800001100300248400b0702c90070594820580010303842d10304a0702400c01034000c001030058040081d080d02c4001c5058101401610100310200010380c040b840300b51180c0d007a03200d030320724a5900f81d52581f007120a950300c3c010140510b00003000e000942001d51561007450804031110ba40c0441c004050002c0c04240180180c5210603015200494969645580100c035845200340003000b4800d00b030207020610102c180454480c050a4480203c800c0c43c00c0f0041d20411441341c03c01a035584481001300009190711480c5400145030308019041009048108086407030448580000800215480c0d0040384c1c100302040e0007003101c105404242c1004d44510600800710700304600002d48400100c0d4414040b0000c5894880c078a0008546610010700024040c0001c1c84a1030303c210030001d58041 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 599224469 1250 599223219 599223239
    0x120a050709030203060402011211070501052508010612180803060f241602031507091a0f340b010801020301151115040c150306031101110c060c01060807 67
    0x1050343c0d0010020081c0d640c442c0c0c0115203181569412800068480c2112841480190007a107130403032060002064915107128480b04800e54070300300c85203004400c40b61045080d0401c4441d41074034910b10b0002d910428154000016104480880d080c0100c40440382301800024009907000d8038046507008030200c1c4480410081c1a480b20741685d00600d044070a00610001b03500818030081800180c1d5030780042900060300300884600e4004421036200c0c2044151030707002035841c000e001844181401000b40000c2e8801c64040c0c2042100192000103050b500070341c0e0114042040a03090300f00a501007143c142e074844000811508a45c1001c0700c2002203071450042c0241c0c1d05903501c0b11100550070aa00404842840081b08008254000c8201104c007824034aa8030501c228000c0505c081076a00d400302114407654144400c0b01011b00d0a0014000100800482400554246003a105a0008170b800c24101003100c1e44c0786030702400000340d4144c00c84040d00200100c844000985110340c0d90b8400c200 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 599225719 1250 599224469 599224487
    0x70602040819030906050d0f02032a1806070305070501110408010b040203131b0f090c0e040c0207172d06010b0f040302040f0f090308062b080d11120a0507 68
    0x2030104813460410302c481d9210303034040d040c83d1640050114151410840610032a40207441e1000507100805010245422156014030340b4104840c0c1107203000440400c1d00b9801500c071950601c5800001600800d141c40766017928400b6400400801018000148580c0a540300b031040301055401c225005055142520a80b80710304100c1248511121895681c00300da80c501d00301e5640001c01e05200490031014803070402c0090100414000761550b88440702030310f00104152610f00c00c81c18072a00800055000c115401181d4240700e01e0402175544400807820000fa0503818508035a80307164a0403040940d00e41584865407410540d181030340c031440741740382a1158030b402d0340d2800401c0104200500b8291300c020340c2400c030b130080003ca07212814003070070684000c800c09800040d000c50510010f07140c40e8403445c41c05c0419100d5007000c513444040340b0700000c1a00401504250f0081810550340d065600034030307442803810190135980c80d8001e5a08041c1c0c041981c00c190403905e404005000d05014503646 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 599226969 1250 599225719 599225723
    0x201110d051e121e01090905031204020609030a03170f010f06050d020904050a1a10020a0312060b13030606080307082205040f0911030111190e06070602040819 70
    0xc2c0381c104103101c91a5201100042c01109440400c101c200c03010040305414000d101001c0340e1481941c0002640c800d0100c1a00031491091601110300000344000084840c0006403132919070246c0d5a50002664a020700b600f01c0b50507024a51000d000c066100c60301c181800030300c1400700019110560443c00000090160b001e24282000042c0541070080c0040c00102030f88590241c601090640400d0070b80360b042e0b85034050103841e40401d0245820a0f5040000c5001c140e40341030300312000500c000e5484070341c0c440c0901417050b43e080501517081180c02c058050420f0344545540c95402100c03810364a1038900c800e4a100340303040004142030a0110071641c2143e044034070a41040c2203d00402e202c1e404c0b88040c86500301e88014005800d4a032401480d507002c0003d0f13000070343c00009042c0001141004c40f070b8144aa49042079000c002c0c4003410954204100d078501d00c10720041d0302c030000e80c0e03985440742d409a80030201090030740c1000813940040003034699030000c0e81d010181060341e8540a03000c1d0640 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 599228219 1250 599226969 599226977
    0x108160807050c07150e0319020a140f0301050906180703080304022b03050c0d0305010b0301120f05010e0c01090b0910050307021e0c0f06030108060a02072d0201110d 73
    0xc1001c16106001524100350800140ca070450750301d811040383c0c40750442c154008540c14800d200303014a0f040c400702d0f900312520309541014010a03400140101100c2c01400d10008074408454800c0e02e52000c8002888000b40080029042c0400c2d65981d0311000ca9102c40c11036012203840e0040640801c006044130380c8400c01c80d0454966030300b002080c600b14890390400c520b840303500e00c0341004240000801e060081c1c4403180c3c0e46502c00415400d0051840c291740925013484010422030025070210382c1116007080004880c828146400e104194400c04068000e40c21b04040079990440811595800c007000d8881000030b9596520180700e5000e03d05559900100f40070701000002d0042005646c0302c442e070b2040d0b5502d680004c6411800110442c1040303601c0d4000c0382d40790250704050350340c4083c0d0742c03040755502e040d580741c0145640e40d9803008090184d10340c0c01143e50410040c0091041d100303142441007240d5007125040c0600307038002d1090300990000341c4100950401e40b0022648103000c5845032f039 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 599229469 1250 599228219 599228221
    0x310e15041b0203090d03050d1b02010c020f0606040b03030915030a051b271504170a0f111c050c030c15070201210e100e0304060c03030b0103110309070501081608 71
    0x82045404050f00c1015000c7c042c08214a0b07076a03409600c1002c040c072490701c041d210300c0b0102d890001e00b1a10124200002c3d9030015030300e1200c102000506a5200314121800310794090000080b030305501641502d40d410400004100e51000d4046c00510b1241d0265042000350780d0311800760703030000406c81c0040d1450b03407000c204228a01c4045001d00c54404c4005628840745040d041c04610004c49140c0440c140e80c07401701e02806040c5030a00c40c0c20b4010860001031100d40d401e81c603008181c54100c40010440c40e4940c0c021600c0c3d031900c2a040c2d10214000c035480701c1100050034440c2d1600314404410380300e4010391200d10503030300e4940394070080d0703000b500300e01c0d410103120382c0c01550621800381000d9100d031034015050340c40e41310071302410348030b03000035409413844601c500180025035030807002c0301c80643c206120034408075501c00d4460710005d802d442c0100f04403450b80010f9005240f268003c80584c5800010801000b40c006040012a4020b03a103000941e81d070500d8085a02031640280301c00078014030 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 599230719 1250 599229469 599229487
    0xc030230030a0603051009060e39060a120c0309030813170316021608030a05030c07021e0a0501051c020a11030703170c310e15041b0203 60
    0x1009564042c0d500900025159100c0e154245031544075140912200e8640d1829420040c290288407644401d4500404030520701c50300340251410504000480105040c0346a81c00c148510003404080744040d240a903501011080140342c61806080e8000d600d0502c050001420300ca4440c00d21507a8040d40d4402003a181c13510003458003681c005003510600809030b1030070021a00317140294080e030441c1117400044441c4840c0a0706240510054640c1003102d40d800b0884618040212200e00d00b05250095480d07a5501807034130140235136034019401c0300b0003840031f125910b07041051440c10b0800321000750220769240c00440d100c0c4619000b140360a500a40e1451820a0903000703498a1070080c14001d9942091482c101c0c0340d5000488180e00050107400c208108043e00304400c1d40091208402e9894880044860121140d0031032840d20400e070b0f074503410401c8401281580004d06081c1d40340e410309041414a4000300c1c161103101078460307894111001d0b4030400b0b14640741c036040c0303c2c1d802948c1810302c81 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 599231969 1250 599230719 599230813
    0x61b0421200f040f0e030f180a06020d0c0609050609010f0621200909010506010f111e0c03071e06030b0a090b010302041503020a120b180408190c0302 66
    0x150365410411515552012075203181800071f084058152104240ca400d6620303803140e0501c9512440d64021000316a062019503408507400e02c2503407450030030060104044c680b40d0014450100c0241c581c1c0108020b026070300c44103400900b103988459000b40200d5481e44025a440c6001c4000510322914140c9594005010b4580403004106051150280c000c105400718000c1001120610540d95450341045015030704812881e0101d40145003e103032004100942543d10345401045840d284d00c5011642c1c0380d60400c10052104620140a80720b10329983d5010515800c0d072143d882d031340c3c0003034000003151451103846000052000200104c14051501c3c05c1c100c01442012103a13810980c00b008041110681d50340c501c48020403d560059490401c1140203105030350380041c0b80d04081c01c08111505036520003020790f80c1c6440560058900d600c952520310300da486802100400941050925030042d034005015503501400b030703001c0c0d80141c41e40fa211440c51a420000d000d8102c40a00744003400d00481d = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 599233219 1250 599231969 599231981
    0x6010608090d0c05030d0c1101052a0304021f0908010548040609082505060a050d0906090c06050a120c1808010c140903061b0421200f04 60
    0xe501586c1c03070200104084000d44601424943c04999860401e86611b002480b400da840402c028010701b43e00003040004c00010404070740b50b0030034400071004c1402e41d60303000c0c1c0401114801a03e10f909840c0110400392480c1c6070f030301c60b6002d5946014000317003290f289600c590610f0a08400403007080c0811721001d420000c011003499140c10f003001c02121100355064020400b50100c0d03110391621900d080c0205162101d04580d8090007104030501240f40f6030080000000c3d910101d42c41c3c2e0310b5445009c012591401690ad00c50049400e000318a01485520390200342c20500407401c075603540da02d0f0081511103200d0344442c000001c1965481d881000e51940c0034070013441052418021004460390030701c00c0f41a03260400e0110740d54954503411140c1d000790400c0c14407004807880600385000f132000a0340b0794000078042c00e410075a5401c01e5060700d00c0c0b0011038001d03205441d04065050f00c40c0600446038044d0280841e040300056003a03002c041c2039002d4a05401100420094800807050180009490 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 599234469 1250 599233219 599233223
    0x90b0612060c0f0a1404061d0d050c04020c010b0a030c2c0a1a03030d0c0201200d0506041407050717071e0507230f0909060a0207020609101106010608090d0c 69
    0x94252078501c0c083c900100141300031f00b01959101c450904228180b0540e243c101a41445082c0032900c080c00200040b1b0600d4a05104580043c1ca07801062001809402c0e0712040950040040c040402004585541d50080c0c600f4181050b08521103015242010f0082e4400302081c0c0a0350400100780b00900e030007401c0306296138482d551a19100902180c0795801034004040c4c200e403262018007060344d0910074181c030010382000160900301c41d15060003052158401c07100e031290301c900014484d501e80745c11071440e82c00b980700c08080c00e00d840e0100070217a07088030b0012101a5215021a07003018400c000380c3d028290000d0428505144000b086502c4a60281c8204c81c04d0007003080c0000c0309c0b06101190719011504210100a02c004001004480707102e0302e0a091041c1c0000d818044a1040040c8241c2d0014000b240180d480301e00f400042d806010b40001c460780419500441d2a46a0b80841d584910381c101c00121900c3d662100c40542e4990030480d06240540d00c08003208008511a461102d1018 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 599235719 1250 599234469 599234477
    0xe0103150902060a0c03030c0906050d0b190303021501050a0e01180e031605070e09031e040803030c12090a031e120c020a0201090602030f030c0703050d090b0612060c0f0a 75
    0x16620b5020840c103803c5441c0c0280402c01842c40b110526400d8014018604181c0c42c040c41040e04290303018007107000343c040180c0c685540384040a001e459074000c485e4502915024110825500c0c64000c1da03401700d01c440000712162510001900e810111880d00c16181642d1007820a68201016060004900869050710070b071500403c0804280030700041caa000300c0242d01850a86980c10514a800c010fa8005804000c00340c0c100400860301000740e900c182501e0810400d950030441042803e030250b500000101d010000138091100050802045003c0002d02c2000e4280d49843c0440d032198a40c04014004c24108100100030b5407070740ba840030540c522400d09260300c1c0005102c280841303809422030f0002d40c0c0300b043c0c404255a04a0710078402000d0602c0154541808841495214000a0300300326020780701041400801d401002500c000c1d00100d8810400c10315141000502c10343e041d40d00f24000c3c0d1000601c2084040042240d6201c1c00486003014139103ca650010282da6000c00140d500700 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 599236969 1250 599235719 599235731
    0x5010909110912010f0b030c0d02100215010b1207030b011706150403151104060e1c080309010609060911120604020405150a302d021c060e010315 64
    0x741d41c0e5000c0f0200075600420000802004929031003086500d550403e601c40c0d480b104c8054096502d0482440e60240d050b0b4240f1200c03582d100782a032901450341e0038074060300511000442e0001200000d0120303000240f61040458880c01b40980480c0c0d541425240051140440c560503c40006196508140d02902c21031291294a000c100300380c0143d0021110800c6034003204200300d1040c003540d00c1e42d0303104100040c50309191600c040c0c00c9401e105565405003000707001072103021100003d414403c2c0e40101401d952464143c05c058020480342c010803040030b26050000c911605c0901c10829480c0035103c901785840e10a410b03003e5a548001c00382079001c4e800704000302c1c00351036110a6606007100909050388844825602400d026104451440201c1009e10398140b13141c981c0e01c00801e510400c11000400004c521416100d82c0311035401c408529400d90b102c600095001d0f40189802c8070071882110720300000040d80c0d0103940080c03043c50315030803202c0014030200d004180d000030400e0135140c2c00118 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 599238219 1250 599236969 599236987
    0xf040f0b06010e13390c030c06021614060108030909100b160b0a0207030504050607020d05190b090303070806190305010f06090b012c030a0c03121101060501090911 72
    0x1114071302a0102c0f1807901c0301e80d40503000311140292055810196541c0c1c420000d4569031419001045001000b0800f5844080d802d1500460b00440c840f60031501c15503468032040041c42920300c0c5400100c554600e000031144801d0750224805043c0c802c6500690304d030042e20381c104a002140900302d024030014108000903403000c1407004094441c4228070310000201e4a0805040700c0f500103000303c1c00680100031000001e903000c02141c0603034000f00e4031591a1922030011403003112070904003c16903c904540c1101c0c0701c0340c800042450074802c00601d411a510590304988a0200341d1b80000400c151303001041142c54400c03038641e201c40c0300d203140300b06d00c83d50ba4481c04d00351841100da2000c2d00780d681d07005000070039180c0504c0140074000c3c245441d0701c3e0984984c88203100c904604d6560280110001040180c1c1e080c02a4510260840e0540480c581c40342402010301c0d80200030310021540103d80382c00c0c02001805113408a0b03c0503110041110300c2c0101980280041c00490f0002886c00c00c01050 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 599239469 1250 599238219 599238229
    0x609010e03032d0103051f0605090f0c07122001020408060601050a12020a030b12010c1202030604092009100f0302060f0d090c090c09031110030905030a1101050f040f0b06010e 77
    0x1008500680013440000881c007c400d0356204120945500d03035040c0603080c015070311369040c031079004440342c030400015070b8440c600d405150280d1480101582600d19a00d402182e000000419400c0003140240b214454007082e42c0c202e124610820322540c010400088040d03000d074020b07158521041c00e1904409403504009002ca0303101410250100c3d0f561040c80030181010fa03103424003244583c001308640c8001c000083d00000d80c92a00c0316a140c0c00200040e40341d25650800c1c100c40703070b002e1002c502444804072500c81208078001c1c628010080395001800560424000c81c049854054410060328210340903c425a406900034825400040000a0503c0d040d4810b214020303018a6030f081c0f64030300340b981d4041030300c002009203000c10080310414400f00b003070040d0f2150318001c01c42e418003201503585000d07406003000e030318043c1c084c7c003005c40c990307860b2600311807808031641c0801c008101d5903450504000301244140c60140140450034044400241c0c607000e11a00701e101414600540382560000034 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 599240719 1250 599239469 599239471
    0xe06040c0329130206040b070b0613020708040905070c21020601060302130519050301061d01050307150507020f1504084c0219020609010e03032d 64
    0x403500c0c01044810400d0210380000c6001950046196080d049090074101181c0070b4040e0a442103409080d41c69411036880030b04a50060000d912020b88810850810f00030152040301d03070a02030700d242490b040948400d44221103003039a001455609060030001c401004220082c513000074044d084100c900450600b05403503c00c0c42400800c0c0d40c00c094007080003414140d06911407814180140418054403c4095041080c4c810270360311150f0038010350501d0402141290b00c5650154607041010540700e80c401e81d11524150062a03080c003599845060564622562150041118240c00c0780302c8918030580042134072500080030382083c051440c0c000b44200f40301080c018405400001c00704007401c000d00c07041040750f2150005000b050000f84403085121211040703c0050102010503c0205203c2c0601c00c040740c2c0c8240c0119100c880a040c250b00d0140d44e610201d0140c07040100040c2c0151050180150181e0310b04099070664070b9540003401d115800c0180f03000c03050300b1800c3c014420034007200341e1 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 599241969 1250 599240719 599240723
    0xc0f050a0b07030b030d0e2e02030a0216030c09050a020d050f2a070624030c05150306151305060f03040b090a03020303280c08010f05040b0d0f02040e0604 68
    0x510807828442e81c05421103450301143ca01982215940d280d480c1d4004441c454000c0065418400d8031290040390201400d0120000e6001d181807809050134690010103010049029001c940c03200d2903006000220084911000f03000d5454914144030305001c0b40c00030354000c00507480140c2060f0125001348141d581c1241d001f0301940f41201040004150300b00600e82d11501880101d0b102c0354040203003c51845414805444580c0b502c5034031208000c0c0780c1d070f0080142001c0c0c50400c0c0c4c2c03070380700d141001c0c8801203445076910400c3c01d0305444100d120100e040b28003030003004004c2d200f6003540c08007440303140e00403654280c4102108407001405031540c4000700a0004118140b1b6583c0c942071a00c0842c4000282c109801c640c8070141c0200069000000c0343c1e001000907142c15602c8180240f03414100280c0004c07440c07840d052105d014001904100140d05880803680c0c034408007615003013400116603841003010303441742102d4240c0c000300da10610f64126060014101203044129034100e14681101940c0c1 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 599243219 1250 599241969 599241983
    0x40c05131d0a150e0a0602031e1801050f090a02040b03070b04030602040302030f0703050a031101060314060414011505060306180f0f13020a090b030f37050304060c0f050a 75
    0x408803c200000b8038216018618034020442c803004400380d0341d914600701c240184502ea0000104600501011880341d9502c105483c41340e26140c0050403110420b40641d01c121150300301004115507640314111680b00b110780790014080440d0076000c00000c0d017040708141390503004444012840b00c00850007007010f103026200c05a07030b95141d44107243c034201c191500318403a600034003c140000382d0b01081507190103801d40340030b41c000322004d4051401802240e10080c00c9140e0a003410122800104ea610704c40c500034411840c403036030609809800d80340000141d07269204454001e005030300d4040051600003130702601c814440380c000586c1a6445c2d0054a200894241c03107400c0041d410998184503900c045c0c498082c103c1070b0a039501042d50924207001d030381c80c3d29413601488401034400300700d008240400304080740c402802c0c4070480c0c9003044607107003000000c14581014400c4003281d00903120a0b1544070300203500c0c1034940101141c41400e0990110380404a40d40040041102040800001405840 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 599244469 1250 599243219 599243233
    0x70e030f0309030705151c0c08070e150d0e0703110a0803090a090203090109210216030f0308060a17330601080603150a06060e09040c05131d 62
    0x1041526104001035059003650041160304841d44021032441c0032914140c40034020a0036a142e072400303601603001c0c010304c000c0d0b01001c100014500ca070001043c0d031115441d04c83e0b903034a6007001140c040c200b0281c815001001e03681000200441d0000810300000c410307000040303000e440c240441c20300d90310794829503c40710141c9129040e4038080e66518000c2122800440ca000c06043c0400c0080211b48601601280d0110020710403003001c0d04803104a07070f4400d02c079109507032410f41190b95500900065100620903801041c025000005603441525000303400203082e81d50640c4d08032130f0000c0040c15070350411529000000c1050f07104000720002e6500c0000b400041d54100f46210075004d01000a00c190300c441c1b600b000e41c02a1305000c443d00054280303003803c040e43e02d0001191802d0241009140c14026410130043c184283c1d40c400c01c15100c04c0d40d50700d64609007403010030010b51400e0360060b0003160102002c2250f49000d00c1c8144079020500c02c0420001001d042d647c2504801800c40d0100e500004 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 599245719 1250 599244469 599244497
    0x6090c090c04151209080a0c05010b010e030a0209070315090501140a050f04050403260109060504050f130f14160b0a0c1b05030f0a0303290f1807 64
    0x1003485030344503010032942410540f8002c2c100c00e0100228a10009001006014610700020394105140158000310360b107554071045007005100315400842507505500e810320790740e05c82d84107220000904400034003e0240e00d909400300301c4e0411020309014107260340e03281c02c0f803050880600303808010000810300294079031402c580120b00312000c065980c426143e00170306004a590300c4691400c1064140c1d000111f603940e81c6820740e02c03610b05546607895040b450300092a802d40d03070718507a41a0389458205020082e61481400140c0d2001c0c0c170560a60340d02d4000003003070005203484d810262406004802d004100c240c481110b403031900d207460340154104e9031541d8078a960900c0040d0040038010b0620346030628151000703021071030307164006140d0f1050f85007100c482030382c5100340005050002e003503034003d5800f5a500d0b56541c10200d4220301282c03c0407003284070301c074944052454600c803201d40300019202150030003840c0320007030704801d6000c241201186541c3c00c400a080e881400e0584480492400750703 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 599246969 1250 599245719 599245729
    0x30703021504030503070c03090b04090c1106070e1905040c0507120207151101020405060c0f121e0306120a060606170c09040e03070503030702030315091005012006090c 74
    0x140c5040821407400500000941c000112a070000c11468445650f41441c41c04540e0241c02e5848800103030301c00709000c2003004003a44020400b140503100c00080c0b201030120191500400c50329100415001ca10080369803d1596040032010300d00c10b44010f6894440303000400321110300003244002407000c50f1001c1080f2142c08030360704984442c00240700c1d9901d0480c0809101c0c125480a100300041121030401445094040d54060400100706503103c00c5015079403540d804540440c040148240d191140c03101509804440003042c20046100e514982c004d180056540080c00f40e0790000d07510611109003802c02c0c07000030001449000c02203906890000000d14001802610300d202045039030602401c0d00842003210880c02d0199004a085040215140e041d40207040000e4100d0100000300300e0140d901000651003002c80c00106001c01d400c0c8401c2c0f10318031130308403113008070400020303c184442d6008200890340201c2049918400102d400d40c11400c1090965a4100e00d602022055803d8500 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 599248219 1250 599246969 599246983
    0x10b120603030c061f050909030a09050a030c0e06011407051c1701031103150103052a0d112701150206130f0602130e0601023c0c090903070302 63
    0xc6000b03504005100c41081c0c0c44001c054026020200400d40340e0109100e241c1c4044000d000081c00c003500c514046182945030351090340e0a00005020010116140c5040d0040c44140e982010070948080d003800f0260200790300107010750307050211070b080c00d151400c80c803002004020321075070151464100842d0020b034044141c2405000744040005814a0708480a07406411079400848010443c0c408d4400320f03040c0903440040f45141c5032548004420300c02c00064a091401e46d00f41c03209000200c5034070405c2c541841c01c020590044030500810081100001010ba81c4e50b0014580380340c4440c0c041900342c05580c8511620104000800100444204039031182d104003558009010710b03160070b4540c0c07101c0006680000308a552407850301c800303000306517060368414803120707001040340e54944040502403401202c220f40140701c2c026602d480c0c0d80c0c2401c46911606071075a5148000940390010b0703074440580000100c501d2060180ba10300c1c60342c494002c0d034003985603603000c1c5a560003e03042c020b0504c80 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 599249469 1250 599248219 599248231
    0x1e0f1b010b01030209130906020705160e0c04051e0411160611030402031216061811040e0d050c0c060a0801030323160f05120a090f15030b18010b12 65
    0x3c414041c00966480b00d0f1111b80d0090244480041c20000e81d01c5c0100c000d0140c400d001d081c41c030668140342c0c0d01522074134a0b0029152894407000b042e035500148054a481180512030b04002000001e40380101c21241c0c0b01c0c060074009001003059840107a4126868000219503411364201c180c1c124140021403080c1c40303426031004d02803861407610380c01003955106081c141d4900c050000400c48402c414190414580a50082d018407481c8101039201000d04121501540c05c8235801c8450320161803e840f030000685080303005010701c00c0d02c00e00c0c00c5d24660007000100380130703000b14403544030306903a68001080b0000454503140c03015419410014483c0b1841c0080c1d80d43c8003102843c0c540000209416600000d42400000b014901c81e4a00800c1381890944028854070508111040d4081c049002c2c003415035140e41c50880071541d604014469824521402d007060155805401c5094800d8006091500d4043d010790001c0c0c186110348422000241d0020040c010b020a00306250340d0b0f1004143d0b0440 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 599250719 1250 599249469 599249471
    0x7090609030c03020607170c010501030b010537090e0601060201050606040f0b071e06050108010b06040f050607170f0903010c05040e0f09120d090506130302031e0f1b010b0103 77
    0x1411540c41068558507400040d101c0ca00200c0d48004001c0031003207c8014000c164070480c1c8408014413071030f010f484280012502c1c100914004201030800800381c0d65490144021640da02140f91503c02c905000f582110361a44000700d000300314569140110b07202410040000d00040d071505100034212840602007501c1044100410024916400282000d0718588410b1543c0d035100c1d03140c030f60742020714203000e80001c260703000b070090512015078041412294080002d00444040e18200800c612450059150a482e00c103020301c0345080038030141044500c5001d4040140c0740011580099800c03440d0102880f020010706001e886c242800317245480741d800c0c24120306160800e8644241618000c0400d201a8002000281060b50400481c0240901660f9140d500d0040c48540000b070441590161414881c11000c1400014540a1b5451442c0c0541c041c5042c54480401c0c144074a01d030b13a01024440c00240440c8141ca1580300082c0006140002041340d500b05c8000094295200405100d0502d = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 599251969 1250 599250719 599250737
    0x3170907090911091e0403030b030307060c0201140105150a08090307051e10060b041404090b19050609060d03080a0b0a060c061d030a0c050132010e010b12060f090708070906 76
    0x707112174030784603089641070801041c080c941b040840e140d40600c10001d082c05081c5000030b07603001e80650000e0b113408150144031525a07240ea09202c1c010414000c3e242c01280308006401c2018420004c164110442c07a096a04c0e005654035902d02e000d4401e60120b000d4000c8034040440f90b40204150441d172003107640300b801030f1031402a1400040c00390744554400040c180219038142d5449500103400c4540c001028025410010340c80203e4101c110100c0090a140001159803032034011074552282d90f004090104080b5a540d0403115100003504c440241500c0301d41042c4140d0301c0b0404000900380540e0340061080081c100300069607065445440b168010b0410071012400c0403040310060082802c0044c03686800380381c41c50040500e143c1e0385000308200d1400f4580f044604019920080c0b46c04864072180c0d0300d030b4031024401c5d01c003803148034414402000840f06080009071960760001e00104003012081500c004681041401c0b10721100180c2804200a24a5089000400030302800d107008209 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 599253219 1250 599251969 599252011
    0xf0902040e0a1505120f060103030305190b090a02070c0b0711040f0207030212090111150702070605030f06040506041803110d03060e0c0315030f0c1005070317090709091109 76
    0x140200600401d8062480310540d481c600c5d03010004d002c0d150000d00100d030007560b504e0800070300403c025104841c10b9407150b05600300080850180841041001300114000d40341c1801040081d030014a0072908245451000150010000c000d01010703400352240001d217144080c01c1004031014404001c05480c814440040460f90028091039231062130251680d44c0d00c4440010f981d5404450074a000c148100003212050145100c4914042c42d0540c089031522500c032101a10030b4082250050480300c9081c4c0010090310f0310741c10550300309501074000100401c0c810784802080700c0030142038010601c4d039442129000e00c00c1240102643c0c541c40d003084141e0400301e80c400030f000c6c040d00c011200080800800d074101404060110740f210010203c403070052641070542e8440076440c0a083c0315600141012140e0303801070044400482d85961036600d40c00520300390311228600644600041e10481c20b020816610340d100d1044114080c1b800258451580e10402812580007488003440d0b508007424000 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 599254469 1250 599253219 599253251
    0x603060109052505130321080f0a1a0901030803040327030303020702030c120d03142509090519151d1f061d0a1802130f0902040e0a 58
    0x40740000d461283d0050800c1800d0807100c6000c0c510317040c01e019400c0070000081060b401001020300e2000c070030b140c07800d00d031008003555038180440d41400b0500500e40051103291180d40710500030150700d01c40c10045041240420351681d000d0300b0464040c880003040c0020f241e0001800b111124494040904d4064041000c4021040510005040c0754000c1980c0d011550f05219007000b0440181c84e160225140081003607907201110305c6480828503000c4240d82c44c03e0b4141005220769480c40d940c8071408501007648200c0c01000100d801040a98403003c5000320440c011640100b156a601c003240d0140500c00d41e0845900e0103001484c0d60f601c82041003900d800310507140d01c0c02103802c8280b5003581d075104c3d00c03100d510300ca00c00c1404401b0030b2540802c1d66a001509800800b440d086407246082e01c0c0d205001100c84c00703005040d100006d098a2106800c06500103081c200e440040c12500641d0714148030642e030005810000380f41d1b030040f6060040380090090b40381d11003ca46da0038070445000b600451 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 599255719 1250 599254469 599254501
    0x51c120c020f030318010f0305101202030a05060a05070e01210510150302030f060910091d1006030302150c0d09030c021c02090108030705030f09040905030d0203060306010905 77
    0x4144030302046280c05660310030542250405016090f02e03642c2d07141164a85c40055074900550100f20580065444a4800d114407440740710400312404106080c55600c4800d500c80e440100d03450309c00e900c0d11000103803007030244900604083c10041514100018040c0050400d80d4400c0c3c1088050301e2510f40e4034140703001e8100707403d02d07401c0001000e03110041c02290b070144940189448641c80101b071143e95500d41c1c000c40c4170b403488500321140e42e1102410082075100c00d0f9110300031101c08150608ca001040d62202c05404c1c1d0144e51494004540800d4500b000d03100c04201115a40c0d0700420400c0c540c0500114225046c6804a80314a24040b404108107018101c0c80c0311010b036440140008050295030301504e07082d002450b0000341c9100c00d0000d180607841072400c0f809129550000a40060000f0559a840f90300c280074504121201e07010b20241d40090496592040c0c4405000c000304500f40020096041d0001000da582d152107410305180540681c032007001603142008014682c1d221805032 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 599256969 1250 599255719 599255753
    0xf13020d1b0b0f0426030a0801061b02060a20070609030b070807020a1502120103081908090a0201050d0908040312020601080c0a05090402040b12030c01061d2d0f01051c 74
    0x290034007404001310f1500c0b1108003442e101081c41b001442005613a0410b003018125a001d0791103d00001174544802d84512072600006e400c69014001d0304045800f1700740c4030304025401078080c00740d120b4120300c0500e40700207075004d4804201c498030240b041c01540d0020591020987c200081c890400c3c4000942d0350034440c1c00544100481e14254140040680496000310010101400107584034103118000b913000e484040d4240b80d0351040c4280c141d01803a601c51152003d1005806000481d40056a20303034004910128600e980349008400910503c010b80003035401209009070034455110082d241c910182c00035861f071350041c0c0b0342d02c556994440711881036a50540e10313040320307407200c0c4007190141c01c01601c0c06502405445114074501d030000060107400c0c910400030f00805030307201550541689410010521211400300050314121200a2440d0744102c42103803140440b10141021032006060383c004000400e10700c0100031915110740707082192040300c3e92000101d6000da41d40029101c501c081 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 599258219 1250 599256969 599256989
    0x2606040c1e090f2a0518041b0f0207170a0f03020f0604030e04140402060403022b0809040606080f04060b0a0515210f0f13020d1b0b0f04 60
    0x52903400509145248004003a0228188401e05a480c09200642040d0f02c4007098444c40c04e812106407180c00c8611842e41e1125100c0030b1401c215098176003d00c41d20484510780160715018003400d0707000c4a20821020380561750761406041c000c400d00070f0070700e007065100d03850102c603c203840c0610800c08a5000f0080d544241c541881000b1841d05904011105500701d41d03500441381044240364000d1b0039041c1e260302c2100c04214150340c852414032402e01c1510040c0d0000005d01041c4014107121035200d4403542848000700640040040360380b070001c0780030011261002c1c0890052101c1c2414028240585100d05100819241c07004840000c407070001c102624403501c4400140c00d039103800394400050200030340004030b121039035a06003200e94403180c0e16086404888200b0802c40300b0511901b4020b407031940c4540d50710b40f500c000c040c920203000b030400c2c0400c15540c8034150050341d8480701030501307600c01c402d0328045103172525100034020180d82c4189200b25041000603030005081e0129410388021001c = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 599259469 1250 599258219 599258249
    0xd020d030c031b080106120c020616030b06040906030215030c03060f120304091410050d030f02030417100608060c040302011404090c1d06090d0303050a11042606040c 73
    0x107801c034058031502242810b481c10904602c1c0d4001e500a0200d41a51620307203071404d61110918001c2e0480c0c48000c603c0006800090205a4117000110141d05003a0b141c5070101c3c04406503000120998000e521000e00380da9101000c00440c10081d20309121104031210560039890702040e41201480300521281c800c162080f07000d2003c0c0d60b2040004044117448048a4560351256125030050410f1824103e04500035000513048a001c0d545400540d0000340c411460f0341c00e66903041d10508848280d00003540001e000c0400c2c0411003210413044000e82400507d400007920001c14221603035504080c0b40c5421020801c1440b25010b003c5070100d80e42843d0080c222151442c4061031409250803034a1010300f4600ea04c003805500c8605154154401c1c1c0390b0801c010400c03c1040300c5449200c0e0281d8014020211550120380258003e80d8030500042c0085500080c1c0710481d41e80d81d001d9001007400c81000c0c0c50711842c40000a0581c5001191400141440d041c19103440070150f01d41e1095200d8850811 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 599260719 1250 599259469 599259491
    0x10603120c021f0507020f27070519090302100c020f0607030203271021020f0714060a180206040510170717060d1106030a0e0714010306080d020d03 65
    0x402050f407000c840e4100840400102d0041696120320002e030b00ca03515142c02e45603285060340f0081103041100c90342d591852407065994880d880e0081540d01405414032458041010403045441940b0b410b503120f9a04030700754030402409403280f42004007001222001200103840c0c0083c080060402150440c1e08c42c4002d203000c902d940308550421550303880c0b0352008508100c1480f020140c108003156003030901103042504907051291092050003103118070060711f0092082da1300034518070031806c41c0e00c0e1400043d5141e400304400d01c440d005149034440350030407254070f8242c4030315031000041402c1500d420300702d0303000660b8500503805564403585809104e85510750090210490b03000361040804c04601c0c0920700a0680c103541000a210304901a00061451400516001180d54070490010201c891181407240d1904018044165070303075030b02d10030301c40315a00308040c0e001484c22680010b94082d0003400101540d083d58482c81c2d241d0b00000c2e611003415001300380244c10740001d01e800504110b0312 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 599261969 1250 599260719 599260729
    0x270108070311090d060509240402010c031b15050c1e030a02210a1407021e031303061a0418120504091802040507023c12071103010603120c02 62
    0x10143e180c0c0000300c203a00e24100308994101e80c0c41039001c8002d45088150071994140840d1140042c00d440d00904c00c00a801036019024140e0381c40e000c0d203401504088521032583c14404580303029150b0018240d03030b03c8070008050003500d90160a500c2d00c141807010041c5a001c5004082003954905500840002c00720386c52a0306482d040082800b42020046070b6007848403207410300703498510902c1d061031034507500840c480791514010a042da004141640c401c1c25030a68011144030081014001041030490355030045041c0c1e40618000c260008011526485201010a103030107060b0259080c800c8143c0010700248468403400d400c4031b41000b280c490400304586a00c11900542d01692920520110340711014540e040801e200340c90401040d03c8010f8207a0341c480c203d40034110189021180910340003143c2c001030308444824000b031a400c031502420389081445000c1050011400411601d0030703c183c5042a52048034142c008010040c11030b1200c80d21000e0300780810051000c0c80784c050701151a0 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 599263219 1250 599261969 599261977
    0x1707180e1c030c020312180a12020d02190506040330091b0e1b130801090b0f09151302031c030e0102040b090d0309090908270108070311 60
    0x8800c280d8488000c40030030650480c400d048810002860241101d9450340004110303440c004445020300b1b5141d4403c1404405000c070b85808580c18010110b5140008907800c8401801e801e0940241148680d1050020700c1c01d61145800d10b081c200b0000302e04041440414030f00e0300250503141086ea1082100b168000c400002901d0b22740340c101c400f15140e03a0041c00d40c04950a14070450200c035000e2100014106090b80c035005440c190074036140411881d003020b44c04120400d28689150b82000800840e07400c00d800c090b44824061394580000c841040545585144d02610105940c13226080c0054011394031132170080086c600940600101e082c065410403c0021250b00800b240d1009404606542c01d04101c00380c0360000c207007041c41e030759030b085018020340e000d4458a4044a040138804000c1050620a0f03032000e07810702c565140081509130a0f8050781043c14001c000c8141e4a400d240c1c1c0c080b84c1e44515240c0c50701c11244500c40e80001d680d014004c2500030540340360104103c034040546000070f100b = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 599264469 1250 599263219 599263241
    0xb0604021605070806071403100509060a0306050109050907050d082b050a150f0e0f270102071203091a0421031d010e191a070315170718 60
    0xf10b11000015103030800030f0201c0c490381b80c903a11901d0000842c14008554001030f200d030020446099010300684c00d080710480d40c0824002c5c40104000d0b60f94840038200c0e00b007a0014440c080c0c403a010800000800c0025800a18060b540d4001032101900c0d00c5602d03000d44a20640d1000444a00305c4903002d08600c03803c800f2150708010841c40c2400f450030320083c90719907180007a0ba8846070b0000b8050504004040c01ca4441c01485030305540c0384c042d1140c900100a055103545140074000c10f0040d500c0002e003c40402c030a41c001a90340516044c0707003030340d00385d03540582c020036080011400c00220304180c804400300c1d0302c00ca026580d4580303241009004503031000c0b2001e504450079050032402d50580044032248040f00e050008a40c903961190700340c0d082d01d8292030f19a4000c40031014546005800c0100440c0108600d121038004040b000c0c001c00d000342d070800c00003505c030380d1001c4151002081340e40050204402c02258100d1903440141c840007640304909a14240f010b811241c0a400e03080154444 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 599265719 1250 599264469 599264473
    0xa0306020d0b090a090c17030708090d05030a0c0b06060708070b0603010f1b0813030905010819090c0603051f1401050d0603050604170412080a02100903050903010b0d0b0604021605 79
    0x440d0540c0b04138000d200510042d1040001d0080004041031a0962950309141c42005503180510b40c0d140d01910b94840800c06811261054414001c0364050010f05242d032490750b1070040000550030241c03141c1001826091282004002d04000903e5160403614090391240d882c4606580b00e40c00240103256240380030706500d00f404809918101c900c1020345551490b91908810340c1c54401180d202060504801404998507101c240040d6008a070b546511030120360402280c020b82004140c1a11034030356003101c8043e41c550041c07050030b416000d0154490744004030642d500055140380101d41099110312586040715040c04401c50744210200e848400d40303003600b0300c0041d5480c50410307130745d01c82214243c8105084003449011031200c4130444041361200900b10b044210241c44d070354500d0380001600002c0d446240100c0065820303600581b03868502986a05488491000c01d00d4203440200342100c0c80b400904401e0380005001c41c00c810f4100c001a500141c81300100810090a42a5550040c02c80c0c = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 599266969 1250 599265719 599265721
    0x40303150e06010318020913020a09020d0501090b060c061b09090f06030c060313030e06210414030403030c1e0b010b0c0c01090302011211040b0a0207230a0306020d0b09 74
    0x200481d5102240140b100b84c4c0c3c1003010304440840201014034805000398841c0c0450041003a0400710f46203c000c26000828900e20140d607624054201c0c1e11801e107800c031560716040108510a5240f00b1b4600740ca40685245207000166403800b41c40d807100421310524940744580103d0180d00e6102a90324a140140078040326080100d6000401d880c2102d2003842803003084082130340c0303090800940c0d000700c2028000484400c565502076072004d2072005c0c4160045001d01400d04e0700c2d48041c080c1401218030003120801c6042c142000380b12030344041001a1541d00410080000a5005028500d001c3d0004034080350440d08a21031000ca40384140003902d81c00610300042041d130070100007081d07c19a18000c4802d08030400c401941c6030000d921029012800c10b440d5900000708540003241d4409215020b1840c05880320756241940d00000c19010040e80b003601f00340056101010419449202d1041d41c0c1c081c1107034000041c0b003103201804001c028079000b041102008d50303650407440001c0e0004140c040340d = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 599268219 1250 599266969 599266979
    0xc120f3305060910030b0109020c03120a0b01080a11120c09040212070905030a150506210c01110721050a0501060e06090a0c0f1b08030405030c0706080108030a0804030315 75
    0x1078801912114883d44001011503201c0400c0b9602034100d96004116116983c03a18100900a412002c4806014003003040070500d079481405c4040c0c0709100c40980050003d820b0b000061040400500422401d07240490310b0b500c5080d41c009851589561080000440d07a03802c01401090180c202103035040340c00841e0a0603150f0340158401d220b080039039646070760b4554940401da51a0b03001240904032504070f800c080744441d255000300b54071000141c22001c0680c80c0b0704211911190b40d81744440f041c0c000c01e441c1c0141c2e6030311109111885110000034058a030030454407280703903114400300d4061010b201c0d19480c100003043c01140d40036600325008000258cc2c0300500108404101d52492140b141840000c00041070303413142d108401080d94510240090000c000ea8214048012502c404041d186039400000e0202c80103520840c40354015545071005844404e01e1315440d60404010301100c04018040c5803c000184d400c80c43d4286070000c07a030f0320303281070540060403c01c03030f2500d09408602e03011034 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 599269469 1250 599268219 599268221
    0x2270711030316050c0a1a090106030206030f040827100e03070b0c0a0803070801181415120604060b030106080d020a02060a030b120a030905180a1a060a0c0c120f33 72
    0x540c900017887c070b0584d551001a07540c01c07034503d400000d500100900100d00e48207048620241c2c003d206180c054540603400c011403100520142c5203a08030102c18007840c03101e00303092482520208150038410440c003200c0300040c1d1108420b0051604c1c21002256500c89181c040101c104a6500704142d655a0f00305042d000b0042e0109000303500fa10035515131210140c500c244111100d60ba281800ea45654480c011103880034032200061542c411000d080b03c0118034414004c45000c2c40c07180d0000188800000103050030350310b02d0f500800041d04800f10041c22150041a15608190b04031901d0b50307100c040c140c0039401024a6404540c00c00e10009070320841c9203001802c110b03464060b4903100c8c5074954400411021801e00c0d0740d14400300c0c4091000c036082c0c6241d5000002c40940400030507124071070a00c0810016000070307128000081c401c40600c400d1040d9910060054017a806041c4c0d10303281183c484d01024000700c10000e050070184101c110110b40384890844005d40e1f00e0387c0500c18040c07510440c030 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 599270719 1250 599269469 599269493
    0x1302010e06190f05030702031602040e0f0c0906060304080403060f090c03030c0510050907290307050d0c14070206091203130314060112080a020a02270711030316050c0a 74
    0x10100b0010118000141c0c044c0099900c141300d41d500551401e0291804402c440030030000481e00b05481d0480ba80b84904103100b54100c0158440040c050403110f81c00b040b40215000d0702180c003805081041c840414112740c11581030b20380140c008105d031000000004001e0000000103810351441c50004400c060b440700ba43d00c4481c0c0260103ea07100620101ea000841d030090700e400c4050b40c0090030400103522030701c02809101d14400000803a03601c4907500c1301c1066000b100c20200140700040c811498030601c2c4170b00d1031300c00d402d4640041c86501c0500082d0441c411103901a00c140c001140301c3d402c595400f078050540140a60070399031110205400c4801484440c0001c849a0005441c0c2444d01200028114120707114038940080a5a01d6120403440381c0c80f407102401103000e00074031000035849501c45112100400700190181d4807000152a0001e04042c2c440e0041050103100404d0055000043c0d03900b1103615544010000404a02034440e8403c000b041807080c05007098420a00420060799 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 599271969 1250 599270719 599270767
    0xa140d1b1701050a05010f05220e06101a0a080c19121d1e1e0a0c0803090a090203220803040b1803040e060a050618040b040e03031302010e06 62
    0xc0c0310310749444c50300d8416907100b40203882e0b018242c210100000c1c0341c8140e054180c0e185d4503200007400025040280c00703a4070713250303a4151076900000a000403a103000c00380000500743d05200c4030811554031010f040030306c01c4105140811000e080444c81e0501010700b11810124550011184881702c0a8064102c10101800302043c614004005a142c10f05460310250011050041c3c0000f0110485100c09030100c0c4402e03003d00d1040c0070042d1000b205074051500c13502d031544024103156180b440c4c2030070040c480f50010b590b1600103101040841c0c40350f1003030390b0603a080001c0160316a622844440e06817a020b000408010400d2060241408080c10040d40558040d281c00716032075403100d44090b0f00c140100c8080c940c40d40100020008107006004660308110b0050001d5a00c0b507899000840740d40089640d9075160194464950b9185014810480444003e413424080b04100c848540d450340001003610420021001d100340440e03100c0c50002c81c0910005000310384414000108071107045103026a = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 599273219 1250 599271969 599271971
    0x1e0f0c100e07140909010204030b07050d05011406030435090a090b1003020703090e0106021b040c0207180209150c01060e06130e0c031e0601050a140d1b1701 69
    0x15410340c0380c002182c02026a510802141035403c2c121081c8135002c50020325480d260355081c04003000142c0341c000c2c11402042d0315965a03440d120f00800e5181181c03010313804540b801c0e001c00700054031600c0e100162680507800c8501900110424120082c03d44054903156000000940c9007400610040740648407000d0180c3c0c0ca0845240c0343c4410300112810803040310741c03005031040b107003540520079001843c219129282503050f6079603034121641200d0003038101c540545c2010240da1665800c00000c1a600c032803c550034050842001c80c043c2d00ca5000380100418012489425510701c0da59804980c6051f90281020000ca8081401c0104541284030484400d50034410001188103030030b42100d014980007440c0c1400d001205075400001d02070644244180d0299000303000b416502400b01003850b10f120140c86403e00240f40d2020305104050b00303e0303807041c54200c100f032020300c2e64000e0000c0c61405c103a448840041c402d0400d840070300004046210303e10b24125010030380400010444000712010301c0 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 599274469 1250 599273219 599273231
    0x9070e0c22060507080c0a060218040e010b09130606050306130b0106090b030a0b2202032d010902130b070302030d06050906030c010f0c14061506040b1e0f0c10 70
    0x41c0741d03140101e40c1d00c00c800008405124010104c4c1c20780300201045903007001200e00c40886a9034107030a0380c02541c1000760303060104680300c50a080c1805416074080e1f2501c000c2000c1014040000c80b15203000d0a1200e4801c08184a401044910b0740000040c080c000c0458201e4601030b0a804041a84884100c0c0d5210a00d0000106180507601c000c09480800c440282155070701410741004000711111180d004000c0724111211000380044006c00c461544d0015a89240c0702482c51304c00500300c05100400c0c220803100c50300d143d07006000d986c1900d0030518050f17542c0360203440807444101c49400610350480c001800310b00301a0004000d141d1061801c0c0180001503454003009002e004c01c548040d0507402070b10000001d5071181da07412045000600786a1580d01194a414803280100000c002e050f40c056010700c100400c41000d6004403c0b0203c50181c41c290410051301a50301442c3d5417081190b80011040c1302c035a0144061790003d1f001c500c410f5442c0c41c21904815625801a800c86001030700d041 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 599275719 1250 599274469 599274517
    0x4050306010b03060a1d0601050d020f07030e0f060a3e1b014d0601050f0301020903071a040510020d030b0102120f0f0d09120f02071d09070e0c 63
    0x5048210a04906e0110b001d558803801034079a9072180c91902240b039400c100440002060764094400c42d40070303640310b0520b0310000f0b0900101c904c0c0c4440700c0380f04d05030500113802c4c0140e104058420482c0c1010b0458004109641b64900d48020100c05110400195030112203a9000148a900500d808070418003049007280055403820f041124680d602e100490644111403078244402e0f1300d1320041c54040c0301100d001c040e118036480050801203a640c01c0400108810710b0004880406400120001c6250983d0203000039902c0e00b035403003212817080031070082c01c0310314540100b40c900801014103410000181c14034004d464500d088040c4010914240c00c0a0360f07035100060780c0709881c81001c0f030186010046c2000c00c0d03580d0010000c50f0703614541004030b24030184c0180681034015205a4503c4646074698802402c00e5800d21141821540302150400918820341d41038a83c3d000380390134140c040d4540c059090b0030114a60020807070412140c06005802c8002402000c90780c01e9400c004031880418 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 599276969 1250 599275719 599275739
    0x303071a070c08030c0a11010e010609060e0c0712141c0c020c060a140906040602011401171b0303130e01080c120303010510050705011e0e1903031104050306010b03060a 74
    0x2d60103498403406000150310030804800600110306241881d19040c0c80080101e03003503072800346414001348d4407000204000740c070340c3c040d010240494840019042c40c100c8001d0069010703900303025182c0502d822520281c0c1d0b01564140b50480d260000c015a25a079801e890f203040035041c081514801d01d400c101421541c40800d142c242c00394001c280c14640100030238202c03070940c4240f645034207001d410002d56102d80e0ba840010001000d0035000812808070311000c1c44104030050380000745014050100c0c100d115404142030000882603400e40d4607082104001c640765025180c20303800400003a0358042012400402214100c0f83d103142140c42c140d8403003007449a407200ca080046c4455205100502045c9400144031004568516003075050284545030903003525140d4080b0007100c0041e000402482545e8002c0040380d16007040188140c1a105616002d401c07106040030341010f549452503c106240b020485000b00760003001c0310807550b1202800c03086603000361101d500c17480d101c10700000c00500c4 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 599278219 1250 599276969 599276987
    0x2113150902090f0a0b030601030f05010c180302010807030f0e072408040b061210020306030d03140a0c03060906030302030c0c03060403210f0e0607020f01020924090303071a07 77
    0x302074500b014a44906640b281d14200c0075244074810754440350034a07116182002070031700850003503a05164400039801c1c40ca085032100c078402410428141040055140c240c2c440700102d0340c1c2860500703060fa0300c18008038010013522410507038607810010041c80300100011640f0030317196412039510320460300010b055040800d82d4000400320703045000040c0070500c3c6202003544000302424540b241340404982c5400c00c0c1d03201d018810703a241e000c81402507606042280f0b2024003003d00701044820505010001e14400c001c2030340071000d0300e400050220900c42d070018402007080c214103000c100d03201e20f0040d4590700b0855650400348140c54112040b81341c00600a4080e41e0182c0718a0408055101e40042da040c15110044206880c2e0b01d0001181007180f02d81d10380b2a0701c07500a000541004d840080c24000f8001c003c004981c01400038114507590500112118402803552000000685440c80d24030301641940d6a49400b003c507142040c03029444d2141818100c0021000080e542d0305411b860500c5 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 599279469 1250 599278219 599278223
    0x3110a090e0603030d0504120e01020d0903120201200706050c1317012304021c031b02010207050a09061a0a020c1302090d08040503010f0e1221131509 66
    0x11030400078580450401c64020318007505403480c044148a0176029118161012103072098104481401d1607400704280300e846009101403d51402c58441c02411101d6a0001612441c100c400240c10716000b5440b80e51b07504ca07030803404056136030740c02c01000d201c0d0003030f900a48a090030800001c01d0118071038111815012540000240f0908140559032000303a035051800143d0360b01d01f0f200c3c45c0314592201c4545201030304140f100183c6018414000107401c25104400361000d1500f1010019401c01000c01d4011a40c020b11440d00702207000403894500301e0307800340e5000179041c2c802080d04d140c103400c00b13800e60b0744000a104030b03442caa4020302a00d1284092910043c3c00403010050300d80b6042c2c10400c0502d0034901e026040002e034400041d8801c5200328126120f210004040259090a0140c283c0704024a070082203414441d05105886918030448800c900300006107144511095a842d017070141d4600e01c150100d45007900012074000c008800550b4042e04200821580910b203004803200d0503 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 599280575 1106 599279469 599279477
    0xb09091e1e0c011d09220c08010e0d05070309050415051903060506030703020307050f01051e21061c021c0f0b160215040501141603110a 60
    0x50501200c9413950310324400307500903944e514614070341c010701010b078200c2251300346081c0d01001070440000802c110000b40000c00c0d000340540c481ea804e64010001c03503020002725401510280601030000b4001100c841c8140803605003034101101d540a0300541943c00c3e6100d80000d4140010025458007201c9410410002c0c010710707004440d0080d0301a8080c00f5064119000329440c0e18540c043c0da8012a0000240ca030a40d01c0b030011140c204200c03c040d81012521107a080500c0d52114800c190b100003070410040712200445051130282000500d4440d8040059141d002c008003c01c2099034014200101648211000000c0c40c0c1481d11658468980c1d03c0c00d40f42a046600c0007a00326604031707041813140d1100e1078001a2001000c90403040b005901da0b62490582e01604646001c514030400d8070301400300340c4419013148820920a0784092092210501c0f4080c1d403401024100c10000b = true := by decide +kernel

theorem cover : BRFrame.Cov 599100719 599280575 := by
  have h0 := BRFrame.cov_init 599100719
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599100719 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599100719 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599100719 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599100719 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599100719 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599100719 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599100719 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599100719 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599100719 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599100719 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599100719 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599100719 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599100719 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599100719 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599100719 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599100719 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599100719 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599100719 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599100719 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599100719 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599100719 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599100719 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599100719 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599100719 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599100719 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599100719 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599100719 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599100719 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599100719 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599100719 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599100719 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599100719 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599100719 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599100719 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599100719 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599100719 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599100719 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599100719 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599100719 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599100719 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599100719 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599100719 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599100719 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599100719 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599100719 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599100719 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599100719 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599100719 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599100719 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599100719 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599100719 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599100719 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599100719 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599100719 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599100719 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599100719 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599100719 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599100719 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599100719 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599100719 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599100719 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599100719 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599100719 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599100719 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599100719 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599100719 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599100719 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599100719 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599100719 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599100719 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599100719 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599100719 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599100719 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599100719 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599100719 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599100719 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599100719 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599100719 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599100719 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599100719 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599100719 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599100719 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599100719 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599100719 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599100719 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599100719 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599100719 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599100719 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599100719 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599100719 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599100719 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599100719 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599100719 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599100719 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599100719 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599100719 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599100719 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599100719 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599100719 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599100719 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599100719 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599100719 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599100719 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599100719 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599100719 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599100719 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599100719 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599100719 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599100719 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599100719 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599100719 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599100719 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599100719 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599100719 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599100719 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599100719 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599100719 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599100719 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599100719 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599100719 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599100719 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599100719 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599100719 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599100719 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599100719 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599100719 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599100719 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599100719 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599100719 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599100719 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599100719 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599100719 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599100719 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599100719 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599100719 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599100719 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599100719 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599100719 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599100719 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599100719 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599100719 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599100719 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599100719 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599100719 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 599100719 ≤ n) (h2 : n < 599280575) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
