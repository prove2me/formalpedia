-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2124
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T05:42:31.343959+00:00
-- url     : https://prove2.me/submissions/b76e8599-8e1f-4842-9738-b2b8598c5294

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 381834532 ≤ n < 382014388 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 381835782 1250 381834532 381834553
    0xa06050a06022803180e1e090c190807080705040606020604111e130515010e03100c0512070306030302070f12060c030b04090c0801110a080a02130302120a050c010e03 73
    0x120115801403c0f130400c15800d2802002c1401c221800001c0c249041034105e40f880c00103d4000350405030714062a0141e403000900c0300c500300210b48280019000c0c0e41080c0d0714103840e010308817828000e134010106486036500c0003520120108801c000c0e035604072000d0140c41d40d43e0b5002c82ea105020354001e0422203040f40a0019440c00c030401d0840516055100e014444c620310001d481c0000703480f5600501078540082007040c048a00120008505c02d00b40f000c005081d403008250baa854100407140c0d183c3d51080400216406002603440e000c0c84904540c0480c07601c100020050b00c22880124003511418801003402640c00f10450192141e401107021898072549076800a019000710f40703014155a1105560315864a00a511040b4007450101c840e0b40d1a0603216400c44a292021407580d144c14070a4600b071580c0202c1182d00550b041c44096111101d80080022102d0564130095021000c0c490f00581039401003400680540641c0540d100c10745110015074284c003031903020070751640100e041c10 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 381837032 1250 381835782 381835843
    0x4170c0f0f0d232107120609020a0c030e131104031202010c0f0e150a030204081902030a0b0702010e06192004290d02030f090109020609270a06050a0602 67
    0x704680c4134440c041a00315182035404907051541078403000001340075a007022000205600a190090903008000c5107414003051000742226244400141081851540030510b55250003040c00c50100c94030040202e213036040a0a09140c3c007a2004031155245d546130109040d0043c458201c10711000c4c6c407403a82c44402000101c036419406010694050442540003442461039806010b035000765403001a500d030b080ad40f00504d490303415000340c0c00a800111440c0b00607200450080d880b1b590001e08200d45450708c0c901680940201810a40300f482018200400d042447c00d11020105918804204041e449107018030a040c00103441d641440e0100820080401b07810401828000d0841c00e0030b202c6600c4a4140b03000d40d00c40e00d00300001c96004800e10034980c1044480f141c0060750741d0001c220020340359000c82c00c0d5010b004901e500c87d91540c140c1080c41d507a01d100e400000194030707110450310f20b4410f0007070006044c14000c09004240c890701c0402da550002600900c0b01e2011411220491140e00b8607 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 381838282 1250 381837032 381837037
    0xd0906140304060e100b03190c030b091002030406020a030b010c02150c030405040914010e03070f0f02010e090a090507050f01050304080a03020f041503050f04080304170c0f0f0d23 79
    0x89a80076a100700c00c001e55403041c840640b003160219800716482c2d4103007080500c0c181c007942c418808c0c2d03450140c0007400180b55000f42d10450b40d101ea41c413809582c0d121449410902c4522545001600020801040007800e6008100141a940b41042030f10035000044030904c032002e400a40007840d50220342c031001c25034805800070488010859107001d4072500030a06a449502040307488064022480049030320030b001d20062009420021030600c622900c50f0f012070f00c0c082d070024000103d9001d018055910445500c044160081e10490241c24030f00403000007040d643c00c0907a401e001d0240701040701d00e0141c41e44c816002d016520641140c455444030a059445107600c0c5042c554200882807503d18100040c00092450403040700028400c0c0a000d410f50700700503da03035030690300f80301084002000b103000c3d2500150070000c0a404180c06081054581c8500c0003860154810310f4904100c0b840c000600c105009625825503002c0d56800806562901c1281080d0240801d20f00358000e03001c804001 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 381839532 1250 381838282 381838291
    0x408070209181203061e03030a03020c0a021804140c0114030604140108070f1a04031101030b120a11032803020a0b04030509030c010908030414010909050c0c0d09061403 74
    0x50710b11182071681c042c1c6002c405110300180c43e4008801c010300ea05e003c49283e0501700d19140303c4450103030088006503c911034521140241030380814051881c003c2000030500d140da02520588132103404910789940350304102c070f080b104040c00c43e0800300c04140c080341c1d54015a00c182c4540c405006001c840c4141030b00002c002d40d07003140c3d8074207850424510341018180208645000b922420382055942103540303025400094904001c205041d001d66010021a800ca0741c100e5002032042c03035400c00480c058504854003a510051020316900d40d6100494404141c510600761442004031400c10b041e2182800040042090810241c016211981c052840c0d4014403c0c4144c3d242c0030202e40d110000e5081c00d440550004402180d004054202008218034081e401d00b0596800d6107402e41860f6644601c0c00b07000c14a02c0c4c4100303c0d00c10b503402101f000019104010b01841545400300817a130883d00046204082841280c840c4902c940c0260b00c95801d582c4507a607054049007850a030004a40c0c0081d1 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 381840782 1250 381839532 381839551
    0x81f14040e0a05011425084303060807050607060e0a14011d0a02030604061505150304050607081009230f0610031a12070b070b0601090e0408070209 65
    0x42407100015401e1040780079140240d5546a000c0c2400a4041250715800b200358090000c0002d00d2008181c025088030388c403a401002c00041c0d508589182950180e007000300c002486607942c0c840307910035000345045a5604242d5010030a480d503441c1e03202d0fa1480319101d8550061010402000422040c4d0004d401c00c3c2c011f10100c9401c882250340c0c001c000e002044040710a65903512035442e00500050b181100e1a400c0717030007801c80c44182d40020341c1344c090103040101401c1c1d40c1c1c0a01c914481d0044550001030900030a40071390305040c03a800d50700550040311b0031201030045800280f01c0d107004080c840d02074001c1c800b04c3d8003110b0a2885003002400c1500009105144c41c4008074004201400554414101d000b07134034181d410504240920b1240c2210290241030420f4801c881020204020355108031040b41da020b01d0000b66400c40703062000c590001c8825420024a10042c00344080441c1c0c060076081e071368408803942e1040c500d925242c007910010700800c01003203140b02500d0040002ea4210724141d = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 381842032 1250 381840782 381840793
    0xf0302150a150b070201140f190906080f10050a03061a04021e0d06050a09090507050402031e1b040617090a03080103080703030e010204080d110309010816120c081f14040e 75
    0x111001d00f8948c118a00c400c200e503000103000030585440c1a0b42e40c104203481e0070007c0d811030412002a00d0440e009045032440c3e4107036400034040150200300741c80101405040c40c0340d8107441703050460252800900541e0034694600808810742802c4c07085803560891100359031105415075203000c0841c1e2090560030b0f0050303200c0030089101d070341d1544010300401c2212400110115035142c41c9050000503403006100300e01c18030411841c0c0d44c490070150055500b90300c80c000190351b261400c2c1f21400088521b031105034000b0401180e0607802484a15040a00d000d15000691329031184076a961908440140003886200c01000054014030140c0111486400d000c203400544102d440d0881c0c00c140c0c44903009030321421040304802c0c0c0100500355404c05d80e0005e18034010400c00040c1607510060000d80500da0494000e00d00c040c0700702400c5082d120b040c00d00340643c3d60183c0d401009024140c465040c98491501d140d090107000c0341c40030040302c0c82e050725494450318040402c0000c0030307043c00300350082c000d0 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 381843282 1250 381842032 381842057
    0xf02100e0901060e1903150b04020f0309160b040503030d0c1b050601090c03020412020d0212010513030f0c050c04110408060f01060311040806010e040303090f0302150a150b070201 79
    0xc0d4400d25003c0c00c400d54544004054603001c00160f10f00c0100024158044064184041155400564034080701c14101090800c0e5142c0400c00911402250300381114020003800b10035400885c240036503110002c025074082e502c80c02410940d20031403054581c558020002001d030740302180c000c600b4030111030601758503540e4a8024803420391264030089030075402002c0140042c41042c0b040b8040542d0303600d4214103184c18000d041c9546108440c002e0f12503400e880c91801195200803003a414440c60b40c000b4442d90600c0a042c0081040004045020808016114201d03500c40d81c00400b4513a00500142a030001d2042404000d12107580b02e41c152680412000c2420311040020714014503200b1103000d29503240c5030307006007150030381c0f040660781d02c008001c104541c038000514181542c1d04051004c0d080d0319207240c1940200a2a41700614820b0250080310905401051140154500b020a18602d9842c041141c00b12040ac82d09001c03504a504800e12020b00c861024103481841814002d41a404 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 381844532 1250 381843282 381843289
    0x703181205010e1c0e0f1c05061509070f0c050705060711040b180708060607060c0305040311010b030a0314120108071e060c021c081804050906040f02100e 68
    0x10603030090341c00307070344408403008001c0c4100300b0b000022542e03001010704840502801400e4a0b01c0c88010341c03082c09810900aa5130303644500510034140034a04000b511140d52130310b90348a0800300d885101504006003412140e050240105100700c0c5191b8880341e08051298059403117004080303091712117110f032003000320380390304c6010081944c14010000c01208007403030010001030320030700850140a03d8501070083c2010130016001504141302d810a25010740c0c1d86c00100c3c0d55401001d00103400c00d4240380715111502d42540c041e6000354000d95a00c03000e85c540000c0c217801d030344042c00c0e07450301075010604000101e44260080301c0c52000181c0707814079112203001152000c640070382240d02690010130080080c000b80301860103d4400146850341520710385140681200541c40c0d020740100c0c10000c5901c03e40740710301d4040c18802c0d8805c51268680c0c00000741740e0720340ca140102540c0240d00d01001703e07607800340c00100c0602c5194084400c030b2880410740d090054007001313140e00405001084890100555 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 381845782 1250 381844532 381844559
    0xc0c060518100902040e120f0d0b04061502060f10150e060a0908071d060108040311060a020d110c07060c03120c12230105010f1103071a010506030c070318 68
    0x10760000b2070350301c0c3c007401004100c840610003408158056249200c10032a03410503500b0100401c01581c3c0c5400e14072090710080c100300404540e0080c0391050101e809102c220907489917a107207a0807100540d0f10780c0811141e480b02651020b2040c00c404a0400040c81c805201c4045002e4034980181c018500c0d40c0410b00607000400804089155584140842a0101706040080c91100174141050b034804d1482c080d1804043c0607076040198100c002418513026261109501800004403041c92420071038141c000c6d04030345011110107081021006894100300c0135642800c2140029100030b6181170000d9503d103000807011424081500c8040407820321a1096904843c1c1c180c80e010a0f21143d80c0e000d0084031503801010345803101c82d440d62031400c0f5019203030905440307007800c0000340602050740980b0001c1200e05125994400083c2d44410002e0000c080c8070f0382004070708126842e90700d0303030100400f600084495209d184003d00000010901c0703040b00781c00540c02031294801301511010f050400d003 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 381847032 1250 381845782 381845803
    0xa18030803010e0c0304080313031707020d020705010e0a18200a02010c0507030f0809030c19020301060504050609150a1a21060a17010b040612150c0c060518 69
    0x159008801000344120f10038105620414002c3c1c803900e5441c1c00d03900c50b00b00c0d01018141045086040e8450390405001e00481d0402100038100846c992505200096440c0b0000c540c0300014020190001900e5000303200c00d080c0b000006041000c0345040c20964182c2020b16905e484a141e1100b44401c00b0f482220049514488154901e503550802500c0207400e6440c071080d4441000b00421550010941c841020f0402260a00d003180194840c041c440745075018240240c44240a20054044111500d01000c03403020701c250002e01c459941c8504110858808a41c61038000c0003180001d86182e124104455210000902501000c2c0d19003c0f5580c940381ca081d88185000000284041c8415800270b00c4080e1801002c214070b020302c0e2030f0f40030815030f845611030102030203942050540000030030341203950400c4c0054001c014141c1d40d2000100007840e812402e690303441c502800e810200c071840c042c0502d81b0410351288107810081c0e0b40c072000240302c010a00c005074040e011003090078810034405450f12 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 381848282 1250 381847032 381847043
    0x20d1218060603201909050702010915090c081c050a0504030512070b0a0b06091e0909030301030b010602070e0c09010c06091b05011b0204021b060a050114090415020a1803 75
    0x140d9841c00c844c0c0410140143c0751441004c3e03110054035800d901300407880c03d8507000030307000c50192543d160503800f40c09103403c02001d00f500c1459034a001001540a400c40502905202d03001d50790b10011503860708003483c0c4210620311030555050103103000da00213110000c90351a0452406039652034650070310400d21640c504070000024030006101120030600c0d000040c03d5410810000140d0008082d4071800180c540100004200004008942c28100d51040e201078103068287c501001c0050b1203034006d00084403c903060000203e14944009004020b58111084003620f50700ca550b241c0c100c9030000111541003003159511703c3c0028425001c0c0c0860030348a29520401c0c0040d49500140038507032500035130704203c0f070203002040c0c0034014422641e0442d015100182d840310151501c1961105580c10003d541c841d11040c002d411009921032412150341080e0000c41024070010086514026100544460707400c0d01000d12100d02e9034010700c0c40307620600b008220040c101c90708440c002040d41c404e454 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 381849532 1250 381848282 381848303
    0x20f012003040e060118150504091503050f15060913151b0509060409112502040b040b1f021c0905030c04020412060504061404080910020d1218060603 66
    0x104282c046050f54100d042401d0092940010b104080c070007080a1080d00303010510141e00310a070342d0064003200d014100090042c440100c4103402100e80b054244401c40d003907c0b0f5803250240f441d0000c01e480e883c0282c0c91221480c16101e0108000035544040c0c142a4034140007000c01000036010350499200840a490105407001240c100e02e170390440c001061030502904111107125030303607480212401e484455a000410900318540c0145600440f2104c1380340c0d107582070894018081c00d111400741a8070880b018000c084074030087c40240c035041d1221540100c1c810b1050240c10407aa00c1d1480c0c00c86032841200c2d04200c000c0502c901000c28465048081140c030700d01445542401c0c85030303070341d41c6000f95000d40c60240b41960200e04200ca03681d014154540c0c80003c20108500c9030040d5685142d001004000c60801e810200010392004400d90310130900650100c5030a800800d00105100064961041c0c03c07407500c4180b005050540e8564883d1683e410602c07000507098460100a540210080d00 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 381850782 1250 381849532 381849539
    0xf07050331060f0f1206081f06120f1e0c0b0a03050108030c0601120305040306090c080c010201060e06010f03090807080418020304020616050a0f1b05061303020f01200304 75
    0xc5004001d600203008002c0210008801590041560441c2ca069841d154150324280c0780c1032070003420070340c0085143d8000c050034003900710f4000b86184d00c030170b810700400c00c001c903074806501551124942c0020107040c00075103400c1c0800e0300584011542144541401e8624009554180c3e507451300d0741000c000c00314042400c0c1c04095152041a015111500056181071201105240c3d00c1a05200d41748150500c0a10b20f4105482842034170021a0f100c9418012400580703028a61340c41c040c041c029007072107681c2a094507581705000d08021205804c10302c0026455101c011100803450169450515032070f480c0b03403000190010010700300c4c11301400c84980c03194184484403c5051008540c07002150050050102680e108000c07140c1d00daa0381905940c0d04511450100e01384042c034a00074011100e01d401c19810f0000c5003001030b5540041c80380b003d061644981c00c00000d8042c90724002c46412803da814001400c0c408410070018005040c0140c0d040d0100300c5010201e85040000141504089800c1 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 381852032 1250 381850782 381850867
    0x21e0a1205040327061404031a0415050c090f04090b040b0a0618090201020105100b030c070c090c02010608010c0f090302040b06090603040302010e0d09030f0327230d080f070503 78
    0x7046c1c01600114940c5454556141d507604461001030030300c0c251401d500820204104010804100320310f1010902481c038100f054202c3d07641198800a026001010082c0c2c590300c0c1c03d01c5880c070b074950301144912079901d994031060059600280b521079031965480000c42c0c800e00c5808001d48200b41e421000c1402000d82c40020f00703484014000003442c848104c418014009042c058a6204490b040e00720b0303c541480c240b02200122035401600094034041c3e2841050340e0640103101a10b4041000b8084500720070412100d00c44005a5040040c0030101d0038801403409070008415542c3c02000c8500303140031200080d6140d4416a000c4015030341d1042411440c03c000e00860415003402d08100c7c440c24515140d00c042c00d0840003006040040710075100501002c040c80d00007070301601d070452414458682c203030007040961001e60300c00070183c48400304d10301d807a01c95000c2800369030010300c0c00d00f40110601c2405058024580c110349a00080c05040b60750303800410101880456001c0e000c4c2c80c41d1030714401 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 381853282 1250 381852032 381852047
    0x15242d1c0201020a110a0509010b0a081f090f14070503040606050906130507140c01150503011b050c0c060d0f0c08090606010c020609090a021e0a120504032706 70
    0x21424980356402800160381c0101d900c04015421000110240c1402c10005000300340a4021540c054205000230a00010b0f00c80501810010703515006000e49403000c803102c0c0300000211040000790156024092a0b845030414000c41001c4040441d020244181641c10403108640d000d001130000300400041c07044138041c0100406054030325007003900701000401e4400c400003094080450b19980800d1303606108007856144031980f2140c441c1c0b1b41c680442e41c0c0d4040c14214519141c0c1142d4035001203000c0c9810710582c2010700051803494120300025400f95410f4000103d00d080900034010506c40a03180d44004100c0709030603800001d5000c451020140480e0841c0e003121041000f0f2800300708401d01700092040e007201c401d080000301e44105100052903442031041c556003250240c1c0510a403c0c10700d8002d0a4000d0340342d440051143c2c45070743c0d04401402406a4070b00080c05c140710001e0018995400755070403a0103841c3c15050720013490903c3d02d40284072f05c55185411041102004240e074003002 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 381854532 1250 381853282 381853309
    0x91203030c031e09101d0f0f1e031608040f03110909010506010e060310210b0106020604050601031b0b12012306041814010303020a0515242d 62
    0xc04507110b0410140343c603a03036401c0195641049a8130196801814140300800c03540040200842d205441800c100b1510f40d023502e0b40302082841902441c040320f410f10319540c000e0b0300b80c410045040c040400400626180401c00945581070b04110202d80a20303080300c0d1a018601454810002c0da0f900002e001074414001c2c00905039034506400c0c0704031a81e100640c000421000c0351441e40f2515183e104001c5000181d0101030744030660000c016541e08280300c02c0506500130504402181c1c0e843c03200380d88808007101d00400a4001c81c1c01070002a003004c81c0c8802880f0a6011105401d4980500e1500369200412450303809110000401490600320003005400381088002140b00004001140e9180180d005401922540c0340c2d05c028014407540c840d07403050170f68803002d549951350790170007940300c0340d17001001e4400380103161580514181010080e801000701c050b40840c6441441426108820b0720f40509901c040c2d051018504480c031200104640070b1444103500241004a04001d0724058405 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 381855782 1250 381854532 381854581
    0x20a14031c0e100302040f060801030b0f01030f20060304060e070f05060714030d090f11010309080304031b150c0813030203090904080403021e0126010b091203030c03 73
    0x40150041ca0350100d0b03090080b04066665200d2040501c070150080d005070317042000b202091101c0042e0055114040c58102c0e030064a00100a896079124a002c089003400082d1038140c11295000020344110300458540b0407401036030b40c5060740c210002d0b000750300668042d078519848092400031120f050150800502906d83d17001019460000420098002c91a01524400b004025100d02d031900b03208a4404501c902000c000e890f405243c0764880980c1420b040e00d09000c081d80103e07240d4000d101e034642054004000c2421551255421540320790000003101000c0c10001c42c510005030415160040000d20b41004901400300382c6005001003401850441c8819001005602007500070044070f50102d000d41c0d00b2409641ea80c1000a50b0744140d900c02500300100440003041e1204500f510240140242d8600325250100b00988080300701d07c2c0501e4540c02c06080c0100180038600004041c0f49902500c20064040d4a2002c5402c58104865100c140180001000800d070404000f5161104124 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 381857032 1250 381855782 381855823
    0x110708073017070510090f03110105010f05060d0f0e0616050405100806060f0a0c0b0c07021e011809140612100203041a100609080f1018020a1403 64
    0x544440030315042c1c1d2900054228400a11102840740034440032509030700702c460600c0740307031800e1900008030040340d0130580014601d0362032211041010b000707290407a030040c801d0b01107840c142001c01c4103580c00181000d004995496013583d0400e42c601490004c8203085014100a241011507140c440500c1005101080410007080c44107944045600c1c10070311292502c25103030b0f5120804141c0c14403130034400c000308500128007813401136032264a41e1006032188000c041143c13104800d2100f980a4050025842801c0030524040704989401038071001c201458003d15211142e00303881010000c9410542c040354558a004800785a52049103030044000d40d80c0083e281c180c00e0b4002d4840d1000c001880c2d140c0d4001000c0740600c080764910100268503000b0b14a282d0034070009050b80420544507150203d003c1c4000003410702c001050b100c0e011f4a519000d814041021009507000307041000c600005441c0b0041c1a0025807202c1d00c041c0054803c408100c40700c015050704162a050007600c5c7c101148402 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 381858282 1250 381857032 381857129
    0x260601060e150a020f0a08032212110705150304050d1e03051018020306030105180d120f0501030b0919020109050d0c0e10092a11070807 60
    0x11982d503400941c02400c00d20f5110014254102e04281c01001028005c0c425500c200c0c0c14013842c40700650280c2c0c2620501603840494241004541e1030041011740703201c026a80708182c0c030740106125007280b400041a11021519000020004000c072804031461080210401082110402c801100080c5900b0940bc4502c7d02c40c01041929000c084c0d000c082544410204100d220310290790809807d04000d84020300083c0c11065009400840c2d01a2196007080b02003000c1800301010f200c51758200c2c0c800341041c2c2c00342000c10749101174404400e003081aa650035031140d51202c0c0c4611400781d4030500c0301510b9410700b03007501881c0500e4002c0210710100c45151b1400142e8009140000f190000e640b035180d08801c0b41843c446210883c0d1152a6040c01001040000340d101001c00b0156141c200081003c02c64030504107511404002d001d00e43c100f10710000d490400d0091b0070310880000d08000b100e051544468a850802815030b00c14482010070061008d420b245084020602d00c4000311408032404a = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 381859532 1250 381858282 381858289
    0x216050d0f080708040510050702040b0d020109090213050414060306071701060c1505090d110a1101110f0f06100509090d0302090a031707030215100311040204260601060e 75
    0x90861000785400341c0083d8038410000503005880c002d040080c544c80c0c85200d120703c06003141d4840001248968a018010110751802c2040c1e20130084d0107950310003500b8200548000207500141c2a4890000d090b0f0340007070b040e582c0740503c003002c0b440e044000c400360410105043c030302100134000e00d040c80030309000a800600300900c0f02d4110f401d246002d046100d55414000f40d200413101102800c1c1e401c20303080100400001500384407060310b950b10036072085800fa90140d280d0401a40c02844203140c858040d4040d0f114211000c1441d032941700390752181d41c030810845c0c9420b6618030a00100e800100c02c01840382e1182401030300504081e502c100c00c605d07225003110f40721602a10b1020038194085404215a140c1c8010040030759409626080c0503004001504c00c2a0400da808400610031501000ca8205582450030701034052111038440a5045559501c1c0703074103854080540040e4244400519031291000ca5031a0a10314040e1030145803c2d00d01e441d0070002c05030454028005113120b40c56950701c = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 381860782 1250 381859532 381859553
    0x3060412090b0a0e0d060906050412020c062d09091e0a020712030903030e0102040b03160207050a060f1e08150a0f090e07051005131a0f03071e0216050d 67
    0x180480e00345e40c2240369498240010300d07410742c000d054107113403400f04420042c13684a00c802d040d0580e001c8072070030300d2548100700c40c034803811109881d001d0100f42d00304c5a42d48216080d69203041001e070410b04004503c7c000c01c0e00031100300c4943cbc1c1c0c80c0101d81d81c1da00260403c1e07003180740c021102090035880e041c9140c40e4681400a0f900c070003000c140e075803082c510a151083d444040c106c42460000d42d034440d5140c1060010380c2080d01c00b4100e003000c0c882104d105c0350000418600319017001e825130100600d007140031b42c1c0e00807a940504061010004401c02c1285036a106c2c0e840001c59900e034501c03e4100543d050388080812441c4d2800796100000a000481c4003081e144100c4403100c078041b4620201e248490f05281d200e03031020b90807100e200c09103580c058001014119503588105905d01c96035a5500e290003d081c04800301320800030130085021001c4508000756405106410b03c0c5003241d41142d000740b400c5260549560050700710a0040b01c100c64014410700041404841c00a150080341c0c0701d900c3d206 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 381862032 1250 381860782 381860807
    0x110307140304120e130606110c0a030b040803070513060c05100908031906050a060504230907081f080d090603141807082a0d15021803060412090b0a 65
    0x40640004d044c1e0f650901c04245940700c0c6001440403d55402004d050141d0443c2d4040382c50041035100ca101c1c0c240030200c9000c40c3e0304101d0700903040e165511452415071010302013008100003003207488a006154080f0300018401a0744403940c1000c2405e0803400d180074904842c41040c2040c900c240231484040689400611004901d00001c800c03498400050a840e800180c2007200b0050001c1d1142e04240078108035035041c401d101c0401c42d420f0005407000c40e44501a030348104180702144045200c0c20700c0d260701a40e41d03550f50159080901006009001d140c0c028070450380007149101c400340d40222101c000f04a42e080c20b000851340c0e041d041b8031640d8010203580e9500203008808980c2c0304204a0100141454015581c242c3d510b06000051080700036441c06035094076844405031424540d0818038403d4001080300c40c40c151032400e140181d4400344002011040e8403400381d000c5e5500b4020320f40990b101d030040c80b220a014900180c22400703254440c0e1075604092180030000c42d00100c0004d4030303 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 381863282 1250 381862032 381862037
    0xc030f02122b090e0f0604050601022415030a0c08010b0d41060103050106050a1d1503010f0e071505030117030d020c160e0709030f050f0111030714030412 68
    0x5400b1034000301d0380000d09074804003c003030a4a0030b001402480d51800c3d40510350a45051095681e82001680d4442084900074144100b004a81401180d0f10b10b920b60040c0304465101c440b1069030700000d2a0400b418400c2c2c035040100c1c441040802c001b40f0407480d070088150ba100800650741c0d1a08e441800c0c610405001c1145500a05085d065101e002c1515400b405040349803020b11400304540c0c0c4401c24001100c1640c604007010071240750030200301c811110586003001088480350b2000780440005404070f0310b04010b0008420540e0b8080c0699090488920800a140443c0b050b00c0351822009510110034043c1d07961162500c5c59100e0110381c191440104ad0702d0300840c03031490b60783c40c61181c41141c0710721034400701e800143da090114421410020240140d681d26480307804407180d50109072502070200d1910b017010000100f2a424420446028005588400c154244804e003560f0f0508909034401c80300008200903140c000d80c5002c0c06042c085285825032401d41d44484081c1c03040e4403440207 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 381864532 1250 381863282 381863353
    0x106090903020303060f12032a03031303140f030115021006151205010e06010c0c051906030507080108030a0c020102010b03030a03090c0e010605030f0a0b12010204090c020a2a030c030f0212 83
    0x15207a40720105000c110b12704102d81c6d40303140850207a80c4490f0720142c00c03000568207410b4055804090b805650a1783c00c01e0004900d140d01c0c00800d040c22580a036014000d5005d94844402c94540c6032050000405400600381c45514031503a00034480c03109041455031032860080103000b88078500020550000c4282012007807150141401d103020303850f0b5400564855555030307100340281f41d2840d08901301d034465102484140c640c10400d5541040034000c0074416401400300340081c503c07460a405038140180000034200d080c4001184c10740c0d003c089a140826103a1440388100808011000300030306251403590000c0d4100b807001000344c88068441005500c3c00b03004210b228103182d12441c0e011000501481040b95005120f41c083d400501c12820903902e880c4407002e140740046144a039142d803000c0e514118840b148101c0d14194180700503004509403803500132002031388294502c00954003a45220000000510400c0554203d003d55502550004041206114118041d100e00c6908501c0c0002d17 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 381865782 1250 381864532 381864577
    0x2004030b0a02030c0409090c0905090105060f061e0d0b0a06020d08072a051507090807090f060e10031b03030815030c0d030503060a0f0b1207020106090903020303060f1203 75
    0x189800351b0342054000e0351a068400d030400c9041e680741822180f01503000d103d203a86400d00da60803504101c0b105a00311300b000c4103400983c908000181602c0d2103240c01101240b1040e001c2010035001604d40442d095903803059640e15203088080c08004140b244014103211701c1c43c50004018502c00351140c0c090240c4020001d51031052003c4804180c3e803081020000d40405003032140d910000001020b40350325074003010071001c40c800d00c00359003a554904000e007807c91511407004000e08000380c01080311503550740c0104d8010700900b003450103121030014440109056080050320307004039500070066005260400c00c0001d4100303000b00d90007940c190012030151344540c04a400e00100300d00b195445202c1003c0181099040300c040c5019080589a0900141d284c1c0c0321070000d89442d0064104d140703070a02281d0300344031361180b140740e01002d00d1002082ea1951503200c003060b9090324108402581001c0108030f41800c215000f8000040c4c100c9030b11464040c2c548559440344a01100201d880c00a45101d1 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 381867032 1250 381865782 381865801
    0x71208041104020a0f0e0306011a03090127031103090f010507060b04290a060c02120118081207020724020307080c160e04020136092004030b0a0203 65
    0x10741403010041c0007903540301c440000040141e810094030074041a90300820a00b00e050004006050b601c0810700b01f050b8003000480e202d49504014504012903490710460100071a90720380c24100842c0e06104100180c200d8a40900205403182e0450800d50040c0600400f5941d00310002d086010203080859456545042201c05008a15440345e0010306200d07280d072400b403000880690b0b41c482d160b03007005608140c00412100e07590510800300043c510050305409403410001090f50140070740300000d40c008041945001e102d4200c5019201420701040103c1c501c202c4901b6198000f001d4400b4060050500710b0302000c1c4d0b84560510703143e413080851056401402041158012508081c00c55161680b081c0e1413a51b540000c0310701c8000790380d02140000d103504a1111207006d10303416100e442d860840d01d00c4c03400305c10749005a50001c10000340303140c80305400d02280e204080c1c4550180403a03180507a00c900d8154a8200081c0608810100320410200d1600090140c0103080180c026a4a8550301f800 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 381868282 1250 381867032 381867053
    0x601030f03200d030c0302030402030303040204241e05090f011505090405010b0a0f020a15020d1404051606020f06010b0a0302130801021e091f021906061a07120804 72
    0x681001040b4a4100690002c0000741440c28501d03030703070b410300801e8462102101a8001607c1c0250541e0050010070010700c2c1c00d810004024020080004065404107140340c2480c015503c484218802c0002d628800d10003103c1c1900070744015900300d9107906142ca410400c00c0e00512801c410100200d150002041c42502100c40c4404010400d0107503584400706003009501c41c0601d03001140744a032485207018000b1403040c150a4128041c0d031410724110540c0c0000e580220101121184e85001c9083c100c0140103649000380d000c0c20003080b144842c50010ba1980740310350001402d544c05049421a2803400051440c152080800c2040d1601020181a400303800355040444030071500341c00104a1040540c00340103909100d203480403040e052424455031030710071056130030741104240d51000c0701e51a4014a00485d284035204682c8941101510b0b4103c00030406c1084030484d46074a4204075a43e0818190600544116101d40c500001c5940307020407482d100c031140c2c00b44280c2c01d00040034004070320603 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 381869532 1250 381868282 381868307
    0x6060f140415081e060106021c0f0918020309010e3f0403150506040603020f041e0f1409060705032a040609261f0603021905011101020307020601030f03 67
    0x104c8101c803200d4a0b15a0b544ca20910340e8071011310915000007106440080c41d0f051440e084120225142c411190454603c40030140e080c080c007010500c009000c500c648445046440c03144170058403800d0041849081d9403040c409002d840e441407106404c200380c040074000848241200c41c6000c0f4013188060b001c000c44074408800a08000718000092002e84105d01443d0b00c00c504c0200455580d0408001c101c404502029410101c120080206c500b81640007910f030700b0f0070380003820003ca00800800c0980340c07490b40c000149a115100d11a0b01e41d0200d48554124128001800d01c07031030805c40041c12400b00420740070907921003c032111244d4207001d17500c10316100c0010310a680c443e1a142e01601d1184603100343c04843d5128001c030103130318016007110401c1e049458040d211000d00318404c1001d03010203a40d1503200d02c1d03a402d000401681c5640d066855084110500d44400340f520002402035005855040c1c4582d0040040080c015804a000350550341e10022400003803c02c1d00303080342e00390550f00 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 381870782 1250 381869532 381869549
    0x11808060403020606010908060f0a050405010e010c0509010e240901140c1608060402010c06020310050604150905061333090e06121002033106060f140415 68
    0x703000a050303001c2401d0b8410f120a0305c8601041c0e50700c0508a6481c07104844841078100c00e04003080c080d84030b517001550014025000414a8001c44059601710340038005034001050001802c10794650304400604604401218008044801c4100004000c0042e0011000c02c200005d650384880e800381c2c0380840d4171400c201e0160345802c94447c215503556800d81d01c2c1d8811000200000900f480c00142580c03040341c1c180d44140728000181d07a100043d4101a01144100707150104c00b0031140c8070000544010aa406006900001d440d5000741644030035030800c5010780c100700201e61000300c050503d0011520b1030341d200300d030881c1c44806803903541c01c0001d80c51860010290004001d150300000a50a481050a45020726201d800400008441c280c209455903001052a03280a1042d0f070b02951b4006641500c0340b515502104a10889610246541003c0c40c0084140300c00d1104920521000c1c00c15a2114200039080003421400c18191950782845640c4403501222f2480d0240b41920003400004c = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 381872032 1250 381870782 381870793
    0x30206212a09030d080601020c0310021b060705071502040306050c090f300c0405040302070e010b0403020d080d0603020a0f0e0609010e01031407180504061503030509011808 76
    0x2a540281c103103122103028031450840e908030402210360401180c0d09458014003c00c0b0311000c0c06400c1e590944000c200c0c6041d409000401076103500c05018002c9040380035600165543e490980d4035100720700704400d00c1c034540c0c0b1280810140c02e0700f00003111071958100c511303a41c800740400c180d031000e4840c07038000030101400d1009001249014a01415004d1401c4a082c4101d50b1988280304098610003035160459007040f076000010080034100441b54422281503030820795051000c141951410359003180103a00015040004d07038909500203000d09541620a40b070305182d900080d00300c40a1a00250051000080560149800307030b00003401980c0c040c100e41821075a9480e1015000d4280c80f070110010905400a41c040c6401c00c0554141c600b00848407130309908540f00c07007a2181104d00c5a003a80d101d1110045510041a405100d81c09506140800d481ca000e1609500380c80042d9108490808c1c0d402c0c00f400000d8100302604c3e100300b001e20b000d00d16003c070b4521010881543c1e43c80510b250040 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 381873282 1250 381872032 381872041
    0x1a1e090a320f150a1404230a1104120b10080f0709050c130608071409060703030e2811030102070c09050a060e0c040302190605031b07021210150503030403020621 71
    0x25100900a507900896040080c041161a0b0003643d102c280740d02089030887e00c001a411501c00e9021500e0342c1001c0694906240d107404100078030000312182a11905039180030042c10005e841102c50103446c80c5009000d002c0b241c0f0a00b10768070207003030184c000c41036101d03000220114050800d90b00c0c08608010039540c00e80d0ba415000d0101c510a451400000701034410141503800c00d1011079000010240109207801a1510b086004046000d000181d500501101141e503600005003d810444014060f0341d03052403903d401f01106002c1c0d2111402640184007000c0811080c43c080411034241c4030000c54281c0d0741810140041185400108001904800303001c009034983e00580107a030300c20f403070000c0d00a0290f414804d104030188110400185c0400c00259100750b8820800c5403403190740c0301181024026800185c2d4501e01d802d079031030141c1c0400c000400786652801990500f414041040603d0307030912000c682c482c0b066010190007a440091886614541c81d142c01100e0301c118407130b6030324a082 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 381874532 1250 381873282 381873299
    0xc080706230a060504020921070e0c0306030705010804080306150f070c0e0703060806191b0e0f0111071a070b0c04030311011a1e090a320f150a 63
    0x5056a0702d0744410310b0701d58003180070b041500c00c54210890003089046e83d000b8414410b108050030980d43c0803a4066401c0010300c2e00040300c03034513015900748581c090700c07403802c0750030b06151111582c403a83c1001600030034080414013500132a600440c4c1038030349582ca00c807000e50304200380c80f1f070110360440c889001904005200a401c1c640003602d1181202d0720440d220500f046041c0c071250b00a201d016000ba002081801d20140c541c1000c250f0081d43c08580b010340e402107d09209010f00e20540819010354013a040d82c034004d65102492082400c28034003500529480c0ea943d080705002d802c800310100509041c615017024151103805521400d81c542900d04144810980d8100b80310440c0410b04030030303070041d003d01c040c050b100e22000002c4134540300340c01d402c0c20000c0c4252001d40d907100d00c50407000780318000d40750030204034483c4510840119550784080088215074903030703420000c820860030341ea81a545600e045031581103100039000c0d0509844003410198000391540c400399002140c1c9000155003030 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 381875782 1250 381874532 381874601
    0x71202011d0f060f0105011e0c060c09080d030603051b0f030303070201090b16021f020702030f011a041103180f061608010605090d1e08040906030615060c080706 71
    0x20001800c1d40c0f15510340f04c2c080c042d960400c0c02600e000c254202054030456084d406100003000c1f903403401c00c41c607500540f0380508840c410a01d140006051389810303c0094070070440c3d00c1d984003031351400b00f00917440c0d40c03510fa44a00350460700045403103144034110304c150780d805006003418038014103a030350701c1c1817140c402b0b802001c2c8140c0445d620107a402c00034440c3d2807550507960400b40f003a00904912800c51340c22110b5084405503001c071040d401d1000c0c2d00561170801c150604030030030301c2c0001080e4416008072504401d000403107502c15403e00c502d180c00c00c148501940e4101100640c0e1002d41001d20756014106406201380e0350961054000308030320051030700c001c1c410070500c586440420340d03242d0104807200c0c401d460a03540c1100480007803000103a10b92440b440c803071010100c081071900f000c1d03440c024030341d0207540b0961059131510780070310510003540320fa01000c82c0d0318510101d240c0e1030004050103200c200d000240050801080903004d0040e1038110140c0904920a08105011030468118203c1c = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 381877032 1250 381875782 381875803
    0xd050f01050f0d0b070c030c050607020607080105060403020109091503052b031a010c0203070f090f110309060721020301030f0c1e03060f18030c110a0b071202011d 72
    0xc0c00e194280b003440c3d081a885562041d5001492212256581007060303ca45400d4902101017001845a840100750180182070191280c0d81c0600810308219200800d0303464180c20861060340d04000400042c1e03080781e0f4100441d0b01c1e614000c00d40c46491503040f1486c40c0c84e0341c00500f66025000304900c4810042c200c015020529641d002800d044061040341105c0c2d5140d00c1564541c9800700000b42c1e9802200c0c401b800740d200800b194107940c1c444c4240701c1048020344c4030a107041d8481100300f40c4883d05000754911807000701c00c00c0d42180382c0a0900e5a403a400a090724003444030758200441c00c8080c200c600c01101014100c00d540c0e95079286000100e030380a455040e29160039031503020852247d46580d204001c40c00301e81225070a800c40d16803200401c040ca403079288070f5588044104042c250b40d100c48102d0b501a8840219041d00c50600c4404c00f10002d22262251842d10b01c188543d252100a4502c40e540280a043c440c60080d00280c0c0180500568070034410050001011003c2000800c54140c = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 381878282 1250 381877032 381877039
    0x1020c030f030109050a051909050a051e07080a0c060f09050405100611120d24080309031b0a060309020f090f06040b060315060a090e010303030203040606080a1104020f0d050f0105 79
    0x140c0c1e9622002c5080794004c0c0d03144230700c1c2c1c4000c0c5090081c1005030f81040d200039000d001640e60190700765969030b1410b5a1040c0200301d1248410140400e00024403000008100500103411140910790304c494030401a0300038034041c004100070007181d0a10403020305010b410094403c1140b4240045210000340300e91180200152071404d40d203a050308089a42e03840505450300c5242422000707000d04000e045013641c100f08041100c070410000100004200340106580000386580d15012024075043c881010114003008143e00846800c030b444000e01a000c4569038074001038481e07a2031001600360024000c2c0c05612180c2401403002d100710414115001d51022a001c0203220ba00d40c0c02c0c000140800c03685d50035483c1440b100800682400c0c0000d028a111034035044004689940c040c44003508e080c0c00550002c1d60100c00c100402074248100400780040703c00901c000c00040c1d50f030038145000603490500854020400c0041c240f00e000540d8100a400c00043c00680703852421620602e1091203036034030 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 381879532 1250 381878282 381878291
    0x13180624050102010e060f0c070b0103080705010c0903170307140d0b040f090c03080702041107080a020105010509191d0703030c1a010506040b0307020a1205030a0615120b0301020c030f030109 84
    0x1d041d80148580301040700800042c20041d510090029400c550041032844501030030000c450000c1d032490304040c00703544204a140d84034000c5052450844808140041c1440140ca50034130100728038220b03105035640402c5070640d50b07654141040f150541d40003c06400d1050101d165000d080e481d030001d003164442550700b0094181600e450301c0c1540c80d43c031006420000018001c0c800724100345e008029240c0050004648419030704d8450400e94400c600c151200340303002c50398455a503420b0050714010182203c07010003500b85481080750700000800c1d0130000d1075031100d4203000c1c2240008600706003588030060f140040d607641406012185c00c42da08541c0c0046034100407030a024404c1c0d019050301e0b07000c1c1c0843d050a040c5801d031403144d80041c005600f0b500c201310109001034a5041c1013210304586070340d00c9071241000580142510301d0354101e004200501001c2c40003c59000101041e85a01c00902103211030820020a00a104e00e91181360307903010019a00b00300b8030110f401035040311080c000401 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 381880782 1250 381879532 381879539
    0x31b060b010e03031905030402041d06070e030a0308070e13110a1202041413090c0f15090b0f180d03030c020f01110a050d0f0614040605010e13180624 66
    0x40c1c4174030428206030410400c0c034450700b540c00d1051019561152000e030000802d001c201c0c6444a408403100243d0b11182d000b0b100700080154800018480003406500400d50000160780140c40c900000b03040104101c4280c2c04514640c0d204604010200d0b090f26003040f0b004110b1100c5066a8000082200070618540d00700d20444083e10840e422a071219003100d403100354072010000c4032241c044440010546840c0c109000c681c0f00141f00008010440104080c1450a0309041c18100a82d03103050030300c00001c4041000a00c140125803890803da83c410340e440034201c011043d0b44099144482d041071030882c0b25020035415074006048001c05408480b14845640c24103403d0316416900c0e40203044007030202c4a0454041c50140940701c00d60b1501045003542c41030100c0c11900980d0001d035800c544400221560700303061140801510302071030300005829004001c16a03610080300c80301c40b000c0e981c5a044c4201100c0c42a5400c00562080c0c0911441c08000c0700e02520310b2000311820044103c011000 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 381882032 1250 381880782 381880789
    0x3309121533050d02010f0212030a0501060306060813140f06090109141209220f0b0901060c1110030209030307060f11030f150f0310052a1204031b060b010e 68
    0x18044941c001c3c60041801c40c1d5a00441d140c0365508040300a5200d40280306000e0340001014603c01c945400c00020305600d084002410b0311040e521200a1014070001e100910345c500c2440020349401c010000d6403500d503420700740d01d0100031814140c51402a141400000c41064002d203003114090b004540200b804a01d0098444480b01c05102510904100d202d02900308036010b290406880c11a518028550b001e86805480614288905050759154443c5d03440c5002808070b400340c542850701c29418541d80d6141c1e11041c03050b403401440340410b060010b410902c642c04075103403c1009425243c441d882450158080c180d404140540242402d0012000c0720524095030722590440c42000c80a8440c0400d01e01040e00c540007140d000190300c0c195040c030362002c000001010107074a000280754944260101140c5600c1c801112000c004907410782050a050801d81c0e401c805184082d80294440c1d1405407149a01d50030035800d02610b80c3e10740c030705002c0540e000d08500e0b4400c3c0c84a840d201516000c0 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 381883282 1250 381882032 381882131
    0x4060e0f0318010306030c060215070305071b020d0c03080309120901050d050403020a2a080313051c0204090f020102150405030d09031833091215 64
    0x640310340d4024071001403440b02001a2060902c010b04001071456101d0301c44074a00c0d0625000310026900c01000445d1801120a00c0c50744841a8502003201d4104100002c05094141c0011002d00e03905504c1c40003559100c0328082c06503940400350300310b01c03035807440d040850750800c40391042035000b455420710404911034101d0769221016590f55190410800c9004000e02d0068002d0f8210f10881e00403600182c0700c01403440d00c1d016802c000003017140d034882554140c1402500040c059400038040344449600c0d60f410740d0140c03507084410f1a41207194000d0f0711440511010060340c450b0408207284140000310b0000c4034004e0003a4260b070003580240c0c4112000035400c0e10020001d6100304050f04128a1a92107204014403e290240d210310340075180b0b288010594109100b510307810300d0480c0030100604031680d690070188501901c101400c810103005000d00344101e407100c4250110f0241006280d509140e0594040e10042001080c0c07105440c9144500c1c8030030740b0318070340040710042e03403a50840503 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 381884532 1250 381883282 381883303
    0xc011e261023150c0a02090103081314030304060c14010204061206060c021f0309021306090b1503150402040b0c0706090909050a0204090515010e09150c2713020304060e 74
    0x1010b0301e283c42503610146903100100d400014028800301c02e0044c0d950004403402503014906560b1a50210380004164018551020444d0011084151140d440100c2642c080ba04142010780d6262004d05160b06140d000680d000b400794400100802c0741c41c0c01103011000c0b2071004804001603030325004161405051030001941c095840e46400c000e2041100b82410380021900d0046080d1100340d000c50b02c041d1484008008103a1105002c1c40722070810320580303506080c100c80c40700d0f121001400084031072001414804060030b01005180b03044c1c8a50701124014095200d503aa0f590380203041076502c441c1140501d10001e01c0c2c01d8400a02c072446402070100c11a04400a0000c58055a08100c0185542241141c09006244d0403403404115440b040c2c0c002d10b100d26101140345805400035040c0b038191800303080350102003c2031000007210270040e190040d011403078030300f070381010041006c08002d00301e6640c55002c401440b0803140ca032855009180100c2c03041c4003d110007000b104440351214940304 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 381885782 1250 381884532 381884539
    0xb04081c0507021903050f0a110c04060303120b01090b0f07060b0402033702040f06030c08070504050f0d0b0a0c090803191d090a09050c011e261023 65
    0x110b4504c0701c0040c850300c0c0d0341552181c1001d07850480310708811081600441e45520104658000c1c04520803824000d0310301c0180100c0b0204190b40c21070750701a007017282c40c502c0c14040c20355458110b01c0c0b03070740a04500c802034458498040e403185400c220b80c2840e94003803103007220200c1c140150409242464020b80e40150360580c4111070000b0240b1258070b440c48101000100c0c40707507221100032440301c144000c20142c8039190011100303e090401c0581500c0c038054003401040407040410a080f540700c0182c6c0d0541d101101c40c0900b264906001a02c009605d200141021b4102800e1208486c0c4030b500482c0d0814003030700c44440c42c0f076131405140cad00ca00600b4980040c80420780b07120010784d4454510404100200c40000c040c43d00040c0c080362104d2800c88460b10300b01d598458000c01d0040c02c022000b0001024a090384c20000b001c243c0c0c00141075402d022074180640769410400e84c070364030043c0018044940c0011441c929101f60790140c03440ca00e20a00412a031801c04a04401410400314604500042c = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 381887032 1250 381885782 381885793
    0x4120c0309050411120106050a1805010c060c1e020102090a0f050303220b070303050a06052d01021911010807080103082502040e16050303090a030b04030c0b04081c050702 75
    0x150903c0b01800b00c2d03400074000044100f007500e1041c821440b4490182040f590f0b115220300c540301014203081c41004480c0140d403ca000c003000079a0b88088032410076544500c01088030120b00e281a03075080078110220145030201d4009600c920f6055028044460048800694484d41d44608003030140c1580116905500308205145d5040d60300c0b600d001010301721840088485070740ea48800c40070703004003e08800080c0c552003409403000b101c0c040c0c031002d000201d494164205480001d20b03024409031212403c13006010595282c2a80240304400301d403611010301c02c4040b8004d00c0c01e80c1010b0080c0803d075011032098404500c00c24441c0d4502c6050300d0b400070b4664500404c0b10110b00101e0388001b03448182c2d00381c000d003400041c0c546024401901002c900101030601c69402c0003011111a900818040d0f072083c400518160749010000040784e070849010040c0c0c0c0c49905044682ca160440054141e6032110284403c00600f41300400004034038890955240c0e5202a019042e10310645103480161f000 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 381888282 1250 381887032 381887039
    0x912050405030a06090f050709092001392102030708040603050903091008090c31020904020f0307020111070b04080c0a171c020403050d140403020d060504120c0309 72
    0x1680c400240c0d28006c0750000215006035540c1032502d40c594004803005a160110f100800c4907510312410030840c4203410084145030b82d00020b00c4038544079a0134400007400d40200c00001205156030b810800d40344100f1400d0b034018100310003401c00d0341e0050041408581c0700021a90f00c04810396a1195204402c20302e030500d8103104501428000c0c0402c0001d001c00c00c43c40442c0c0d9102030300d00c02c51400980f03c10940f4a0045200b505090190703032b849000305107410100040071089128856001c582d0019000384100312013405000703020714500a0340252001070218030241e2001c01843c0b090100d68000d001e0221005c68054950180b08401080c0d010354101040c000780e0700d08050000601044210341c085e100301e803204103056034007140c1260b0380280003c01c3c1d07404e202200d5503080d001c01e00704025481c103031640d0380307942d500d80c1a1300c1e40702c003009248a0310000004001044034019034000380700204420640c18030000809082ea0220791881c0707012502c1e41100d0048004188464144d21035400b120f15 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 381889532 1250 381888282 381888293
    0x1120c05040510031e050106020f0a05060106120f0e06010e0106050705190f0b2a12220c09141312031814060f0106080c030105011d040207060912050405030a 69
    0x195015503030a054030f0f0500512680703a059081e058a9040c000049140c1d4034010012b07091880c40d00d011102c82c1c01000ea0180410400640d00d8112000c9182c0a06809418100750006044000703d6510032821300b60280c406150010703006051f900d005129030703a40e9a907400c050b2028070403074000904a070484c8088030800c0f03019450350b00640f40581c03d404034041c15a560b0700300088040f940b15008080da00c94644108141040c0c41504820f000c011a25080c2c1c4c1548042000700014114419402d4401801011100f07401601004543c0040c55802d000e0701c0750a940d028002a0040c80e20141140700000c5c1051508000740f41090b821807825404000000c408801825980300c1400c819180a04500005070040c0441c0c000303095402c0140507582840718401e002c441c03043e0b000c001042009414052841d59500449044270070909008049a5400d40900e18071082c1c2801e940d030040c4081030510600140b0307009001c40c1c500c1030302c041030741c000c401000307540c2400fa90141d50f41640c02041d10200144 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 381890782 1250 381889532 381889549
    0x70e070207081b01210501290d09020a030f0803010509160e0405180d020c0907020d1704020d08120928020105070501060803031810060e070507030e03030307020c01120c050405 77
    0x50f061529018101000c00d0701d0f00d80c1c0c0310314103100c0b86017551140100202da048e016a60505240702a0b42d140d9444250310041d40384c082e5405d0080b80560303500b05841103549501450000310b9001044005a400703e05040e62960024401c141c002c40075a00000c3c00085042e8407241786802545601c40d50300702c1d1034141f00040c60024012107001110f8030b00444440300400610401030150307801064801506400d2011258016102d0030079540501c0b200d042098106a494001c2c4140c100e203402e03269503600028040391104c100240a1280020f00886c144940d001c140e48241400b01c2165107a4400960840101c580f00c801010700507898003030280190301c240000e0191a02450011541644501e09541568410303601207034415a6281d005000d0b1800b03100c0080c5003004104100415458801045140780c0010034003001c200f0005035060825000302c2d21508903000203000c03a516881c0c0960007039540c6801d500050302080c441e101c0600d00e80e1050081c00749124040c0d6820b810a40303042c05000c500d5 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 381892032 1250 381890782 381890833
    0x503090a0804080a0501062903070212160209060d03021c0302040b0d060501090803040b09091e0c04090e0c031e0a062c061506090a0b0c070e07020708 66
    0x5004004400001c2003251010300080c00030366000c0c00d1482e8440c5803103421990310b075106244074445003010032003842c5035480c0001c1801c941040c49075643c1e5807503000c03030a01c0d002040d8640ca40501060005270b5130070309a070b4220814803d03540a00c43d030b03c441040010300045500c009006a10801c0400340068840340d910100c03962038103016003025220451175440303403c10008501340a0341c0f02420021917034000c02c104014000304016500e810b040c11202c4603181320b2003c15501800825001c50002000700c0c00401e0040700d25400302e122030500611b554081da100e4400e0421045c244204d01c0032005001c66682c034280d05c003d0040294401c81c20b0750161540c80b100c5880c50a010344112040800c0441c040c16219100002c00d004c02080c920b0769481c1900c0c1c000c0700e80240c681c448010040301224203162864500400c44825072104480e5001440642c0260408081b0500c00b0801d000803100004038402500c01c0c1215690003991036000403a6604410310610020303500003100310207040007814024604 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 381893282 1250 381892032 381892051
    0xa1707060f0c0204330b0301050405040201090302030102070c080c0301060509010e0a09170307180308090d06020405031203040210031e0f1d0d0206010501180302091515040603200a0503 81
    0x90200300e400260840c1c9543c061041e2800c0b000d01021161560b400c50064107448200d05e158105043c1040b014460105008260045640d00d01260540e8002c100c01c0000310360090095640305a90325110044080034032440200740b0400180c80c00074541070007100c0542e100a0036400281c0e190410411680703c000c0c0c54140c500755549080390108a811039840c82801144032101d9403401c02d40c000801c40b000e400000d0b0b800d040c0100d010300000e43d001c1d0449080020480f01400f01500d1070805000a1082c0c0c0d00c0544e062140042e9480e070301380000061445140219007241c0c0c0030a01303c0ccc0540542c0d040c911001c001d18698503200760340382c880343d218590080360088001120112664000c0b18400c003440c03003100b5903001c00802903000f5410883c00c0d002d00800c0c6000c0b0000550448020040401c2d030200921078804040043d040740300c28504078011660050040c400003030303420840300c40d0358003030300030380d4000b81c2001d24100304d00646101e0001c264094509151501d50964001c6916030000f0f0441b85a = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 381894532 1250 381893282 381893297
    0xb04060905010513052e03030f08010b040b0901111c1404080309060310091401090c0f0905011101020f030a0203061f0f0c050f060f10090501050d080a180b090a1707060f 74
    0x46c00d00c10342c040e044002c440c003440007211070950801810749001c1031b6020041120107c01840020130800030343d8119003624414548881c541d40060f03518151b4204440c0543c8150070008510080802007080e0b914010703100d9415006090300c041109108500441c0e060b50320400410603d0706040c0001c5034000b02c030411145074140c0725481d0b042a1070f06048483c51240c02c00300188814020340c800d0040010f010305000c010410b8018010f880c02040c0e00c1064180800700c0601401100290101c4594524000d1240c1d45c0303103002503252009410030349400d80680d040e041d0b0703c0b04075054030381d0380c002d101c03c0c5440340114120b000784100c500c2c006000d011a15406841d5001d010340d002046000e0080c000c00280e4130f418030300359900280944050380f1281e031260408004000a0311806111510150881c624030351300c0c190080f0640d40c0308921880c807810b00b41004000a0200540e10140803002000c9408404c0140e4a280e248050030300242c20390450780149038200041409415103180740c801a003007102 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 381895782 1250 381894532 381894571
    0x30703052508011e050a0902030a030e040f0e2d031806040312020f0607020a080904020a050c030a17070903080904050603010e161502150a0507020316060b0406090501051305 76
    0x2801d4400d100303e107441000d000d002100036085540a441d5126606d09010003074490b580d00069034400c4e5130307403014060005044d0b4202c5d807621607802c8030241204001d028405610380c03980c1c1c946d071950342280651141c041190f005218407440c1c1440c22864101100641c1401424a00401010001d55246500c0a0708000000002d1a285464003146c0400c2c0c0240210f0301c0103411090506074003e11200464001c001d003000014200010740e05082d8003078074016140c1d1000e8605071906c0c41040031442c2280320115030003203100d500c03540c3c03901d0700341c0007883d00b01541c0c4600c00190f44004c418000140304e00001d204486032802c080d405154004030003030012400c1c1c3c0b50703a5136a42c00d01c0400d0b40c1301e1001d643c0354030040c060100c4000c80c3d90300400c00e510003040d150440028141d400140900000d40d00d548070300c00300340c20504c20816204e000e043d081d00c1c010100c1c024a0010028607a00b0300440c080d6003044000110303d6500d10555040300d101505903141c6500400114004020091650b001071805241c80c5 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 381897032 1250 381895782 381895799
    0x1b0f07020405150910061407110918070e011419030209010b041d010305060f0a0e072408190c0201090c030807140a0809120c031213050307030525 64
    0x10f005001480607140c0d800200400c0c040944001080b520900300985400c21115074001503040c0d041404506044c1c0754070242c030344070945140300880c6607030090104050080c4440016511042c4036880e4044031170455a55803030802c481000d104881500c1f940e2600c5110509042103e00306c2104440340800c9050f81b0f0b070b40043d80b106c1080c1c001140c00d030f00c041828094400d114005052510b50704c000c8800c990325550b216555450000c043c100c4244040c00405e04138101608207072010900002030360042529550104024800c03540f241040d0300b072007201c03101c0f145e014124441c016030441340070b00708c48500c5050034030251100f421100119903071003804d14085040c65022038040e511400d20965a04164145450140f0000c0c2c00b28034a9088106000e000a00304411600302038006c0d5608507030310342140c0000b410a02c403408840d805005000b00242d05120a50040c0b200c032220010b000501511001415640e60150000810741e81c0164a100303845080b5103813005a400305860344003030041e25079101 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 381898282 1250 381897032 381897041
    0x50f0f0f060109171608100609090c03060908070f050606010e040c171806040f050d09060c170f030702010903031b0206043e03060109050f0a090201200604020a0e1b0f070204 76
    0x8503610342200e1411f4035443c019019010003040e204005008400050312140014a5184401040160703a10015420400450192024282c010b4500e24061419040494807a801101c3c441c4c0001d4141042120514081c8030301c4203648002c2c1e5511403450b200720f00d004141c6034044c00350040101c02c15655140d1243c10008180300f18840c4c41c5c030703195802991601301d2416181d580303800d091014040c000d0107445e500840e22075126412028003451000440900e017007610401c6a403444070700c0000708000c2059015048030040b00e220707503010080e50360994914807140e2840000310300181c108102040114505c0c0105111080d4a0050000380c10000d40091459a0b40000c01c0081561941d40e45042c0e0301c1c007030006a00420f96400240910318142c005010758110041092500b03030398452180065912410000120340c452200441e1118241a81103039a0402220300f00d128014071b920100d0110707000343d00d59000e0040c64490303410070b80c107444074001d4a07003000003018034189040c170032900035071b4640c0503 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 381899532 1250 381898282 381898289
    0x10e1311040f240f05040317130b041208090f030d0f080606031003032609011a0f09070c051f0b030d0201063501050f0f0f0601091716 59
    0x3009541c0d1407402e00c944400149a5104881022400e000e81110308400c1e003803418240c0c0c0da458840c0d540c003031000041d2a1801250400b801c4040c040483c46035148404004284100c03603030030360400050340e45049141c54411806000e1034200c1c0300301041c000549600c09415240e20050110443c0401e41010034902541504c0080018100188200c680c5402c6511580c000e103041d18510310707624107070f40d5200c100c5949201c001c0402c550348840000c0e000e094511001d240004000b003010605250518901926005011800b912521080004541ba01b01401c0ba488100606074034841d9440c40f90a036810302da5184262064010380ca895465036150750f403241c10601c80d18000040c10700c480028140b604d801c6284800a40e8900704090002d01c08000200074400070200210900044001c1a41005401710075082015800c0c0028000d191508881e042e2050340d42040d0581140d032090016010280150b51490124180704030900659180000c9408000d5802007125071003120943c403000e84440d240d1 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 381900782 1250 381899532 381899561
    0xa0605090d143403031403180601080f0708070302211207050312090d02071404090f05060406140f07050304030c0b0f01050913080306062101090207110907020309010e13 74
    0x5040810f030b60951207080040071140401c40748182150b5000e0446c50403001e1444c00c5500102c0042c043c81144007204980310b6441054808551396540d98035a1000d500c40c00d00719070300070010003203001c602c000b401c401181d070001c01407456a407a03106d002160007001e1a900c9814090a8414070126225a0050010b54410760095507150a14295070031a80c0028003c00903940110403030100360f550000300501658441d940c00c0d01004070903c0018010034503890020209038105018a088c04000f1070a80d12982c0204000d001d40c04540500c41d890007800c98a001007001d0400c0414483c92190018645c050710900b8008080320a0340c40c1c0307400d566411100c0c065455002d074014495414400d001c240c000754420144d1200e01400e42e00c0050720702008000034019400070400440f25880d14010a11012074140100c0c1e9550b10790301e81d24080c3d40300c45010348602100c0f1600d8281800c000b0a002d02c120300560285061509000045440c40102c2240550107056441d160742c1045003486450841032804 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 381902032 1250 381900782 381900823
    0x50a030b01090605010c02210f0a0b04050709060f03030503150d05030309070504020307050414060d05010308040e09030f070b060414070c0b09030901090e0705071e02030c0a0605090d14 81
    0x103001c903000c1c0c42e81c58201031704202c6807003984001600c4410310980c00021058207060428404c004551078030320348010112881c460800038034248100c0320340f203501840c0140195081031b0f840d0303500b500a03900c040c031620154884402003040031030300c00e40265070080c0803c1d141c1e58200e1406000114121103135481914182c00c00020302c100ca5408000314401040300707440035800d51030300c50009051030040c0d01c01c0e41401440003159805d541c2c0e0b10811500c100c04040c004205550b16801c2c4401c1c290014054450166914004544071980000555194907286105689070a00340ea8600d10140c0c1c0180c581600305444100d0741e40d440d04d51031603040c85801c1030396507800d0101076820030004200c2e001d0050320454004203c44a41c90f6400107490741642c040c116100490f84032480110340c0b034403810310050034100b50b1629481494040080e0040004d0080342150441030b070700803c20465649911403030010070010024442141494510000314601a686103100c0003000805d490500c00c4800c0c038080a480304 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 381903282 1250 381902032 381902039
    0x5040b041d0a2d0b03010f09050613020307150c050f0d09050d0b04021c0b070c12022d010b0303160209011703090103050a0f180203011b1e0306050a030b01 68
    0x5061a06521240292080c40410981c01482e61083c0701c440751007031038402031082403071400142e40181515000c064001c00142809034610802850f0b5620200d81c03031701a4402054082c07114940740308556400a01825007103140a80700764280c1490703030151091100c207494142c0416024861800901044000350050004260008000d08095000302d88a030310071540326404103425200381070b4020f9060716603001c400e001e100310140c50000000018610307030840e010088555800201c90b0081c6101d00b01040c100c2c08204400d030f0b2901d103a1b1064108400c1d986d44107680000c1c1000c103041c6203640200000805074a5200400d003507603c0914000c5000414607901c400b181403078801c0c64018a01180180c422498800d4802e031070b03100e1a0280c2d4105a12000400c65000f00c6900284c500000410100300502c40100404119410608140e200e546040c10b229410107641030403401c1c02c0f03c01c1d030310300070360b0285580c0140c890444d218007207007015943c502c04126030700d583c00d201000c2d50242c440b0800c00d614 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 381904532 1250 381903282 381903329
    0x3080a081909050309190506070602040807090b090a090809060705010228051204170c0a02210c1309051501090b03010603020f0607170307210e0303041205040b04 71
    0x1050000740024910b804508404250302106851100500303e8240701e40d50303200c0540c00c040c5041070b002150b2107540000c0000401034598001c200f10b0743c5480944001c941c0c0c030f4071520f086031a82d20000d41c00c03600c1d03400001c5c0014965809607440500c941100c90a000c4203002241d00f0381c01584084600da03500260b40c01c003889610507007102c807440114461603140c120340c00c018818099080c040520800301e0004c60104002142c600c0c1040310010407a6403942d15487c541030b03594034140010f034081d400c258682038082c0e80c1c00200c4c0c11030681d20401401821950b005000c043e0520301c0401212982d92020140020801d0081010781c000e0441c002002c0e5041c8140901100c02c0140e0582c880d038900356007000140c444240c184152201100c0e13007a00c421042c03e00b400d0050070514025640880003040000c00e41e08901100e50040d20481c500310841c0b800361314082103030300809103180d0302d6000b070001400140440d892805040c2e03551030054105a556114005990080d41001e100c020203403000c03108544 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 381905782 1250 381904532 381904561
    0x100f02070507050307030f080c030c0a080403061d2a090103030305100914060108060409120206011a130306051905090706030509010c090501050c03071a150d08190903080a08 76
    0x1000710b000d003071950728650741c40f8001c05403100020302060b40400c0384005801b060069407d42f9681d903085d1441c1c4446850415605d51160000b1030302145006501111007400c1c000701024a410300005100101d5078440c4042002102c20f510040f0b07002421403082a07445410445008621903240406c02c0e05110706008001c83c1c040d0411600903240480402050480b41c070500c1d0440c0007800d164032282c960402081c042c160885000d40000c80550817480352aa001880b581215121402c104101e044090041c2584c4100790761010040ca82c140b040c0701089050340015000200c503424000d02d203840d80000d0301a1007040311200065005500204011a09802215404001000204160165110042e11240c000d0250f03504000c00172591b00e040d210100704440c840d41c0c1000901c079a0000c1480141550202125030002d000c4c0546440031003030410200008649a000c2409030420040c1c00141051f505107a000001704030035160000f000c00c41403001071005500b295903a5840b80703800d00030402e205 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 381907032 1250 381905782 381905789
    0x70221120708030601030504030504120b070306120f150b0a17100b09130c0b0c1f0912120f1128121a0a081b04140604020903100f02070507 61
    0x40d410400000080c10320001c40b03501000900300041c560b155801c08580d24001e030703040001d60300d2000300740506015113100210b114801c43d070707820310810f80c4450000806440e0610020488800d20b1550b0b40001d500407101d10381c4510072100061040f41260025500054950021485e050043c02080c10901c0c180028562040310131406e108100414022030484a0010255101410300d8140d580400624810280050005800c1141c0f030b141a078240944900640c4c2007084100400700700402d1600c014000d134494070b9003040700c551100202140550b01151000c2080ca0a03955445084841c400c0c94880c96400d080044c442036203420340407020b4508c2008008201d0005410302108102c410790203020030200440d201000300f81e0060114007030516948049021341e11000e00840070642031000941c0c008020380d54030340d013543e116400050208803441030000140011385017000070a203050070b4005000014001e81122203d20382006001c0c00c80b9036040c0c00035115500011902c091100810801015 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 381908282 1250 381907032 381907063
    0x40b0a032409020d1112010501270c0906050d151404050a05090606100201140106022b0818100f1a09090a110a1d04120804021311070221 60
    0x11802c075030009490024084c1c0002c0030041c0000d192042503c41d00030009007048030070001e00c07182d61540411494041100418202110480000205030070b9600940031040c48544400b4103d50a03c44110344a034010340040e0011a10b58101c0100d150507584404010080e04003e0f131084003800003080b0036201c018024601031401c242c18822140400715841c1d4004c42c086400e41018500c1d004107034007410300c0c2c40400c505444003034000200c0302e8001c10711104a00450070415003d030528000100c90b8420781d032510000403c020001030751010b90304100f0300200740303800450304003007503514420041d0707924a0804206070340c80d0181b0703001d20702800542d00200c00782100c41082c00d1911400099a49803400805000c42407602c0c05a88075881d607441200141c6480854006449101c200d2624040000c0d00c04503042c0e600b104000130454071a120450040d54000d003010040ca01041a50b0f024001c403900740c003c1c204040144000580d11005400b02c2900c80200c543c24a0320300000403403d12107086156120b = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 381909532 1250 381908282 381908291
    0x8060409020a14121501080d0516080901050c03030a09031d010c0f1403070f051c480606080a080d1e0515030d1418040b0a0324 56
    0x41c0c1c2c85030031410a0b10555448850303800c0f5000c0008186840e1144401114020800340980c00404442001e0680346441c0840344031040d40303441161644a6842110700c1040c0c0c0300e04e20400989698020710740950305150030b60522006005040c1540e0081d41c60f4202c090b5104108801c0680103a081e940c918548026003445444c280c002800c218020b280040c50503d00801140421464198880c030310942d40d030450307480e0041403030711094241000d00c0c1950548a030407910001202004c03c02e0000344120740e1000d900e201100085c0d040c0c5202840c00c4000d1421005601d00d8170641c13448040e0760390f20440b0b40011070410505080003101c1d1181c100481700e420007450031002c01d0944e412141e280034481000a050034100b40003504290001244030030706400d10b000d100141440940c0446004000c80a47e507aa0f9081c00050f15200d85402c4509003a000510500140c0b04012219454504010b04045031002c1c5041c000307046001541c208903016044084e40000151341c0110345402013482440030403 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 381910782 1250 381909532 381909551
    0x1090c0512070506030a0608030a0216051005090105180913020a0b03060609061e04060c120e031b0111030a020f0d110c060307021603230313030b09031612080604 71
    0x141c0b00d1001d4018079009503800800f00781070351025880080102200c00070349440b100c42c00b0000b911110f180400304c0c1c041c0503407140410103242c5440020403120302c0e900d034585400462801540e05c0e401134511451601c1c940c185001180e10751310030707070361140e00c1500408041d524944108074000d4141e802c060008807050040141a803900c9003102c1090900703c0f5816180e41550048503040d82018401c0302d00c010001c10000303817194200f010700404610402d0083d0428120b076100304c0b041a81690003540c194040e4405054220b0035000c0c0c44a03500041c90100403200040b40381500d140d202c2500040164000002c00c1c1a03940700f803048056013089803030045a181e000401d01c90303903100d00300410b6211350000008180000d0081081265007080402807000881e585d05141c0c0000b402d090070031010500340f820400060340e020045405128140c403199140c079003151140c400e1702c000200541035610080100c41c0300c0d06020b41c041c0c1c06242c812a03e00b5071044506400510f103150180100340101e0500503410f = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 381912032 1250 381910782 381910819
    0xd020907030b040f0630080d1505011706061c020c0c01020d080408120a0b040c0201090627170714060108011a01020a1b15021b060f070f02010309060203070201090c05 73
    0xb0000000388100000c00110810031b00701c180c240b1880103150311400124100f41594503000f06c400f42c0b1041e401c46d05071580d40c00055075002c48400580c0c1c0781c1440c11000580c50300e00000074049217000c80742c414601080c02003980b01241c2c042c4107012504c0e8411060759a640d03904100103440c6d0070007490000c0007800e103643c0b6078160340a203010000340c0b400c03508000358ad15000c952041c0012100104148040b04007880040e0003021021000e079111800c0594403115180720380c40c42048011a40686840100301340c440b01448180c0105c151169802007050201043c10456022600d08010b8040c10744d0754504416542103540c03140c4142ca0100c1c0d04048110107a030041980300e260b94210300406500e5412480440903941c46070410207510703081005491065030f00081040c170901482e1003008000c100401007140c1d50048a140c1d041c0040304000480014132900c00e58a007081c4181030205504260380c0e560030030382c0c20403500000140c0d51004d4503070912118044140042005036145180c03001c509004 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 381913282 1250 381912032 381912059
    0x130f0f140306010905061804110a0602161703073002010902060a03020705010e120a020601050303070c05060f071e0510090209010611070302030304090b09100f03030c020d020907030b040f06 83
    0x1044e0007a683d03600010861f032505208070580002c141f020080070b14091401d05920035000c0e14450080b84c07840c402103041070001500c1d031459002020b4a0b46110b20f060007480510000b61b1101c2c0d1140418005100054161211894416030400584900b0741d2603203901501403c42000c48400c5a04105440001d42c0700c0303d044032240140d130b18000d40d407607800d41800da000d0145220204901d10807034038400c400d4106403010b0302170150103074240c9030300c5c1e41d903941010355074000d50001500b2003c0b074032010449071031309000900c1c0a2001c107600d1030400d801600d58010000c00c0210030010751859010340d6041001c24000269102819001003003440003a80110700780720f205020360000d00a1551074191500c1c8108208001158001e0450f80d5540d182c40c0c0e10b50207401c04070111750040302000302050004000407494070540c1c0b043c034a0340c407003645140c500700c030445044031040e41c01003400d440e6800544c440b02541840f8050342e07140800c58124940621080322000600a0000d0303103051410710031005000c0d403 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 381914532 1250 381913282 381913289
    0x22060f0f02191403191808090301060e0402030616090e1501030b04020304110907020709020c0c09070504060f03110c030a090602060a060308030a0b0315040317010b030f0615130f0f14030601 83
    0x840118105e1080a000020a0004d4a04903071140b8000540104801c1c0c200800c501c1e4016130084c0034050352464622010b8006a9000303506412001c001a4070084100e01d08000050514000003490766442100d4640c94042c0c805800d65002c0310f01c440b10b2540c0500880c030340810300707035821403030b45c40c054030707081284522080380c00d10890841c40401c42041c8200f003000050a1780d41011591420b50307403c0d065882d05d500d411140174121030000100424041c0082d90119001c9071940c900741040c00360100c1c010328032654a23914480c0244010400d00741d08001400314141e60b5155420702074100074000c0c2c0b8000300201011804c3e0304240c001d200250001c01039a070026070341b200114440b404140001e0030002c0d000e04103441840c51900b080b050560040183c0750100500c4400c40840e6280c4bc600b01407840222001846039060002003500713410060354451003c0b010101250600144540113a20801507034044070341d03420780c0d08046c812480400107400080c87d10340740c400b010b189440d002c04d44481d030520 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 381915782 1250 381914532 381914551
    0xc090d0311010614040b1203070f02180403030e0c0a0f0b0306150c0303010e060904020109060f0903060213141206070f03140c0a0305090622060f0f02191403 69
    0x618109070041c40014095001a0024054161141900e48891031100c582c04d03c128103000f030041c4a802e1404040104a0210001e5803900030180c461034480000098101d0b000100980e032400c07a462403d18240c01584a580c02050034030102e503101d8a00084440e555210728507808081112607108400542120488d0b06111b4481d620400012010103e58600144119001804191030140400218180d0b1000c145030146a2980000d00030309840c21500203010864121042c00820300809201882041901c1c001d582e0a4481c0e480d542070f42c00c04480d4080408030841c00b40803070600148098143c0d101640c4015071030b080300324416030b04d6801074025800e1246038a9a14642807080e040502c45c10b25414004080e824243d400505030ba0108180100080c909404264160780126007035001f00504a02c414002d0804035842d0750603443d9807000c5030b40355524100300303103c2d1880e40210202c03220303129001030300e5031060340488104484842102080200d60041102400d1200d402d8a41100850 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 381917032 1250 381915782 381915799
    0x2060706050703053405090d060207030f05120112020f12060603010608120a0f090b1201031208060a090e030d0501030c05010809153601090303110a08010b0a03090c0e04020301050c030c09 82
    0xc2e00146d91600c107685407583c1000c10031081a0600c069a002800c3c214400d5540300d4903000003040c121000d000b4000d40f401104140310040119004034013604040b180000c4c5040d210078054000580e03040040c6071100c11540080b002c0010914003842818010090000a03196640340078414504074803072094202d042c00042c4117840107552092003000301074243c965806a031600e20089080a8940034801251000a8030030141456446150360324000c032030182684400906000f40c941c003400005da005412407000f440100185680c0e4042ea0303000b1405440c2454005003040e0004107404001088624a54044146078000718030041010398031151100c1c1400800750818040c500060840003034400c818a0320103c1c990020065214200c1a8400d490401038210200c141100e107010b10140a408034131008010818004a1001004190039524000905420595445c20022541d070060b00702103020f0780030041181024810642c1109a0030041c508610300908208100c0c400d0070f5185028a045 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 381918282 1250 381917032 381917131
    0x9140133050108060d05010e0303070206150103111206240309010e010912080718180b12030703030b060c0f03031503031213150c0201021305060909071b0206070605070305 75
    0x294800f20023030b03080400307070b999906004500a640c4c05040c5c0d0740e18821000801c030b482d4658002d20402d20802e262903500d0741046000499010b031100001c007141e4002c51140c5d03041110580341009501c4a40c140c00c4026100d0914000203800c40e0342c11a103d050313981c5004182004100d03414900540140d0030b00c0c000400344d40c1c1003000c07a150801015070280a1072100008114511905070344d25500e105c103102004440c1c032600400c0740e00700343d44041d4800c40d0004c1100360040b0340300b0b402000945001904003441c0200c1845d207a4600200001181c00e5504003106020480c0419000348032907900450080d1300302001440c03410480302001d482c04402d822202c003500104020355984814245000c01d08203e0304c80001400b0f030207584140183c1b065503c4030980482c0c01d24040c015900c0c20300c00500610030355900e5074400c0d10190811510541e40100344c5040f0801a943d01e40103000480c820300d40400e4600700008060181c0300007400d00440381c1184040804007442443c50f004010401030a0088030355803 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 381919532 1250 381918282 381918293
    0x6180411040908070204180c061d0a0b030405100603020a171516110a15050c04090207030c1406150f04090c170d080c04030609140133050108060d 64
    0x100305018075080382c10481d030041030101c68400741030a140207032003d02402048116002c42150f8009004000754000e8406001e45481010089820410808000d420980000008921556540c0b00c4000a07900104100802c00e0902c00304880c21940300040c0400d504650010301813540c64003986c80034005110101c02110420003c0c20306404001c0c0880326030341040d0300c60600884542d660310000c00c080b241090141c900014044405580200320294007408000708a4003a08015010038a40c01c0300f800f003c40c0e800340d07501c010120244a5100c01440d00c6092400109030008041c80c000076800240c00c12001c580d030f42a41c51002042242d852802030b090400260080c48084e4000d03100340e000b941d0210f86280124607820310100030904642030b030395072020300300d40c084000c0300c41101218060204200082c420380098803900c0c071501c80c1e80030001a102c401030840f24075405504005103c01c00004480104800d02c6e94410641c2c06402c013a54286130000e4900000505104e00611400142a05000 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 381920782 1250 381919532 381919553
    0xe060d02030a0608030430020d060903080601020a08030126100c0f11100b0418060e1209010215041a0c090406060305070f05180a0b0a02070609030b01050405090c030601121a061804 79
    0x540c002e0100c800c80e095814041d00810350340700c00710040dc1c000004503843c2c2d800003c14038241e41e07001007e1031642c5e00f0420000c1211207166480885240a610030b019110000e01441d102c0100c5980001400b5800c0c00d001003c1888142400341403110065450076958004500381c0e0902640c000049081800b01e00131800802d40317941c0122218484d804880d0410459070080b007031502d405030885002c16804400034a140c0316841c03450780035030f001110782400c0f2503101042c581c1c001c2c00340c1da0101c1c10000e40b907a8600c07600e40031200350b000e603040083c15860f80d242500c1040080e00303581c1390401c850300d0b200c0c03800b501044562080038144000411200c6880250901a210050014250a010540e2102c603001c0300e8010084400160043d540c0100702c2d01c2c03103000c1600c00c4035000350005800340d01c1c2c41d06100c020300c07001d40116164050058555600e85040082a00800e610b080c803030a841d0041c00d00d0300b6041401ca110090f8207030034906110540e40c80081c0c82d0000e681941480f40283c80e140f03410368108 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 381922032 1250 381920782 381920879
    0x504060602030a03050a020c0715110a0b0402090703060303050f07021302070c030c1a0301051e041b020d03110f160c0b1b0a030c030e010e060d02030a06080304 70
    0x150810002003030455010020b030480104644003400651100481c400c11390150312000340656020040820158001802c0d0408600160400300381d03e080b1907098904000c0040340503074284040380180011030a2170f494050b8081c0e014501000414103680d0b0051280c0300f5510300c00d808044c003080b200190341c0c80603802a813616200c1411540d0303030410310b8142210b99440c8402d40f2a1f010702280014035a591035101e00211401410640c950380c00c01040120040246200701c03105d04200da229112915a88a0071030354443c0d83c000000b0740c3c540d2000091400c0c005004003403c06041050940001c1c0602060310761000c03003501042c2c0c0315141003082c001071400030800a0040c001e00c21001400315016402041d001412424610004e100307120300c4c0b40e9a86480c50014001000607802d500864426005844003000500d88161541c07040c00001d1300d80d0700240c1515035040d07400810300ca21581188100c400a004e40b070003640c2410b2820002a07004a0404089050301819054800c103981c403100c0c44000b0f0 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 381923282 1250 381922032 381922039
    0xc03040c230d0b09070f030f02061303051501090e070806010506030c132912071101021605010f0609060509040b19020304081804050c0f0f070807080d051b030a1505 72
    0x10402030925200c5528140c80700702450081c08030101d02c0003603001b100300c02e03a50096454000b40340700c0d600348030b2907501003c900a0b03916040c0e080840007800c1400400c1c040d058118108903103504051684c0103c0709902d0000116074090901000504000b040b0303641110f40859180b900c030b0307545e81803800da18410030701041e8a000203008041280054800c43d03110315603031002c0c1700d0148002054202d1083c80303500b216084c80e60789000081c0600e48144400000446248005410305a08400103c0c03010150242229aa51905100e032400b0150340300d244010501d03440e00313104151a00c3e01082001c20040d00c0074068020420024070311404104c06400565103064046603686003171f04012849401c0318000c010700f46c11b94544d050503841e282c010310f401090075520712454441c0301c0c0c0c035480d100e91210001030b9582d6401c0c4003403000300d41840040c01d0f43c5809a0070b0745a55858054010085500c010940f102401c1e00c48521b00010b29190182e80d40480d0184001810005803d0407080b000c0d501c3c0d011660 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 381924532 1250 381923282 381923299
    0x712091a160602120f060d03080f0411040515040b151209011b0c061d19060e03070f050607051c0b030f25090605030d0c03090e041a0c03040c23 63
    0x201348a07001c0c030301c5100351988281c0381100c2d199841000604000300f00c0103000511003801150803200280e0310650421721030105429404e1845021505075101203481503045420003080d070020b414640246456000c04403031511658005403501181c0e80202a203108944160b84000380340204d09521103001f44240441c00ba03200801624002c0003001a408102e4078907003001031000d1042c90100002800c0c0522402822140c945100005020061044182c8055480b4074000d42041c0040c00101200d034003a24011f0a11411410000d14054001d070142c02000000c00c40c1c5070f401c00b02c80711308400c9440750640101d001c5a01d40000b03490302072421030a001a00031129840d078035119003c841065081074101400420b0b42d02c1c0141c100301d8019114640c3c01da00130000301c00a0038400c0c0c8000b60858841d0802e200210f80b44d1a15030000c100450b01140d411004082d08040703003c070303003180d02d501001c483c1540d465880c00740d59000c00c20700307248180c000c903040c03980b1440c44004011810005034007000e0401079 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 381925782 1250 381924532 381924547
    0xb0f07050408010f051b1905030601051308010c2303150f130515010f050d090c1703220302060d110c031218070503122d0712091a160602 60
    0x2003805a031b40300e4010b0000c00820030589004815100c5004007202012001c2040f144d0607141c40d4402815141008001c000031034072081d08511200240075841d000241003400f000f0040c0603044c024001c0000920411420080c0c620640e0449501440302140d0500c4a0180e002045503442a407603007030740c400b20105484001d503c455005500c55901c03c05041c241010707480040d039120071041182000603078100544082000150807440c0707541d100c2c0345480c43c40d9035521200500c8800d10f40c90303032046403c00558420b410500c82038108080c517100c3c2008400601d5540010b01e1032044280c001c0c141358898692802100c080400d0341c0901c081c2c1426070742d032950325030310102c03040c10112000c4807903403c4034107018140f0300001002c106030781000d8000c014000c0115486801c40c1c121854071008160101700c030044401d10307800002100c09a000303c03107482d554180f4004040c0c1c00c50032070039810031801d428108003004640100300350b54560141c809565001300d0b040c010500d160420041d003104d00000d18a03 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 381927032 1250 381925782 381925811
    0xc0e0604060206240d0605151011060f16030903031b090f081902010516020d0b01080c190612110408061b070f0b1306060e100609030b0f0705040801 65
    0xd1041e910303903103040c200d80c0c24044e80610070703040c0c150220340109012081400058260744100d811016650448041d00700741000a585550b468508400182c146c800c0405106010041c49411422031951400c291904007541000740d22003884800800d500c4045403414180240d0015119840c0e010303074081000c022842c054100380c10b0707118115010340c0c0007600040488012604140b41c81166151b505098100d40044509800100b0b100c203100000c0e20448005941d20b000c00d41c20580700b0111302c1c11a600d01002c8905004100030b0490081e0242c82c044000d00c13000903401010740318542410300c1041003c1c1110f10047c4070032225501352540028002c1800c00b800200e01e4412401c1ca40041080d030808540820640034100c0b001300440d407210320180010f03090318141a4000c98070541d0501000882d10740b6825541c030b41e8081503401c45a00c050250020600a840d03002e8442824082e22480c9140d903440442d480040820307a480c25008081030980784110111002040c03010001d100294994096 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 381928282 1250 381927032 381927043
    0x7171614010227360108100e0a03020d0807020723090108160b09040906051e01170a0803060301091b05010f0c11240a0305150109180c0e06040602 64
    0x14603e1246414015200001c541000c4100d82c1000e0144d448a44490001d080560511828028030300100c042d482d11a00c0039244650080681d2002003400da8404002901164030610020007160030000200011903000035803003e81d04141c0c50a08203071790b180c003422803c21030581c02c144900a00555815142c0410070380b0780503600d608582d8000a0b903038a5001076555810410303448201d030b58108c0100100c1100c000903001c6000c02500105d8148041d540d01411139130100c0b000411a01e206c43e0311550200071500c01405030207074003590058001504811a43d45002000052403006c0010004500d42c90a4105401d01c40e4407060b050031002c2404c50303400c4556440d02429000a03501507400c0300d0f161040d8030004805800240d1281d800d800d08082c000c884038000c0414261000c000041c41100072040c0090060644550300001c0074102019080301841d409856141005241401031040a0f0540482c1d01810900c8800080300410313190141d07100412604c0741607010740d01040021342c16802061 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 381929532 1250 381928282 381928297
    0x50408120c16060c0609031b0b092a0f180903031e0106140a0c080c0a0312090b0f251d1909020a09080604080a020d05071716140102 58
    0xb81c1c0e40140b900003194165010303034814100081c032211401030105443e0b03841440224000d00c1d101c40c862000d6003140c42d0070f00e884c1c03604450780b110f91010080418414400035004861401401c24114090b03081718111030040210f09219680ca40e094900e203035a003c0d03507522881140428034213185450038285403241c000301d60349090050300d009004403808000303804505039a020f85560441d25988401d06910b80c0140c0c1c04c0c0418070100e543d00c9008500580301030f01d201c20402004086824481c42c00410f00a048c3c01d80c3c3c0703034941c2811184000112002081c51303102d460400c40d148a9075920304804203031464003601c04403110407008042c41c00c81c2d1000ea10041d0800e00c0b0050701a00c11010180302451800001e9403183d112031700e0007445804459001005031400c645010341145894a0300b440c104007007a1800c607401c481c0040c1c45010a82c050110900d0041203090490030240c107038480f44e5941002d0004060303a07501c009260003404000c101c40b202825040400c04602c60400c40609000354820750 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 381930782 1250 381929532 381929557
    0x308160206040807030507050c0a030602090103060602031206060c151e1f06111e0601030302120403150207150c020c010e041a060721030504020118030b041205040812 73
    0x11800500900016040d4010750744075500900e4604d668404030307455001843c0480e0b20340111440080d550369040d020070082c40c01184010303900e08031000050104c481d0355000d04155003040c0510840f4141ca03040302940040169821340c0d40700541c1d070f0158106440312260b000c2c107540d050140a000c12400d104800d21a01c08030741d500c440d490b41d00742c000404064521a401480480000b40039079803182d0b0684825030402c5003240e03902c01d00d030041d0f100c80d05825240c441890744142c1c010814180d04026070464450450041ca15050442c0c44410041c882000e0b91005c0e1500014094100711480595011519040404010702100000000c0d142c140c25401240007442c1ca0403100c000c0d252031702c158550202d4002100381d51501c2c0005101c066000250113842030740d00c04100302d02c50321100c48006800b07000c50340d00003064a00740c8005051024001703034800030501c100e601440002c41c0b9808160700301d40c012030348400c5410310070f41c01c603028415500070307002c40d0258140d11030010301404d000e450102c00c0075 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 381932032 1250 381930782 381930811
    0xb090c030a0c0c020904061a030a0b040b070503040521070b0f04030e01080603031b1c021f02040f03021c06110405030f0c0a03030807020304081c110105040b06041d0106030308 77
    0x42c804440c0c006043d030001e54080042000700740041c150358026007a03030340003c2060000d000c0038400a801d00c003040c0d8060369149100c200700320400000f605010b51084140c01c01c2401c50401d5140c2d00c0e03403580881c0d0300b403a200c840303904420800404203003550310069020340194914908240502c001c04c2e010388045022a2207014442000d40c0039030740451203508040c00440c1001c0c03000000050103e4000011041801154680c02c0039945000b0000c4400c00c2d240c00404010083d1800000035030b041c0c000c0903088503c144800d02c4801075a0040d80222501110031145800800000500d1940c1c00300d40140420300e41820700e00002644005030007150310407010703030715074081300750300951503e0142c0070b0301e0b40c407040505060000901458040381c02000c80c0c41202e00742600d0741c1c943ca1031300d4000b007050f811603004040c083c407820780d00c908480b90b9807075028003c1c409420959240d00e20000040c102e544a00d49590b40225411041c0461460040c420002400415070700d05024255120a4500c6219030409 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 381933282 1250 381932032 381932051
    0xa1d060d08031609030f05010615080103030207260a110406050a0b0301060f051308061b0a090501050a020a0203030301030f0b06060a080109020d020702190f060e090a09060b090c030a 80
    0x88200140056000765816165554102c8503042101260440d40c041c0401004040042090200710405041c840c0f000000c4080c284512604030302c000b00d92900030007580d00010300000b40e01255800031108240c17a04046003915400e408036a2146020500ca40e00c0381d03514000a1004c2d0008512503040b05030741c2001803036141c070240503801449000e441080c0070100300401c6410b110b580c00e443c801c00146003080c288174a190100e00c080c07050760b01c018540da2200703062105c00c140b00c50000d5454422a0b141c0c901d48211508003900e025102d2040718140700340803521a14160092100102082d8000d0940b640c9603160724010100da000160700740c5000c10b000e00000c05c0c50800004aa089000780e4441909581c0391800d1107020b0b5028140321080c0c01d809000303410050300c1c1d07482c504d00341c0b040180400004034203024200008001940c40101000250f01c0c03075400641351040315a410214800000c186120b0904000d006895001e8402e50480c441d0005c120141d00d240c0003560140f240d841091214505 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 381934532 1250 381933282 381933289
    0x12061d0607181401050415020a0b0a0b010f0509010e01080603120705060109050105060a02100513020a1d09030a0c02090a0603080a1206060810140a0503010f0903031803050406120b0a1d06 82
    0x3c1c0c8a0500e804210100410b00600c0e90700c0106038501c0d6040c1c4100c2d0104e4a16645240c101c50040da000311306280c40c4c0400c2d070b45649c0c0090100b03108a10074982035040001c6480000c141040c20a11103040c049102d01080342c9840520110410b1160b420a81c2c1ea144241e182c10f5903070704001d126802207645480008121894020119071038210180c2c018180c1c48000140c01004100152083e29411150010703a40180c961533440d0004049504c13540e004901820034207000240c00401d0ba500c1a041000651406d41d00003002c10b890700c1d01642d29003cdc81ea00d00400c07200500c055003024140250104200310001c0d403005110f0305050300c00c80c09120582d07840c0c2098036030030000c0e80d00c007241000c80303c0203004210703140b40e6040d81d5034001080120600e50300c1c8040f80c215a0480542c81c2da59485a208606040e05405017451011711113844044280a0f078400810a010710300540040080c031060180b400da8240d0040d41c0c004100508100c80c05543d02d02003c00080302a4521190404000c000341881c503 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 381935782 1250 381934532 381934559
    0x6160e0a0305070e1306111809040819030f020d050105120708120901021e16080606061902071509061106090a080c07210b090712061d060718 62
    0xb80c1c0b00d0000d05942c3e040650024a400c40103007000c1d00c0e03981050304600455054003a40c1d000f10800700d030310369441206401081c221020340014600803ca403c052100180f0365000300c0307074825020412008807818480080300900107204c0d40040a9002090041c003802c0d150b44140d0499408540c100d20f0040b849980c540c4401d2140b1a50215400c400062516000414000c0000081c1481a185074140b0520030f0030350340e0700f0b40e04031808a602c0a1078540382c0119a41102010f030602500401d080e1030650000307100391041440c1c1045200207282c202250600800c48800513060046030346c5004401c03800c0007813180c00c07184a54070005080c41030481030b0b010086001400784c03010350f015050000b0300b511558800d03880542d50070610702c03074190005250481140003c85119950403103030b0b178542075030804000d502800b602541701500480300030040f0f010484c030700884040c0c0c40701340030402c00b56a040d6040c214807403048424290240b8410000244d5029a4821503000380c8d014000c02c03107403286414020603 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 381937032 1250 381935782 381935789
    0x5010807090c02240c04030602120601030b01030204080303010902090a120503092b030c03180b071106030907031103160602010f15050f01200a1a010603050c07150e06160e0a 76
    0x30030000c510b03400d980c0000c80890780800c5d801c2000f40740556964a000c2280d204082c0e1999840c055014400590390501401004540910b4150f080c00d007051452510381c030044c41030325011030780003601e2101030b01d403000b0b010000d0600700c0107000490700500f481901ca49c00320b000c842c071400b010300d2507001445416a240410001115026807140c031584d81c00e41d665036200c2011303420302251602c6944800c40c2e40b07080c513000e000350222886c1c0b269050300d040046001146207540c496076017441041144400065004e0031281c0068440612404950100e400c00e038000750070f80780c80b0504c9400441c145805421400c0003860441c2c003003003080000f0512850103881802007552050002076114095031141c00380410540f0203800116059010410320f03441e00740c444000b00c540650030604041c00103640030304c060040029090910140c6400481e29070540310350030008101d00d452003250100881c90350f100001d042030341c000b2185907041a81d01c2c07240d10513107043c0e8000050310002615000c0c0c109106503000720b = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 381938282 1250 381937032 381937063
    0xc0e0c0403060504050f060907030302070e0c09060d0e0102070b15040608100b0103020c010516080f0610210c0e0f0612151207030b0f180d05030606090405010807090c02 74
    0x103081c20740d50388001038080604140c801c0e20440520002c0b1140c1480158080c2426100500040c1e2444c1340203400d00c2d0890f84100301703a0183c0300c10003203800c070154102c8010380c400b21039007544d03527500ca4180c03c010400b124115610f5071010614070200085486494001e0b012019240700d040ba40c0c4003000103403441c034068400b060b0000302c803071107910405811160383c0480c14180942040543d40c009402c4a400715110a840508920440c11a03a00f1081d1181c100b0029030010f41c080c58840b0105d0120102089104104801c035004200092025034150031503803114241400701b0905590014003c4041c0b000d001e10400e603201c40c0c0e503250f2914a08031403220540c6010040c4035501c160134a0b03043e201c60040359030800d0310403c5415400c0301c14400c0c40040c5200380b07030350405c904048144c1c9280140003040c1705240c020500070b07901e55000c001010380d9100c0321442c000340e81e56540070129805000300c84401d070b000f0b0304050020881190120303100d41912054034040140d12403410f400c81e540e042d03000c00d4812 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 381939532 1250 381938282 381938287
    0xe030901120903210216080a030c0c1a1b0307020604110d11060903070824100506091002010f06062606130e010204030b19060e060a090b040b0316030c0e0c 68
    0x544101c146008180075446400103085c04850001c05c0352240140b0b5013107d0458001440d060299018407a8a0700e41080e498070078070083d52540d41211807e250010b4110383c0d8020000900c144400302c0800d074424180360b0480d03489081007a80a0354500080d9412601003a0f03a40070007516050003a0012942d40c0c00603258011542000c00f400010b40c0701040994160003040d001080192041204809000008401c2180ca0614240c19800b000018bc58146418080042040180c0e940000ea800c001e40460380401d503220340002c140c0c0140340410203400c105041034000500f144c1c021804070500350101400394160300d00417203122403001045070138503130200c4110203c403044003440c0e018078074161605000600d01622034448401e540700807280c041126444248580e44040346018000042008103107190050411800242584810303006640345150380d00008a00c551302d03900601c0940c9030280646088042019070340c04880414002030b1034450b20b0000c00203020b40c03c00e400b10321410f04a0700320f60 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 381940782 1250 381939532 381939557
    0xc0d0305040f02030d021e060402060306060d2714070501020a150f05010f03140105010b180102120301060c0c060e030703152004050102010e0303100e190e030901120903 74
    0x180180405001660541444994080140c6041116403044021034005141811300860b0328a41e00f101015030701140e401001c01d00c0010384402d070550303401c0407049603401e0300d89408004140c002c24552039a2051040c500d070080540002882c84078a16901605460030500e42d403074103c5a5440581c81154010b0340016000004038603640b01c00601d890082e24003185408514600e00160ba03030a8004411100304900d04104000ca06008a90b0207070300d00000f0301c0705c0c0d813400b1450000d80c025a035900c801c103104c013140822242c1c400d0102e102070b161009000c030344071350f10751100070000007048608032090300620401041d014020b0803804640000100200b00c01c034255a9a03943c20360030b0710306201055840740c80071100d4a1a0340b181c5a4482c008501854640340f81c10002400d40f40030455176a01c4d074004000707000c07080c402c550340380c4181c81006000c1c600545400d8001d0700214501d9089040c0c0f80c0c41c020800901c10004802009050000d03640c81d12001010482c800490b1f2549000401246000d040003 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 381942032 1250 381940782 381940787
    0x5030c01050c0a020d0305040f0b0a091e2d120201091712070305040801050a0b011206050d12050c0a0506060301110901020d120b0301151d040b010614090d060e060c0c0d 74
    0x1885e00600c2032520f141040c2c0c2c3e4582000082280c0c1c0c10820b85035030003080c1580b80d2640b14103904000c0c10301400040042d10802003000892415000f4540c101e0308107141100d50b005031007031000422284420001915a131410071414003184000c0803800100000400a002c042440e0719104880c040c4014141d0b40e030b44e5070b0b03211210f075018180c1141401001d010006021100380b0683e071140d03442e040081000d203808000100900c280c2458094000e10f0710303c041c006510381048030020706500880e44801807a901c41e00341c1d06030090f00302c08503152184500450030008042181406500150001e101400f40c035652030040703004003916203006900c104103803020b5900c134508141c415940c2200001d00488008082800e6440c0850640c0b540c03414406e0400007100e04160300141d00c1c6102c4d05c3c140750f609180e0380303001c1c00c1e10381840340108000055841d1a1110400f8044030180b0000600c0003164514900e888009449120103006046c0500c4000070041008201215040744460018045070100b8200a = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 381943282 1250 381942032 381942049
    0x8030307050301121a0906060429130906090f1401020702090a0f110a0906020c0307032109050402160204230a090c0503010f02040e0a090f020d02060d1505030c01050c0a02 75
    0x203172203081d182c00500008041d1507041c41d02841d03030751002d80b046140500070b01c0240c0d10020220304c20160840d40e2460821000359500300c000d1012550704410380c0310031048030040d05e0008005800280340c0b84103481000010300c0313005001032150309501c1c01c074160818442c8c200c2c0542c80c0080d41141d0f0910024000508551000c200060f00081c001351034003c40105403000d400c8903000a01080c45010180711980e01000880c0d0441d004400800c3e04034203554486000a0014001142c80c43d410f0100a1005010f50340600185c01d001c2c2007151100904e04140c43c0300b01d43d05d0010303801140750040440c032445a40c0c04111070011081c540d02031700d071500101d0b40010072011324140d4010a00d0800407030503036000e00540da003201000402588172801c0c042103900301e80c1c000e408400d00d6031a0891a1b00083c201d00040c464264044800d08901d54030b83c004180c0905c1140000d0038020f15040046011560b5940b40005642e800c0e81150078441e2040300644051142c07000008055116610080052804444 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 381944532 1250 381943282 381943319
    0xb13080703031b150c0509031501140d0503120a0207030807020c0a0e090a140105010f150f05031b130609090908070f170301080f150103030f030c030b0a1404050108030307050301 78
    0xa2100c44c43c1d0703e004e0307000200c803032081c22100041c5001511402d103180c00c0050b10585800910120440e5151084007103030b031041800300d603000e400c02102110900600340103032107105c1c000d40e00d080e05502c1e140403020f00a40c011003080300400c4000000c100038910025065a034040003512812449080c40482e2007282c10080000c100f902c034004e0060000f41a107030002d14065481c0e000480e081d4102440000c40800680019644035104402985200e5104240310710307041043c10304a94030b495070f003010700d10390010b00c0c1c0768000c6d114001100c015007458a10280120b418a5480d00d20551311020480d043e510b1005010300210800c0c840100402e4521001c0011203214060b030280c1803c801400c0709550300240e2200314250001d064a6220354010300c20021080000402001c141d810b42e94050b1907807407800802c00070140c1da00701003c1014000d501548001100510704114a42d0321510803840031034001d120f40c051801c103030002482800000a4074094042500e5040c15030303082003402e8552400241 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 381945782 1250 381944532 381944543
    0x30615061c05040b09030715020901090e0c0d050624092b0309080c01320d020409150f1e050405160e010c0203071703070c0b13080703031b 61
    0x8480c00200c41d0300141041c0311685890301080d1490103040c400d4040304010000706031500100101400160750340d2110440e408103810050b204e800d0040101c03841d241641002015800c02421f11a07004910405880c018030703084014004c0d642c610050042405059038101c0103242000513803440f8805010140100c10781c090305422881c001c3c07592054580049000c2100d9410207590200300381031b4002002000340101c03000500da0322900000082071100f800910207146441d140010200780c8100014407110001c60036641d40f80c48188000700002c0d40a072041042d142c6c43c040d6005000079158402c0400c030381d1000702c001035051a103400a04440080c00c10302841400000c1301180581da80d02c55a40a00c40c0541e0b020340ea1600c2c064050940241100c500b0f0510900501c0030740180d40000d5000d06440d81150011850680882d0741c600d14012902c0003060381400c184003140200004c4080c003040c0300c2d85950f1440340c513a46c2400c95101c0c180740c08080c0006441c0b100c0401080b42000000a0462094 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 381947032 1250 381945782 381945787
    0x5010c0c111e0d140d02031e0304030c0501050916050a03170306130906050412111e0a060e0f0c15030708190212060a08010c0c020d050a05070f0806010e010503061506 73
    0xb400014100c02200d44111600461000041c03803140741002440503400342d6000071032414040350180d00607031a100341103c0c000300f000400981010701c20700340142483c0d4804000c2c002410507100300c2c3d440360010b10f50341d200c2401003400003610f0303e0601400b500300d0350880d1003039a42c05030816030041a03a00040c80c81da0410440d000e400c640c00321502c41c0d0490303540500b2002503507044c0b0345400c040c1c2034000b91005040241450010620400100f420504201c0180e00c400d40380e800c3c0711071141461030701c2c03002410081c40c2c182100040c0300041100d0b0044044442551160088e550403c09080d02024000b5000b440510002f0500380c002e142c115000f01c469841012031011416410b0280d80c00051000b140d100c4d00028008039040a0f130801010b07100c090300074807040740d0301600140200100d65019228000080d402802d101d801c5c420040350342d4126081d60500d9849411144030650385103d507003903e2161900001c0c2c0c131600c0064a906842c0000c024040c036486468070500300402d846403141d40f08008 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 381948282 1250 381947032 381947089
    0x212010b090106020a05010506100e010c0201020c0409080d0c0305100603091b14090c0c0a0b040606050603100608060a051f0210020a0c02010e04060b0909190c080405010c0c11 77
    0x3060400740c001e0030302d0307070041400c40e00c1ca02d000c60039150081c004500414400155084054020380040841582031a0501441603c1c0c00100e18240a00e02c1042e0043d29200c4480140b1084400601c005240160f0602011a9002c6d084048a404840e40c0002e91889502404050301c89e8002d040b1160140b2a480400c6404010300d00b4032088590007840301e012a15a844080d080040742c841c0e110f100c01c5080380c20f00c0b403c01c454076128121040c1c010300c5204168000340411102c5da1010015003005072100d5124588007a105810401c0360003404045114200041c0c0380d454150000000c0e100040d0241038103001900c400a100040c2418600560080301e50400e40e001d400c1c80506107103649950f500404480600000d04041944807080c0d002d139090100c184041e00f941803c489420a0681e1051400e60301c54001c61245100d01d5800070000d4103040c00c44601c1544000001e02450207400208070301100413070140c1e40500c000320020302003c440501218185002e8803103104048602e5242c0c00740011 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 381949532 1250 381948282 381948289
    0x60d0807171c02250819140d050108070e04021c02013c05030c0f031e090a031b0308010b0f04080604080d05100605270301050f01030b0c160212010b 65
    0xc180c10620415400708600310000082d4204e480e600310991002110000b141d12200711600c1401c4100b4800e0134603036030240380148510745180c039a1a0709544540c86110014003c00900000c0c400c10060344561440440c605d410010798500540e4010320184005150100100006001d88800d1b4140300100c0441d50b07044118103103410880c9040400f1103011103000c03145011b00700c000545201088070900800c40c003503000e402203c00c018029006180c03203039031315501d00c1e554400260b011441d4103592814410003e5000a1034000c0c50b04c0b80d180c86410f100c00f185007002c4920703403000150020b80313020010401800034400501c480070b0381d0030440d4902510303030350307034a141400030360b4100c0d08520009890449103c4910a03a5000750905500d40c92151800200400500480e00743c04500720709400307040c055131031011500394a850301400a002914005402691005d4248020780f64100310600144210410408490000c0d5158509907041203e580a1040404143d440154070f990b07117000801841d036 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 381950782 1250 381949532 381949567
    0x6070206130f120201020a0b13120203030105101b020f010e060f0d1a0307030b0a060e1501021011160501020d060e0a060807060f03150509010914060d080717 69
    0x34800552081d8a20b80020b04000c010150b20520481281c66103c6005030380c0413a40c559840d07004000e54007140c5421045080040b5540700040c6100030060404c07010b039030040b011f181218422900f550900e0f4409400759062141490090039481104c04500d00500e08203080d80c07403400303040c50002c108212640110b280c60780180602100c1440205406c0d86a109074010400c0d501000c500340ca2448050101095490b0b500b80002405e5110341c2c0c0008444400940c4500d0040882813522001030900d00c007800c602480382201036005024a2000da00c0c6180c2e58040c0091001c652a00c075480c0900007400c1c1e40101018a000300e0390f554081007420001003140c0520000340460380c09d140000d040038400d44003122000c2c1d00140305074101c40d10400502c0d80000d1805400c1c00740d801c01141c0e0303070312501440308603c065400c6254050105000407542502c036521240110b440c4a4100c0143e0300c07a5000c1100401c000103000700981010800300001441c4004001e1040c18180c01003410031440304213424590 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 381952032 1250 381950782 381950797
    0x90503241b0a1d060405030a02060a03020712030606020f0718110403080a2106210837020609071e09060608040c050103020702010e0103050601090b03180d08090a030c0206070206 78
    0x10401c034550880c2ca5400c00c62560040c100b2544d41c0e00e0320b4030306004a0f13110003400001907c50070000c030302041c400307009404030340340300d540440d082011007220314015008008501560006200d81c104608200c40c00040c403100b070705c200c0710040345d440661126441c040c20280d1008848c2070000c0c040003002503d6200640407404158546400c08600c06003000c146503c14050040c5c80350a08500b002580c2d800d0002d0302c03d18041c40300280905680d820320300e106101d2a80300341241c6869044800d078105001901402d001c186003002900b040079100c0499466038140e4041c0380c0c60f044094104500341e038800d8019400d80b4aa0380310069982e45021b50402c803116a03100ca0041a480c4042200304860b202601c000381c2001d003011810203905400080c00254051260b034103040d5100041041c607801084100000c1850364481c40e580e103480743c61441c25403454040350381c8a104e90003030b2200e0380d4021070a0301d05c41c1f1010401000c952a6984003100c00040d4040181d800000c00c101c26000f41c1c4a0070028080b5 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 381953282 1250 381952032 381952037
    0x80f01060e0c07030806010507170309010c02010f0212010e09072111010c1211010b0d060e06090c060715021308010c020c04020f0702090606121303090503241b0a 71
    0x2000e1a281c0c4000d00128001d00041c2110020401d01c40002c2e00551443c0e0084002e01c1c01c44c1c2c0b200c0d400e151001130707241806508400e242b000300c100310200c00150425070040d07410f03600034821480c0c8400214141d0188510620b0311840d03c2c00107100d480d0500420035403100b069421100c5050790358140000303c0001c40700e035188886081e15400240000180340c001450740a03e01302c00d45c40c1c3c1c141c840300c1561203401c40c22002c2000b407c040d07880103142500500d500b50fa00030017040ba80c020a290600c001c0c02e850584107042d008180000f0500d07580850a10904900074190310f1038070021b60350380b51402c9209143c0a4019601f07104d5100e074018544468400303072581d02c0002030300700e80e1100040e191401440071140308500401c0000302d00c01c45c00c0240c511880c4d0648101c03140d40c03507000c000f405500449805090780341c0c03100d0030491032020160b42a0407081c080d4032841c2e0b401c3c0c3c90700c00b415120102c54503000310307202c1081001f0010b00112034007030764046201460b41c000c80340e250302d0030035003a440010340400 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 381954532 1250 381953282 381953291
    0x130e0601140a0f05010c030210050a0f06120507150c120f2304140409050307032003030403140702010c020a0b0c0115050a060f140c0709060e060904060b010504080f01 73
    0x3480c401c050303051061010464a0300c0b0440d01e811900000c0d8000c500030181048a000b0100c0c08243c001c000e4200c1710110440103005a02c1c210000c0c000800040440c4506c4509102c0c0000700d00846840301106c60744c010303000d031020600f00f2000fa00131416a0a51600f004042c485a0010034403610016454030a41e03610b030b4019119814000b048031008510600380c0080d8001090541c9070004225011604503654004401c0000400500100350105007d401400009542410540d0160304043c482041170405d01c40714042000300c60b505d0001f1200240070454500818000032100800703801070310300c1450040c4414031981d000c5100c201c0c180e84011414100480c111030b40110a025101040b444400d0170700380d41d4540000078540712a14402c04d0284980f0500b10240303184200342c03207506080e01008165031023103050001da070313110010310a400c5000e00c0e00e08040f0710b0004a01806009450050000d5402c0d112911044010100090741d0b9052040400c800034030b425080c0f201c4128602c44800024 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 381955782 1250 381954532 381954539
    0x2011b080a170a02160318081506100f020c2e02060a0501050d0b0105060d0e030c031c02070f0b060109170c09070801050105040b030c0f040b2a0c0906130e0601 70
    0x9070071000180c81c003403e0314014098800b460074003440c80421140c05140c80c202e800c000100b55211400950840c61681c0a4040748203400405002e4560140340251001500e0240801d01200c0b000075030823408005811000c50500c0a16001c000c0c010140b185070301c0c1c40d0300c204d02403e0540014603a201d8030009a00306c0420010045810b104080c0188000d4503050300b4104555100321000005010700d5101c1c0e4004120304e1003401d450f9000d0703204282110122139a4001c4607800e81d130389030414542c0103002c03180541c0c0c001c03a0031014000e803200d00c0c1d4420210040c0744c1e100c1daa5562582c44c002c05540c104030007400c00181c90003000700040f5480b01800081c0c0003401f001d405008010100030508428001414010001d60743d04c0412201182c8024413146c2d1244c0302d2041d100310500c1100343781303601c0c1c1801060210300146044018502e182c14180302c55803062111201d12510b50300c1c030858982541041d8a420030758180364a6059004100804808440343e481d00b075402117030f10884d0b8501580e8000300050 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 381957032 1250 381955782 381955817
    0x1208071e1e02100608120f1606091a0a0c2001090203011811040c0e10020a080712020d030506151e0c07060207080102091e0607210905010c020a0302011b080a 69
    0x81d00a0403e40d400340165510848280d5010720420a507e00d43e1440041c0e01c0c900001c0c0708503040c003c2e9601100a0140004030700f42541090140c20103045000601008505041c2c018071400d8140c941a444081e1540b0204e0805040b10518000b490040d5494286c070380c005903420301c2210700c1c50300004104a5911840d042c040c0c6c1510465142d01e004510b060700d0102080c0e0881c04c144b55400040b101c000100710165001c900b003850394075006000a40106469081240c007501c0c400b806000e035402c80380e20395202c5200300c05556040d40c80303d801ca104400703440790008003070300207012156505c40c9001071201507416003442a480030269400d660444103007401301c140e040c08240d004111003002035040811940000b40c0d120000b04003c800a4a05d00044449032075410aa030302c100d401210604042540d00b000440c2405490044000200d41030400b15103980140196500981c000c0d002d40d07140d0f0b003180e00540750700b46000710740e5842d04e07808405000014a050010003000f0103598410900318880c2808 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 381958282 1250 381957032 381957041
    0x637020c0a081509030d060b030403170609010e0a0e030403060b09060919020d060e25090806150d0203100209040b040902030307060b041d01091208071e1e0210 70
    0x3100d00c50300a04070200a140700000386055240b005803900c10850300c2c0c4001c00e0f0300e10b200c2d019128600d42d0400d880005c880c4114400340d8462402602d4482540103602480b0050f84401c42e0221ba00030502d800601400201c007076400d5021740300d0080000d514803684c84d03892135608980d004031103460b194a80b64036181440400550040000e031081000c03401c003408008458942004007480007603011400754051071040c1c210800030619080203494074100b010000c3d420980c14001060f002d48040000019a4440c1c02039104840c1100090009902c40e00300c010088911040d81c541d01c40c49000b40407000d81c0e4288808607a0804c11640140d982c190002800140c6400000b090b104e10f00d08602c10300543c40c0070080324079140e40310304001400c0491800240040001600110603c4402e440c5032164810561001031028010500350411210103041280c1e4410100e80110004e91540381040101d5008034130481003008d03604200c080b001c003a41c600400c0c41200d849400c010f80c00300c000326400030b02c503114 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 381959532 1250 381958282 381958303
    0x31d061602011e020d0b100309020316080a0f390501020304031101121e06090b09040c0608040f051f0b10020c060a0908010e030418020a080402063702 66
    0x74020402480c414102694280e01508800d540010b84101141c1d9254055408500c0007004024030800c1f0300001001401c8002d0200d0003031140c0710701c591240d40c0c1740ca0420300315a41d001c01001854070307a50b501a080391100d40704417240403948030801e18103030403100e42c4101004c2d60400100c0c190a80141c4108076085d50380641e055400c20002070011802407404284141420300305070062148000e1414020050b00c20185a101c0c006990340f5074000c140e81000044441d01301062001c4004c20081056040c0181d034010040d100303d4000b001410b01610b91160300038010007225140c1001c075282c207030400092001c4024440002c03102172204400f14481c9100302d0005440700345014401a201039a10708010111611178800481c560b601c0611403000f0074081c1c0040b20080c03015030010381000f17580c1e030418020095001e238411240960314402c0d20a0301c03500d1413941d40d40c80d115111074082c48501da000c3c000411682c2c0c10003002e00384550301c114000c1140911007040d07101180d110350b0001d00303004640d074 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 381960782 1250 381959532 381959537
    0x8010908091c0b070503040317090c04060911030f2e0510020a0c03060e0a050106090c0e06030c03060906040905160608010f0e0a020a1e02030901030501050a0e0f040201031d0616 78
    0x4503140b01050030780d45000d0380f000c91401d1650b0750351103505080d40e1071014004038248401e44002000a1040d012500c04c0e9180801e0741c060000720749a2904500340c035204003103c06c4100d03040c0001807a00e45080d44007a006151507481e640a4403070703400e19407500006c000c1b94100301080d061082016040064095007010343c00e1016080c0c2a02581c0c2e48800300d012440080c14103501c440c4c0621180506008070100390707500038000c1059903034034480500900050244d010100f00400e002001074104002101d00c242540c0300500c2ca0f55440c081005140b2001500190300030303580f9612100015001c01c40ca042841304108001e140f20710300b04000f0005141604604c6c60440c24000400c60181e17a4004d40d40c118440400250315108014000c9810030a0446210442141c2c510500000781d00030bc003d01503210281e03000d110701d0f070701d420500210b9802c6110380e40400d00410005154110303028503041d0458414540801c0350f8440d01c1c03c1d09040c624002c40040c1641140c400d000b01e0b80003a0030011300c00000390 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 381962032 1250 381960782 381960829
    0x50c01090815040203010b1009080c06040621020d0501030b0405100c091202060d02040315050c04050a1e0510030c1704020d080d060b0a2708031804060801090809 71
    0x505072240441403014038030505500c081011542c01f9040046401400303040c170185030074400300003001c070903c91045601e61302601c440000740e0b0601e40d0403241900e0b42601c9840704200d0000c0038044400c405c20301061129424441c001e4050a58000e00d802940268010031540c14141011030900030b161680b051903915016140c010141c0021246013152910b50400c4000449400850158420a41d000032200e1002802104000340310604d20510f0b49000c00c1001981e50300c0040960920840c01443da0010b100482040b46c20410303004c5100207494610780b55140c82d954004038505041c0a10000d01103600c1d00c5904100c158807550001d00b09404189000d014141600483e561803004040078196550004440442c814190803c5000300554500183c0d10000740c03000a152007107503540200740741441c406210000c002c5208132000c3d941c0b0701c805989800306650004007410045015140c000c1c0c1c803000d00003440070080c031821942a0052440e15650201102000103d02c2902c00581c07004000 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 381963282 1250 381962032 381962039
    0x30507091701020702030d020106081527030d140a0b0105030115080711032205060a090b22090510050306070f03021612020c0405071706060f04080a0807050c0109 71
    0xc154140c04460320800001c040d202a0044540a4840d041001e5050b2080307151510132540e05510002c200e4001c0d2080c0c510003a0031090200103030304140c5010040e0207403203c1000f010120030040c5140f030b8500804881c60f043d09058880255207403200404d60500c00e0008201c000f141c14003035001000404d180403480c640c10134a031441c0010703c010000040181000000308020f004041411b0011444811070f41c5841038180c0c000c03404d140700d418484811120100006a60404034240d510016054403103e410500309140150320744c02000782c04109440300c44040da41c00d412a0300c5000945010003020a05143c406004100c9040e2a03110038000d0307205004105a4a6110b02c4544071503406150141c6e55001da0451300d8006200d031000a4002e140114901b81c009800050849c90800e0070745050105a680c0f05058a48010700c4160038008110100014071a00c0c00d50020031410364a421140c4c1055180c4248034948960004100c404c60300015071181442010000340440d47c8007460300b50b880906 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 381964532 1250 381963282 381963287
    0x2003040302060f0f070c0308070507060c0302060a110412030509270f041502030a020307080603010b010903021c0b100303020f060402060703031503120e0108060306010b070b090715030b030607030507 87
    0x2448101c0940c0e100042102032604c0000000c03601025007241c1709540305a106e050182580e80190802c60706403007205400104036020303d1030342d049241c05030040c1c0301da40c0d074152071103011700420700e05d1084602040102140251031010408842c82c003a544241d1a58594801d01c10800b07404d180d010640304002c104002d5200d1512a616446544174070420581d80f40c615006080a500a1145c80c00303c2c000710801000c04103d074091441480140c0e2130000646440c01171500301d8195000060004800704018005810034030740441407028517a0f81c1c5c041005031900c401e04041300941e6454050301588000300141a8100205103d41d81c904010b0899410700354001401445020401170a00d5110860051440c241c008000000d60300304400001103030320644020a0010030052150110302c0c0c481c003140c05810300141c2907040c2c500c1120014607104c00c4c0c0c2c07503091b1301d054010042c4503644216200461502850b20b0200400c01950f00c01007240300f1514100341c102100201070b80200740c0340c402000071155 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 381965782 1250 381964532 381964537
    0x120f18080a080a0e0d03110c040501051c1514060111010204060504061115090105102c1305010e06041709030a140a230d111c0c0210200304030206 64
    0x540c000c2ca850b40c0c9140c0d955013942c0008005040c16441145000c4d181c1c01e154000280c4160300c0524810b4450050041080208031070b8207000c1c02c0e0300070030a100c03d01c08440215518035005401240d40c18017148411480d0816120800c11b456690140c501c180125945c01541f0181c2d081040c02c000e5013440d0030110014194000c1e489484204500d610040d0300410043c850a6840400c00030017503501c0c030b45107824a0207040161600c50345021401030000342140c80548480c0000e0402215102c010081c0c00141c5030300c24003034081600e204503030004c00c0000e0024400e0300543d024000c0504000e1900e07080c802820b007070b01c0080d40740400080110f608103a0b0082460f141c4290712050f004c0d44941e50842440ca0140807640040c10b0140500b80501402c4610446405055403102110501c0f13030001021683c80d00b01004040855000d1401010b2900322078102c684240040d14000f0070605598000606c00584d110b071600210b803501c000e4902c0103800508030305150304658011850540342da0701241452 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 381967032 1250 381965782 381965803
    0x1a0c030a0e060403080d061e0f0909141e0c09090d113a0918091104050a0c09050a14010c0618120806190b031003120f1808 54
    0x2407440ea6024140c1d601416580510381102c20292604401054040140500d002d00703401c504480b04460084040c4c840721034180ca09080710303010454944600840a04500082262502d44299583e50302c21810085e4588010a04400c0580156014080e1341010641c01c84035001d100900304000c140c5000241c6003078206400d181848940780c610680c02e0400c2d0840d07201000c030240c0c4c0c8070840c1440c4c2d000e49450084403806818500c035003181c1c1d48242c071706201740c0c4180250f000210306005500e815680c00007036110f006042c007a041011100c00107048590446621110594820f94640511342c8002e03d407011700403c8d81c1c04840c59040c0007600c5a59080c0d1230200307040000d80090041041665005411404030324a586101c040c0c4626000b483c4510300b0f00f46200054102001601d50302c0d00c0340b01403201c41091186070010a041620611240e4002442003100c41140b0b4800000102000503a401040c81942c0d03024802e401001c2c001c001e4a0700302d100180110b441d860a0140d0782000c542d06204 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 381968282 1250 381967032 381967037
    0x1060f0314060603090a050d0e0901050a030c0e0a0b04020a03020a11280609020901030503040608090c090c0903151504060503010603050d03180c06081501020f3f041a0c030a 76
    0x2a0f50366a1001742c540b0300c8003000208180030b080684174405c1d03000b00d04c000c56410100c40e001e032507030788079000c2c41480c3d00e441c48050908802c01ba003c01c8080211802240c0106e0200c0e4082080315203c0c0c0402c0c1641d12070002c1900080e400a03020422030360080a030710780e007074503c0d020b40410030080d002100e4000d031a0243c1d041c103001003146001002342d20f502c00c101055010b0030a45242da0f45e42051512500103120301c0021840000000301030f118003141801e11103030001d00700c8120f5216800300007800d41002e194290036109944000d00c43c544100c8103a417003070703449109800b04440694240000c1e18401c1d4440e034082d07030607e0001d000042010a4000300c0c02202d20b0000f1394508070084080381140d60080c007500220081101260503540000064410613119030145009080f400c012640c603400e0441c1d0241716044003000a03150140b10030b032481411000d01c0f00c204024841c4500c3e641001d4151494022034100160030026044105006102c0d000d40f6540c441c1046104800c0036128410003824904 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 381969532 1250 381968282 381968287
    0x61b02100302181e03011b14070201050d05090a0201120b090103020d02180c0a1803020f0111070b040f0f090902010912050a0f0302030c120313260a020601060f03140606 74
    0x254078007110304440808020141c0714001c03560205250b04c8000030094074080d50070041140c41d155004208156034041d29a1520058540c0c10072143c001d402003c0100e040010030090b408420105010740c40c000d45e000000703480c1c00e10786403001421181c0ca42c121822064102280a2115030320014650304494042e200c0d0208400769100081898000c041280070300da01203014846092801d4000c0e180d00600c0d42c41e0781e6107565002da4a4001c00c441840007d6014803040b150180f03035440f0301090001c42c9203400c216170700a610382442c0c81880d00a81c020310402840c0410400c260282800c1c080c0c024004c030681002401c4172030300020580d11580c010003240030003980810040140c1044144020758000c8100006c8000e00d26000792a94003102c2c1c1801d15100f6103a0143d82c03110210308807030041c0c0c10481a40d000c01010b68070b0082040034072421840c04010780c0410140b015201c0020000640554090480b0350b0514802400d03480c4440e01c0c600806180076540c01c1d422001c403100c02c1e0041710450300c664 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 381970782 1250 381969532 381969547
    0x603090507090e0601030b0f04080d02090a05150717030906010b0703140d0b090a05060306070c0c0807030c030b0a020301050105271509010306050904050a020111030c070b04061b02100302 82
    0x91414400350320031032602c0d2038041d100c008141c0201e4407a040e68071a9000700380030384800013003010202c01a42c020b894200200100e4807844000da00906644801401c0c1c12001c0e50b07502c1c0054001c0c0c881c5041d0360f0b10b182c070001f28074040181c80c49200007000d06240001d07065090007900596100300500032417041c56000100e840174103004a04122817401c04405150351004e60055010203880d400c0340f443d008403184008102080214000e452160101400030261607a8904007101d040c0490502524200d0020401195118060220740059030140c084507444a145140204001c000140444401441440140703c9603038001c045070784143c0909036811030340040c3c16124076140308040c2c1c005e034042141920001194604405402610800d8078100203165498041c404404000c58000f071503600030041c641c0040d0701580190352034074030341c8007140d08254000c40702c0c0e850302c6640d40045804d60fa02050401c103180e400854a98106090030400281c4290342d80440d580201110390787c42803580110303800 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 381972032 1250 381970782 381970793
    0x209180f160c050f01060f060305060f19050904110109050a0f05040504030e0319060c230a0201090f0b060a060507081e0c01020f270d110f0402030703140702070f060309 74
    0x3402858100c001c0c1d070a644444c400c01c5000b003a1a1150701424011201c0001d81c482c000d100d96403141c1c0c0c0241036018820f004d0400c1000950100c0d448040c16800000080303126280c10141074031851040002d000c03a0104080050311350700c1282d01c078500c2900c04c401c051001e011120140b10845205980108045d1924a0255810011548a0342c0c03d0300c110460086020728016440401d140203860400002ca28617008030354254001e6150f00004008603441484500998014080c0611074400011200295501c8400080c0107410039100b40c4040700512003545400c2c0307020350041290b030400c1c901e0944941d031500c0381c60048200da080404201c000311076444040c601121294240c901c021903039940c82149003c0c2c5a0486281c00844020070b040c0010340c1c3c015041a407449500040c4040303030441c2c250740c8112111744862440c0d5048080c426940080d501d484c0082c41c0600501e44000c16400030325429841c2076040140020119800260104005549080e01e1000d4480740d01e40440e03100c1a07410071 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 381973282 1250 381972032 381972047
    0x60e0a031209021c03020a030306140d080f04090204030804090501231c02030708030715201602040501030f020418210c0c171c170604090b0a0209180f16 67
    0x400d8407140704c0283d40d070405502003040d40710a03100303407801c014098880050300c80200d04500c00c07541001101e0200404559542d0142c080c40e512484250700d02502c5502040590304030307900488107080082428800360040b80206030140039151058554060817150b000c2d018400c02003079a0194001505400d07140407040c0c000c3c0300c030b036402808903141583c5d0b5501d80d964950250200303841d404500080f415419800b4043c0600200c001180d00e0007026068000301003a51108103421480c00041d040000187c4860150702d0086009417100d118400150051000380e40b403501c0f01851070310021040d00c0028003a4240c0350701a0709008080480c2e086400f1056904501c204400b5008443e06400025103101c161000c03540208040d0684518101103009405200a020f6044001c42d121000f502084030010041c960700c1305000308003040c4100240c0740c285200b101038520310a0340e500080e1503071031804d01c251445850488010b06807070500e00300100102800020b0071690f92071078841072044186100742c05 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 381974532 1250 381973282 381973309
    0x300c160605090f0f0c060703030e0f0d020309010305070e090103060b040f090f0c0b160b0604091514070e0d020409030509030d08070e0d03120b01111603060e0a03120902 74
    0xc00036401c011028660390710803c20301a0720351140001501c040e9201054011110740c002c0e01550500b41d441d5000e074050150014801501d101c0d4010605114108200b8002000b181d600079503940c507042c100040c15143e000304064140584603034240368540300c82758480c0c1143c1c0c10890003d81d2500314000a80600880300381241001e0502d400300080c002514103c18101b0300c90451581419600c2c01194003034021070006e18400810181004d011640d004681e075070064000300002034000d02d42c0c0d240220803501c0b0702c5a0401c10356a0001155800d0b26a50b0a500203005050014140d1400000074510712040074009002d5601d484d007503020540194152001c404006040e900302c1c08580e00000c0105508442c00c100050310545d030041d843c20044906840070f80c041e40d0f020000d840d10001c00c3c000d01b2000411078100003110142e0110a50b00703000245000249071403d04006145003400c0080d00c3d048401c40d0030701e406c4561540d000a8001405014202d000c94000c500d00c4400d00000e00102c1e02c402 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 381975782 1250 381974532 381974543
    0x6020d20070f0f050405010e04030e150c0102031f051e1504030503030f0a020307051621020c03070902130e071101020307080402010f0f020c012012300c16 68
    0x6002042c411115041d400507210301003503003141d8554803410802075810a06c941d0072500d1201e0041400b09104041031400c1c0740c00a40b102d605a81000110306550b07203e401c0e2058a65404400c1c4035440250102e465942c0500c0010923180a0038200040c0460b1240c8140c0e10000c0d01c45043c441711a2100140d10045454104906445540c0d909041e40c0f030b940226402580200584c0c0040c0a20b410351090b28010201e6546090078061000c1c0842040354141105894003089119804003483c00d0404100403006554041c040e4804500300b41881c207a03a941000c0c4025006102049100c1840c401100880701080414006520382030415120841c00911102e0103500000800017071680000365140514800e0365103150740c0c00c03695012222444503020800040c0c0200c0410013130756118640c0c044d004182449a11400130044440501d4801c0c00320180e151004003044040a000c041c10600c0310401501807086440610108000b0398158000d001d19508480404c10502034001012030311805135004 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 381977032 1250 381975782 381975793
    0x4020f040f1d01140903040f0311061c0f0e030403081206011e03091a0f0609070210060305060403020c030f06060121050403021018150b011715011806020d20 69
    0x408907003c0c0c0260484465155130040106661800000845003259000310a0124090451360f801c0007210700c5904055101d002031000f1501541800400040c403400b03c0700014003415a2010076041d5048c100d80c01d26183c206004c2000810025801c40310511543d51010f04580d84090040e941c10611001841c400d183d11140d81e110590154040740e0081e024644038240c02041c880c8a40b0400710858080c1c00c190010340100e0500d05020070031640251180c010340d2200c20b00c5d603201c81b080b82c0305540140c07402c1e070048041c4030a05405000c0498503003001d9001d07110031039040380701503aa04405083c03941042040c00c0c0c2c219030103544580c06481000e003070740c042c4814107250400035503441c194000e800c0401e18081c00320440042011260078160303131042d518003010100b01000002820321038211410320013071429030102c03a441088034621840d00400403039001c0300c3c40030005040306170780340260358a003190355400d0145035000928000741c64202d1900400d012148094440c4049484c802c3d0074003845038 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 381978282 1250 381977032 381977081
    0x60503030712030e1f060506091f0201020d1104090612050601140112020a030e0c010513050d06022b0e0114010b03100308030106090911071101050c01180b0906060904020f040f 77
    0x190080d501c1c83c1400400601c9610780b520100001e0f841542400ad40c4001c01c1c8004c40c4a1041d100032072a8044a540001801c4c140040742c441c00342c0d05002c0214181c4040001e0501003860907109510103448401504807405540d5a42c2c0e5070307501c40c180220070007513210500f0f40c00c5980c4a0070218240c09110795040d0f40303c8900020160107003071518400001401104040c061301c1d4420700591355001c0c0c20013078034001c03d498501400903010300140d083d10500e03000c000c9001c111342424110403510b4542428000c40540c03441c1c044013241c20154500340c2c1641849900c100c801007160409042d10404090a07030f036070711a000754000e402c8180d031006005400200000440d140c00001c0d15048484012051002c41d800070106031861259400c01004e5030302c41091242c865103d000980052642e92000151252036107200d121444900c0508441e043e40300410441000012b000c0709410040980702240d40307081070350020f10551034150010f40501c0e610700c00391b040b201040d0803040d0ba55448142440d8580721 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 381979532 1250 381978282 381978313
    0x23030408100209030d0c0b0a020d15080309210307080a021014090f030408030a081f080607030e160e060d061b030c0807021c1710090b0301060503030712030e 69
    0x3c03124140302e40250810308140c0c034000c41002003541e90152103a071180d60380103015030081d0442d1a0070300900369a084c01000c040010400040601502d500440c0c868802c0d20400491105090f22038421042c129110015904001f05a5000340d030b0280141d501d40d040840102d1618a81e2041c030100075045c544004e054a55410381540282144002c0e201c404d050201940d0341c900c00c610580f10180c4c0104040b1000d02d00c074142d4641c002c00a07000c0403890040080030022850038a4111507103507080b00050100c071607010321584080090a8010701a49a1040418442d030282c4c4e00c02c40c030150a280c0001101c50b550951060b2200b5444503040003106d0001764426815451445e160000c20300c1c1c0110300102c1c41c0120a00d034880e101660051084040041c048200c068407402d804061002820401e483c111240072520304c641600c3c40110011440c10b10000103541300701c82e465010b03134500389003846140c90100840b19001d030017010005040d40030400450040c2120600380d2600e00503103039032172030380349 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 381980782 1250 381979532 381979537
    0x303110d0c0f020d0509091e0a02090405070c020d0b060111030406051b03070b01030f021f0203070314130e04050c0301231609030312110301080a0204050a020403230304081002 77
    0x40e9514051410124420391380c0d946840b11200c00701d0018410300342035103450b800300c035444a908201201124030700d01c090107100c501980d543c00c0480d00031507152250b043c6442216840f695510301440000a19004100e818038141ca024128640800004405034000c40ca400740a5181d28101da40e144e540303040c000c2450304400d0110747c0d070943e0540b003031428400000640741415044035918890340d285540d0307030f05414503c0b002280c101014102d0b00545002020001100b402290050f50346c9001500d0010404003903816200c009807024040c4d08407aa01c012613040a07207e05c82c8903d04251500c0c200185449818a4055815030a060a030b2150502c104079100c0c030807403141c074102c0b0540c403880c01d001c258184410b004c01c0082c0c0c40340300800200e41f02d4411101c07000d0039100d0000c1c09031000071080d01c485d4002d81060f6800c0d48807100748000c43c02c0511170036070320900c55003045023040d007156a0850003000705071003607421210039010040c510005008840090584101b25071001180002c03c0c4042e4 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 381982032 1250 381980782 381980801
    0xa0509030c04050f06090a1112011701050106020c04020702180a020406120504030f0e01200601050102120c0a02041104080601090b090f06092706133008040303110d 72
    0x74040c112110096081c20b02816010b0306850815034032658441c003e1018102c4014040720205464154141068900d40300801104070b01c002145059030400a40701002c0007007aa1079000c980c9490010024164042107000342104e02700e602583c0d0303003c1ea00009541405034035a80950380000003d021b40e03904030740d00070021281070761a094820f800581d846011244103d5002d804650004000800984540d000c42400181410300003162000031f20320521072a9006007002d031951240006100b60368040007610540000031180a14207270650862549644100300001c1c00345413190003c41c45080c840e0240d0303015144880484a4640e5901d8400380a407028404140c0180a4000490384174060308000750b00c03980014020fa1460b4a40d81d807041005144044140c60b101e101e0241810356880c28483d0302e009006007920054601e0041c00c00d110744110a0311090324819011a100c1c0031079a40045401000031b00d410454810380d0707503041c2507024203040700c900e50040800251b012451031042d1b114904030f = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 381983282 1250 381982032 381982039
    0x804180f182a17101b0c0b0601030e010504050a020306060f0f12070e07020604120f1d032d150906130606090905010903020106050f0a0b16020d03050705191203150b0a0509 75
    0x18174290300001d500040740c1244100000b500c1810715000304050514544c2c0051041c580003924804040d0030908446060314111125004142e1003410f40c5410800c003504844e003201e071440ea49a4410000e00041040422103008910b040c4020032224402d020110003040c0700e00300118a0314000c0c400130348030f0208031011a030300d1280101e6550f41c40c1c41260301c1c00d0110b00ca40c440025142070740000e0421101950140c5906114203042c0c0c4c03030288405c4000803c0d00c1883c0001201c03041c484400181800390070608a0b554142d40300410948200010304507400450030301902a69500d2418480094800c5801c1a14034030b003000c0201c820464150321813a4a035019034000c00010340c883c800c10100340c824903202c6900c079100c0402481002480001409484c285404c1e14684440c0c0c0d501160320400800025008100041154024003000f0b004440340f0744040c0440e540350902d9035840c0c0d00f00c00c03490f04030300703040580c1c0d145406502c1d040c0307480342d20103000481d01141d110506800002d02a6200780403444c007 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 381984532 1250 381983282 381983291
    0x20c0703050a050709140c090a09020f1b01020702180405251e36050c0306152b0b121b040e0c010c0804180f182a1710 52
    0x107040380b0604c46d0728907450007440c1c100801c0d1200c151151640d04620321440d40003451540014004103a44000c144801140341c4040c1c40d0f207803241d11990703205408500660703140d0040040c200166106811081d80315507541010503141c40d103040040c90312244c0442000e040c00c0074804501034129111102040b6000710180304802c0d9040d00391604803041c01c1c49104c03502c081900147c80d2a41da108003480104108031a105090885100014180c0308242c804118021001060048070f060070000307a0b0915640202c50361411103c106440241e8901c1d081c010324600c040400381c0346070301140e0066042003d0083c8020a803010a044076500d54240700c400c0c0c982c4540d85880d103080c07800c0900804040d10644000f9082440e140e40040d24002d010513011a07462904201c003148945400c0d150500480d80e030f00000844404a400c040c0880f010020500c4c1c01940d20907070300c00010617001c00c92046444600303400c441c042a0400302c200d1120b1075001900345d003007910a001c0840000040c0052844020a018031 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 381985782 1250 381984532 381984539
    0x305011404090c18020d0212070207060f0503070815031f05060a03031b030302040f0803130b0715090309090f02030f0711060a0203060303130801020c16050a0608040501020c0703050a0507 82
    0x112000c410000300300e9044510100504c0380ea400722040040142040503140ca408a4584000ca81c0584080808030810340c0500c003206030304000906c0648014204209031048504010f071180c000108000300304000c400010f1142460b0015000514101504484110014054900301510a4403c1c000303e1881c0400041c042c4c50070650400803aa09a209c20040c0341c001d450740e440c05c40c02c0b4241901807540800002034100c4e00c51400300e004007400c02c0a55212681203070b05c43c4400c041d90b80040c07001d1005024507408219030b101c202c681d101010000150000d061700d801d560b04c44155101804580c0b52821800046000350001d41c49840700c00a402050b0784c8a01081e60000f00800c0011000e610800c0090f94100b00c0d68004c40d04100b009007180d0030316a401203c0351085402e900f090840d65008203003804200070401c82c0381c21a0000f182152600c03410080402c42040c018450304041010030004030b01880000e6040713a5201403034205441c100d40c0c0708e080043d6540ba0240c000c840c54458410b001 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 381987032 1250 381985782 381985789
    0x190308040b1506070303111b070e16140930060105100813050703020307090f0b0901050619030917120106170105012001061e0807030812190c03050114 66
    0x1003002d8900100380c1402c1258a4a0480007404c035290740e0301c088803041000205400401560090005485004003c160705046c0d500904d900c000d0285030b401d18980700050000d9030001d44c84140c0c0d0042060550b150202c840014451560341c40ca00c0e4810418800c20304805201107440103c0c0701a09001c0f175101da6625020300440e0501c10411034009a10040401c102e0401c0030241c2444a00400442d60030700c0d01d81e0002401c000c2d065005c207821643d01c03040c03801d01d0451400713804c4021004480605a030f6140c071000c1001d5116102118820050f1140d4ac54100741c040c3c0d02c1454520b80002c14070540b20100703d10741380182d110012900200c40e0840002400394800c5a050b0341120180d089000544d281c01c00544100b146105590100c0c116980e150704025400d101c0c03407000345641e01d4200c800e03410303800303c890500c003441d04010b0325a0070001007032020030500011a030740d50088103e0901303d56607201500100e0800c5450b0b8501743c1c0d040c0f61018010035407681106045c1c640310700f480f108410b46817040 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 381988282 1250 381987032 381987061
    0xc05010f32011203050f0705031c0b03060601080a2304080403020a27050411030a03090323070e090309100201020c06010504090b06040b06090a060c0c090c08010b0c190308040b 77
    0x10144110150103000d0f0000344500080c0041c0500c41c6003040c1003000540d101800d5800030000c0e4a0261620281250745044134003e20b0302d0070409902611050901200007045290b0003480d8548080e11481c08142a0061a02c201407803250300741c608020381818036255140b544a8401644542c508100c0070540c1c07181d458203100d40c1400d08000e052510b0130f480c0490081c4c00c0040007500d5092803104100002c1d14203022070174581c2d01c01d80d00c40140b242946401ca0342443d0211a000b81d00180407101d400b5008002140e600766000200030001c01e6860074080c600e144a043c500c25040031034172a1034030305290150082d104c81d2540d04107803120303a078860003880101c030394414014000400300d40216041c3d040a6101c0ca90121000c2d0440e45403400a00c0032941224195101c100003c0780784220400340302041e000503002c0c1103e90707014000c0907500c2800801001060107411640c200004140c1c4124030b08010310040d60060341e0050102d007105050190450785c040314192400346a40c000501c0f4086820103 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 381989532 1250 381988282 381988289
    0x912060c0316050702040501060c051c0509010c06110403080714010c14070213050c0d0e0d0804021002030d06090606020c0f0a15030207061b0f1706010c05010f3201 72
    0x2000c1e04503a14210300e5580d02c1ca080c1c807401d0902c40204000c0c405a16a801000e0192150351141c01c5507129601c0e01134a0302001c561300c1e1942c11480c00b1084500790b802012224151424a003c40b000ba44a0811500607c0c55904800302d424000600108000c4040003030581c04c1e000b00c1c0c0d80040b1800c02d217142c40c00c3e940103405c000700107520400718030402000ca001402000d400504420344062042554104881059645041e15003021546408607813075801840098200c900140c890007146d0540545811405040280b2034001c0340c040e004064820025502e0b24400c0000a01160f542c0d2402c440081c8507a00401c1d0060041080b24007880c2406060007407444005444001001d140c001c14111100c2c44a0405c03041640821100000c15803600034080e039280491014401d03407058038009403c00c0039130034803402400075591161000c03821850281d330b4880000c5c209440081c00c40c0c90031030700404481c182d42c00c446190203d2010f5000340c4600700030081a81454100e0f0b80e1441d150a0f9918040912 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 381990782 1250 381989532 381989551
    0x90a09050601061d030f0106080d0203040f090207020d150609110c06040311010e151f08030a0813200a12110f0d0507140a0e0f16180605091206 63
    0x7001048554882c0e0401d08030054102020042400004006802c140360840e254105a448850601800d07905100c4050700403031600046142070300d00340c699500d061281c031907010019070201d041400d64641d1042c642c07036a584442d54141c002c0788100800000c00c00c0f8011701140918140203520f031408440b0498be0421507050080c03009688a0790704039440400005034022554030f5a1500d4080700080168550102504c0c1700d14001d8030b80f8074010580d000218440c07441a54001d00c0402240001104a41c0c5024013440d015040c0c0e80d950445810849150500a005042e0281d8110200c08014525100d8120403100a20f10903540c1c50782c2d1810030340f106c1d0040d103440c0c101e001150b02032429001c54000100c014000380099036458542c94102100d941c44401c80b80c08046208645103480007607071018049008020100d03040c080789050031508020045c00902c0304400d21030180a00444102492180300f01e00b0106a41c0c50b0348005009400614000c0e0142803201805003644070040707003180c45601c112 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 381992032 1250 381990782 381990793
    0x8060a0501080c04091b06021b0906010c031b150c09060e0a0e1e0f15030d05120a0b12100b0a030b0f041401180519021011010e0106080c090a0905 64
    0x9010040244142d19007181d500402c1c120207a1b5101c041034803603000340300c1900a000d200303085903000c00451050501041c401c0e40d40104110003681c000d00b01401998141c40c206041d8a940b0460b40b2b06054802c4005d4000a40c00ca0b204a0200b20340c0c01030854420300380d90f048030581e6110801d80340e000d050003d40d03900402492060020110902d407059210607168000001760351a04c040d461009070580e202004ca0003c4010000640700b44400340000100070b400505940301c00324001003040c02444c956400c4200b07950082208445a60011511a440100341c0e90104c124003010307540d200c5541c018030004030f0400e241d40ca05444c1c80c03980103003100d0300181008116a50340c040600c038264001c1c0115184403228419440200c001d03c120b502002240c40400305d800d009090403854241c030b60960084101c07602040b940181c0b20010a51440685428005003181c40000f103070b0301404088442542079813a1940c000307056800002c3e00c00c41b403407055039580d0706a02d80100100030741c7c009071300182503907010303 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 381993282 1250 381992032 381992053
    0x31009210905120a0308010608060105030406050613060b031f0f0504020a02030c01050f0612030c1b060714030a090b040b1c0209031603120509280806040c08060a050108 74
    0x50810342410808245000228a0b4a60000503a2480c40c00c03000703285a4401d401c0e0008040d0041d102c203005d031606090070300c110300d04080000d00510000b80700418264035540400c0a17602c07a0103180507440581403041c8035003901c804080b074058004a89448030080000024002010361003103a6050307401140c2c544918600348001d1102a602c407945c6081140701c20406081e0242c004c0c840d41c0d0145003690401d80c0c250400408015902451040508440e0020000100c01c03c1002079000c500d1842c216000140b481000300081c0c0500800030b02502251684131400d447c2d0201000801043c0030640302d4510b440d4444c903190302c00d07006601032910000c40400944410554004201248c2c0b10544400751800c2c40c0c18012a092282141c1e610307021040001060042118040c4e10341d6600582d0701d82035007448446400207005d0764040381c12100c80b08482008461845400d4810710103000c40d48202c403003905140c40c0c000d810285900c20503005000c0c0c0404030744050054094903040380d00c00401091807941 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 381994532 1250 381993282 381993323
    0xb06060a050d09051e030d0c0807020a032d0e1009030215090418030815010203310b04420305090c040f09021c0302030406210218031009 60
    0x1000c1d0192041d1143d1030f480310303404021340445c00451401c040036507120407810f45964140d5074041c0007802402203803410040304940c000743c003401040d05443c216400d000101031600c0204080c1c2212091884008141e41201e5003103d581c000d054020360b0300c3c01b110080002c0480f40304600d400002e501000341d201c0300340b00d9010000a03101001c0014070000c1c00c0002c0100403490540411011070100f070010301005411101c41403405245e05080c0091842d0207014840c401150000d2003451181c90b0401d12118080308128034000094510018803a1b0b6454031001c3c210705503a1003001852410343e04071182e50044007105c44181c021290380c0c80d004400e00c2c55003416005000f0040c03001c1580d00c0b800ca41c640547d0798500075a10400f91000c7d00042c1c082c05030043c0420140032244811880849d4203807c4006503000003102c1c11181145800c1c1c1001322a9000481180042c1c42190021400403d01a140d005925150900000210203c56a0130f07010491001a9000c0e860b014040d0081c54201003103428 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 381995782 1250 381994532 381994541
    0x20d20040e1e0a02090412090b0d060602010c030b0f1003090b01080c0a15140a0302090901150306050312030c0a12140609090d12270b01050906030a1113090f0b040b06060a050d 77
    0x40c0c1f2414920b20700e64450003941c08079000b0b500043c100c90f481d110108040c540a10804036020a10319060010031800c1001c180140c0d2010b80b458055241503040d024407911035032081c012580e001c0a01581960340f00c40c01541c0e00d01c200490340c0f081c115448000740004111200b448641000e84801421600400d100e249a4010300d00f420300f8142c0030007203400540d444d0003101d800b03030100c042d07440500d0040d408010300320750745600000e009503c82c00783c441c1026443c809070317540f04002e070f1030705540c44100348811101307004010b00240e551400e15140089101841c45214411041a545a01a9078510114583d501201d55504000c10180324404040d489203400220000c100000c407040c0c90001c40b00901260307000c0f12016902881000c00600440c50804220b40e0407100031002400c10304015180c400c2381100700c0030311910403d500702c1082600d04040e0030485a55400144a548035045410180f000f0102241e046490f8955900010030302c1c60000c0594402100341d5481b52700f803242104802c030040 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 381997032 1250 381995782 381995813
    0x70b0c070f0b06011101020a110106080a050703020f0d0212030a0e060a21021908040203070e1006050c070312022401060c03080c0c0a230307020d20040e1e0a020904 72
    0x1c61903034018041c01c117090008128040c03850340c840f5440e005074a1050700b15262a0062800d030f400443c00200494400141141582d8045842003010203400c80010111040c6600003074014581c00040250a1804000b418101d002500d0303140d5800b0300c440820175140f0a000c1c0800200300c020001c0d0248031500c1500e16141c0423401c100601d030607080300d04511903010850428002070b000d04200011418107100100003031142d44802c1416040000101203404c0040c0641010480c02050b141501c1d10204151340040d40c21820000200c2260300c1d0094444007090110725101c50307031106040c640c0b080c40c0f0b0201e04032041c5607121007825143e59821501c031040540301c0103540109000800181600b48010102d085c410720000a030610b01c99014241002c0c00c89031090310b60010300562015855101d8194451035021080110340c1e40c0c00f0150350f54040d800403550b908507207491055550b09070300080900354081400052100070b0090000941d454003041c074001c3d00418200040380000c1c21006181010 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 381998282 1250 381997032 381997037
    0x106030e120c0c13140105010f090b12040b16020c060c031e0c1605030601050d0203150709080c0f03030706020306150d02181914040b0a0b070b0c070f0b0601 69
    0x40c8910400800320b6004a5038108842d00040c1c8440c55900d04492208070341460800c1c2071001211605603030a000c10140704580c1480000b184507403c0600c600201c4024010610307619485001d0800c002c0482c10040300c04850142d0f030840410794040c61113890b81c1075026036500510718080c01c40c003800b2041e080070003280c05504c01800f0703d4020781c1444101110f960a03820310a901ca00704400307101d1611020241c00c102c0c00100303590503c00c54030082040f9040d204143c8000441002d5131020074602400054103180d050580010f00c521594008050001c80300240c04850032200e00070100303c641481002c801d80d040e801008000c0004510760091a84440c00070580e60340040c0001c5030003001c0d03111500e903448166002036204001401c3c2c071304c4d003880361070161061301c4070001c291405008088103014a42c940c840d0041a56025a12504030291041e000317061084802d60786e200c1c2c01d026800c4072000b280d1701460100040d10040030a002d80701c0e9583c106100b000c2550f0170b501e80746400180038004504 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 381999532 1250 381998282 381998293
    0x906010f0c02060c1b100e1c200a0f080c090901060308040303030906051803070b0a151212020105040209040b070905090f0a0e0705010c030809031306260f0106030e 72
    0x96aa08005803c400b041503015001d480f40f40750410a4420200c08818410810010201078082d4003007408008510181d40e00b030441c40300ca00f100780080c1c5030814010314000008000c60b00c100180c00c080c01040303274152004c0800702c3d15400707011200c4050307000d002600c0d03000e035588401614111044070340045442000051140e180d440d4107401d6802900180d0210ba29000341030700b00030291140302d60001400041e1300700d41e040d002e02141c40e4802c18401610b2003d4060104403030000030341c01f204041c0d404605030701031b2964415015612212442c01a03c1d68503e40c140d4000309401802040d1003180e0050055640e651107558528080202501c0c01c400c02018020101e030940700d82c1581409144402c0d002402450b02c0204001542c81d1148040050380050b42c0c10082643c200e03030340004140e130505081006a448161891540c003403500e020f4220788019200290203600070078038442000c01000e044024003c458801d2070044000d943c44500760b02030740010400d10384070340d0201c064a40b0300000d468 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 382000782 1250 381999532 381999557
    0x106171305150f01051005031501030b040c0f03050c0a0f1d03030f1911030315040b06070309031703010503030406030f090f080306040b0904080a0c03110304030809120a020906010f 79
    0x2d140c01c0e40c20707000708000185441802460b210600d000ca00504040b40c2c2d01b9101c81d48150003d109020260a0031101280048600350507030094000c1c80074040054002c020400201000800b440c50315421b41011034600380100b00390700c4400d003c45030302040f070b0f40781c0b1600c0f03481100c412180a9500c201d4041d400380c00207001f8003190741c00d03c02400d407000104d54050b00c410300d450401c811602001c8201081c003100403c000f030070701c8d4044150f1f64420307500e081004062090202280151400c52603480d44804000b41e000100760300007001c002600d00030f28140d50000d492081c10f1203144000c0c041c00780d0680c002d100800c040d620941140780c2910203110080340b40c02c031070351703406610703d001e00000c0b5058600031041088a0521740315400e441d10b01219040780a00b440d888411080c401c1c1901c210400403040030090900d40989007003c11a1076290850355525501c1c01d102d4404c0d002020618401c040701007502518900004075044020340041c03251410f503ea0400540f6804414a82001409100035812 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 382002032 1250 382000782 382000793
    0x3120c0317070c1109060a1701090212060a0b0306100b2503110d032a0908100230150a09020c01150603140106050a051303141501061713 60
    0x114062061629443d214241c94074002801009402030240121109420810a41d68003101d00044a0070b558211400d41541844140035080c078150194001d1068010b18800100008000d44203000c803000802007030140174201030311200240e801090a505000b802d00c01d010000d00140b010140c0d0003141c465403034203901d0580204155140513404901b214044240c1d8030414001101d03440560328081010034101490222402c20060b001d0b40c5405101d81c9008059000354415000b50012500310740f0003802035443c180296120b003201c01d0400b0f001d20a806100c2a800d500303500c0c4084040008600b030360320040c00341400c40c884507681740c0c410b003842c13130010346650076100501e11196540d0005c030340100294803400e01a161588001c080610b0419982d03130b91640100e20a054416516145d80e031821412400c480d180143d4101010142c03801000101700407621a40405014010003501c40310801c034403400d800f441d800d2042501003044000c41c1001c12000c16042070348200803071407540b071a84a42c1c507407 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 382003282 1250 382002032 382002077
    0xb0a080603010f1e050901050702030f0906070b190c0207060c1b03020910090b0a1208030c0d050117010533030703050609010b240d021c05070f120603120c03 69
    0x75807011241c841e0042c02081d090084d1541b25809500a000c039081244000b5540e20a00300d510500a401250700310642e60b1300e13001c940c03800ba00301050569604100c603031404582c0340e43c6450400b407484c04440c4600e2034000300703d030f078211051612110700c8103200782c0740e00740c00480e4802081780c4400e60043c04401642c4442c0854007440e101d0840240781c0742041c00540480310300a5160384100c4140d90200030801580c21b040c0f145682c400c80d280e840740c481c0d43d0300c1103450254181842a01e81000c0000c00c1c04501a4010180380701010002d00c10380c0c9601401c0100341c400c80c030260510700c0a1080078016041d004484400d052400340847d40502da076500c1c0d113810200161050f642c50b0f51540301880380ea26041e91031207a102456540030f400034113030305041e8202e8407a0b070750341d90085900410303000e480300f0008250704ca4184000d0018082844c0040c0c00034074500290f0800d8000c00e15059080082c000140f05a00560790f00030721020b40d4034500b0106540c0c0c0c605000c402c070300b0002d002030201e8140300e41c520f4 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 382004532 1250 382003282 382003301
    0x7051c05061f0617071404171507170103020402180409080c0d02030a0903230f0c15120a200a0207031205030405030306040c02280c0f0b0a080603010f 66
    0x8402214440e050071107451038030350f80250100040915003524510384c0ca0080d540000d241d081c100783c0028504076003a11409298000b0b40300d034842c00c89200001201083d241c8030043d400410103c00e988d1a401501e103070009541004906659100601c01403c0583c002c0404080003100441d0411440c0006002d81c0d016210071118920040790903d07108038100000305422924ac0041c608200800c800105044901d110241544171b4403003c0d16150203651003002c07c5c803501e0f8802d42c0c007540440c0b40001c0ea1001e180102e1402052046c0c801d00100030b20b1400d0740c4c0d8000c0034174001015a110a1104000b03040079004c071018122502c502d107140c03090603a000300b11103e0b403034015004062540c10040c6450102d01043c0081c0a0304004000000300080204d81e44100300b11000140c5501141c801c0b4a40352254620304600c9280f0f0444010440f0b0b481c980742850b40c810040f40b030810f0384501c0c080780c082c005845a0380400505104103030403680581e001c0341e44468080c1c00055140c1400c003505055a100d1807 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 382005782 1250 382004532 382004551
    0xe030a06020d0506010e030a1515060f0809030c150402190305100614010801090c140a1709010207050706051c090b0108060907080d0c0204020d06090501061e0207051c0506 75
    0x1e0080c0260000d0046980c0004d09091000c000800c01d00031940301c4403002070040802002112205d00d006941d4880e401940c017071610500340540f1403001611000c010010035003c0368410f070001c3c05445c40003044070280c508c030002030203100c0c0140c00710000b4490041c200700e0f0300419840d071160308100c035031303841600441c019130040540050850040e0100c661a4022640c0a4a0300080b8160ba03604480000d0446820050018455501c40750844003101e04403425202000002498034003140c0c0825805501d0051140300360385a01c40d10102400c0380f09844004116400030307402088418000d40140c5503500540d0003440900048510300c4085800201080380c80307040c0c4100611002e030b0f04000407a80107150000501c1e6003420310350416592030510a07803008020803006504115101da406a58245031850000d11100e82c03140c20354006000b0902840c0000703003200030f54580e110000e50420804000603009000900c3c141018400d403542a4080640c0c0c4240a8100100080c008c0000da071140c030020 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 382007032 1250 382005782 382005787
    0x1506051b0111070b100311062115010e01081003030e03070b040b04150815040b0612040b060f150904090c03020306090a02150a2a140a0b0a110d0902010e030a0602 71
    0xc4c98295031444c001307400b803117684440c00001e00000b07661041d4443c12010403036809840d41e503040001000b8040103000c2d40c202031400ca0038441c40580b080000c0c0010102600e8856010005000440740c3c3c207000c403041004603a050300204007103070051910509240300a000d4403c52911a05007040961041c1d000c2081da860015080004400d40750b00a04090241d203482c86c52801c14002000c0105010030089102d175984000c08031139981e5100446a04e00301440e80d03040986040c0c1020301150008848182c020002e00c81d4920491422641c3d242c1458101348006041c0310010007400003e04810390100d448821907000800907a80c108a41882000542d008080603904bc4c410300103840707001058050030b50b40501c8140103181d0801607441d46044041c00000c480080721007906008551900c01902c00d240c1165410300201c2c02069544440c1d0007a180042c1ca40c413140f03601c2c0200c0d25124140e900f0f506040c0310b100c3c0e2040494000322a210700525280e20f01c07280442c002801c15030500012034005500 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 382008282 1250 382007032 382007047
    0x60a150503010609090908091210060311030601090e03070308060d02060408060a06060e060a030f021e12100f0605030a060b0c161205060c130308030a021c1506051b0111 74
    0x419040241017501000d012180d8a44e90340c2045001d2480980e100c0d03104148110b000500400c00741aa0001d0007005004690342c0703045c0313081050710a50802d401303806040004904800f05000d03001c034ac112034400031031401140382c83c1150100030103829154030240307000d001000340e40c03010b026002030300194010302a40c0c1444a1343d5000c8030052f610a200340a032442000503503503269003d540ca00300d0142408101c0740340c0b2103400303402417281c1003402c400d90030001c1e01c0844808440c4e000c0e064000140c0c080340c2c01354603000c22500c00440c032481130441140102c00709000701c600c154007441e04100e03036a41c08643da98803002d00c50400c0c0c0000019000d41e91000030980481c41140c1040c600800e910b4100303172400030645d10b5650720382ca401004a0501c0304006036030101c1c410a051040d00654016080f0f0780c0b02c0c1009108240079601011604010000102d031b000031401040c410790508070401904021464030700001603403036400100c1c6402d80b620754102001000f840a002c0c00c1e21407109101644d03a00c0301d1 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 382009532 1250 382008282 382008287
    0xe0604121e081b0c1f030b010c020a09090516031e060209090a150b120c03131b030c1e05090705160b0a1b020303070315080109110f060f0d0203060a1505030106 70
    0x11340c60350300c4c840e40110840d01c10444092003101152490381c03401040d20303003100006a07810f8404640027904404243c2d00050403903040c1e4003239103845108000303680324076021749840303043c00c4001c2c000900341e481c82309130f1000341c9110781b0b081c00c09a9203da0000340c1041e00301300029001400c00c96a01103807640b15011000f181a2269001000e049040d0549003080858145900648001004961505800400b1565405405030aa1192035000c14440100c0442c4106101174000740d11003122144501030010909021900c10100e0054141461005142c942401c001ca01074010303161105100b4200800d403002180e801d000d4030700c580500c12034110760409440f50021554200701c1c040360440300e80304880c507059012003103940007020780c5804502d51141691071035030b038410350744074030407a62801065200700b0600c901e00303c440d000c2c119482811000800d043c13000c0c5209400d0754940d50402008001c5580200758007070f603001b49000d081c03d41515112804028401600640400840d1022004018041c1e = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 382010782 1250 382009532 382009543
    0x10020307090b070501091502131203020c0a030311070501051602090c0c10051e241f031509050606120a06080a0b0a0b0d1a15040f0b010e0604121e081b 66
    0x20301f5001c003180f42c07900c1d0020614001e101030142c052071520003c10081418404c0115003169000289031000d00c80d502e14001c0e0445050307011072500b6000e41e050001d170300d41c010f4040d24a00c3c50000b66207000950307241d08000154130700400c01440014148580780780460100420f5500d581005800103003410300d10003007201b0781403100441540e8000da07010044102c00fa40c01130240c90480703a0340d0071060205400000d4003031000350311344541c04411440140c1000c1d415041607000343c001c0003c1e01c2e0102d417075585400a803401141e50907045401040442482c0310340652581e8042012940080d0668a2301000b500340300f80c3d84801d40c0c1171198107080c07018251451041c0b1480083c112410103800d8a04c0d81c41c0401d40d1981200780d003016090000154a6030145010180d1440d0020f2003000b2000c030b08400d20b00180b020017201030004006181410841c02c00200310b4042e2401040500c1140d5020395640301d42075049900d02002507100114940040c8204010f0181200c04ca07c1244c1c0b03040c0c0c00501a407900 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 382012032 1250 382010782 382010813
    0x9030f0d0e0103050c181c02100906080a0c090501121803020706200c12010e15011e0506031305100525050315060a0207080f010510050a0810020307090b07050109 71
    0x803808100c5028600074403030010441000580d80013840b0626940c1d11039401c000c0f840c0103500061409c40c40b081c0b1503400b00c1c40e0700c01e440c1e60761141c403803d48824014071304035208034050101117080c0520074404d07503001c0e400b00700c0c00c020080c90108900d002c420003190001246901140560311511003401119002007a1134092b42440c026a4000c2c41c0c1c4a0f2810b903908a50804140070300060200c1c402c00007000c0d08160898260030040750110300040031804503020091041d000700c1c00d00d800c00d54814150b9044103004071540200b50a0540c1c03100c44413007049400601c42200c40e17224085041642c00c600e8019280f06201402c01c0d49251010103c4540c2114000c80c00305007005420820031002c08017007014914500c60560b0031989458016005929006180c0c01c045090300c55115a0540d040301500024840c10121002009896440b014080c1c3c0007068054400f8a40080b441c2c4c01c1d144825078041c6a110542c1d10340380e94810740d113402c891803d0b0301103c420740c3c05075101c0350103609004d5803080c142c00f503 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 382013282 1250 382012032 382012051
    0x507060801150210200a0e0906030118080307050c160312080106020307060504080d1a03190c09050916030302010209010e0f0f0f2107061b031409030f0d0e010305 71
    0xd088240310013500c03040900f003003584c0b195841c2a4010144004160300d50301c4800004c03442c0d80d40c5855540030304481c02c80000380d840351a41500083e040d09040c0903034500a550004840c80040003555080e1003604004e10040800c50148002400100c0810618030a9069144001e41071421800e100702ca0a0f040c0c0c00441c10310000c0750040211035400412641d50b240c03c90000130303194a59190600c00c1e032081e4403500c03100505000034882c4c100c1800015200301e0030200c04840c0d03c00846061f43c8071440d58a00090000000c500c01009400d65940005900c50100c40542d00c4070a00c00744602c0c00643c2540003580141e40c0441e2070f03e11541c00112001b003050080740c5a00030701c00b41c4000110954180c00140340a0307014803241610700d8840c04400b031814512407031600d0008021694407655039800d8030803000040c0b1328041c203161035850f4020301b11180da00340d50b4817004075184140c03060355544544c40c03070342e09403049d404440dc220005000d05000d0501c00e0303941c100d203240c13180b000506407000640380644 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 382014388 1106 382013282 382013309
    0xd0207170c010c270b070302070e0708041a0f190623130203090307230d0914040203060d12020304120b060411090a1703040f030507060801 61
    0xa511545650706140550a80040d13070600c2c0c9003080038207130104c02d0031003800100c0080c0000d2074603a019004131010703203688590390342c00500c089074074100084644050108001010071034004c0c1c03d154681c03000d054184601170079440b4001a00581c0010031401303005401541940210004207401c80650411480d05a00c0b0602e0300b0503004c540d0300c02c180d50803090011700c1480c23003517900490712600114200346503030342d940e24500300c005458074031060900081140200100400b070984481e80c2d030f408e04281c1c5070040d25440321310301c0840144101d0041c404c00c1242d440d105c0d0b820381384a400010402cbc0d107200408090f41035104a402c1728501c0c1440c0c041c10820b029002080c540030b600103481c00c0000030004204c0121038000c0c5602994002c000c1d443c20403100c40390112004030030030307024183d0340b400340d82d03031007a110500050b401199141c0000804200403600002600e005003d403006841 = true := by decide +kernel

theorem cover : BRFrame.Cov 381834532 382014388 := by
  have h0 := BRFrame.cov_init 381834532
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381834532 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381834532 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381834532 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381834532 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381834532 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381834532 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381834532 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381834532 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381834532 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381834532 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381834532 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381834532 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381834532 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381834532 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381834532 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381834532 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381834532 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381834532 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381834532 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381834532 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381834532 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381834532 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381834532 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381834532 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381834532 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381834532 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381834532 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381834532 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381834532 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381834532 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381834532 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381834532 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381834532 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381834532 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381834532 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381834532 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381834532 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381834532 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381834532 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381834532 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381834532 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381834532 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381834532 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381834532 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381834532 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381834532 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381834532 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381834532 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381834532 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381834532 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381834532 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381834532 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381834532 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381834532 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381834532 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381834532 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381834532 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381834532 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381834532 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381834532 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381834532 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381834532 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381834532 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381834532 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381834532 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381834532 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381834532 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381834532 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381834532 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381834532 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381834532 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381834532 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381834532 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381834532 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381834532 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381834532 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381834532 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381834532 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381834532 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381834532 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381834532 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381834532 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381834532 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381834532 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381834532 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381834532 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381834532 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381834532 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381834532 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381834532 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381834532 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381834532 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381834532 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381834532 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381834532 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381834532 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381834532 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381834532 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381834532 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381834532 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381834532 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381834532 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381834532 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381834532 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381834532 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381834532 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381834532 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381834532 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381834532 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381834532 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381834532 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381834532 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381834532 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381834532 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381834532 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381834532 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381834532 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381834532 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381834532 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381834532 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381834532 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381834532 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381834532 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381834532 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381834532 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381834532 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381834532 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381834532 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381834532 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381834532 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381834532 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381834532 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381834532 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381834532 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381834532 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381834532 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381834532 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381834532 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381834532 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381834532 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381834532 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381834532 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381834532 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381834532 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 381834532 ≤ n) (h2 : n < 382014388) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
