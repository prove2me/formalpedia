-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2632
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T07:16:45.105437+00:00
-- url     : https://prove2.me/submissions/7b2844c7-9771-4bfc-a442-01be6a7a2db9

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 473201438 ≤ n < 473381294 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 473202688 1250 473201438 473201447
    0x60906121e090c04050c360103200703050f03040501141305100f0608010e070e1b0a08070309020405040b0f010e090c06070203070e2701050c190e102c011428 69
    0x5841042080320041f02201d00f650092280040c00310540c01c0000302c2e000426001401e0750b110020071810131800700008500c0d0f0010700d0285028500c07030f10000c03035000d4961088550511000d41564903140e0106821800280c000522001420340054003181c13a015100b0240000d010b20342c09030040394200107481880d8400411024180c0781940ba04204a0310b851f9221401e0052058216448080070007251207502d010304c1c0e426600088528021460b28000d50110702590400e440444034203103254280b0011000074041c0d20b0142140340c0b00d141441c5031076201c840d03541c9001d0400c0d41c014800003903803105648042c00400007030450550259400d080400f600713442406d451806d0080742110f00e00c80da802003c10300a203070168010251241c100b41d41001c0c0b099030b40152a03030810501c603080c0c6d4800b017141c454100401201146444542d00e030702e03601c00a44015800c0c160ba00980c420720007008295070707800810750300c031140c4081107041e1903260b0203c42c0c8040c0c02ca20b01c510801001c140020242c02c0394032 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 473203938 1250 473202688 473202757
    0x11518050a1518050c09060417010624171911071704180b010207051302090406080106150c0506040b040f0c290702031b060906121e090c04050c 63
    0xc3d2508115554861a01c00c0d168024030000a500500800c002c014958554010500d0700f211480002842d03640c50400d6100800d03081a002d0741f600119409412103508205442c1094610306480300d0903203440072a84881600c10703a0740111f0159280e00e06001022614203036001c140d4046405441c5148414020503542c1041c85400301c201500f100501e1001481c1c0208001020103030010402c80381008208040000c0404081440b282c0c00e20042e413955031140250401000c1410002032001e050045004400307002031039007018042203c4a000014000140c001d91181d0010084140360700c1d9464003001140c00804003030040781200401180c800035002004213407080c1d59500c1400c0109200c001c0185005502e40654150080301001d515440000300903005010002d041e185084115400a48241c014011450100440310f0811405003000140505001c60100441d901454820600c0e0b43e070700c68841e00303d80515165408038095176103000c1030b80d40b108204820500040c0c5200c040d101c0d202c10703 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 473205188 1250 473203938 473203979
    0x3100b25050120130603021b030d05150607051009021504060815100806040b030f010c0c02040b031c0e1f0512070305070c020616020301050c0c011518050a15 69
    0x10000030300a91100c01d4001c039a0180b0036662040240f070f24061041d802500500c2c055055001c0156100c5100384051008ac0b071003030044400051107080a01140319408500b200b214051041007110b24003046c00003d5004002d0054000801e1120380341c0b022a29860008082c1c02d42120040740c0420b2036600084814461420036640c0c81e1503035405000c202c400c401d500032200110315044003040550806030446800300c1d1002d02120351047d2288501800c4a04e511070000000302c0d41c0b00203d0441ca0603006110041008400400798100258030302c24904c00030700b02200c140105a108012a504e03400c0800c025241c1c1c01e0100081d0441420002e0310903402000d006418012600c0007030761941c024421140500c8955030341c924201d000b9030a00150740c0c40070364a03030801558000e0303060042e9401d0103058819500a18219102d5028a140c01e0a4413072588890600510482050140c0740d0803013005c2c002115030b01c9000c00e0710703161080680000c0c00e407130441e0141c0c407040d01c1c004281500105014181103e = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 473206438 1250 473205188 473205221
    0x60f0603010b1c09210207050316060305090d02060f0703140c041707080c1c050316031805010e0108041109070815040608070302010822050a0308090303100b250501 72
    0x1010b502d0760812a40c180c13000504040450b03a540b130140c91007150900d1070a01d00d0040b2800e8036115400646401540c418038002c02010360024040f440c0d06000b5103810580301c80c024092030142e480081c0d03c640700240700389402e56680d000078401e140309030071034180c401005036074695500b0900c1490400d58041d00454818018000d900352104000041030400c070342d1741e527000d008100200000c105640200048441c0c1550040141d50b0200d4824002490241000000455400c00e50301e405003c03a481500c2c51800415000720030001c0f030360042040c0c4030040091901c1c5200d5950751801c0010f020003000c0454100207692f04101c03a41c0d81204945014050403c4d80b9002ca07d040c0301008255031a500800b100c90300f0114040006500a43d20150032000140030031001ea00554600c00211944800949090b0b02c5440c00c10706050304404956046910b8401035440c501c0c00036140700b08100140716500c1d40c25400070392806a161700400c5114070204142e08560000c500c2e0800310702030800050402d1116 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 473207688 1250 473206438 473206477
    0xa061109090c0702090703021e1308070f0605030703051905100f050a0b0706050c09120705090703110304120e0301020d060518070215062b0302070e01060c0b060f0603010b 75
    0x4180403010350b03c2c2c056000704450156611020708a001e5006080800c1503840c92200c1501185100c0c0080c009814604080c10b01d001d16106000303207403088030792041540c44c420200910035a50f12a045960000540c100400c068507800203a401c62541c28900c3c41010749003001f07101350284810f803444102c03007444806201042c0c86504101d01d07100c071071003180d0703002c04104204400a00c0e95045243d020040136885410001a01c01254821050101c5245c070398101403018080e41c81c18900f91a00300340c3c0f41ca01089076200454089441d4440038201900340d001c082c00c035021a503c20100720400710703000b43c000d5460301c09002000009e4a4507018a9104681d04800500005442e81555100341d0315903004012a005d5015400f845040252805401101c9251020050f021301440d2070b00a801c45981c0300360006180c00c0080c1040441e4001503201d400b90030040016039401031060910580012118619072210400920825281c8001d160800c20120000a140d0408009000c45600160340074216 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 473208938 1250 473207688 473207701
    0x1a040f1a03010b061806090a0602070914060919060906170c2b1e031e2d050c01050a02090108090a08030c030405010b040f1b0504030803180a06110909 66
    0x2c0c0c0e0f5a140b24103070040c070305000200d1000c140070301c8444010070140010785404003e2010904180b0203410940240e03100040c1001a041f96106100003415a00b0a0078418103107940001d001080c09000f442030010240700052007403c0c25400341009000101d820400d80da620700c00c0c003502e96015020000c080c00340d546500c5560504101c9240d2441c0c040b40d0215154441105a00c902913078024150382401142c0701c0d5412441a004c0100d4155009440e400b606040703080000d00c8050703a5483c000d08000385c6002d011542c818030722400245001e030105601c240b0a001d441101c070740c090054000b82560802007448054180c690041030a0013007070b80c80d4112030f030391040d03a15900e02ea603c10007860500e042000950504a5901554000b0320540011500c070f801440003500342c2e1010480358526941d07030009042649400000c02c90ba0189a0500c5800c05185803100d82030f9020081c10310220381646003941c1c202140500000c0c400380d03032164003000b000c544034207203180301c1d0030900c1c0f12802988580e000c41e85 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 473210188 1250 473208938 473208941
    0x10f0f0516080f16091a0301090b030f0d03020f160803090d021c1d03010510050406090b090402040c0306170a05073008040909050c0f010e0d061a040f1a0301 69
    0x101d56a03d020300e04071501d89410340c9024009a0349400c0c00c1096181004c200c003011420410341d1041d040d004143c480d41000d80800c2225400800c1520030742c031840c440300030003402280002c024803207400c00513201ea100c00c4140d42507200c0e010840700030803401c03006101000b001c41c0180d40128085000c541d5103090181050f683d40c0d04050555046401d000c0780800e0391b505c55180b8140c840042d0300b1842c3e480c0100300100f42510070548900041d181d074040180082d0805104450007051144000e1200500040120300014400742020b800783d601e030003800c03214070700a030070030030042c44520550000142455103040c0c8a050800c0101c0b00341c0030f0395100080d41c64030210b510b0700031a5000110014a251007160f00114082028201c071082c0e270a0000040c04d017118410743c10002d004034058980f22903800704201d81d000e800c1181c0c82c140404100410b100e512003d10001c0700690004001a89072140048843c101c411842c449901900307009003507803010119002030070021092105076140c1d240741d204060 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 473211438 1250 473210188 473210191
    0xb0708090a0b071e05030a0e0c0109090e0a08030106050309060109060b0405041e02041e05090f060603100b070305070b1b1909030f0303050105150310030212010f0f051608 75
    0x981d80a605004081071482c05042d40049560910b1000000406101c1014003840041400814004000c1010078540f40c002c3c2d0700c5480355031001d8020b00d0080f0300040c00c1d40c0c45034042d81c180c4503500c4048501d084001c020035200f058004050079207135a507640008145603c1110442600e00035580001800009805a101503c942e0002181028280b1041c4401821000391460607030782000b20b40b48100e00c5038030040001c1c0900c03100c4500e108000f01600d4442c02e807030f40e01c0743d401002050104080260039503200368010000f100c1040d0340389c41c5d0740c00ca00c1261407640c2113500b1003400000c4140406400c54010a503a030710500200000e035541005060b140340c00900c50b440c031414100b207041074803018180090b02c405254146448803640f6a20f5841d40d01c240300c102240800d030381c1e00050105240049a002d540754415502c1842c40c5001041408003074510310009001c3c0c000d10b01015266402900280c000c40902e1600300907010301c100652004d4030301504d03803411a018840484100b82d1050a620303 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 473212688 1250 473211438 473211451
    0x311120301060c02011e320a230301180c2309030a05060a0501261902040209040513060605100e2404090e1009120c060f020a020a0b0708 60
    0x440c11030b840c2800580340c2440d07000b8101d0402000120384840785400011a400d40300840d40d40d218440e1090040c0e444d0542c0512104481807440500807a002c01102d085450f108031510f055003403031040440d660b1281c2401d20006440c1e0700701000204500701c1c0c020a03201c03040b29868040c01103200a11059130701c40e0302d4072050003403100c1440001e1003420b0440f00078150128054122070000c07120381c46081c1080410b039404401e1648443c0104041e151303401c40035546403d5049140341071641c00c0e43c2c40d51750740481c0603034038a00c680c2c14802c0340955a465065480158002c1d10511191a10200c0500070406001c800c44419207403031808502030420700ea04421180b03240c1c61742d80300c090005003045446403429070f0300d40c070b0000c00d68051400015548054001410780103000b06010440014040c180b9450b000aa10020319091800012444032035800e2070311007041c241030800310340c00d08060300680103803980f1089035800042c0440300154002607210707906000781c0c09a940c6403241c030401c0300d03c4801030310398 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 473213938 1250 473212688 473212723
    0x60206040b060a05041a030c01020c0306130606050d14010606081902070501020d09050703050f030703080a0f20041802030f04031d0a2c0106050a030b0105040504050907030311 77
    0x5030000785440e00c4950440001003041040c80c0c3d4582c001016540e8103030f010342070044241103a40c8281800c0046001a04003400607003498403540340420360341d0b07400a0000e2048410600e03c48140440d40d0301c40c0e000b50101030010005414281400f0103500c034200e00c2180d0a41c40e081c80040c000b40f11342c400794003900380e00e24030311031302d001c4d80c0d07001c40c041e402100043d18555400c003c2c07800843c82610031503408501c60f5000d0300d000c52441c01c3c05410200804400c541d0f54000b000b041001940c08a43d150f800b400c40200020000c46929030000103040340d1200322150045030f20b0300d111500566000d881115101c04402005001355104070040c0e00094a40e0081c0403038080210340020b000d00c04560f807201c5c00d00c200d10f4011640e1400140c2a580b15480b80d044ae40c400303031042104440000880724000d0300145038808952600e00000e040d845001400c100b0196211001d040c0c580c4503500f02c4000f444020030a00c40e90901e400600d0700c5110510003240070500c0d54110b00c4801c1008100c41c02c520400c0c6c0711 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 473215188 1250 473213938 473213941
    0xb090703020d0204081020070b06060a020a0b0c1c06031203020906160f02040c03020a09031103030f0d1a0d0c0308030a0603021e2b020f03070b0d020c070f060206 71
    0x150041e401000d00410420380902000c20711000420010210640004c80407c961100c0004200c41e2003d0407400454104108a0789002c00e40c281c100300d40111081d102561f40e0b8981d510102e040c0804000b0040c102000703a0140301c090401d15000e801a903185424100d43c95620b131400300c00f1180240300003010803030300c00e4a4121160082d40070f880e984901900e502d20301929603d480580403100c06044840b40300c40010700007941018410007c01c4409805c00b1481c0c160b0741d580c09080001d2911008040001e00c0d42e074020703d83c805006603110304506480c259140e0021071021000b4140725401481501240e02207141036140c242e9003901c000350001d902d0070f04c035421521400700a62004000741e0714251200e50000043c0ca42036541a40c004950a00040301c1d6010b90412410201c4c1c0c0c20100c3e011204c5d0000c0711814044103e014084560442c2d032014108240404641004d46542c01038440703c0c4040390700342700443c40380c00400070b00d048103086d5a4020740b1807501c04607007005c90081c0d90059100e1030 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 473216438 1250 473215188 473215201
    0xc030c0307030b0403270f0f052805031605100e06030703051f03150606031e0207020d0519150207080d0b130501060207030b010e2a090d03090303080a0b09 68
    0x65441c1c12500a1406046d0105d4058130203040f022510070303205c1c20144408003004000300120401d03000d01860248082e6030b500d8a400200c0c0b160194000c9448072841c11403040200c00304181903002030901806503a541c40e10303100170644a100510402d4020718103101d402144902c03c1005e040c0c034010042100c1e00716229202d0413001084024130f9075080717501c1c2210780200b2482640401c002180304070303026611124140c00f024203884440e4061001e00d0b040c007000c1c542041c0007115000703405002600050b00c40c5003d00003c0c122050050011b0000d00a6221401c980c142100e0542001c500500c000300c1c20030294005402280f281c24000341070400188170849003074120750080d0744000d00003041200c0004500821a007112420b9105c480542d01040007081002080b196150051808200c0980e4a242c001c101e102c800007203583e88603034003860b44583c114015408040c2da11100010313140c2d07031403a80311303181c05091024180030aa01144007000051b0359140d0303d004141440d503014014003801d44841 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 473217688 1250 473216438 473216453
    0x2c010806070807021510060f03110406120f060e1012080d0b19090c09060201150b070c0b0a08010512010506150a0c051006050a05241315020109050c030c030703 70
    0x107050f4070214003c1c0074100c2c5107280880c0c00140074031550086084805d01c1d260001c1c1c8585405081c031001c0c14140b41d4134141c28014182075a00301c90842c1051104017860311640c000030001009002542d038a041380100340d201403000410300c10816924103540746619070320701c049000ca40c1d131001480001c080041003040300c015041f60716207400c003500401d20041c800d4176610400d5007a4111f4612030340c0d01e0001a00c480d07400000440200040c2c00200103480420100e10240c61140c00380c0020210300107441000c009100c50400d005140030003a6545800c0c07450001030502e0001e12800d44074105941c454880c650041c403a2500860303004000544147d810700100440d6041110383d1000d1080d000008008035405111b03022580c0c58040b00002e1311402d100822488682640140303028205403000245094046d03c4208480c004221100d0740f521100c071800f0314241c8454100c0c03101140eaa04030164200d405401c4644010700c50750558200080707080074196501c10414190b6850f5109160420200d2601c = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 473218938 1250 473217688 473217691
    0x4030c0b07060b03010f09020108060a061413120303020418050f070e060d09060e0f01090305180a05100f032d0209040219080108151b0a09030c2c0108060708 69
    0x82d040100388200e40c88002400c403034802590000c816144c80c400000c560340286100e82c4140c04955480805003014401480e6a80c2c60700e04c2c1d2001d10303000030a1024030301ca03d400307840100b00300c2c4500c1d0350803c218500180a07401c64821a22060b007090041d0200180c9401032034070500c0d120548400690f134040703044440041d02c45071182c1141013045220074080280c064209024005e000120b10002d0403181c591078200b0010320300070a40d16281d80b030300006c0d60010481d0080da2580b030310002540c9a00e400207007010302c1d540c08654007403003007805d41c14019007103ca88815000d054508000c400355040c00c1c02d44103240421200c8082b90850000703080e0303000f913501505991401030700050405107051007441002c07070b0381000326002c90340c603000402006e17200b04041605240010b00080450404485c4070019070080c02c0414050703100483c03050ba100388641805c030002c40e003142030040743d90740e1a40782c5c0880d0029544602d481000030030040c06004100404141200c8641c00248182e546d42e1504403a8201c0 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 473220188 1250 473218938 473218943
    0x190e06070e060a2a23190c15030e010b0d170d0906020301090920030d0c060e06010906170a1e2108160309120807020309030601030f05060c04030c0b07 66
    0x800002c841280500f80509280310010984003d0302443c0070300f4000f4032016800081044005035000c442c8103564003040b901074944400400711001c50051608884250141d00070901d48c1c03404c02104111203078140c1010080700c4001000308081482e1070144002d407030318594090320040c0d014408103231061000c0010a4100c61102c00040c80d40002c1d90703264140d0b4001c5c1c0c0800e00b079980701c11101c41030041ea1640d40040b090641c0030441c100c900900840c7d1103201000c110720034000080e83c444184420398104414000396078003522002c0da107800c1c01e0f6008007101c2c014101c014081c42048020f00030001030ba092156086085107140100b07030307220102100102c2d54120b404040c41d0400c0c0700b0004a401d40e0b036450b500d60b5111420366203454102e00041c2c03140080441c0406040c21501d8020400d80e4410245240d1207190101c903070b5403030300c905901d180f01d10281c05425114500c000805e120528242210452151080d42c0c000c0c1c440d044600c8260149001c0541941034030304040041034020780c000d05000d403 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 473221438 1250 473220188 473220197
    0x1e020901140406091806060b070b010b07030e030f011e060e061201061d04020f04060b16080c070305030408010e010c200c06030f0f060114160c0509190e06070e060a 72
    0xd80394110342090705c0711041c02c0f0340c10502e001200e4003049094040c1c1c9001d060b82d014010b0801c0e2082e120344c007064006200310107400d200000e00005062040300d01c845007420180c212425800c5000000d4020305046543d03003d4240c422041840d4a10140600340c01c841c21903560800b151224001c01c00d02000c419100d80056607a80c0d4001100c2d141074001a1001c1d217418034500c440d10703090042c0000100d524844a1149191140074407880744010309032a6401048a0000450780c9030f860700301502e06c215440c0060a119010000041040000c010001d40710b40720001d01086403810340180c2601d0090000101041c3e194443d400307404e14901c01a00b5142069044400812041e8080341c41980b05642c000040c8880c0ca04204001d0850110340741c04c41c2c82840c14600750742810310070758120300413074501e135400c0c041c21100d0605100130b20309028054000103005032610304002d641044464800f100440119090444012070b4440220394a4807604082d161443c050031000200140b0b503112025170740a02 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 473222688 1250 473221438 473221451
    0xc020909030409110a111606050a030e030d02091e0a030201081b1201060f0c05030a031a040c0c0308091501051519020d0e030c0f101403131e0209011404 67
    0x501d55004604074400100042c0d9a10070491100500e80220511b181019074001c1d043e0003030303086480d01544201c5000e450442c5e00c0c0c04000a0481c01b034001e00ca41c403411480041881054800c15030300411503070008584010f03140041c403050300104003c00110700c4d8840400b03282003015500030700b20301d940b04403440c000100600d13610484c0c02d06500304040d044c18442c260001031101680040d10414040300f14100001e01c03961540e152582e0b84107120b040c0e0300300b680f5044203030741c1005c40301128006203070010f1050014a01a0300001d14100d00584160001013404d40803038480d20011604407001e07545400381c40d64603030821b010310590520205840d07444101c20021010000e202c1c0441141c2461039502501320012000002880416484141403080c0c2160010000750713581c2400703140905009035000c2e04846002203098810003802c18180d2502c10001080201480005000001c4c5910903181038000d45202c400c8101e0380c00c01118020342080303040c00107000100c44000179105881c0d0040021400 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 473223938 1250 473222688 473222699
    0x1f020307060504051b01020a1101140708031e0c030c070f020d140a030f02010e0a060c02030c0a06060f06050a050d09110d0f11190b36030601060206070c0209090304 72
    0x1101c0d803c032010354060700300b03e10110b00585510448265600244011300002105071529500020703a900454144803060341c0d1040808107010580d03152076080000d8689a1505010208a00d445400300640308000380002a0007032407400c01f500d00807404200c0c41818a205070f036540c440c4102e200d40603a4040c2c0800490310000d0044480443c02141460103490460194034016000365150b03c164015a410f04088001525000808650b8107800480119007101210000da04604c901440030545004099011050003151381040c421100400e5101d0413503aa10b540c1240c003800740991610004108005d01000007050341c0100b21003034003030f610308800e1070b21075000035120302c440500c02c480c0301c2c4480781c4c05000c0c0140252030900a0f4000d855054442d01800c006105039409405050802400451908401c00c001c40b190b00140c494068821654014003081e80074031104006454868840d01c00082803541c4081130b0b240c0a901d0300c3d2034a19440c01c641d4204061755400034803000c850310091000158 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 473225188 1250 473223938 473223941
    0x61d0d2d080d0c0f0813020108040c0306061e060f17040c0f090e061003020a180f020403030518031f0f180b160203030405030a080a0f06030b0702070f051f02030706 72
    0x10428120140002e0080e00004080c04016603860010240817005080110580b00b407494606c3d03256092800d5031450761689040513210751550030260416103040e03800f041c1165070a480e022014661818143c50035590b040449a48a0f419900c2002440c500454084840d1400c0303c41c1d0418400c201ca0314090b03840e10440d0300707948289e03801071a40c1500c44848074030584090241c00d4000100d0301103c80300c1750075a00403c003404654421440c2d00c1c911036003207411801003a406824560300a6209641d101d5603030030000d04641148070ba00032142032986540043d40b500103010080c0280f80c0400124103002550801c0c018001054041601034540030507200f500e449141d130074070852203003624064030305181e480d221000144800d0300c420b40d0302c208203100c08900000b007910101001c0d41380c40d0626a8902030510050000303041c419a10a04100d004070802000b5600140304404641c01c0341e01481c3d940c0c2612121039114822150800710100014904a480300b00708071114810b4011030745042400d564620 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 473226438 1250 473225188 473225197
    0x90b09030f0115090609021602060a02070f12120e0906040e0a02190e060d030c0807030e03030c060403020d1d121906020d0506060304030f1116061d0d2d08 68
    0x250f1442994100703004402e240d1141e0005821000c80c11800c00c2c8001007a40b90442c43e40c00064400c11001c1003101d1950b10130040240030b040014440c1220f0703555000100c0d00c07544008400c5540c114201d0040441e07911804a042c0d540300024403002c0d1545a260500c0300a1640d113501940b94010640320f1805a100c482d030f01e80b0003c000680c400c900310701d0510400c00408015201c2e07446252200b80c000c01180c1c3c419071a40840e40c020f00c000b99203009610303082e00d04a80c03401c41c2d02c0c0c25010204603070500d10004602d1503c0b403030003602500e10554610300e003204c1092a81c40703240040750030040549180d0501228441d00300c64003800715601100040d0801041d0800840c4c200c03074454000404440161040c000d498125000307131005801d600b0503540c0a45103004020822341003100022031620710300403c0060340210326542e40b8603081242c4403040104400484680c8214484000d004090755080410b040d184254104d490548504649025203604130008800203e0320810030f40b050000c51036480040 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 473227688 1250 473226438 473226461
    0xb070c2306090706081311030106090509030a030506090c040909050c0303032d0103081b120c010b03060609010b0a1b06060f0305011d0d12020f0406030501180507090b09030f01 77
    0x800791450000c40300c40c90920b40c0c3c0c103c0002c010164044c030072001d42c0c0c40b15441203240d0114217007481410283c086401030010f5400901d45604140c00d0003240760001c40244140102980c05102c26070710142444181e81060301c01000c0b00c68108810051040640d0025100030300c20001c0e02c203652120000070346190011b07215000e08600c0340c1d11400c00c280001d074004110310901221811558510744403071845024210341011a01000c0d140c4100c107070b20030f000c800310034428812515203034486046001d0080003040c4c102c3c2d0091059601150161078201c8006040314001003959242c814482c0b400c030350301449000c941a0343d403905500180015100d0040e0000751048005008425245046c410b09591072120248054000001c08041d004408201e00c030014540741014031080c502020648001d2041c402d0841500c500445d0215009615800280c100d404007485001401843d220350070449009588280c080768452900304082c1d1620b00c0a00080312004080d6040d119000301e0341825607058110b0f0 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 473228938 1250 473227688 473227693
    0xb1e06031209031c1e09060207060e010c05010c03020c0c040e030904090516180f15060f09030803010b040f080609030304020d0c030803041127010e1015050706180b070c23 75
    0x2112901258175039200203003859454900961450b00602a4031820207020784410050021140b0100341d0149191380708190380040200207226035401d0043c02504610720100da1402425003240780f501d4035014159000c02500045d5262203a1041000000c00c41150215914010008040c0340b0780300c4040810005c0c40089484003110702172410326022920303480a0045002d280481d410401680182540305552040c1000800c40b405c0305806c3e506504140d00007000000000300104038110320708040c0c0700716004425804030540c0c441700019120f200859422880794070a000080142ca4103050b6915018018110150341503101d0302c1c2d85c1c500c0d9000310b5059520740e281403d8025141000c1d0000c4906000f840a10301002c00b0080c404085402c0610800c0d100b041010040789010550502c40b00007888001651030b00d00ba500e28020f0103980200c8000c2d648989890074105c5c1104008400c0e40c1c601e42e009000019a54545400359201c3c104104207807017070f83e0108028650005945088400008807500 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 473230188 1250 473228938 473228957
    0xa090204050708071b17070c030b01081207260a030e150105030a03120f0e1011090901060503040516060905130e0c1e030106030b1e06031209031c 64
    0x50006032100600030b4010003000008000e2034951203103200c0011208400c0a0709441d000d8106800079002d09008001201e10010350f460400401c40341040880e80318210aa4440c1e980341e05241d100c02a00c00704061044003008004002240b0402c180818074000640b51a0480e042d0440d0840c1d400440350000442c1d59145003401c000c1c010030504101002c140c2120745c1a42c14000826111640c2600003410301c0310032070b0000421440d58101c4002a42100390030084600d03403641d100d9580c4002c20380500e24070700e00b026401304c07800c10604507001d544010f003005509910b05201200c07164030003031055955010304400c003450031068070b200340c00a007a81e80e9411800342c1050100003800c144142c801c040140380213020340860401240d0000b070780c2c00460303880c9a036400c04810508100981402903515503e4050080700304030f484001d00307010380d449002e494201400c4130000817110034191a0507034154014400004030004100c01030042010107030690b15840381c4280c0d007040d10300c0304040c1400801e02614 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 473231438 1250 473230188 473230193
    0x303010b090f0d030f0f021e070609060801050102030f07061805010b1206060307030204180506013327090e030a0e06130b03063f010b0109090218090a09 67
    0x400d030b04440400c0758110f1403943c182e94003a002e4406900c5030814840c003002c40b0b02170f103402440041200c5042030b13030240c0c80428040350a604c3d04481c2c052040892000039000c115144074140c3c241c165601a0021840c06952054508098220305021900540c94a0b4110780c510311740711180a8040c4a1800826064540c02c2000888030101c0440151a0300c0541007010741d9400041c4030049a4055400154860502c8031120011007413420183c003e00c5420000a040d10150b0141d8280c0c00fa804010101c0c1915805801941039650923110b0000340c2e15071195650085c00b101004485c64440c0502c22070544d1500c401080c2c07900b01c480740d48103030000708409003410341003070310b0303284480d42251580d1500da1404034100251030603001d1481075441c0440010b03070a0b141e541d2040c0f026480340d04003041c620080069001e4091071a0000004201c580598041d040700502031038606d918141c60300f62141741442d40d0a0000d400a907094400c03260214244402601c036a49030f103004880a040c00700d0401c59a0 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 473232688 1250 473231438 473231449
    0x90d0c151802031b0a03060905010b0d050303070f0c030c060b01090812030f01140d030806131d07060f020d050306030106030b1e010e06010503040308070e0a0605070215040b030402130207050303010b09 88
    0x18503a5115820300c0b1000c2004541d05c0c080e20209595100c440010a1032035410018010a42c100200d5001610403040700280710001000c0c42c42442e0581d68140170070740e0303698111010300700c852008004c2125280b5140004541d5001200b80f050103151814185503504d0050340b8080320b082e5440a040300020074403001020034210341e4003604e0b9100c09040c0d044003e40110b48100d501000c007a080007001400700e119655000000b0050950101080c840703001008200c40210000c006038051501c00c58000141c180c8c068a08002c03108455000340c640c0e13291041c0107603070982c03001307003290707459580c910001c40007420001e04140192040c20b4081c090800d076112504101006801103100b880303402c0204003e03030703030300904807a072255261a0422603070711204016221130b614015100d520089200001c150241c2c0a005049054000c50703050102e912b8040c00c504040c4602d020b202c42c47c1c0307810130006000d0f090100d1030b42c1c0c9080d040700c801490308c0501d4480c10705641007038000b5130f4880800141c421051130715 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 473233938 1250 473232688 473232703
    0x6010e06041e080d02030712020a0b15030c01020105070f1b06090803160e060406030c050c0114071409030a120203130816140108040308061201020415090e090d0c15180203 75
    0x40d14000e05100b0200300f4081d46da4028560010a1903002290a0307150170b200340018419643d000e034441d816414080c0c2c844192024601e40c0c0c90007807255080d480250b40c414042d05000d04065210001941c04400045441000101c00180c0f0f100c0f809603410002122807242c142280c0c06060402c0d12410000c4840402c1b14448409104102c540c0070104615643c000c110340c100c0391031b4103001800e942952025143c5005c3c840229100e0351030715801c03030049801340e01c62521409040c1d80d165001406506040351078040c2d90b4105030550b020401820019813955400c012a404900469042040710a00418166101d401c060050340000007801513400303c19600c480a000354203503081d0701281020000b403024000a0000d400c2003240000703e60603803030310213044a072050008004c1d5502c03501e0b003204e03403001109560321800095001d0b100203903500040034482c5c020364807040940300101e0031b41d904417001140301005681c00410301c00f1b03100c41c85000b4850000b00000c0d998000240da0628010181064030 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 473235188 1250 473233938 473233949
    0x607080d110f0d050a06031a090c01090b1903020f19080f0108100b0f15031f080d110106270f0c051c0605030102070311010b0a0513020306010e06041e 66
    0x418004400b01c5075100c0c081d41c0a140d2080c40c00185039031140b00402c0501102d5201414a04204c0d8644020801e1320002c548152103480071500004101401100c41141606c500310101c1407d00c1100d103407007400300d005200c41d10186030240c104012103e2242a40e40440d8071842c03800c0030b4017264801c840d0001282070f8400c2a458541c80107603d462207098503540c860b075442d02c003ea91200c1da106141e4901a80c8403500301e000e00344a010000207000c1045070b074010b8aa0151034080c0d9040708500c4040c5003002015600c102000d8000019009401e03030307415034401036803481d0b552111404142c100c40203110040714480310404010b01c5245410500c1110020403400403150300380102403204981103003c480342d5aa01400e000c04403c112003428000704540d411403641940005107a00c01d00d03501c4142510718681c40c2008100c140489010024078060030700c1120b8122140c005100040022640515031205041c10011001c1e007a10300007606651140d08140301400c08030f096542682006003c10020b0b01 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 473236438 1250 473235188 473235221
    0x9150b12012408040b10080106090609050901020c2121041407080c060a0207030501050a020c0d030513060e0c04110c0c040e030927070306061403040b180c0607080d 72
    0x1021030030041401c0d20051002d008170400c040421076210840c0001e4004006890007080000d0312610b141010344502e225000499040c407003c206400018400c03a1402140d40c4002e00d04c0810761100005800f640c0d00d0360245090781803001e4a800b400000b05505030203540c1a0b0a521403811313103043c207040700d041920f4072031540c485607040c0b15002c40000c80c41c0075102c3c1200d040361121180d1504921f0303c00745420041c0f1950816051140c08482a0054548a01c0d4802591801300d09403c1c118110b540490749459141c0458000d60041001e0f5881003141070460b4081c7e401202511002c1800d41c2e20303201508100800014821001480600025521501c1118240560a0482150717a901d004554980b8481c2111011100c898028611205d54600d01004000d9140c50250400350040403031380300e400c0204504820f05204c442200f001c407072145034050100c2d503903512008080b44050f44902c00102d010f1081c40070460b51a59000064001d080c4039250a56a64040341c0003d001e03500303e401e0706141c05 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 473237688 1250 473236438 473236499
    0x2031c0212040b1929090f0109093306090c05041a04032307060f120f0f0204030605090708070317282304050a09150b1201 54
    0x1c000c480c201c01d400035044880c0183e070b0f8032104078a200b0030444941589000d458481011003100c490910018150304510055480141d42400d004158a0895190480c04880700043c0f140007000e40c000581c041c01000100c0d9544c94125484150708080c0705000103101c030802e510040c501450103078001600f0044011f1001900144002d001406a801800764010700d07249230303840c80a02101901c0c0115000030038003050174240140ca0310402844100d001e014041c07590041030850107000c14030b0080700184d454170059802c14100800401410184110503520380b042c808000f1228009000035501030700001401e41400d01020b4986100c2d50700059058001e6881000802c0c05443c000040d0080c0414050f0755058555800d690b4076040c40c0d0303c0205103890b001906a075030344400c150541d40b02d44c1445101100d04140b40c600c1c280030303912801e9401954040c05020780703626504235044d1050402b508020319501d0b10700002494000300410b100150040c40104100c1c00071440c000201c070600105090389 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 473238938 1250 473237688 473237707
    0x80d060801020906090d2919090f02061c0e0f070905010312080a02090a0308030a15140118080f0114070f090320030d020706020d020303062404031202031c02 69
    0x413130180d030803500c5c8201c9401d0424018000700800408441e89450707c9040785021408840701d070f1500c10f0352488030603181c0134031440e200729880c46100e12254001040c1440c0d89016800c00001d50b014980070b420100402e5101080315040e805510b110501c02030240014484002c811840c10300036a200740d101034148401000400e004440c1d1140ea5015444d10408999030000820040d10071804820f40100c10b5400010600148002441c0290104082800000d400c0d1800c07190044050080c024000d426604400c1158024a410a6442c1100b840c0c3c0c103e850b9101c0020303042c00c04c200c4540074680d4407042c1c203018114100c0e80240e40a09035045c0f0000e09515208024000300c018000140380200040c540c3c680c0d041d03003102030394a00200030100c40303140c4c611080c020f40318441780c4079840240c81525514020070b400403040d284100c0c1c014202c1c0314209000b80c0200000c0070005248810b0000400011011900381180344214010b00d4005568a24650301002007220752010420b03001e42c410300c0b0204a = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 473240188 1250 473238938 473238949
    0x1509100810060317070203030c0f03030f06030f06010b09010c021e040e15040204020906042c0601140306040209150a02031c091104050a0f02070f0c0504050c07060e07030b04080d0608010209 83
    0xc80b0041510304d54480241d131000c00d1451241c166450014400c17000044e85007070002004501c5090040c083d80802d88440051581c0c512201c13982d109903800420040c02803d118401500c04060145891a0350003116000b20f450340426507001c409003c071100c0120401d0505020b002c90030310045004021300c1d10700001c502102c801c0681700038440ca030005003000f80c5a5414040d50007030607080054001030314844a00c0244440f00b0440f00e824090b84c01d00040542d0300400c141354182d9104c03aa128a1559407108000003580503110440e0322009601c464440d003414800074010718031171078004555038a6407148600c1e05c44041498044210b040241050001d5803003610450058400d480106080e21142c001c0f1005d08002c80030b000c4441c0c40801c1c501c05018450841864481c003070411444c0c140d4540c004d000c151881101c0d08425640e04000c040300250695000020220b03103032003035940541e141c0e981c0c42500581074a090307800f55000304203915040c5042c466a002401c0c0d21008520706040b0b000881d4 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 473241438 1250 473240188 473240213
    0x1209120a020d0c080d0203070f020d03020c03040b070c24020601051c080703210617120f1602150307030b0a03120302090103020f0c0a17030415020315091008100603 72
    0x20800c1c00503981007000321380402c0d00c140d40c00220003075450f443c01800c010b0404451451000040c4114400b15001c0388c040d00c200da83c3c0ca25140c01840c90715040039030880700e035400707490304884064070740c0350005039405e0b803030003946030081d0050003038480c1d84402000910b40203042e00102c0c800c511796510043c020038100000d81400f9480b4018a803a01c1070307030805031448501b42080f41d0503009028400c4c12402d11340c0d07000b001510300400141c2101c07015a44448d646c0c0100400d00d5984881c2042800d0881c1e1500f0050100960380d4003103040d800100d80d000c00c812404025051040c0c2c0c0c0013009100c544e94050240668089040d502d8154161560311040c800c220782c9982e00c003c0c19400201045d190b40709030116940c1c1000300390016600c1080000d42a95101103900c180d031006a40010030b8295080032044074003668108120110380100d0040c0240291300c0a040c200d45070310282000141f0740c6a80b40054410190a40c118698502d84207000c5e0070580302c22480c00900d4902302041c400500e030b504100 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 473242688 1250 473241438 473241463
    0x14010f0819050316050c040c0912230706120c022413080c0a140f0c3a1403070302190201090803030115090506040b18151209120a02 58
    0x2584114502c0c00c003641103100f500c06420007942000250014030100090640d04008282c60401199101b400122000c001e58061640f102c242e66100e034010444000302a4100b418094140c10b1403003006008034a0440307694000e902041060a8054610342070b4840c11940c80c000d40041c1400b02c0c102c14038511403122200c1440b0240100d4408034003d04030418401c09010b45c170038256665800c58201041d035455503604101c5050f42050000341d0040c202180c00404400150700615408070000204a0001140000398209041c0b503403007003040d401c03408150802d00f13204000640c000c0d4640d0512218400c0c4185c0c0c00e112a038001c00000340080e500285640c0c1c048189443e2014a0b1110701c01202d010395660300c88040781c8400300020070758200d8007144103044c2505807a1804001d564509000150080340316640040704107114150028132030b00c10246a4980081c40710210401d642040d80c81d540010341510003000c070724001c00800e117400f0881d02c1141c00b056a103250500302c3c01d00740203695000c0301944 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 473243938 1250 473242688 473242723
    0xf1605030d0c39050315040f03050f0f0702030f0607090e0c0705121801022a040b040e010227060403080f1201120b0619090209010e1314010f08 63
    0x207080c103000403054805124450303909100c3c054400d4814458802010800f140400c1558000020b501c0c40c0c00500882c411010300421200d83e6900e854040386004842400e6007400810400000c0c0c0580c40c10040c080120f052401d952543c4090041c149000940c150610196200c807085c004040d0708005010102d8402110400c00c0c2c0d0b4484c904845980241174008040d80b09144880c0e06420982c0301a001c02260310b51a14050590a0f0049035101042c100c0d00c0340c52180000070400408400e017400c0d10780e110282000c10141651400b04007100c00081546182e6540811180a0940306550044038514828030071550182d5003800035240d840740e4400100070042c0041c0700c40e80990742c802545d07180c85d5a2407000300b03950380d42c00700c020900e0f8040c81c00b01c500c9500800001c0c06803a152600301e840089400198000300d0510003072200a52220001c68103000750784030090420ba8a0f0320781040f444040c00c802145034164541404ca11000680003000708403038110040c41680800908817001924100c20b = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 473245188 1250 473243938 473243957
    0x1209040e07050301020d0219020703030c0f1a071d01140a081315150803030906010303030b0a0509150301051b0a03050403030f02071a0a0605031f0e06090f1605030d 72
    0x2409407030800298001601940081061440c0e0140c2c2d5000c0c0640d2036054400407000101c0a008984500580c00003d0108890051100c02705501c0d00c0c80030309251007040c0c51a0102d0900780c00380f00841d821601c02000882040d1100c0d074010000c00b200304e40003003e0034080501020030076840028020914401c080028410004811841c0c62000844c0070703802508500900c3c83c41c9c0740710805803080112001100500310710015242070004100da100d41e85d282d0240c80c01e6429540d089000c0c0107441609036101a181d5004250b99030780440140c01121040c003d103030381c601150280b50946034000e1185a04c401000850a0344103581d504440d02c1c0407852400081035a100d240c00d4000f003540385110000d040c8007282d1032080000700305848000321303415003480e501644c4001030b400540e085070140d1500740d0030900c0f2008090903e004000a90702c00c004020859480402001d450824121140a070a43c8a00a4003589400501c5040c080303142c60020142e9450501740425074032000520303d141088070540 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 473246438 1250 473245188 473245211
    0xa090c020604260a0203040f060c08090907020319020708060f09031b1603030f0e0613120206070209040f2a0e0403020c100507030e040207050a17070615090c02120904 73
    0x708501d15000f01001d8183c0300c0c16103000082d643e40080c010510710458882c0c0115106004070300a400542d4041e00744c514028416060007040300000d000301381075200921050841c80000010910341c001194010882035141c80042440e08030003030114403c0d1000c85080c018280000710444a000c0c0d44480600f60200e08074846e64501600e0f01c03c1103107910b02c441408420580c4c80750402900803119600e603900c0108200402005100d081080d0700c4030b2081007000c0084402d601d030510f448a000034881c03030900c40260085107080d402160221404281a441300d01001072202121070302640064506d08503501d0280d0034560542c250040083c055140d4001504143c42040840b000400140414007603403407001000e0040e4121394411000b244d2070a42c616120b040610036a525160440010016103510b03813542d2401c1c11078000500001b00c1c040280c28007190103030140003185000060301c2074030320307180c504c1400c12284495494011500040017107488a011901a14084070303086400041426010 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 473247688 1250 473246438 473246483
    0xb1b0708070512030a0504051e0d0e030a0b01090603030206010e0c0414030a0606081b010318080313051b100206040f0b0606070b0906010f0812030c09060f070f020a090c020604 77
    0x1d0346102125000002008540b405da03401c0365015520800c01c071604040f200040d160320f0300304030342c2e200a10b50040c0d529112107885545034102945028080e07600060285e107825404080076080800d0342600c1d003408008065040200e0341c010715030844041c01c00d0822403242c0c2c01c1403242d07100d40903900181403040016a9003e1059011040e817103201005580c0e41c490480d51101c03000749004400002100f11000c655029014116891540004c03104070410700b84c0e99041150005850091586011394100c00040d02c100500c9420240081c02c80e0506481070017000140410004a86c0841d0050018800042c0e150024140402d80c400d500414507071340da4011401d00c7c02206806800c03910200184264510f010941606a80708500110905502c82c0c034002d80e84c9543d800c03d20700c092002c00020f245006000080e0821060041034a450b040643d0000314842d0040c8100b40d540300502d4005000714641011950000c1c900c0302428000c00f0324000340a5100c420050000d007500c8200013101c460360888 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 473248938 1250 473247688 473247703
    0x2190f1502121e06030304030c0312050403050f0a231e010e0a200105190503060109090e1509121204061401031505070509100e010c02030106120b1b07080705 69
    0x3610481e2280c2c1c80d00d4000c500f0301c82c00c049107402001d05040302141c0b503420003104580540b03820080d4501d1051540e038034080802c2071a5054420050300340408000a50700780024507504481d500103209400060600c2e0f05200d500041006141003d03501d4910080f80116003024002c02c01700607498201ca4510b6030318090220303070428442034040c40f640d540800c155200001d0090003081c99000d000442c0308010b440d0ba2140d01c4c4000c00540401100c2802644110000c603480300061600f01c5a190351080900161541009000b03160f03040040c3c4c003003520b100703442503607400100d460041100d60241f5a61000c07a00c503c40801d01e03442c80c100c000a05100c00351b004003212039004c0d000c0e0945507070740341081d61800c0050464010094201408508654850701c1514103158005114045042c0524403e0321003090000c0c820303051118420404002d03940c2031184400a201d080040a2281075070f203030070300810000400d0f075904900d0f13110806940c4401141941c103980d50051006660b00e20724103101c0e160044 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 473250188 1250 473248938 473248957
    0x4120209070c0b01080703110f0303090d14060c1206011404060e0109030206030f09100606091401111b13020301140409020d050d0c0210030e1005070e1f02190f1502 72
    0x55090000400d054001b40766400c581c05400c10b02c81c1030032010704010590b840340c600c2aa140c1e00a10016803a4034140641c80740c0148215101c0c0b2500e51005007140c10310b40e0440710305905400c0420a12040108000c103141c0c0b150003440e0102e050110498003400034080c030f0141c01e0804c11a854001245c1c2d000e692030001454004114985030315100c2c0140303685c20310880b181d513180d000d403091210311481c4500607201a910503464908000c0d040940d1400c0c40c84051200c90b0406c4154003c14441d68018450107001c2c440a0492044080d040010700104074400071071f4405651041004006901d41d80b2402e03400504221000f0885178401c2c000150000740700300014010740591609090404d4101900c0b002c52031090342c098241511801c01501250800c1c0700180103500710103100401c00c80307558819070f40070600341080d11109180d0380114a1150280d500c1030b0380320b5058090305008513010015258401c0202c0054058148150780c0e0b00061082514001c00c0c4c3c5a0180d14103039002c80c0c03601030b1041c802 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 473251438 1250 473250188 473250203
    0xc05100804060e0a17090f0d120f210c0f050c100914060709030b010e04020f01030e10060e04021822080409050403030b13020a021906110f031005010504120209070c 72
    0x355100b8425100394481d17103501f0302c200c1041e000d1708812304004140c0304210340c0281c428a02c02403806000d442d0562007041c610200900303101f461080000121400385541d92241d0b00003400c1960110141c68240251450400c1c008140190725040d1800a48100c1c9622500c01c08a108001d80c0b81007407101c10881c2e5812018000c5808010400f5844106501141d014114110140e41c0c0c81c03c607100001c409480c0a9040310500c40c1020855000e90800c183d40320700e036000c45070714910910b07050003214104c0c0c00181701525294140800e43c5041100c5020501800b0030b8020340342051005900c0ca104210300721040c40404050740c5052008080595000b459048403d104524151900034004c050640034240700c4c0b102001a449401414800d0b00c691140d0340d001001180545540d130410050703000c02c1200d00903105c90b480240402480040c008071071000100d5501e90800b179041c040c841d00700ba008541000411301080140f883d190307450710a00c036016103140381903485480040343ca071000000b018011a = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 473252688 1250 473251438 473251463
    0x24070c060203030a1109370b1c1437050412020c01020c0103180f08070c08150612010e1c180509040b06030f190c05100804060e0a 57
    0x201c0d00440214402c0014001c20404205024010701d40c0740580039a9a4224801030b8503840c040c211580c0c040440399031000c6900c1c00b92440b13203014105040f05d1b0002000700c000840e03202e120040e00100345240c501d02a03018000c007000e500491203110f00c010070980a0f52131201c0240b141d0000800102002404100f1606461140c1e15600020f0003007907400303c6260302030076000e8520900c049a0018545c805902501003035001c003004402400111884580c04803c8651110006020300d05004400d8400c1c0042074440869041082c2d075861a1380c0b02d0340e6141c004411340025203500e40d400c0390348590100c0c0e4150301110184020340c0104038109144039548211024094102a6004140786402007036a604140d010b84419400c5005520722891341c1024102000c0f8000550407035146d64414405021a5940015904214681302e800350600c0445420030805106001645059402600068952034510785d01880c1c001c01040b00140050075040d603c0030307981640b03803040c40450b80840c7c1000380e80c200c1 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 473253938 1250 473252688 473252699
    0xc091801030b0f09031315090905010e040317010b090618091317040b07170c06010f051509300a050f0c0102060103020a0e0703020d050c030702011a24070c 68
    0x9080b080c1c410003160111100007400c4000c00100321140c290b01d4032a0b52955500e0203d47d40550401c61241509111405034081042d02540c45410300034100c60304030701000d0920341000f4202c40034030f10140000c2c4070300500500c0382e0702c00c0b0b50071517203191029036486a07614a48062031521802c41c0c1c44095111442409001801801c4e144410240380100d00c43d010031004440c51071743c1c0740710381e00c1400807124083c80f030301d00442c00c0c4105a510b1071842580030780c649020010131a08010098201c00000704140401303003c1410040240308040003881c01c040d01d4508800c0004403140700c065580701c030303ca1503551140444800b503a5810118200c1500b180c10781c0c1420310307141ea103401c3c60010b800d20a200b40d0703010413815032000855604076074020f0802000141045142282240000c00e0b540c1410b408100380041c9541c82c0c0320310740c424a00480f5086d01c9003400b00000f801e69a440d082e181c8000602d489107610342d41c40040d130070108854030784941030445045500c001e441c09944006403101e004002d00045 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 473255188 1250 473253938 473253953
    0x1209021201140c0a02120f0f03010f150201090c05061b01020d0c0e030d08060105030a020f0304030c020414010608060f01020a1e0b281802030706030c0f08040203060c09180103 77
    0x19502d81250701d81c545564041c1100541c0c050110b4090040c0d0082103040f1b21154910003d00b41c2030390b20750309589001660008144140d10a034480207003014036441c00c02c009110013020300c2040d10b05100070b04c0031203419207403085003071091b0190a100b07240c0010300c0c0002c004803802640600c5030301e00003907403999250b548030340080402c2e0128030089118240610034600c1c000c0b0311801241e035152601030301174580100440380d54200a00800c0b4099080204108264414000d18410792180e0303159425400c081c81440103980c41c42034480c003640c1c0d40703c1c01440815003213660725500c10400c0d108841403160307600040b403411114400280005032410ba0003100780e1190342812840d10b01450b80741001d91194039802c02d084d10140d003003404882040c10541115407181d0050a000c00e03001e0948181c0e0300982e0006030800d602940004042a0303522154184190400c21903840a0110309003542c240c9841e8003c40d4662800a010701c0c540000000d0561b100d5039500344215030241c008103502c0e006d42c1c482c85c1109 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 473256438 1250 473255188 473255201
    0x903300903020d12020304080f1b011407030e06070c080a050708030408070b010f03120c032f0c100c020409061806020a080c0903030d05090c03100b04060603060b030103031209021201 80
    0x3000513000d90f2226401011900807240200d80c4248420716085025201034036a130030200308409030200042d40103c03026024081c141d86010f8080c0e00643d24184403001608460040b074890500da040407042061590b0000c90582e400346c0c12183c00303a0b9500340100102c0d0507110b2840018541100802031000b400b41d024003a188483c0b051884040303030398030b0718108090140c86201c02045542020250a5018803400c0185100b038840e0811094152072180700c1c45201859540c0a1035480340242101d0a5602c1001404074102048c1c0e020030058180000c0140082020240a07000d191a0000c002c1000042e0340071564584078220800780318401850884080d62101d005807000440c0d42c00843d00c0c044840c0d00f2030302c04210080080d45064040b51400b000707402c00030b04043c01c42c015002200030350385092200300c002144a1000103150729000702003004a482c1604204c0805141c00c20a004a0700901c0450f03040d41d82504203102d0411101c081c89024200cbc3d010020b4100002900c10003a0a40541004 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 473257688 1250 473256438 473256463
    0x19090c11010b01050c0318040603060c0c02040c21240303020a0c0f06090e06010201060b1b061501140f07060212220203061314011a01020709090330090302 68
    0x1d1108203450b10046442c1e021394030052a254104200010102d29910b0b000c00c181503010348049070300307030766900c850303044406003040c0f0390214000e00c0280e4114603140c452010100d400f411300041080904101001500d22080f050040b0f40d83ca49980702200c0680c8030b2031010038021805d4540203512481c00a40710707180da4404450600195201184001c070482c00304050715055640c06c07646602e1b040020304191001341000e411740d5070b2a54007080b01600100140251854840184016183d401010707140000048c0a04603c06202da20140b00742c0c0d00c04642402c2006649003180c039a20f4204161445100e0108014449440002d6000160a100c40010321880ca540300c095103202c0c80c0254012010645031000358150050000a071003903a500d002549498004d0415401030b079480c61945007141d1082c515209850021000e115140d82c0c1040203001418548009005801080d9006402c101c020b502c5040c0100c865084d120130b015103506004c2080c0b03000c0d801806207581c1d0703041c003940702e01d00c111a0 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 473258938 1250 473257688 473257691
    0x607110d1113050108030a050a050909010e19050906040209100f0e01060806010305040335101a07050d1d04051515071a0406060519080616080619090c1101 68
    0xc0440000c0030f20829040f07030030740d1024601d82001e440d01250b83c2d0344104010b5041c81011b00942100d500c5500340c281c060a48000c0c0e0f03201030704001c2a401c804c050030880741e14501d0306010410843d01d2010507030507002036040e540b405032600c0d10001e000b014031113604100000030300d04c240082c50700c010030b50907030480e2001e444070526508c1c7c040c01141a180200c401030042441c1610000d0303616181c55100701011500d420042003104602143c50704140c080d1100080040110710030b1040750b040f41045038076080e191895900e044030039a00c9035190b0b8202c141c400207010041d160f4828424491000c9110114010010001d82c604a440f0b5100100100529030003404050a5a400205050200c64505401c034000d1900700c54090b40c040280c040080c0111422504c1d8000000c0d40d0712003100b5000702021048411017824181203d82d443c144d0020040002c0f4615030304012800d9030070401d026040304082d10f420450100e250b0b0701c11413000b41c50344540d5100b8905451951501d900400400040d0502c100 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 473260188 1250 473258938 473258959
    0x20405010f0803031603020f0408030c07050307180c0302040306140f0c03010b0708180a0308120703060f0b0918070306031406010605030f15030105070c11120304050607110d11 77
    0x181c0c81480c008a02605201d680b00304042004070f02d405000009a414a16000d40740050701034248503213030041c1e4407070401688045001d602445083c05120b014250540040011510f00803520314100c0a0101c54503a15589840c00c460440c82501120301458000303805003d807018840402d1440d01048940790203000d050800b01d0b2118010b10200c9040b90400080281000042d40b01c0c0050ba50140c110800360680e2031030450400d4842880140c01036020301c2c45982c40304284100307920201402410101011b2400d2014000d0359050762041056030240c3d980780f030300c5e030681502180d8840000c01c4500071000c0d0706e8040020312641600400d09880c8118215104000e203004003d40c3c641e0207025010201e6401c1c40018151206001555404440740003000425241180402c1c21180c0503070f2203000040d2120100d005200200b01e900755102c1094442c40030f131001e0aa03030f03c0c0d00c0e400b480c001c86210742d2002503800d0600411110480d00342900404440a680136440d04800c41d92503803000030300640e140032 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 473261438 1250 473260188 473260199
    0x12080f06011d01030c0c1202030403141f02070609140303160201020c150606070b10141c110f03060f09060f0f01050d1a090f1e12030a06030b0702030702040501 70
    0x4500000310321903000e846160b0400400103501034501500341c0c0e020030815540c00400305074064050714610030300303401a40e5240e0642c10800c415000003204000e407940156408603c0c04404001d01d102c00700110360040c0c4424051038100040c0c4021440580b114425140c0112450300c0400158041e61100702449005d190f0174034281e080c3c1c02001c4240d402d9803c0180c05041103410402d0b035a6004c00010a4640761500341c4c0e4851401c040d09580310303480042c0b108404e106209089600d43c4110404580441c1030360044040d1511590100320024628000d13103d8030b0007180c81d002d142118110000f0b09580991500c0303620440d02620880c0c00320441e104020116080d00701541c2200d0040450340300b07881d0160308003030034060855101c290483c0c0c80442c10000342d41d050f0900e03882c240556030300710240420400c862005407500c250f00c0901c50001c1c40b04e0300b21210700100003904100c410303078a1000f2a10396031903100c070300300a101e603500180c1112424400c119000750702200034a91103100311400c000301d98984 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 473262688 1250 473261438 473261447
    0x1080106050607111c050102370e0a0803180a050114190c020a0306200a0207050405100503070602030a08090a020109030b0a0e16030201030f051003120c12080f0601 72
    0x52007480e4218104004030400f203040b0202e5000003030805440b02c03031481d070504116000c82c0d03080300c0213a0303030b0740d5011840000340c0c55503450050314404180384042144041e600100d086450031000304050284c0807414000c952a0811110700504145091326260000010b04030700405441c2d10300c1d445810340703000109096004008003c060710454040c14100030b001d00c040751003d12040d2108041c41461061140141d44009407000030798844c81002c80c40c003040740803603004021000002d40310310300d00b406107503402c0e0360008404045440488022400d40c0b207140146884400982185426028500d801304103150004018882d011040e41c8038541980d414640c180c5540c001c00c4000c2c006003442400f0404110459496500300204c1c2d03c0001d0391681011102d4684a0380511030324140141c07034010000e540e010703c58000043c0034030200f84603038501001102408041800010181c0f0031036440d614035a0f202d401ca4481059005210b18100022180c028102600807100a020714040d032001500301d5114 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 473263938 1250 473262688 473262701
    0x916090c0e010c0312060308120a05150f01050d0f0e0f0703030f032406091403010207110d1502030a021306030902151b060a0507031515120b040f0605010206010801 72
    0x95500c001e201e503a420011150403c0c4404103504215615514900740100f41c03050340000d44c840e52855035542c0908030100c4070680c0042c14041c816181c0410800d01c0003060340002e42d0755004482401840b00c030b07240182c61601075071826902d418036054140d020010254000b1f0f81011245c400c8990f52181c00c000180d45580c3c0d0702004000034403540804910500a40143c20080b0700180c0751520881d0300904000041201e0f404100054820401001140d074411034441c0d08000580096240601f941c440c01c14603451114003130301428407103074144107110030710310258600d885611080d5079030f0134013117651320103900084889035600108103c001071b5a80207102d0f201010341c0c05460401010341400054500e6001401301c14101c04a800d098120503505200741d0388a107000c403100054a0a2008009080f40d045d0100900c11708100c550034000001e620240340070850341450030076240301070600007402a106843c01135400c1400c01d49404205030040d0064426658280c4c00c0b9200e5a82e1032210754280d840 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 473265188 1250 473263938 473263961
    0x120b031e031b0a0c29070b06010807171506160308011806061215120807170a022e06082a060703181d0a0c0519080601090806091609 58
    0xc2103a810007110a40c88158104146800e0300d5849817095800040c0385030344250000c4032041d092008102c207668001c1011500b14040d498031480002108440c0943e4500c068a007030795070449205078861540d580000c5a04140d000b03080307175420407424900541482ca0a0040343d015030940d184d00054218944146070031518241d0f01d041c0031020449041d002002e00302100e410440311250085078440461184868151241245940c0c4074a14207014010f44103034484011085010490a0b07044c80d40000c1c4000760303c2d08000b6407000c042d00690300405e0448d800701069540c80c00c114002600c1c01000c07a103e0b0080e00c00701084030170310781264804240040004601f0740e10071020b025400101b0b02c01c44400f00042d0314035a90041d03145e125107121100001200c0701c0d860300e0b40036100700000001240100c41c007203030082c140300d41465504d0511107400081c2507003d00400c9450030014441e40c0c440d0301204002d00d03160003035a8940c1001c1070003985481c0c0c0104002849040c11000140f2030a01d403180806195 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 473266438 1250 473265188 473265203
    0x4060e1219020c2106010b070809012007170c0102010b0901170102070503040f0815040803040b06031006030b100f12020d050f01020c0304030b010b0a120b031e031b0a 73
    0x103020107081c000341640e40d089103003140305441c1e0304945a2980c1d14a0f80c007881d414510040b01c0105103d002d45050016002400340500a00a450004030880180c803200d40302401c0c900e0b4200d0741d04052020450024a548880380b150100028800082c0100940408002c0e0140d034072280350b010040e801d848901e0041074000080c100100000d02404620041041203031002501d40100364442a103190000d4009010284c8081000c0040000400050310300203e450a8200d00d80781948603401c40d8000280080d1568500000082c0b00355014069072006001001007000910784908227050f6099040b68414400d140250307000ca01c0d000c0310340703168045560300d003040715034000c0d42c0d8280903107070031541c1c0304903240e12401c400c0350341c03030310b1701f80003134a2503004940c011604d8500d942041030002606a100d282c0300101003002551444c0d0040c4d604c6103a0712003480118000c0c188001003850b041045041c805005d0114698500c441c601200030003c220000102e24588070701600c000d61901c01801c001007940 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 473267688 1250 473266438 473266447
    0x51c09170711060c01020d2a080f010b03060d051903030f02040e01120206070506040308100b030f1609050316031a16031503140d030507030b061605010207170304060e12 74
    0x1890041d00500a004c00280054248040c107201c000a80782041300740350724003025401d0221703400300c0303002945d40302c110701c0c03400415506014004004c0725106005014130540300000280b100c1d124400c56a0040342d000c0c0441c1d51008805840e8046144120021000030f420a00a000c0d6080c040c0203032002d440d680319443d00c0e00d074179120710580f403802076510803a00540700b840680c010800a0200e64820390017a112407049107000c07648081ca4801a400000c6c0f00b400c03e000703104148404050707066005040d100345030081d03030050341e09466080459000310350600c50082044015481c40c022001240d20036600562075006186002405030401c8608403110307002c4840c144031151294002e0740110490300d100300d1801d51213403580c0a440c00c003001007010303d51041034500700c299810322072039500549070b1901f0001c01c0300d80e00c000340c840d20460304104c0200714490403107000e015007941181c225540c40a1090790f0941010440d10094000310340607127695182c0307080f141d0310a9010552038903490202c42c4881ca071 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 473268938 1250 473267688 473267723
    0x5010c141903020702120d0906030b0607030807050705070b040f080c0306070225180b0906030d0e1e1903051207030507080d09150b030f0708060a02030601051c091707 73
    0x1d4101360410390f4001d040881811012800340300b041d4410b00b80d41e03200c11845c1d04018014059032200d81c0d50602540d010002e02c0c0110703510141150300013a003450015900c101904041e03140a105411086904000150002d0722440890100046803010002c0c4d07041c00070503404140c0c0301c0c041100d01901580241e020170041c50f480305480c3c150248d10410710b1910a48404101d032404a80e422640c00325036550700c0d0b0703403440c1c80d01780101a80800120018a00e5070100c80004040644141d041400b807440302241a080c00042040d1034900500580410102c02401a00500820207448151490b0061030030007441c41c0d22070b030101c0c1d0301c81c1d4241d00c5040c5048495030300ca4000740d0058170301c449100d6a41840764005059420240001c920394000403512800102c20107051a0444140c1909680084000c00c403200c0c001c28021b9011401c07650050b01d070780d03ea10044e2405e2140d02000109074052480c452070402d81e0f179002070420786c0580480074016502200460f01841842e6014180030325020302000c9 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 473270188 1250 473268938 473268941
    0x10518070311010e0d06050106092102010c0209060d051212180601050f01030b040207030905040e07050d140a330506010203070204050c040b120402090906040309090c0e060705010c141903 82
    0x3d4130005040c000e80902c1d00d03141c0300221034087c0c005c0c50005012440c10440000800c40383d200c0d039850742c0070081c00304066a0010b403c020300d421009001b40601000034006c3d5440c0f140003411039420000b512510900741c0b11043d5140d00440e01c1c108440411030114011400780819066101281002882c1990a0001700a035003041001d00798105611040203443d03e4480f80058040d00b442a10f55440b41c90030302c0200800d451002103014004d0344007440400c00355494000c1c1042486e00302d2040c1604242c070402e000c1c148081448042c181c40c12100a00c9000c81c0540c0034400000021905e10039841040c2141310181e030425030381580107a0060100c1d8025240c560700003074001c41da101000e85000c0d0361301e08102c0c41d5000b03c00d100110405c0c2001300f100398184000641d6125141c40701428840c6040d650103850780119001d901c00301b82d0f84082e801b5416000704006001c070080244030545585c03a40c079200b406440c0510760100040c2c3c00425000a140200098030f04525400c02a15a0742140280440 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 473271438 1250 473270188 473270207
    0x31c0801060c080d0c2102090307060311090a0803030a050f1611070f06050901080a050609010e040f0510090201021b01080718030f080405091e150d021201051807031101 74
    0x102e0030b500030003910044d41c01e82d00c02c010410045445000e0802031403401070801d4400071b560715001e0b50040104070925039001c150070040e18500d0a0010b00c00a0071911320142c1d0040f2290320750048801100801c040000002852050031051000d004a540c0c2074948807440405032a0742004000304010004441d0040c28002c240702e04c4030040720700300c0303540e01440300e840c68003680300d4004600001645036031035910102031a88002e06000500c400d00b0800d01007449450144100801d80b030744400400c0402541502c5216256004011a1021441c401c04440205a8030070100d0161103014203003664050100f842050b182016124441140d80311034017a212244050380c0c142c1c2ea007403c0c88003c000034118050901d002402100442d0700e03a4100002c1c8840d2a50140120180c42900c080702160002400c50701640110406c81c0d80306c800ae58907000c02c5940701d5082e80294003e034901005481d038081540300302c2c400c0301d0405c007100d044420500500d031104084d000c090642441c400032032081e0f5000751a0b20 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 473272688 1250 473271438 473271443
    0x3031d1207030c1b03110117090c01050a021002070318050f010c020418020a09090b0106021c052a0a050142230f100c110111030f09031c0801060c 64
    0x80e40071807846131072220b40405580007107420500d042c5c83c0f115596804405044542c2118401d4059401c02900c801c1d6174a040401d207904204002401200041c400d2200800219484005541b2405c0b24a0040c3c41c1000d040c0e41c3d800c2c40300d0707140e000188a1a102507000846c4038182c4a20402c00866000d00c0040c3c4404036240d00f100e4400100d050042c2c549018003401007a0107100050800060f190510042c081a1b0011045600c00496859480807040d06542c90f02e4560400c20703503852106880441c1b03011000f112080394184030a05010700d0002040e01c41280d4420f01c000c00c0f1401050b000c8035184211030054100d041801d1114203103003030f81500c22814480320848e090704039603911280c1e81c1d031984049440c1003150f10700b031079107080508103640c1000002800f00d415024440088000810500c040031000c0c0441004c03601c012250390084003180252308034402529642c00d61941c4215907641300c08078650103441042001440b1591160010240100715176070310780740743d10300f0700f08880600a00005 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 473273938 1250 473272688 473272703
    0x609090604180f060b09060a15120c0c05070501084c08071a0a0806040905120c07091107080d0e100b1c120c0501110703031d1207030c 59
    0x4181e00070320400b0340b40d07014454900281c0310b003207524049065901417103c0b907020321106420300a1030b0f80c4004082003030310801d074840c041d1611030800032070700300f40f0070b40985401d94540708048914683c451051840503010341f04071483c440d07445004460b688011189440500ca65400b2110010b55081e802c20b4a440007086030324007a089805442e020040100000c5070b00f142030b0004101d4944107102c684000c080180300300c00084c0f40702000c1801d0b440744884410401c90362500080c010703510760b800402d196070450102d4910304041020b171000c582c01200d80c6034191086400c0050100d005004800140324458101814800207030b44422403038001c500020045611015801203030031080194030f0b0510404100400c0c4100d1290a020701d4840c0050650318942c8959142e5001c86c41d111411071074070341145820700081050b0b0030300390300510030451800100c050000e0400203055164001603102044010f4005450300a0010944d44002044c94030b5402c002c11f0015401103030144405850b03640c040c804 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 473275188 1250 473273938 473273951
    0x212031621021c140402040e0f0a0309091107151104090213170a022b02090910060b040e15010309140609010f0207170c16080601031502090609090604 66
    0x3400303071800d0340e503205604482e40803030300c0c1c00c804440202400b8014021801000403000c483c0000e0300003600208081d01660b02e4030b418425880042208500604801c420345129620919004001d1121482140035280c20a03000e100070b501c402c411148076507070282a880610740020031401c06030400c810041d0100b40284800504c5540900040c8100300400c0d02202c0c1d0a414240460160640a401c1185503408250707a400142c4541c03850202180c2034010700b40b04071068520303800d0b030044003600c001e4110361f48900303100d840600000c25580c0000c1080c8203028041e00e4101c031803200d018074030403c41d85841d484081303500300445100c52108940d040c036011414800355118945c22240c0203403013205503030020f802c011111100b0b10902e201c0c4070301c0010a40c0b5003000ba4484102071060240c022000107000101c4ca0680f113010004c02c0c42d1580a0505000100c0d644c510058031100b00344415900c0011a06070306125140300d00c200c0314400303c0180304905100d01d034010b00c01407a070020000c1c3d800650340d91 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 473276438 1250 473275188 473275217
    0x204050303181305240402040503011103240109030b070c0618030e0a0b0f1b15041b061202030907030203060108210901020706080c1207091502120316 66
    0x80c541d40c0010038560740c00d9000201407050702034440c00380010300f52601051000a12417035621440c41020b0702d6503202d86602c03201c0001c00a10a90707000310b605602e841004401003650201940c481e00360f84850002c2024500310b400c0d10f600000cc400e41c0040e04248062001500b0111126044052031400d081c508045540350b030201c868116507428640d014020304400c16500828a1625807411350307501400500e040140c00240c001c00d1141e600c3c1038000b00d20a181c80806140c0a06e071002c00d58219403203110f0001c1901c9028501f682c0595140142e5404000110f00e01c9420702c3c212515a5100203011002000310341c000c2d00041c001c01050f0080e003100201507902085034a0181c184000034060404005100b160852241c20515032072200c18002803406a07004241ca5084a00c1400e044020b03070750b2816142d01d03a200d070070800407401003001d0a0000c8150302a03260301c1960781e04403840d41080c03c401c406070b9542007551a0b4030385400040000405c501d585640400c0590b150b424051140b01c40c00 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 473277688 1250 473276438 473276443
    0x406110301060908011b050a0509031f1b030b0307270501061e030e060109110403050d02010204060e010509090403050c2b0906090b0d0b0d08070308040c050316150302040503 76
    0x2a031220b030000355000c00078800f442080c403e044000c0f200d50b15a040071022140c02078101d0280e40200c1c024042c001c03030f0f800c0c0c198906200703981034042c0a440081054034500c55200040c00d01228400c3e00000008201c00014002e10554a030f48200030003e04440d440c00d00140541d425103498480317000711103034603a1401243e60007074074040c1101d511074900a1000c101c10001c4c0c039078004070f81c0d0201802e2890b5024030010105000341503030400480468040700e0344039030341440c0c85994401486849041c011020f81c49d0b040d80a0419540c0c0c1c0c3d40c81043c00f03841035004545234001c0940182d030040010000c500024090f40c010207030b00030400d00396882404411083d2102070400310100c00312840c032501c038818081d44000030501912720360420240b020704200d0380400030f008110414240641d603440c2000d035503031440e074011141c40d8040c02a594a4040340350041015100345c400b15807000703000001050501e004030701d0300221142c90a46254240c81c014201304926000c042240c1450b908000c081200d490030b = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 473278938 1250 473277688 473277691
    0x20403080a0e040b181501142101050103061805090118350301060507051606030b0a150203121003050604030f0f0e151c1e0b06040608060904061103 65
    0xa440303460710040070b90184010b569000107414810b881d101c443c0c00b800d0072030601e520b0700103100302280a5001010740040c0c40300480d082030103a42d0100071400b602d440c11081c0000380c40881c4560514040c0c0da80d200198140d0b000340c000c1815003290500240100922940959440a440030010420600d080c0908085501654040e1044221041b1242d41c020b0038200120f80080e0420680c0d07000c1080e50341804207030106000700b4080000028044081c85801c200440841000300481c80301281d54200140042030004126802041c400e14001040080b410140b004071303003180c01440c41e1080d44400c09100c0d02d80100012004142050080b001c02c4c1c040040c40c1c4118400d4640b0b003101d903001e1314041d22800fa410025410131900c240c0040c415155084000880524a495940c0342c01421407110710380900110803030303100307841d00e01001408501080b1141c480f00904000b009007100d080c040c02103c5c480ca000d00c8001c1448440414154103000d0600f40e4042d00078980020100201e20010035150b00 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 473280188 1250 473278938 473278957
    0x1003150605062a0a02240c01051608091b1306080f0f060907050a15032a0e060f0301060804050724080a0c1e12110d0c0819020d02040308 60
    0x80740100082050112000b500182c1580000c1801c4030041c1d00060708401c0c01d008400804808900c000d1482d91744001f601d405d481000c00034005490102c6040010540491706140002e42c405e0210300d9181e80818088a000c0708480c0203003030182c0030000e0202c0c0e5540c01954000309544e8a0700018004410311205210700307041c50240800038003021010340342c490040d003e001c5ca44c000c0a0108159552001100c04882030021243c9400380000800e4000307090103000001e1410a500c0410b1580c043d0b82c18240c80b45615840d1080984101c00c1401020301a0507041c8912240400042c001140a010150303885489081246e400c2921040d4803060311040d00e1003c0b10300e000b08980307202d51541200d50039500044e2440100b0020302019001001c1020700c1c0100b17a14540303046a2050218441c00300c0c106025100201480950b0b1542000d608c00c0d400304140070403440c0750041c0303001c11520421400d40645160040b803150304d016100d1050080d8886000000c48070b900f040000005004000038165088 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 473281438 1250 473280188 473280217
    0x904240f06060f081e0a020c15070809070617091e0312010b120a0f0b0315010f060512070e0f0d030c11090105100309060605030a0807110405100315060506 68
    0x28a0b04901822044146142e40c0a0103c2e80082040c802980c69040d1260086210b1498081e29244070410007849070740b602c40e00900440300509400c0110380702e150f008803000d0742c900584c0e0703803200611a1203102d50300506000840c440001c511030240300301115000498801610302d0b143e40d01002003920b440381d00303211440b50000705021142c0f0080b6a040ca004041000500e8038124034800312070026800282031004a0780ea800824924210b5507004240d980d201800703c460500090100380c0010209105111031910a8100440c80c14443c0e01503420000701d1104c10041502c80110a4404080411143e90099288252003020b0f5440d000d00711651406521400e07030608007802c2440c181741c0241075441c05014400010002c2e074940c80361415050320301d85000604860f180c58400080e004c03a41c80150701d482100e12801c14890920024458244200460390200344080c05100070754000b154140646040c0240400c041045100c1900461140700400640240c49100050f8542c024440032105007 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 473282688 1250 473281438 473281451
    0x1224100e1504050f0114030d05071509230606060c0c01050a02121602130510170c040507021c0e0607080a0201021308010c1106010b090d02012d030b0f0904240f 70
    0x31591b540141d140b12401c0d80079185000c94144080c005200f9130400802c068032001d550400c200300c030360003085c2c21548442d10040c110040b00ca0100100348481c440455802960042001440c104045800e515100710241c01c141c01d0b030800554040c0c02021f020360070340c0600800158120840360040180d8100c1d0500c0c810034070380f5801400141e6142a25041240d8074190074040e043d0720140c5020102c0b19003c0c00c0c18668082d010790b00741011500686141c1181c20a01403068250300441c0d1541200780c80d03100b5001400d20044115000c40c4008005500010200180e0000c80e041400a08403100306000151520300198000d445141a60380044a940d41d00d240b510041a0b0041022300d41d149181d00406255042154114451080300000744c030810803002000116400341810000c00040c6000c0f41c46081c2e0790811041602494408100001c0e240404205241c50302ca00e003401b14000c0509040c03155a126605e548031464180a8a010740002600051101d001030203022080c200c01c56010030030 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 473283938 1250 473282688 473282699
    0x30504170409060e0610170a0204030f11012a0201030b010309050d1e0203090a090b0f090411040c2a02150c0304031b0315050408091224100e1504050f01 67
    0x2944800340005204090141e0702400c007da004108003c480c804000000140d1074441c213075002031207141c1c0010580395a030340c060f900703002d440038201036103060a0b01c50075000780f800c400c05060b4401804841015910782c0100d00c001d54030a0741720381155203060500144030426900c440e403420040d00328003030028540e10310041d0b00903406904c1010000307503400110b04006000700090760740b00c1319000c0e0004060703860f06050410391b1209154030302c031030300038042c8840c5040030f060044004284c40d80306070159040c00c08010f5003610074180c060507101e107110300c0f0740c20300e03d500c002c98071a5071804416a42f002d40d010035041108400780080c400c2d11000360085981310300e180f0307003c0f05040da40e4104051003421400304001241d1540d0456103c400a51301c005802d50301d61038142c1103400344240c030940040340e4200b0940c151400103110102d02451425040420181d0b8803140c4180c1402c84040a0780c6100307803000c02a80640521151b04181500d9210301c0e18400040898101c031021507040403c00c040000400c403 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 473285188 1250 473283938 473283959
    0x90e04080d0f0b030a080904150f080f03040302010906080426180a030b161106040602040509060d020109120201020c12062401020d0f121a01020d03150603050417040906 74
    0x582450704052100701c5044000917180d00411001800030b540020300b03204541e03107031f03441501c07484101098114865102d9003504c01250341e40c004c80c0c013540705210400304412000000e480450368143e4600280a042042c11501d0100150003190b40c041c0300c1c240c811401c0021b08000200c9a602c01101d07850390803000c61410144003003411180504d0001030140081060300741010703448005503140500101901500300c80024441031864000d000301d0040c00f08116007a001401102c0f004c440881e80c80c1c840f4810450014a80c0341d0013400300b03811400400882101e010108020760050054912640884011402e5004084030321565500110b0401607410ae00c004e1119041544180c600918221900040e540300d40d003189400c10300003031640500325280704503480c0000601c051001d03c0b03515280c0b030182030a107007100295070150251200d141c1542d4070a2260082c0c16503044003900b181c40c6810350690081101420030b452507100703021000400f43c03129008100070004241300007505032805c8241c50 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 473286438 1250 473285188 473285201
    0x203091302030a0b060403050a02210f061602031c110f041403010c11060a050a060810092f09060a050d08070501060509070519110d0801050406090219080601090e04080d 74
    0x1442041c081c403007403001ca0723000a41402210703410386000110000c140b403641106140110303803c265100302e250b0760054440100301c050288482041003050b958001005a8890260111400d50800d041270b5001a48409402025210183c0002e507480e002c5051840c00d020361054209034842d048180401003182000d11400318540c4280c9044c050300c1801ea9005a1215405840f152082703460720086410f0301c0c402d81c80ba0000700081004c450b01e1034203002150020300743d5954207035030f00b880340760031858603802c805d52482c402d1041c8484811002d04140400a2031040a4401c81e00200b0459001c101c035210b29925200c12401074510b15241c420b589011400d444e03035900854003549001c0188181c494210050f40d0341c00c0541000c001702c1c1c0c01840300c100e4914102c040d10b000326104030245400c0c1e881c2c000c4c1c0000d040c3c1d28207843c00e00c0144c3e00c42c44110f041c0e03c01d104803a06000d10201d03000700520300c10482c06800520515110400369620341400f110001c0035181540d0072840010460003281c0a4420031 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 473287688 1250 473286438 473286461
    0x50c0f0c0a0803030f1b0405060313030e010318080c070e04230309011d180a09020901080604030f0f1806030203090105180601120501150905010303090806010b09100203091302030a 79
    0xb1491352801c0e5811400940000d0000e2180c115000810700c181003004090f5400740c10041d0034992645440410411954528001540810540c210319001ca5109004400020302c820161440038190703503485c01c0c07842d400414030700c034680100d01010891600502156020364042c00da503140c0d140001c20f5241417400b103064101c405078000c11407482d1a98102c584003111a14413040c1444005040c4045400000158510380329070768104c0801003c104950300c00c0007054000d592090031a030f01c890a90740d036441e0030340e80680032480603034600701410301c0b41e10407000178002441d000450304142c4e6000a13040081d0b400403800720341c0110408c80c01e18001d01c43e99070710843e52501401c8046010f01101e4580006020b02c4202403804000d405c00c2c40b07000d400c10441c40c800100c00c101341941d5a41800014942804201c000400d086e00c009600c0600064080c141d5803d90b006503d41141ca10810169040d03a010300030942c001804a41000c0c0e5401c001c030407500041f00c001594a00e0400700a404607144c00450 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 473288938 1250 473287688 473287693
    0x80703020c0d1d0907110f0a170703090b0307051b0102070c05040e070b1305090618130f1b090c020106030309031524140402040302031903050c0f0c0a08 67
    0x4040380490005038030500e01e907560400c001199140d5220a161100f404400c0d50080080380521419035032185140c81d512101e441981c1d0ba0400349420251501e088180241181c00c601512400c510307410002405081e101f803d00d1a035440c1c1d10030f04240707580c1084031258007150004c42d003400c6101c0580c0506030030006800085140103100e647e008002c04860040e5030165a45604044d0354800401c0f0440250148000c1d25450707a490600301d1400031050b015003401346540d08080703401414400a0042c070700307114400c00680d50723a455540080b1011400c0c02610540100450040407502d812035610a0102007030a80c2c01590074101a6802c3e10140b03041d500840e1b00d014420030201e54800081b00a03030b90b206042c40312802103100c0b0507001e0040c840700c5d0b58400b003003902c4c0210803141c9001c01c030b0103c0e4412010076240001c2c01c1c0800049001d94800a50185c2001c900c689488001c1060f140c403c078842e04095007400408007107113140c0940c0040b41125544414154410b5207400e14101c030080101200 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 473290188 1250 473288938 473288947
    0x10e0a0501240f11190212120d0504020307170d020609160b0309012c0c150909061f0c021305100501200a15051803042601060e01050108070302 63
    0x180c200a441c8004030042c100152503241c2d0350018840d44016981d0341c00c440846140803081004a130030012810012885a0300c61507103000c48800100ba90b502c00318004001d43c1c10445403840c0c035800f0b002c00074400c90781400b665001080005816402c00341c011a820014a00a018440080e1412070003600342092580710b4a008010300403151562025600c40801060b125140c0350b50860140c040713242140b01e0315885003184244090380a6809802215807021181440302080500518158822403002e40b01c6c801c00215940341007110744035404c40005800c0c00301c42d10798001c42004c411100c40042d4001f0724070403200001e5140111420010a041c1c1c201003005040007841207142074a1840707802d050001162a00381450341c2c59803010881800346080e940701c0c0140b443c05541c444000021041c0e05494400490b42c0307101060403401300201c0c428015071a060034950700407240100f5004844e040c008000c1d4400c0480c0c028010800100000030b00c54031030754100350000d080c01c0801040e17001058410321 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 473291438 1250 473290188 473290229
    0x603050c0d24020705100e0a02010f18030606050a05010e1c1e050601060f02030909040b1f0e0702010e0d0e01080408191107150804080306060909010e0a0501 69
    0x12080c03990041140c00007001d5081d460070380340488100034407a40c410040c1c5001100580550010b1500c0c1388900142c502d00c003e1941e101c8101c904001025030b09a00c40c03250707000154018040e002070b030145820040d1400381007601842a00355070f60421a44503403150001c010360304014450f40f01403d03003401c4c4519505500c0c80850034144420002c40d0000e500204001e05210764070038040c50f1710394082d29901881415040460740e13600280b05080c001119411f18003032880c40881039450004008000141c03544036501c9440c140d03000580f1040e804210181c0401d100b041074118107000b07000e11500030045240407034003c0e013140c02a4402c450b16030400c1a0b5074444031350180c80086140d40900f4025415160380c1000c0115003d4260380309040342c0246801e41071183c02003030919201105030121007146403280c40344454402004c0c03001c9c003c84c0c0840c01103000920307100050740e449400541868103000e41940060422a4280c0c40b849010901c0f900b4010041c04c0d07402000c0c09050303c841041ca80b1010300c03 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 473292688 1250 473291438 473291443
    0x40303140c0a081f05090c030609010f0b1c0e010e0c030105010b070f17070803070e1201060f06080c070606181a06120711070b0a090e160f030608070e0f0604060305 72
    0x105090340366013050400900700000e16410a01420024100050700c0c81c143e21040780c260300030380f001031040d031000000007420030303c0285500a4a0068480328200500e42500c081388070402c80c0c1d40903d05490340340c0348440c964248035030f2101a5802d0028241d00c46c800003814210340040c0c0081c8a0303854104420804a8185401c400241d81c0c4541049529900c687e00c0300ca01e8010355200800a140c0001030020040e032040382612000021100d50707982040040305282200d810340720380c000145100c1400c010b0b4030700465a0540c0b221140c80407510f840d44640d120b40484181c1e0700a507960107008900051042c0c500e12030580355003030101007a4030141010000808a0203030408003c00c510a480020b440a03104022213505882032000b04c41800e138841c10400b80c150014600100010038022002402d42d04041d132240c068011f02a018807160b0724041c04480d003500321b18480e4203050f140d400008186100b00100c200a2509003161000340c01c0144510803100c1025051510035402c0800600210358003 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 473293938 1250 473292688 473292691
    0x60b0603060f12030f12090606031c0c0804080a051615120515030109050706181d040812190608030903060c030a060807030605070e010f080123030105040303140c0a08 73
    0x1120701e036845020200001d8514410440502410500031584481ba2011248003d0041c2405400c0c1c0c3c4491303990710185503070342d0441180d0100410b80ca03000800140d020b800c00380120342c0101c0031140b41c1900d030021507203040700c2e20104981c00d500039400382e8000e000d2802c1d6040030b06101035000b000070407200c80061541d5811300240100c2603441000c145060744485007800e08600103030081c030031011142420f13500e0340201e220b031002140f0002004014950424022001d45035811001c96000f1354100340c54641044c020401c950701003041058641c4201d0403440144152100d0082c1c00500e40b22681c0e140650fa0340c1d5201001940c003d00800b88180e80101d042a80160024540e030740f00e69840c040032001d4001584034021b07500405030080144151074020b20b100c0d04031515440c510981010046401802280008000500c160010b0100c895402c003400342c0f020345d240300306c0485004c0b500040d0848000b03a50032000b02c5d503284503081030030000c0600541e002484400480c1070820004028100c02e10 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 473295188 1250 473293938 473293969
    0x2010f09030f24150f050105090a090e150405010e070b07080a030b040f0c0e0405090c0d0303020702061317010609020a051e040b1605070806070f0f090e0a0603060b060306 75
    0x8101d074810003075004428207200f4200e52082c0310568141c1305003030200d4458051121404080140030a10354010811a8280c01000e45050042858a42540001e00c09403800c4d00c1c0c140181c0d00741d441003080152840703010b180a47c2c00040d030485103141c07003460101603600071040501c1c02e01c011400b0806403401c1d10000362080c203000c82d0070b82c142c000050040c0640d050448a41d45401010300782e0a5000307004070b14014098070200415140c5114030366039165125034450f4896080e01022000034425005071201a101400003418101d210f0f000900299664024200741c20605074050b1101c43c09029032001000b6100c2d04601d030410010f40105035101e108282001420010300b90030b03105900c841150001e1503859111521070162680e83c1c0c818001f148815621442080400316451401051080c05444c0d03913151030002141100066548404024509003070101e20000025401d4042c1c200c0e03441107001c42d0000503002e01f54500642190752501405004150520402c5615124078116541408 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 473296438 1250 473295188 473295203
    0x151303050301060e152b140105060703050c101b0e0a14010c0b010b030603101e0b040b040e0d020115030c0603021b01150e06011d060309120f0702010f09030f 69
    0x1130702e4041000f00340c41c02e00041081c0320020b5004a0f5020000c0343c106000d481d000626510480c54049600f80c64000001d10300c02202c000041000345001802045024481d081035420400c0d10080b0500b0031099100a810f000d44641c0010307816015004258160403041c00c08043e5020604c010490310002c5009410060310340c144240349980c081c0e01c1000c030840c2d015802d00c08075078481000861540007034600381c0c041e06c5020000310f0f40141038020072030740c42c44072282203c3c035070740002002c4007801c80c02c0e824641283d036522121480e91207074081d03d000700d070612000b0724403114552002030031a0308c0442c4040c210754280e401400010352069204084420724900941c0b80e00341c80d49203042d00d031030000140d82c140d8a0107290361505103404920400301d40c0390440da42c01580d80c8034010b54682403514018540945003200c0400b15181400295807c001020700b100c0c49007071007280300c03404d603441030b81514204100400d07400110341c2d010100c0c89a9026070301d06515070328510741e1410001a0040c40040407107 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 473297688 1250 473296438 473296457
    0xe12120c01241a04080c010309021302120403090f03020f060a20100f050c160c0518090610030b0403052206030f060816061107030b040515130305030106 67
    0x9809400c24540103280d0100c110440d00d1240000401c8000e42c414a580000c004920360700088000c000d8408a40b200c5000d40030301b074403020044006004184e01281d00480300020310044140c0c82c40501000d08004547c2c0178070b4206414003070045c4040d03502c00200750b449a00c0a000507103894040000a520035200da940321600e000040d41c5265580f01d0380da498064003060990400c100103140c203484150000304205005150040c08140c03101207a0b1040c1e94101000300c208044145801c18142e68043d4103542000754940f030015007580070352201b94108040c40c10034010f100d84180000c6400c410341c490300a4946103103941710015402c00810140a0100100d107100c2002425080b003d21a1103051010548130303190540074001744070380382410300d400b807038a04082086030000a0404000c07514801c02c001e00d0349042c8088980c1404083d45c2d01c0ca0780518540000042c000d50900d500442c80b60000c0c0203041c2d03500c1c2e050750544000408504101c28421002c0002c260010110b81c1980c0152910406a = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 473298938 1250 473297688 473297707
    0x815010c08130305190b0603060f04020f0d05010f0f18050a1509060c0c030f090e06060a0314010303020c030f070b1b0f1005010815190228030c0e1212 66
    0xb070089074405000360194864000c404c0c8481d581d281d400c03e1141119006540f40d0000341552404100d07850740d184000e01c030108004d45815100c8001c0c01d4002044012040c2403a0742d21030a4441a0b0707200b04c00c00b501c54000401030f003041d01035141141c0000380c4d042800700d40c41d19410356540001c0400703068620160704664281031550400e00300d160b081501031140103e482c10042c40811049070603030008814a46910816100c0c11341c00c0204c4040020100c0ba41d107503401048883c0d8001c40c2000c09040e0303102042d228010071260124004c60003a0080c00c4001012401e060410014034040925900504820b100f0716902006030791500e0a00642e01e080c1291b40102c0d58544030f4240080318141c8501d41c000004040c3c0d581155060380c00240c15940f802d0300d840d100880e1280300b5100040c0000d8550f00b11a103001d03160b40907001442c081c5280c1c175080c105100b19601c4c440040c02d0705d540080c3e11113064500c0190004440a03d1643c1511101210b040d40203249454648a0300304440c4400d00055140c074 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 473300188 1250 473298938 473298967
    0x12021e09060c0a081c0c021c09030204050c03010305060117060a2318071202010e100201060f080a0b010e06030a060906291e180720030a0815010c08 65
    0x4110b07a1060446002071030604040132540c01000304502c0145a003500989981c1e10380c01a105882015002428000341d8802e00d65128040d9011400811a1021001002d66a40d02030140169024610640d07254194240142040720580242d030002c4e045128000407401c00251840d4829510100050340b840303600f5000c407510b0a900365203100c41d03112405204400c1c1c020b00b1003480401c01d41c000c40d03d0041e84c441c1c450394814203211000c1c0c0402c100f008810f42030304000c400c0c201c40781401e200005a49440e82d4600018a100f6000010540d01400e41d140800c001403510501402040c0c800801c2450b02800017640c03642c1c1114014141d070303162011841000115001041500c901c0c108003000d05600c403020782202417181d81c500348240d011044417030341c6a84c05803180e02911406800c003404540704e0449200315400142c00072040114401089200810f84140d141403010f001c40610707550044440010300b5a00050840c19014489041d001200c0e81c101e0003540d600c0b07034800700d01c1351100c0c80c0e00303035520 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 473301438 1250 473300188 473300197
    0x1e18091b0438010e15072306071107030b0a020703121a03060a020a2307020d08181815010e030d080108101407140d060305060712021e0906 61
    0x1404030881001200c602c2ca04802c1000c0d14080c0c61079020105440600112901c501c0c3c00c00564021901070002175038000900e00901034140950240d502000003034805411094407541e041d4101e400074018408880d902c200140508113001006184c014110b40380d4000c40f103406850b41160580c00101c00003014012240e00101c03502080d801c00040007200301c0ca090a00703c43c00b00383d100b80a0000011241140307031003030b00d0403040c8079510126550007100299026070340340c0c0c2d8032800e22242408000700680d240707003005240c648034004060300d800544012042142403038030100e00c65500d031441e00122a01401c2c3c1c09031302400789000b8682403d14000103a5810015100352a01401003600c5001242e800090b03030303070482c0c15501c11985542c00704141c00040b02c0b0911040952880e060002c1100144501041c40e074124444909628007004500700400f1108207500848a40d0032400030040c000e0f400180348540d07001c0f0644103520380205010903011840340c0b59094180d040e40410b46070f0807601e4813030586 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 473302688 1250 473301438 473301461
    0x503090a05060c0903070f080318010c17190503090a02010e0f18180601030804090c050d02070b0106030f020f0712020a0203030408070812040b0d0b01030b1e18091b04 73
    0x82d403a506080e410100c1560105101c180640308404000880c14513940400b070444050001a600744110120030f1505865045402ca0402c402654184046a112a0010400403030301940b00d5940107440c031001a070030000007201040c00400d0041105d203901c0852101e5680e5030910709401048414070001c0c00e094080c00055800840c00c101503203043c04010605070180c104462060804603078140c1455840c0710900006101e0102400b00b0001014141c004008030304090900b81d040280c1418054101d0700900741c00d4078540140700040100e541c02d84140b25035119864420762130036141300c1c40c0744400c0c450080000c018803000701b0410f4480e072003403211001c0968000c0960707548541c0c421095548003154003810b14603006111a005076000a44110f40442e911412424101107401e10104010070201c0d111506058640b010759003c0d9689100107010714200d20000491442e1407028080d00c0c07810900300d0b0154900030740610002e03500010340700500e020013a52103080c0141507008100030f0305800200 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 473303938 1250 473302688 473302693
    0x313060902130216050f0a02060d05100e070302090f03071a0304080c03030f04120804200f030f16120b0f0403020a0f6c0306170a02030c010503090a05 66
    0x1076070003001120f0945244c0303501a10488641c5c600ca03000c101e8690f90202c070000d5102c08200f00391003c1c1c10254220a91200d0121643c456040e83d5003012a401d510032121a00000e0340001d4080c040d01e00b441c40002c0406e000d4000b080d0413030501c8804051361420001e44e8050403000300019040060903000c503860110200180c0e600c030708000d1560030402c4c030155011564080c815690854462003900ca0394401c40e08042c071824203205170041c542403080c52810340c64000c85250301350b4415490820200d40c912141d1030080c02240c000700c031100c00f0b00006410980c5542d0b0145001000300d1000708410f90040e005a290003401d0710b807071a06038034150282c0c4006024680c1d1071150000c1c403898040c5d428202a4403110030141c40b0a51040c0b0700340084c00c0100360034206d2034440354042c4800080c0084000c0f0f01e50b1048034543d40c0725000c49001c40000c0100c40300041d0b100d45062101d0800c0b10304040c8882c02603001400700d040f1550009440c0c4041a01c400d040100100015003140d20411245072101c7d0000c09 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 473305188 1250 473303938 473303947
    0x1a07050318030d08040b0a09050a0c0f091d0d050309070905040b010510080708071409090f01090b030a080a0507060b0409030306170f070b0a110709021c0203130609021302 75
    0x15018986100c03580d02030b109024040890340490f0080140d548501c1d409040c115040d503807920024020075001c0b005840758480c0c0003ca10000c4d1074403407a02d014002c4040c5e05011b5916007400b203400d544a000ca0303900b60714404407800201000001e0ba0481c0da0829050040d200c0d0780c0d6041e41444c2c4585503000e50103090502c070502040c0811741482c40d041e10070030307200c60501144500c01590b80c203100f621650000f03030021001594030752050030341000b080c00e0703140382c00d14010801c0001207851038240c0d41c400444010314010044c21502c1e11a020380c1c030006501070403101740c0a444454450085182800a21400084080400485601c01c071201800244200442401c2381801001804a40545196002c1d503a035944410000050030350007100a00004140307543c1005000391003030b04140b10b02020322460880e00300038040c4c00e118000c0a01914800181c4410450001c2e403210500c00c891524941d10410030b001c1040090b14a0030209a0058408620794026202007540c0311056a06100d58030310101c0d = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 473306438 1250 473305188 473305207
    0x70e01021c2d030606090e0f0c160308060a15170c160b070e0604120f08131502240106030e0a020301020f090a0902030606340311011b091a070503 64
    0x150300158018580d50304200c103c5c0c49410070340d440c40081c022410406118000900c0c0048824000345d0311104481c03c842c20710b490314034642c40031343d45440100c0103c2c22110812031241800320510000706180a42074001d41154080170304610002c510904417600158009070040741c1500446801c1c0e02e4542194109091500782601000300036501040010031400f49901d1528256054600703030b5100b1070071219810f215a50390032055850321021545820140b10b41c12003500d150061500804080e01c020140741c2c00395000a0401d1001c0c010440d00d45880305094813a43c5128011074150313200360500080500c400b459551901c100104000e60540c0009503600410800f1400380a240b08140c0c0d5850031551550081010f07800100c80c00760b00030350107102003000e24415001e9800403011800504040c00c0b10782d00c40451100c07c031402170700442c0306860706c428400c0d400d01c01c02140c042c119401d1300740ca1782c002800a004500c2489014000401580f218041010110440d0318aa07444001c8039520740c20304 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 473307688 1250 473306438 473306507
    0x80f030424020a0f0c0c0b1e03040b0601080108030f120c130b04050111010b1c1704030309051003020307020703030f03020c030c0c0316140d060608010e0f06070e01021c 74
    0x4120a000038542d00c008102c81806105c0b070300302c5142d125091030901c50511603c080b180d000700d9002204003850f107141c030580e20710200042d4021406800e2002c00c81c94410009001e074807041c0c1c01503400ba80200301c000e00006ca1003058038088030703d00d104c4100903200c1404045c864028846030b0505680c20a03000207840380500010412a1420780f81c06a8614840070030318202c0b4850350310180c00c4424080a065035400d21210034a80910450501100c3c04540c0c65062458000b44c10880c04100142c1c5e0030300551800352101c11407140b451038254510b10b001c0000a4488010b44030003414040240d0040112a0103a01915040c140000c100ca4440240498495444401800943c000e0055401c1301d100c2460f1010103a060701c031050000423581c00080180580d440c841c003016202c855841c0d60100d20000203009002918400e1303002056180740306100c1c9400d00e44040c0400080c0500b45407084ac80f642c02103403107103a021050346060404a102030065407040c1404480d040095048002c40c940c000d1030 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 473308938 1250 473307688 473307697
    0x61505010306050102150a0b0a0f0306140a0e030a080402060d0c03050105090112080a052101030305070b090c030c220606050a03150b0304080912031b0613080f03042402 74
    0x740d80c01c2c0040c80d6100016030711076131400d1004c19905540303800184031940c0740d0801650010064100303c0685e9584101d00d001d402260070446115445e80310509844101070201a003050034807104000b01201c070386e64242d981c80340700e9186c8140300e482c5000400703541c1c0d00d1060b21181d102d4410140308501201d40020010103003402820320440d1034000210724002e00c98141e42d104d03030f401580d442c0342003074400c0c082c0d426400025900380420307002c00400c621120b100c00c6080c02140700380c50303d44e2101c1c1503152444101100500100c590b0788411101ea0855070005545003882d81c09817444c0264800c0c21041a03134004043e061203180b11700308600081c80b2a40840148684940c1e550300300000e8005003c6d021440c002c9118040200ad0b040c0003080106115200030080c203200140f6404903c10308210785801d58214030b201d4451110050264007201c141031245039886000000d000c02d480c031450b82e42c45d40600407040100490b45c0007000140c20803684044601100408000350348280c99524201c8019600 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 473310188 1250 473308938 473308949
    0x9051201021c11041a040b070606260319050708040f080d08041106090612090106060f03020306060307200303090d030605011b030809070b070507031208010e060411070615 75
    0x86000800c05610b0707091103040c0c02d0928038240d1a150616150720080002a243e0300f140f0364141c10080050f2a410f01e100a000f06485010085070b600d20301040d004c0310402e102d4104160758101c00f100c600c000d101000721010b221303202c11015000410208211601d015010303000340003030000a804224000811601011140440c00715510760061030021555010150350092038000308800c0d40a0740d2a18001408100d44080c0586081401c8003002811103602959108a40d9550b024240425540070406481c4011581000d40c5941010030100e030091200912440801603842001d00003504020500d420b403201007022a501c07400c280801d40c0c2c0307610310078064a0129181090018465005000c800440407048889503182c41240d01d0a40c0c00000c0180b803943c490140120206414020401400f0424055401440141d0440c500a200400f800c5502401d0040c180010003081400c4205190b124030300b40d174049040032a4501d19640350040460050480b820300325112a05030710190403208075103 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 473311438 1250 473310188 473310217
    0x80102040f051f03090f0609060c0f0f39081215010e040e03130303200105091e0709020d051017101802190f0605040f030b06010905120102 61
    0x80c2d03108104820310000e448141c2c0b081c0040c400c40b002c1d40703009a000d409920b0058688640c04503003030b5203001c1182c510032412a501c5548003c000d4101f81d2101d4400c0102e083c1d42031024141c2c100010181544000c402c1c0d00944a109504038481544a44000303a400241c051440400c43c1051500041c1a0003484800352030a5400000031400140b10070251143c23203060315003290300d54004041c003004d00a20704001d0f180c0d100420104407a940e448607680700460090303030741c0c048100c00c00c0c8240004030100c50b048000c50703041000f4000f5100000ca0304150104403030f090000c0c0410000301c0a420800640c4c0141405840402d8034001000b00d07402040c0300300003941c03000d800e25858000c6844c02c05100003c00c03410358400d15140410709410b90010030b10303a0007080d82075007070400c682c0050243d9841003180855584500d00030400b00c0420820305000d002141042c5040c5824401c5c0400f803220302d480050001906480414016405810460050040904071125504001c035000b400b035440940c0c07010440 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 473312688 1250 473311438 473311469
    0xf1e010c0c020901060e18070203040e0f0f07050d2702040b030a0b060409060209090109022505100504060b120f0708030414040506011709010f240314070f08010204 72
    0x103038880d555049400340c0c02465051643d0078942c1c112407180c2855030064000b81e2001d402888605000078007403150030070354011a071b02d5050203040d0011071009060410b034450035005002d00403240c1c0060f598400e80c1442d28940300d116451400c1c019052140700b03588041d0b0441040045c182d03201c896015a540252003d01000002d00145076541c840300303802502c001071030310100d0001d241c15048002103e00400f000360401c226400011180c020a034841d4030384a90004500e481c814028a41d9907d004000c0e01580c003910641d29400e854102410380b9100440d50348000408011240e03204850a91029044400802c21868820350300c6107003080030445845017440000b01540c0000131035099840300c0325040910b02482c3d06200180002601c05410703c030351114074421200c0c5000480d0300c2440c0c9000046103000786409040d00b02c4d200a49807920303811103a111000b00c0909a1500801ca81e031140036003058012044000703040041c290444421016a0100020741d030030150050815170b084404816400c = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 473313938 1250 473312688 473312711
    0x5010b090c033903010803070c0f12020607020a030519060608010b0f1207050d030c0c05010c020319050111040308030f090f1b0a03150509011109030c0405090f1e01 72
    0x5002c00c95040e0340304542003054424103020190f0341c0d211100ca04100300301c0c2103070b4104030219a030402d0f001516aa403021034002d0910a4641503000140aa20342c01c40c0c0700303030030801006c404a45100d4064002d04001036020300310f4a82c01c600300000e503000000d0f24102e442080c2c1c50a005e07600c4030002d030360081c01e000000c54400c2d818840c1d840c85c07090041080303454040e004184a5000b10f014501f440602030000700148580301c0c400015569403007a03035a10141150b903d061812818184c12042c100800d000407080181c60008005c01e0041c2a803650300352000d6075141107805420741d504003400100000c9000010040000003440c01110189440c0c1d552b986d074500015907c102e4828040d070207601406008500121800c0301c081d190f50080e1482031a2612500c50410f4100c00403034004019a0b03607020407441d03900a03c20510701580701441e4038034040c034a100080c0c1d6145062000380c0b00d56560740101f19505420080d0040200061042e0b80b07103184002580340b8400010200c0c5146542030000078180c = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 473315188 1250 473313938 473313961
    0xd03020d030b0613030b09100c0f030c09181d0715030f090206040e0a0b040c051207092d090c08010314061015050705010e030c0d090f0504021c060305010b09 69
    0x740c0f81400c6582c0d10070f451131758039829501040985400407030b00071a06080d0440c80349000d00100900251580409900c085000070708403040380b42010208500d503802401940503140342600003969003503010038000403d200c402d40030144581910000e105111000803000c1b42181c049080b14441d850410400c4540194042031350101c400095200a003007000703002909541e60300b10b400c00612280001c0402c4088041400c46010791110030202e03401254200c0441a840300b43ca500120380d18051150074a09040107120701059802c102503410030480180200855603204c0005000c2002c0070701c10340c40012006050b8820a000075030740d01400d1201c90004141c0011050b014024200e0460f4140d4a040702d908450000d6024450820204120080104100340100c01101c60701d040910f5440d1609018945424804c941d000203014804008124103810300541d4012a001554050785c0c41d4107146000c58007425010718140840d00d4400b000c000d02034158024091100280d03940a02c0c0d4854601c602d0 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 473316438 1250 473315188 473315197
    0x6091409011203091a0702040c030b03061513050a1409030a0813020f030a0506010e0a09020f040504050109151506080c0901030b061b0c0306060a0305070e0606090d03020d030b06 78
    0x30340046480004108941c1180882070b4514068580300d039445071a000b08450890a44e00c85004845001c640c2806500e80351040c208114841e0030f00300021100d0a003c80e0301c408000700305480e4070024500b044035580702e0302c50810b1081100c030400c01181c6802c1c1c580740b0003481081340380c0c01c09584080010300043c80006c2245c3d40035000e9291440c0d41e984031000c19581181d036080480e00808038408000b507a44040015045040c45400030702000c1d03042150035107000700001d10381d0000508068500c1c01503200c81c07075a0f214400d1b050310085550342c0c841c1041400340101d1440185110705050100d6203184040e4051100a044000c18400c050f9445600b00d078003503410fa4000b40f220500b00014419503010f0b41c41000c0c00c2001070310b0303142050000c001d01485d80c4101240807500f070300f10b0b0503000114903040c000c007944100c040360035404160960310744568500c91030003004034402070680464030300d5847c2c60981d038032442e000740b50750b0480000e03290081d11a17500881190109003410588642e501c0c000301600c = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 473317688 1250 473316438 473316479
    0x50103170906041712072307060c0308040c050607030c0510060b030a1508060903091c0c1806030503210a0e0606060a0302090303040f0512010203041509051005010f0609 74
    0x103040509013440c1004044092483e1482841011403d0700d4209500c0c0180c06103600500c00003201c400b034442c02c402c1003060f029035943c2541001c0c00900402e5080701e80001540e1b05850728034015038861808400b100002e400c46680042d011030b03032000701640810b490f400e6500c0389082c5d0f4071301e1805001040a6800310f00035044010b20500014503156442d920204444201e03102001216950703451a6040074030030303501c11402c0d070400501e0141d1421709034503a00d03c5207500c0c00c8540c5d00c1903d80e150300c0c0180e00c1ca40100728000380c50300e00303091100b5004d03003041d40995007180540c4d80d14034080d0700302005003c040c149680354410107000146800114414007075140040c90240c0140da40340350800c8035941c0008001c0050680c248440c001e1600c0c00c2004d8409015507401c0e00c25110700302420031229018980720102c40343c2c0108200000140d034507800881c2d9141310381002c47e4408903841c0103414810000d00c114000b514003400000d120304072100b01021246251509401142c07103602d10a8072840c0d603c1c01 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 473318938 1250 473317688 473317699
    0x1d010e06040221120a02010b0a031103070e060619020a08040b070c0806070c030e1801080705030c06180d150f0501050a0609032402071e050d090510080702070b04090501031709 77
    0x3289070130544400108090182c070b200000342d00f51100b002500c40300480e00140c800010030095546142410424800540701c0c1d094000c14034901000020094407460f1020b030001d80441080070820750003000580b02c100d5100310b0b802e03121615071842002542002030240c40c510040380d0001601e00340480c1071401b500040c1d4401c1040007041e10705484a840c010a001d401101d008070700d003050030380a04054040d080b52005070110303034a40010113142008178600700e480344d4810018039190115400f40f008403031109030350300424041c81d4200070001c0c015404c400d036100c0c0e0402005240c8107209601c1301d4160b440031034480d100c0c583c60f01000c0750802e0b4640001040c1508480d2081c0c1808c51203a8001b03400201140c025141105030341d00c541c0070141100c8503160002c0c40c40b031000704001082c864080c248005107414111585401c0001e14074040703e0307044405004110303020895040c4203021050240036903121603944d81c0e82d42e081240c02404c003480199000c80610b690042c00707a500c4401c0f47d4000701d00615 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 473320188 1250 473318938 473318953
    0xb040b010e0712091b06050c12210c25020321220314160b120f2509080f01090c0501051b07030807030e0d020a06031d010e06040221 58
    0x31850700034884c0400944002d0130400000c0e04401642e030401c000740c01c080d40c0f0f4548540300b00799950f190142c26091514035113014003505003000d030101e9801c10083e40c0350346441200d03160425840114401c41036640510441d1441c04c5005000d0365007041c2e0014403c0d000c9811901951080025036001c641140c01500b408001e81c45401340300c551041701c2c8080d207060b41c240d5a9500e03a603141861308219540380c20b42d0001c1000e2001c1c2032200c50900b0080c0050307030301c03186008202e4403485035444004040c0c1032400300c44000301c0c40640003010b403a20a0307d02c4480c80700b83c0100b00380d005003000c9c605103d1260310f4030440341032909090b010f010b640c800591040324208000d080c54010360300c03078100040d441e1400551210810324218104010b0000710f0140300c1e10755840c000e5050003001d407641200602c0c01500f0319200940142c64005240c02200d10a150000d101d00c440c804800380280d000030843e84a40c2042d00e280408400440c1d088d001c0c52003100c903200c2004100c0003042805005000b90060307074110340b6 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 473321438 1250 473320188 473320217
    0x21e010206060111010b1008100e090a02152715090d231516020a0302071404150b04050f0126040c151d0301060317070804120b040b010e07 61
    0x155844c58110000001060000004002c02d088101710b5003007100013a2400c0a00000c071501407801000752089516074000340c500700003840d0340ca0200c040002d010308600400d030805203a82c401a5900b8629060440045041a10110791103014011016104000b8500c0c0010099441012224207240280c602c890300103840d102c108442c40c00c090501e544060400d25455000024080311440c4100c0308070110007820458075107103011125014844c05e40d031207028081d0100340c00041030341c200c0d140d203005000a0f10704240810050000c04842020300400c556020442104410242c0280c0f00144e6421100001960045802206903c0c031080d00302100f14007520790f049a80902a80540a188441c07122551400d000c112001c00859407400a4000e036000542480044020034602c4000c500921a05003035403104e0300e0840302c03a00c00841566000882504100e6040141c41c02008511424040c3c140d00d4240300c65a10011101124080c52440c004540514400e520a00130480c0b41d0f1080800c1030f92a = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 473322688 1250 473321438 473321447
    0x14060309010209090907030c1d040b19060b03091005010308040612090804060806090c03070f0305060a090c02060a0e061905090a14030c0714150d02070501050f04021e0102060601 78
    0xc0d00c00100c9540800c0580c005403284150706004000510080c40c801349141800d5034000c071a6040040303000380500f0b100b80198400d110396034101d42c224104126a4031000c00e2143c0c03949186840c2c040c0c02c0c0c2400000180700c2c44003405903100351031040036030b40303020500014002214800d0100500f80c3d002844148410362152280e23800b45581c1da140094001940c0d164003035550081e5100000003101d220400c001802d14600702da4011440c00413113415403c0c038203405418034181161510406603554002152a40e82000410060100b52400c2200740c1180d14005d4851001712a402111030502090090030440010301c14131030301c1106154401000010398280c094040944201e2852140d0f031050004280b101c0182021b141201c070056030f90384006120141800d205920901114080e409015a152145140501a010100c66856855542c002010002e01030040c01424a40c600303001c020b040c3c540003a026000318002c440c3c508282a07003002004003c0b06d09500346005800c02008030310b155004 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 473323938 1250 473322688 473322691
    0x80708063702160f03110c010516031e02030a08010b04121e05010c05180103020405030a08030916081b030f07060e06090306090a060c110d120605060307090602011104140603 76
    0x480700050714068040190030f980340c08400c410745135038003a0a4801c0405400405004030300058030007404107180c00720006041c500076840700440315400421400d00701881030f1031101d09242d218850010048440400035503035080105031074082030030000082101c40303110b02034030100e400c4070514030b0062aa07580d91300b400406902000c40960790ac2c0c0354501c0007032030a001e180311140d61580c41e01d8491032074026482d142004441d15505040c41004240103944000c52200d48150b081151142d894980c1c1404914000002c1400e69034100c402d03002080340007010824101c0c0082c0d003022015900c0c0c00070101031b00c1c1d10500415001c240d0048000700400c0b0700880311116504070041001d401e0020460201c0d0404500310758104068000105103010044548181c000800c56882c00040214901100320b599901454610f800d21410240d2201d007000e56400c07a1000d0030b4050822912810300b07207405003039038005004507805542040200e001d48071052081c0c41c00c87e69101641040300c102901402400d610 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 473325188 1250 473323938 473324041
    0xa0b01170a170d0e0a15140411010e06040305060f0f01150305070504050a060503100905040807031d040903111c05090d02120a0b0a0608030906030613060302090108070806 75
    0x3010f01024041980074030540d002c0c603030500d000d00080402454030b04681c040320021181442e203003440c83c400e092800940603611990108a00b0412011a40140c0b0362000c40903440f80d1048000401004100700800d04130300400c207100c104400c64803409000180c0c00c07001d000d81c01a050803905040422407003a04081e800110724140f0915003504c0f81d011507c2045550403100109400006000c900e5041400c854020301050004002c64105665861407500c615000071303082048000503d2004c40240000c1060001c1c0103104028151136894040e01a0f81441461103d5006011a400a0950140721001a4001e6683d860325000b036090400601340e00c084004d0307030414281064402c2d011010008101c0013801851006030600c1c0184444041d50700d6504100500c0e0010320001006844041c1500e1300454211035003c0b0081807558007500421880d4006540300509a00028170010085602c40039660001c060394070b1991070f0300117902611085a1314070050701480c000c0f5251003a022005250321b0782d = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 473326438 1250 473325188 473325233
    0xa11040903093c060e010f14120609070c12050a020a05010c200c0a030209041e060f0e06040c03030507051f0b0f1905060310050d050a0b01170a 63
    0x81d02c0f9500c0c1d18514800d4032040c200c40c541d0384500c0c912288440803640c42c4840050440201c1030030305030010042c9281c0a0018180200c42948880c2d0714000d401c45d426010195803a84c0d101c1d072a1107441380000341c0c01d455140c0a9221400419907041c0300d104070303c1c001c0781c00460a01c801000c0307000885047c0c3c002c81908045014901c84a800a0400e0145031070600300b6030303610211103600000c100d103980a8181035268903481207001207000d0700e03550005d000301c2e40c040b01c0c80201c0340d40d41d0400c40790344080c0b10300003803032003522144103800c1000c1c0d83d01000e0254000710302000078021241c3c00503a180810b590250a8040e46c07001000064400c0d40204500c41c1318505481d0a203a01c5001d144181c1d4070007a04003d20740c1c0b550805181801c0815110598030b208072100c0780104030a50018a004001e40284c0740194030000001c0e48819450340c80d04020300d00504180c2100320340d07003130a9495031740d02c003401ca030b110a00800018130300500b22401142d00864030050489044c1ba0381c0c03000f5849460392400d54846 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 473327688 1250 473326438 473326457
    0xc060d02090405090606090c0403030f080a09080c0703031b0c1208130612140708040f2105030a0501091e0906060314030a0206011a0a031a060415030501080a11040903 73
    0x586450103000c0c0148136141c0248800d04040302005280790005000094000b4180301c1040420740c0310030206911521400c03c0d0305d01d42c84011a1201a00c09400c0240401e100060284c01c04940016050304983c000d94a02000d226056030100300f0341021040a09110f007806014800d0108050240c4e031094442c0841c0c61500e40b50000502040400c0d60000000c580a01e0810081c000c5ca4010110190719042c00e03403e140c5000040980b2003600500081c11034020f4041d1241080702410750174000382c2074002c2c1516500640840105030b03504c2145c0c014042c5051800004081525028810804408040401d0803c0c24401864010b10202000380c0c0c3d110340b00e10700000030030350395000340060191a8001d541c2d00d00b50080d01034a807200607442040101c0c0301d0f40d64611444110b0042c0c07200c0c05a14580410300310400c11844d01c00110681c1d10580c05400000e00240c210180ac40d611000400c0380c4080c04182e036a1803480e900c07243d0341103010b40a242ca03c10406280d2401c0e0b4080c0720418441d05158221 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 473328938 1250 473327688 473327707
    0x160c1a31090513021908010b0301062301020f070b0c0708060c0f030c040e07050d0506150406140d060f050108011202011b02010c060518011107020303070b19020c0703030f0507050c060d02 82
    0xb02c10b12000002d0117000007441407044100070300442401910030340003070000038908a000c0200382044000750940c5000010818101e0384240030a8400800031011201c0003501c400340075080d41c0c4a14003000301485181d030001032940300402c0c19803198a40c042c1c182c1c141030300324002103e85d070b00c018a42c5000c0e000030840821a140c0403102c8074011340081e6181070310383c1d0358040e02c402121310280840b0b1040081c034403141c00250a002c11201620102d180c026400312550900c4806800741c50000920a800c1c50004a640320b80790340c2740421207400b40e0b2101c0d120799845c5481010000f440d8001382c0090004406000791034045040a15040c0c4185490310560920b03491707442c121201a100b83d0010352051414003190304003401086041c1280d08419481d143c0c040d4002607503882444001000c400040002400c1c8280c10241c000441d0f07110601075580c0c0e112101c40301d48860b5240812004544544120b081a41c0b040c005e4420171540078004184031f4001d2030412103c2c0e040496045230044d0200a1042c1 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 473330188 1250 473328938 473328949
    0x61608041b0305060f010503030304150f02070f0b0915070207060e01090902030415050115020613060b0a06090603060b0405010f0e15120402030606060c03160c1a3109051302 76
    0x2c41c00380002c0c048030700700305800700f00448069200c14401d61050040c0404989940c0d09084030a43c41d80e00000c40100000c0074002a010350400030b803045d6040c00480013030140e070880b02072040e00e00c10203880310803030914042e42000c41c1c00da403141d005a20040061026030b01409c44020f0b01401410030411940e5500d00481c241c0c2d0044074222600c070f03000010815078940074003500e405041e2000c1e0200001c810031500035915440104002c00036036100c400342007481450b0380b2000c2501c00240415100780d03259007010f030a404561181000203441d01030300089244540040c4c4080d180140c1d100070305240c2c00306088422900c4030500503400702c101c0038014a280752080045c10020f01c1d940750080c0c64a4140105410400c0040a041c014281003010150102000c4120b81c441c010103000e00c448084141060704100116800020404415807800c51103411102e0160024040302c58150988200800ca0384420041505d000440b40c20040390600c20251150000d81d80031201d40d03800c0b19113503c903400183e03 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 473331438 1250 473330188 473330243
    0x703090e0718050123180306040f1103010b0d0b070212040f1410051603050f1303061505060a030e1002160302070f03050a0303050604020909070f020c0306160804 71
    0x5000c900906008800c080000c1c010308003c0c542420900c43c4441541c141e040031652104210ba101c203030000b110351842d540a04451800d11001d0116000703443c1500e03001c0603140119800b5034035102c10501c1140b15240500400403222005803030b010088900340c1e0390a030305140240c043c01c20b501030f113003075000c003041007401038002080c08410810703c042c40c3c40c0c02c1103a12141004c000d030003000d079540004e07441600881181d405605a880c05d02604003207043c101e07298041c60050403001d100002c0e0461a64902c03121480c15a03009501c03c2098803680342050005207564456503400c1a0300348190f42c8000c2c040c0c1c0c4020500304590080c2d1300a071000205a400f02d9100d5910b0315850818541e0000a042c0c0c1003150130003400d660b1902944403070461321001d50703500481c02c00504058072000019240d46864054945024005e05841c90608114401500e20040722104800521480c404403403a0701c0c5c006601800f0340307114608100f25950180084401d408000d0055400702a010b101c1c1a9011151030241d = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 473332688 1250 473331438 473331451
    0x12030e061204032102040b040b0c0a080a090906170a080c0f0703080a0f080702071202010e1305010504180b060f180a020901030c030e1f0e010f140603070e010b0703090e 74
    0x400c4490781e6180113907580018403032031840c491040c4424072441c2180300844042c0c40005002644850b000c0c48024605807203103900900a00000c80c804c092190002814030a0b5030080317109100485c0c544e103800701081007040181c0f003d030b80f0944411003c149200010881d581e0f02405480c0c6480641c5d0101d45062001d910855003101c001a8008002d944038030282802180e80c60150349078103209030029a0386515009080d856940140c4d03100c00c44e80103a01d400f00c89140a40380146800b00030800000605007407040500450900a246c06100180486123034015440000820b5030b0316514188243e56680041da240c010741c2641d00780e080c001402003043d118040c902400750790b07550000001001d48001c0c030803e84c1894207152100c40c5042e40030480500120300c00145140c0c01d203499013904060078199070407491070351800a50405005aa8102c0c1501120f500c1030420b1946845081c159903147d030340b107900e419010385030043c4010030300c00008281090013454070078046621055075801504050f1401c = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 473333938 1250 473332688 473332697
    0x150919031d01090803040303050c010213030303140903090105072d150e0c0604290c01090201030b0604120807050f07060c03080603010c0912020102010e0f0c090a0612030e06120403 79
    0x20a031040c065004640454030080c030f00300000e2440c2001d1507640b4015808014280306022448840c3c00500354151090b0b00c0e5556502e4456582d02c0c24081c00800c0b6900481d070480305008006004400000101c0d0702001041c0c5d502c40c81c040c4c140c0c6030303110300a0806801c0701500070360b9040d104003540503001d075500320b5025a5859422002e06a0201e045441101505a20ba00b1412441744141d036040c095078101e482424520300c1c2000070074120300090030b000010b40c0d801d21002c50b848402290551011020601c00c0c1c80401c154003980080080340d01640c4030300d6411010307203003030800059000406800101c1c0324804841040000b040704c1070410441d90040390016200c203404500b4107510204407908150180c0080020b0303210040c0040559000c0c1c080c0141c000a1140e401d030859100754410b4402c1d045d02c406940d031f074184110016441e4900c0c010600e10aa1075840443e4081c81c0900ca036400f00d4040041c940c03405560f03550705850140c4c044c10807691001060081c91010100b003042e0300e106074400d170785 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 473335188 1250 473333938 473333957
    0x6090605090a03300804034401090b03010905030a030e120403080909070302030405150c0d050c0a09051e0f0a17010c020609160e0a090512031608040515091903 70
    0x60500134040405844108403501084c03002007a00030100d03010540780c10741580c10030140d908c039600d0000d05040003135005881d449840c6660058030f01c1e000d0b05071084480c09010112001c800c050981341c444ca03001c0e1140d0020040f100115010354004c41610b55042c0568151650701c207d00440758010368001e035850000002c100c80540f8103110216404035030780c202181542841c4d25615601c480e400d4080190103001d00104140501060548840300700c1800c0070302091514401c4240c25412000c058000300703078080b8000c149460507400003d0f404210348100b44030202031204128148001340703041c1c6e0f0400603200c0702003500301c801028204029071106c0003256803c24624000d24101e0024200402500304440d400c8581080b0701c2c040b41141d42c200001000d645804001000401090070014000d01c10043c2414424101101552080c0200286c442d01d00c15042819215114201c90040ca2500403201c2d140c0c0c507400a071401a04500b1038021a00c41044004903c0000c2c030a80e24150040340ba07000 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 473336438 1250 473335188 473335253
    0x150603070c02010e0a1a0703142704020a0503040f030905030a05030711010c151512080909070504080a141207120206011208030f1036020a0c0f0f06091a1006090605090a03 75
    0xac411220300c1c403003614218940206100000c06900005e04001c10750040880250180342c4a500c4040c0a800000c00b514107042079444e205560350310824003101c1c0a0051380b4080c1c0d141d03004101c881040c540002241014942664446000705001816403a40d0200c0c050045501d5101d0040300b0311140c4142c0390650399070804d100f01f000c0880b000701081c017003000404c42444074600101c1c61010782a8019002d180b0b409035080441d04010f010b054521083c1c00c00318144040c40980100e2a44060054085e034616907200d48500e102100c0c0c580303018242500070804282c103076207a01940c95000c19200c0c020400d103512440d801e5a50303170400d004265034100c0142e8038502c203000315040d8005004288401c614100d403643c00601920b442e64400350001940c91200c0d803c0c07102c1c0902070300c5041d078868030801c42c101c400d00c5c1c440000815403100042804048000489002c207112294080d2442510741000ca1850101f0855590b80f08080580c1c000c9c41d0000004005082d2000350142e007003e00241800d80c03200c0c1c1d07 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 473337688 1250 473336438 473336497
    0x209040c03080f0322020303220b0c0c0a090b030d260906090123010509040812101d071706150f04060f0519030203150603070c02010e0a1a070314 64
    0x30f409000b00305c5005d10b680e40160f40000858207510340303400100c20540c8140e030703205000859650000720584400a000725448902003980911104110382c00c2203015101c0c9249800c07640b080b804c0f00e0f0103901040f07040c4000c501541d82204503800380c20818483c46500d421089601c1d000360307000341450303019070300340010190207015010344004810425121941a4407a15000c1715061185a001d080381c0c1e00800c0c01d0100c51003c582072070b550646500c0060503c1800c0d9000ca902910a00c1e041d51440340038900706003600e41c80d480c010000e5035508040200680e00410001c54090a0940d020482400103e1481c0340320019246c2d942800200136211480c4c01c01c0079120300300c803c20b21010040208030348003d4948040f244c01c102901482e0050b2039a030b0300c103174641100c1e8421485d01c1e4054004010004003d5104000410309072007a078a07013280701180c50901581200e240110821403246903008190380c480b04014103c40d0780030389446200c0c1040c1040084a07640022281240d06034400c0001020303800070f = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 473338938 1250 473337688 473337721
    0x906080c060f030702161d0c0408061501031b03060503100c1e031104260f0a03050d090b10031407050112180c300f0209040c03080f03 59
    0x41a010301100300605000601e10300c81c19941901604010002c80c800510030045030040f000301604040f0041d40310f00a18034003407041c0c1204100c15059000059100032200c0548040f02c1c0320078014459500d8010380c1c0b0040400524100b8100340c0d03140150b4103a031ba60801c48505207042d644000036002c0c00c00081c10b0410154038488100c0600340310403036a50541c01403003000c3e030088080250140011619044001c0c102107d0442c0038801c2c0880d002c101c40c64507071406003c18900c0c18166002c10400380340182c484541d010300010507000b25010b2408680600c000701001200c3d4500002e074920a81e4548000c038000743c80725040b0100004051003003180c40b822911002410701d0003019001d180c40002049423803003c090072170352900c7e0540c149080031100c40307917003040340d01c01500e9030a80d4070780d1089801c14220b1407aa811508604202180b40c543e800d0440502c260407900382401442c1c02c0d002e0020215010303004850020507010f000011804020241c91003c14080d0f802da80c074200b0700740300e1250044 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 473340188 1250 473338938 473338949
    0x1324090b2716090510030b0102010f090803010506130801090b01031b1a0c011b05181c080c070308070302060403080106021606110712140106060906080118110d060906 73
    0x24404281c2021000340303076295400024842c0a00c10504180300494640d50190b2144e500403102c1c00c402014150503400c88038100400303034020450390140042080c252034140c84003400b43c1a04000522040c2050741c000e1031698214406654615503c000040c01c48804003410368000300c09000500400449120940020340040c1040e50342c00d00300901d40d8002e42540c020300c0741c800030010344800040401e41100b145081400300002c00300c071401d100a000c5522140d141e00346642d000c1104003440c45c0000500c10705400220740c58104c40c15a544050343d41d8001202a505031003500d10000009071404020800136100742e010380700c2402c20f480c0c064507010060300000207540048980e840c0f202c1c02081701380100d900500e025103040026040881c10403060740c02254913211000d80c0c02081c04402c00c00941c03a200c0d10002008000d41e5400210780300202c40c0a00c0c000180030f02c00400004010310702c6141d83d40341c0d0310713000181c884050316071440d20f0f40b010314140703111502e60030f04010340d6540d071007000c00404 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 473341438 1250 473340188 473340229
    0x304030e011106150d1202070e0c04081504030c05030f0702090f13061a0a0611070b0a0207090c0203160f02090c0c030706021e0406020a1106091324090b 67
    0x18120711070b554803000000e04d440950343c26030898440507910304002070b1080e5000f5000e100c0020104800944400302409010484680c0e200800c1030b040003002210100c2d000300010b4034820740c42c04152103401d13034041d00982c204031610081ca00841d01c14030003410032103c045c02281c0d58820034410b00c00041c0004010f1601403011800f00050440740103000e20f80c155001c80300040201c0ca00d5500c1023150b0b10011403503001082c400b4041035042e0002860481180e102088030b2205a0f58450340849204d114090401070300304102c2040001c11070340109444150b24010b4904040d00b0049408240c0710070002600e046048818000030350821204003900811101c8000d46032100920400d55284118030700100100c0d0300250ba01c0a00780e01c10310203207042d503e0340304180d82d95644038070003561070310380405c19941d07072284d0160505140b5025086450004000d090207007020010b1640710f0003080781001444104100d411804400b42c032038072408010341510440062401c0f03140051000c1d0a80540034a441d55 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 473342688 1250 473341438 473341457
    0x1606030e0f070807150512070302072307061e200a061a0f040501230d0c03051c020606030d081f080f010e150402040b010909140a0506191401230304030e01 68
    0xb8407031f0a4025404401c0d03081c00761303560300d5525021166403103031a26598070343d811101050180901041c40b80c01c0b90190f03510018041c16186c505807840794040d0416010038400d0b0065031030b51030b08114031006003600300150344c2400200d0320f07583c064400d141e4a10041101c1400501e000c2c3c40d00c0b10902581c604203560400a960516102c40303030700008100254581d408413445546542e030f80d40c00c4e502e46d856200c0c0403180076980d24a041640ca03001e0b4032024507055040352079101800d10006169220b0480240284039000f0700d900c090b50a4080076240001c14051001c031050700700d01d43e4042c44001d082000040001c400741b841b8090848218525241d1560481000a690003001100b0b807904282c0403100005c240d60002e0040e9120f0305268042c0c48020304080010924004001c10a071190510b0003041c8002d9403104d04102e505890601041c120a0040c07806000b4002d14200742c5041003010b04210750407501401809541925400041c03030590300000c1003104159110721140050761081c01c00c06200c = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 473343938 1250 473342688 473342707
    0xa0303321006020d08150613030501060e091605010c020604030501140403090b0f0904020c0a0c060c02031204030308040615120804090c030912030b0402121f06021606030e0f0708071505 81
    0x1e80c2c8094020303107030f01c20081c6c1400c92a958510131107117404a0700828501c0503130399103009406040c55115201000388102c0c002541c0b02408104c81030b1402461070505c1d40d81d81043c006442c07010360010140d8216a042c400800058000d00c10348a19510f211050015460240f400a110200030f8002e5403051009000382c080c22074004041d10b5242404850260701d42448008480c40c0040514000e4010100c01400041e05038012015040e01402602030780e6031140a00c1e0030302c400c2d01c101e1100800040032213000402082c1c06904c10055083c0b1a004040d2880e514941410f40b80300b079220030ba4600100040421003081148504408200395050600c203000054840195264812400001740f603100e951942690341c8550450740500e2410340021143d0030501194980003003043e1000590b40c2004030082020390002550034103011408030300c20700c11402c119046024081390a962484c41c8a1500f05401c01308090060034060b210101c0102403040ca0003034901c078800341c0941001c040c443c081001090b07 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 473345188 1250 473343938 473343947
    0xc09060207031113050c03010f05040902091f1a0a080609040c0302061e0a05041d22051218030613020604030809061903020406030c0e030a0303321006020d 68
    0x460360055a0003448844400104a10085140040a131203140c0000c001d04415600f0143d41600c000340a00c0d0006519131040c4421120190300280d40808400000f601054045c004559045840a14400c00716981d110807085840c00003420301e02007001003181c2d03000540c000310060b44040c04988051681c14552108105640180000b9002d950005050107201e00e941481701d88840080c281079560701001813004dc203075005801036405800104022008400640b02d0782d500500c0b40504041542e460b01d861149054070282040f1058026000c101c04041280790280440540700ca41248004500c80e00705030510500415040e10071140410300b5000d601c44e0001d031002e8a84c0300700003036503600c0040d00181c414041c1c0f541030481d40d81d03401300340041c0c198123801400031240075880502002581320f40039100e1000c0880e8842c0c00d60b10055940e03020900c07076004550824000c041c0030300008201d242c01c540d12022055a443d000c19250184800156a00c4050005108070b05c090411203464030b400a0 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 473346438 1250 473345188 473345203
    0x702131409070b192730140a1a06101d0f0109030206030a0506040e060103030c0b130807030f08090a0519060b0a030506090d0e0928091b06020102040b0304030822150c090602 76
    0x14100b104a00e0113245c403c0c42049070941d61390308270800700300340784409107601d1b04107408840840c001c401c0c01c440b01c05805d0290404c0248010185c09811003114032034140701241c5540084241040701c0010004056103410700210b02031100300328003013000e09d0204d041c0015039610b40e002461690001d001003020a0780482d0442170540d000300040c0b001c4d1a8488242e6459081580c058021138001440400301034111001c055103414603100c6050a070785c2c1088482e1603110360780c0d001d00646c10006e0708080d03031450741c0d5041c03071a180b14003000142070720804049000d03100550001c864980c4280d080c050450400c0040309251400d9180c402900940b00010841c030302c5000d48401480d170440700780388151814100014151411030340b8100300088850402c6070343c500e488a141d42d01a0340c1c644001c03c03024418021242600c1100500901d16103503585d048452000c005d1081801300d561002041c5c480301c03400c030006440c0d80a0a00e02109469503c1c440c4201c0701e11a91000038410b11071401c01c9131700e8021a000 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 473347688 1250 473346438 473346443
    0x1020f1207061b0e010201060608070903080d0212093909090c1203070303180507030b190c0909050f0609060409080702131409070b192730 61
    0x684821040ca4424043e1011030302c1d4544072204004558200e981c4544a81c24070002640207000d0280d69842c281c45114095403900d0006503412000d00101d07480034010a01016101e400610308404440102e802a900703880215103034000a00050348803e0013020004504241c400ea215401c50b043c0003100c8615050800703d000b002d0840c0020300070482407128202001c00a01142080701d9100309030394581d131006104401081c6421007000309800b80102d070340c400382d41c407900418800c1d040d51150072060200510f90400d5803043c803c010f600000c68050301210001c0c58840e06805403c1101150036500003c0c40320301c040c03c42e00100720141e5142c100c0c25400000680c1c0c0001c003284541044906889a484003a4021001e0701c0c69804140055008443c00140c1c1e010b600d1250700d68840c003c0e2511051320503c8504001400340030000010403804c07405410990030f00b203581d084244400141003604845a840f07540140c1001c1107907900c100480c100c5074002440c010040d03045048603a10404085401 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 473348938 1250 473347688 473347723
    0x7020d020d08010806190b0a0b0d0f050609040318080d0f030c08060a060f020703020603040f030206010b161716060e0f0309090a020304080f030108072120010201020f1204020a0501020f 81
    0x440f86c005580019030a080113415601859194110611613601800e00481c10b5441c218048103041241e00c180d40c028000200401801d4903151400c6030b4000d011685d1140c40400050005403902c4100491300400d81282c0300d2115a0350705280190491305c940c9803100620080804000b120303620711555401303070380030342c10300311143c000c038150480c03a01040750002900100300005000034006840080b207101c1d4440d50840304940e0321410403103e03901a510028110ba90800c980c42c000401c8400598581e803c000c26581c14230720802d20b54003840ca10080240c81c5c1c0c60b03441c00280404d950a101d0b0000050408c0000d503d011128408100d624000520f111255640480440d040101410883e03800c0005140081d8903961550f0206d61074404a11030841030381402d240510004816507030607441c8070b411800220072203960003803000d00000e80b00d0a89046540c00c005c184400d02031080941050340c2000780030380d884d1501e441407004a4140740c1060341554860a50b2020701040000c0f2854071001c0941c0 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 473350188 1250 473348938 473348971
    0x40b070908030f070b060f010525020616020906120709051b070c0801140f0c07050a080a020f0709141906090c0c031220160b07020d020d08010806 64
    0x4003110060141c0d0001c20940c0000114000840072031005011114082c00d0060156103079001081810641c04103c02c2c00b1490502058400303101c0b0a54010307203141020f02103030318003d0660000d0002d40c400300781c02c501e00c507420b034080003503041141c016640000d06a441c407140821001340d09030b446c4801e00c0340d028820b807203c00040c040b030300202d41c02c0541c240010007251030700c643e0310304440c54005a000b480499803038110044001780c03141d04014000c103c01400d00000d501c403689040402d03404080e041e901380c07041110607000074080c0002054411107542c040d00074010980e40c0a82000b0441d0710001c41c940c2030102a0b02c1307040d012195690400d410040c100c150344404034000e0054100c0750700040a05142ca2401d010190700008224102e612a40c1c80c541240340c200d550908070744d088069407103800301c3c910713100380041010740040011110300030480c1104174256071a640100000c580580040c0c202d46141c8034003540400140221030000e080a00325981012001035a43c2802040dc00c150840382d034 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 473351438 1250 473350188 473350201
    0xf1b0302010e060705030420010905040203060f0a180605010e131e05040305091c15051803040315151505030705040806090c01020d0f0e0d020402090604090b0112060608040b 76
    0x501559a0045102c01e603001c43c40d015102030b1442e04225000d45550a0351030b40c0040c2900c903902282010b00050f1074000c0000d050005000094100500c8241c00020030300f49450190341e42c91664006112903020004006060900300090303030130580c001418019182c0f0340c486d0070350f6680c0701650070020800c000210f1096481056203c00321f9a42c1c1200f0007032401c2c0901041c0341e801002081078860a5851066030b4407200019001084201000780408280440860b104141034000341d41026580010341d1a60046c0f004c020b055901541c01142c0c042080c135071a50940859000c2c06188a01da52085405241b411030b81404282d802d0f040c2100304000000082d241a008800740e8000e010500304894152a01003152940d40d0b05444105016104e000d9450b0402486010a00f456481c0c0d9907511040052503010300c501d42400303582c101c0c0c1c8103809103c10340c10341d101c550240005250a1101241c07003496040058204807800101000c003d0401d0002e11069811074000d6802c144e10038034445030340e83c800707 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 473352688 1250 473351438 473351441
    0x71e0602070b0403120b0603091b03211c0b030703060c050d1d07090225020a0e10210f150b04150602160807060507050f0a0b160f1b030201 61
    0x141c100801000c03502083c0820b059118a940c43d49286034002040302100200401c51240400c56500601b03500c014203c064009041420080d001400b9088501c41d24803c4c407044a00300b00141c1a0400240105145100c034503c9594103c0c86840d0900c108031610048022a40b124a00d02020345516162440300c8102440b540c00c498800d043c121303040260285100400700c00d143c10720f80d0382c01c0310301c02c5c0c41c4042035080540c42200e000c1c1d50040c00c000c1d410020042c42038205840c0c0c103820f03a070081514400050320140e81410911401e110400c00b02103034200b07248440d5040010b61912001202c030611480042c0803510010120b54020f10040b905a012b8042480a04078441900f030f040f80c10010170542171441450420207640c40b64081c0c9116801c000c542d103050b924140f16010040c0d01c000301c05c000c0329000b0802894241d0066050701c111032840c00c01c06290601030135080f03c03d04a45410098242d1500380c1042c05a0f601785810502d02d1074199005101200958007004008d000c90600b404140c000d = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 473353938 1250 473352688 473352697
    0x111c030f1d07030201142106040e010c0504090c02071e06091203050f0904090c0e0a0c03050f06120f01150510080402091513061706010e01080319050405130c1103071e0602 75
    0x11049402c00c49403500c40e444a040023600c045020307900340043c80b4100760060154042000c0d590751000e0400b4a0586003001810f402d1544900b540100e02c0040340040c41007000d00701c03242441315040c50040c9004802001c1c08400c2d408071a8811b0480c0105001a030302c00e088814000c41400b03000e0700c8950f403200180c000d000b6480024051500000005071120301d90315490300c1442007500802900c4e40004056042d500c040320840d104c0d102d10400a031903460126540340c261003181c0100d402c0c111501e0409821920544c0301d50010080b8a0010401440c004030384846880d07441c40d11020b182410380c082510024050402c0098044d084a01c1c0303c941c481540302d4030a4083c20034140071380c1d0764541c40092040c035115a901a180500030022907454800701403035049503420001103160010b0100078180c0002d400c1d154100f04642000000346070782d101c0c44051a0101105000038000d50303205070280800c6240701c140004ca4000b40804000309020b401c0304003401041080b60707600102d003441c0107170081c0315 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 473355188 1250 473353938 473353957
    0x503130308061c0c0e0a0e0616020a200906100f03110c070f0317030f1b090907020606010207080601060e0d05240405060106081303111c030f1d0703020114 68
    0x200f80800f0700c18030140c16141400c5801080103c400c9817104054075040d5013500c0c0c2d810785150312150206007014010210401c1070600740c410b903498222541d4070280008801c1d10901d11540345603c41000515142d1600754200c00115944031200e035100401502c2c40c841c2d0b0b0481c2044c155558104039801c0e4450007100c075140c01d508240d802c034940712980803d00a1071401709503183c14145410705090310342c610481c2d000751600182d0840b50b64500141c3c1c100c9500e08013650a05c50002c3c004003e0f151541400341c0e000b030419401034032482c60210002440c003401c641c80301d0b081e980200010041c140c0c1084010301c07003903810b44005c4088440760030141c0c0ba05100326001c0011240005864081400f1502894041e0384544280c4010340d07a62036007250300d12415921b50704031900c0040c0391400a401219088060200541aa8803d1407401c540250072a00e800705000807940300d002d000481009813040445a24121003426100f4581c110b030b16940d006107000090620200b042e0031030f14140180c055548601 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 473356438 1250 473355188 473355229
    0x31106060a1202153103020303030c0703090e1603050a0c0f0c020402040b0d0b01090b0901080c0d0e0111030712110331030309060c0302031e0a060506071b06050313030806 75
    0x190300400c2e5000700081d802c2c9102d04210418001710650200e00d00c0c0c000c40390001e00071030543d158042441c885500484084040c81034090b00000c0e0011050740300e80c49084a040b920fa09005008000303000c2d031384010600d258107454200d00403005030f00300c1140300006049103066000540c00c0c5c40414024400c50304819000f801c0802d10207c94032540e00140c00d103540a80c0d035602141d80d0b45251082e03500030440154046031601c4002160070790f4420280490300814100803a0340800139541c14219441d074030842d80011000000c000805400171030441346902d00d070408018454030803020088500016041c3e102003280100c044c000540c1c0e5a60700401251208a4148010980d29015004000362442220300c1e07418441e201e10030b1030003403090741c2c80323480f8900041e000745040590001243c41d00070800b01c0501c6d600d0901051940350100500b85c078030f200e0346400300001c500d0a54550303518007a500c540c04105080080151801400c610040010b43c5403c04069544501c000103504822071000d000245 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 473357688 1250 473356438 473356447
    0x21c1109040e0a1e05070b070807060504110a050f1f09080609060f010608060607020d0201120908070507050d0515072607140a02070b0313020a0b07031106060a120215 73
    0x1000d02040105a21307210b03510031441c4200301c0ca0251400c1c544e0703180180554000306800c000154040c0e00804545116040c01032425109964030403c43e102541d054644405ea2074060007903003000d00710344020b0032048940e070418102c0140091100c0d014030f4540c495808032003c004140e90300803070f986006880380702c05480c81d500d4008601c50750741000b00c80b070407003030a42003000103601c9001d0350600b40a55805051149044007940034001c400c80d04840403410400c25001c00160003a00381320f13514801d4410024642d580201f070400354a00032083e00040e104000b900001c600062002031100204072941e0942401503071090700a4070f0a072444514440b81009008a07080201c00e83d660b590b20909036601d0b40803090780c82485498690144681030b00160307001060501c039a035103400c007441e40a082c0c06031446801c0100c0d400300721070346d04a17070080900c05804111142015042030804990102500003401546400000150b14002c01e1280707510b1040003080e140d06548034520000c1c0c1d46000d8646c4c50750f60703 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 473358938 1250 473357688 473357711
    0x15090306130605160c0b1003210207050301110a08100503060109021908040510020706020d0906020417030307090302060703020a051509010608070506190504180903080703021c110904 80
    0x196041480200e0700709283c00c0c00100800d8800403031115004c07460b5103411502800b9078552165000182107071006001c40c17440000002c140e8464150f000710283d41200100c0c803655030287c0350500d00c0e04124880e90601d02003140d5402050f003034904100103807401e910300b51a06e1142c180c0f00280740c0c111903050b0245c0d20021072a201d80343c00034210240c0c401a0940f26070b0030301104484400040d500102507402c500859266a03845402030551130f0300501006141c4036a40c00d02c2c0045490300101116900d4001c501084110455940b50080c0e03036484024519503c1e00d080010f0010b036150100900c51280070420b4010b05208001c15445c59502030106c03250344141407006183c44600310b40070540c641c04c04c00b0100e4040004155041182c00c05400700e0f080500184201040e101c1020301c1c4030402c80180300024840344c140407024500daa54041c00100d00495003801821020000d0003c414140100642e05041c01d80300c81007800c0d0039081400007400d00035030f000800310f80f203003c04281e841400d04170002c1c030 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 473360188 1250 473358938 473358961
    0x207030f1202030f1501110a0c0504060e010b1603030f1e0b100509060304020301140f0f010b0301060f0c06060b04091b020d020307110d02060c0c03010c1d15090306 72
    0x2400c0329101c6090421091a50005a1008840560b075100c0154003040f41101e01251200301c1707882c1418101841d80000c1016442c021600782d054420000007407040001341894821000039041040d1500019070401e4407501880c407889140d60808400300903074005040c0300341d0142d40d1003c8001401d100743c6051a00f2003040c2c0d012110004170080c540301c004843d51400742d0045200f05000d44441d81084d1115040250319040104140c0e00355490341440b221504044a1843c401c0510041c040e4441c02c00c5100b0b003a00b101c0580080b01040000c00c014845140c014500b5194190189448040c3c0c884d14a001800340507141e20a084001c0d0204000c00d03084400d410003041d0b03841d081c1c40c0384281c2c640c150040303aa801120540d9005a00100015400310b01c00044404110102078000d801c000c095501281d040c0d03120040909858100b0900c44541d0300e02030080400c0d1480c2071909a050b400d028071014208054580454854405849810a60107801050b0780d8141c5004060f100b0790324004c201000f = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 473361438 1250 473360188 473360207
    0x90901031b090e210c0a350c06060103090c1e1e0503010506030d0e21030721080405100c031b11241b09040603050c1503010b0313030909020703 63
    0x440c0700f080c0e4602000b40d0f04c186401d030790500c021040140191791203a00e4a1004000060340c40144a0720601d200e440d1001c82c00d003400a0808aa80f89036403030b20034034401d50801101a1141e41090308094080d400f050b24424140155072481180c00c0c600051071034900358201c074035031040c0340410980c4c1c400e440c4804419a11030465400398020320456407588105078031809040d21311800300380c3d2210320f02c103075040040c004031500d5498241c2043d41400c2d803612500d1600b007088101d4420000045817a4008100000101c0c01d24040c149070b00d07141456076542d600d81c1c0f41a00010103043e6104500082d45120780c1100e05070104000010300d1449000200601c52011408400310038400c0c05100900203c20b5113070060f01815a01140181d61940f00410380c0701e280c4481401024031044c0407a41d41076803144030314001144070f1030003032194000400c18041c1c401001c43c10f001003200d007440104603404801c812254030042c0c1c00b06181d880e00052609031204400c5401c004001e03440410340c94105078025441d41e = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 473362688 1250 473361438 473361463
    0x7121b0f030f11070f0203151003020f0f0907051e13060f02030a0507030503040204060504020d0603020301061a1e19090e060d020102190212010f140606090901031b090e 74
    0x1d00500000042c0c5605803142c5840240c00001d0401032580032502c401070011120784018240c0b400c6400d405410b0b40b055500f03442c00c1c003644504400400c00c601d4095540070b5241d0f41a00c3e031910990740340700082ca5040d8000e00500501c82d000806140c5030102d00c0c0c1c0c282100050750344441e151155261440f404020500660000c648506d0401400e0b82c0000141c0f02101d0a070741d501c901c3d010040d82c04849540000c4c1c0101e8000380c8805001c180d0381c0d10790000e04440360001c01c00184861841c01014291080c2d81c0c8548500300d40c4035211b640412000c402c9994080c5040103c1152b01e140625079410740c400d0200c4281c801c020882c036258100d9010000301c080751a044084181c44e12520104000300c825200001c0c0507030300a1005c909040e540801411031240002c0000c0d500514a01e4400d0a44500210303161a46644002400d2041c50301c202c0143c000e503050700d0450502b94a40c000c075450140c10b0101034003112414036048140920180440040c0100700740038018110800c01c000e60f18a86107190 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 473363938 1250 473362688 473362691
    0x80906040618083d020408030702040501230603180d021c300b0a0602160902030108060402060f071e0b1602030405042309031c0605010807121b0f03 65
    0x1d08510300080c03200c000c02d4031510480000e86500f07840c9688281d841c0d0203501c0c101c3e540702c04404e540f0f00d40c800b0b0001003c800000d50b1343c440341d61040100f25503058100d02085589500e82c25404030014040c2100340f84141c0300309540e42c40341d0824550101100c044070542d88100391408102541c003141008504c0c00240c0060722080c2541816103003a1740c84250f50344400865042c5c0103100c25243d1410214070f500f841c0c0041e45100f8400482d900703a099810440259102d140300007404901ca24625009007586102141554140018940c4881c006071029100b6540416107101400c01d603c100c40504c0d91281c4582c030b10264001c0301d005100e00821095031809240700002c1d400b1065446a100c2404403503018501d8a41000104801400c1c7c5807891168034a04444105280603089126401885044015601c07107101c94003d01e0901c4101c8074030002142401c40c1000140d0b00a1102034100c8224103281c001a0300b200181d400400f80880107800f100d425460f0322503015008000b00c5252640c9960 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 473365188 1250 473363938 473363987
    0xf0e03070f1a01060509040b1c0318050108090304090203040c120b18030307090614070204060b1e040303020304090c050f0a0e01120b01080103110a08031804060e0402060a0c0809060406 81
    0xd04880360b14092148101040c03080201d102c071441c01d5403003000141c034001c1494848005007502d00c12030a501110807004075000160484203250200d2803c0300a00342403030302c0051032509409482d00c0b800b8902c1800c5003107401202040030400548a05009030202c480d000484d41b085040c0319000c3c00041c1c0d50100d04895030000c110499501008aa114110316212545510b181c000c0403200c0e4100710000595101c1c043c880320006a0b0b44c0d016513002080c001c036981d5128124904082c0c500b0820303c50185007220204010000260040141c1d800c507170520f540010711224141003690140725404090009510008100e02c1254004c000c62510700b90a030b036100070728240f400101c41183d0901b140c0c03d02280c0300c03500400005024165080103844090000100291380e00015407a5030000c03041c2c40600d1340d14403505030392030078030f407080703500620908007009081d00707044d00800c0f9103100d8043d22034100403031410004284000b00c000c488038000f001d880541e80382c2d62104002c00441030182c1c61003e074001d880 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 473366438 1250 473365188 473365223
    0x240605120d030c030501060512071b030302120606030108120c0c10050c25091d031315050f030106081b030703090c0807080c2101050f010303030c090609090f0e03070f 73
    0x10481b8141c5405850396840c09401c223401c01c281003401000042000049208204071046c02c480c00418070b0f209486c0540c4a0f42000c40342180b5600007000640210818801045620400164203d01c2c0413803c0074107035030305180310216003800540803400f0342210710840110408c540c800e000785203c0703c1140070348001156851000d5140ad40001e440307a8100c00d02c2e0000c2c452040681e0080980041040103000c1d48404080d45606540100d64103001554003580108020300d00009950715260681c80d08915100d001012001d5602043c000d5004100d517010001e940841a4440e19289240c1025559101d20b040c10004001e400260021581000309980000700c041e4001810030540d06210064407003112a0024043d442e0806054425410405018109068428400d003401542101c0181286605601300035054480c2020500200030881d1000c011040d0f00983c240180c0c0c2103e003010408284061007217015041c1d1882200190200203004d80411040d0b40c0d017194468400c1041544032260079 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 473367688 1250 473366438 473366441
    0x31c1103042a0f0b090a0f0b0c0d03110301150c0501060905091002041d060607080c210315090a02070b09030405010f080103030507170c030304061406040603240605120d030c03 77
    0x521941420384000789090154000f200090140805c019244840303030b580d11000313000100000c2d0b01070f4550000010b050304015a0500400031401c900b07080034021400001c403d006640720510440f4208013850038415081845042c004020642000007400800e407244400c1c0300601d426111205203104104805d0b24804050003901c0448218800300b44080920010038000000000d0801c1d92040040148000081c88a006000c050501e10000c105400c4041c0d40c0101d03010039089880b103008410f000f00010300381f01c6100705005e20815180201c10b030321100010800303800303185001054400c40f0000c0058070f800000c041c10071510242e0f14454000304010050326414028040034000403420040301006c9000e1a1940790034030100103031340d481d10006601d89800d503001940c00300c415a4655842443e4101c281c642241c00c44e40441e410007132103240d0341e500c04040703100e83c54807641d602c8082c0b03070550890410b901600c014803001d052035004500c000c1e1403035181c260044807100400c3c944081a90b0140c800d = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 473368938 1250 473367688 473367773
    0x1a060a05010914030c0d08030108010b0607120c02190618050d050706050306010c020a0306091b06020a02011d04051e0c090618121e0f06060102031c110304 68
    0x6850b81d5028505010b440c0d25a03c06a4407000d4042c03041c5028801a40ca07421641082e15010306401a103950414500b2030956a68420491092009000580c0072996031b0780f61a14549860a051041030b46d540b020403401c01c0e90404240d2010504840081c529801c0010074200d820302c40d1625006503102d808006902e80c00d40c0010704581d1040328107202e040d020700021600440c050404000e80d034501d600050086049410841e001ca072180280410081110303601201c1c080c2e0201c0820181d820010001e5079402c5270302001e030410100380e400c401c920761280681810742c200a007050103945000814002d100203603600c080e0208070044000b0300305048203c140c48086c2401484140b40010004080000c60346c0414169401a440110140c109400700400880b269050406c2180d512106101034101003c01c01025039941140041029903a0701000300c0380c11a4686108034294035840c05070800418051000c4920a01d000081c0014031603468a02e9482404c04452032683d02d004030f00385402e4040 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 473370188 1250 473368938 473368949
    0xd12030222142b2006040b18040e0d031107050a2406081203060301020d0c030e07080304150311070b0f040c140a090515040218010206010b030403140706020c03071a060a 74
    0x41c6249600000d0046018854243c1a002e042841900380e4400202160700c587d0103043e41400005643c0056803003000f66021120080b5000c0024102000c4a142c94000480c200b40806607a00c0c108136a495507a000d0350305168101d42107a10709000c03450090050110340700c41080d00c411803400081645483d000c1d500a540a14002d001054403800450069410103000d140d0300d5502400f900500c251588107031b801030503840d5004190030900c103114070301f4640c15402001c56500200030a015000c2125040143d000d41480d0004811698070394001d000e00480ca03009010500d00410700203480b1007840d401e80698011030300a2512a51000700410712194034000540005d0326101c20000502d45500080e40148162241d07440070b5801c2c00094201e920900c004c0750020070211036080c0c556410890640074203981c8400720f1950900d618041c24003059100d001e5107d50b00000c0910422150f078040d600806c500d00c0444c1d450341414540503030040f41d1044810010394910001514620300881010115403 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 473371438 1250 473370188 473370259
    0x9010b0405090c090d110a0b0a05030c0d0209090a060501090909240b1c0606090204080a08070c0e1510021f020d091e050c0d1203022214 60
    0x78a0316003400b01d06603005144500c040b40c103110f2940740f81c40303441100d4212440303074440650381051030041000182003030b0002d4084110600c4a00701c40b0b0b40290803203401013107003a0707040d80b02c40000610310041d2145058980d00104908140100111700c0c0e005442a50000d80301c5a22803515070600004a5820541c0030b4592241003030700080400040c41103440400010740c010039110340d048041060355480380714915094080b1034404052050314419900500b0104c6001e5280074a0038840035500d8040110241120200144c04d000300541b1030500c50050946894855581c0b80814175401d0740c4058220f800e000d41032088500d11107604c04259090024894001009030b1811801c04000235000000c54289540e42c03104a2000318008501c903003105000d1038442801e8000e685403490411400c02c20782401181c01c0d41c0d12000048800d18440321a404511b401a180c4100c5002882d82800407910324484d02050000410f400108010310326030420103171000300d4080c10172120300b081c40e03040010449412 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 473372688 1250 473371438 473371447
    0x120f090a02100c020f03060c120903040e1803210403030f05041709030c060409050709091404060207030e0d030e032e02070203030f0309010f0b2e03020d0609091109010b 74
    0x54080d00b00034203460b001404405080074924082442e07c1415550045611400b1a104c0c50b40071101291a9114602030301443c107140c40c02c8020785002601404c8043c141c0085500a18049401c0054550340480420140c040308a2082010721130201070b1402d800013420601c410a11031180c2c090300e401607512202c401c0d000d040c03415003c00540c01c81c0789003a515001c0c0032000c0c20f1603a122005403024084000d800116401c1080d0040d001c40d01c0b6501c100380240c101109801000146800346901c503400004c0036a40e1009031070300b21909040003424940c040d0034003484c0d030207041d0300190141803980c0542c101d40245400001d13444541c0f0081c003a056101e080303488090507d900c0c0707801515595101500b140e06201c24910100d0701a081151005079a03035440d00480800020750251045035503054079001001c000040c068444620f900c001d0a8201e0403490300c408800d0300c00d17811500b040d0b0b401c4804101e4140c0302c884910140002c2d1000390f41000c24000320310050f2500c1034105040319581e140e0300e840e0 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 473373938 1250 473372688 473372719
    0x20615040f020c030409060914040f0602091206090601062309132309100b1f0912080d0605040b0315071403090f010f0209130b0a0902120f090a02 64
    0x1030411030348020280c50b024440340807100c504001500141c00d0f50500403401d81d00340400c400440d840d8061000518550000703000c0840c180340801c1241a8000c80c01513955a0300c2800300d624070801d6422640607109075420040c117008040380d01d0781070350300c00d60310f0041000075940174000c80d521042d0481c00038001080140e41c41d02d040c81000c1c5282204000104101400141d01c1c03030009500f0240d003184411410070000e80d0041800301d0480120001e4041000840042c003040740107880b842440b903800546c10401034054081c500300e400502400c0c00e2820f41e1001c074a030a0201da0071400c42d01c0c0c13040303081003800306052409000d4803c601d440030713004150000c00e1035405400c008001d00b08609002000e03416010b07541c40c500083d03101d50030b181e0080c0820150400220b003161a02d101c0c104200e481806128455903a0f2800007942c90000c04000c1804004000080c0b495862a40815401032000415400d45400b038101a81300f0000200e100c6501d0703842030821611220344100082d8000c085c540301c0d001 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 473375188 1250 473373938 473373941
    0x603070f17120f04060f08010f140d0501020a2c0f010503070e0a09020a0f08280b1810080708101116050f12040305060606031308030114090702061504 66
    0x240d2548048654000da42c00c000d221551104503000482c00e4001800d2242e1030f081440300c440703003145180c9441c2039890302c0801500c0e00700d18000c090303200c0b0550b42070003640e544c0d0703c20504c0c1850f0080300840d03031000c4c07a81001c1e202440500707000300c08102280155210494111a00e500c014002c2c4c04220010340400c0112819440109600140118900c1c03c1c1005c0c0c8801d6013000c0a440001d40040e0307512124500a450381101013084400c1240a0041002241c075a0030701042680352400794400d00801c40361280064040d802c406a00086101c044410703060401c0e0825001d84000c0341007031106602e4240f030544984440c05001469840307441d1440803600c0c07a40c001d18120010003516400c11942181c3ea10702106081800d0f83c0c0ea50010501000e081c0040c8481710381810041d990505d05455030f6244c9403a00ca00030003c904c20310010000507151400b980c45001c2065202c03c41e81e641e0342e1640780c16600c001074003003810b0082c0d0314000000ca1160000480c28000c60324118120702c0a1001e008120 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 473376438 1250 473375188 473375219
    0x120c06120612060114040e06060a03020112021c0209041d0a0201080403030b060c0610150e120c130504030306060f02030306041d010911030105100302130203040c050a06030905060603070f 82
    0x58001d007818034101000e80c0c00340f00e083e0192094403200c88292907405c08000903224032507600c501940260701403200030343e6140800000c403903080c20b2520326410180c030541c00074040e03680c1001914121040b49460b03401594024410000e0480341001f045030000004112401301214410465201031080005980560300b0507511a1191401084070340708180880d5540c2c205000b41c5130660b00505c2480b10301a070081000001c3c012801c2000300e61504a02d004203200c0e80e03826040d005c0c000440e205182500c0510000d0b03900c1364040d01d0200b0500c0c3c0041c008009101c101d400b41c00282c600940482c0072031040e0b5a45d241038025500460560701c8103000c000c01441504142902c203000218880c00301402801109810340c0070787c00101d940d451010a03d400c3d568014101c3c0d0040c40080300034170060740ca901d00120440c50400700140c580e40c4d28940a8a03891207a0803030f6912035500c510002c2c80f5645a000800d45a00c1381040c0e03903054036200c5c2496500e2000b806002c00e20500003200b840000078409410 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 473377688 1250 473376438 473376451
    0x4060207120203030412020c01050d0e010b06030103050313050103110403140c0907090905060a0e0712022101060e040501030b2412011b02070602071422050105120c0612 74
    0x103150604940d01e81c501a0800d007092005600044100302c280001949400d111100701c5c0041c1a10841c03900000b011031044803d034020150341e9000c01c000c484030075407101080400c0541180c2d9a56102d00701541d8a4014210307507220424241404201075109005402010020102c0c160030103081d590f0349400c1d9046400c401c1c00c1807107015038000312541c55800035401a1290b494a201190401d00f002060704d6000307041a0080500030300400601c0c100740ca00c29401602450301c002000c00b1916184060303c0362062910114189403441000b1810f080b220604940203526800c01000f0140e050000340e030000d100107010240c2200001e03400350391031110005100d041d840504061501074000868003006030b0030840d100d82d551142107400840e000341c4040791440500003001810724021000b95070f40450702074901400030140344088117480b004801900c0c00400001e01000c60940d4115500502003486031510a480100124012600c0410007101910340070b04528035060581c2c0ca101069100034001 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 473378938 1250 473377688 473377691
    0xe1621090f0804140402070b0f071b050102030f0108010504021302031f080102030f061507020f0607080c0d081003030203030c1e030106050309010b2d13140108010e031903050406 78
    0x4610004100c00d0207000341c18400c500494965042030f01a800e05101c00c2c504500851041007001c02281d07250040c0c50f444118200b400380355544415085a03401c040d50420300350742003030900701d00402c038064001d14460074001404d04041c0e80d85448041c265481600c01a41002c51170030f0000d4442411740045900100c164124110381790410b103020fa8580c8681d01000d22a540401401035070b0340301ca450260400c00484415401c2404100345070110320841c20000d02c00c4840c0740016009071103d009580c00c00da0003a180035244c82ca45200d15440d240049102030020fa000340001c0c0062007422007500c1640c1e0554029411503a038003000303000642c030103029500b03405050708068401e038000c84000c502800c140da50b050b407241421034659013920a060301d028824580030000c00b01043c0d410b451000420440e501c5804480d0b000004120640703000019039a030141414400c0f1054071242c900141240c2110700200142100d4800c0d0030349078011084480d0507a58120901e05071710b881398004030f8005018260 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 473380188 1250 473378938 473378951
    0x203160510030f0b0a090e150f01140406120b0402090117101a0303130906060504140607110301050a0e1212190204120b0103031701150c0f0c08070e1621 67
    0x680031701c5668060358201c0e0301c9104441c50724801303022100c04214544820741840c00c3c016075890541c0c5050217850b11400c24005505015a02c980100005202d5400340780010219403e1811132114100c4040c0e018062080c00081d1401e1a0703417041e5400c031440e901038403100490405601c05050036244d07c09180f42954601c04440da014001468504521010000510700d0180d4110680d0f009500c0301003071120500080100700c0075620768404001013141c01d40ea84441a14055200004a5468a030158a440100726180a990303003e801e4031040d142c1110041050140709400e00e204a1082503000c0c6402d034042189421460602141c5008407240581050341350305101400d40038880c81618402c82c103000400516070842a0060f0101c0c2d034421429056040c070400261300010a25021b003009110004442031165400049140d113501030440c400710344d40c0d562140da40c2e0740c440c0a41c00301c0c01c0200000c100d200710710440403a8008015151130017201125503c1e00f2a091403240d81d0f4514a482c1c09 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 473381294 1106 473380188 473380211
    0x608010f12050114191d0a12020312040b070e030a03090302190b0d0501150f02060609130834020d06050402061b0a0203160510030f 58
    0x1800c4005500291600c1030050a44444000c114010078091145010041d044131141c80081d010501c039030340804000144481003403401b8013140c2d2100e400540020b081130090248943c03140152411701200b04480d082c400b03421103003254000c6080c02003000464000120300b0f08402e00b50002d00301d118982e07a020300044040e00000c1c0c071a1041c0310444084070135110220020340b1081040c603494100014081018101c00e00811401c0601c400099900610a813440a803005a5034000c0c40c00c0d464500510105140203404200049882d115840204001c6170040c415040526070880d00340c814040029032903e05603004540040030a00c000c3d02596620b005501d0080d08000000307599112840011a94460b03050b001004044c070340b070441d607500e2000c00c940482500a5041e281b1082c8080c400025040da24042d15502038800c021118050340300754041c0141c41340380c0a0006d2402070303e0 = true := by decide +kernel

theorem cover : BRFrame.Cov 473201438 473381294 := by
  have h0 := BRFrame.cov_init 473201438
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473201438 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473201438 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473201438 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473201438 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473201438 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473201438 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473201438 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473201438 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473201438 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473201438 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473201438 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473201438 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473201438 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473201438 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473201438 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473201438 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473201438 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473201438 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473201438 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473201438 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473201438 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473201438 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473201438 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473201438 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473201438 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473201438 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473201438 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473201438 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473201438 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473201438 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473201438 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473201438 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473201438 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473201438 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473201438 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473201438 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473201438 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473201438 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473201438 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473201438 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473201438 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473201438 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473201438 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473201438 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473201438 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473201438 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473201438 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473201438 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473201438 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473201438 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473201438 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473201438 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473201438 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473201438 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473201438 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473201438 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473201438 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473201438 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473201438 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473201438 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473201438 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473201438 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473201438 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473201438 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473201438 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473201438 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473201438 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473201438 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473201438 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473201438 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473201438 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473201438 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473201438 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473201438 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473201438 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473201438 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473201438 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473201438 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473201438 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473201438 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473201438 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473201438 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473201438 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473201438 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473201438 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473201438 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473201438 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473201438 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473201438 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473201438 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473201438 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473201438 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473201438 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473201438 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473201438 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473201438 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473201438 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473201438 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473201438 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473201438 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473201438 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473201438 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473201438 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473201438 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473201438 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473201438 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473201438 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473201438 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473201438 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473201438 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473201438 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473201438 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473201438 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473201438 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473201438 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473201438 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473201438 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473201438 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473201438 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473201438 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473201438 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473201438 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473201438 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473201438 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473201438 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473201438 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473201438 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473201438 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473201438 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473201438 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473201438 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473201438 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473201438 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473201438 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473201438 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473201438 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473201438 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473201438 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473201438 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473201438 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473201438 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473201438 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473201438 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473201438 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 473201438 ≤ n) (h2 : n < 473381294) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
