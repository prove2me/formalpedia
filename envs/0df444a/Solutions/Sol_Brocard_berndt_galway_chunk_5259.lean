-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_5259
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T15:16:27.850475+00:00
-- url     : https://prove2.me/submissions/6d2f8019-e2c0-4fb5-9f27-2f9521d4601c

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 945683453 ≤ n < 945863309 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 945684703 1250 945683453 945683461
    0xe06010809061303030b0a0e011e1208042606070e040b030609071a04030c0b0408150105060d0f3c090305040620010c051902010501030c090209030f0a0c14220203 71
    0x1850a07d102c1d4865080801032000000759110401c406060a080941da45148a80c075071040d10708000d03145030f0281c110641440144800703500702e14010120400f2091000b00400c2c40800d41e841d110040b1807034030000f91000c120a205080034014100e140780100c0180100d8031f011900941c0e50840c500c9140b040f210310981501d40358203c0d508a07405144c1051002402c030b5140d07038403250540e00900c103511562051029504007200c009001c10306881c002031150785003c030366911020140419000e4101480d546002c00840562210041070000721078144940c28603d00a0190b039041c402d41031642c9249042003e000c000a60080031201a5081410040007500c00545c1d00c5540272410345403001ca5611780704e25040c689411070054006841c03607000016900034008012401d0301d80a200060160710400001d10089400e90058454100040c2c122605044061000d42c900b000400b81526035000480003401508808400182089411342e1103181150002c001c0914091030380c0241004d0a074040042 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 945685953 1250 945684703 945684709
    0x12050603030702220906230f0c09060f0403060507031508060103021011012301060908030f0708070506070504090b040207020f21120d0507030e0a080d06050402040e06010809061303030b 81
    0x640308490309218204840e9000d8a020b60062047c0188802210031f240082c440a6a804000d103210740350045100c2c040d41c40d03c0c182c03610f0750b410661030903500c4601404140341c500181c0c00900000c1d40149000b08060a00010140072510155a291404101000140200030002910a0440340d050700c1b0081105280c4e00101c510f030900c0d100028480d420714200076941d800081d041c81c60100407070150784c15039903503010039104030741c1500c203d03541c5400c2400340303086a003110000b5000709070141c40c24a03c0c10081d540d1711810107004503002e1003c500081000d0010780d02c43e00c24484402403da40442c507014058000135021544060440c3c405c0044401301500038400c01025810380b032160341115a0f00040100c0e0710215000b07030404480541c80c010000302482d00c83c1c001c502580f694140500342c040210340340c4680d107a22404060f00c00d2a220000090680c6652000740000c00c440c6139070300e010307082c00c07800107200d5000505607001c10343c058808c0c40300002c0035001100c0c80342e41c581400910f5625401c04 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 945687203 1250 945685953 945685999
    0x9030d0e011b03051e03070c02060d0905070605030108070b030c030f1003142b0e01050c151302041503110d051009111c1a0a1d070612050603030702 65
    0x5030b2100b0621881180d4105a041070103041c20348407a209110b04403c0000016060340012100c200001c0d6262000002500740400241443d04c1b4480d00890420003036125149000c280f0344c000d000043c4004010032900606004c00700c09000d214803507501c4d606028040d0201c502001d087e0088441d01000803509903106040620021980501c0c4240424080d44900e5100d403258035000d540b0490b030040340d03018612100040c070060300352501c0d0390440c0e100071700044440303030407201c841911403048035500440c4141041c1030368440c0340c510f4106814002c2d1071042c442a43c00017009424407403c82d10b01480090b0141d480b4003070941095030524001c0c0d0050615521703283c101d0202c29141071400c440c3c8003d00080034910501e20708140c0c0c500c0441109150390810000c0202c80c082d01e00210f01c0740c51864180304030040c640203001d0140200d83d5036807000c4541c0349414043d500f80303154bd01800e010010355400c41200c40c2500c001c07420030007580c9001400329444e4810340400900c41c05404c50b5030840709000c01c035 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 945688453 1250 945687203 945687227
    0x1a03190b130605040f0b060322050f0a030f02010e07090c23030a060b18010323180c041503060209062214090705090103050411100519030209030d0e01 66
    0x1180c0102240001e1080c4020035250140c03601460030040c03500701c21100b80c0280c0554002c003804503407459483c0001031680b40c452105510301e220340031030b00d40d0120f80c0400030040c801c0740070070141064420b98078010300010b4084d03c02c1015a41403402c0041a0070700401c4a008640002c240070812034220901298190311450f090070f20180034002c0042407a030800c020f50721801e05500204025600d4850380d446030b0262860740b210480b240d000144039544283c00400f03100d116840031290302030000c0c11007d140c1c0d03002c60300180e150100800009142030100b0107180d0b0387c901a10108035103602c6816000d050385460101420a079000110070000b43c6506080740e40d00207401c3c1002c860940f10700305503800c0c040540f05402114402c86401e40b6207103441c80c0306500900f801d031926854510b211005501901e001001500c014034820350701d041c5500d5250b20070701e4014456032090398a1544004102140b8490800402003510600000c61140c5002604041c11140c034181000720348012401200c0c101c035080c0c = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 945689703 1250 945688453 945688459
    0xb090f0106060503041b0503030304080c0106051206250c1b0b04030309150527030c03010c02010c02070f08061906050303040f05011205160302071a01031a011a03190b 73
    0x703800549036500c44081c50140d8401c2011a1481440e0017581610308607501400b81c0c15001040814001000d400c02060900707103503000072a031f50b60348200007180495448040c1d042c580048080140060301800c004840c60890000505910054440184010fa0bc1080244000d80c1ca480c400349076564101e058000381041c0c4c401c0390707a40740c4900d4020007004151003549d0507020492041180320703008a05440303681c0f141945046007949403400241030020a4803185030140502042d10240703840038041d01403944625000466948164007000340790a989030300010f8801c2a1810511078001c0119010360804403544500402441600e0104000c050503403059500d48400500001c48921841e0300c0c600f21032098039042d00300d444400d28001034402c21150700c0000c00e070552011003c64040d5000c0c02c810390162030440603620480009420070310082c0c00907a07021400100625000081c8100d25003d44140b000d158040d886000000d8164000501840398112341e01d15132a4002429500c903c00d115001 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 945690953 1250 945689703 945689711
    0xe030415020f0d050702011d0f010e011206060806120609100e120304060c03050f100303050c030d0906020706061205030d1a090406061401020d0516020415030614150d0b090f01 77
    0x442c000d04603600c001e10483c08143c42c43d003131807000c4232031956658440030060501e190101540004442046c510a4201c2c1030009d9080d40042a180c1441040080c00c840d845000765030034144104041070746403c04044e129030140c02084030441001c5442d0326180c880d03c1010540150b440c05144c2401c115040c10005e6200100801040c0103180d0040d990005190b01d080001d42c03989081000e03424030881c0c0c00003850038546410000240305500400e030f0704500d06c3c1560b003840f003d48061015150704443c00c3d00e41030380129049050109c584a0f0300c1c01403070305a0109192200c160383e50b540701d0080c0c0d800e1100352030796070280301001c0400507403001d10f000c8010041403542c507261030301c02c00524040c051000307580d1101041103078550001070741030041072031034691500702482411707174000d030900c2803a04a81083d00c1360144212194201d04c4040070318810b50022410359002c8094020340d00009212080b0310800810104140e107545c00050602500b00301fa5503815a5110f220750b07e41800300102c280d01e03610b0 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 945692203 1250 945690953 945690973
    0x120807080a0f0305010f05180901021303050a0605010b0a09140109090e030304030806060a091806150c0506070503010b04060522140f060c06010e040f0b07080f0603010e030415020f 79
    0x11019190012140b59102040342e41d886010400a0042030b0007107581010350034120310703a089401454643c0c800100d000140c0f4010b5201e605c004050340c258022581540214000810000c403801190702500354003080504202101e100140200ca0300d106a055280500c5c0c14241607906c19841c42001d000c0f28a010b1001509035038143d5900e030f1003200c05400140030000800d5040c602181108e021200580c2c0d191002410440b039907a4500d8008240c0864030b07541c950014942000030b414280c1e059003500c400c0088101804c00390b0408100521200820804000612002c01d80100f0b44040e51010b01d0091b8072441c0303143c1410300800e21f1018424014490b808002001d992880d80f0300000b62042c0c1c0c3c072036054003040c0d00707201c11805407007140360064201e400180991164040090f030701c640164190317a41001140c54000c2d0755841a501000081c000c84204042041c0028015070031070b0080d0001c000303480d045c6594a03120f010318050901c03600000d8411100b140d10801040031036134661030136201c8400c4 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 945693453 1250 945692203 945692207
    0x141921020a0c05061005130c0c170417070513180c08060105030c090f042406060e040e0a03020d0806180c0915120408130e090706020c030c0307120807080a 68
    0xb41c4801140c8502c01d280c0044c0c030104485503040c1c1120b6000d0842078401c5155407441c40a000002c90071420018120b001c400440c01e0510724904144640c1c5800c3c1d40c442c1084402d200c96200e8a0481001c0e5110000420a98607800020000c01d50318100001c0c0d01d4a00c1c0d000604031403a000300103000c0c10402040441c0c40341011034054100c50089013200c1d011613000050101c01c100031100a000030305440000b9011503078030156140341607103020120a0240d290315901c412940c1035040791b00082d00b5120000c5040c10315102d0380500201d200f0041c014890903540003940c984008485208100740a4027092507034a80c00000e514000c14900b1501c903074a002040c0300c0c0950410300c042c41c0700c2c901c81030b411480d80c4165001c94020311142c00c6440140d0307803651180d20f056441607550000b200108800080c040c10018845800b541d6040d010344401031504000070b191917404420b25100c0d030040984540282c0e40001c40d079007120a141c00800e00c1c407800742404401d5006424018041350400a031140c1619 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 945694703 1250 945693453 945693467
    0x70c1103100b310902181003020306010e0129040b04060c02030705010503060a0b03070c06020309151b0a0305040606031208010306060b041d15120a0201141921020a 72
    0x4082a41e8040f2022056010050682d80d142240b681c0f112024801c8030420005403c0502e0260000d0040f441c0100e20406103405003e084518070304a01c89800c00b03004601d814000d40e801070452198070b0701e040d41000518891f0958890002044640c1461515681c014920517100284000c240e650b4545503115005400820401c208a02c00d016a000c00f00301503001d0003e0301e0041c400940403007811814400ca20040c0e51015044800388525013483c440052914001903100d40c403560050001044000380c04d403c040006020a00601c1640c2c0c1540b082d036921400b643ca07003160f280b6003c03c0c59250f40c1006001004580c0019006550400c1800c00c034a81110081d0b040324800e410411000360f50b030321107a805014030300503801c4030340d545030030040446011140d168000b80303606100004030400100040e15482059034036403264000300c41c00425980c111014240b51045040154030701004444004842440d00c2da50a0030b01c500000344401c0c0000e8806816040542d0113000c55a40502250280ca03030 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 945695953 1250 945694703 945694721
    0x408180a0519141905090a061a0a0201050a05040b0601030b150c06010e090705030d2607030e12070f140a060c030911061303021201020705120a11060c03070c110310 72
    0x2c80040c241e40100d030704012001040d0401c0502c8000c1813079060900b0050030076000345c070103a003040c0ca1b0100482c41240ca48150300321442550034241d0303681c2c1c411b08040c1c03d50714001c0030942c1041c41d110030000424100c030384c3c4580c0402d0902e40080c05282450000e0b14039040e603c074000c59a440824a50b1b00028001a2107040c0c03003038146403030f400fa80d50480c001d40d984058081c10790143c000c40206414070b07021310310480040c1070413200307040c09072440810071444101c04c54211001940314403038120404801d201c4290200c0711a8140c52a00c04585c0702c607001210100f4000f40303c403440041c8010241d07014065822031a40c029401c2c811529103000040181800303000a548018400e440c0c038032145003510403034550340291000a40902c2c07071502003041d0701040c91403400c0f555400704460000203000340b00340004c502010080303548445d03443c04014640c5003840702a088a1b8828018000315040c4d1400342e076841070b0185081c0480c510345103818407140d8290b4448039050311400d60703040c62101c0e070343e009683c40c = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 945697203 1250 945695953 945695969
    0xf0b0c250204051f0b18130b1c230f15090705010915030902060408030403030206010f090903020303040f06150303080f090c450901050f0408180a0519 66
    0x2264561040410704c660078030b00901c0600c14030200c204a1380760110040c00c040110021490b46000400340416201480c1c1d44403102602d0360703680000303041c1ca020410b003008007030b03403072242009a4420f0b0f886052888120625044008101041000044080104846408811007640d02e05441e480d40c14121150580c0c850000b030156071800b01c0c0b0342d4401e074100e10840d00d402d00141c10054890b001507000f0f1103688000e903004035082001088600b420401030001394400d9008010561500051407840060303034201802c02803c1c4002c40d40030940c0042680c4d0000d4108000d00c500c0f0702507203045001812515101030300e00100e0300f40003003810303040020f50b0b2050640301d42c180c8c125a1655507183d143d0505810803036010b181e00203201da09801c180c0800292070034451242c0c1549001d00395615460030100c070f1114500000030200710031528280155500056071707182c4081c1c01e0501c0d5070399800c5805021444901250509150405595185010002800702038821220001c3c9608400d21840c441e01500f02 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 945698453 1250 945697203 945697211
    0xf060f0609081203010e0601090b04270b1815030109060c020f01090c06210f15060c02091302040f05010312170c04152a0b060108040f0b0c250204 64
    0x9103914000c10b0f50707588800440e16062a41e03003403240b900180702c000b13015141080740c00301c40030402d6421000144090101c40c15a95048a4695291801d15001c45d031032072012418803540f04030301d48540c2103900400d80d42d6010a000b6a8548450b903912090051516a0542c02c0c21084030522810741c0c841402c001c01d55083e0f8801020816410b4240c3300240c000400e04d52504404001c424800c5194510304102c1d4000101d0004003034451a00f516992500b10320307600e9075903c51451941c07025084d5401440d0b0f6050030000807005400007404071100400d20410320551700c2c1c0c0c04046641e43c0c4d00018103402804010015540c5900b1701594040000719103070b01180c0c6003400c01a0840e80c80f8000351040c1249420145012300301744600c00c1c224030540400c414002a80500096441000b422190914003140b030b96003d103405040c40300b02402c01601560510001100f07000128040380104403100d07801600b808a40c0c1ca440b4807140f024824040b82e00507064441e075910304486400c0d80c402d01ca180c000c6400b1300c = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 945699703 1250 945698453 945698459
    0x90f040c1a0d06090c0905010f0918020403020d201203030402040b062b1a09070c260417032503020703080a020a122309040f060f0609 59
    0x541110029900a00500e084400c100410481014062042107091000c0d500300141020800d090b101e064004105454031500f20140c401c0d8007085001c000c0009280c200d03103011081c3c078090600c101e1406200101c064101d9211081c44854040b28021a405004617600c401c041c1005086444000b814511071140c0000440813481d0161110700642c3c460406545181c0b02c55003040000c0c0307030004549070450380501417002040960502c85109607810010948103001c0414200100d881c0000746038211100000d84000d59290f40480680c007002d141441d0701540302c10b041044003442600302a0b00001d0324030040009040210014200f01d40388000540440f0303c0d40d0360900c0c5c07079000d42c0c0c0b51200c54001c640000c0100c0d1007000900b050441c06070066a01181c1c8030348980701150702c01c0884c075001d68400074a45040084001340c03004c81000174503001c0000c03920480f20f40360101c1710b44504041d640740421a00c880341c4c1c4d45c1d80300c80c5100303085220410000da5036003049452212588203400c04200300d03503000 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 945700953 1250 945699703 945699721
    0x70510020d0207061e05071a01030804150206040c03030806241803300d090b04050606040e0304091d010501080a1a060916121e0c0c0804171c0e09 64
    0x1850204d004061005d0030200f2060100c90f1500300307103800d94a5594001341c0c212944030720840e03139000e1030080c140e60b903a07035043c03c50f120f0441a180441c4030865104000300000310308508004025654546400c054680ba04c1000a4402c801c40d2000c81000030400303600389803c03684100902c40c00b895401a100030fa00c80808050301e1b420502c49540300e450300245041600c404400403802440007030300c010360800080340307e5401101c0e992101151204000c800744418020204801d50780964116424000181e0ba502e000d51240658425852800d88031841c0c011000d0f04800000034171105400200300b69a50b403060940e0300e6800080076541201ca031030f41c00050140b101c1c401031003024090460101600d502c00000e8020000900e9001004003c04c2c1516241105020714000c001d01241d00d000c100d0740e0303960104121080122204184600c000710440000e00c4501564200c811404ea90500300c00005219800d00c1c00000a283c40c00000d1488914210340000c3c12000c55502542c07000c1040da105294 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 945702203 1250 945700953 945700967
    0x31b1002010e0d050a020a12020d030f05060d06020c1e10110c19020a03020402030709090b0a12020f0a12050105090111030103051c0311040807090509010504020a031103070510020d020706 82
    0x10256420101c3d141c040640070f00010702c1e40405500c1141e04030501e80d00e41104207020400c0703803401a08410300041c071b102d030706014408030121408020065804c1038800200751900d0542c004000c1500811001e00141c000e1041000c907100110001c144004c285c4035140c0c43c0c442500c041d8901074030b001c003010504803403030060700d8002070790000400d450156001d1070002001e414004990041002c0000b00058070346001a5009071810b0b00e03001c000c281441610010b071084800341c0e50082e9101701d400c00500d05240580d0500a4042d10300e4003003880b401c40071500e010226081080c046000402c41400c104056001501c00c0b1200e20081202113510405045644403e00c00500198001c254100603604032141d000a2000907060014000c01c0488003690355800c6540312007108d400c501c0c4104441e090314050954001103c1c2e0003080309203840e40c0014850f5040707000182645140040000b22a281000080e02800c80103084075006081043c00941d0b41d03010020b1000180180940018664009c0b01 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 945703453 1250 945702203 945702221
    0x4141305010f140a0b04060f030c0819090218010308071401050712240b070605060f0603040b040c050619030b0d0201050f09043306050403110d050a02031b100201 71
    0x40300c81480f45491800c290049800c0d0080740d01c400700810000324428020f0003040204680c3d1104031900c034a00d000a8125280c558619040c0076046040008070818180302d40300d500c49004000942d82c0950012a00000e881040da41440200310004802d21002034060007645208580d401c01ca0155841000c0c203860050b034090000c01c8038000c8414020103213801c41d80d078829525404244621a004203503441d80c4c015440480380d81800607000b81800341c0c0e030162030741c0408141c44940d0030035401d10200b600c9100c010005013603401d01d200454108007203480344100400000b0712081d220912084000d030b260721000c1010011a2921004482d142000700300000c1d119016181d1a00300340d960102c61805501c0f80c0708190b40301341d0700d040006040b122032207805d08417420000f000070081381c4510032640c40051900305400780f040c00d02c020000a45003010000c1a4081034032071441d2142240390891030045800e800a506000f140c2c03c0d4404100313400001140e221084521002040780d86900703034201d8124903 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 945704703 1250 945703453 945703469
    0x1b08100909031b02030c03011b02120c0712020102160905180f0a03030221010306051807080a12051614100c120e1e0f0705151204030e04020414130501 66
    0x300e10f076a0000041c001400d14009000d0b030304481c440c180041e00319091041950380c1d00240120011a66904020a4030203205e6189442c1c03034050051400f0f6541c4149104110450502e43c60860031a44288544458210103414100c86a9101d90f0220081c10080740d400103010113000d416143c9610024a0400da001014081e2074076110031388048000c1c3d404a04030190100074008424091070062203030a00039801404000341e6030600420b4540bd503907090001c0100d07540b10301010b204500b030214482c44c103030741d002406201c03504000400380e81c40d00401c5c42080414044030f21083c240909a00500c10004e4400283e50a01c2e1300d40c507181b021038228500000001d6140701c804200c1e889180d00030701c1407905401c10ce51088003910ad03191100000c20710302c00e03801e800004100c3d440d554108400c9018100071075010b00c4c103902c0c4059904090090841c3d6054071003042022405041c041c469481c5800005041513540301d4403481f401c7d0078841d00c50074090056000c09644810180b9611405d81030f20210 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 945705953 1250 945704703 945704717
    0xa060810051317090319050606030c03030d0c021e011e020a050f0706061707030606051804081612050406080105061e07031e1d0102072105011b0810090903 68
    0xb540780c031060ba00540220a110740400c20080c0a01d42e400c21001d850180c00f0702c003094094090303203000750a041c806041140a40c0c0019005041c59a022050302d5041c00001000a0901c1004004902e060b144400c2940c200701c1d07041581d43d6501041d048445043c1c6498418032024020340c0600d8128851320140000050081c02591115850340d00203108890142d080890354a0b02c5101100c0c070400c80560341c5416500c02c4004004220301401030000920040340d41d840003142089640c0703820030004200034001d400025444084542142e003113462550030407516070401c41512000703042d0754041e02519000c103070780e200000360a141c501d045a103a120394041382c070040126102405400e40041c1d104405005444421240b501c01c2c182561426001690300c00084a0340300c19002140c40403100058115040300b00180f2080040c0c00034249a4001300c1072844c58100381d030400b58014200c0b00d92100700b82c0c1d5040c10404246611554513401000405890600315940b0524078084900311840203000c2021 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 945707203 1250 945705953 945705991
    0x60f07021b0d0c0e0627070f170103050d0207080703050703080708121003030306050103052e0f031406100e040b1503010f0614010219170c060a06081005 67
    0xc08035031508105406040541e55003801d0f55514120207264018100c00c3d0503941c00c0000e1031501c0a05090303020090b84000e10204007500703544607010002030a85003886203803840c69660b02e00ca58810f9400100c141e0003098107507144d180886e00c2d0345c90210b541006101e01c09021412417030202d0b41004580d4010001c0001a203503558100c02c1d90021176040e035000400b442140003418869100e603108860b032413601c40d0300034118a40501290280c1d002581014a8841044800d4040800e80e890741d20300d010f5002c103400100940000d03510855004200301c1e078400c10001081103821441015003200e82e40580700d881c0d99100c5949125031440c8035401c001d1342e50740c0c080340c007050300111402d070080e903640d0080281e070001c0300119094411890301c030600140e40d010300300807903c1a04d01e802c2e180e00007440504098900c003010390b41c01480b0060041c1400101e8000940540622011103890940b203809881c02807500004041c020034203441048610300401d0680f52103110244207440c40b803d2101c1c01400d005503 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 945708453 1250 945707203 945707233
    0x25051018081b0d1e03050403030909050c07240f1413030c030e03031303050a060f1109040f091e0b070507081c0e060115180621061a0705060f0702 64
    0x10b20910940f4140c004841c040b4036a00030109804013503000741c507001e41c0c0710700e0f503c2d00034040f505941c011318440c0d1a160a02c441240441c0441c2e85060304050140b4003d1002040c106085419074401071010786408030418580d81141c0100051284011607810f00366107007845051104c0360b40350020001555200207500090055991051200001e800c9070700344804003195003542c2c1d0300c030b40084d01c3c0ca03400a0040c1d010400703039000c3d0140c5035203103840600a509003803142031080e000304100c9a1045440c0e03001c4240420565100c0f40c0308a4001c8510400c004203030002d0035280d00d0403801502d485148070700003100103000f90308442e203542d8000d81a62400b20101040c402908085588001903a120740c64140050020400c050280c4010b13004170b10380246e00a005403491050001c0310851320300c100010080c90703070001c0c45903040c20201c00d02c1001703408803140b8040040c0342503000700040b11001c1b80c03044000404c40015044152048044800d03548407002c0d03480510108484c4040103a00404005034814 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 945709703 1250 945708453 945708469
    0x50906090705070309030b1003060e011a040f0906090b1e1003170d090305041e080a0b0601140c0601050117090a03050904201806070525051018081b 65
    0x42e0280c1760044500c0e0300c0360b603001d00c500001e803460a0741009070701003032051040d030380700d4294001000382c020026000408260158082d41120b410310996403002c3e039004034074203900450030481d40702e003042054203100d240031940700d081514140087c400d480f00b10000040f80c01502c034003401140000f0040c451540d60350004e26100c809840b03583c04c2c814054101c9036400382c01140e103c580b0a45038952203070300700240c0041c010045003c50300203c810a5041080c0740002c9849040b00341c008800d03007029a5003030016182c42d1b400c8020504442000a030442003201c0104070f0f917050722002d980d165070707041c3c803d180c12107419415a088071040d00300305020350029000300020f000541000d00007051401d8001c14485800c0d00030420070741ca444c000215900e100011181c61183c01e031088643d241454030300e4403425a00d5590036080a90300d100c001c4c65450009a0b24225001440010003100c6582030358440103103151200a00900000703028480403900503400303d00881a616400a0060b45580d010200a024 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 945710953 1250 945709703 945709717
    0x14060307030204050d060b150405181302121c030603050615040b060c0f0f120f030a02070b090c1203092d0307260d0c0602070512031e01050906090705 66
    0x410b41c20480040c40740c41c3c1c62500c0d0581170180c403000078840000750901c00000110811040e00f030000304010311072a41c4030f81020b400002d05001c5400d4039a1945640100020b08001c041c1d0b0001e400c4c0040b41c0c10746000100403d1040c0010000b2004440150080e8182c401c0c0d404003c0041d009180000e129000680c099800c83c00014004207110703c2040104400ea4001c0c44680060b404c88113161081c2c00d020040801074030700b01c0000700243e0311040c448400318007629500c0c00d074120002021407500300e000d405840566400c02c49801032420b18407110780d80d40420103941c5004000f00c00180b82100c0e40403041e180c0d9160094203450034440c0890450b048180c5150702e1115540e22020030032016182003104401804003404034100301c1082c0d411150203a42c449040702403e41c0300394210340c4100d601504002000d64090b5001d0780311480d47ca051401c1140c280035223555108040100419001d406d05403c90700c03408001c1c807036a542d80340c0c1c007441003001d1704864154100354844085128207104000400032 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 945712203 1250 945710953 945710957
    0x3080a03110f040e2401080c0705060f240604052b080a11061521060906011802120c031b0a020a06050603010b01122d0c08060a14060307 60
    0x1041e00c2804003000190400121641c031414089401e2050340c030384002c9079070031a81c00d104010041e0740d401e9100d4682428a034465041090783e5010915405400782030300c2d4010380c4681074a00c03e03d0800502d040c00e4204039002252010900180050a860b4080c02c00c0c00310006040c4600d17141c1082d0601501109401c2707110919a134071004840c041c0b04819000d0b20040c802c010043e1390701d200000007031544155004100d495040b240602090140500003a80007100558903240e0391090403000c02143d03841c0b800351313034a0350164500700701064101041440c16036030f01020702120350011f151354030102d02501c2280c140c070390005000708003d40c0705a00515804a0030424144117001444083c08154100b81d2503280503a000017091010400e01d4064141e220005600812018442500091054045010568079a6a1f40c0075984d00402c080300e02644102240e09190810104100c2c0c00c1d00803e060261240011200070101c0d0061034201c800350103d03480030311200000381801d41000719a9001504a01c1 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 945713453 1250 945712203 945712211
    0x1413030f09240e012d0309140f120a08060f040e12030703060b03060913060b0a060c060507030e0604110607020a03030804052e0902042403200a03080a03 67
    0xa803842c0509800c00c480011002200c040c80c20303580c0081e01c42c00c5502c6241d0706015450300407244520b80e072410405040f0352203e2000000360384407000d400504003517401038126071044003002c41d030324000510102c844542c0d108403403100b04c081c0c603410304070300507026400006103190020500300d1510650107010a00b0092000416007049003455240c44841d14070420600000b10422200e1501842040005c1c500030015a15610b04100021030222005001c410f5826904410b1410721020f98402c120540b00607042043c40d40d00c0d00c0e030140c0100c030f0340b82e4100c074018200070000f0300c481c0c428050440d1203048440204200e84035517603140d10ba0941088115000300d4240101005030b030340c180300d010045010b038840c40741d0350405060286c207001200007048000c2880003000c4248403422100341d40940100100050307009082d01c0090080d11494000000c1d450341c80c0c040410182054080e20200da204030702840300e844a03004450540d10b00181c0042d80101c0000c01007010548050060203012004c0c50002 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 945714703 1250 945713453 945713459
    0x90c0408010507110d0f080606030a06030606290703140d1e2910110c040207030806011707020c0d030512041520030c0f0c01020304151413030f09 64
    0x142120821034651001801c00c00100c00151380600003e284d242042c609524102c400359000380c4040703800f030455030260030004000703640c000190744850080c0d6070105080c005103a03244a00801301c0c801c45400c81e2024081c1d0840c00c04014808111410507605444280350102500709481064224540481025840d0411f00c1112240c107541001200d00083e0700060445250030f030041588071003020501740b0401402da1440c0eaa84040042c400c0c1401ca140c55081000c1d0181c011307050501042c48607402a001041c2d032002c068124410380d204000070391f01c100840d02540c4805460310426900403025800091040415082038105143d9690290902a00d4400c1c1c0142249941c0801c8909850125a190f0301e41c8030120580140c1022001e00381e0700101c940d4540c025010b062102074580c01d10046d00164004010040400384c9600200d110000c5443e460141815200201c1c041d9411012a00d000813010311110110800da000e02002d41450529000c181d0701625018400d05c880c100340140c100b000 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 945715953 1250 945714703 945714719
    0xd0302090f0d0305070f0606060917150c0d050f04210c060b181611010b0114070615180b0603090d030b120d170906010621021e071101110705090c04 65
    0x4006e5103440ba03140041e00518004000381941070344c3c1c11410301150361119a1070b80e8900001c030007800b0f05c1d001e9800072598560344980401e6100300c950310b0781c8260910007005944540c0101e10340c4120700660584d04a9a08041141108050002c2c2d040101d210f491004c008a000361b40318041c002c8014042c018403010b40c580081304040d0840301443e85000810001c10851390001c018140a403a4500903c008000340f40040c02815184904240010020407030505000042c0c20003039800b03525411801a0b02d407907403203c1c5a09200341c2e202e41c80711400c01050071030500340041264400d04035840035050f022003141c0f0850107018003422050303100b030041c51014880c1405000050a60b6015261100802c81100f641c510000e00181006002d8002000402c00f0755046460b00d140d042c80704d80400c000c00140405500280103510600040001c1c280c100841681d5400050403414000d5070307074008108100d001100c41c0f01449000b508541c0040e0000c00081c2018102030341c000d241c0441081c103050720b075002 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 945717203 1250 945715953 945715973
    0x50307170c0912010515133905090108010303031812030905010e0c0901172107021c0809040e030405090a0603030801082b030b030708010b030d0302090f0d030507 71
    0x180000d0400003411180da190000f510101074600400030f01076450074a045841c04411150428022a18040c00e80b00d10841540904240151a0410246503100700d00407965210b00c81301c060000400b041c04085500d005200f96550500e0583d266030f220783c2141e07400c0b000b9004045046075500e1850340c0d094002840d000c55400068071954000030808014107102d420b4444403040402c40d9001314020b500107413180c8007a907065a0600303141d10300c0c00c0d0a5041d007516050000e10100506c594540c06241c000000f003008155070f900803118203882240d140c60300414042c0450008244140030810b011003800d054104440303071800d103416603042907516400f191000c1d40490b21640884e070354183c00c0c01055000745100e0701400902d8010710381107040590740031503614059242007e0760b0000504107070703c070b10030b4002d90310b04a805400c0c0c800c90381c1c1d11a00305018000d1030003003034400c1c0034000650030b040344070b0703c01c2e40d00e103002c01000325009101d41c1060000507070001005404100c420049000400d064800d = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 945718453 1250 945717203 945717211
    0xb04050a020a033e041e05090a0c020c10140d1407050a0203070803060d230715090b0a0315121203022110080a0605100b040b030705030717 61
    0x5000da0b40e400e034020300404a41e400c603a000c004642501c44103203030303101c83c2440b04d950718071030b4140044880a03101c3d44080d501465200f62100500d4a80104401210054120444c1d105440010254036003d031070700c041c5d030a086042c0340180d1101403048a2841c200c903100c0c06140c92814416050b541544c020f14859106980400c007564440541d480d03c9198161081e41c00161403030484c0c105260518025228815041c01a008020100101c0d2113582c3d03800c45076403d00d5011480b01c0f031400705a00c500002091000d80c8035504d018443c800940d003c02034030355141c0c070007a9645501c00681003a4082200b82c110507070b400100344d600c00b00080c0d010701c10f00341c180c00b42c820981e040300c003407009180c0880900134900c008410140180328003640241c0741406e070020455030f100c45110070303552915078440b90a816400b04c841c5106101c01d450610500f07501140c050508104105e03400c90311138580042504c1a44103591480d40e00304005000c0030311075070103146c100f0070518003103020b00c02100c40c8042003d0107507 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 945719703 1250 945718453 945718471
    0x20c0712020a0506030c030a0b0301060b1204020306073b09010803180f0a3f020a08070b03012603070308190e0304051e040c02010605190e060d060b0405 67
    0x3401641076192002896008180854a2504c0c2d441c2a000e03000c00c602000d082808c606440d09005280c036a42034101c0b20282c0110052141c4482e4080c3c0d00c8032034404d082d07a06901902540001c188190b1040080c09810a441300c6100361a00b48011210302c0302062030301d10001000d400c4010807a507030b119500180249800c100441c0c031268200c064840c0840c82e900594440e5500344c0d17109030640c840c0404c1008545900000704410b40c100302d420000d881c80072032404081c61800c802042c0020082207100c0c0014001d4400443d100d840301944c9680e0407981c0035000641405200400c0030000020040840001425654100781c0b95207801500c0c54010400460100d0011310070420344442c201e040c907040c140090014824100e030707041e000c2c0d00d03449203004560007642c0440795030b046086044541d0b40b022070040c100700000c0b0355400000740202070b10f0080d517200d00da01e103101c06641d8414919a5040c0d03068a407401100c1d840c2c0c0d07001c0001d61140440c0031680107440b103490249036505c1c1e1140301c0c4204071003 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 945720953 1250 945719703 945719729
    0x20109140f0a06090510050909010b0c0c1915080405030d0b12030c0a03270302040e01060e0f0a1b020613030c080a020606010206011205070302090402010e0d08070b06062b020c07 78
    0x70100304110303680c10f0b1b00741d1010410188600724082c0d484803030312411074001480c0c0a641e05080c0058500700300c901c45505030005104803180510170100140401100d115108142c2084152182111402c106407400341699006105c3c9080541655014001840000b041c0c1d5070070483c0c00150785d04540007180e44011f590804200301741415001820303c90a001c3c1c0d1180800322540d440540c0c0da41e2021408003034004d6542d510103d00c602400d600c903c000d00740180c01c0b0001454807507011000c04400310707003040199040c03203031440b000840b0015910b01e4900e10307005040c255649010034940403075600c600340c1c100010b98201c000400d8001f4014926034095a001d0000351900070300192410f82d040e400600040300c2c01c3c1c00a40840c2c0c0205003181500c0d4100c51001d82a100d60004891890f2180c40c03a5501044502d034403401c103c001e000a041041c400e01c9603076656a00c1508001342c5015080381240d019101500d1142001d03020011240d40c2c1203141e02c014240760401203864a060a1500001c00303003242 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 945722203 1250 945720953 945720959
    0x12101502011e0c20100204080f0c1c060213030b0a0203090d020c0303040b09030709110c010c0e0d03050304021f0207060210050705161415071803020109140f0a0609 72
    0x100410000c081e1040c1009024000c000c242c028900414030248a6281220f1441070a40c0130090011070041184102c065480d180c449501903240e84001131020014403400340d0410803424200e11385840d00c28039680e2510f6110703240c0c880c04041e61100c0c10048000b06200d50101c00205002075090050348041e1340140c03a0f1510840c42860b060703500c0000c400f5544038814020165800000701c03005d8031000320300b098803440c01c0008070749804915081004150b003084150000202d00c040070b4001010720300003c1c0011300d032000064920008155560b40c1044180b41c152000c0381c0154010b5400c40d1024110556807800101950140521038032035000513000075904000140d410848042105e0100c42c04015030b003402140038080e032081102c1c0401118120305048103200310b24609a9040f00b1001c2691124541d01148110200c03044941d10701050901c40003810141030001d406050382d506850394518541412141043c45c40e40382d0b00c80d035110040c20124055510b807aa0140b000b06201c0d1204001241 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 945723453 1250 945722203 945722231
    0x3060b0f030f0d1b05030307030c020d03050c07060b0d020d0b0a06050316030215040e0439050618060414120a11010f0c1406010303110706051210150201 67
    0x40014003034400ea0081160081040000c1480f030040381050608221061580c1300e1016000c140e00800b500900000c010800584d42607004044000707059401c2da0420144900b05808a035001d8030074903403022040c000c2e2000a8a2540500c07074440c00100401c00341d0340b269001461098484000b08c40d081081810710000b10498080d400280c076044014000c00384c22680d101410b00030a20002c2d11a1610880503a5514001c1049901410584000c0344591410382842a0340e002c400303028222100f0051602c11240c0071007001480390702c1e0715100e02001c0514000400580c2d411030702d45a0154602101c134440c080c3d4a101c01440108420030146030721000c00010000c0400540e184020140c00184c1400300103505d20700080f00b1500242803c07601080400021207180089010042002ca804912140640d20004105040305c0c42a81c0701030821400c0303440309407542558801e00010441c00d00140141980908059602c940388002c058803071682c90300d074034098003084903620307015035075402107464048 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 945724703 1250 945723453 945723469
    0x1103030d1b170f040f02060c0a0201180305062404020a0c1e05030d05071701081e12041703090a120c2301183c0b07030c03050906030103060b 62
    0x603042c10500c01c1d8034000b000d401c4840d0001000303002160103243c0010200040e614902d01150b8006c0e000355250000042015507601141d041a0f000c00c003030103c02c141e40885045004148c0c2c1e03100014281d9500e41c00800d801c080301c0010b000a0401050076000504e880724405400704106035030395034240b51050f00700008030300d100f0b803240c4280784130b40031305440890000401c0b142e4410440c413002030543e880e0034080701c2c1d0381c208000c0d50800200d404000641d0b03500001d410300c0b280100255006103030b5a040005a40c600e564541d880d040581400200400760030501502903441d8208203981c50704416400150320342c004ea800021b60014491541000e001d0800150000782820f440c7c0e017403844110103801c1e01103245082c9101e0410820164580e03083c83c6582c1d61500800c54200c100311194401204a017220b958007082d8643c20742c2070f15100407100d440c0c820020481d6101684180f50511640701200c105804084c26000d00c2020804154580c0340d110055000398007a810000e040010381007045010 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 945725953 1250 945724703 945724751
    0x3081329040509090705040f0504061b1b15050702010606140a05030402040c0c12031a01181203110303090709060b18040f15080c03150906040b041103030d 68
    0x2201920a5248a1800c0d88003220103440080b41c0d56070155503148851803170800c0f5500065041340c2005400108030880d40c00541c0690301c82e030700c02c0c0080504031003290503241c1c00c061403400244285000e0b16401002d00b1040500c00e01680d007000f2000c04030300c101c038183c5030161003400050703542d0031040018070350015900361122410084c04d4904040f07007800510500000d40040d100f1a40c555900722118000d80c0c4415503a80e100d17804841c401c0146101500800e4031140da4a500300d44c5410487c201d622179a2010080ca002d807401041031800e0546100d071889000b401101801a85031191100e600200069881042024000c11001f42010b94040a4907d2079205c8005050180442a40f03e402d414032082c0b0300c081a940020304071244403501e0042c005003581803002c0b464400c00490242c1002c02c00f00d500360401e170200c40190344154440c811904d030444444925821010101e4009450100a1070b04503004000300200000300900180c110b070700508134080810380c0c4668800050f601e021110104d = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 945727203 1250 945725953 945725999
    0xf04030303060509090d1d03100f0b01030e06010b0717070b041104050f13030e061c060e070203190905100f090e130807020310020703050301030b0a0614040213030813 73
    0x70f10b0170319014030340e5141c040b10f491382d0500403c404c04141e1030401c81e94410710320320b0040880e000d4040000daa00001c02e003106101034182d0420b41040050f5009000742d038440900c1c0001010260320700500d900366034100030707020ae400c1e40419038400101c0724104043c051359809058200c0e1903042c549092501e003140356185e40d02032418181000015030003528000c0e804494200c42140c044841c1c60f04880c05803503501d1113584810089000550440b00c40250001a40383c5102002100e4441c00c1b088072a000c100e07460401a8030400522045400790380e03090102800900740b140e40e15480e5000a1141d0031010070500000d07505075071030104a42c1c0030f0300d604002c21441750f007461a03090802d810240c0d08000c00300038218140004600c411500c04101c2c40c000c42c100c00c0c04c21074550950f864000d205510030b01c002d5071031000300700c081a20030289204d044121a084030b80c2003640c94480c070922000c3e4000764112081c070891343c00c0010100d04508002e0074111302c0000e00444540c1440c00400a07042c9807039410702c07 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 945728453 1250 945727203 945727219
    0x6011805040804121a0a0209040b062b0603020409030e2e3507120c081503010f050916060327080f04150e09040c05090a02040b0f040303030605 63
    0x1182c00c2108441c1500c1c00610781c2031495105043c2048107151008030303106015006001c021250070281e028002074042110b042c802600b103907003004075502941c0e4091117209041e11605290349210f030701295520143c40c101088050303481e00010222030b10010260049a0600c014040750318040140030805031410104056841c107041c0d00e00035200c0104024401d2240084035600c0c81c6034000e8902d594000f00e80c000e54502c1c240703214202d001e035030709132880404548901642d200210180c000c11803100b000c0d64415049a5405a44c48020b02c1e180c01d095815558440400c0d55020090180c40e1145407120003c01906481c803180361100680d0703600013403c046c039100208003d0264060114805149462403044c01405420408080d1084452f6000e40100c0001e000601a030424446081d42c45151034040c00550450148007856070100c4000340145043c410a102c64a00f1120f541d4001d01c80003401424103440701d80e8000203500c10303501075100e0800800c040007050b0b81801000d000c3c00050750300103 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 945729703 1250 945728453 945728461
    0x12030504350901050d02130807081515010c120314060409020306040f0c0e0f0a0606030b030c12100207030e0901090c142805030a050a0b1c08040302060c06011805 71
    0x1c0c2601d040300d0285201c00c1000500c000103a2207641500c4e540907400703104555034504000f01c000d00300c19030f02c02d03a000343c0291000042e01000c089040340c03891007200c2030042a03aa850341c43c1c42ca500900d942960600111031030141c0070a1508503c10307208511910b000407e15801000040c50401c01080c0c10720030b50a00001c0001a2800704080303421542c803c0b411a0020030718540b00e850031481d0781241c2191410082000300784481c42c2080c40c05003002c10300802215889410440c15a03400035185030b0103a00102d190030890400701c1028240c04510420f82d0f921000f0b11000800381c0e030003d42e05600040c443c6000302d21a02c0c1680b1501e005201900003000b104d034a105d130162140c0c0080c2000d5142c10004107450444403548103075030034404182441c1104058000e074002d0f02507042543e800d414180f520380024100c102034428076800d020002c2201c9414580f02e00c880b4000301d0103001c2207034030b03039014231002006841d060003412078400c0f92030252090f58188807044102c3c2c05030381184006182071030240 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 945730953 1250 945729703 945729773
    0xa060e1c21110703080406060503030a050417070f050d02190602030a091d04030507060b090a1d0a0512220b0405030d05040605070803181b030c0a0810021612030504 72
    0x210800c03941340c01c0004080d03446041110050000341e00103034040c040001c0030b0701e200e0f5100700280706980400030920143d4007400a0259940454040e8481081c800c9905015618144403507480884c401007005410401d031350021100381c44c141d8001409a030000c5100d4282c150400142006001d42d0160000340c05140e1044d40401c4401a0000d02400030005803141882099080849804409040c0c0c900c2c0d0f0408164420083c0440d40f114039580c0203004041548840105040c2a9581c02000908515846003842d016607808016050618245482800020100030504500030300e904410151074a1414040c03500f448840c0441808010f01000107111003900501940c07402c83e0031942454a035a21496040700c2143d00c0158180603205854103e204100007000c1d0100c594401d505a07020603040d642403100c401158000c11050f60006102c6c6401a42c0030350140c08440c4001c28103450601a58484420403021400c0380d07000a0f0f00c4504200901c901002c1c0a03468002d034402d0010b14603162044 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 945732203 1250 945730953 945730957
    0x3110a0e060408010603050709110c25030203010608030304021f140a1b141614040c03140c0a1719110f0c01021209010b030a060e1c2111 60
    0x4620140a0242a00c01003600c68106490141110b80001c000e40d07610f074100710f69a0389480c441c50001030300f0004030400c005c010301c1c162540c10052030300924003040081e14a20381e03500c120b034900320200d51050002000d0395090013a01e0041403c44041e5070341e82018014440d80b0540030f81e0b0308031b00c0b4040e1041040002e0380007100c0c07140200049070744ea481c0c11504400310380030110390000000501881c01c4001c20321450901d2218110298811118070f0341424a00210b0010b00e481511901002c04140c00602c0c00c05030021084462180ba000900d034044041b410710f189001d595000b041103010070b10072501508642600300307a401c1b81e6569459440c1180d11807520442040c1d901c89007a4440f44035071264248181650342e948503c8501c180c1b580d005443c524000e41000020b04501410303440807540c1c144c1e041c810351a826501070080e02c2ca0800c1500e42c1ea015140d640b0b05000284680c0000c2c00c03e01c070240c0c190819a00c40c95642d103110000324042c2d0a00c8001c0103450b100d041e803420341304005d01d008041c1 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 945733453 1250 945732203 945732217
    0x9060d0b0703140906061315050405041b081606021504202218020f0904150903080108010b010e01080109240308030f0f06030a02040207051603210311 66
    0x804280c41c0d46002040307000d40722841084a03002d03100c0c020f1104030035010034054402c41c402c1d903015241342001803019080d2259000816403561100d103062041d82003d8200f2a07200c0c4c082e030044440d844504507080c2002d001540811261303000b80020fa094100342d145070388000d200c00d100030f007400c000e50201d000b610755004d03000070414070300b2094a40244207008407240701044000c0180d840c0c185080c4048001d09a103410408020303140c0030388006001c003405046416203801510a0756031144000900149100151060316103000001c811070048005004a40400b0b10079a203408840d4503100c1d1385805c0d258181580307030510180140520550f64814000c07030458400c4c20011801042c04141c404650041000b46c1c084100040307004001c0c414100003c6008a03111401e82e44581e0fa00401500360b0201036500560581200c0401030143c038050b009019114010020388001e841d0f21145c0500d844101d80c0101c5082420b50681032003a414610001e4201c1c1c0581028045402e044160b85001e1042503 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 945734703 1250 945733453 945733463
    0xf010e01060c030c0b36252c07050c0c010806190b19050f0423130506151c15260106210b0c0c0a060e010b09060d 50
    0x1c103090003414810320800704000d8020803a500241464a19031084003949201d0618106c14a030a4290740440f83e0340f601c1240490102802501c9580092054084800070b1908501c0340e00741c00c08202000543e88481030040c0c042200140c01040001e05d80c07402c60000d02450500200b4402c800c86d080002c600541195401d180c13041c01560f420b4002408400720700d0f2080b190011b004030210328100084000d041d907032080d194168041d80c0c0001e0454551081c6815146002c0c03062000f0090b00780d01c000b008850702c0c2038110038080c0348030300d0002c1040c81895890400e0f2080c0c0b24014007550b424000c10394441540140416840c11325400c400d1580006020310802e4040d59524810710403a440191030405001e9160700b0f2081000145106110407130144090300f0203500c0c040700040c40100442e0000c0c000c22103100c1c19908601301e1f0f210004c0c24035000304184641202000170007244e000c2031085420043c425100082c0c0c0145008129003107542c007000c014000c0c0060b8041c0240c6659142e900c0b40703001d82c02 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 945735953 1250 945734703 945734717
    0x603110108180f0102120612070e07050405040903180801020a0c0b1008030304120e10120f0914030a120504021f1e090e060306010e070513050a0b120f010e0106 70
    0x22041c01c01042541521214443c041e0b000010070181041d00240141054a140d085490312000c00308007c14031000070800341a40200c60070080300c000043d01c564422900c3c105941490f5865010074155146802e04800040034840e50032200c00544c403000d0003030410704c4001c41c200241e900e80a4102c40c0401c00240c072403400f41e80006c00075000403c000d0090090142526101c0c1058a08000c0d00e1182e0381c0d504020549a004c8a55582001615038079441c901e9603804018042c011082c4000301441d1910309842515006041c000c141d191455250500161009603035841003001c00905d030a0344a51400710701c034140750034040903036a6103496402c0074403900115200c000103030030117445031954646107805040183d1a20345c02550130001400840b50780011514441e6206001c15840d14000d008041c500041040841e0210384560040c2c00944190000004a0364640b4001810014540d020f08140d10340080c1040600303070000c140e83e40209521214040310350510f00320301c9501105019074004c001203 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 945737203 1250 945735953 945735961
    0x30c0f0516140106030309150e0f060703181518030c05040203060109030c03060c0e0111060a0b01020304050d06050603210f07020604091d06070e09010e130b0907180603110108 77
    0x2421888a554802c4030008005165030303841c0c00b42084e00180b05200d0050380d0b00e20154038031809001c07801c5190304028503000c4000c10070300812031746801030760060301080b141c102ca03a4551042603111501801ca0340c0048052030014040043c2100c401000c2c6013242500182c5c2000011460340c03151064a004480168407a075404004070344180c5507030b00250031030103061000418001c440e40140107d02d0581ea400952a406100540f449845604d070000507502000006540c2c080e60303400092040c4051058924044c2c2e41d5001455a101454080d48d1283e610018064103143c200680001d110004501c01d052294122581244d07008483c24038070f109000080d0070003195115012640a400380000070001e124041048100c08110411102442c0c480d2801080f24240107108001d86484010910302d490707824401001c020300c2c4007800c504507980c01c0d51040c000184008407003501c1480658000c1050502c2c20003030b1a030240000b4101c07965107180100a00c081f448011143c1100d010a081c5910b103515 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 945738453 1250 945737203 945737213
    0x225030201082a3001030b041202010b031002030a0e06041a0a090819120509030d090503091f080c03190e0a0b2a0a0c020d03022a01030c0f0516 63
    0x1041c2c040c044100880050078081c45400440801309986455200c46940c0f1a8040c0100c0d00c00c1d002c2c0809001c200c50040001c1c00030300c0551120002c40c03124400030401d002140042032924100d802e180007036503004020810161058800d4030341d100d19001c0200b2403801c080d00c640b080880c6804500c15004d1003c0b0006460160a0f0400c1c10070546c00404d00342c0d20381d820f20803010840143c600340b02c0024494028003481140380c0c0205400313103042d10040e501d42845241c210313000b0071899808444500003400241480d98500b800e4103484000e40c40801d0020f01c9840000f8005000100786204021040c4244404201d9400110101d000d45040c0040c40749212058549088000d0070010310305520fa5003001000d400c01006040d00400500d85d152198050340c0c4504854001d195442c0c000900c20000000540b60805010300050301a00583c2c2115036086a4100c007105e89100040c550f00076482c4410076540d0510841014806c103160030514403007401d80091035031166011680814107140f0180d41444 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 945739703 1250 945738453 945738511
    0x10b010e01081e010b180316090e15010803040e0f09070302011b0c18110c030703081e0f1801050402220e03040807050406060507050c0d080f0a022503020108 69
    0x100d08483c0d000c91540e981e9034480403d40c031000c014902d8042e1070024007818180010012002030b003000385034104905041d400300052080e0801c0d0300c0c251142c401c2d5014500c100811480c040d04026014503a80d50920a080400d641e001e00740e81e11185000342001403070300d0081140c0060301d0382403a2140d003442c5002d1220070585800b00c030182000e2001000020395142c442c80e5410550720a034000c1c8001444246015024000da45030300140390403c018010009229a01d541c1e0710104007444c0000c3c800e891940e40c152117100311010b1800c40405402e20280d03078120210000007207440b034000d03c994509903000c00c00050f0b00000d071b170540c010b0300d403160600011715401ca88102100617040381d840c1d5a0702d04142d903907400c0d01d102e1079014619008000c50294030460490303016940000061011410090a000c1c26005500e02600c200c4070902103440c40080d00c00003080c183e440369004000c0c50084120050301c413581442c42100361001441c003000180d800441c07142d407050301102003112203811050ba80ac260 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 945740953 1250 945739703 945739741
    0xa05071b0b120f0601020313091515050304020103050c27130207050105152d0619031d01020a0c0818030106150f140711030709050c040e09010b010e0108 67
    0xe00480c81404402c60100220300c200682e9219004070340f240310042ea10f903c544500400388800072a82482103100c01c1e0040f040055040c1300c2010300b641e0b02c8114070084258903005e0303800100000107000c00d56a060041030b42100340702c000a440c2407105c280000d84582c000c403094011899880a0031744555070400715010000d030001d01503507180d40038a4440c0c0242000c5070103861040c052010340342c15007010307c014514403081d0b5505030074003946040b8003521504031412140e403006040113050081d0100c030b03c442d2581081e030348002c03505509108580d0b5070941190302c205056803060044548640e0300c00d0560078120740050049a4880c042118a41001c21440c40950036608002000032180c11140182a000099649001c2d0510410200300d030094440c2c050004003800500c000000300b56151304080780020b0040843d000c0c01d540d030b0810307002c0d94800c6031f01880c0c001380070908008103654000794640c000170480c001c2160120300c80c0080c0c9250b90004080b0304124195000a880f0154071102601d8 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 945742203 1250 945740953 945740969
    0x6080403030b0a080c03070e130201140405041506110d1409010302040b3007020d0806041d0c1908250e0a1a420316030c050a05071b 58
    0x3c460b25542403541d81c044081c401c502a2140490005e080d84000549030b00034111a20f443c0c4c0c0000013030b0011035030020402c0601d01404001c000004095a0314418a0034410741b4250f0405441e15054000d0143c0710444c240c50a203422500d4859442580007401d1094030b0317541d00d8400e84500c082c00040b070003405180c200e2010b13080c0028500040c11007125046038640705050b00314107404038900b4500795010082e1400f40160344030344000c11034a40118a425481320340544005111065410401801c0d000e9289000c0c0541044a4a03013860500c0441c081c101c5010b0342c0c400c0c03c8a440c2911080c0d40d2005c0c0e81d0a000ea0070429101200c082c1d5400d04404020201411a2203040c140304214000911304001180c0750030680b40b880240505004590150340410540800004826900a509403c4030780c00124401c00315001c0882459000a000d0f500540c0400d01018031a0010407014040742d021a071a501400390510440b50250381c07100c01c5500d40c3d0751101c00d0540340762441c892041450402e801c030340c2c0 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 945743453 1250 945742203 945742219
    0x1b1207030e12130f0605070c18020d090f05101401050906120a080306090109050103020f04420f05060406050705010f050f0406321302090702060a0b09070906080403030b 74
    0x401644103c500c000303485000c0050014907030b650509845500c01e0041c028804d008401c0e0411101155003014076114400040140c036144002441804941c070020b8110f80110b6490a241d05205040002810303a20285108002250811003003002e40d03141446598403a51110000504075120486421426103e5804403020000760f4500307a88250400c44809024084500000600d89414005d103070481e900986200c40003800242444080c0c90641c01c92580031288808080040c501c00d6481c0424480c007841c20785240341c1100350405c14601700e5200394411009000c0911850341c0781011102102c0c00c03801c000f0b9440c151361600c2e078090714002c1381540c08246440100001802c000095520891154000300400b41101000c000c030301c0280c48103509000c0700c0710480b55503c02d4150501c1e0304901c40d0240c4070b00300001c2c0e0780044d00700e0b01c04850000042e00303c00c043c01920200350180340c60480d011520344289203081c40300248101e0a42c41440c0c100b1020308040360501d40203602c008440003010740018 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 945744703 1250 945743453 945743467
    0x80f090a2307061d01031401060c0f0203060c040303170601020718110313060b010215010501051602040203070c2607020607112e02010213090914060a051b1207030e12 73
    0x36084c410740c50100c010138051200c03a03184541c07082c8211146c81e00310301e10007001a420070700120b65540490104980310b40760110b0280240c0c0c0c00700844e51182c43d0251003160b8980c02d5280060030035681416440c0d0744e807000c809110140e81c0204001b8265103060b20740e840010308010141e4094030030440f1284101800000384400504440303500d4040900a031010f003c00030040d401240d803a1141c00302340f031800000000500441d03108100801c105448040701c1c9044c550540c000504a0303005039444804034100c5802002040035501507014401c081e070040d10085104080300800510070f221000348501d00000c0e102040107682c2e510380c2005003000d01850110311605003c2d00010305880c10001d80e280c203403940d00884610500840300455200600c0a44051600b14040d01a01245004803600a42401181841d900c208106445180c01407000f14481c180310304d0040202c0745d007480c1500d90b07100c10000744003940080344c100e079041007180c60000381c40200000303c2814214815080034190000007410 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 945745953 1250 945744703 945744707
    0x10507120309140f0c151b072103021f0e0a050703060f06050a1701091203050f0106170f040501060b1b120c101503060615080f090a230706 61
    0x19154144144802d140741d84241e12140e50f9440780e03001e1002150b1010341c55500c0ba042121884e5541b011700d03400d450900070080030313803c00c5102a0100a10541c4600010050048140180503610640c522030b03402491150320b0080d02c40406280d40355044180b42c51400009266501c450031810860058070074180051138815100c800034401039445509050380715022040fa445044111f9000401044640317262103000704443c0701d11403488140e950b80301c11440125261440d2400000d1030391b5000a4940707000d441420760b810040e00040b0820800d0388e40841546d241d0083d03da00001c1c480181d0415503a01d1406038003603e0a0781202030041c00118810042950f040d4a54000b1109401a5141d004004180040d0780c01001141020396100e801410031000c01e5a001401003401c00c0b2440032610340303d40781e0506550b41a440341300003c079003802c3c10352040c0d401021141c0003018440700b030400307041410000ea6201c2300500e02070f001050301c0500041c200380c407581036401c020b071100075188126612400 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 945747203 1250 945745953 945745961
    0xb0f07110a0612050604230a09120f030e07030213050a1e0b010905030604020d02091005040515030d210c020a0b0702031b0d080f070c061109040b010305090a020f0105071203 76
    0x152551044c185000700e101454039005090701c018081140c031446000aa008610088000d000b00c101290355103045070102e10708030208600700665440e0b02012902c0d099000b000c850000c15a8a8240c00c0b0340d0f001d100507a204503040c2c0960b512505e01040c540c0300e51120360018074040d00c4ad01158001c0300c1c0700c000c18040315009405001426221165850350340c01c10705450b1482114003c1d400407190401c40c005180071a00d0301c0c0c10207102480401c900f912403020404039070f81541c0b10302010250b5aa14060752808101641668200c0e02d084c0060005022a8080c980c1c0008940200c55483d4001c40440d28800c0008400d480c4d0048010301c000d04003090083e481380c0c854094500b20380550f80c0000d00300d550000e0021011051030352050429502d9800e0241d00000107442e103003c0082c50100c0e80081807442c021005c983c040c2455a40c0d40b00c200c04100000c6400d401c1600d814181820208413030400e01003070354036199405880351013a03810840f004aa251060f2100140050b0707040600050059041e40 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 945748453 1250 945747203 945747227
    0x3060a0b011805091602030c07060903021302181302090406030f020307081b0f010e060d06090e0d020714010215040812060f09130206040803070605060a050103060b0f07110a06 77
    0x2504144042070030b00d001001c00c0a4012181c000d203210b0080340f24840e900d0301140400c14140f06603070801345201e00f003d050094aa2043c0c002419010042c01585060440c00140800080c0110b2800650600303410700b0341501120140f0810146000d0408003d840c1c04503004050000c104100194030ba01c0c2c1240700415558040e40248654800031a1144000840f8032400700514843c003004043d410401c015206480101410003514541c24203c980782c1c0c1d4050b0008441114000c01c005040c0300085084500200484084d1340c81003041010280d00420200203482e081c907410380f0700803c184010303442c20959034941d074641c40031001040706120a0038003038007000788a03c6440da2107032500000c011039a5070250906034090324030000b0491682c015990060207510181410382401e5603200d941d419504810310541c1c120392514200181440c024092001904090a0400c01c181c201030001055001e0b20051240030f1000003442424003c208da4201d00381c1c40d00400c000380b12034568000400041038a2 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 945749703 1250 945748453 945748457
    0x70c02010323090f060103020d0f020409060e060414070513021806160507050402030f0c07060e031309060506070b160c290f092805011d070b0f030c03060f03060a0b01 73
    0xb6402c2d680d01100031545c0350480350000c0c1590b42c3d0158640b504c400303240e20403904903400b07607070f481140300007c01c14019011014001d00c0070f403901c2d20b45400c1804030404035906d00034058000103000d0210b6580d84245000646810b42d0041c0c841c008941405110049200081d81c0400c002c00c160358400d0303031035034203140b66441031041e201d1391f036a2030007400705900050302c603000345541ea503001590b540c0142024004c028051480428205000788520b415644030007800034010001440a0103582c000380a07520040c00244c800f5440e2001e5034441d41900c40015084081c00006868800e000074410140d0b02d00301504107031880400548843c2c107a01511034140300d5a00710030101c0c00115038012a0300c0c43c601c91445100a4002145400c8046c0e0403080004040720360741f46504101d00215009118050b1302100c103841d080e24030451548100d1400c01d0300d81c00442100003c10070b031800300413002e044d20b40148081101c581c6039111080001c0a20030041604c0e60984999002c001040030340e81c0100392500020303 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 945750953 1250 945749703 945749713
    0xe04020a060302031005060f070f08190203070f0602070f1a220f03050c1f05090f0a08250506040308010f0501030612112706010323070c0201032309 65
    0x20300e010b40903030200f02c03203120302124803407410001410b014000700104040c014995181003616500c070400080e0050302038030007180104a2400c0d5104100341540320700d40500007141422190341d0f90a03801d6030b00703000040c5a0764010800201b00b00a01e082503440766440385522025003402016030310545403c0300c00158041d01030f07400b40010324175010035289194210b81c0200300090203403000c1c0d03141d81c4445880c010b588200c6280020700d040b200d4051000d074948800200369400d0a440d8076251501d040241520f0350040b101c04000954000700300c620100288054880c064003040c4280c01a4a034420007408a014903400c00040680c000030b0141130303c6a038068000201d440d034004500704c900d140150b01d14800c0002401d404110800d401d0312018100404000c002994035680190b90b0303424000c146007002000e0f00b40543d075a0103000316980c41e000d10b07043e0a841c100c0500b6180c030028024141d0024080e006801001b50b92003604424440101c080036003489003041107185c80140d80841c0e44099600072 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 945752203 1250 945750953 945750959
    0x60906040e031207090909030207050a06090b160c0e040b060915030d08090309102c06070311120412020f0603010608072106060e0111010605090a11090301060e04020a 73
    0x60300c5050040d6040d00019418016201030f4039014040103000502807051101d00021600308901800e0b050754400e6001d424000d00c2c1a05214400c0d000e508114140143c00d58140f1504000109440078800e44c50b80e40510b00540e418105200070440c2c10461290a5180c10407081c003001840080c05800161030000c0155070345c01c80c29a4001c280d4020a505070080224095100e1140341c0341d94000031160141d034505815580010010003a03041d45002250603c8880c102e1002c3e403090024607207441040c000c190505940c0000c140d4414000001c042c0328480e01a8031640c44104076080c0140601c0040c00d42e155242c40d480e040044480030102e11502c001b284521450600106a90484403e51a03442094032070303003000d0f6044001710081041c500c0c04c14804000746036080c082e400080805031101110000c100000402c0c554014402c400603a0403d04100b02c540c803217a00c07595001c900918001040807249003c820980304a1040950543c204800425a03000c88881180606e1003120301c15050b5039 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 945753453 1250 945752203 945752209
    0x40f0309080a2108150d060b030a0f0c0603090812130614160c020a090c050c07030b1005030c0108160e151207020f07060c0c1d01080f0703021c14030a0305060906 71
    0x80103d80b031004281e0184000116414041c0c01b00700014032074200803615482c0c07000480d1500d4624001915803030030b10071000382844540140308014090a24080c0044600d68aa40c2c110344100003426801a0481000540070443c00c2c0c10342d8a155071000d8240b02c4100d80711008a1981825134810012215404112403154001e40030304040741da000d0304041d0704614164040008085001d0700c5001c1c01307420040c2460b1180c092044202540c490741c103112650904082403c060398254001a000c2d0b881080070002503a080542540c0c0140d03c0601d404003c0a0b840d002ca5102e0b1844080d41d4110440004103200220402c0c00340551004651041c040b40e51686800c0340c0d41c0709183c1501c41240c014000a000c03c0b8411041c0c020443d0103450416460741c2d9070000c4801d007104240e0390b0113040107880c00512101e113090042075907014111004018081c11600003a240d1881e01c0f5407848402107606103001013040c03001030504c030340b10f031002641d440351204000540036140c1190039034400c5e0440d50024070186 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 945754703 1250 945753453 945753467
    0x3131506180515061207080105090c07410d0302070b04080c011d1b01140a03150824090a0b042405100806010e010806040f0309080a21 59
    0x2411824501010055800c080070040c0805045000b80d010701e022184050b07200c2d48004d20400203060140c880c0c034505200010500c01c41a0082441402c4034024000503c422609960360305401110071000303c98001a0003113600c040707001c00e10498819603001031228059040c4800413039070210546614907030103501241244204000242006101000b080c003241d00e08020301100010302c0000203d8a00b86825440b50203c4102c2910081c3e2240c4154017910032100300b10007100c03000b17003041070003e600611480110300504001f003042580d11208134100c03481d0552100c0090480d0350030740d00313401001c58000128100040e04215940c41500c04100340140010300004802d03048440601c4603102c0d03984041d050101d13001080c1e03ca10010801c0d444036181441002c0c0901106e1103600d800c2d9150135025410100141d00440408506a0040150060109520b6030040d4003c0451400c910f007072401b5607980d0703800e8120014910580301854104220300810220000b00c42c0f022507180380741900116055 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 945755953 1250 945754703 945754709
    0x105040201050417030f030f04021c0b011517090c09100b041a210612061303080402030703051b040e0a0210030509010e100504030e03061302131103131506 68
    0x1c02c100001c00c2403403103000d10340300c41007508800c3d2031030700e40c030104200d25075042034540818070035940050004625000c1c01810700c3c110400901c00128916840d47c42e0420340508c141c801d000c400703c0500c080c20303210302c0c50041005400c00c42c3d81307514200f0020140d0703990100300309280910104801b00300c401c00da030492241105c60114000703141c6410040c1d00c0112251a40f8007400250060241d201607030783d01c0c808000c5401c2c0411414925207003d000b045000004502600714a4002c0c1e02802580c08200300d110f007007580c250412070419100e070300c0030914046650f0f102a045000e81490180c40a150308a24100c011080710180058203220010b10b468841d6400c0c020761050015a0619080e4003d800055104061000001e0703003000c02c040c00781c10040201403034251140d460080108042d0004242841104258000c2c12180760850b40300d5014080c4000103480352820041e44041040b580d0400100c860010240c41e881e403c10240c80382e98040c04a404403070028100340c022283c5507480c80395100b2 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 945757203 1250 945755953 945755957
    0x12070e060d051b0103020c030714060c0717090316080c1f0806040902010e100c060f060f0605131a030417090d0213060503060429060114090103091707060e0105040201 73
    0x90070f88041010550418000f256414140c090080d86c80c1002d080c0041d24405000c1d140903842080e000c1e030b8180c1401c07001448d0420801040c800c01c0301161045020980b0000b0740c89031556500c1080c400a881c000360010300c103c03401000c0002050302c0c50041400000d007030003661491a0051200444040c1c0c016803054600001e00c00c0000035201d14040d0060039116006041c0a01c1040d0f40f1008507181c0341a04030014089581c1d0010041000558840e00d040e41c3c00d03803c0c04000e01801e0040b4138222107490311a20007003120104d881003400c50038810341c6008020b029490321100d10501040a0241c01c101d80075200351140410090401a00000301c81c0e51410080c00c0c05000c1d04241d0801440030030311031034401000e980311804242da072420004280128040c240700032210b2804001a210100c04100102c400100c0000303112040e40c100d6441c3c420321540b8881c070341d01d030004c40c1c0048000306446000a45080c0001d101810204091402800340d20f0081c5000e00c4902c5002c901542660415100240 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 945758453 1250 945757203 945757213
    0x1c0c170f062d01080a150b13260d030626070305070608180111070b060d020901030303050a061a030c0a210209010f080613150512070e060d05 62
    0x5002051856565010100520341101540050201102c00c034091409410108895001d9041d940e084449154003074842e03002441140380c41050072024a00c10311480400402c08035420510303c800007102c0014140d524200c40c040341d881b02d01c0083d854180c208400460165560702d80034184627010f8201070700d091a83e0140514500007a5030381c11003001072040180e0180110100c0011024050079006003016076440d05c035401c1c00760072018038182c042c2e0000c1940e850840c60f84860f48200054494198001e040d4082603544c0c0f8011030540a0942c80c000d40c40981c0000200c101501b50380214000d2107050020400103407500780e8016a011240d0905500c01820720021748011b00100c000c04e80c070861468580c2c2c46001c011510002d4101d00316500d0000da0300860004030300d503406038003a92035440314600454203082200100f01c1c0031000a81803100c040d101d610390348008a0040d103540041c03002522203c40e0403d0301e4a80364035001d00d0702802280b48284d9020840502d006002c5403081d0303030031001a00e = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 945759703 1250 945758453 945758461
    0x20f0f07092a121413110a03200109120f0c1e0e13140c010206070314130501150603050f070804050d03022b05070306050a15030e01111c0c17 62
    0x90b958032103580d0384101c030544070f8200c4c0c03407440360095260380601c0e802043c940c02103855203810185500703414117250040c1c1d0041410000f00e00a0041e0882416003480304c4180450300c140100c5858403583c0100c0c04418000c4021020414a000305a440d06d000e080010029912241510b120086581c48080340c83c021035000d00940d59148101c0e60006220119041e584042d551044001c00b5a01e80d100f08581014030f40700001d58051141640c03000103072038100595030012400004001c000340c0024880080c0c90001010440d0940c0004008828440b03515401551004014045d04088a41d40c014410500100e110b09009149060156034004080c041c840d0360008120001d40240c0114505012014a040140303078080200b40c428140b000303004a20761500d568041c00341e41d01980030f5801000795800070032840c80c0c0189003083c440c03150300c4c000ca014004440c02c1400762110b000280d41c12440090b0311220742a6546c100c09400104032414002d01c5441d450a803440500340c1081280000924005 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 945760953 1250 945759703 945759707
    0x105100203040b09190e0a0b09071b14031803010f02030403080426041502010513050303060d06021c061a090a0b0a03020c150901060f0503030f0a020f0f07092a 70
    0x34007030801c005045000c00e04200b1210b0070245c0c8080d80303d500b45550b80c0e0b00740b00600441e4040ca420110041e82c21066a0400501c02003403100c210040c000c59a441014820420a40e0310060341c000103072208903a161000c032551400008000b00d01c4911a619140c000c20310101c1d10300984c2d2040340c140c0c442808550703da4556007075000e40c6180701000426100e0000c11903940500c0030300050a50260740034140c2071810070181c211100a40440c0000c1d0309040070400158000045a500c48000e8640800b03109940c03910101078080c2c02e605141c080c420200c501841c1c01d186c1c1c4180d084030011440483c10b80c2040b08031610a116600c0d955400500e180c40500008500a009240342c0304689801480c00b940850218148a203400b0a603400c4000481403202034002406214090300044026840581c90b2100080d9203200700e840a00030341d80d0102d0800c103840c1c002e00c500000f20740711740141c9008509080380f03540c45654501400c80d98a15000303048215403c503200d804010f4580b5280104018050742d01 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 945762203 1250 945760953 945760957
    0x8060303192127080d0c0518220b01020a020405090c010810060e0607152c070b03131b03081c05391c0b10090303030c120504050c01080105100203040b 66
    0x2a2240502040400340c1712580d0b1040d10b6034a40d10b556100e03140c0c8592a0044003582036481d2036880f031500f04c40c2c06030912510500b030203034007910000c0000f1610400340041c3d042c10319020010303601500d45400c04c12049408500407607011800d0b660080d25545001c4446d088000038001c0d0000038481d684044907d0804c17400922215005901951340c10146a0900054612030ba2029428400d20400c0419102c590070300d400881441c000079000941c200222103e030b07400001c11a5000e8280c0d070100c3c005100481481106185500d0380301340e6081e0320f078140a21690700580050740507a450041b082c010090300d100b004d0180c40e201c0200840350198000c2c10708012403a442160401d0354900c540c03800143c00100500100641128501600384d0040080d0111116120b03441d0140d40b004003010405941702c4224015030350300d401c0000301409074000c2100e4442d4100c505e440124900411320052080c002400d0841401c261ba829146030303200c100740f04811050036014405648148014800c1c1420700300 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 945763453 1250 945762203 945762281
    0x30604050c12070c0f0803010b07020a050a05030309040f110f0a02070801090209010302041d031303030813111516140105060a15050919090c170610080603031921 71
    0x20403c4170100300340d01c49160350f9200f80c0c0305892241000400b0802c5040c01c03c942c4005250840e02e190780c1a180c58046501d0b840703440d2010748140d03518040075045600d0303580080842c000b04c1216585542d071400d0090704075804203180101611a203440000d10020501941c00c0c2c0300e5002e001c0100c1a481d40e800c0c44050050325800c109207100c0d946d5250b04608003000a03000d00b0b800d07501e0b0ac0040500e5418090f0400c8409000d4001840c801060300012a0f0f1038114100b00c0032054450705403450164104080c1c0d0300805480c60003c0c10200c482c030043c0700905510b030f4100480b55000f0030280d26401b082080c2401144a00319000c450301c09a10030040c06240074021800740a842400c500c004140e2010102403150800482d01c1d6030390141a4845900246c100c08010340d81018169034140200019055004070100001300001400010f519440030301c1982c1c02085031504007614403000117070180010304c0304241850000c1030360b40c1c075000c0a0240d004040c0034410b0150318400c070911035038020000d000c49170 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 945764703 1250 945763453 945763463
    0x1003020a0e07030e0a030f110105102601020412060f050601021c090803040f06020f0f0a0f150e010b040507030c0c0209060f03160501031b020c0904060b030d0203030604050c12070c 79
    0x5807414601c65040c0a017000e421710036030704c6207540100494003400b105141812080e09070b00d40310410105052210307081e0140d584208401051070160b12581c15002c2a5440222003540081800690f045441d00300b0b500b82c40c8a214184800000885d9071022103004507100e81c0183e20450140d0280208401c095007000040e24107120019142ca804624682c0b15500c1840350315006c000030880c1b1541030089400384a413200160048560206000e0398a0b80d00348809030040d003600030380f20300700148407604070405081d0440c14801c615400024074002c1c030360340c51454001d90900f000500da041c400d02c64480e584006403940c624901c40c0d0307006c3c0111030400500f15904240c0d250b0314468203645c20445402c1071010f4144141c50301c0d04042c0010103844540e42c40f5a000040040780c8403c064010904500b50700d07081d5071030005603a46040503009040c008007090b030540a11200300702400d5012009510404c0117880501c500d4451404502251280380c030b08403484030381c000100e81400d210f84040c04070b582c043c2d = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 945765953 1250 945764703 945764711
    0x20306220f1d060f04050a03050f04050909030706060b13030609050c060c1006080724120c05040501181217071e030221030c09130e0607081003020a0e0703 68
    0xc1100708080b80e00340c07500d03500c08548107011898010710402c5860760200d40b20030703440703003504080c1d54803a507a01c4075480c001c05110340032941e48054001c01c800e607002444000d0aa0419061510b00079460b60700c031145c01c3c0c0d031403810400c2c0429803240c0303001201c0d030100c0c1440020445524544640d0700070603441e4001c4032175004d4001454965501c04003d000c1440c010000340401c86040c1e0103410444420307600c8459036030131000782000900c4910900742820b1034400500f0104015901088511981c81d55000319118504030064041540c80300141040c1d60003030700c444800314181c81580e440c2d1130051141c150102000000840010084513070005007428060325181083c84558410408406022540704581c8801d8203500c2070645c10011444030300400e03440032039240c6460481c1030303191100416155440c04000307502612601c0f0304812000e040c88205040044080c031030101900c40d074007600c61000180c01d0001145250069001e6a02181d900030300030f0240e107107031480c001a40c4600801010038142d41f = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 945767203 1250 945765953 945765971
    0x5060c0111070c0807060c030503040201031d0a0501022203170c0a0b0f15010e0901030b09030906030a020a030501050a0806070c02040612030309060f180f020d1209050f0402030622 79
    0x40c10301a10b40207105411000d1007504080d0140e244c10440d912000801c0b1350f210100010a0f0000c007203a412540a11b004204070005a5010051a8900d0800189803060309511400c1c08010b501a01c59444402c00003a500d00c509014140c4001c600d000180c0414005050340250000306d40041100c140701c08196203440700c00742c4441d00d120504403000740c80f02c00550b040042900c19a44040002c0b20309090882d034509041d004078401000c1400b0041c10417078480003054801c14100151001000020070301c564a140c20038443c4040e400c0000340380d0210341008000b0540d868051804820340344400c0041440d43e0783e0213412540503d424509a0f0060703035900e0081289280c2900d082075031806501c001c502c544036450302c801110b05096010413881c1c03602510003032032038105c20320042507074001d06a6001802e8034000600d00c0d0018080c000c0000d1030b140c0c044461181c0201100080322022074201c0d1504450905010580c40b08541203035100b00d0154080549040b440400340b00f001b1404070004695803 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 945768453 1250 945767203 945767231
    0xe15060a030603060501270c0504080a14070614030708100b04060302031608150d05100213080616050316030b0915120a171c3e0405060c01 61
    0x211040c06000002c0e11a0800d10500c00540141030045c804800850141c2c3c18200ea003213160f1034040c101100e00307500c0f0720b0454005403240040c0d40180c001007040c6c42d8041042d2400c051034110b450348081090144c1240052824040c3c1099000105469005840e550740c0b034000f25028000141844000210400003141d60854031001d8405000360341c0b00142e032401e100100c4050040c00c403103254100417050302003149680442c3d42400280c041614007484054403403601ca414080150000009a0b01c04034510306a200000c0221003281c5810090b10916124510160070384074241c03d0900100342c00f0404120301410350b0501c405825500d24000540081c91000074055603000d6440c6800484125140881c0340303446200521400c0400e0010041c400082d55218446031043ca1040d4080c10081405420800d100c80000620040d01200304800b84030080000440c04070b107442c4c51105940d40c40707050030392002c44100581e1481008030300750405207454100111948003015482195480e40351043e0b41d94 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 945769703 1250 945768453 945768457
    0xc0803030717062215030803040f03090b0901020c0f03100518010621021c0b01080307060e010b0117100812030108011103040b043003050a05060a0f0e1506 68
    0x4a50340e2005003005815500d5600e00000c1c107040d00c203880a210444802a0740d0105001160b1030700c81c0401c09017110021000b18a16560020f415101d000042100f00275404140c80449482030f2240d00c041501c51b00c0b888441c1c010b0185460250744510792202851500522081c028980101107541d01c0e80c07600c01100a80c5c0c002d42e40c038116494280c0d10700042000c01c1c0640c40c040c1c00800514041225a034000509000d07003001d010f4042e4034060640b0005115a4114030881608503080020ba0f59460003a1a540d070b005000540b50186000724500300c070300c418000c40c5580c4105a550301c082c00e0b07880c840001201c10192154040c0700c00721200041d9000c4c1408040c0c001000703003207455141d600d414102c900f543c080042c94001c84000304100030001c0c045560180d0010742003168130b4402520000d90502d50859140c0014103408429002241c6940c0740e000a44607130702008060105864800501180c00d105014031010302000c240b0502611b605400b14641c00740198904030401e0920501184082d = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 945770953 1250 945769703 945769711
    0x160609090b04020f0c100b01020d02060c0c0f1c0206130809010305070509280501020105071d0a0e1f05060c1b040b1804061a060d0c020c0918010e0606030d05070c080303 74
    0x86c2d04400f030130700030840c1039204511040382c080c0050000e58403214802500c0d00001424501207480220351070030310040401c511402406800c04a82c20490351040d13040c1003606a0042100500c04d510000f600c9030b1080e001000082e40c020026400c0036094001900500340c020141c60820406120551096544601481c5c0350030b01002115504206400c4210000d009038001c581517a042078284880c80780d2211161040b0081040c140d003000e400c09000401c0c4205036800a00750f40321070020320540038100210310707900d2000c0e0074000f2084c41d42c0390203000c1107010780090340b1081e03045030748032905038600300301c044140c95002000000c800030340a0000341c80c00c0640c0c5550a110904000b04810401d051043d512524a00b1201302c119200040001d4614030410160300c02042d103443c80444001c0c020040c680781d442e0028240780750340c60485103001d0051000180c3d48819800c01e001032500c80000700f2568000c0c1740c0039001d4008920004026565540700003411078600100010006611400f40065030107 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 945772203 1250 945770953 945770977
    0x90f010612122a0311030a090320210f010c020304050f0103090812271b0d050709050a0609110306060702031c180603151716080f160609090b04020f 65
    0x80d40c0700d1420020074207035000e1244c2c149581b0400000c81829000b640c44c20881303520040c40400a00345420780066004502a2560428120350413018400220441a95040c40100840e06015401e050341402c9e59200d02c0c915025800401c014040d41c00d080300c5644d4681e6041c140481d5a41c0325075a031000c10340c40310805240500240003405044c2c0b04484091441c480820340c51011081a80d07242510750585141c50301c0d000003642405203007034031000c0d0014105034200c000d0300d0000c2e0346c9044a2024100c2261120540351030041c0c04249a0024420041c1c14201090003900707503521041800310a80c00a10183ea061192420440166480301503025030f02c0b455941c0c50b40e2290200214a04030171a40d0408014141001115a070914010103030300308541701c00007040e040d600101500740c14a9081d400008000414400110f800c400002e802c4600c0c03524017040f541c1aa0f8845032000480c4958041d15000800f50f01e810400d9900ca034002400c100e40c020001031821808944481599110701d180c0da072 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 945773453 1250 945772203 945772277
    0xe0a06020a03150e0112140d0e0123090d020301090b0408091f0c06050601030b0a0803120c1303060c02010b060703031e051603021b0a0308090f01061212 67
    0xa0459454081c0d07411022003100031450440c01c10313150b603820380b90501a900c440c0c80c0706582101809952003503d444040302c0c0d0203543c0d00d10600107000f0440b0f45100308103400304500308000b19030940d00c0f590399407038201d40318281811b2410f020208601c0700700084007a640741d92035642e5540403900d0340406178040d40c03040100a80c3d41d00c20a05000080e8004840a8616001c1e908000703031741604141001c0751103034802d01c0010140c1e0b850340181c0080041c94001c0c0c2d001080c4a00102300808008014030704222085c104860507502c524003d15207108124414040c0a1100760030400079220350407500d440703181030001040a075a10f4003c10402c3d0444982a00000e44400148585080c130400c52380003041120700621441c40c05106900102c00784500c42001c02d58001000742c0440f00c0c4a98413505401d1000640d582842035050090204005a03001c0400c0e009800460360442e07414882d0324104e4200c210480712400d555200c2004450758007407864140721342b441ca04800e544802034904070040c405403000d4 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 945774703 1250 945773453 945773467
    0x8180a030804051e060714070f0b0601140406020a0201021501140d031202032e03110f03071a070b0a0921210f0e160909141009060c0203030f0403030f0e0a0602 70
    0x4003942c001c225240000c5802300a490040740703050540c403181c0b50700310f2030814150302ca4400407a15800142c440c0c5c4507014000c20042003695020a01c03200e0341e8002d03403c4842e1075042c0348503800050000e1243c0d0380840079403041c420b00c0b81040c40c408000341e4000d04149800803150315109040e64811200086106603504000070104002c0c2c006a140801801d002101c403400c1d1703500e501d541180e41030400c2c49507001003502502640c08100031000b62010314107044c0104801400e518207074002e0341086980e5400000029100c0001c1d124100e01d154020010404550358103014000c582000c09000d01040101c000e17410030302c000c03c1003030f0707003681c0a46400148100500ca180001c49618401803521900041102c0e045502c007030300c00301c0648013040b0000561460501d000d5038104260010003a45018181100c103180c213450384114009401400103014511441d5001c076201e00c01150f510790a20106404140840d2290f4407441e8650102500081c20302c0c003c9009901d00b80c403000d0112141a0006400 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 945775953 1250 945774703 945774707
    0x200d110d090c05121518030408070b030106140708030a0203040f140d0201050c12180703120503010305150720070b0d02040f050105031e0403181508180a030804051e0607 74
    0x700b000010200043c1044041c6081d120920340001b802125a154480d80c000c440c065061007110010510601107a521968400c09401547c10912824000c15000c42c3c840700e001030302c01c2c11144d0803588503100360320791381d107159800c4000c1d00060400e81d0545242840e080000744040d00c1104040ca115005180c2103510b03c60003401d542000303020808107402031000805004002203030315085081403880c00c0c0c1950000322a186890600c0d031020303101804840741c105400d03070400300842c10ba0b4082c5040d1010071505282c01c4108040556001000481c071402d40c482d642204601c441e1200c2542c4241d42c030140c0da070510f004050b00529802c4092560001d010001c411010003c1001042c080c2031450451504450701503010140c2c0680d40910500200010101440342c1600c000510000c85031008040d00d0b03100c0080858480080380c0c020411000210380703a1a1076900c00b2040850400003011070884d80d0307900300c0d4810b40181044038507105280844042041d48102e4031036000c0760390001d01d0245048940 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 945777203 1250 945775953 945775969
    0x150909060406050a0303050f1e0715140103140f0304140307080606090601050f04080a03090302010e030a08040b0a20010213151e02100c050c01200d110d090c05 70
    0x40309210310b00c0c0407030402c280d44034561007074101c83d01424a00d844829150140c0600c1c806c1400304000002580c440c00042030207170015003012402007926034011a01d0160450440303500b4154840d114840f1401000050040540301c000d862941c0d0694415004a50455280d60041c0e0090184074500340c01b041c00500701000010300030104c0300005c11483c280200407a000220191020f8100400060301c0118070340c0c2281100c0003003100c80110343c01d500050a0050620b80329000490000d03000400c0c3d011a8940020742c2d8101d40c3c1c03c815000d10746403400364418103e6008400c08018404001a40303942e10f00c0803035014031340c10038850000d40c0d10000c0516031460484240c1040c1c148001082c000c0707050b9980602e20ba80b20400740c02071620805000d440c26031410b192035040712403650810302400d02040c0d200340605030124400009101500c00f98000d1510030280710681d15064105106070300406031941c00c229013840025510a140069107810b030030503194040f00036110002d02c44070130802c0e400c055103 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 945778453 1250 945777203 945777211
    0xc10020d1112070f210221130b0a03060803040906050301060f03241404240b06070b0705120906040c050d02030c0d02060d2a03021303061a150909 64
    0x2d8010a0503296001c11940107204003e04151040000c0c4401c00008290640d00126805c0c01998103010448000355108105030010320070458103e10ba903043c1072103900780c030b19140c48003a082c0d8002e070425000c88515003000c40440b042503101d10000900580601c0104060482411301150450a140605007540c81e030b039100341e00c00c0b90721207402c201180c075180e00c0c0764140d04440110200c40384980541e002070200c001ca07500e400c60b9418140030030049085003010640080c82e0710030f1540c0d010394003d030702110303441d50000350080e00401862000503c07800e40706034004424200541011205251a1100c000440710032a599010030b051100780411041260300400046802000404859021948404c1440c0d825030298456450070011951a041907440031102c00d40c080101c542810002d05088029000c281d0540b03456100f1030170458802e00071030301030300d4080c403403185d90300e2070f60365240014460742e031103022006c04c249801406035540a90058600d0641d09019841e02d2403603003088020b1001078 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 945779703 1250 945778453 945778487
    0x426011d061b04030209070c02030106050a0603020a030c09063c02031803160509090705190e09070f18090503130312030506150d090c0303170703110301090507020c10020d 75
    0xf0104200503a03030544013540c00f040c20310b040010303000380c1e1012a01416054000a5104001000c0450407a6150303000c3c1034003002659041c4505940300105440c0c81d0094095500001e0495116646a00018107012107461031842c0b02102c05403203982d1107800340c008001c03040068100044c4480d503480c560010b22250501180500b01ca28401c4120060f030585c944203039801483d1000000e107040c40d05010000080c9009000181c01d03510380c801c081c140000354007800040c450320101207500080d00280b407030305031174100113036503008d90605414051442905600c4401c45450b04145c000162007030024100d048504030101c0403160841c0380400c9400700c6d0300002c4040520b403604025055803414521403c0c40c1b00e030400f055a500120404c0d5014080810020703160b00705107100042003551181e21002803152a10302c49030b40d900c4404049003940c1921074202460601400140329006542e4481c03030304590a40102eaa4051100700801d84030f0075a41c01d0b440c090f0700700c1d4040581c100d41210160243c02682 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 945780953 1250 945779703 945779707
    0x703020306010c0f020105071b0f0905060906060309071503020a1106090a0602090a051806120a030c110f030a0303050f06030a08120a020909090a0210050426011d061b 73
    0x100c00003040c0f2078049101424294016000c8801e590181c404c5400301504462980f1055491010707440f0780440c00d22a109803000807100000340c100c81031164900a0200030f08000d55500c03180c04100c070b80d420240070849240130b07201000490240c0c280301c0c0084104540c40141e15400c0c031040c054108007252942002642081041144012001c504480c40310f9002c0303001a1030351001030100300300b0490f68001f1a040380d26801c038410102001c183c82d62107a03030129544120301c00803201e2507444603c400c1000300840c900305401c80000c1c8442d49907203018140945a445008901e600084c94004421402ea0104e40d4603018401d020250f000590340c08441a40100140400e13030b81c03150113921a02c100c6645c002c6800002c101c0351031a940459418900c028282031103814289601d0783c403280c034200100d2041c480300400f55a2070740500705035811103000748058040d80e000700480010b41013400d5030b01c0986540c1e880c503000005001c2c40d01c80d06101c0311400100903d00c0c200d14030010542050300001e0502c3c1e41 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 945782203 1250 945780953 945780961
    0x4170a120f2010060305030c010c0306051f140d0903110609030409021308011d01060509010b03010b0c0a0b1609091406100306030206030a050403120911040c0c05012307030203 77
    0xc80c2144045801c100d0300003076401d0b50003407024148000c1c2e4100035501130070300400109110000018052aa58000c0200000c000510080d42217461602c0381035000388000d00c43c52041c007259401c0301c220032403605264034910b000c00d02c200c1040e4401c501c25407a25540703010150506900284940c10300501d00000c0034241407d00d0741580d0ba00480c890070364000c2e0001070150340c10051602c410011310420009101c00f200000c0f280e444456010410507466103052000200752401000b154105e9200d44219450340c2d0030400d1014030b03640008046521840340c0071840700003030343c6907440600c100c450a120311824121200020030b684816071240c5c1e01d07142045001940d1503034008105402c00d208441c0c00301000140c0302e040e005005590303c007952210b00803003002070076a42508050700c110f10075a140c0c10703208080707451003040303603041e02c0e02808140164042000c3d5080c55808282540001d0801030390544d500d0ba0b03801d0a44842454050002d070111907514402510f4000594011589080a44c11458 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 945783453 1250 945782203 945782207
    0xe1903210f0b0a1a2802070602061005180903070c08031b01020f09210601080c010f0314010905130b010f06030c090332030a0f020706021902040f0204170a120f 70
    0x80d480d6011824441c001921466441c1c0040305400340302417402e10101d5040000780040e440301c1192003460f02501900300020071a081e80c607800e0080c0c0f00001c2c04c1d2000041044c200805180e0000c1c040d6003a84070800c07001c40030400c2030010000408408005503030707401203008036401c013072000d00c1013008982c0103100c04908606d040c4140d4540440580d0404950045150001c4111996122080d004d000ea90004101502c011529013403050302030725800105000c5680403000ca030256541403d80d4a03202c0010321a41c0d140390451900000b40a000034580350003621010000042079100041d48980c1c100300308603c6815014910040885052907a1020b03e0f503200c640b0f0981c042c240b029980726109800044900425500700314011101c42126107940c244140941082e44081c054800341c400c140340002d89620020b282d49624281c00c9105100c1d4201d6803d0001915041003840902c1d0780a10020030b41c5038054552484017080b602c002c2c0828101404c10006681c00b4400103010021003018081d0525 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 945784703 1250 945783453 945783479
    0x1b010b12070e010312030204031514010605030628090f051b0708070620030a0e150910020313050336060f0309160f05040501090e1903210f0b0a 63
    0x40e40002410680945c4032100710024851a0002042c06010003007600302000641e002000701c4080a00e0250b1598840000ba0754a000488041d079001048030120f14040184000300d400610090161007030807604c1d10024826501c040c0c0e0700921040c0c0d0780b001c104504d28410f501784000607010344550300e000780d01d840b20f0b101440b0f841005026144c86004071640d0303207802c0c5140300e440c0300600100b98603400c10000303900c05002d4803101c0c0c41e00d03841005600702c10301034800202801404200001c2442d1040304440401030b40008010110445001190b58085132041c8001d007101c1000c4c0500759804800f42d802d0441621030a040150602d00412440d41141c070303000115298003143d00c07503241d100d5031500d850a05c4c107440f980440b130062002e590300143d18000040c01500340e03041220241b0003a0b03202c10b5600121104020301c488550b0001c08000309211840d00300710000c80c000d00d0503084070f116140c040a03c109101d941e468a056840201c4090794030a4404c81d642c0280c115080790801c0d1510b07141c0c0e41c0c10 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 945785953 1250 945784703 945784709
    0x14011d10240e1c060c0e010815060408010606030501060816020a02011b060606050309011a0a120c0e09030304060c1d13090b0112060b01020a031b081b010b12070e01 72
    0x32000c0124121210b00904080201e100c000b4019404000c0b4429000c1c02c07101d95a800f1181181094100d07030b60b080c018000c104110f90180c0d41d1800f00c0e0340302280c01921100b0301c031103a1b400040801000c9201403080c000d91001d008517850201d010751510b04010002c01c0014442d06110318110404410594086003020040d502407a100010398254400c1680d00706404100400241c9005400079404e07410030007540c032030040f035002000755406504424a2160300c1d101031a5100c0340401c824840b41c035958030b11b04101d502981040f00c031503031644100c04810f9400d44510b4040e03032010040004009890148407814041490403055034007103140303020350b0030148604562081c60100d032003894100070b5178043c2c996241c205040c100310f0359480007aa1400e5101c04020303610581004c0810a0315400090141c40d89580340e07a4600d10082c0034100782401b1080f82100f15409201000b100c2d0a07011010a5087e1400134540000b990070407000811950500b800c0031074099400c420802c12825000c48851411 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 945787203 1250 945785953 945785999
    0x2031518030304050d030b060f16020a2c0711100519020a050a030c05091003050118090b07030e031201060e030f0d0203090d081621031107110414011d10 67
    0x903040c07480001401c1809034130008001001c3c080381c0480e1041800c80070902d82c5000799605075540b901e4030071100e2215039040320003545450741d101e560301c080040701d4637030751056061078031625a4001c1c40d005404c0030b03c03a00b00b1883c0243c40b5401c3c07004984030540340b403c42d061904000c51078440040d8000d070650140d44803100078580d03905400c0030814007034422100050300003490301418003410400600100f60a010380d00c0c684d060008240050305084c42117504594200b1014842562280c9003140540411080c0c1c0c500d40c003007030011740300901080760030314041d10030b603101c2103e5134000405152400d901c1d429052400c0d4440d100c0307854001e40200407902e10074019180c4152040d03050908404030700ca1855004c05120b0110109000c5c0007280d1010001001c0c00c0030356824400200c081107060316030b00c1d500c4014031002004043c00090b60000c2207131704c200000d03002203503600c0e609030000c42e145000d901c404107a0400c10b1490048101030100c13076501074160030049001c00e040400c9520415414000a11 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 945788453 1250 945787203 945787211
    0x515070816021002030a0f0e01020a02070326040906080c0d0c1401140d05010314150711010914010b010f03060e070c0c180f14060d0809040902031518030304050d03 72
    0x40d442849401c1c00f0303811560b0199943d0500040310002002000d00300000141380080c03c21004606000701c07030800c0c400b58014407000d41191601c07802102c0341c5900c9011901d5034001c21440303100c1c0d8800f4000504591a000845d1454404080d05205025813080e10a0261321084c00010303503242642000d5580920307064081e00b450a005032100420388882c41103824002ca0703622039545294005605aa100d840702120070424001d4580d510a1102d8030300360100c1c02440059401840382d110f42c8030782d01c10302c000070074407154685030021505c0e9444202030040c0d4441008200707550708201d0326090740d100d03803038104902440c0c40e44d4003002101c050301410812170361440d102d040c003002d40300000140c0305e034a198003038410790100b0300001800c105241c02e03d01410201c0b9601418406140544202c40150141c6880f91440d0384469542e80402c0704150703c1079490700c607480917071410002040061070074200f0250301e041030222080c202414401841e00c543c000c008210005074045100e015034002424045 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 945789703 1250 945788453 945788491
    0x411130e06030a08031003050f1c08070e060c060a060510080a020a09031a0a050117061801180b06040b0f0d0807030c1505071103090a051504090203040f05150708 71
    0x3403d080044070090320035107020060010304941083c082e02100e101e02c045651590340640005e0f05c4440302d50142c402c0c1da00f1040200341503409420281d600005514007014081c2412002503c2d40e0000d0000c40038070360185080003200740083c0b00320800350030211902c2c0343c2d40b81c03078040085c1885001403040c61140d4000c00d01e20201e9000c0c00ca650091076100448941001c80030103034004400d000c031102070035281000000201c11264228400031200e081e005440c0d103540b081d0101008040f0b0301040c3c501136688101844003d40c04001041d003803845207002a4040c14004100015107443c810000c2c0705880441c1103481035501d02c2c1380038091383d030b011410980310301c0b5604040c2c0780c4000d42d0f01c01400c0d6a0112085a0301401c003a80801c3c402c2c540340c0c03076403004201c1004ca1143e99020340d80300d03143c00c020034140902070792070500c0c80108d4205201074807902d00303138941101310142c5c9c1050343c040b600f0b81c2c0d080c08110700f0007900b803042190011518907000446c0c80d040344002c0038030780054a010040754100984c0 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 945790953 1250 945789703 945789709
    0xf02010b06181503070f081609170f100b0103060b032a09040219021902060a1409060a110d052a0a020d11030d02060103050d050903031303050a020411130e06 69
    0x9000141e002d03140a07480f8900b802000c0e01b100b1852400000080400300016568500030715540800d032a150740303003a9810304103440d144202480a050128611402000c0c0c00000030800c200e481d490fa038060041030b281c00280c005020789a0a42000b0403a400034402c0111500c8071340c6c104850511100345a582c500c0b0340403554042031040c03448554111340006035101a440030b1065500040c1e1080e1300710b2781d54500907149550303c1003d00030020340c0400204856468184103103050710b080d01c2034801652408416074009242e95000c00c803144003149a9818150340000140038846138005281003070341c6410f040340c50301120b160700d00800c030090b451060f01221741810100406c6540907405089010f441d50a41054044c10104840c421310920410b0002ca82c01440895034604896000000302001010258140c1d041e40210555a40500c400d00010070901a084a80b20055001e00098481840c2c40d00501050301e01400f02860f019604200060420f19500d800508480c1249200305080e01c840c400 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 945792203 1250 945790953 945790969
    0x30109211b05030703110a4b0218010e01030204330e07020c130b011b03050703030501060503010b0d0f0b04060f1706070206070810170d0f02010b0618 66
    0x105050101160801c040000000c02003d4050103500c540200c403014030324143e07035081d14100040c040946044119101c107080680407a8580e00321064440ca4415003002d02c05030604034012000140401c02c0700015810403034a950401d00d50f42e440711070745604040380c402d20200103210080c05241e5825086141c1c02c2001900035900311000d100e6144174517100c06464652005010700c1186001d4400420010b600000d03242c0306c40c020140c003040f418014950820010020399038002c0c1441803000c0003c0812106504206606107e40c0310541c46280f9410700070200ca2050300300d0002d0160070001840780c030210200b0ba602161340506c0104601c0e440c40380520192070300c00e016540090902c81c01003150803480440d03205540035044200c00d01c24140d004259116016116032002d40c00c04008540214400d1500325881900c00c0c00c1c400d0010355030b40c90a00300904054a80c81c0c103030403000900008943c030084040c1e401066200a1100107484400a02c81e4032460117070b0700352041c10001c01e00d110307104c1d582c1d = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 945793453 1250 945792203 945792227
    0x702060712150e04020109050f031e0f06130b07140706050406060906061d09010f0302090a11120915042109050d0b0613020f120711060403110c03010921 67
    0x916484443e954811040d8040e0095030100d0215411200c00314440c240301d03480754440040240207025030160a150081904400c2640ca9040d0081c0901d1300c902e00010040f46001340509004194480594200300400c80c4c4060321050800c00881a01500c94004205503041150040b900181755101d91a040004007803039440701e144903062650011f034041d008946680c2c20106441d0750384054401c1000c1000100c000d005140480306400400d0016003000810760390b105004e101c2c0003980415030300c1104200d820030013a80d2500040c2d10108060790300d0621280f01d41410760503d0312400c1c140740c5e440c1d00c1d24604c80503404030b8002031201e420904a12030003c0c80b00424000d0b112984030000e0381011000010101c4255006840ca0807648141c042c061080318606040543c0780350030841003003984c0850440107401e440c02c1004051007c00740324004d10011303000740d100c3d84880d041e1048404070142044641c000552181e450201d041c80414212601c003031083c0a500701030003401c1c66002d025526009260 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 945794703 1250 945793453 945793481
    0xc0a03021207080603150c0304061e0f020403060e0109050a020105130e0109020a0e0d050c0d11090f04020f030d0903170c07060e0f1210050705041502070311090702060712 75
    0x190910082c550401c1c83c1c3c0307000300415002e642540c0302c4442d80711079081090300c450302a4a030400011300130540b59440031854900749042000442050045002030343c109640e180881d9a000500f0000c0003140d10960303006816040c002d001c5083c0c03c0d15110348844108a019050040010f01e28540e90999484800a000455028071555850b000d5a0b0b00a40003140101d01245032205048458513000c0010802070317070711030010030864079540c041c011421800329049808000c0800c1c201807540d10111100d00c01e450142020025103458010400749189542c0101c2c0290412541c071a400c55004404100313980e0010f15542c08140c005e038414202d4403402149250300d004030301c0046501c55019032230302007170081140c0c000b081d580e20a007003142048141011421940c01008461604200d5800c41e641c01883d80c144079062507075440130384415640c504400ba005801500041c0100404514140825802618241d46074504594040e58508001d0070f001e00340300314480420040c08081d0401109100a2 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 945795953 1250 945794703 945794737
    0xc050312060a0b040608041a0408030c1c050414070501091802070c09090b07030c210c11010c020307150207050303062b240e0c0d05030c010606050901090905060105030c0a0302 77
    0x101d0001b8040308040d101140c0c0040c6400101428600d81d001c4180290b40001070300385107440b0640c11000d2a401000040d9540940e420810410030107882600e01c5580a4540c0d0b900c0c51140015450420040da00300390f044c4850102c062040710301c1100500560048604016074480c81030030711000c00152640102c414600b00324004c0c2c10030295007921402451075403424400c003c140d4100b941d034810010f150542007101d410010700c05003043c2c2c12914039803c0c1410001d507c00d040d1100d550a56031400301e260701507840040e0620402c2040c02daa0100321050703420450400d9416540d5907140c0c42702a0400d03100300c1c000098045218100c402c91070b000301c00407058108804851400b548000b000c3d012140400150366841541c0070a02c1c02620701d100074502c00380205000c07800070800341c0710040030117070703120710052007159070380c40c0300f4407840002c1c3c05280c4a0307640f02c1d100340c0001400a0710307540021002074242424400c1c80c1e608107043c2ca4100c500509115200c0c5800344049009000301c0300401119441 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 945797203 1250 945795953 945795959
    0x2070218070e10030903020a2d051b0d15020c030d0f050f060f0a0303030c09081e06060d0c090c1103030a06080f011401181b020d020d0c050312060a0b04 67
    0x901078151440e802c1d900290f4030703078480400360121003c000010700980c10683d42840003410905141c0201c08441c00c4a804076484440140d0050442e00c00850b2194010904d64a8940c0daa040840600404580f01120020706540700c030118951000d101180715004520006511024000e0380c0c1030442c2940c0c10010081c260402c9000707400261600030011281d200400c0d01030420386021014048003801800d0001c0c03540c1e508030000e02c0011a01c074100446a1404551101c09010f401f11140c1c2d0300f02181c1c50366818040c0740342882030181c0751a1090b04001c41e071100052a14082c1d400301c460f0307910002011180f082d0180d86924144d0006820b5020010810001021660049040d10909001c880b1071003984c5130204c2c2203d40e500400c034a070841c1040100404035080076604040c8500348000b00d94803c200107508481100b1100c080c015820110700384000301c0d81082014030280f541c3c60142802c00e0241c0700c0c943c0f030b071140e00044440c1010305070010b501500c7d084184002001030040b000d9440b69 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 945798453 1250 945797203 945797207
    0x40501140907030b010e01060507111c0b22121101060b160c05040204080304141906020f060c04030b01140f1203040609140a1203020f16090c02010c02100207021807 72
    0x1c1d01d40011074042c5191800403551b40c0711040164183d4281d80c17a00c9103010302036200c13070364106002120181d00451100d003800340c00402c0d807507207003900388a44102001d07810528056100c90070410280c0c1c41d20810204484c000c40c2c3c0108003680c0c065403908009a50054003910365000d4241500300807130203000003405031400800c405c1c40c003840d60b0091b0000c071341d11600c60341041709a220324415000d060384248000e000a41d0394070190240c0c40c3c0028580c5c10250b1511042d160746500940c448405600306111840c000f030014011680d005000d000f030300d454581075696600f01c4580600a1406407004050169441c0e140d40640905038200100381c58240c0943c1204075950fa4454000c00001035411400047c40081e04486100000801800400503d003003440031010544c10342e006a00318400d000980491500030303c030115000b064074083c05080d40c141800d01003a04d1f402280f42045a00d00184451019800f2031100c96001d00f8820259a60707026000044c003544040e0f07030740380700700c2c140e20706210f0a55 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 945799703 1250 945798453 945798463
    0x512030f070f1103090402090f09180f0312070818010911030706051e07020d290702061501120207140a111002060703180503030703050a0e12120405011409 68
    0x801c19075490202d404560021522080d10583c1c0541a51050094080741d00e03281d0082e00254078003509c041e00c410030680000306100c00541c0c40c4030380005180903400402c0028404e116125030540d004515103084a440c202e0035440c010091020805101c000c1490b15440b840300690700384000e8024041000340d030a03e003034904c101319040c511900c14400c0c0000d00078002e8060381d1040d0304a5020540584030074a440900398441d9074205d80c0040c48041040c00a40704100c0100812030000c4031101003103202d18202c10f0340300060024011340d07000008004000b00b09058040e10303440280b9002040051110f101000703130042c41801001e0444031850b04840720400148921302c24040c3c00488050440d034801c0c02500301004e40f1140c010b030040300004101c0e40c080c1e0070801c80d241031810101410b90140d103406045820582d000b1b400a49c482c014403600c0340441c002c00e032413480702c1d5000e4014481c2401c8050401d2013009902404107094030001414041d00b90b1000d503000c54210340c80c010501c0c048841d00c1c1c80b4 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 945800953 1250 945799703 945799711
    0x30903080a080a05060d0c03170c0a05030a0f08010e0a1113030f021003060b0a030c05040e04051605040605030a060b04140403020610091503021903020301150f1d060d0512030f 77
    0x243c1c81c08001030414681900d00c100d00540007403203094094155120100b2125030080c1041180d80c04200303070700c50200204110341140303005201554540593b51001040104845c400c902080781540c0103011240302e000e4074a4010980c060001800b5140b80a4840786000c0c01c003d4451076600b00c60008140219840002d024602c00c0700c40c1800e08031051002e40c101c0380a0301946011503400d012a10816000c1d80c000d000d43d001605280c0e042590742c0c01803004204003160200c1e0140c00c440c5140003039840c0030114002424040b0ac00780704150501020903038507001d43c0030107400c40351100c10144070394072690300c2202c46100ca600c0f102554501414082c2d616a000d860520329120807000c0001c01035044d100702d91840c10300e02031100e0030361b18507000c108400454074083d46100a46182c0040107075001d102d81c450b140c100308080c160403481d05140c60103940b15a0300c1400c0c1c51500c0c020210003010b40c0c00491750700c20012502c00c0c02c8804542041854601015130f00c0078802400024044101d2541c940c180c40b03 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 945802203 1250 945800953 945800971
    0xe0609010f030f020f180d110108090a060213080c030706050a1d090103050f060a0207020f0108181e012901180b0408030306101b060f0b1929070f030903080a08 70
    0x61003c08001e00404030716040b006031242e80f00000c0f00c01190300c600e22b40b40e000b44a0004861110f18140c50b023004990150442c880342400f2620104030801c000d1201007402c980c102d000d044041d04d85a4007900610039102c2140c100300036081d10342121044041000c0064101401241042d03850386003050f0b8910101e401d1700014410017000841070b4a0a000b2221000e80c003405c0211410000001500d070300401800c0c06000c5901030032106492034042007002110103014609101e604945d00780282120f4040002d00903161490340094031080b03041042100403032080c0303000411040207a1030102c94058a8001004078407000030002003951000002c2c50045104a496001c040c5040c9010f0b2501c0c0d01d41c2c640c852002100030590808180ca661110202c0702c03400d0800305994a01400150017890103d800100c40c441541d030621400351212400060035255100162144c0511034100d9018050310304010000e16100c5400d904040c0310300c04900c011030b031240400c1d032a0311910502822501c8100e480b110 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 945803453 1250 945802203 945802237
    0x1d0c04141302010f110303071706060c121812030a201005250203040f060302120a0c030209130207060b030111070f06090b16030c0e0609010f030f020f 66
    0x8540e204600d080c0c0114403609141da645541540152206580f400203038041c4145171480a04111003440250300ca00c6281d074854604640c1040d02e5125804003400c440c0c001e05090040f800c0c280700003c1e509289542c1c0c90340b110f40b113800142515600d40c5a0f0b0182980000000c01c05402081000014040001043e2126504000d843c80103800c0c1c03411003506032603103600008411402c1082940702c2c071303045018005220b01003200c1100d4604818241d01c202d40040e03000040801a1400d5071180401520403882d0a5261010382040342010350006400c42108541c0c414030100924060341c116005d405018186c01c0c0084154409403001f50084903007520b1071424014881d000385010b1140c070310748803c82d044207070500c80c3d180c0b541401000d9070001241c8481d5101107500120b03210796800c9104400c3e2070304401600c020803c009080c1c03601c0201c01c00a10010890310541590707010180d8402d50030a103800103c3c20000101100503000a000340e034038140c40000e43e040c00415041c0240403880700d60024803 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 945804703 1250 945803453 945803471
    0x2130e0c0a08070c03090305032b020a09261509011407080c09040209091501023d1b2c21070315061a07150f1d0c04 51
    0x640e4038400c8484020004200000040c10075000e61003c500e0580240303420303190561250f40c0c2c0b42c03031a40716003180840c0c001d00e10481032241c20181c0c420000e00740014000e41c104103519002400c658090300401e9030f180d400c226000307051254288030703041441001d4212070807100e021080300038004040e9883e038455403c10202803401110100110b009016903030310441c0b503581c2c50320440b1311a0044c0c1d80342540b164080124110300c1c3d9803007042074002e4014907012600146210000380c6842c3c1030503400c843c8a2300700003140c68812114180e00c1d48054902101190314141c2043e01001440d4140c03a01101c0000c0401c0926465030001087c071002c000d440c258410404203841e100800760702d1034803d5900c22042a0252907109400b40c0c021030f4460420b040300c003116225070311000826400b45a481d100c5568140c20003400181e89041b0071035900c000f01042c94040c440d1114206040003120403803a050712403040300d05132807060703010103400c12000c92040c1c035a1411582e036030344640c1603d1040d4820b46c2003840711 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 945805953 1250 945804703 945804721
    0x1c05010f06180e06060409051006080f0c0301050d0f02040507020a05061807031217130204060b0f09010e01020c030d03020c010c03020408070e22051c0503061c140102130e 75
    0xd00b01d62001203000c511149048001802d698008000581054050000040c0d10015000d0b0740d015144401c0104500c40c1000d00060003058000c2c5000181d02901050090061001c01240d0556070281c807034002c108c03941d0515603080412044025003041c5044108110390b5404901040210301c1501901c0e042e407198003514031040c1c071200e039400080d000a0341c108000340c0b00c0100464900a281401024240b100307070034005528003140c011066842134000101145028480e01d0007402040c84a1410329a08004003002d5020b0302c4051814850082030803001c580c0200700c0500341050090031918a4a6681c20040c080e40240c1c40e14840d5608015400c45164024000d4400792841e180050140914103444c02601481c081c14840310f501c0854400c94411156003501c0c012540503d004011100d8911060341541414120000401500b4001d02401e13030b540c00342001001c001c1c017920601d003107582e0600700c2d0203041c05c102c507204641c03000a400e03003101401400720040301d034070290402c040e07601c003101d07 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 945807203 1250 945805953 945805967
    0x305041505090d051b0625090b0318010e10020d140c1c021c09140c0616050c060c070302010906020f060c0a03090f051f0e0303011403031c05010f06 65
    0x3200302c4980100e40c01c2d07040a48160090003030002c032485403080241e800341201e0f0810a0030ba0710544c448405e18103031202200d200e206100c01d003446103001213002c1d00d488142500350101424080d03000c9072290700d500001c2e07025008141604600310030380325a8840540c55400a600803040106040d0a0100c500d180c0c0d00400c0180d4440c0b00780b5a065407511280c126040d180308075042d00d03450400d43c280442da0101c040d8000c07000c2a040d548500140d88001420250110340790f0704440407680d4003514080d1595204e000c266408003c2c500156000c0340c21900d000390800900c604401c2c4c102c4404a000e4440400018540c004c51303000782c0304c0c50a02d98807004126100d2039642902c0080703611440c0411004510f54004081e01001e80c540000c2904044d6501140440111030a44195101ca0507071021620180c41204400303040c21020030501880300507258803070105110f480c2d038096050045410076141801101c1c1c0407900e0030350b5084480b2402c081480202420300640d00e07071100d40c1c1d01c01f04482c1c1c041e201d = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 945808453 1250 945807203 945807211
    0x118060e090d1412130c09051302010302090102010e03180f01080403020c0607030918050937050c0a030f2006030a0b03161d090c060301060e040b0a060305041505 71
    0xd092820300504099540f072003004007410142500b00444a41a00c0500d074a90049040c0070302c680312003d00d030400400c2068140c00080341503191001380002c124151055581e91503086c00d01680f100c080c403005034010b200309441400c06001c0002c1c0a0814400c011506000a03003c982049490007601d0045030602412a4010056440407010b080d4502e024400f800442c0c0c42441c0c400302c080d0f203d034007508030105052404204c1c65210400d10048040c140b121040c50b900300b010b05c6000200000d80c00c1c07800e4044c0c000001034240b89000400501ca000c0c44080500440078017a55004c0c0d5036840c3c0351020007841581070303c80078045141e415440f481c0074500742d00404000c1016046480d038150900c001c0403032801c0d1a6040c0709802c07286000000480400005000303c010780c03a00520040302140d41183c0041885d0015008030343c1381c11450791000181d9055411501c0e1180c607204050010070010848a0f40b040c0e032040309203200081c00c561541103039102d0b9201d507409145006000000c4400d444c2c05613 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 945809703 1250 945808453 945808471
    0x1201c050309070317090a0e04050d0f0c0201121d030403060e030301230d05060901020c120415050318070f14040e0606040f02070204060e010e012c06180118060e 71
    0x10f142007001c0b07903220144a0a924064501d1454400201d00285054920341d0040110003060400c100034841c1c01d203d40b200c1d00e1540c0c1410085064240c00081800f070940c2d00003814020446d00600c45080c0b00d5000f44050074206c04250b01229140710100d5485c0c006110446249050540c11143c807107011041d02c0c102e802c5070134100358104031031856240340c840310081c003a00f00b400010000d011850401c44203001e0003040c4001030b036410507000704a04181071541c2050035260200010061100b000c0100c1c4491006032403c0d6803262a81110b0818001c240180000f00c0d00c20040f021500c0350121066104031500c0e0320840c0800c81980060005179601207d50081031340115002501c03c0c1040e4000c0d406280902900519056203070b030004044078003d80021b00480ca640c40103019040d01c111100307003d041005e2480d40c824003916400501e00051340c8030b14064030b5200010680360b860f56044500341030b9207400c44c441d49684400b01100300c5500e611500d4541418410f00040c0c2c050f402c201d09004017080 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 945810953 1250 945809703 945809713
    0x20a230a021314040803013605271c0e180a06030606140a1a160201090510080a1b08060d0c050a0b22080c0f01201c050309 54
    0x990204618042c2400305a4449516050a4880c444080d002c0c03512441c440c020441d165410718180903802a058122001c11081045003a01ca80c01044200f801c0c0010007034000c240c650fa44240c502225459001445a200c60040d101d01c0140020031809150780402d03040c1d08481180c0700c0111501c01d10908501c1e0400000c01c248045c002c0c890086582c40814020045000c4d583c0340c1d90031003190405d501c03140d5400884007081085217000d9072004000d00200042140702c03d410700c440ba426102d0601c0d40034910f1803249042e1b0859004820180050800910810209244a10141848504a402c088094500724030000750003503e081c030140c00301c6260345200107a5108002c0c4459032850120948081c074148a00141d5035603400f801c4000380021414590b04c590115080c0f2042030641c555400c3c104e880e0040c00d01c440800003c0d28035200008851140c0c00c0050300d0011780300b0003102001500700820f1064490a41180000c410301520100014a0408064418202c50314001a43e10003100d07004 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 945812203 1250 945810953 945810973
    0x315060e0d05070f030804090b090601080f070c08071a09030f07061e0608030403030f03091205091f0e030616050f030a0b0612010326031902040f06020a23 68
    0x21a0080c042035602c2042201c00c0e035911110b1042120490f68003c54450200140034000c24030540141403881e402500c0000303160030031000103041428000c01140d044070300711380007483c0a441f60101d2011190448440c40e80d135042030500c040c4c800f14800c04622801d40b500089800200000101c42d098080d545e1f199081414a03910b80014003c1e1003075000144518030755045e407051291140b40b000f844240c0040da52b42c1d1451a015050002c0340020702c00381172074443c0342400b06884141c0c0504098140c42c0a83e92207002c1400201d405481c4040340d1074802201d81ca103000c1d075820011421400c8022821243c05a0b69807803040040368464620b01c00188050003105070002d6014045c44d08406c08040100b020303a565004200c00340c0000200700d039048603450041050064124609900101805040d11040d005180442e054440508048005543c1c41e20700009441994107640140074584040084155104030081d80c521180c4c0342655200442e080c10241c0a02030340c640307507800a00c04044c1c00410b80c = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 945813453 1250 945812203 945812209
    0x30317090d0f180b0d02030403090801020301060c030c0312110315060f1803190b16110705130b040f0c030c050313033f061e120809130203070315060e 66
    0x2c0a81c580000c1858040f2000c103c81541c4c5002d03218083c0c200c500162240b4003800c00405e1603005902c04043c0364030410041c000070751f011852a80311901418112210b0704185811580c0c900036032414950507103440241d1810152401c000c44c05541240e54002c1c111a1580030800113114201181c030303585074204000003405903003d000700303500e40c0000c0a40b0f00d409030104025075245a89041120459980020041c60009203008610034900c54075007215065a0440d415a44107a42d0007803611440350200100020030103600050540040600b003407280c03440c08102c18000c1e0084d0500c2002107403c24514100c45441001170b41d10600040c60854045441d6071001d41d01411282034a5907101e1024030b001d400c0c804483c0d0300013031181500d2184c2580c000c50389000c0381102c0c03450300406616841c6a00380c0b0700d041451910300043d1841e201190340c6160040c41c00202c14400c010203603400441a815101c5c02800e560f01652050794241c50030710500714070b42000c050307140150182c01c005c41c0000c290120581 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 945814703 1250 945813453 945813467
    0x501110c1807170f070810050d030e030708030c01090c1a0d0509030909040506061002010507090506090d020405091501050913230726010b15070602040906030317090d0f 74
    0x111450a084001c100e00c83e48107520244115560306528268000313001410390b00c60710b4140c1c0003905031100d0031880d0400000451015013250f0240410030003c00d054035580d810b2110340b000745040030480341d0b5140034050b850b0280001d00c1c02a1545154041d0016000b11b000184407021071032007201d9441d010220008200410000d080c40045120602401e111500c0d4140c01c180218042d10003000c051900c42c0070000e4803c0d5002d058011a414041840380954010142000b41d54089421f0381d140e03107041c1c0101d01050351400020754810308100074002c0ca500040340c0a21901102d0900007020703a00d50051118180082d140224000020340c0721002040a2901d21490403001090144d82111200d43c5585070410319045032140c4a09108081401c12281a001984402c01c1b8001d000c65100a00058200c640d04210201305030b20010b0315001300102981204c01814005004019041d201e040061a44400c10545001c029960002c102c0d038040c00100009071000681c0c400003100034580c4c2c111000 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 945815953 1250 945814703 945814711
    0x114160507031b06050103020405160207140102121222030e040b0f09190b0a0524280e0910090b0a051c03020c0d15110d090c0501110c18 60
    0xb00d55280000c05a43d900480100d24040d04001c18a9415401000129840606081c01c42071001001c80c07a4141c000c41c000040390128000d074a41c00c0000d82c0181c0c1401440c01c04429103400c0050800010b28030121010300a18039906c00748007aa201c5c40300c501d40852000b2020700820b60055100c0428a41034105200108000d0070300140040c04401140c4031030000e6903000d40240c13040000040700d41551140900c1043d0494460380d21500d08000b00f81d145010401548001415015880491080e01c003100e031a8540b10b80380800d1244424541106601811825400240c0d6004948402c3c0740901840b80a034803004600b110b041e103418070b914000d0281920250f0040306220000400c0e0b9180c0c02e0304104240540140c110000d10307882c00a040c408081e44203031003080d0595075400417801c0b80d10784410000074158005500583c40e482c0741780038090300400035031325400d0501c901c0801c01c0641c0c18100f1141301f030302c44203100719800c030500d0b032a0f61701080800e40142c41000c4d2000e910010800d10307504 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 945817203 1250 945815953 945815957
    0x1050a0e0f2407031107031e0504210302190b01050a050a1809020f13051927050c1f02060a052e080102040f0e010b0307080a201b011416050703 63
    0x400389800340148901d4100e001b054011910414031030343c44d9011f1003100c00c0045181d00d40306180600b0408410705d400c0075000c003500c200010b00ca54008060007001000082619012280d008030b6440c5862042c2c50707409d00071070780600031280340050b2a04000d48410280c0305030700420341d8034000c81800f050041c0b41c00e000a980c440e454214842c50350316511060344a00102003004a800d103040d114190000b4000c01040d00b456262111000d000200038249003000c1d5214041076400e54210b00f4564039042000f40e1161f40103980504001008956420060313010039070b034003655000e640b07006568085580072503126001204980040e181c04600701074143c5142125948027218546411070325089070403d800009003080305480c107100340760360249000c2c014807001040341d242d4541a00010040440030307012584050703c0792008040055640741074050585c01c1032035191220514261103560410b90400e45009510708480c80c1d06081e4400348061240c40310b0320081465500c091030881386544480f0301501 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 945818453 1250 945817203 945817211
    0x504020d08040605040608090a0201020303040816080f07050d02010501031106090a03080f09130c210b040c0e1903230f01091203050106080717070e0301050a0e0f240703 74
    0x1903407010282014110390b546198485041c140702501059015000e40b034aa44400860070060307a00004481e44503520681e45600d070218807408202c1c003114008000c01c003403008144a6400a02c50024180581c0200c007142d17000e08801d0000da00701d03402804068031018404012002da03040c890300030030b1080405008450000c4d40da856000090f000328002d00f0390060006191000352a00c0100c0b040700e680300d040b042003500e0b4054030144c000d01140c00b00d0f040b94a809000c007003030448203501801d80e1680183c024090390014600040c540c03180d0540c2140b00b00d11030348610380b4802100c181030003aa40d1010140e64000b00d17114000700000703074601d002102c620135800340318015074003030069a026611520601c8609070a5420140a9070750503007006003008403400410030500e906c00c507003092200302d0385001449525205800c5828112000f43c0e01e800d50b0074003040c8940100e660f4030515178220300e40b042c0c8204840840901b615180c07038680c5290a020040446030980740c0540f4402d4205055040002e = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 945819703 1250 945818453 945818479
    0x30308060d020901090c090611101a0d060f0f06060e060c03040510080601021513140313031b080105071d030c0a0909030e1903031409151c0b090406050402 68
    0x980f207402d098102e8000c00f511101e4000800d40c100c1240c401a001505080b00f1038a4190380041c2d5403400c02c40790b20b100948540007a4601440c503401008161000b5144040221207410f0600250100e00c00b20b40e11546017240d940302c410381d14800c0800f0b80d4169a201c10f4040303030041c204004c83d00144003c0032280010000007806541d04100101d444e46d26881d14101490320a0001e4104400407080e8514000420104081880600009058140d0001d125044d0030840d021603840c5004031031000103220100700001c02400701260043c00c404070315925011046840c1d40d00b450a8030002d59800001c0b620780300030344990a1803096107985818018017115220000d007800507403000203981c004000302c1da5030b00149007807651000340a00d000c1002d84902408600080781d41181c1c2d1201c0c4406810802d20302e0016403503440c04400c440620300002d02c80f032030320b04503400e8440003580450300c560b504d40c03261001410800d54501507445900340c0200f0300c3c441ca07a541d4a1b40000f900000380b0407079100d080e01c1180 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 945820953 1250 945819703 945819709
    0x102070902070c0b0307200120031003080406050c070b0405010c080c0a020301090b0601030f06150f170a0c0909090b1b090907020f010c0516061d010c3501030308060d02 74
    0x1540c4a101b09550352118045100044803030703801001c1042c0c80590420142c00c01030f8240b52110680680c0141c26140d0301e5a5209403071110b00019000100440d900041c0011a40e92100251082d03e41c264103503a44141d890442c52a0b511a078800c2901059a00c07101c6000728080070007809950b590007066031080040342e0300007421140c0d150412105088036005110303071544c1c5071140c0070100c05802c00030010681841c280d1141c80400303092950401013402541e01c5801d108400c9002c1c04244014044114100904010042c0001ca8400720018805200000d0910050b001c0c822501c0e42041d205101a240c03010322003110f008002c1c500344401303010410400241c98050359184942a181c1c0901030f00020346441b01c0c01e40e40d54494550400909002215000450100340145954403000c005004000d0000744660032020208410302e55103003262a050440d0021403020a50b2121801c1c4601c030b00b0310540c007881d50400f014101080600e454014000a0b01603a1090340094006040a104c00360907400 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 945822203 1250 945820953 945820957
    0x50d0603060609050901150b030901060e040b010306150f18021903140a1e050714030708090601050d0f0b190603050102040914090a03081015080709090b0102070902070c0b 75
    0x803104540d603100300700f2030300807144192500711208900030300c4070300320100400c151340e5964011045c0b07c210000106551403000d5100342d00401c804000744083c0d103001e08005540351424802501d0250074075200781c01c95106052107905842d03070300c000c00b00940d003410121007000c4030250f241a600c40d4200a020007120078045080d0020b2a16070b4082040c0441000c8070440d0300e8083c1c03508441d5414100b10b00c6d441c820802031904500075140c2c0000d0729698120040340c2c03010040302c08d4805088000180451160f204e000381d441508100c1c21904966030f10000d000112907000300180200307400c044144005000c0500050f04000d6805140301d8001014070083d040b00c145520440e5160350000f41002000001d002d01a04000e940072a06014038210705035646034007001500404005d02040081e4607d62509510805494180480c440402c11014007030310070001950040045094034100040b2952a070040080301c1c4d2040e0b01810b9100d01e4544081c0203034000c0042200d0829403508042180401080 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 945823453 1250 945822203 945822209
    0x306041b1d0412050c0616090f15090b041203030510051026070c02091f09060806060a060e0d031211030609090c150c010b031c12150501050702210609070602060f070f050d06 76
    0xac444045a5854100a05034201c80d60211407400002e200800c2805815071300d88083c2605402d02040b1559000d682c40d990b4840b81d004290f210000d950484c00c4c542d842038032100401c415040d44c44050f800540603205810040b1180400284103200310001402c080032100c2d00050703d0100c1f20f80f24003900e8a4032684040d59000100090342d0342d1002c2200c1d100400040760010400d445076000030f82008402000d200c00c01401d80e0080112040910426214043c0380503950b082c4d400170004c3d0816405c074400140c0c07054405901c103030381c0c000200351010000b05000600610042c920003070325194102130b441d81d0300004850070480d50707505098001d0361024404c03c0c01907404809040740c601104080900210502a01e00b400545801c09042c0d1030600401a002540d4003428410340715061440000d42c0761081d80210034540c81d440a0b0031544040002d07203903000b0750140c0107858840b5220b085c102d90302d07102100e040700c1d43c2c40340c04080b0b06032a000b000b25015400c8181b514502d030440c1c041002040d03420721782c = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 945824703 1250 945823453 945823469
    0x503091e031c02150108060c0f070b010b03180f281b0608130809040f0605060c07090b0102031c09030e10121a0306041b1d0412050c0616090f 62
    0x540755000c683d4148181d0300e8110650800b40119418110069074800f4000c119040710040011120072408041c401d40320f41540c4444243d12541e1141d64440c0c00350419582007c541c4c0e4690601c1111940100c0e0900d03900080d2001003100110a50120b2550782c030b2005083d00400d9103401040201d000b140300348061003c00d0303402403a9280340002c01030040000900c01401341c2003d00c1128000741c20f66080f140c440344100d5001c00c0c6007060b100c00340e0040072658032840c1e202c13000041758142810b01250310070498261141c1007100c06981d0005a0320380c85036091084c0c450a01c8039100c000002d00341d1003009024082d140a00e20410f61b00d0120b000400c00c0d11070040132031045154040e10201da4090340c5610120a040c0c41e50004018011998529018000404504060680d001d1405a400328800148526410351002c08200c0181440e01c0340245c4041d100c446142c866031442c81e0056080362000d55280c0005c1000b0740e60b5030b6890030031038010306100040182d0020000780802200c000c40024003504 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 945825953 1250 945824703 945824743
    0x20303040c0f08070b0a0e091504150609050d061410150c2019230906030304212f041a010c0224091c0503091e03 50
    0x2904141094110a40c04011002d803800c20600040da800f046000480d0310080c1c8098850103102801e0b0703982c56202c00c0040c3c2144a25080044445214401400038682a00c081003d0300d0a601c605800c0310050068101080940c01c003046181480d150110107140107690001d00b10743d200c00c40c00b0038078070107881d280c1d0f41a080e080140050c2c41d00681001000403c1c5c14500d03003280c00c07a81e440c09007910301d42c00440c544001e00071481c0b451f21584020380340c0c3d5100c01020a03c03161940c49501640000c4440b4035228910403580098034100344c00c88601615009004609007498502e4020040161082103518800d450201c50000743e00440c250400d002190709814040e1828140a1000d1000e806c95074841d40c14200c0c040c1b81202030800d01304400800f8642050040f2581c0007003482001000000c40901c007000e40c28012155107400600aa260b0840311811600381b13200748001148050000034141d80c004018a501c0c92134000850100d008000805118040981000a092501c4038621410341684 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 945827203 1250 945825953 945825961
    0x6020304050d0801030b0a05060f0d030504080c0406053f07060e09040210031a03031201060f05180f0a08010c080106020616081504110408160504112b0903020303 71
    0x2042c07142c0200400b40c0e107050b000310743c516182d541112030f000e880e0500f49540c84001c611161110611101140c00c0070f480341d210021240341c010410b5105128407100d50084002c0445140360500401044034402840c0b04220383e5103024880400e032810b0413601c0e400312845a01405007009121508000d0310b114003408000f4504500a05224030220318030748100002c004210050b41c0f00030042c1009003483c0350000304070b50500e00c921000c688042d0304a40c984000b061f151600002208001c0c1030ba171469403580c40702900e2404c207032994020281040e20360a11105107100e01e04206c84c864200c588002c041481441e40c604a80d800c485032a40014005003614005000761901000389542014204e9400141c00a800400a00107180030b0f2000c00d02035080980792182c1e5541d90850888440428010303a40c0c2e80c0c1c0c0c1c00700745540d0420454801682d0303000032000149841c2c0f6101d015480712840c04510b00c0c0c828084c80381c8010001080c0e9561517051901982c40303888070540710b031080352440b9800842ea2414 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 945828453 1250 945827203 945827213
    0x7110d050d0f050f1305120706020706060b1315122405090c0d020f070b070c0506010f060509010e0d060f0f0506100516060f2c072907060906020304 65
    0x1100498418481e800c1400340101d2181134440700c1d034044200000103841640d0303803030414108610b0390321254aa800200385403081c800103500a124007403281108020059035444001c0044c0621a8946401e181d8440c0800030541e200503006401034076850410488048540070030222031810100706003e45028804e00f801420300318038540508800c40b240209450070840020851040301c0b00d20f60850740200b002001034464200740c03402d41d0342c014803560b01c44c40e1080004024419204003520341d445207200010340e255100104030305031030041daa0f0901d0422400015207181010300c3c81117801c003c804112078046025403240d940ca81c5101c0030b0114800c402d8a0310740d401d0b03034000b410031440740c1c074581440305000f504003085800c21940d5065100700c02c4401d080c403400904c85a03441c0d034039540c20980300b0345606a00b80d49481981c40386403441540305c90440805a030308c280c640a1b203265450308901c0807145110030701034103140c050500485440c0104070350328070040d14061041210855004828401040 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 945829703 1250 945828453 945828461
    0x1b0807030506040504020f0607170d0e0d080f07110a0f2003011112040c0b13260604030e040213240c0c0e0604021b060907120506010302060307110d050d 67
    0xb0100311014001400e20b500003c84840c2804241440780320000b91600c2040801038400b500d1a400715182a1a04110f2500380c015248052150750310307000b04210084000c1c010300c04907000701c43d210004911a036506802b0341e007013604080c003407400c0e1241d04000d8001a8582d4421f20302d6500c01e0030b00c407604542422680c5030b02c00c9101c100a2180e4140000481c15001e0241034811400c0c41c410f280e8215121418260f082158070b070003c0402e104005091800b18200242a90442e880b0917400380c00d560710803200ea2001d4440c80340b1806c031070700a1000b25000c240b03e520300002101c40280014500342d00c4001079441d85109500207244004000d111501950034445500090400d908282c80303102e080d40e4440e0382100c1c940c000d01e06012030681c007080150300c0e44c0c1d041e212060b2011008200030126140300715999803040b1050a8903210b00b0a01096519070796000303201842e030103c0104500d0b4255400c0100c1038100070b0000041005694526503e84010480000181c1160300e610f582c5084c00203d1201b5070f = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 945830953 1250 945829703 945829711
    0xc0605060d02031f091e02010f0801080303160201151202180c0d0509010b060412020a091a04230c040f060813020d050f01050c0909060f1011011b08070305 68
    0x4648468070200582ca02166804005000819400784245a000352100809064801901c0b08250790804440030015102103003400303000b41c95a041a04520804a804900034052080150424404074046031012114141c1410860002080e0003400c600404025585c41d444000c000748428400800c0d4101107a00305040c01c562038910a003071500c080340070000d00c240d5800c40301481e514400180c01d41d00a6124201c8440024455a910b59480410f030040001c0007106030303c1b4200a400002d40c080013442610b414591144205110701c9029082200406104445a108010160101e13002002c100d2a0a201c0d4040b441c0c0c154031541010180c0c1d1005156820683c1440010010300c00f00c60584c183c08c4205c140d04507100520516285896414420701800c0886e4030343c00c103003d10121a030210080e061302113040d64448600d0780d4520070041c01c14000b2051a411241000c2071482d002d209501c07558005c4445000403804070400303c401d2408032040300f030000c0060100c1d4140801a54980661900 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 945832203 1250 945830953 945830959
    0x10605180408070f050f010203010b09040c0c121b06020307020f100b01080126060c0c0c190608090307120e0a120b061002010e0601080106031a0c030105060d02040806070c060506 78
    0x440c1c03038955642e001c103100d503240183c240c80e125030501d010070000b00704151200305810002d64503035035140c00102160700802d044500c00c0b410400b034007081c10b10451010001c01d801000d000841840000169510003642c805014821407161920000c07540d680029800345250758002c0401c4601d41150328104540e20030007801d120709001909189a038404081c90650b0a84510040c0128403401e440da6022855030050b03690340030f8070041050004440000d82011507203401903980703140054042220b00d9071000941d03c88944222410b02503184100603255000d800541103a25040c1c1e651103220300a00c0315901800007442403c120782140c205401000001c00b40c254034444000200e9482e6410143d006100e50300649000c071024240318400d4001c07820620a02c01070783d816584039940b4030f0285c030450105952a40307452900d05000080d021000e481010b01c0c1e0003081c19a4201001c100c00e0b6440160104541c58082c0400b25592005005c10760044486481d0151244010303d130000541314000d002c144 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 945833453 1250 945832203 945832249
    0x130b13150303020601290318010c090303020f0d12051302030f0d03230a050415061403120a05040b07020f210c102a0c0e1e01380309010605 61
    0x103c0c004c0c1c1907440017400e0000c080c0141d1a60350b405071800a581c902303110f41401e9801e003e6507522440d04426250180ca000344c1c00e40e44155010080955140c1e42c200d40c0800003008504100303460700d2141c0c042c6800021100821a0320b003201c0e00004d26000e400285007034143c000e44440c0c0046605442802840c042e14401c144055203800505040c1c024000c01107101e0a40f608001810000925040c849230000c41000708046a11001c0d807450b02c489400300103000c8e1003141a001c00d0b10a5810941380d00d9111652454900f070300300240f1000c030341c0001404a800040c4000d8031000c9590782e02007103184061582d0001c0306800c40161861800108005450042c1184203440c520154007034991494140303a0380d00e811451822510404850341100320181900640d5180400c5c81c00e0303090381c41c03805401c4590806a002c0c0400c030744940c5045003032052030a6071602410509640410100380038100c00f50500e02400d041c0c801022404942c000c0b00e80041d140d41d81c001c02d10852400100d9903852002034600700e8 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 945834703 1250 945833453 945833489
    0x1e080111030a0f1b05070302160e0403201507180803180f060a0e01080702120a120209120c120a1a0603070b0a0c030e0609130b13150303020601 63
    0x1d2001810500d4003a40758416005054080e8000d40d41c1c00540010803403508100c0e52000300507400c064811001805201007110110f88041b1007a0b0594180400104c9035803190340e019200e80c3c6455031070301c060081403200b04584d124107002415205541000b541143d00d070a9600815254031440d02201542d102e000911000c2c00000a80301c00f00d03e04590b40f021854500005810f449130710000c95404900080e018210580c45071200b2a004e4080e215110b450701d030b2020070f030707101d454041c500ca402d50300900117404440e100d0020b180406100d0700c00145001d03117070300110b004400f0844c41017a80b07a01c490300c1903869083c50301551007108006030244c17030140d21690b80c0014440b060500c0e10680f10720785c40816601d0382c06003c18070080c2220344200382d82d250900809401c90000786400c0d03010900c80011070200d0300300107003210321040006252001d102c180421030001800c0c0d0007041a0401140c585c001c0c410705242c0b15640d543c0706036992103500c03c1e1a40c50002d1500c1c205801600145a40d1100c803 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 945835953 1250 945834703 945834731
    0xe010f08010510030e010204030c1a040605030f0a09142d0601140102070e0f0603010c03020721140c0307150c051b03070609120f02010c0f08130501061e0801 69
    0x40381034441c110340050303081c4400f0600f1806404904040045075100003000820080d45c004a6811a0a14030400302d80800d2882103142d113005038030525002c06d07420000580d0042d12801c615034001541440050058026100c13014000701100e132065003640491222358000e0340c000c0c008a810344418907005004214030214a0315024184269501528947c95580040c0e000340440009003c02e010001c129143c00c8041c40c400540607901d06000e5443e1407480954075100e402158002500203400348081d444047d44d40498581d01281e4004000c50b1001c0a40c50004240040500c00381d054011a203038201e5080000180307c00d0b801c945043c40c50315031680801a0000190740c150180b803604520714030500b90060b4218864080002d000f6803a10442e2400c210400e00c1601d0f40541581c0c03213045074a1012010b03400c80e10381780303d90004038402e0f60907402803600c6200185c0c0d010b01000311300a0b4000b4695540703820f460071a0030858484051b10f07500802e481c044841e42d0002c3c5100b00c02031000c8180c40000d = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 945837203 1250 945835953 945835967
    0x80912040617100e0906011e140d02031203070c05071203080c0f0f04091413150b06041208030105011706150c16080106090b0414060120030d0902010e010f 68
    0x1515102881c480000d00302e10300f4500070304002c0c004040c0c030241910308503001549408003406103600503001d0a15035800e800039100080f0940714080c03948a460381c07110302000224002404200c1e498424403040300480aa1440910700803849503d07407042000c0c891034a1810448582c0120b2061031405958a010942c8001065001803450b000380340e03210003458800082d489401c03103030707800c403030300090f000a0b01d07840340e8490002c80052020740c03031560f290501400e09601d00c2c6180607104d0151036a295000f00a640d000c01c03100f42c4024201850280d5415480300b140c00013080c2038440740404001000b041d60098081a1381161b501c41ea1000c9160050001d80c4030300703a08040380845200410300c03a01c840340811110807421035004110f00c05982d562491400f908440c041c604c041403c0c0480280242040c2c010603240f100b0b03c2031142d0180e0354035401115000c007184200707da1346108540c0c41c0903042c400c0c0f0007850189400d10000c54651030a0001600b820710b90a00d84e410009a0350020030b00c0e0341d020034 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 945838453 1250 945837203 945837227
    0x21e0f0d0c0206130e040605010e060907050c0c04060b04030c06050f07110a080a050a050706030e0a060e031303111005031e07020f15010801060b09030a11060d020a0809120406 77
    0x1000d50700425039002107010780c080d1444046016078021404281c035170f0302d01c2d0b4091142d4810030b001d00030b40e030b220700c030010103900d055a019401803941004641e40500135400340401c070003500101d403c0480d005002030107072202da504c017001003140090284240a10860400064407040c203003c0e20386043ca4101d11814401d0b40e801034900c6a5400c880403141e524001d0580080469000316408441c003801c005880d94030b4010220f4140c49460790002d5202d0190084450f02d004000103001440c1e516180c190140064085150150204010241545168914038405180650b00c10720540c40386500f4003010f80310001e44201400703024010422502d250b1502100329a0300c0341d10030406070b1111071090b031505d000d410a94640f8014118030030f0b100700504240300c3c100c0741004002d000056880b040380b0745e24070400c2107440e05a0481d004042c0410301a80080d402c00502602c01860001010840f00c01ca0700500b18600004041c1c0081c05803a100c2000b07682034001611880902e008c0ca00302010300b030103141c02 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 945839703 1250 945838453 945838457
    0x1e040305070801020717210108030a1808030901122c060c030103111903140309091003020d0b1008010c051c0b060316050904150518100909060209030d021e0f0d 70
    0x4d01651f03000e0400c107060078950030700005c106295860384110340c0c80c1c1c0c011800d0000024080105800c0c402c203c04103c01c21107414070003a503d400c1000004640150201d001307203000e10388270304280505026180082d035140f001200280c41808a04801030304203500a0b00d003140940d000d000500c0825950a965903031968115000c04510342c02115414606607590b03c0a080c8180303042400206840c0031006160007241191112042d954000c47c9100120003800007039042191410720b00000b6103003501d0160000840446941e1482c0c0c0d5001090035524000701060000790701042a0008200000c20003013031282d035141c00e00117280e590000c00d83c1400000e0590500e80da0038003001c108103000b682241ca403040d01910038080c10ba0005c03514070311854144600382c080c0c10b8100d4000c608140302030f40140503041c01e03040d041c04640f800020802400d100740d000c3c0c5042c0d40c00c000244443c0d40c20001100300f00100d801500704601100c2c01802004955900030031190000c0841d041000c1c2d001c41c04003074415180c = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 945840953 1250 945839703 945839707
    0xf1a2508060402210f01170604080702060304051603080d05070206070e010e0f0a0f031e0f030c110301020c01050106080c040f09110c1506040f14060f061e040305070801020717 77
    0x70f00921072208406144d03c1d400070a0150500601181c0361090f14140c402c00b180b150410118003620903a950707001c4030064401301042c055000145423000041d47c00078000da048507030701c80c401e0880c2c600500c503076801101c164078009410382902da110302981e5440b100d980082c03d03c0d480e1880c4080c0c42d503203005010304e041006002003c0290350743c1508040c600f000c00340c4450700f015110800c0e484503980e54007082e54080c60400114140058400300e010380298045004492014241d03000d864408040c041140c00361502800424251424406081c80e80f103508000304095150441c007401c01d15014096003180309041000744012400c006c800400c440f800c03c00011100c03040a602800350081405040741400f501c0c003107500a13042504c6450241d80102d07000c03c5101c48542e480e5040f40e1005021245003c110b50005040c0e141104910101d0280505402c0c5412501000c0341a08041c2c03100740c651a4201140a10500c0f2041107241c024040040003103260000300e4966507030203107201000d22041400 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 945842203 1250 945840953 945840967
    0xe0d0c030302040b0c0705040b0303160b090102070212030d0b090601090317130e01060f091805070314090109140a2111030a09090e06160c0f1a2508060402 68
    0x710b98100c07001803103c488050303141c1c41640d00b00d64071074a0701d10850748134074240309400c0050326020080302c0c00c11240032141c4880d0703030095550030350081006246410a560a202d0000036888400344c00e0840e41825001c1c40d600c000054a1200701e07181c1e610310a015454500c2004120303600800d00c1400d1b00d40207031201d006a1100030580f110380c4513040d500e1101510401c40052541031942245050b02c155480e42614401c200a040f1080703d464803840d49240c0d85d42d17403114440380480c2d1065402020700e280108000c1c0d00d12502d0b120a0344e042d510018213030f43d6044a601800240c0c0a605a100c0381c04c0c01400520081e500e4520b03030003b02008100008445580d1369480500800917200d003407601405407900d401d103404000c1c00f0850f0394803581c64041d00f02560002c01c80b5002c9101882032920383c2d41c450b4941c44070302084400d04141d02007110f2000b4140180030125403005070440c1808a4002c0410700c03480c00048001600c01180c03402000000b010141d4840c49801109040c0d20150a03240180c940311 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 945843453 1250 945842203 945842207
    0x60b03242b140115080111070201030203090a210f020111040e1f140901060c0c060f05130801200307020c06031003080a0e0f0d0203062d010e06040b040e0d0c03 70
    0x48540042a0000e00c982444000406412402204942c1401c006040d0355484c8001c2c2a503a51f9020300e50003030800c201610043d030107079002c0c1d50004030900445610f10f480b595008400c825590454600c03145140400159a03444024a1981c200e5407001b071103186e80000840e02a40114040e003005c1c0c007580d800040d0094140319580100660b4001d06100e1030341d964044400414042c200310340070304540c90010814500549a01c0101c0f944010103441e8589844c000302c4484130511281030402c00208014480780d1500325841000c2c010200000589881b1180c00d2380c10403218942a03400000244200002160041109c2d02c0310355095038070700da481d59940c41c950b01e0380301d03a07400040c000c020116104007500d03440312175815050829110040f6407030106081110030104000020341c958003000000c1d601050b0141c0e4001e11b60724004014041032000b42800b80b5941090304941101010070302001960314003409031565410098030104a43e083c1842910b032148086080a0240210b4010381d40400d8 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 945844703 1250 945843453 945843529
    0x70915050405010c140f0a060605011e0f08100519080712050d0c1502030106030e0c030f07060509060c0718200d0b0109030210020d020f060106020d0f09030204060b0324 74
    0x10300c1744407e994150f48103241c140d004000c2c0b0301805000900f501c80e1000b400306080c00b1043c40c01659155034002e5107290343c1c11122544000c0042c615081c1002c0d001890b03450713a0300002d400c1e40c3c40e0305034505458107003070a46150015581c02024002140c0744e000d0b010074804140d00343e05a11629000b0016900ca082c0700441504010986100e50b100100000d800c981c1503002180e004d803038000b42c5100b28a00c808040c2d03103030b030310300300b80e04480d000b8220401c032a60082c0010030340340c0c00280c20743d8100b0380d640c0e1180d1308010180c0d0002402c50011031000100100e14801d00304040100c40303403580c0d80c0d9410084a10507000380725a4001c55941c88002c074501d0380c02075401200460380101800780c9420b9405009464040d604040310151040003102c1e41c171700d04041101410703100c603980281200c1168074000c495400507540c03886c041c48420000480903854a004003009815401c105690704c0c00c0080c041d80c5005071484040c041c09015941c40c55103a9180d009140e80c8a00c85070342c12010440001c940c3c50b002c = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 945845953 1250 945844703 945844723
    0x60f160809130e0c030a05100e0a081318060b0304200d0c0918050c012006070306061403070c0b0a0f1a03010c140405090a0e06070915050405010c14 65
    0x31580030705222840301d07550800f40d0701e225a40c059504004108051513516251324800504542000b000d0507107190466010243c100180022200700c10000d455010407940020035003e58040100c8050282422002c600c0d00c424032402410081a440c00f0b50342c01d16400b010700014002100d2014070701444100e02c00c01d600c00e07007004101181d084074524000e2110745003440788000d02801c140038017070b149000110003080a60094040c0c0514800d1000441c1c14181c01d151850000c800c01122909001041002d10b00c0f440690320001501401c201d0054035901e440711340c544500d00104100320155600512403040140d001218450f1038861451010181041501c50043c0707610744009110050385108030486980025402088200312080b800c841001a11b90b080008803420001080b442c1010130005600100341503001400012208185061483c2501e443d40010362158040c4100a54620501207004290425518080ca4500082c01c8003140c428058246d401d82c03416100f1000c0180030f00c00312 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 945847203 1250 945845953 945845959
    0x6051005040c110d0c0804030b06030115120506010f03051c03020c10060302190302010f05070503041715180a110d050718060e01030206091c0804061706060f160809 72
    0x156030b0340c0b2800425881c00d9010b8010307540304150782c0e410198010000d00c52900d40100d02c4a140601f180c840c00f614101c003078003151b010342d82c401c98000c0301d504100c2c0c040041c0c0103200030b80c821880e240c20481c0c6068010707000a2640042d4280400000348006580203092070200c820160410740c900c01a00240142440d54031070303000d44e1045413a01300181d444403098a201301c2d034456017945003142e515849001404000e000c02c4c28506010000ca00070005442124440e800300ca00d020b49400203040c42c0c0840f551904915440030b4030710722840149a41c0d0550022038020351241150085101e160303510140e1001401107080c445035042140c8806e0407000c20160007100312201030323030703079400001e844400b5903004603545141440208005034181c14080c12070340c00403e0203092070b01c150200081407036465800c40d51031081c007100d000060070f8000540024491a182d45d50b0308140d0b152210a003100050040c2d128402c2002100c0c016141c1006035440110410b030504072406051503c02d00a105045031103038 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 945848453 1250 945847203 945847211
    0x2120303010b0418020901081b091009060305091c0507080d02040608011a070c0605031510023301060305090f03031609050d150c090521010c080408070605100504 71
    0x101c000c0b0038030003032003103460910b000604040c10700950b4040340610020540007690020100b041c003440a0703d1402c80c0361000f0486868140c1d017800103154a1042e414850210f040071104028441d05481540d03400826200074002205100c4d00801c00300c141c1e0603000c0c09201c00032884c80144501841a80c09111181c04115600c6403036000c003030b080000034071800f49000110b15a000c80d8030698400e4030001e80d449200501c46c0c41c20008140c3d01500001c210314079a0b503188007000c2c02ca513a5400c4450800a0759009000003140182c00000c182c421100801620746401204144001c248085141103841c64500000c40780c075401c0d0005e0400c1410b001c00300b058030001c014403640441113490300e03409c1d801e02e803511843da40e9104103010607000d5249025000f4240080c5568071f44442c3d800c007240c4510a490121803280d11000010701d401450210390051076010080d04040442c00d10403480b104443d414502213900c1d16a6400740d880c824100010022600d502c080b800003040050414040c00340100140 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 945849703 1250 945848453 945848459
    0x5100e0402160b090d0210020913020307230405010203120a0605030f0d020d1407110319060603200d03050706330f050102150c0706140708060f0a0905040212030301 72
    0x7414010800350180d401142a50100e840b428000510840070311854000d0687d016400c0c400100070742110389140d8001e03486546074186001030388010352040300310707803501d007005003200c210104030034080504041401420401030002da0b030000143c03034a8912040f208011a40c0c0c101c0340c800900390640c801505441036500100e035000010600c2d1960014640c2282c11403082914103e41c94200302c01100d03240300007080402e0202d0042011402242005021981a030302c0280700c9200d5860312040c00c3d1421b9a40310350600130401803009000d0f164158401102445180e4400504210340c008402810321000080600411015412581400c9000444001c00891140701d0b0708440c0e0b001d001d10000d559001c000030400d41c0c906003803107080e10810f81c01001d44a89840e400b054240000d440c0c0400c0407410302029001461300c1c046d80d400044603544100300c0782401d0b04090000704010781000e1044500e250b10510b0b544500043c501251915031011545031124008148400540c10b841c0b503403800004008 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 945850953 1250 945849703 945849727
    0x60a0b0703120c02010212060127081b03030309030406121503060b131e0f200c0f010902010507060911040f0b0f01050f04030809120307050619051005100e0402 70
    0x20920b041d03122024400c1080c0e0310f8049080744070b800c5080605e454400c0102d4080d510440c403c030711203402e120300001d02c901c000141840c034000c150320543c01c61340a509441c082100b201400485014180c00441c190704010b031300c0e00e40703a006038040e54007040140e800d42000c944e601c4d0080310740400d0301d00151102c1910380c149070025110001c0c0c2203001d20500048201d0640807841100b00c120081c3c03048195140306404038001500c442c01c00060056294030000c1c442481c2c9050541203034402c003c5640d40d422642100703d04027000c91001c00e800e82d15040445000d42d80003c125145954010000250900c007440d0000d080300021151681003441c00007030b007000d51400c3d403003480900340c2202c40d0f0b01c0d503d480000444041c4036802c80c00c0e100c0d840600040000658840140000c004024078130041128154001491500702400a640341d03403064081c040b0301e00105500030300c0710f00040000d11441c40c2204a00d04450154030901d80a660441301d0801c0c0e05104e0240b0a20342d22008109640e00d00c44100304c = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 945852203 1250 945850953 945850967
    0x31e05090a14030c0703020103020901121d0f06070c110d08070303061701020a020c090a060812030114010f1d0f040e0604060506090f0f130204050c0a020708010c09030605060a0b0703 80
    0x1080b101401840701c0d84a86900002c10340d5280c40e0138030010403c80741551700440183d040040e08505101c1c01d00c104180f00105406161004980c80c2c44100981c0c0e40110090300d4094100d0303504030560000c41c1404440780d40000003040d6240c000081d60207095051020a50a62000700060440e24000c43c280d0109540364109800321042803108071401031010964500301d00c60000c008000d42d114000541c00d40c2000b405031076002403401000036034295100f0b102e41c142003901d4110724240c1d20000040c400d0381c0c05c18904031f09241080c80c09035040040c4800c09008050708040f02e1031007008030211051345503100000b071007108401400c00e200c20040c9059299941005840071601d450526002070b40c242020b00116102e1a004c020030200d0b51034000c2a00c0c038401d00a000f00030303080303030481550740562203500901e4051814885070903556486032a000341045a19002078078180d0406000d01781055104403400d040e03035004140000c4585850001480c001e20a50160346006d102180210a0580080e6 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 945853453 1250 945852203 945852223
    0x112020a0807140306031b131803020d14030a05040c09020c030d061d13080f0a0507020f010f050d0209030c03010e030406180f03030507020d0c0e0106020705060301030b07031e0509 79
    0xd8042c900003d11458594500044a4254142c1c0c4003070800c028011803940c1116000c040906103140791400c110308182a120226152002898640080410180e04009880ca5402a0303e88002c0d000e5601c1206145440080c1c8060b1030345850b8800303c3c0501029400c0f400052060800440d95001d0200350183c0300c2d008040304030080342c42c2000008040894040f01d4640310f401c0014404e06603110800421070054a80007a520b2040034402c005403203903140020111b2200c01e4490a40700c1c3c3d46481003142c4200d0700d081d407a041243c00c10103201c540f600102a11110685410090b07118045200480d00c2d20003945100d507419828802e1016140030044000c0c4291106603480305800d5100030300c00d4a9401e000d125100d002d1440c2a0100003081c46080a0940d46200422901c84200c0750b484100c22038404e908420003034a101c0e8010010381340c040000000800d8103a4080d411907140d43c50b007011710b040091008090545918a09070900a0210b01f2002010203003c100880d080013044550346085600d = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 945854703 1250 945853453 945853457
    0x4090b06121605041104150509121c030b03210d0e060108120d020d1b020d0c0c0e070c0b04031d0d150b040209100e03100501150804020112020a0807 65
    0x40c82411a00c4000c0b40c2c12404a01c0d031491408214544014030008100d050300440d400030080c0702c0800c03021400004082c00d07041e80d0ba038050312480e4000810600001e803c00c100020b900c560303000b00c603000d8440380306406240c450a00242c01c0d101c81b800b081c00c100060031080c168464500d50390401240076005031891182ca4001006400c04000206568140030300506010f03500c20002207100b08642401000e0007040860302506005e140f02e0402c0954080c481a00d0b0380454402d0b80310790f000e42c1040604594240c51400460144440d201e040c4c803000349001c0c1c5076024480e900010f003c01d002d6522101d04035031041b11802c0351700d070900340140f0707210110f10300904901d812603400b00140b5100c03c0513903030340390042250011118040107000040c9982c0001940140d024040c1d20b2481e0303142c1040c0344d04042c098682e884000c040800300b50518040c9130201701010710f4580140031940007a1a07141c4066403509184c056a29a4001614218141c01e400f521039800041c0d104800e5034058080ca004596507 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 945855953 1250 945854703 945854719
    0x20c0a060c0804020a1e051020010b06041a04030f050f010e34080d030b040b150a0819060f140d05031e0c100c0801120f020d080904090b06 61
    0x807000310350186043d10080d600640c1c40c282031140800d1180d50011299501803100301540e900d901050980155041da0300104005280b13045100c0d09000305806096075100081000b1050780000030014000c7d40140c1490b0002e800d041210600c1400c2180e0203150824409810b0341e10911f40b0569803580404440394950038074064404241000521102840040c0302007044003041148965018006840548010038074020000c0c40e103101740f00c2d0b540b4090300c555011904082d944248820fa0707120794605400381c0584a0b44141400040c1c0598501c0d02141c9400a00c1e0b403501402320401c150310b9001c1c2080613103048000102d10501308070346011030f0602058001d40181c0e9030204455a42c2c001e01c041c3c500d40042000015180440c080c0782042041e02451a09214254002d50b1802c1441090303040c90315581c10151807030035041508640180003003d0060045074155581080c2c01051203c001c0c0148c0b0004458002c1141d410203070380000201501c108041105420503107080c0724203540b914050f15034 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 945857203 1250 945855953 945855971
    0x20a08070b1609060f2a0803011505070206251415010803070506040209100f140a050a1512140f06090709230303040305060a050402010909022a10020c0a06 68
    0x140c034403d012240c41d9100c0761300307030020048152454121100c2a40350814041c004542014405808005140c01207c06c43e49a605000703000719603150001c07001060040c207004903c0140d44200441b000118081828500c0660b0011907614641c88540000d0425a000780e0501201d0000a86500ea4900410a071510350340c0c2d03843e0b4151640308400015149801000014000d410700e604815040381c02680c00143c900c8c4d0303c5000e400904042d8000300220f84c0f000107550443e15040e03400e500980b004a030824813031440c080c00c00c0c4074188200300b50000d2165034030740d420fa603d1055005043d2007840c0c41b003410f80c500e868140c00e00d410b04229890351184c99142c0120700d615100d6004642a00c242540c1800701d0907200c1c0c6034210f02c500601c1c506600d0f2204101c04800244107001e294010b29903840c2c00f26035420148009403842c00f69400a40a07039105000400c0a16810300b85801310903204421400c42400d859205802e24014010382030034640001504411040b00046802c140e6009800c20002da079a = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 945858453 1250 945857203 945857207
    0x20312060108012919020f061608041403040f080c040501090204140f060c07170c04090305270a0815090102120f0718060f02061602031801020a08070b16 67
    0x4001e014101c405044110440303002d140c01e04c0c09081101d081500c16080c0130440c408501c407000700b08a050016040700e0b080d5203840400b04407040d042008660000300105c1c2010000b000707075400030400f0345003610300400e90514000903c00c5602418078003216142d80780c3c645c000c90380e80341000b2840c42d005600c0d02d000000d428005109507000ea40000c031b0140d004e501000c0c20844610b512406055018a04019441c5130380400c10203080100800f607054280c84441d482d0490808030182c407054000c5082218003030010f41c1c0402281c9120a15030328118000080d003840c0c0014408460170190000711707001e0b010402403400034690690450080c2c51f55816616000c00301c0c03c0c5d00a002259610420303400100348585c041c1442c040d880300d223515086040d210420503e5207003d0465010f9004100c41d100154929030381449103507401415401d0380d400c0c00d611928029920b11501a210501d0104101082d000361310900c5590038264110050580310142824074600180e01903602503641040c0701c2d00c00850074 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 945859703 1250 945858453 945858467
    0x40605071205060f010c0c0b030f040302071208030f09030d0e010e1603331a010815030607050d14092416031e09110a05031612061401060203120601 65
    0x1070181204444e01000640754594884012200e402e51a000411400d038440c016602c6400c03000c0c164070351401c3c0b03810007174100401a006410b524114950728004204600201c2e0b82082a200170300a050341c0d580034403801e5024030010750031010300b880800c80800710150423103075141c034040058410500030810801d5a03800b543c80000d0030b20b489540801d0014940c030039528500079000c2d041040201d46401104112410a040340051084000150701c403541c0c010051544a8040460b08414055000c0060356a44005041200308040054100091901508502104c1004081102c09414007441403615105480500d003c4144119102003c040e0103510a40c0580294110060030081140d03040b03000d01100366120204001c1980d08104004952150f2081d850050240300c0090b0b24500810819205940c00207109a02401400c60a80880141201250044100354035918103d14001c2c000d840803000032002c441e02c800000070b44603000b10082c01e03280a13120721840641d540c800151011 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 945860953 1250 945859703 945859711
    0xf030806010e1210180c0f03050d030902031f1b0306051f09210b0408070605060402130b090a090608061b03010b04170f03041d0c030708040305030a14040605071205 72
    0x1a0b200580400141303116a000441121408080921034101d030344802e444483e19500c035440118000504000f8400c05000400300100e05184c00d001c0b0850680009545181301e88031120003842e0812455140515517205503608010030b581c1c07062482022002074020035091040300d0058001103204003001000914202c0001d40b1034a40710402424039400da1900c0c20701403074031500728406940d840041103440326100e100328441d40030a80d440720a403802009550001d4080c030b000e00e0040c4112a07003040c00143c00000d84900401080d01c40c41e840c00015105105070b0300c00c0d00d0b141d00e44900070560010102c0c04900c29461900040c004042240c1791586503c0700b4810482c2508049c0824000400ca108514035a403100c1000c4034401c0e80313600c24840c11580290700007034050aa030300080c9000301000d5811984240b10802c0070342140b4140501804801000f840101040070000001780c401a00f6841300e9000d17000210544c07101d00d00303468804c00600080da21040407171903c822040203290240601d40c81 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 945862203 1250 945860953 945860989
    0xa0c0801210b041104060f05030c0a0e070c031202030a02030915060d0210030f061413050c04050d080c0d031a240c0304090e01020a0e011404051c0f030806010e 70
    0x5060080c0d100c4803900d00018008072141a5840f4040132150f5407801490041c1902c41d03002c4915600d014101032400b12950300c0140144140041001a80c084041d03055100c03c203401d0080d1302e0103561070704030f030881c0c034212410903680c1c8084144181c1c0801c03a03000d14461925403080b51403108220700c4014180004550141d80302c0c100040100042c10700701d1440b501c2000385c3c01c0110780c06074483e0441080d562503410035924000358601803c0746181401c03881030708024901c0c041099040007a034012880c4128001c1d0340c0260032032181c0104014080007211724000c0c0c2d0354190b4441c0411160020042c0001c0d4120414401c1c000503055814640303c03061500c1c4003020744105042c0d41050351000c4e801d4000c1d074051440f03030106100001c0c20440c90302480840f0801e010005956803820f082c0509210742c2c03101001c4c10029220680881403110304100c8060343c4049618007034406403000c21000351000b40400800e00f03220b5028010805800c4100305018410980b070b5101c501038002c040c0001c0c40c40c65005500 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 945863309 1106 945862203 945862259
    0x105040b0709120b06040b0a03081611060f1813180204110405030604110d12172a07050a020603190506010e0607060f06030b0a0c0801 59
    0x4050061502c0707140c3e54030440e0702d85149000c0c0052070140126a03c44800c4c01c0b540d9120035200c011640300d80019034444212440a29000c00910308035612040e2495030480351406400341d81c82c60105d403c0e82410800c81c1c1459907202c1c01c14818803604041012002541002c080c043c2c2c0011219103c2c060a005c503141c418441120034920a421490206100600030340e80e000c14042d42240d04007101c80424441a0001a86c5112502c0b0060035041c418506008142e0401c2123089888500d03050300040340c0d82c403400c07580b42442441d042014040008501ca03441d03080c1c40090041540500111801d022440d4007103441980203881405180070a40c44803681c0c80f0f114080c031a4801c200b0320b030030908000c141022907200d0240c50001040a92a40c3c02c20107440007a0788010000c41d0461803104017414191800001024000d4048000031442000443d6900041c1805c400d04802508014 = true := by decide +kernel

theorem cover : BRFrame.Cov 945683453 945863309 := by
  have h0 := BRFrame.cov_init 945683453
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945683453 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945683453 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945683453 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945683453 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945683453 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945683453 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945683453 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945683453 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945683453 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945683453 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945683453 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945683453 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945683453 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945683453 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945683453 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945683453 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945683453 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945683453 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945683453 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945683453 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945683453 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945683453 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945683453 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945683453 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945683453 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945683453 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945683453 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945683453 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945683453 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945683453 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945683453 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945683453 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945683453 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945683453 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945683453 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945683453 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945683453 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945683453 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945683453 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945683453 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945683453 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945683453 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945683453 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945683453 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945683453 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945683453 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945683453 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945683453 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945683453 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945683453 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945683453 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945683453 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945683453 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945683453 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945683453 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945683453 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945683453 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945683453 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945683453 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945683453 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945683453 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945683453 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945683453 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945683453 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945683453 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945683453 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945683453 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945683453 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945683453 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945683453 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945683453 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945683453 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945683453 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945683453 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945683453 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945683453 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945683453 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945683453 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945683453 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945683453 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945683453 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945683453 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945683453 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945683453 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945683453 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945683453 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945683453 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945683453 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945683453 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945683453 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945683453 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945683453 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945683453 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945683453 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945683453 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945683453 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945683453 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945683453 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945683453 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945683453 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945683453 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945683453 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945683453 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945683453 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945683453 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945683453 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945683453 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945683453 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945683453 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945683453 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945683453 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945683453 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945683453 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945683453 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945683453 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945683453 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945683453 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945683453 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945683453 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945683453 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945683453 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945683453 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945683453 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945683453 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945683453 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945683453 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945683453 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945683453 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945683453 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945683453 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945683453 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945683453 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945683453 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945683453 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945683453 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945683453 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945683453 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945683453 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945683453 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945683453 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945683453 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945683453 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945683453 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945683453 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 945683453 ≤ n) (h2 : n < 945863309) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
