-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2064
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T05:34:29.801299+00:00
-- url     : https://prove2.me/submissions/40caacf9-f0f1-478e-b024-9aa09f6d7225

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 371043165 ≤ n < 371223021 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 371044415 1250 371043165 371043181
    0x2040b0c07031a07082205070f06090f05030c130f0f0207061407080c070201141801020d0f050a030e01020d050403111603020d02221a0103050a18061104030b 69
    0x8001d921003a189512000743d2101c95140b10702203d44203030659690580f1940d140800f2442d1810005048500b2074104100c0d03200041c420010038014050102d8100611480e0000041c040d81e040d400c545000d44940030304100c01e480024000281010403114025500c1d0103001d400000c1207655041a5514200044003a10800b542d0080202c04d00504061088181e0002800304014099070104001442c1b200016000c20022001d003090906c1403401020015080075a072045820140b036200b02c0301e400c3d243c3c0070303030030341e010001081d4100d490304220265103640200545035000e2294004203240d1205c5c04044041d20a604661404514001c104114103143c01c00610f42405040000390038420204505031149a001030038003102d90082102d110320840d982840880f01c003c5130401468034150030280c1041c18140125003a0141011707216000440340303800182039074000b0340340b049032a00c2d01c2100d02e003101507130910f040d0298200f90045140c40d84541050510300c03c550000d44640401303003e0242074 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 371045665 1250 371044415 371044423
    0x15031b0a030504060614030a020103051b0c15011e1401090510031e02040e0a090f050a11010201050c030702061b040b16020f03010b030a11011b03020102070308180a02040203040602040b0c 82
    0x203036004184c100662a15007800b46046030110080b9030f49603000c00000b4005600c2030b003040ea4401c25080c2659941c1c440c80030388148940046450305126000110742003205c180440c0e42c10300412032031401c1401022004003507051001c182c000d0756104000d5480140590340106040340040c0800390144400078001107008004002a200c2000140e411404405001d2403038000c3c0c030150307101c6200c2030070031361154000b241c01001203440071610f00c08004090710124505104800881e4080c0906185034585c040c0024211603004069008800303083c810b0120300b035800100550f05c64101c500b9010440c064501c0c000050080f540308440417800005c1052038070104603408104244240c4281c070170410b52000b05800d039801080b50f580c241d80002180700101e410b072610f00c1c50103201810820300040006190310041511240240c0c0945e4002506004265200e4802e070791110071042d0868100456565260300d5101c4040d0180c441c4e1380100c0414240310b400d6046500800814104a507a02c1d2101c1c411611 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 371046915 1250 371045665 371045671
    0x801020a080106030b060904021e040e0a0e030301031a0405010603080d0b03010e0c0d03180503030a0c050d020606091b0f04030f200108310b101415031b0a0305 70
    0x80d9003100029982c1d000340101c1c81c8030280145010f0801d01031f98203010080d040661101069000c1510702025100400020006080d0550789141d10303142c0b010889042c0d948641000c1030aa0040004101060041c9000d801a8650000316081c42e240d03400d15902521040d08050581d040010b660301c9110305540c411a6401400e4000b400784c00300001d200d07500d901c9c0d491805a000902c00245400181c4290400e040b103d28411348040520f0701d805c0820701c0c582104a8010110311090300308814410204288035003060a03100515451802d50b020458904000d480304600b8070511a41e883c0303124840c01602c0c25010724190391074840369a410a121041c592a030151840314140740404003031040038410741d01c1e0b050113031202400341c0c8a035410301d082b102904002c10a01a11701992091025400c05003c98550003000081d01c1420400980365003044d0541c40180c0554100314401500c3c1c03540d11b84450b180d01540700311616940d03034600c0c0c601704180c40705503c0e0b1501c0c00082c90030500d0360142d00441c0 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 371048165 1250 371046915 371046917
    0x1308070f05030f060a09080c0f030d18030e060903070302030f030405091b0405011b0503070f050706030905060f070315060302180618091b16110f13051f0801020a 71
    0x24440d6500c00034540c850720700d03648680107600f008001841707007900d641015030f409101724255440c00301103034411800c0020003544070400d44c10014980204503074600504a0600642240c107003541c10580d00a8400d4584103000c031300800021440210581d01809550011034000d070544a0003200c0115917902d0394003c0c020700f840784060b000400c0102e1a00c51a446089095203502c9140c03506000040d2070350803104e409840d41180c0d5240c40000110140050a8018450148050010080d1030464203003c0e66410034000c040c0f904010700e0119400280c25600a240c402c038228058490034401c4004d400402d6404880b00300c10100040d060f985a8000c080310758151204402c2d203004402080304511400c041400d542030055080c40407407030107007295070300041c000a4208881c82d881d9002c0743c60b074010018100d1602000b82d226028445a5046588400c100b00c60281c04003615000150340c0d0100f05000f169100d82d21400911300c030701040a07040e079001e200c00c07804142d29a03500001e4080e601c401030840c = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 371049415 1250 371048165 371048189
    0x1b03021603120e0a240c0917010f0c02240714030a090501060b07060b030d2f011505010206010b2809081504020f090c2508220605090306010905070302130807 69
    0x10342102018481c507a1b40f071a0550701d201282d40f07052403e180802114104c04c00b00d550700c000300350900341d90f40306044640340741380c0203041407090f203000300082004074942500c0000759038010043d0070f035030028170348240c4845074080540b03a46449c8031040081407100b00081a0b5882e1070700104183c04940082c1c2a030074400c03c0c0501000e82c0060074562600c514928a00100722000d01290b19082e001350581c080704490074015007881c0c080f0482609542540d492030354415001d4405000e50359061280d10302501c0345900c07480c0351604200d0502c2000c1400700501c044a501c841d0500000d42c418411003000381080400c4a6080c803800a00300c500700b0b41030303900b00e1088000303048585890400c0d000b418881c2d840c220120307090a40c002c803080c2201a024110303050324100b40c81810009507020014100300d00119100f40c1c01d941a00d0a003000c0002290004002d0000900c880b80203603800103429415031300c480034041119251800140c019003d2a244648600344140c00400c00c3e00300006c01c0340c21128825a0b00b = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 371050665 1250 371049415 371049473
    0x50304030b10030503070f030e090c0d20090418120305150913110315091510150f030f020c0a02010e01030b031902120609011b03021603120e0a 63
    0x152071010054407000b0b040b50024021b0101240324200003c80c501c0c040e041040d103010000d8001103903088102c9200c1030b101d00201c0c0350113011805220b0540e030b0852215401071450300f50454002c05004220409210719200c80034803040801840001c0d0200e50300000c5041c101c002010041c000d0201250030310700492051154000c1450101000b9014513500914003a0f400000e842311050418446001d0b5050310a141c0007090f0040400b15652107034043e8005403819801e43c91381e407280f038000034110244911100c0d10a001c190400900c6032030071660760611072030182c50b20300c095024183d9085401d5015101196003041010701154034808103100347d882d03581120a00d00150201c4000d606035941641c0030059003c4551048803900e840300d800186102030280c0c000c200a89406803c64410005944803581c0303000544000044811b0800207040541c00c0c0441d10b07000b202c14150500018003008034000c0c00d003d0a528a40c0f011001c88016000e403910084076003401d066180764407010040c0c519000c03c034 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 371051915 1250 371050665 371050681
    0x40e190f0207230715080f0f1006080405160303050903060a060f03020f040b030102071203060f05101d060f0a020606120c060f0f040e070f0906230412050304030b 71
    0x8035611150b00081180700790103d0b820b04888005260b0040030355206a200c049441d440c104190100000255240c9200d8a091112440980005017195101170403813418016a0400d0210580946855242100d51603589050548c942444542ca49010999901020061540c030500030100f10400f0381c1103840c0e030780b2512100c00807120944903810000b02103510500043c60240700528203050f006102091005032800000d08a90103c2d10071144528646226140250540a0312000b0980f81d21601d64052900300428418a6402c20303103020410f4a40c0ca0600040e05818035004021000e0006a00c2e1101c110022006910072080d40025204000c005a082d00c1c1c5104030303081100c07070f0b800541540400c0f5024880680c00c5840041c90354a8144007600744100441d028000509110314001c8060500c95005080c0c0d80c6600804810031210100900a003504010501c000413990305580e06114040c03003154640e402503401081e404040211b40000380309000000c1d0064074014032110340300740c0f10105 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 371053165 1250 371051915 371051917
    0x90b0a1b0311061807060f03060315020c060108010b030a030c02120a050607090b07350304080307170f1f03021201060504151208090d05011508010e07080c0d020303040e190f02 77
    0x7018613855005a40c01e100c0309105040f00c40c1d195030f141c140444d1041d02c0ba62042058900300c0800c402c0c103a40881d0396103164601f080041d0040501d10020400d14880b14042511a440010003605000300a2030700c0045440b003a0384043e00c01d1041c015640051220301d420703501c2d002c0c10394051000a601d82d40101e801c0034140d046580c0aa40010078003040c140351110010500c1d04400130001d0413070020032031240c0728401d0004600c0341d03102c0c4140c29640c1c03600e514003400c01c0c51603003c2083e440c000e4204000301034031200c101031380001d030f0354081b100b528503000c80648915000360002900300000310203004411205400910179684203c45c10700c071219040c1d1481094448034441d1403081410820f000e00410700a1000b01403106002d8440390185440d9100e081c01c4d42c5c0022122011954040010088034000384144408040120050312200c0d103070901c016074a14005040300d109a0b001390b84442196000c004403002091110340601c0c032840d182003140803071303664280807042c000e0611742041880c40301c0344 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 371054415 1250 371053165 371053201
    0x7020315100f05220b03060103050c1c02090a050613140f060603061e04090210050c011d0a020f0d060518070608010e010603050703061a0711060a090b0a1b031106 71
    0x40e001a02c0c1c1d0005080035200d000104c240b00108a640b0260310440361001c2c0480ca018500407002441444040740c14040c00440c40c10241d844030714200d0200006a48040c0714540001102c207010400c1c0d116840004d54685447c000104494034000c56045104e5010000350300c0b030700d410500308240303544030b03428420540f0044480c954030010441030051300300341a1500d846a00d0300070b0b100041002c4582e011420b4141654502c1c000329001140360003400409004200e400c182c003a0507169036494018550760f031030608a1000344140c01c02041d00d01651038240745130003100e0700504140610705180c03c0003220820030002102681c0580c00300400c0c00d034001c0d044241281c0b803055400d81644c2c43e0040132001000060f000c43e04050701d03014006075011694620041407180450025030381c10140c9000603010704007207003140c0101814040d02e04926001100d050440d1700001c9119a03640720100215005440c3c0070001e052003000e10300344800e0503030080300d1a80c0e0034081c03001c40304152070708400d040c08a0556 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 371055665 1250 371054415 371054419
    0xa0c11101e0501060e0607050a0206131e0501050a14070c030b04120201090308010312110706080105042003160504030605010b0a260403120f06140a061b0b0c07020315100f05 76
    0x40c0100e5050a06c10001c010980c0140165074503072905a002035007541c4a2994140140c421080500010840003065102c0d42c10041104564600c2d11002a107140a18810141441040c106590925a03c14101c980e095440814061034948903d40344a0040d03080e81c080c1d83c1500c0703101041405500501c5901841605522142250f170f203540d40e035549035081c0350007803403c0001c122071241040c074080054401914140d10760602c65810841840200e80c210210b1429584603481400070004410049a410031170422210004090151080d2803030311035a400241040d01d800c00005150314042c0c06004040495a10161001c0302452651090140402d0400100403c14040b03000039008182c0c03103543c1c40c5c10910109604002e50710040840d0a00c0d8040c3c856064000e43d0b81405142000f55480588501e05003682641d000c210200000c0c201d0f068024805c0d40c41c1400709880e01401802e1300e41d03c99004044403103900c0424140ea40c655000c1e030300c001c10790045100c04514050307007010740000e031140 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 371056915 1250 371055665 371055677
    0x6020c0d180b0901090308070302010f18030c080903070f1e05010311090d0201112b0f080a050604020f0408030703030605040b010f0503040f020a0e0f0a020a05030a0c11101e050106 79
    0x70003480201c241d1140ca52103050140700fa1700000019504405060214040e0b000000c0d1410200a400d003590480125035010022480c05403001a8100ca200c01c0d03c150030014441d00d0340e1604002c40e180400c07607084102d40d803071603500002d00340c100a9090301016100741c42039a502a6160019419034041d91050501620184260b00013030515125400003640140341c0110000b20b41d9007814205503c0b41d86c801d0034001216a074155000320f03a45102240f6600c0c1c50b0000911540d040c000304550005070504001c15140c8010484a96aa8059400b00030100b041150b48541da2402c1c21b50ba5407060b5000c802007414280b001445180c81d10880d80c4c082e8060310340036940307001d820702101c80d0360004001301c5070703045e00e111146c0150310b42d420035802400c1c07000552401810488440610070b8001011144514010001035241075400000d59400612021010510310543c2c0c600b655480700841042c1c003c1d10500c00801000c071920380041c8024100c40c02d200c00c150414080d00e40940c0d1003400745c04080b0742 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 371058165 1250 371056915 371056919
    0x304020604030b130213020c12090307050126180f0f030d09060f05090307031404080a020f1305070207060e0f030a02220c030c0f030e0705190905010306020c0d18 71
    0x1c4070f81c102a500040944c42c0849400850b400100203100100e4841c1543d50b020801400d031484c108450103180c2041400b0030301305506c1e000080e981d0b0701513005072410001800c0341c4008090700343c40c983c2411103184200040a25101000400300c101d00180e81c0705610620308021380004000c20b007a600d240a1700081c40c42e10382010801400303801c0344c80c411a00107a0b6107071079591100303031881154000c0c1c18050286a98100604004004c111702490011034440100410000c004000640389103051b0f0540b04000040c10303800008180200000203030781c2482c18001000f0510b43d000c240e20301520041d488410203107188109102110801c8050180c141c1e000d00700c00740141c0f800c08a407400784200c8800002040f50950045401d80700d10380880302c04241c8540002c52119003201040311501d0703007490300f0400b030031400d0111980c0b42c07864440e050286511100c56442d107031249681102400c1d103e4014401540e6074504040250b1009510881600400d00c3d6100d102c0d05c51000409116102041003040318 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 371059415 1250 371058165 371058173
    0x90506120121020a09020d1103220f0b0405060906010f0803040e100f0b030103110d05031902030d060608090607030203010e0103080c1504141b01020a031d0d26030402060403 76
    0x2458010b9104420055a1540050740c2c0e000a00014001020000d0703200d0785c04a0b042c04c2600c441c80f48011a100050041100110000100030000800310742618122072107030070084400c1c00c4000c03014041542030820081401710009419012355480011540c1507030b070310003100c120540384e40030381e90480d0020003040120601d17030401c0a402c002407605400030f088d5180b5038680c144482d41d00115070b018000c40104180a05189a8040c3d0b01060b80c00c0701c03000c1e030b80f9600c26449114000761808504507030348040307550034030800644580d244c030700d9000c000071501c07248041d10110080340c41146038803d007400220110b110f4000d69040700d401481c00e43c3c2e03d07400c0da92082100d8008030310300c8070a84900421040c2c4541039070402401a4064923410314614403d801c12810001c05a82c1c400e101209402587c0b6240d80c0010302c5c441480d01442c216414100d540c6030082081c05401400743c0c4155011a81024460341009040c002c162150200038100c60101000c6110b0204070b4029600410070b000410100f = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 371060665 1250 371059415 371059439
    0x10e060906092125140105040603021305060310030b150d030c080c1e0d090f170c0409031e02160302040c030f0905010b1302120a021b030c0d0905061201 67
    0x241d607400b107010418081d00303001c01e00c4d0110082c114108803103880c0c0010f4a01900b602c0e480c001e0804116110f040803030ba0400a0890300c00d520516081560000382821110308981000d000f81800038003140c5daa080910703030040035414900084d40d060440c0b5002c030340b660425010001488801030800441c80e10280c40564200510b070005446240e8204410a40000709101b500301880d0b190041b501d660340c01c0e510315464040d25140c00c805000070b1060504c00b41c186103071514121820a0a800058940600d0460030800e1200c801030700f20307091601e10010190032400042174442241c10084c81200208001c9035544100c50079101c01e8620780009001500f070a030001140030880e410041840c0140380000001c84c0e01c0b07030000360f80a95540c00c49881c2468030000505140400728015814241032610070011200c014081c0381e0255400150201d0401c1071942038102e13120f001c4240ca44908031079080c9038036035980c8143c00d0005210340d500403030249460003e503940501c0c0006059041d81c00d01c1142200c07 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 371061915 1250 371060665 371060689
    0xc05131d041211030316110615041503080c0303011d040309051504080d1701350705061c0b04060303020a0f03110d030603050c0103090f0f020a0e040809010e06090609 73
    0xc0001c0080121030352442080194000c21107003081403018900c2d080002c020907003020000047c1e40201c010f12000b20409180403101600403900011132404502c0307203d1020701150300c0203040840210300c200042a01001441c102c45a804030106201450210801c824000300e50040104205441c14131a50500c02040342407220042c5000c0e00c4d040c0c1300c0000602e03100300b1560610003d1141013044494100c01e8100e54010300b0b0000c401040c800240c2c41c0c852041c0303405010342d100c0c25080d0a0000c90b40004112590080c42c0281c4000d0b07840c0308080c441c20f2140c8110f039002061030b04040440c0c4003030410388540e400301d0360164050406056542d49003c2c040e001d000e0b050301041100c0381c00401a80703040c4a040303590710090300c000541c01c1ca54a00103007800c03100501103060514000c079100c04a10749080c110480b550100100e00d200d142071000441e80d030583e421000c0810f10328010442000b8100009100c00f05090f26a2000c1c8400d8004000844c49010501c9030001c8081c80f0315000381c00c00d00d0904c0301f = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 371063165 1250 371061915 371061917
    0x231302030a060b0c030d0b190b0f070c150f0206040812100b0309010903020106080a030c0206030a021201090b09060a0315020d02070203010207030e090709031a06130c05131d0412 78
    0xb0316180e5070321482c80036800c01034044030290000170355981549514414120059800d0f60714440c42410400c2600701c10b0399074400e4442041d00041d40c007904000a00403514039944c000d042840241d02d44180c000c909412030344003004900341c200040c69070360001070101d1056600801e028608000721415860b070800180c82450702c04160755001c1200d010183c041d40c4200c1c0e0440c0001481e02050030007c0c01d68440e03900007140c80d080b808041d070200f94001d002c0300a80c0d030147d680503078907218402c10100a1054258000740c1007108800410180400d41026401e1a03040323a40c418140c4407041000a00f202500c0000c120b8048000300d40701d6613080b40c01400000414490060800c1c07101d8000c0323070a80e030140318100c00141c0c0e0a95202c449150503a0425044203003450001d0101d0f00b541c0c2c4200450000e00c2c2c0100e0345103c440001441030f5500d00c10180302c00644882031211a00030180076106401c1010004030f600c41c220b402003041e2409254840c50a201072603000e85a86881e01ca881c605003250401c00 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 371064415 1250 371063165 371063171
    0x1110a030c20010f11030c040501080408040f031101030f020c060109110403051b090c1207050904110703180503010b0d0206031005120709140702150601120f020301231302030a 77
    0x1101c1c0d00b2507505514011000c94001103184035100218400b280c0409091703d11902c0c041c401c0c861342d04c4550040c1c030103070307982820448010303116801c2c050064010765000164008504c070002c03003006094407000c12047c000780c07800d02a210864140c50164010441c078090035602c035070010095450319420880168540a0820f0301c2c05450ba2135543c10180800008000c01500f00c0d90a0310b9804c1c02820039500040c0300e85c030241420009a030030405c100c030141086080100100d00b419050b510743d8800d2903100c03910045150764550b6854003501c06c0404070040050310403545400511400c2c180582040345400030300496041c0305c283c0c0cc01006170805000f61008064010303012420351104080703260034a075445c0c01440510303c0c01c00c0c8101030b0703107490040310802c20541c802d0046058000400c01903801e661034058881c0c0e039400004880502d0904076034185a03040c200b4191856803a940298107958100e81102c66070f002e0750785500d0307181c19901246074015424901003624000e00c2d502654101007400008 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 371065665 1250 371064415 371064437
    0x81614010f11010e0309031c02030403082212050d0e0303070f062004080706020706080112111005041e030b0f0c09040906060e06090907050d050c03010f0c090801110a030c 75
    0x12421130300aa450b0b1411a4000544a0550721701084550880068080f0790b01e010500984003c1d00e0b8011440010600800450044180490302d0341529200e0074a4200015065407446200343c0160380e61415a440c1c0500d266500b4200d100c2c08841192200c060000d5103020810f95400707484842d8040143c2d209551080d84480744c8600c00d50f140c00d4000c079500c3e40c688441c2006681030804070b095111790b0a540c40034804000d10354204800031704407418030803000000342403824059220301101c40215404000c40700e4030038443c0d070007001038000e03201000003003041c4070380d4041030001e091468000500144c42d18030009064030125a43d40d0392060170064603d0038490b007200482c00b038031030882d021280c1c50349901003071080c52004d1119592004044070f0b40c0c0ca150038518010381e22161180600307802140b0b074020311414003e00300083c0d0401e040c043d00070401c019044055000030701e12410f0540003e51a10341c00034110300305025258814012150207481d140c6540c03020740040c1017034100041881000d0b080 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 371066915 1250 371065665 371065697
    0x60d02030d0e030c090f310201032d0509160e041419050304150203090a09020d020906040306050411010c0b070305061809010606020c01210c110d0306081614010f 71
    0xa0350303025401c81040c00c006c500305410303001e4030240301c0c2c0d9a00d21078000c00f580ca01c5089004e0700381074003080d0702801c0001d40461550900b500c0d001120561b41c4080b00014103100740c4081039840144206104404e4420085041000031448007061242c400d112000c02c01203808110301004403400201110200e546025403040c03442e4840000c010140c8207a0070203d020010000d041a9905480c03103140b001e980391160400014001c182d96000c0c4e101001d40c00b04000b8000c01c000d42c115415004002c00454540e6568a45000a03040442c0d0484170100344403041849540030301481d40c0100c0d4040d2070a10b03a0741d18220304400800d401400d40341d100221340c1c40101c2190700d8107040c0340503944105c008101c8905022001e403a01a42d42800c504014076a804809100e0003090501c0100c0003201001c50040c80348142110b00038000d0203103030042d0095210405038150584e00c030608882250061b500a081c9221760810030403100d1003070340041c0c83c0c65000c1c00e20541c41071003840d580b5001400e04004003000281c0c = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 371068165 1250 371066915 371066929
    0x108061c15020a030c031e090302010216140106080703021503040c0b030c07200307030b0a060521060f1603051906120b0615090111010204080303040c030605060d02030d0e030c 77
    0x6041d602640e001070914070030b5070b0501480d1204c3c4c6881c02d0034041c030302109180c0c007541c192040840450725503d00128007058800e40449803114000300795030003000101d00702a030785480312201c50320440d072a160000a45110100359201104c0e0010140c004140c210010442a548010700464000001e600003056010000025601902d141d035200c540b03074030003803411a11465218111078800c02810b00380035190b580c0024400d007074070340c48400c8103130300e0302c502c05044088d20407030f0019544500307034607140e00c14681e80c00501c0d05c18001f8103040b940c050700c1e6281110000002a43c03141d00d01c1f0020f0100f490128003030340049802c44070120807d8175844107294076030200c442c1500641100e41c8250281007d0064518440b5080030041760781c00d0611320070a4005141c0d10444000c68144445400590201030081d0306440c000e12205054076624502460000b403020312a00040301c8103403801010880303d0a090b82c15020443e4041d006100b13050100d8420341d15690702c0440c0b2075040c4209541520307030b81c4440e4 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 371069415 1250 371068165 371068193
    0x42630070305030613051504090f08040b0319020a0c03050307020a0c170c1207032301060305010204060908010e0c040f020c16060e030a030c020904150513020406080c0108061c 77
    0x60790701e0f0346a040440401050030400f0035100d00741c070f080c641403146150200f00c560f80155400c80d0001401e05892034007420320342c9038100142450b500450005a170b42c41c4e15005610401e40c4c10210007620000c80542400c0b401240c1e04500050f52140440e800a4058801103401040c0c600407100c41980d90b41d2041c00301455500100031075840c5500c02c60b2400d008100d20440644c0c200e4825000d000e0004141e603803056103100241101d54020500b81002c80600d4451200700840c500902c042610303401c24034043d500c6440b42d10300240c80c046000501c20418821781a020083e40d005c1c040540d403200c2040044c158420f400c60328550700300100142c01c44c00300401e03504200044001140c051900c8000380020300b034100d80901a80201c280e1400107036206015034006641100c0c1070b0110b032074900344030890050688a00107e40e03d000144803e50195840c3c0e803010034400c0310144001c0c1c0d00e60b4072954503900c40800e10303404901d20b03d01140070b40c50805e1510111002403402d9032410b81c290341391205004030380 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 371070665 1250 371069415 371069417
    0x30c050d020a09030c23060f0f0304030809070f03200619020705030c091e070507151d030c030d09080d06060f0e0a120204051e0c0426300703 62
    0x2540342007041040507080f000041c0001e07035100c3c440550032140010103841154610780b064000007142c2074900c1024060703403101c00c0c427a0041ea03280d161624014201d000c0230760f05a4600e1145441c0007030100204140842940d600544064903420184407000ea154907140b02e16600c14001e0062070f03041680b980c405200b003980d0382e0040500078608018981492201c00065000d506581d00300582d8141a0b0b5524113540c003a80e101100790342c0c4402049910b4020781c0c0004000e0302c8d911801c522080b01d40d400512084440c8201c00c0b03204100c0c681c0507580d03441800c075440d14941052140c00d00703404542e0f000e02009802001d10a103050a001c240c0b004585460304008046441d1034808080b07140d2100307645103059825101c070181b9606160038803140035140c0f01c001f803045d0385030000260b500805074043c810410310644100103500706016a5944e43c0c1180c00341424103281c581c2c0f0012603400100c071600031202c481018104104650242582204001c0703c021024000c05100c0201402c1010080540b5402 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 371071915 1250 371070665 371070677
    0x106030b1f08010204360203010b1207020d0219081204050102120112050303150d020a030302031908010e221203050105010306171b03070504050c09040506030601080c01030c050d020a 80
    0x24032480481c0a50303550082030050307206100601aa03641d80041d505900b030b07440d141c20700c1c00325080d140050703428402140040707160002c00000f51151580c0054110b80c41b0340f41400c02c0d603585444c000ca0703407840c0040500f40185c0c8121000c0c533424804080111803940201c1049180c5000500d401c29158401d0310201c4140e0350002d4401e8030790025055250141200000c0001245490788520b0303600e000c080d1040d5000d0550305c0d0080b80f0350b03440840381c4c101c0e181c2c05081104065a281400b9480750425003010303180c3c02d800b031043c1c012680304a068a05941d68602e2000703941e1a0707000c21210400c0c58065402011070031080e011301140340c48024881d02d070389a030340c0411b15606044c0014191076450344601503100c40c03214880743d4900c004c180e600d51680b1030041151482c04800c002481c0135011780c4002e4000e440d040030300a5440301c4900811190784255000d201e1174031860309241c0e69020034810541990401c09a0540070b6100390880c282d5202c00d494841d0820341c4c1c0702c5011013241e010040440105107 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 371073165 1250 371071915 371071951
    0x18050115060f0207240903020d0b0f010603020909040b090a0c1710050424060f080105061e010c1509060606020c040e120a18030f0f05010509121b0106030b 68
    0x150182c80c1c00001c849034800383c580b036840d1805c030f21081d22658001d007004042d4a02c8003802c544c81002240015034000f072541c0c1500515081c01a0403140c10345000101d60208400400d100b8080c1c02181c103e00c00207400c800b219580c50f02d800d500d16070050032252581c00b07548819008560408103207006407110140340b043c102500008549081a04444103098504200400011800790042010b0740b00d40000e141d4120341d000001240208425009483d40b80c8041c1808100c0320f03415440380e845884140c400d540c0203041c2c40c0315511410b4051000754009000450340c00001282d61240042180350054086a011215a500410f49183d13810410050f8001901c2d100c19280c0750190130341083c20032020784050321010780302501c01e03c6000d24010600465030035544040080c50b007124011600160044507525080c500003190005480003510252b00f01740103c1c841d007101088121940f900010050f1900d407032201c039101000c50f601c2c1c2e082d0b4603541e150000408a241d181c842803203800b000ca18800005 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 371074415 1250 371073165 371073167
    0x504060e01090608160608070e0301020c0706020c18070c081201030305030a050610080114010908030f0403020a0b0a0905040915110a0230220f15021f1805011506 71
    0x51040e03032110310954004034005c000380804da00c0100c1520b8083c582005180d950700400e4441a061034040e80c3c241d0300c0010003400c03140001c0f072003009030f9140c4d5017654103085990b82000758440b05003803181455140c220100300c806000d241c140418030321610106040144030005030384482400d03070055010500000070005180307418801d00b0703400f500c00c40784100b020b615158020291181406a844c8600219640c1c00c02a0f02413941c0b04000e00c6000e040303a40d6041106c064410503001440103c0c0268010130000c144403400a0a840803d902079a4800032113190400300710240641120580b85c0c191640d0100040c42e138a4092154100b6110100580c0e505581c200249000c40e215142c120440d04401d003030240d4608241500b1780081103250503602c5090b085007a00030400164001c0300030b80401200041c00c42d07600c112903001c8038940c5000d50b0b41061080000d030303100c0019110311110310380d20b80c010f01c900c1c5140d64860210710800155600210303201b41d0312207084945030301d42c51a0520740400200921 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 371075665 1250 371074415 371074421
    0x10603050c090606030417030606090303071b0e010e0a0b012105041401020c03040e07020106050d1a070318030c0503040810060828060203040611160303050c1e130504060e0109 77
    0x240c0c10313903210740386180548803142c4660358410158060701e4000b02140e42c903a00d10007079a00104005081c0d80e520a486d18081c0b61004a0440d03c0525507240c5000151030b201420703500307040303400480342d0030444d07607d941ea076100074504100e9060621401c9003503d400e0304429140c02c22100780500c030000d03481c03e041c24400c00380c54003042d00303101d607030b00400615400843c003006072001c43c1d501220581c1c854445003021780c0900780e2034002e26003208000307404c00c081c050241c0304003000804d281104182c54442480490544000248107000301e0701801b00d41002034401c0c04640b40c668050f50580e800d1079111100c150500310701d04108201281c86e14014041c1c2d40050010808078149a0101c4040d0104000e0b00210f0200c0b0b500050001c0750302000207000c2c815550030894a0800043d0a107603640484002c4903115412513209900082ca0403000030304800902044400b10880213540c0387d84000300810701403a03a400001803420030b0000d1280000c031500d8600525000d418015905815981041c01740310803 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 371076915 1250 371075665 371075671
    0x10201050606041d0c120f2509030311070801050901060302040f09030f0507080706050c2a0c130e03040b0c0f0c0f0f010c020d030e0a1a0307031508010603050c09 71
    0x10502007080100450f40e4949210740c4692244d00420307940b542c1c1c3d40c1d204461030148040b0140c00d05c440004110581c1e15880d10316100c1d200c5009054410000c0c0070b524a900e038103025082002c04c0300050203002203400303043c040f05848070300c0b0101e0350042d49034011982550425a0b0f4800c440c2e44812061045140900580104081e500000c200323500d010b803001800074880364111414400c0005444080c4280c0c0d0045807091a00110244024189101303852040d0340010005480c14000c4c080840c0c40321105072080b1000b620030340050005546e603c0801406490800040300140e40c0c0e030820041c02c200520240000740008204152622500c1c0c0d03001d414044080c00030300f1680c01c00741c9880c4503a907449028036060201990381d14981c1c56440d005075072001030611701a41c0081040000c10415501c41a2080140700a41d10b00783c481d030340d608240100000d140d2a400400703901b440050403451080d40301030300c8030003501342490b80c3c0355840c00740d01d0031030b2000d4206440a403c010102d14007401c0094850790 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 371078165 1250 371076915 371076919
    0x60115080c030601030c02030d0501062a050c090903040f0f0f0807120f060e031c0f0902221d0d091703090f060d1418010c0c0605040215030f060102010506 68
    0x2107854184010300700307840010421414160348602c1701c4030b414400c20030f0b240e100c00c181c2030410955071500d0018002c0102801d1400c20707110f90b41000c9a000004590724015594840001d09000502d03404000a642005004411910091200054124014901c030006094215407061031500b040c0d80a0440940d54001400560100a080001010091481c0005c42e0021f040c2d030145002807502070061b110200c4016020f100200d13218031820300301011b80c00000b42103181042a001011211029600140c5000c1c1d80412603100d1075aa00079000032441803081102000281001c040d20040008071828240000e41d034400b0340403511203504120388001801090890b450850006400590b0b01e204803103200d4007944242002003503d880d101d0640309503c0d2400000d000070b500038801d0b010003580071906041d800c5010395602c01c0c1c655040c0b0401880d08001c0d692580051150748175080601409001243c0003080010490200c43d5002d0145009584080840c01c0a04082d07000900f900d50240080e8 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 371079415 1250 371078165 371078177
    0xd03020406021e1e0c040b0109050f0103110403080301081c02060105130c09090f0e0709110910021c0f02010c0206010f061416060b1912061802030a05060115 69
    0x10254640003d0503600d061600301e00d4016404a25890700d040c0807032180800c00003800c1041005100801183e511300141d02580c0410040c1c1c200b4004541c3d1200c1c5129280d041840c04002d942a544a500540e0b441d032801e000a034035069481da942c0400742d0099000490903040041c0781c00040d101032240040018603171000389080e50501000840c60612110314003600f541c3c483c40c40c1d40c12030254404034001c00510354104940d10100a4007800f410302c41c48849903030301510344081391480c0107115406410282d490540c0c1042920310a01224138a002c580d40290300c90405170350078441e42a4070300b41300d0665950f1030341220514808083d003921041911801550840b80050042c41c0300031480b00d04403801441c00d4100303030390000b0003910240701d80c901e04521170b0456000744041c030400350400c42c00080705071a5611402000b01d05a80c0d6640c04e409084204850944e4040103d00c098004007155041c90b004988810019800240b42c00d504075003c0350950070481c01005441400c00324081204401d04000c = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 371080665 1250 371079415 371079419
    0x506060108160207090b0f10180602161e0b030a0605090717040602180d0501060e060a080d1d04051f060e0603180c09040b16090503031206060d1d0d030204 68
    0x1039104c4e205030148003813983c0c0e560411003142e82c5030302d940312010902a1061451401d40c800c014015010f4000c1454000b841074070010301c039440001c0010140d1619640001e00070b003040b010949859000042d4000241200340110300c3e00c00810003507008050000e00005c80c14504014054201c6c0001d00a03814050504038481d410b08420b50303516480782d48040010794510700d4982c1c000101002c4044035800041c1c00302140c6c104001540040b090300c0c00d010942c1d42c03559034201000300ca508e40d4003400f002504045100c507420307805041194140074141404e02031041c02d4101203012242c0880c2c070071030580707800c0b008076080c40d16469208015107018900000345d620b894011070070a01c80503211400b03180c5000c413084641c100600022415803001010820a030a19062690180781c044c2c0711844542c1c980510300802d54010300c15842204e20240103181401c06c0c01d400a40c3d8204011b09683d0000703020401d00c0071400301d43c840c0c002d44602a6804580c0c0b01003c011251800e40c088151105242c410401 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 371081915 1250 371080665 371080667
    0xd1a030d030f0e070303030e010e060c1b070b070809040606030204060e06090414040c080606030c0904060c1829090d020d110406150810030305040b2104050606010816 73
    0x2004406403454100803a810702100076800007800c143d14918983d004240001c01055859048020080c42c2e450003480300d45030b9042000d4682c1c0d030a9404810b038000400010203140110405030b0300e84040780054480395039580e518a0041c0d440300b0130403203030a040019000c500b841c041c41018060691440c00710f0405e420014050442666208018810100804c01d099079607225000b03440304a2405105a40034140f40c98140c107002514001c0900b64014a00025040d08001960201900c001046030300262070b1500e5280080000180450400c106180e8140f00320582e01c8002c8002d0510340002440817000c00d208090181d084d5030100c5030082c08100034541070f69a036000f4940d450b011200504448080d24004240140344a14160894100340c4009038000345c1184071130740e02010b921610403d07605c1441548028130b02c1e01000300807484c02c0c4030501c0030500e44005442e13446a8640005290404580c00c82a0484104d40131604e661189003001450b50b030041d065904003040c012440664540e00300 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 371083165 1250 371081915 371081923
    0x308090601080619020405150c07080a08030612010b100216060809030f130e09010902040606050c07031205070602121b041508190c030e010e0a0c050f010201090b0901020d1a03 77
    0x144c41eaa81e4080a1035020007421541118010200204420305118013412825495008000e00d800640104000000c0c40100421442d00c10b981c01904945556680c3d820031594009940082d0032035980c501590443da2a034040009040070381d034004003000d42507004a04c2100724950006010031280780c0500914482c00810394410241131800c041d02c5240b808100000c5505950060048100001c14481d0100040d40301410447c000c1d01c0c107000b040d440e03079400c1d9058401c01c800400c5a5000c2c0500b0004111540e054480300015460513900c2d000c83c40d141c20003a80c10082d0f05112038032005041c801d110000d1809205d248684512441c1020315184d840307440b89a07070012080900c240c41000130824400003110080300541c2c00810468041d8541d8000c000b0010315510350b18035841c2c4030047c0480b580004041039030f1796100609508450900051085007003034420300b141590340350226800000e1810810074800c2e10008001a200c1040c25007050544295154000721445400c1900400741c601003 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 371084415 1250 371083165 371083171
    0xc020307080a17070c0516232d040b151803100e01020a0206060a0b0d0b0f0604031407121205070c030501060902040e010f0b03190f050c0703080906010806 68
    0xa40160384036103402c0402d41d203a24010100043c03080c3e6010800400e1508411000750040c0118101c4214042d40d54009950701c0d01d90040514807125503c00d03820082c0541071060703031040050480580c803440d09401c40240e0b00c0584c0ca406902c01080b4011a441c10316100703aa50f10f82c3c04440342c41e064403480c5560091842071031040d0494407a02c107040c5500c1d0701c2c20007011703032100c020f40030800080000922460003504119040740c01801004080b803218940842e04006517003103042c0d49403402c016801300c1002000d5030343d550351708030355081000c04040d0703291006000114050292007a103c0100b2060070305040e05500070758400d60219400c0000b24015400503138240d116418219514111340c01d03d82426003891380000e11a46c20301e04040342c1d0030080c0d0041c2c022500ca05640312440c0c0d8945884021504080c025039480c43d4003800000c01c2c240d201c0e40d022464000c480320005a100380c258100b0140c0c0d500710350703804281d0800602c0000b01039000d15003e900c0250040985459414801404e85402c3d0203 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 371085665 1250 371084415 371084423
    0x6070305032503090b0a0c02030f07020a0f0e0610050a09050f0d05070f0503070f140f060d0504230c01080f18010e060711060112020d08040b0d090203010605040c020307 74
    0x8400121020700407020200004190054010034110b100e42c010003a001c40d2104492410301900032a0074104117018806444480c0e4000d5402c4c0454005500825004038100381e0b80148495000503000984c5d11148001e044140c0c00344070b1a00e058410b00401284907249001009810484004902d51214140081c2c4078101c03980d0580c0629840002d2100030000b501611a01502e80001400f48100c05d611048810503070075154040e5503803012144000c07da12441e82d032302110445400c424985541e45050300c0000800f0306040608005d040d80403580c1c201c42c101e400b40080308c16181005660522a41e2000802d002031420f0030648c000240608006000ba1781d440c1d150030301141050440d400508028031031034000300801c41c20144020750b201c409803002004115112410541c51001180700d5040c2c4065031210803030510164280081c09109120594490300144000301e081c015144c0201322228001c2c0c8081420022401098212038440c0c0c042c1d40329500d050380040900f5000b03c16030300d0703a07600 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 371086915 1250 371085665 371085667
    0x50114070801210309080d031d070302010210050c0712030213090603050c090702030f0703080114092403480112110c0607020a0b010e0105060304020409060917071103070506070305 79
    0x9513203400d41e42d01c0030f180c000181502428065010b0315034075070320049001081d1a01e5031880d0440c1c9103040c0c1ca030341450201a00513080220305800e0f4000c650411900205428803032480d00341152a550b01c80321084841c2e034000f90300003d030130030303d030310604010350103003080d00020040a0700c1d541d1501d903a221442b030014068030b42540064075080c024825921908039403e14603581d207440c0d00c1d0090100c1024090b03030402e5008008000414180040100d12901c0050300c450b011004001c0207118603610701200551501c0303a280c01841040c442c0d001181c00001c0543c102413904440740f43c1c240c0000c000250b07011403224401c80e41455aa000d2504c400340c5071980000180e9080640e501c0245100f40303032581c1c2c058442d03402030001450b40055040201c40c011112184644d03240c041c03044c0f81100c00e2003815406003040c000b01b005458564451024a4400c14000a0b42131166480703e4613034910a0224412020101c0e540c1d080c00743c001c1f01c50103803401c00c0b80508509800c141c0000d155006405001c0c042140c = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 371088165 1250 371086915 371086979
    0x70209091609020702090c18091005030d0f0e04090b0105060913090b061315031103010f0f0c020d09050d030c05030c03030c090f01030b0f10030612050114070801 71
    0x203100d071056000c0340060100318a91a21107800182d840382008900910307640c000207542401c00b9050300e17000e0b00340b1a0400c0701403900c0720400c000401e000d004031b0045020100d000074a42e03410026010b1300480740d15111201c20984401401d100d000700c4c143d80c019800c01d40d000b070014480600e518103481044400e1034a901034140425030f0b07120070307441c0588568603080700c0b00e00340504510030a2103034804685d05030009000018140a40d04007a80c1d204030040101c00600000700b1201d1b50119010001d00000351012203100740f132058503024800000c0c3c013541c0d0412008c8683c2e0512040c1c1450101e402c04140e00344ca802d0104070003d0241d0005410045a240e54208000341030013260108008181180d881703090020240300f41c3c0c0c1c40410010b108082642d120b05465000e0b0042110000000707098500444100c800e10001c4000c00000d1801c040d582c1c0700200d9107522010908074142c1c0550000102c61804546628140e54040c12100500400707200402036888000c0f440441030700f1031802c0c3c41e4082 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 371089415 1250 371088165 371088181
    0x103030f0c0807050a0209060a0b0d0507030f0207110310060602061609080303040c0501030b1816050903010c08010f0e0c16020112050a0509010605010809100218030303100305160b070209 82
    0x201031440010b00750000001c0c242d050200001d80300b108a80202e603d455180c40305010000310b08028031485034800000d00003529a54120750049600420714200440d91940d074010081c01c0b07900c0b02004540304000d03540101003e080411100d8030b0400f40c3c1808005c4941400e0b006940c44034010030004148400700c450b58202c62050702114018064602142d4603420680b400071000300b62400307010f00007031a00300c0c1d0070030510f08100000450f100700041c0d0b0b12030b42c40713000c2200380006880c03205d001841010424101d8585007481124048a8150358a25055041014464245241d548040098428903040c020600100d40c04c8641c10380001d500d00b601c4000c03600c016039035800100003513404145001c0410002940355000703d44501340304002049410749410054a00c85000c1d03078010400d80c02105080301110341903000702142001d1421240c4c1070300c1b100001914550007201c0050180300010802c1082000802c115840c0045011260208600f040310704801800341e044060f00c960769902c0462028 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 371090665 1250 371089415 371089427
    0xb07030b0f0409210f080a18120908030d020c06060613052404141201090b0c0c0a0c08030a0810030f12031508030a1202030f010302040c0908010e0709060e0402090103030f 75
    0x2521021080280035800d2078090a405e40007025000401d002c0d000040c00161640724209180021050b410070000a9866006083d060038a01005101030044040342c0014104081d10400b40f0320003003d070b40c40c0c43d03d841c010b0509201801181c090202402480c07002030341f5082080a558040c1c1d03c2441c00f9040346003070515560139407440d152035040040c0c0458400142c16071501142c03001e440103d502108c1c000c07094200e035001c1e2030280c40c10540301e0229090001400c0284602c0141004a429065035522035003994459644034030708642c00000c120011941103160a6402168480007144061a40c1c0b41c076986d50308505002007030b031400080001c3d400c5000340e100d03160701d0400c4403a2080007600e81c40c3c8680d0b81d5002030405404240e0701040d0400c00c480034000c40f4030854081c9000540b5900c0c42d403c4c4400f502c0d040da80c1d0780611a22f1040800d00c1c040900c40c401201202c0801006180d1620358150121032294000011503130b046810000540c0302c8404190440c1d50606e070003007442114000c12901 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 371091915 1250 371090665 371090693
    0x80607080601170412110a1a0709090608010c0908070803030c0f2701020f0f0a14010207021e0f0411070311010612050f10060f0603020903160e040b07030b0f0409 71
    0x40c81c500f16041c03200b8004050100742290603191039242640c0c400c0540320783d503001c095200030505d031400361072101d500707640c0b85525810071000e06000880750340b01c01110045c1d40c4d4907000009503a64854509503400d6200c20004018800300d4094082c86080840b42d584900c00103200f080410070001d00e40e401c080944003124a440b025808200d0140f2549404028812107144020b0040c81055000c014409010915404000019004040e044090358038816100411540c081d86950b09008000158540e6080c800c1818a00809402c001c0082410003654511140c40d060041c0c0c5006090806040300130100c3e03290a401d424801840302491801034017400c655003024920f40800741c00d000401000042800c2404103d8054505240100700e9101c03c4648a01c03c07a00300080b6074030208a5140280e000f0500004082d0945250818035030030544600c1030380e400781d02c0300c8158500f0071092101e002500d40d040b40d440c1c80d05001d4050403000040050b10320302c070654031840c0d03075002c0f800801140c2451440 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 371093165 1250 371091915 371091947
    0xc0302040608031918050d060905150a060b0304020d08070c0819050c090702030301060c0309050a2402060402012f060a090b0708040c0e062e0e0a080607080601 70
    0x5840e100d40142e5200c4c0c00408100f0310040b030b140109290240034500e1780b858190000d0070046400d02e410f082100040c2c000f4019500180e84a051030b011803800d101a40000902c60050070850034014001811a103a40d4031540d104401401800300503503030410803a80031600044581d89451260a15410b4a01d0036403207107009100c0c2c81041e10a000b44210b003150f00e940140d054035280c958070303410f2020f007906c01c0b184600140c00800050003040c1c025201400200c0c001e1406420302c907100c40100d003900c262900010074404580301d02d4520304007090907285035100944050031075410305500181a010382040e48000542c5007002174113820840e0044020043c0100007142d40300d003090400072000303142c5200150f4144a9520001e1002c03030144100301e003d00e07404104c95040d0344c03800e41c50319001d181c003070007807a80441d03c803aa040c10341005c901001041311943c250070012900c0c4840c060018500380392030b02d00410b505001045490008152240e01203590f0030954150f6585400417210200422000d036 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 371094415 1250 371093165 371093171
    0x1050103150609020301081e1e3417010b090a02030a0e03071505070905031501080f1204051c080c060108070b0306030c0d0c170c100c02011b0c030204 66
    0x8144010110840107035000340004012281d01c800c00340c8145d1109000d451407946c4859014042c00100b01050b42d04080d02005851404448444c04030b1141d40d00c610508981d0320010501d400301c1d80060310711440e581d00c40e01c04440d5070041c888104000002d440703078020711194004003800c540000c1d08026400500101074000910707043c00098006d4105486948801d40b43c48540b441c440000411140515003102c071030346034500d10102440180030020301d28010000585070010ba01d403420000000b00e81040702d54000958180350300c10b440e0108403d00502d01da48407503100030203941d80e0380403102030310401d0380c001002403102c050900502c0000c6100906030000011848a03504000c142241a15880420b40b6003050b5100d00344040f90100795629641a0042c08040d40c1d03d01d03100c808860001e105119428580e541c80015114210600c10500c02d16088581d000a281c43c02d00d00d5080f0540d00d40c14080c2100c2d080da00000d22903403480300156130f401d4aa40380501448038040e9031800440d0300600c24 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 371095665 1250 371094415 371094419
    0x1510090f09020403110306011a03040f02100c02030609061303110313030302070f090501142e050403110303040e010e0a020d3b030316030906020d09020a060212120711010501 76
    0xa000798483e101c1a01c0414211100041714680856a60b04071442081a40003c1702026450307001c9600203401107400c800b030703000d4080050312040613480c4040320342d0f11040c0c1c10030881c4c0145410240f0080059142d41c0061040100f40040f03400f9601c01c90707815142454080102034120381c0345100c3d0a5240c0b20301540c1c0d020010815a000a030035090700e4a5080340c0a009a86271074070400d0703a4007801900811b8103542c41e40780c02400c0c500840300c00d007074a40e811485d41718504000107440003801d003007400000304e001a0a10922440307030784405842e1000e900031480e162608034030b0003c14a06005906007000d5500205800e190303a601134500d4034080c06800c000c03002090444aa00c038103a07004020310400700205100f1014800c2d440e048049201d00c02662866480d900c00640c080c210030082002d0540d9039070000c002c00d045201920260403490710000d0148480d00400000740c1859000c882198000700303500e580c1003440d1041d1228004110aa1035490701c17503140139035141c40c1c05418090158640000 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 371096915 1250 371095665 371095679
    0x7030902030f1209150c0a030f21050a110414010c050708030c06040c0e1003021003140108010f05091f09081b0d110109020609060307030b1c0203060703051510090f 72
    0x42140712402c860b5100c00c031881c500100030b1400303000501900c03900700c5100600403e0240c00c0710f5034031070790702d180000000380c0c1e618030528044c2b08010303091400c540d030380100441170403584140c182c050034404140f400c1516056001e00190a001d089a04010684541c01c04002c402c1020300003900198098070b8807072a0011103180d4071341040381c05640300f014407600001d2981c1d00e807983c180506045d019801ca40350464080c003007844100090f100c20180d40e031501340d08042802410a019040320000415443c42c02c0c1c44c42c0741034490142c000b04041e00300205592000030b48506040c109a10810007249603411401c103405240105a440084010f140d080d0643d4800c020603c80c0e00004140c4034910b180994039440c41c225200d02600075000346080200c0101803409038040d60f807083c1c0704d14020822002000203c0c51078000e20344244244040400440114a000c0c000264002045c2c50200118941061b00002890041240501503081005c240042900c220605000380040301c0010815517a1008 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 371098165 1250 371096915 371096917
    0x23091504060c050c0f060a030e030c0a050f0c0a0522061a0901020d0807020d0e0a03020402120a0506040203041505040629030709050103030921290906010e07030902030f12 75
    0x7000c0310b06010700b212004462070000521103801c040540211f080ca4035002040d0010003460184104511041c0801503807200c1c00c0080e454804c6c070400150485e031070040c14203407516003900001da22510305410188001c0d203c0d0040c59115610803211000443d62800c1120001e00290304038241107040e000c09000c01004107002844540002c3e800c403001c0010741c40381101c4601f000d03a4064010780001065100141c4561064404042d0080140a80c00d59a42c0014200c0c1d0140c024801c20703d1b40441000b403c0190f51080c150311140c15181545103140a61324015061a003151400e42183c0d0f41d0003007420300900c3e41c88140501c440c0303034410440030054103404c0210340040403001d11a03c11901d010032080002d0041d06d0491782c0c0740d01c0b0400c4560801d058004058420390700520400550b09070000400c070b854000d0708a88650f241502400d080e158605400070344020f000340b110b60700c401c004110380001400007036800603540c940010f0540d45480001d05040640754658828484c1d601804084c0c04080 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 371099415 1250 371098165 371098187
    0x9020c2a0307300f0f0602070b0906090d0e011404030308040b070f0903120219080d0e0a080306010806030a0507180b0103140a02091908071d070212090d0b0f060406062309150406 78
    0x1c20380c0711654800040c2c41e500c01033160f202c8020742003070506541d40b034006c0c0c1c02c030007000c030050420900c4a10340c5040c40705e060300300360300503000a4609800d0000b030240c020142d5030050203e1900f020340002400014140c0c0400703100007007060300c180a0000c00c0034402d12074815000e20403e4140114016420098141c2d08a0408400503030b03e080b5011407090000100d2850490b1b200f5243c2c1c2c00c540d503040041d00e611800130540e03074240c0516410b0740c00051080c0422405410312030210100314940464202c01c94001d14415418985001d01030446400b0104081d580511101005a0b070f81c1c0c042400300d1341170030102d00504140340c81d00d0b00225000002090000c142d03a04481d2484100b803450550200817002658000701680280041b104403207440801049490000b4100c0005aa003594074019041340c1201c91940e41d04200051164620780343c0101c2005080c91b01e000718524540c070411211380c030f8051307070b80300240000081c1d41d01382c40e1610000c1e15006004240000d4a46903180d0020b001800c0f40303 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 371100665 1250 371099415 371099423
    0x5220b1015050412230714030106030b06040f0605060c03040617040201120c18080a060515060d110f0313052e0510030c03030c14070f09020c2a0307300f0f060207 71
    0x3c101587c09410144980741c1140d401c02003075030712521548140f000030031000c401502c016403610000f19a5454031001400010040c50045584525050300144001e40c01e4824101141c5807400384000342c0e030700c0404882c50100c62000001d01d000300d6002580c100c0010b0088000610031240002055940818107403600f90041d002405990303124410561101150b05500794840070a2005000c03820883d40509000c90264514500d03010352030b461800c503608102c44211303401040180d040c1c2088020700c03210b5055290500c2008440b800d08194000000c000f007254410303540e0715000104108200f03443d03440215008840203841d16200d00b03005081d4204003000ba41e0034110751000c0c1c0303241d08000400b0380842d0010b01c41c80380b40341c1c00c0c04c00e064040d62000c80d102c0b000c2e201d02d0700e00a42c1c64501c0300000c009a81c550307040f2003200100406150030000c0582c0440400100060004000070701804880044c000e000c89040001c1103518001400100c1c00c44060041e01c55158914204422940201441809 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 371101915 1250 371100665 371100689
    0x1e1403040918020d0327030b04020f03010b0a05101209060608070b04060507030302030703020c010e0607030c03061a0c121207110a0302070905220b10150504122307 72
    0x28149002d5102060310700c025040150020740c0004039119030300304040e000d0380c50b503e0a41d9421061044548625580054598213521401d12045180c0701d0070300320906600386c00038444920341900152030590a8802c0d140540081030030640794500c10300340c0324410400a80c040083c4407440c20010004c00b414050040c003482028004158410300d0410385044446aa4495260030360359541103029402c050319241c1816020b00460390384510a018414121107400f00901c9240f0349210000e0a42d0003500300741c018580340070020302c1440c1c100000e10381c9a4140300c014668803004007010b14a44507007048101c41d6070401086601e00d201800e0a602d003d04596520f1125140003104415114108000001d0140c0d11881080050b010f0b1500610391022915a40c1b4004400754405000c0c1600349410858080e034501c010884200d45d9503006034007802900c0005e030400504104064070b640315500442c06001d03c20b40c40102006000307210f0a429069048800b180700441540160762800c05000e07407840b50345 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 371103165 1250 371101915 371101931
    0x1090308010b160611040518040512040b1206030c21071d070f030b0a06030f110f071502070c0303020307060c050307020309060c0f01060f0920071e14030409 69
    0x20b01d0030b54070800109403c22240c0c02442d03445100411001c040c06084140c14000061960381d05122511541030741c10f803c4035a03150070300e00281420f40007408030403004020700c42403011134621030995101150403402d0005175141c2c9000640f0b8982003414541e4048161074841903c1ea00c0201e404000e00d400204031100c0c9522464800718400f4080c1c0c40c81180a98440000d01c4035205003d0348044890754107000078070000d0180442d03887d809036000700f40482d0b2a52409803e0304c0d1203201d69500346520125860a018000c10043d04a2184201c00b820501503010041c1011034150f04442051780c0c004180202c0304c0e40d074030b006500c0f40c1010740305480c050300d080d00030303400781c5d0280c0100d912881e4a0b81c0550714010200007004550380298440540c0d41c4501c201c03ca902180910500c40070382030032204020700610300102481620007818110b86a00c1750301d515036003400d0442c401e03124019407001c0c0811141124a802940b02003c0074006041c6241a850401642c80040001e00a0303c4c405601800501 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 371104415 1250 371103165 371103179
    0x1401020102340c0f0e0a020f07030c030318120e0307030308010b0a030f0e0f0d0e010e120c2115130f080c0d212322050109030801 57
    0x301455250303140014544030340078002d4110224007000d802c90040030207000081d9849150038040e0581101c4185503003400203111180d400041c06500080ea00c0d0154500b8841c0480814a8020510002d09020605000b602018080c0d0480c4006004841c02400074806034103010600001c495803030408180e000c803507228203080119003941665096114220fa80c2d00c2c0000440e180d9201c800e5030300400d0f960382d60500200c8118003c415800001c00010142d014580031001d0410261008410030b111250740c6103005660094000f0710a02412282c07011400d084195103410310b40b0200c00d56074010f641120340100740f940c001c075521818281000700ca1112690205050807944140c0e00f00c0324a0007654041c0c0001411034501e600d8140c85222218108011090034519050000b0041d00102c0d0501c0f419900c0c00081c01c03841c02020003030756014055501013804a03842d015200055000c55246140022000010449500c03038840301d8142d040c6400d100e60511600030524048202e0016032214000200e138 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 371105665 1250 371104415 371104417
    0x1515081203090304080114070e06190e1c06090b071d0603060a03050604120806040b01020a0b0703021306171e1302060906040b0408060705040308031609030209090604030305011a0405280b041401020102 88
    0x9a0f140110342c0c4401602001660a140320303388040d07100003406100010840c40481c8c546c0c24501c110703004a41d880040c82c0c0090740e20340003040c1004002210010702100d0f02c04c10800c030f403030417000c2d1061640ea884503000320340b5a481c81d400240041c466002031108000810440003500720081e9218203041d12403108200c00d440951507024016030000b200200480c5c002c020040c0c000d80c04d402c0041c0341c0500604e881e1013004550b40941c01046c441c1101c0113080f01642251a8007402c00c09a00c030388400c140210303002c0c5e0400074004240540360030500d1310444d180c5400310f4042080c02005103444a5445540c0034995100d40182c03440b60203103001041509000c0c02c21b0300e0503641d200501d607040d40c0d2100c1c0c458040c0350404010008100c90340f2000405a00c602c81c440e8082c1d0124009032145184c907080190036944103a100c140032003c03686010480030180c0703050380d0581d80201e440020090b0358082c818403450b03908010015440c080d40700003c11416080040c4111012140112200c200010040e0b0807 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 371106915 1250 371105665 371105677
    0x90114120309030a0b0a060f08100b0904170c070f090609240e0406020405091503010c09050a0b0a020102090402030a0603021203040608060d08161515081203090304080114070e06 78
    0x598011501c1c600080c0c4100c5d851a07021400610000e1000d60780ca0f0a18510001540910082c0d0032200c6000790301003840c01001c282080c16598688503040030b90340e8440355100380c50007034149400030442000001381030100310b009080d030b8015081d041d078031a10004010502403003010091803803e8124400c40b0040310503860319907010000c030721007680b5008036403004e00d00051040314043d50030040030855030740e4880d079140100d011520010504a08105060854410074120b00034803449680811080d85e80b9124001603c0d075031070718280c54807801034040e40a4040d100b89558464008000c2140009190b071004003100e000f251540a003c002d42211901e070300c45c038000c040000d840c001c0010701a040003004c6c83d40480c400c0740740500d08048040c1d5280801105002121030149121000e4103400850081480740d00d981485080018602480c10766a4078034821198620100440024170100c0f050007514020840e00e0000e00144148006013055010201d602e01e020071202c2c5903580704c50900c207080d01c1c0 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 371108165 1250 371106915 371106919
    0x90f070912080d0c1b0f021507020f15070507140301050714092418130605034308070906140f04021c02030604110f03160509090114120309 61
    0x454245229080c501502c21310700303050213000c1c805119081e02d034140c01503c002c3c54001c01c64003400300707880e00c100078416841015101c003414061010f075001d41d689161085100300b003114002401080c8144000c1c0500810a010300240945400000c403200c00c2c40303181015000440081002c0c3d034038179405807505150141040011481440b1080741410814240314030000000d03081c2e400b0303004076211403000354020b090100030100c10004042180c01c02c55050003852070450b0003406000d0a00300880d90341e07880124107442041007668900c0728601c0040307030349882d550102d48039046100251003004c0110500e110301150391007800c0000420b0405441208140c810b203006985060108a04001c51f20801c1c004e1154402d508101c075403003902c03603144951401d6250020160b10b9150850802c800c6540444403a00d90380000c00083c0302d440041c004172a40805000844030440350029011551801055032481e00029190700101e4110825080c0e82c2c10070400f03c9420341030013480c840c80d6403a4014190010303 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 371109415 1250 371108165 371108167
    0x2010e0d050a090b0310091b1202040b09221b020613030f0809070f150e04090c3602040e0615030a0c141209060708040c0302010804030e090f07091208 66
    0x1100e401c40300401075803c041c03201070306c8a0964a43d82190300f25080c1e040c450004103168070001c07108680000862513000d03024501141414035207c10a80180b080301d0080303208516074480600014690300d007421140111010411101c0c866074001c41000844030000c1c4054032982001a103580c0c6c1c180d041c128002c3d4560b07502c2c0850800c40c0010341c4c0300803003d40500700d176028151022808090110a140c010503101e44d295065106a52014004140380310006002d0340c206505136020619040300c0c44c08840020701c0076403100b429002c9544030f40500c4001c01540f40b03c046c0c20280641c8054000e04240c4042c06441c140a4845808100d103907501000500c807039003028400079103c5502540558004807190510601d0349210034106545540210b503c0c02c01610503805201194604000503036200956003000c1d012401c1580b505840003a5600c00281040703001c0000800f0184a25030105c10040080d200c1c0c942805e05c5130480050f040d08a41c440c002822807400041c405030901c10345032049401800403 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 371110665 1250 371109415 371109419
    0x30a080c0102070209040804050103060b0301080a0f02012601150c15050601020f06010e16020f1c03060e040c03030f172a04090606020c0406060f031a03030a02010e0d050a09 76
    0x2256600414582aa030795801d0061070050b0303c41c0081e10303101c1c0303200365502a80e0f141048009401c45800ba0407a4901210034001404132490000f00d1468554002ca04180d8000b0a44012a0071313102c4402c01d00050240386401100326544038140c1d506071252070481100ea0b140e802c1d003c0705e45180300000540100140d20524040b9219070f403205070807610610503210760098541d00d0a19140b001c0c0e00002100070440100b1054180300003080810302d020388080c1003162074032441c655591110a031214200c0c111400301c00f0300e00c1d0003a40940020b25080a16038194505400c05003c0450184801d4020844101031002d0340d5100769410714418128031511a00d9031a205004c0c120f50170480d680c00b4920307100e115164008100c25018100074590101d022038843d00700070300281071043d000700290207207080074014014140c01c1030035030040701e13418600010318101e94407840340403d0100c1015a014040084e042003203d40c190419440b4100c1101260250380164400b1112849800c074a04000b41150800b = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 371111915 1250 371110665 371110673
    0x180501061202070b13020a0807030b190c1707030204051f0e0102030f0f16060504080c19030503180a0816110f0a0303050c03070206040e1501032702010203041502011415030a 76
    0x1a100d405001400a8404172384034404207290890f07070380054810ba5000410081300c0400f01d164150040c081080034000210600e0001d01030300c803600c1d40d000404440c203000488030762080d81528002c01c4020702c800e8440000b0404800030f100410221000a406450a4909940000b0031986048424083d051401100d00c0304a41d580d001040304158001d1f00e14050004a111030141c64010360003040a683c3c8ca1140b0341d0034901e0701545c0d80c4001100301c44190550040f035042403d803540100c0340030340781556048011360b00741005003ea8005068000c0854441c2c56000c40d01102c0102c1449074409080066814041220700403091201039441075040c0300510000b4860ac01130b01c07114001500701d900b0004079034006050b03a009600041e0203920340e601004244501c045c0d500c1030440c02805c04112030200caa0215501c0c03c19a2100500b425a06107480d00716403080046074010110011040c20180c850b0000a01808034880070580e009107500c0401c00d1414018080412040d0040c0100004003050f0740b = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 371113165 1250 371111915 371111941
    0x40213050114100302040f0f0e070314040803061807030203160c1509050307140c04060512100e100e060f18030d0b040908030f01050312040602150c04180501061202070b 74
    0x9071100406400f0b120000c3c007049040147d0016050141c040e00d056800e00291180c5840010000d904040c14061489403034059007076620b8000e5004240103030389580d0314003c103035964442803840802103179103420404850790540c080d500441803081d2643c0b54001941040702c034100441405030048920708088aa15105a031041d8107240c407590503a401c19103182c440c03110000322000101d4060300110041000d0303140c14441c0c4030160200300c4581c00e91406210760903a69600c1d4031607003c040d0780e58001c0200c03115020803d0003070b50240c00c9030910621a0030324502d80c6440c025512501d07018482c8010640c0c810300000c0d040c2050740040019170502180465071400781c0311542803542c115036100a02408140a100118441c044041c0e000045500d000c0034546480c038100c018101c050001d00062120759400308407c400001c1c1e0400c11245512495202c41a51242e940041c1c108203400349040c2800060340c2083d812140343d0b84989124664041c00d2000f64482c40700000c0c0070088020014246503038a40c = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 371114415 1250 371113165 371113189
    0x140105010c051c14160b07030501120210022e1d1f02070f03021c050316080a0e01090c060e0402030106050d020a030b03010e0114130b060603041415040213050114 71
    0x8981121404004690300300d140c3d00004002c0400f907145c03904002805003185200c1d41104062404105541c940314842485580d40e56000384128004615981c42134400c00c2200c0d0b08144000f0204010500640303e104a5454a07040240344c82c10003209291740d5480b000d21301034001c1650041e0504c0502c848075182030745132400c14104c52903820700690300420351000407604404d1094000b0320751204270b104400000c5460030b45c14820880100104240410180004111031540c0d040004158840404090140101c0002104a9845e1007850710510052201480407140d85441d989142030683c0203020030b84c8424040ca002141c010031801820b220564000c1650742000d140004841076078070006425911056110318031030b910751720056007030746038107103d84e8002c1080061401d0060305070351080201c500040c0010302c203030004000038092007484041c000c0740d0001041a158042c2d541418581c18050584040e409070384514201004540c480c0b10f034a0503180340b100c49014010322030f4100b022000040c = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 371115665 1250 371114415 371114417
    0x4090201051b1f140f0c160f080f0702100806010804241415040e06062404030309090c0203180f010306030503030a02032203050f0d0b1201140105010c051c 68
    0x248028125003c01d468645010040610200300703c024206041031011010308845007864000092042501421701128084450001c14048a81d8a402c01448821101c0d1024102c1a0002903494141c1e4000005240061080300c0501f13469900d210121144841120218089503404010a01086031a0700d101c14803000c1c8616002c1c0340b00f81b50387c40803d8581c03941500c2c2c103941c071039824072981750114414481180420745007005441924003440d0366884001d800e80e400362907884105c2640c050080b0414034000b0100110035680c40c4c2d240360060400c540c522454070042c2ca016451034010344003004441c0c0708080b1082d9401011142070800000381000701c40b4605042e600d0700000002841800135610403020458016202d19010342c1130b00c0c0071044a02005550564818400c0c0000d800000307988204405502d0a40c42e00c541c1e9442d640101072001c1e00c903500680d81c0034140780c0d48405401c0703080000345000d041c2411366030f1540155508420203100410369040b5000c56054203a4100e51f00c070611041d = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 371116915 1250 371115665 371115673
    0x140403032a080a0c02090108030720010908070803040e181011190207030b07050703050d05060f040f0504030909020f0409050a02041e06021b01050f18030d030f0b04090201051b 77
    0xd40e88102c180da001032801004a40b0b0180410709602e481c00070fa80c0100307a544059481c1c11250f903070b002c0d40c440e000710034074a94081c001854403080c0d02c02c1c0b1901020305584000c4036546d54454242d559a90420701c12000d400c191340c070010310183e0007030506e82d0551440600922192508000c0c0801600740e200498012400900c01d0b10010410042c3c2c00d54086100d402030540300b03007541425000d500000344424207111040015100003030707110341161030030481c142000410b9200c05002400010714003801c00da125082842d583d54256440c0e02a42c0036912a4507040c000507038034a080816402508003030400c90030284000c1140c1220f5402c402d03400f810f10300f0014546500c81d1042c0d40c4100c2508070083c8a42d082c503030288036060b01041960110200810607901d20504c44000820601c5072f540b449540340408104114005c1e210040411b0b0400c0050954007005d50141c00140104400d502c603560007401c3c4915a1250300b41481444003880d010395a01e0318056a2303001c1812a1725510a91481c2e0380701e = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 371118165 1250 371116915 371116997
    0x8010204030c1521141303170c0f0304211d0f0a080a060207021219030c03201b0f0306060f0303040305030a051206040b0102070e091e01060614040303 66
    0xd41604031180a601c003010000b4480c10f03406175028a44401040745022420318155030700070a4000340e40a40c6007140ca488200c1d10780c0c40e503460003407038000e91080852034030020041c482000382d5040c1300004c0c0703409040c20305003000302140221000012101c200340b000c0304090150401d0308100e68043e00c1190003400f8225281d5580c0351b49441c12021a00903a066a80841c900d011494042050084031905a00900c02d4200c1d0060b411150600b4600050070307c81c90251440070035005030380c070984c003080c0703120f42c5411400105449a140c170b80358900341109818410b401446881c1c918040d91b182a4054001d10b015079511003032001c003000c08500c495151100b403000100084040004042803440c50381c0d06901c8100d44200c1d036840c09000713810544603908004200c034860f40c0c006495805c03202605d50304181a1100381d4001e080c80001910358100c1070070485802c00c404815008075049407034594070711030f81501c54114150a40036502006002603c09146c00c0ca4520065010484a900c0324010001c2c0350 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 371119415 1250 371118165 371118197
    0x4020904030815030f012421030e041a12071a07061104030609150908160602040815010512060f0c0c16180c050f070f06090b0f1008010204030c15 64
    0x9118000e81010b1307039107c0c0e041080c6061000312400c816030300740354280950b0f81000c5441d003040e010a242102588400000041032500c1806500410072005d4000c02c4034448500740380c681011071000440c00784e07108040803075440600140413021298940300e200f0302ca05807920311022a910a0300180d420a440d0010081147c48500c000c10066200d01b10008643d549071900c06410410080d01c0c03940f030340ca06024000440d95071022a2400b032404024880d01081910300b4000030300890304500c0b014414030000f007075800400c400d140d06a4200702c8448601c00049114030795602d07030407103281401c418490003041d020440e42e4068081c0d070701044103a8100c2e40c1d502c40d070300e44100445d40c8003107030019480304102c0300c200c000d1183c10380483d503502e4113134613020802c4c60b4081c5c903103c0d003c4d0042c600700010030100188005903201d07009007036219400404a00780901100040e91080e02e251b10003038003e07240014000b20500c01c4400302c030313400030764601c0b454504840000140f001c1c800100c1441040c0c89003800071 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 371120665 1250 371119415 371119423
    0x70806010e0f0c0406082a03160e0405070903020907121505100201050403091a070209041103060a0c0206070c060f110a1202070206040e101503060e0f0402090403081503 74
    0x2900c2031600300702491920300300c0a500c00d44094003008515404010074407040c0c0d030018036035a10010001207107445081c0c3d0000c056040c5411505030b88903a0707011092105001c0041c400403290146550b614110203070110810049030003d59091021441d00036040006007081309082c1d9100495040c01c03141800700860040c03c0e00d03d11903200031103249000d800c0c0b04d1071520410701c0401c24954130007008245000d0358040c11075040c0f80034196035000c540c2c5040c4480d10080086824081d4050488451410640381001c0b159401c844614030078010000060b800381c00300c1c401c42c0207d0a06500400480d29040d00a50304910b60503000c1d03859544442407c040d42030207005196400710f81700d201356a68650f80e40011320080445440f04445801002031901603500e10003960b09440420741c2c4440e0035100c54140c030040200c0713a84030481c502200e44d2410f65083c0c00d648000300b1078034901441c90140c0c0c1d0303165008040d0002110025407250f0702e01d001c03034082071103101d40361751100ba04500d500090103443d001034a0 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 371121915 1250 371120665 371120669
    0x402030f010e0d090e04030801180e010e0a0c05060a05041503090b0f0f100506070611040e07110106050109080307200d0b011a0712030b03070308030a0203041406060a03060504020307080601 83
    0x18540c40b1003c4110a554000010390003440c007014204080e007010b982c024401941803023a041c0c1041da100ca505402980d0350f0000d401a0b000000810011301c1400000c0e441d15074101040d5110050b07010009400c0c2071802c00c542e49104a65142c80ca00750a00c0a031087c039a022011079070406944050391000100603187d0140554528178080c819440c08404121101c1c038010705030205007482000400040d11024117481c5000c1d4482404100b400ca80340d0b20300941c0c000c0743c3c00400000d840380c007844803050700309a0b011034500e05800240007003501c5000640d00b400203445814581d902c10050900440c04014901f60700601910f1542d0650b00954005240524034100c00da55000021004000d0b10000382c1000d05440316900780c19051402584403000c48603005d00c074803818940c45801d0303280705640c24002e000145601008890b100d0a004010b58003d40048804440100100c0c001e44100d1000140c00c5224141c02400801e4080c03c40da0b42c40301a00c0b0280040b03070148900706011a00c000140a0280 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 371123165 1250 371121915 371121941
    0x7180914010b1216060c05251a2505070b040828050a20040504080a020606090f01050d060e0a080c07060e0a061b0203011d15090d080402030f01 63
    0xd5a19406402c01c21641c08014142030140d100c480300d9010034504204c10340458540e82094030040c50a420f1640c2003903041c4c001340681200c0940d0b4030115050b544003460039201074600f51406120b07241d00391141c1d0b00c0f46884505528841c03030a00c084425031102c031488607510072803d503081280d0741e0740d503440190030a4004113000c1d0007141145014440c0c0d039810784c00501940f0545030340740030340c0d490b15501d41c04091005400c452503600d2140d040b41c4203050021512074040c0c01003200d0700d0a400c008480e50460102c20006018030000704e41d080c58541c00050013030445210b04032844e480d0000f00824002d02c032804403000303503d99210030022102885110044d502504406990300780402406080003460742003182808a400d40441c01510303050040010788003035003071445080d02c8003031482c441146000c40c0254190300307001c900c0a0008044803017182c0e000c010001c8030b010b0f000c20810700f400c1703810848241c4160340c0103426440a891190103401d80180c000740655000e1051030591b607003035405181d4285 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 371124415 1250 371123165 371123171
    0x10b0a0e06040e16060e190b0403120f020705132d060b1206090402121e0606100e0d020a0e0c0901080f0f04030e0316080705090a0903020718091401 65
    0x12800c1d0909000342c3c4201d00c034039005000d030244050305076201c001980c0604820000110314045003034582c4088040411401150140c0081d80c512031000603501070b00080f41e207a40e094510341100350040d40392400c9001140c01804502e0305001c10b1150b9400f04c540100010790710348040500b00d900c0c058000d88514664060a1000d0b0f00940f40c02044d64816404180340300703c00c0142d007140500404980380c01c00c00466040800d52102e0001920381e03200485d079402d6a015903107802c3c0505041d25001007003041c0580c241d032901e1751a46c0400800f2048407034080041035047c03124154500e007410245021a10040041f01c5e042e40340c0b0655020034900303ca031a1400c84000034159103035a001b800c400c0d803140421000200a00d0b200000d081d1102c400b810080521140749030103540c07681c0070f001340c0c05540a42c243e1214499a16605996075803400d12405008441810100b50f1515550207130608943c0c1540081c0303030031071038800c49445a2039001803041c40c1d00e40e16200140000c0f0482d00450b400d2003c0d01c008 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 371125665 1250 371124415 371124421
    0xf0406020303011a0307142a061603110d09051501060903030801080a020117190c02100e03070209042a0b0702040b04050132181008031c0905010b0a0e 66
    0x3028245080e50030b02581136082c42000340907503100c00036180c0440c210a040e51940240c4041c2006c2128405480d0b00c403c00680c0b040122a400081f814803a0220040c05450700300b016200ba01125a0080d4400d01d0b414100902c42c142034640c0c01484007188110708444940c10b9400c0d00d02110301080c0c0010b8005458083c00b0410305070b101038024007500d001005030004c0d0042d980080c005044100501c1d0003c0d0f028000240c1c5400702207070300c10269607032100078440040c1c50240251201d060240040030507150174404c9051290010654038115405000010291a40d864001080d044000c05005201a1401c0700790345840d0281c050780209008900d00361100201d20410040d038a0741d0009a00640c42c0c60010842960002504200700c24000c01c0c038042103500700b0079070694034848554144c202248c08560030b482071a80c0300c442d00c20010340d9000295140c880b040e50343c07284110790b03040d01312040142d48a08812810fa10010388070344100b000003a809080d1002c180391003099800984c644d4440820 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 371126915 1250 371125665 371125679
    0xd05130e09060603120c030406030b011e030501051207080a030c02150c0105010f05040924090c0f0e1b071e0f05010e0d0309020904080d020405060301081b0a2103050f040602030301 79
    0x290414400c0d40c2c010290070525550540760361f9005900c212800c00da1600001ca10507400384041609014121801411000d10304c080030340038120a1285500400da9108080d111103008130300d40702070710500341c064610380c152910100d9844200120030384e23200d1024241c819940b0214001801002d16620021036158501001182c642e003d5600c0f5030300646c01c00e0560000175003900c12140b0070141c2d20501c568079041081d4a00c00514680314002c01c1102031190201c0c040e102c0c0e2201e4400c8a40c40b0344060b400340e8920181e064107003142040320319500b0303040c01850002140104000d202ca0441441e0071039020342c80d212213204140f22203007078035a659114407440f035060003805070700044051810180101c040c1b0340d006c551506002040505080c001080d5041c520550b074040760300400004115540b0f03940c65045041d1509688030300c5185071200000b0401650500f81c40700f10031240000020700708540c1200400d20003d14445007241045400c101510180c1c0462000d0400b404899004588960410207 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 371128165 1250 371126915 371126923
    0xc0306120a03020c03190305090405040804080111040905060d0c090e011404080304020a0605041a03151215100308030105130b03030d0e0f0303010803040521070306051905010302030d05130e09060603 87
    0x19946c0b000058101d16000c241c0040450300003034020740d00081c0f16a070368100078070300780141d40140313283d94200300300300501040c002c02500c2a500c0044003041941c07543c0c0c08200c8030588054000b020310146030f104100b200350550000301000822000401c02d1042d200c00410b52000460f012614000c004c0148070a504000c0c85a101500700c1d4141a454141401c003424028080140c543c40034200c0000020390003c2240740e210030200c2c0141c4119803039143d48204d80e80303a0a2095490540c0e0b00401c0005e4000c080791904607040380e0308094a203245034240800c2c40180d003017640404002a4071011140140d031010402002041140c100000710008228145800c01c5000c901d0324015a00500050180590110481d0b045174002c80b012004031281d48052621403242c00c4801c4135500640200206014454002611a5403025031141c031034600e200c0b0520031180d0a01020350141c1c004001c40e64030358041c80040c001000702c0c0a090880580c0c984c200c1501080454131204035400401c00d020981c10200 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 371129415 1250 371128165 371128183
    0xb0a21050a0807201c05120c0d12020403170d1d030301180902030d0c02030709060603020d05010501031506140c0105040807050c0d0b0402010c061e061401020c01080c0306120a03020c03 81
    0x808000384c2415414005100ea44d15030910001100b8888100c5007000420407401541d840c04003219030300e5040d410200e6171112803034410040450050100380c2c035084138a108490a5a90007a40740c000403520500342181c0743c02000b050072406070340346001c03080b12418841407a605040b49004507500c0d81007d40130368000a041ca00c2c50070603800c00c44200f00507500481c03011900141c41c41e00081b0080680000380c60152194020034880d403400300042260b40d4180c00410140c0f8038080c0502c03040e43d8170f00045003129005000585000070707a01044c400603200b40610641030070b14900860900001200300c03401c65100f0340d002c0f81c84ca84000b460400700241071111f2850080100c800601920454446001c0d0b40d80080001741006001e840d91010400a0341c00b090244802d02c1d40101581e0f92008007400400b07045c0182030186602c950031054030b610008600304c4440c0b060799500c030903842d80c1140030b2194201501c1141e00c050722035101d2260782000c010348074440740a0360051103c01000010301d41414101 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 371130665 1250 371129415 371129453
    0x40f0c2c040207050106030213020c120708072301020d092a090519020a020c090f150103050405071a0a110c0d0201050a020a0501050c090307090b0a21050a0807 70
    0x840e60050000c801a940310112000980300581d60300d920389010350050100790402507000c0d220040025582e0040d40c050720300806440304440842c03515601c100ac00340900403005042e0202002040e000803400c0d4655a22030780d040c07141a41500042110a0070b98001c00e83d000412a5250307088010300001d818141c1c48084031000e50b800d00800280c07601a9081b442c0a0b44000c280c031240401c41c6424056503542540840e2801192512882da01c000d4440030030f5042c0038880c180c540c000c502a4141e202d00c8500941c0c54079070000c101c0096400550142c44000c1c001e072060700911100143c500c4c95002800a0920300d5403546076a80e00c00c4201600001c0000481c20305940092180c070030302d844240b80c00c14241d0702401c7c034030344600d1801001c0745815100b00000f8225403c2009000100c01c01c2d50142c06002c1040341a00c0b181741d00d032403550f8100e44840b0b112603444810b9030402c0104c5052090215610261211803020701807860719440e2605503002400c6072481000501d1200303104c18140d0301043d1002c1 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 371131915 1250 371130665 371130707
    0x1127040608150403020a0b15010806010215060f06070204051602121603030203150d03020c0f06070210260c030a06081603031107030f0f0c1d04080f0405040f0c 70
    0x520002035940c1800b0300c641e5020108a1001c2400d06008103c038040c2d295214840074114a0158010b141443c08050f05070301260806001c01c80310360000c115a0701c00292000096680e55400c1d081001240003500f025810501c10400c00015031203601615215001600056641115249000740703400380f2014111605c541c02e2040f03626407600c101e20784a161b5050300c0d000da204d4407607038510307000e99552900e050343c0708480a0a950070503030045882060048215082c0c030030300d400e00c014001607202e070f00d81c020341c006211500801c41900074800ca0404464a20621901d414058003000305c100064442d20800d007404000c000020440e07000d1072029100f0180504003511a88502da1054092400010b05100c86a10941c02d5280d08000e00e10045030051a921013600f401d05040c20034200d1407805903a100382d04040843c0190f40c1c01c1e12051000e04454943d038242e41c5036103d006994010411020500714200700c005410750f62400b80b051b81d1740011000003400341040401511b5245201c2010301d400d80 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 371133165 1250 371131915 371131919
    0x4021e0103291207080307080d110d06151106010e0a090206070c0e010614030a0b01050c0304090515040207030804031202090a15020f0f070303120b0301050c0c010c080c03070e010311270406 83
    0x14010040d90000f82d402341400f61201c50001c0c92a02502c0345032401040c061003c81d203c400305d0744a8000b501202c0c1001c1d20440e0203420032004444000020360010095401140104944c80d602c030311040d030112118000140640701c0e54000b278803688c004002a01c5403096500140100812155001d0040201e42403102160b1892451061240002040c0e040c20541d100c0b0140d460781d0049040345c00c1503410506995403161a030603202c000b040b05583e602c844426890020059090130b00c00c54032030387c0e00741c2c450f511695107e5400b19103500003142e02000d1a81c00340620380c1d450321902e24500103403003030350103148056002c280c0c020310340800740d0000c00d9194807000b0420181040070507c1029280c15180698014984c440f95070054003040ca5195010746c0b800d401c0056411050340a1700301c60051000900540784611021181c14174140c540b504070500410104203940d0107000c1c10b005500e4181004500d1141c40c0403458030a0f0041100a1046605c031a40007000a41d0800d0740100c1134400c85040010074 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 371134415 1250 371133165 371133179
    0xf03030e010207110f031c03060801050a0207080f030c090a1205010b100e010f03020c0f070602070f050108060609030c0d0b0a1d0a061e02030702071a0304021e0103291207 75
    0x7001d540c044e07009600003901e604064400f4801002c0b4111000244641900070a01c000e00611442c4540621940307440003180803405c141c002c89000b96003000302c07e4109100014408c5c00d9920180400740c2c0031004110b20360b000c2d21003107000e100415003d41c6d404400c1461742041429140ca6440c22031103400c1c80d5010154550300700d03549020340c4000703280c409101c0b190142c0540081c8202030300c1502c00c2c407506140034446000000c40c00141c900395825109226a41d2120340350368481805580c2c041600540040c0c0e66040800250564020060071a10540c09000120f14510080d04d01591000903000400c030302c9002a0042c0c1000030150002840038074030700c9a8690300d0f0981d0140c01000c00c0d80ba481503504480d940d035954503100c0d0000d10110b60b00d050408003e562903101344600311103c003034040c4001513040104c094074440c0da005001c0300804410f03170780b516400790460742456052680d14000c0d165500c0070261104100d010216014013101c0e69501001210b4078040784441259208400521040d = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 371135665 1250 371134415 371134433
    0x6010f081006050d1e090c0611030301060c061803020706110f030d05060f09010b040e07141608040f0603091a091209010215190f1a06090f0d0f03030e010207 69
    0x49256141903a00e0f13524040009014004514081166100005115103001142d07170003103000512502d10350101e6030342d6542c1622440390407409011642c01c144010400c20380252819252a0300c80c0d003001441d200413501c00400680b4130740082e001680701c1c000c14002c680c0c002007a90300f84034008008280140741c0c12040c0d03030742c0e1241601e000c85164482c40855480d40740d0000d41080e40c0705c000c0141c0700f40c0d07850f10742c0000c041d0001d1003140c2c062440e01c404a03903000e0003003130300b1004e20402907030103072034003c00d00d0084e0301545240e0710841d101c0c0310400000504c8180c03200707601c02504050f42e011920034001c0c00d100345000d1413540c1075000f8418601c02c0c4181850001108100d41c94002c41c055181c480c540010703800c001e0b5051320584400009803c010741c2100e0204491041e4086e890101f10001c4000707405403c03640c1542100812156280101d030031890020701521580c40002e104200700d04121001c202c07510f0804000702c1e03922414400100805416005102d00709100740000c504010950312500707030b1 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 371136915 1250 371135665 371135669
    0x1030c03021912060504020f070b0c130b090a0305030a030c11030309190507050402042c0405060604020d060b0d060314030307120b270a1a100305070504150806010f0810 74
    0x1e02c450003d11009811042d0810001441c2c01030085484048440c0e12641c00e500039601181c68450030000200612a24420b8400050f40d42c4c1c48290a281894245100bd80c080140d0903488028a0b8000001070400c000a203900c042954001c103003824264009002a50b980781ca0740e50307640042c020440c2202c000603882c8098100e40c0950b00c00c42026041031400d0900ca030f000550420f00006012554481c0b49000801e11110000000c0c40d000340c282141e849040142c4000f413154211101252030b40c60150060a03004000c0b090000c1c5299880b412100d441e40900c20f01320307840da1a203800300f09005902d8407000c140392045010f5842c524003100001c1044c1e600d0505503a403140e41c2c0c0340d10301841d203404824040e9044640413a0b41c800d03c41c2c902d5054081811a07401721803500700116614050108007127450507043c05070050801c07002c040c5041c1d014000040003e000c0140038480011441c0124404100000c4192240700840c03c24400041030382d4200b4041c0e006000210b02848440c494210058007 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 371138165 1250 371136915 371136917
    0x503121908180a0b070e0d0b07050a0504091d011103010b040603180b18010c111e01110a0309120804081b030d0e0c091503030301030f110604080c01030c030219 70
    0x550b5840d01d49158603480034400103054410ba00081e010841c3d210076007405040c0644604455190541c00c20541c9601081c00800f101003400204080600680242c1101f0145003021410603480741010400c0b1340b0301801a0114109001200000c0c0c0000e110380b4401c1d00b010035040d480c56040040c0c0e10b00c907228500c550410036076610012400329178041c219800c143e0340000c100200c0d083c900007030b00307014003048010180d651a0041c6050018060464041d80320007210141002a170701020310194500038400c0342c601d65486680c40c5403165070550040c59141c4642e1400901641d071b0342000345a1418184114042c001c1000500c0049486c1d20141d81d251421003204201c40f1000d07081d11410740c080c91542540303860420303202c10f1040340003007002070800c2c0c0d040d41c01c0e21456a43d12040305c116444102078a405420400060010481040700369440d130340140844a481c1d0505800701c2c000e98055400710015070040c0c842e5400941e41402414030f501081e18007541080d18401c1d01d040c80c14410300480c4 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 371139415 1250 371138165 371138177
    0x7050717070306020c0d0908060907090b0d050a0812090706090b0307020c10020109050609120313030201060312030204030201080f090d032c1c090f0b1602040603030905031219 77
    0x100303048108000001c040d60b880402903482c3c410000e8202c3c2d1b00d20381d0101e5800030804c200c4e00803900c1d51001990a200c0c20075840200340d05441c0c644800024403132a071203a900807030159403000c041013003000015112171041980558a01079203024485581e0090b001d17074110b8005560403c03c15501000300344c1960050300005950f6280c5240592416a0742020550040010645025456010b520030700c400c82c041c0741542c406540e003001150f115109400b4900e4120000c0c40030030201000e84c0010b000d194030030b0000140355030b00e03a11203c4503180c1c60626100040d4000509104550f880011300f5086a8400e81413100c500700b51160584909c0c62503c1081011703640c0d000241d207241c2c80c0c40c0d20524502d01c2d0322a0860304c0b0007040300507243c00120740c03840e200ea13000c1e9030019a003900c14401c0d0002c84500e00300407811903003414071448895003c49074010343c0c14200704551001da5128403406008501c2a10782c1017120385441c0915060540c01e142d013a0503104180200c08042c05d10020001030b00d00c0f64a040 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 371140665 1250 371139415 371139449
    0x402030103030c2a090b01120912031d0319140f1e1602041a0a030803071106010b09090c040308130503070605071e03020703050f030904050c270120060114010302070507 74
    0x100c5a1400d48802040e2230340c100400c2c0c105004044014003d00982c2ea5010310892400c800280718143c07150303c00c401158001c004800a41c9100076542c000b0070402d01c0c010590805203401101c060300101c240c8880c4001c0081e6120805244904802da400d4a44134034604001c856000302030342c454030040c06805151174803500c2628407402802070b40d41f030348000d090300b0420392641001100d076041101c00034046002e070400303072004032000900e40e81200c610010151034211107105011500901070400410404217000200000300d1400c041d000a403114102c5140c200e10b81030070980307402002c0c0e001030140401003000b28042200080142d120320001c42c000c0b490200d07245412403078141d9952000d40140a10110b05441200100041080410449051246490341b44d02900d403031083c00046410490106009448403d4a0368806140c000c1414000d0000050700d01c40c1002d92400c5044800d00c0c1c00c4140140406035100d095980003000c281780843c02c0c481e09994860382c8071010301810902505482c80c1c = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 371141915 1250 371140665 371140667
    0x80a0c0903021c022710050306010f030303020705030412050307030f0810030803100e09030301090c140a110106150203130b090f13110a09060224011502010603020402030103030c2a090b01 82
    0x80070f1740050751403034000201c060700702003002401c000d40380601c00320b0f0034030030006140c6400103006068a0300300243c0030401d8075543e810b500a5101310001c840e540018880002c1d542000c482400325140500c001e15034a1526290062802c04060a2101445021428810340d842c240e0b50810030b403684800c4495485d02d46e85091083c0c81403a501c120412614441004005200400070314126500c072201071041c42c068801c29902c0c01c49084407020300e810140f00f2803c81c00e2041e00c400c0d4002200f100001000c42c0c81c1e4030f030080c1502a510401003d680300280b0800c1c01805444a00001c000f6001d240b07013000e0f400d50005034070720041c0b044107115102d021105100c10180351301208040c0240036525036a20740103d005000b00d005442140098042c000054034018081c000b503041e9110041e8003089144e0808400c0002d6074100341b26641199600e03100800141c4a910045020718026151032004881d58038048440d42d04d924640149a01c1c00480fa054004560080d142074400c94440403e8032809400 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 371143165 1250 371141915 371141929
    0x15090e010912030204180b01020606010f1b03020124050d08090315011410170a1a1e09070f09050d0212031c111e0306040e030a080a0c0903021c02 64
    0x100038064400502c0c486081c01d41650040044507107400ca9a010312595a00702004c5500816429025070440300000328190303c42d030502c604880c105d0404861402480f03500c160380e502c40c6602140541c0d03407042c000c404421f0b01c081545e000c011500d607000c95541042d01107a25880d00d0000203001d075101180091203682e05000d102007140c14001019419a0b642001c0f10102141f81650390040c1c070b400c1c00c2440c2c218401c01e6507016100110007c003807aa1120b4104074001c0082e440030115841340c25440e0b083c00c2d60741d90018040751a0f05a40782000c178044004001c0700040203003800c0140401c0700c80301c456607600000c50f0310884404441d80d41810551f80003041d1507142080b20300f000c0c3d020026070350000141203810081d551044190030040f150701d146146003141b003407600406200c00c525481208600e0340344004d41d80140040c202061500a09030341030300c4c58000c80003000c0400c10f00303800c1000901c11441404c2506180d850710365034085c80d5401040c1d4049541c41020644081002881c0035516010 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 371144415 1250 371143165 371143181
    0xd090602160f060f0504030813020604080f010e1c0c140705120f070603060f09022104120e0102060709060507060e1603020a0902181309170406080a15090e01 69
    0x41d15032031107251464400210a10780c84100c800515103144882c6011030352140714807907a0b143e10b03544c40644034203401802c3c51500900890b481042000b003c10003d80070301104124140303280000c28060700000c002400c00e454088801c1c0031840810050003015030103d6820515074100c03000d64800d45401c014242040c1031034000a1b089130205200c0d200c42c4d0b1000410080c1d401008041e01c403125100c1204400340d985a01c50f03c0f03a40070039803c0c1404806103d80c0200b038003141c8200c000c940e14000c64802103591100b10340c2590503a21410440c484143c1001401e20805401d201030311841c80d0030f07040a800e00509000c1d9208004001c183c0b142040460f0b80182c50340c5206200b00c8411008101c2c00c07569403940d038001280502ca5912000524105500955441c40c1c0c08541c1882c24145400c1407000c01001280c684003460b44030036408000c51220384840342200b0300807810a43c0c0d581480000303406840060316104d4400d2800000f00000c0450003110301c151820034102054520010f00307100d024061072 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 371145665 1250 371144415 371144437
    0xf150b030336130b0409140f06013003020a0f1b1707151809061706041a130602040f03022103041412010f0e07080a02060d090602 57
    0x780c0b11508050b41203400c03200090b41010350160205503142c410104444411260b04a0443c02c910041400360b43c00030740d54050080c1c000140303941c3d140c445010000e052004880c05400c0325044079182d901c00d010740743c09409850703c3d011140f100a440e00c10120743c45003400308407846458002d01090320901800608941101c100b05901c070349400c007101c01240c0752404810302e0510110014500c10103004c100198100840a0151075103001e44e40b200d04061007180e0343c1082050300010314000c52158001c000360041036030004555003040c01092030382c401400700c5809a4042801c0100007009001003183d4229000f48501c0252944c00c16a060ba56005400400c11400464085281e500c5c9101c00b0342124000c030f4908085e042a03141003e484140300c3d200b035240350410081072013000a034a071250001017000d00254243c0800c02c0c4403a007140c0c030389001684450780740e03403180181c004200100b1b00a0080280035011403040b5a00081483c0300d0000d007084025150b1441809005455064481d2a408 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 371146915 1250 371145665 371145667
    0xe0a0f021b0c010f110a06020f04080d03051012050604061e0f05041a240a03120507060e120a0e030307050a1415150d060b0a0b040f120f150b0303 64
    0x440c554041d142c4180340010743c00140e82082e22100c2a205080304569041d0140140645008503150003001c1d40c0100d00d10710a60201300000114414100300c0440c101030956070015050400c4100c0d58603101f0542e0180c14005540c0194901107100403841c242c20a40c0420001003032104215404156440c0000344803060b490944800e00c1e038030b21070700114031641c42030210200c00956a0803034100d000c01030b03d0132018058000c407181c901c001d03410507181c407008004159903107042d920b0356240704181400c0501400141c000c5105070402641d4000c001c0d1000320070000e498000d00da2202010107016003524403080244c80c00c450040340e142403007103810668004040d2103d0810f0341c107026260001980401d525482040c64895184234008922402641c400c0041b50046c4164000c00607944c0e5040001c0d918180c0e502c10481c6075585641881d401410007800007901c4510b001e2802007407403400e502c1401d440740c0350002480000c40c030010103150291310400981440c89019070002c0180a640300740e940500c0 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 371148165 1250 371146915 371146957
    0x3440a0c060e0d11010513030f0215010308091009050f010f1e030b1002010501060c030503180114090706170109051e010602100e010b0a0501030e030c012406090e0a0f02 74
    0x801240f400c8a1420039155031140c0c0b8100801c40382220703021511020b107105a80500e20009200b10f0b2001e506004c1d520481d00e800410040c40220403000781e1040b0f544000c00a440c050700d007000090b510b0b01e00c003241400b05201c0e107130202040c80841c240c1e0603281000704144844071940e0244481c45110201d03158280088000c08601034010401c0d841524441c007840d0a00c0c200d402e00c140a1f0a050b9640c5035140c0e10311a030341b03503030654650304042e0407030003840b64186018150707007001d01c03851045211840d00540c050815600b03890601103650000310030420b00c034a440044811468500c0c0c115054100c0002d10350750f5114100c141510f150150300d00e40c8607950000502558000307160f0015900e405800c0010380e02c40040d403800ca81d40a8002904401c146074104541c1d8081d038403035984d4041b00e00036030b86005010050300382143c1d030b01245880222900f0265000c602000c00e10754004d006a03003401c815003800d01313030b8200a102d4020b010f070f0609500e41e0780403119504640c0550760408000950028403030 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 371149415 1250 371148165 371148191
    0x30a15020301260c0d03110109030206010f06020d081306180501020a03060b070b040b0702030d060b0d05010b030c030117030d0906091b050f190b030103440a0c06 71
    0x241c400e03c02c0c103425a604001c103150300e40b000d00e040284906648000d06000e1094002c1c004098640002503082c0107504001001145007801b031080468420b41c041d1403d50f040c08582071014485810079400c40d40016401011103030091181500151045102034060b6280d18015018140c2c90161110070392000c01c2000801c641500685801042034500b40800c5072a4005a030b514000c1c1c0d580900209641400b28000c181341d0340d4044d030486c0c0288192890080045110401c0d900654801c0001d0480010b00b4621f00d0901d200d0316014200c6040c0c0c0c6131a40c102200441d2207070106004044160505004401c92002c0c20401c403040520340c3c6030700b40b140001c1c40c10014024418a0800c0d00d0303000c680c041004c0c05960380403280c0261400146590844100360060100e061114540e8842e0340788803d1022490007c0303030380690b0085101d2001ca41c551035280100b00044568071b100b48121041c05a651021503500d400348601d011303420000d541c2c0360400d02c00110b0310805c05641c06409a8070f01614031443c2 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 371150665 1250 371149415 371149417
    0x9050a120518030109021f0c142103041101050f12010608010815040510110408030711011205090c04050702010b04090606060e0105040506070605040201020a080d0c030b0603061806030a1502 83
    0xc074146041100e1120b80500502d420f83c0c141000085d400000001c40d2517601204001c072441c2c4007007514003101c01948695807150741503030042c2200d01540c8100c51a0410000c0c0071140604140e4100b506d5040d410b19550713051b0902030098041341070010103c7c21507031010414090b1074a02c50b200c00031a4503940e55400183c0580020300451035140076003101c0113880d8852100031070096038441e004103041286910301c02c000305210007400701080000c00c40050380134070410140172001e000b4400c55110590410001d030a04034401c024201040c24030041101002c004a042c000c4924166404683c0d070b81c0b425001c03401001d0f42440543c0c4185002107d8080c4101980584103889861316400321184100c2300560300c40c007403486850350020040143d80000307000c94001d0f5070064410b0048400c61207403039480009030f8200009120545603074104141c0080e83c1806003469101c03083d0346003840c6040c01000728803030301e03118004039602e45421000326205480403c03003012455040f82e0f0304442c0ea5000000c40010b = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 371151915 1250 371150665 371150677
    0x31e01120210020d08010501030c050d0615170f0114010309140a05060109150302060d09050307031211040602031602010e031203040605060301060f030b072f070803130909050a1205 79
    0x900550b2407880146400007903544244419034960b0f420136840c01c2c00450107020196428820031000788038845640f2994081e0070090301c001e29a2422122580900500d8415840300c41c1c07007404a50001c7c064124101444c185c155950170b0400211944034400582c041d00020900a0514845961084520301c1c04079256281502c50001d440c00c03642d072100440b09451150810ba00c01c2183d245d0f04000510b803810040402030b5407140080380503515900c1d40b03421034120220540100d94482d6030f0001321442c0303101c2c2420000301031001c00d0415080c01002581e0b0300a24010000c554962120070041da80502c49819200300024201c0740c18100701d1a400a00307406c10785040711a5418180030a14034135047c01068240c0385403480040516186071128215020060017103014000302c40341341903c2d01400804105001a01000c2c0c170084a043d0100754980029a408860103401c14854495940140ca081c07000b140e003803a40c00304d8640e840341481c5003006903060b0020807038248251803458560300000901f032 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 371153165 1250 371151915 371151919
    0x40e0717062403191b02012a0e0f0301110703020f0705010c0321060f1d010302090a02070c050418050616080403080c090a0902040515040e0c031e011202 67
    0x1015110441404000405041c5101d03030124000319141e5192080b2014581c03083c0c2d100481040300451007520000c4030100101542c1036102c070144c03045640d8090180201e54842c2050b1440c0700040210505111149110460100b240038080a07101c0e03030381c0081404804200500070003841540d000003840e9640310200071009400742c0c002d00a06000c002c524181220301c10384803c5c1010605a074201c9070754240c42c2c440103503003c2030b85248060905510603d0041c003001c1d040c05500d01c0c1420800460200c01204240341042404014401610b44141d0f0a4201080080140e16a6841c0c0f03460103180e4140c0c0c1115800c6441c000a0384252001e2800d1030312014000c2040c1e0307849444140c842c2820b107901e010303c640030840500c04900040c0c41031080e035074000825041e49090000c1480040c1201c062a405040c80c20f4001c1001e00035072030300c181907202900240768200c1c034082c079280c82c00140c00d60050041e01e1480000c000240f0903006142e005025102598401c4590b46c4c5402600c031107800c01c030005034 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 371154415 1250 371153165 371153207
    0x613050106180504050c03011e0918020925050d290906030d020307030c0f0203030309010501060806060406091208071b1503110316121d01110f070602070206040e07 72
    0x783c030f0800c2d2190318011014610190710b56070a100c032100c0c94aa034205003140c6035400100004400c0c00301d2181c0480000c001154152040044c01005481c08d00070740107141203100310b00300c901041c111a40c0f1a540214900b0150348502110200d50014003154080344201c0c0c00c2046001012903e1040d0582d171810210b0b48504181c032244180b5903101003180711038015034002c00450002c0307400303140c0448106201c0d441d0a0075442c0d050303001c6410368006550403409603444600500c00b40f50014201d48c0c0c4004181c8a240c1050301d400c60050103074081d44030b100820f01e00c011048092240038803c498502e6082030b02500f12440040e58015000160300c244011200240110b85115100e80071f038050090741714407268115112060f082d200601a402c0080a04c0201d101385892020a40140c0400d8400e0720340b91070340d01c08030120140c25900381e1208106071410400c0130b8000c07003040d03100351880b858000200686500b19840410301d03034880c541007010080e654900b00030440340d20403981c400c40d080d490b03c0d007 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 371155665 1250 371154415 371154419
    0x302100e0a06150b0f07060b131406040b060f0d1104030302030c0f070b03190906050a0f05130305030103080a05070f120f0c0c060c02011716020d0c0812061305010618 73
    0x341c0d0042a98001e182c00c03c80c0405c00c1181c1d205020000c0c0c0100e600507500000c500411200062500c00900300b01c101e129101d08020110303034681c614640c0e0051043d6010b001c00301010b000204144103020074101c44100c04035800c0400c0e649640400e80040f58075849a6440d03031071b410040e607290410310030341920f4030400e1242404850b021a59134221002c1003400342c00e64a0710440d2000e22158496000222a6504070840216035035000ba01c3c01081c034500f00180f403540040850003622001002552088a840101340000c3e50080840b811240c001c080c80351031301c604103403c03940d40c030807600050b010f219202d0b050800c0c080c3c41d00c09505071a00c60b44465142c16280d51040d24003508948020b0000b10301c1c10f004105036400360200e4440d8a02c1458101d10036907540d015584001c1c4187c0b4101d04d881d00300c49800901c15010400e004008206003802c0001160079a6038110a210305403803803110348108030100c0c00c10f4844d0a180c1c00c10030303e074550a21540d0703110030000b4081d10f1804582c1e400e213130b52a040 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 371156915 1250 371155665 371155691
    0x1701080c1302070f02030a0c080106060212160317010603021314030a12030204090501080102030702061e0103030e01110303150103180b04020409020d020d050109030f09060e0108040302100e0a06 85
    0x102801403001900404081c0095900203000f9042181c065581e0890300e06807070b00603a02440103e140e148240401c0300c00f10b04000505084544540150081d54415411031024066220544403540144c00d9160805003152508458003100d640503a554010604004144103806130081c1c03101c44101ca400c1c0c00a240d880d40f1480f400c001904000d5003680040c0c4002010070302000104c0011401e50801510305940d41224400b180c100f41d000344103903580402800f40d07a170343c1808000e820407034000f00c0c0380320040010050451200188801024483c801c9803030542c9902410610313009400c100d0589880340303070003041400807481081010b40042c0c607100c0380c890440124000000440d400c682c1890060740d69500b80300c01031078095416130b404402c200c500c1c801a80d44102080c01584502c0010428011030304c1d0141101040c1161074060100b00038050200c2ca50000840e000c012007482c0a400644440c02c00317038140038007000ca00c2c4042d400c00c00c9215001100180609001d40700345410802c803d85258 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 371158165 1250 371156915 371156923
    0xc1909030809040c2030040902030411040c050d1103011214010b03070b1801090509130f1416050a0806010509090708011406090612120c0f010c170108 66
    0x7050810300740701c203804a06050303000d040202c030241403451180c21020001071070f58444811004096008041d0100144014180c001c4006020261041ca05840421031403d0340036a019a88965038040006070500007620044045010b015204110441510700010505d91001c0003d82d805030500085460308060074048030b040300e00d8101c2c03c0c0301066240d521200301f2580164000b03090741d03c0d40151010380d90144600d80060041d41500380d0340b103138141081c5c0c104504425402c0d05100594508000c141c9403c0d038016401001103142c4072000c82c4914002c20421240c41c0b0107400702c500c615100d40708203000501e00c54421010100d00f110103640d4010003a61382c00e00d016811654009400421490030901c0401d50081c1c103080590303d03c142c03500d41e0706007161300d1180c805d4540400d010501000c0c3c20068020f6030004419504c81030211014001107581c0c04100900c1c929504000941c120b002406001508242c600300c8004d00012080c1c001c020040540d5914142030314610300300014030184001 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 371159415 1250 371158165 371158169
    0xb1e0406082505030604091b1706090102030103030207050d0f0f0b0105210a0314041d100915050907030b030f06060316030506060907120f0e01060f060801140f03060c1909 75
    0x81e071420703d035503245c200f4007001e020446800c9401c5d803952001d090496010403090000390030380381c0300c140c86141144001454001c001d0000d001e2a44104014004641c0c08034400c0165402507525015036282894055140c49040c070f0044c0446801014240800c0540000c00c3d0407540c049846410a003554101400b0003000d1403035605a076032000190b9000070b0302480120600700300203e0a5420280d4403a152040382110071400441e410f50b10040190208045500c0406800380c0003040200015550141c001e0b8040c0c0d008980c81000301a0018128900c01c0d0009011a04050f094a140582003071449075030391401d6036514401e004000e4621400030004520b00c00f02da40103401801c1c1d43e00c810003800002c3c14003a10030000c01442502898411341140100e00d4424001e40c400182004100d078454219251a044604040078111041001c1944507a841e0b040d00c001100079407003c00d03607a0024900c540007490a03901400368004005001e0081e40189c000f08080b1540100c1e28403100740e007243d00c00390034 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 371160665 1250 371159415 371159417
    0x100e01110f16020a271103071d12070609090f020c0d0503060613060e01180f090509030c0f03030f0907030b0c0309010e0105091e03130b1e04060825 65
    0x1402081c2c1c120401c0d01c911078105002820782e051190311002100c0300910030703034580c0c1c414070303503980804030141c806101d030082038591006028154109240300178040002d400303081d01500804407000c11940e882c082d0306040700030b4200c101c401c003950719107015000e21894030818480d1072415001511002c004d0080303940d1501104080c0c000d070201c0320700c2910541c01c041e2039260802003d0040b071121492481e074441c068140340c1c9034032080420f0a000140400a1040d640e91290f1107840200480e00e0300d01c21540542e0712418012540742c1c0d4031324080e4510300036601782c0303a43c034441d403040c0a8107404007000450141d10662404182903036a03a24481d0388004074030008044078038220019002c84565400383da00f021000c1c0000c540301c04c40641c414250b41040d154041d0765045035100349400070740c820f9070300300c0091010302030350604000b0600b500740910180302e00245010700141c00100840780112441c1141c41c0e0002558403203480c3c0301c005101d1070702121090f0140800c0e80d00401e24aa000080003600550707 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 371161915 1250 371160665 371160667
    0x6020a08070c12060e010c020f0c220f05010614040e010b0304030c0609080901020c180403050a02030c060c0901110c0904080c0a05101a09040b04030f11100e01110f 72
    0x60340e48080311075118800c290380100a85401290700904203c4048102d40a2a40401c100703a03684002c83c01c5a8904c0d0480003035520100c10410f1854003c266012815411502d0000d039070300c0070b500349804070191520150381c0392601e0584101504264032a40c141c0e80380355207010a900e481511960940b02d41c1c010000c44c07c610761300410190341140c1c000c5500034407900e4072184c6c2d950681c3d542401c0d220017207400c4074a501d000c210f2118039607040000322011001290810301c0030b0148041d400c1d901c1c1024001a04000c40052642c01c43c500030800c688070806207501710307070300c91030080c0380d042d45900040c50503070004400240c034110300c00c80021400b80011005003440c0203500c2c0c44c1d440003800d034081c82c0c081209018107403c100101c2c0052103119440101a400440d01a01c4001508561140c81c42c10610410b040414000400c28190006a219034582071035441704005040648440340d05455407016849070606400c0b034841c6680082e104040c0303c4000307001940c91041c07010410301a031100c032020014 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 371163165 1250 371161915 371161933
    0x70e0f010905060d080c0a030f0903151812090e0a0204080d1206050a0e0a050108120703030203060103021902030703110d050a1d06040e16030204031106090301060b0c0f160602 77
    0x681e03a00640c2c00110081102541c0d902558030150700384c10103130080f183e5030004612a001c2c5074100014440d01e59452400d088440d046903134005c44134124a601c40182d42e9150328101c00400110400183c568101c920000e030500100001000f4400500039070000b8540070300030485824080c025241079496400203404590709040045400032101c82500d0342280e00c690b030014503521201c0d111000385c01c00c807030081c25503c2d0441c4440c09541c0d0603030101c4200c3c0e021500c1d03455042440c0d01501c9006502d4a800f5139282c8800300120060b0040007080c03103c04d203a484502c405a0380003c02009043d201c0d844e403030400084240d2407901d801d8402c4041e0003042c07041180342c0440d849030096801c0d44ca00ba4030045050250300c0c010400c1508240c0048002d60902760600032106140c88441c03201c141140b500b58501415544e40a01d550000310145010310780110b00808265001e4220344050100c03c42181e4aa01c040e418940d9136801094400b599809040c06034241c0b48440070540d81070396107070b400800c00e800c = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 371164415 1250 371163165 371163179
    0x50c03060f0f0415060207140a030b070302071b060f110d1103040b0d1514010516050f0d03050a1808040308400501020a1109060d02031905070e0f01 65
    0x3114500c4142d030200b58000741c0c00c05035a46218412240c0c40f112000c03010b5a003030450113454528603030040c2105d450207810710520b5590328110001626884a0007444c651902c1c01c0c144c01074051708000412082202041449644044007101c0854404e55030711000c070810342c0020f482c105485840180550000d4614400722405004400c0c1260305800407030385000d40d5070003441110741088410304060703a1180300070035902c44051604005000170501a14000e104040080e110b4451102d80320150620100307464140a403d20881030111402810751300c641d45015401001840102e07500c9031558a41484028a440003052649c0c02e40d13480b80e0300510780740c1107031644801030b001400322035000400802c09284e040d1034001c400410203100f0342c900d07584504040c006c52405a440d0045030465110750110801b060800031076207080740b03054039850310a840711350110300244038544010750184543c483d1268401c5221044490450145080d2641d05458080d60860100161988100d003480000140401 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 371165665 1250 371164415 371164429
    0x507170c0d080c0c0a0605060114030f060118031a040312020403020a0506071b0303020a0c06051213080915031005030102090306040305090d0c0308030703060f08120c070b030127050c0306 82
    0x8469a00b0105040a0201c19134904e844c509034001c55450352160148070503541c00404d0f4000c091140c0324018218a4200d4440c458210300419941c10410401c10420241002a601001541d00b002c041c214400c4000725a050100041e00c048001680c01c107400d0000c207031070384240c030190780d0b0080450103110300d401c04000d415041600c0596156044959401400c1140c1d030208004520a8014250070100ba05141c0c1c451503280c1d00000a0040400078404c02101c01c400060340140d841443c82d82d90f600c03600b0000d245029a004640c1c0182100340003404403041c0c0406144582c04245520140300c1d2070f1707003d060a03402403402c91030f0135074400da01090004e401140a0a01e10802800d1403400c0510754a410340b080c9000e034030923100080000280000d041d854050000903001d10350090350100d103807450ba25981c2e03468002180f241200442d1034013019000340001c8006010030102503480356103c50014200b003121400607542440790300035620314000180942c40c4030340300c00310b0b911781140d0780d6005003e00c03 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 371166915 1250 371165665 371165671
    0x240109050904110904120216051c060e1e0c150a390516060509060d0b19050a080106050604090b01020f0a051e0c03030304030509130c0507170c0d08 65
    0x19032491030540b0300d5102d0790030f02407040b030003401c00d03080241551401a0800780c001c4d480107003a40b0b23240c80134400f94442642003052070039605032255800e03840e818004002c2000d00d46c103802c94041c22140000480c1070058860540407941c09940b10794180108004150310361012034202584140008107105005a213060000c5001c030b041e1044850b82080426120340c0700f010008604a502c00c620410722008016213080301c00300100391404c45040c00e901810600071101410322400000450700743c5d216480c3c12041c6082c901030161a8030f03401484010b80c1c07042c89405020f01a80441c0d0300040c885405000b075038125079001e0a6580b0f02814000f2040c0079020700343c0d409042d4400d0f1050a0f443c0e01e4100108229180500042d007405d0200382315105506140d440ca4803850351081d5031160301a60044210fa07085940740c2005550f8424002c0130506201c1d2807800004040e182440d5859025042030050542d0b6100d038000d10040c4001e1540b61069004150990f4116440900c203d0803084c0580c10300c3d50 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 371168165 1250 371166915 371166923
    0x30f13020a0b12010603110a0816021509070603051b04120602090d06140106021f1802090106020f070b0c100e01020f221401050a23030708240109050904 67
    0x101c09440b01c0d0300900a034400025040020080401000300c0d5070b1611441d0200034103800e01e00c1c82c2400802d801002c4c0e48c00030b419410744005070341902e01d80c0ca000304511540901142c50088151900d8031100da1210010700c039800100741800000307024405100c480401c20701c03446000300c0c1000c0c104404014854403805044a00355420004000036648051107100b200e80300d03050124401c1040640c2e25600f0034180e02410565020325402c0710550405d8202401c0751001700c0c000550070340d414101003981c5450800103034208200c00001700d03241d94080356551002e02d13401e08131070319141c2d00c02d1660301c01d1145005100c05500224004c409054190304001d814250920015041426210001b0f295601058090045003c1004c4c00380b00c58440f034601100a240e00f0380400d00d0400c0ea000060030314480c6c8424001042140c148042040d0349000b80080803074103020b032150700ca02d4100d80c05402c8a405a500804089020700040b02d02c81a44812075800320041e9034581040b85060148500940040c000711 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 371169415 1250 371168165 371168179
    0xd140a031409010b031c021e012c0609120f1e1801120207020a0e040c030b0c030a1a0a06180812040303090e0108031b031c050105010f0302030f1302 65
    0x700510140c444014000c02c015800000d400d02c03418201442c107584c2035040c094045d600300d601034001c1e4010503c0e003120183c03000000072241600302c49034010010401032601030103508000645013120700110b9a40500c03400c00b124101e44500c20441d81d5082c8941a490500000f0130980c0d10840e021806030030045406010a03c00320b0450100711ba2540204c100c1444c044408110340c0714640c0d001c00d1002244404040031442e15809401082c100c0d4114001c2e1540300c480385002c10f0030019414011001144c0021209902d0704022203115080d074416140c4c000040d0401003e80021000302131182501c5c5070041000d54074519082d0142c400c00c00d200500e0300000c0d19040300241120042c4203140102d013206032410384d11401c514010304620000c0d0068a14444480018031401c600001150100840010b90035940c44115442903e907201d540311904010f600090080c443c090a80c218505980c0240c0741e401c40d42c00d40a800310102d00046420342003050042001c551b0903041020003a5070309002074458 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 371170665 1250 371169415 371169431
    0xf01170c041e113406090203030f070308060906100f120b030304090219050309030f03150d0b06031903050301090504080708070c15090302030d2d0201060311030d140a03 74
    0x2d0000c4403025800e01c40000400126000780c1c00c1d4804118004c2014045828004007640346400c0c04c1e0400044000d013140e5440120b40150344d402c00a80d00141d094510b143e64540c114a030040c0304c03080941d281c40c0103a03031780c20106030141f600e400c9509941c2c1a5684020418500e010201c903081c20507c44082d0300380c5d8840080c2020389050008001605420b4000350b50b60706c0741e80b00d540f10028803142060800c8001e1003403066800c00401114608450410442c3c4c4030344070707404000840032001451a910140b803644003000c022103800300f94441c01e401c400382e4400c144030303410682540100d40f00003000144100010301030f80140b94051900140110340c42810818650369030307905580141c100b958881d4a114041019104003604498042001c1c904002301030302e540e0100e40d030f44030805883c0d42880b03101541002c1000680403a1005188490600c809120305810003130f009004c0f034001611147c1400491000c00d080005980040d0040c0ea6544401a0803a0724228155000900e44804140c0c442d82c01e = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 371171915 1250 371170665 371170721
    0x513021c0515040212041b0b03070f0e12100e16170a0203010e07230a090b0d0501060b0c06010e100e09150f0f1308030a1116030302030f01170c04 64
    0x24190030700c8400f401442030309103811f001490034a003107035001040d07102c00d50074404441e04900342c1790441c4041c1000065410618025140881c090308800c1d000103400a4500028038005809480d401e260b00b070402590440c1c1202d40c1d191203030344103104d2220302400000c0001e800c00100c029080700c5421306442401c0703181d9000900351820070040325441e9201030001d0015584060380700018148030518140400c070004003181c21440ca07480b035500300d0755441032150711585501c0758014a080d4002d00030840e40fa2070b20134149041d045032880074810701c6104000704400c6134121186020b55904c54000c2e080700c1c90a18420390b00100200a040c550042003002c076164040b81c596140183ca503104400184d1800c6d0065242040008107080d030884004c1c400d150115120710122608440b4a100118400380711402c82d56803407141810980c0c5090700c0d03404510078103525601850281003034950145050366580d03410441003070f50b00c031480d00c140c008214507655490b040c1d00495290784403010600d100700724404c03 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 371173165 1250 371171915 371171917
    0x20031c09080315090702010603020d20310e0705040b0604030c030b010501080a15030b1e010305060a0e0304061d011209060902030f0a0c0506030c070b010f0513021c05150402 76
    0x10f2110f41c5180da49060300161825804045c1d00c0141480200101859900040ea01e03445000000c1d02e007140f40c00040d4202440c0d00311a0700e03d032501408403510210700d02142504913241010f885e03180e58002714000303510001e0303000f40b141185030140141100c80c24402003000416280301c0640e07101000308400400500c1c21000c5500850040581c07008a614110015209010043c01c2c01c030311030329040440c000030104824140a80b50442c8101d119580c07610518280701c0344098003404414071510000041040014501d44078003800c22080c0052404944495560300682c09040007080000120014907207c030f000802c0c50742d105240c880c03130241c802c6000000311500030700b090b181191121036440560801304132000e10303070f030072003008040040d85c07915203c0300010540101403042c1c0700000401c0d1581009015211510b80010711160700b543d454159845408040c407440b0702420841c815541c0524991080d9010101e10000c500002029030390000018078000b05480300b2000b00c80303480802070300c82e48 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 371174415 1250 371173165 371173171
    0x181401141503060a180b040606120809101107030b09120403030e0f09060f0f041d0f070b040321090314100f2304050118080a20031c090803 61
    0x1400011aa205101c241801c0450044c0541d8155044c100c001c03400701c82c1410106205a000810303062251290b01d401005411580d10200240110500210601864000071310403190200d400106030901808191280c031240c0e601c0403c035801c030040400100d026041c08a5118948105075014405403103085c54950300107401c280c0018084c080b40c41a241024400d0b100141c0e000c544481c02c0b881c090002034602200400310900500382110030400b00c1d03c0b0b41d000021500d49050301c0b204107440c04c00c00540c1d160070700c0c03c600300399220f05040046c0c03950809007181e055030f130015002c801e81c00c0e580c89a6075070040f076030307151100f00840c0000c00030109510056818001c44800007a208604e400c2d6203107410343e41d0390180c1da000c0c01e103016015032a400a0710a801c20400b81005030b00c0e5680c1c1c80303040880c01018007045008603051140000c2081210b070900070450302c001a1110743c0310040c04449111900d03605051040d00358410881d48842c0303507040c1110078400d500ca40c40450b040758580d17135615081d0401c2e = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 371175665 1250 371174415 371174431
    0xb0103030f020c0a0312030b03030904050a050402130509030703200d030606020106050f030d0309140328051218011509060501030c020f06070e0f0603090d030f18140114 74
    0x403030380075040540c1807010f100190802c54036141d0090a42d25114106c0c00014558006e042c1d6a11200b840b41c3c4080c42561581c1100400c1041285000090000640001c41c0c04a20400c142200c4068000c468850786001c0e0711761400543c20f1070410f90342660f40364134850f205840c0f10384070030903000f5285c4c5c00c0003082480304d06584c0200d00c3c5880c00d80060309403242034101d203110341d2062203d942c25071000180031b10641d402e4038020071003000905007861044804208001c4501002540303491150015410602e41c0f442c2107000c01e6036aa0f60303101115180504c03081c0c540201100c5010800480d0b0300000001414906000000c005010020b40214005a43d004400c8180c481400300419a014816007014811a002030011050800d01d00c035110b000080c02c0205110070b020390001c0c203840f00131031920401d001801440d50ba00300005215501c00280d001d02c4c001a051408125a0321468019000520350082c0500c95000690703075504584425201410681d40d690110f124200010b580078030b00840706 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 371176915 1250 371175665 371175677
    0xc0702061809010506090d06020306280f05010e060703230c0f07050603160c030203040b0f0909180705010c021f08190c050913060f0b0c101a010f0c0b010303 69
    0x300714280101002c059000911034102404883d4017510350110303001c0401d03480280107a880c0d0390fa4000800d00a4840106a140845107150804108be24141031080c0d40c000d003411041a41d550004581581a040440b5003092043c044074001a000b182140701104050340400020110440f1142c1241c008030f40c850b20710760110207007025244040c401035014080a07250545149828103900f0190f02c0c1c44080ca80401c00326100d16002d2510034401d5402404000401907603600d40250740916a82000c81d6461254a500c004a1820103845003003600d10300704400908001c40c9440e00644240c10500c8090740c00c0580104411141000f008224016084070b445807100ea0619007040b00242c0300300317643c02100030704d8a5543c041c0d00b60410280c85e001203007242c44442c0a10701c0003040ac0030f4040c69024409130a11610081131880c8130078050404154242c0072107040b9603000c20300c1401d03100d41511207c01c4c2d070070358111048075510619205656800c0c03414031504062050343e40303000030142607100f0b03800280 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 371178165 1250 371176915 371176957
    0x7081e0313020f0603062409030102030a0c030c0e01020c010309021c03080f150145080c03011503020108090a050a08030a06150207050103020307021e0706020d0503011d0c070206 78
    0x103010032030102c030f11106a80f20380c210302d00180440e40c00d20032002e030704854054048611801c0c41140c01211940131000e0000d5482c0e0500b0b02c55100075200c40e1044502003810245014985485003900741851030050340240804521800194020101018282d80251841e00510501c5014071041c0c15440d03c81c1c1e4801115261012010311311603130103001140248415415003070141e9000031110100075442e107601c030107000c040811b00a80c020a06404c0102c82045903c11107150b60704c0101f0040354040000d640c0c00203803031000c05080b544003c45050300901606018005544611002503102c0890002c0394880259510340c0c601e40420b40070200c5d9440400001c11001101e0f50152400505415844040720070003c80080d4882d40e41d0b00803203041641c00700000300540e02c04c2103011082c1010006044200f100309020b81d0704d80303140c1e0041101611402ca201981c080c426402c0b2412116264078648400c41100181804138101400c40441034109103c2d0801598400d4001c1802036a11920504401 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 371179415 1250 371178165 371178169
    0x3060102160b120c090d030c02090c270d05030d0902011812020415210615080703061107080d0212060906030a0303150308031003050601050301050c07081e031302 71
    0x1800c1c1281030428080341d050100401c14411050300d515543c02c001d4010156a1500012100d0094074009680001444071080c10f150700840709480720340c021740c0c00b8281690f40006219152186013000c1400d0306c80c4440984801c26550807070704101d500105042c0ca800003070f4035640c3c5180c02c0b2440302c0b810250303030f030f4140d20456800c001005220b61060030500c4c0454501003070f02406030003005010303020b2a20f41c00e42d01841c1c50016031800180140c2100c59500c0d0b040c3e0700300c4203540500070704211882803405184041e50401e00c60030a044ac0d00340c0703000300a0182140d0740c04018020040e0390000b40c140c00d01056001401c21005460701c203d0b54980143c40d03070012030000681501c00307000c180c011200d800c10300c44076441c0840e40da01e41c1a01070070040360318950100e0b01410881e10303510180032002d0100501100c1c16500c840c43d070441c0d0041c000c4444907621001094205d41094400b0054a54104603810006103500c1c042c1400200320700a2246000340100c07a61b6940d44102e9802072084041c0d84d00c10214 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 371180665 1250 371179415 371179423
    0x1909090e0c0105040902030613060609090e010b0f061c1415040504050615120607020a150e03031b12010305031c02091c150e01050f0106020a170f09040e0303060102 72
    0x31000404103100d803000064071a1140740034000ba401e40010004076642c0f1581600c55a52171500c03020810140e862400030000c1c1d065014042882d400d081c0364150440f014020003850000c02800b401c50801e050042140540c041070301c528441401080714907061000d807180b1080440600d5140210340340c001903a0320060014401c55104926000600010a00001c1d5450740401c010007440c140744084000202c0e41044281085503600c80c0c02c08000300c169020880c001581e128000070f85035030f00c517400c00c901590840d41481c0720750382c81070000400c00203140005120401052881a00d800c80318605404c05680c260403c0e0b80035030000801c11042d0400c1489107908001c5540c00314101121038000032026000d62540d035102090894402c000d1180c1c3c0d200382900c8144005082114403096506c0902a02d011510311038005c04050000171000e0000c500d40051640c442d09a10451081c07000c2e000d0140c20040d0000980c43c403d000c002d03000d0700c6501c83c00a110608100541d12490700310002450 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 371181915 1250 371180665 371180681
    0x120b060301140106030b0f0904051e03030705030a02071505041b06110c040207331416110f0a1b0902130b0304060906090803090d1e14190909 62
    0x381c0c584803541d42c140c4041441e640c19140c2a01d804690410303584c0014000c4400c1c801a0781d805542c40040c0020004001070280c01041045400301c10b0050401a041d00c9000445034540030034401c100061205070030340d0040c01c95030311807040d00d500603981c058284100c0303404032011140c84000d050b0300304030340800b21404001002240b034080d26111001d015152200813032010316004980200311a001c10440416800c2c400d02030800090017585460702c02c2c070180c10020302404107640707003908000c580340c07042070f00034405d1204070846001901d200f00102c8291964407414402ca002c0c1220751440420b0500c01e212041d030062402c10300d000800300702ca00c640c00060b4010340c1034501c100070303628006c041540c4400c125104646038548a540750300b4a00301500044038010003140c540320320030040000a1380694000c030106021a40c1e41c2030340c0356040d20b20001c49011a25820903500c0c00d8410a4480e01c429814411880411820403155280100f60301119034241e0020600c075140078442100548074001e4 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 371183165 1250 371181915 371181919
    0x5090f010b09091b04090519030e0103050103021005070c21060501050306061f0311040b0a120603110402160803180d090e0403120b0d0602090a05060306030304061b0804120b06 77
    0xd50f400e104a10b1607a41641102ca0701054081d81c2c1244840c0c1d40d1640303c0380b0707817541000c10b544110211750044080034000c80d8084004c10091034041d061544248145030683c2d074040c00d4119103000061040d241c94001120445544546140100340d84480c8103494582c0c401c1c0500162010b10365203000019100c05800c0107000360300901c1000720994410901a2044003121442155400d140c0012000b8022002441c1c6503884006400510000e5410090845000955601508042001540f41601c5a511015041c0481c00d54880500d1500da402801150150040505030849642e01c56015400843e940b400342059010280d0b20000107010b032042010072490869211810424903201c0800058030180800c145220400b804032a103910081a07210300034010410001a8902a030281d4801b28600c0d00400c81c1d1000011103003001030543c1c0c010907004010318202410139100f1110149840d213000e001461b11742805010075503610080c0701030038034044070403254202c03400c140c5810103000e000d44d4 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 371184415 1250 371183165 371183179
    0x2131508120a050c0312090a030305070f12180b100e10030b151c0b0106021e030f0a03022106030705060a0c06050405030c030c060613060509040f1505090f010b 70
    0x518000c1e030000c100e4803001a00e0800f16141c0451240280c610f000b988004400c502e2180305014401900084c0350358028070a9806001c0c030b983d11201114180d4140000d107000c240108001c42a982083d0071518080441c0034032000018016111101441c4003030341e911a003011224018060091401e0700c076540204c0c031080d4036016624540e00c0d107888c040300601c080400c0118004410003a52000d8580b0000d508a50b1001884402400c0c00c12520b502803003210054814540d006050280030005c005040300c500d005941000004502030034240e102641080030140d0030070180440440010b11a000e04005100344400351510700107040c44c2c1340d2070303402c41c503c946001e00042c0c1c500c680c0000e0003200142d10030300105080c0c07a645045884c0d4065503074003940c2030102003040034011400142807403003290300710786506040403400400d1040355614080c49800c07180000010300810783c1072151048091083c081da400100408040004480c819503c0925a800c41c3e6001e80316074000740100040690200c440c1 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 371185665 1250 371184415 371184433
    0x810050306010e0f0405011506030b040e0705030a063902010b01031107020d03090305011b090b030c1b070902040b190810050f0d05160302031c0f0c050a02131508 71
    0x18100e682000b4075144c20303120a9030014081240a41040200704c400c0000c4610040e194400034028000000b4201c0c0218600000d10b204400005852001c070740025000d482c12102c1500c4501c090904c42075442c800c4080d0005240d41d0302001c0b00019a18404081c2c400611501d004009003558041410301d41054101010421104081c1e4100c44445030704450002602049140a0301e5542180d440500307603501c0c2c1261580041c8103109600c0845410ba60b8040f00310b900c8030500311540c001a80c44240607001440400c0051100407040041d03002950122600b1550f140b040c04160b80c040d07000400c4100c07000c151740c1c03508146020300c05610203503418860000d1600620407107403540c8520815201c0d0901c843c1404a5071a41c510100119810106640c408041c1d10101c407105161407008a0013841758a6031000c014500800882e0340f151b40d582c44050b01c1120f0030f0b080b9440500600280c071a4001c00c0c440742d0050b55610076040161074829404502c64180c113010122888890340003040c260400391300 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 371186915 1250 371185665 371185679
    0x5062a12011809050a06051801020c100b01140408031306111c050405120313060f0e210f150a200a180609030b1302030606131b081005030601 62
    0x2190640d02c181e545140041450824034028014018000d4441c0c094100343c3c2090080541000e4840c4110703040000c0d05080c400700340c038200d01c200c014140c8180c000c1c46d000848020190000c8254400500d00804c8250081c0001800307a071260748580c03015400020301c0000085e03100c05c0d0b60018903440c10182c5000030281301c025140d040348c82d9034400707501e6840140500035001c1c5040c1c0c1c003e480302070001c00e9500e0b28910041e40c1ca17440300040030808000c00708001240c81c4035030800740340030200741c1d10750851b0b00120b0306100044807904245d03103107605512060360645404120a61000011500504080035502071030070610401400080c05036080c05040c4c25407525a00a0840c441c10340c60520303940d000d44107001c5444054022400c0000c241031400010303080d51003041d00096030701402c0759221603150703039503900d0040910740c0000750960004000034010345014900e580c9121054480440c4d1940e04164008030f0360280b481c000c021618440901665920071103c0703101a200c1a80148669410401 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 371188165 1250 371186915 371186947
    0xa050f0907030f0f0c0c020406120807060504020f041118010f09272f16030503091e07080f0d080c0c030d0603080405091b03070e0d05062a 61
    0x8101c0a050f124031008000034602d0303000c1c240b140e0440c3e5040200e4241004000d204021038141a4440c0e4205140032680c1c15014642148060b40580b425150002c80d84d55074001d807400410580c0d20400710b801100319900c490003101e00220410302d000c2d03501d8080f1203100320380e00402005c50f030400041e10700c2c10051035041201c1005440603031101c8103a000000d1003082a00b103682001c80f841c3d07401c207080c421030000d44481804d862720100300d100215a034400448085130040b201400f072000d161003154400700e40601c00958004c02c20302c0649185003442081034032400150603d0000701d6221910401500d01e0521003009088001030240048801e0202c4c0140303800c1700588200040700b00050343d00000001002119030b50b0544283c14000e00740d40741070000464105103c1c1d24000c0c1e40010014060070104100d170754a4421100303400381552103003101144d00350600341040d82c00000f2104c040c400700b102005041d10510020642507404072a041d032034a6404031b25074418400030014030080040107074441c = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 371189415 1250 371188165 371188171
    0x418140606031503120f03040c090b0d0b0a150b09030d140d05060102030c0d02010609051503060103030f090803030c0304140d0f0804080d0203090a022107170f0601060e0a050f09 78
    0xc51103a143d5089240000d042c1141c3c5200280050400108150b800c042c800c0554481ea001e00d107943c20042c0d444c0c07011002d46160410715036102800104a80001d0300c83c1d203d07141c205210440029981c0d1816a00709031504c002d4000390411a40862809060f03d010818010901240c0c03414000304441d07110300c4a524000c414802444640710070004900c1c1c3d03c00c1054400203522107088a04170f80990101a00070f118034010745940302c0c1071130006401600800b160b1003040390090003c0105038a1a20110b84001c0186120820410011000104d00804002443c083d0300b0000146540341460b02c1c00744881048240d1008250304031000d506c0f0410342013551000d48050301d080c10442681ca81c50a0700703051045a90500d8134074401305c140701240c0000124480741c5442a981c10018520720076640b90aa10800b184d40582c2e445810140181410085420809820881145d034540c07010042d1500300f0500741c102000282020f0103620142c50320780c901e4801080291a00e1042403850781c04079002d11001 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 371190665 1250 371189415 371189431
    0x5060a0302301005100e0c19021c0810120807380907050306270705060403121b0201050a0f0c020306100e0c0a08071803020303041814060603 62
    0x240408402d0305400c1e4600c01d01c8020341005803015618400d0100d0000d1006443e5222051130340c04012500d1b45010b070700c080c000c00046502c41d082008149100030450900301d01c47c401c501a5134200c2c2c6071200c001d24100c2031000c140d11031448519250380584a08111b5074070804c44201004000c0000c210f401d001c8403d5203403c904902c120303411046c0e0071041c80c18017014496002c440d4400d003c013140e4030005824054001002600c202e55901c1007016510a025912400c10074404480d0080750a01c1c0303101060810400c40540d03a000d03980c0c0e8001811504190300540c1c0881600c4019080207a02804000c0006141d540641511203560002081d50148134021020302c0344101d040300805020304010702029078010115600c91070b244c00c4035403100806100e4209100390740c401040c0748400c0042030715804c001964503c03a482d07859100454001c4070007818113100c2e10100e600403000da2002e00c000c5c009043d0039583e000440b128102160300311041c072081d400c040b0302c1c03c209202c0c4950b40d00d000c90390083d00c0 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 371191915 1250 371190665 371190709
    0xf02040617010c02152a1e03040303050603160909020319050d141213110405010311030c1c030810030b010f031101030e060103150e010204080a021002120403060213150306080105060a0302 82
    0x101200131b00b01d61194044005100110461060302e204403040151f1240d4400d0350b041c403003a1101742c18036035a50341c04100d040000008000c1800406010f42c84912140d000804035450f030083c01c01d0041c2411240340d03058900360805802000f400d80c000180e900b003000503001a83c0340c12801184080b20b0400580201d0100404c200c0100512810035503c0d0b0342d01400230320400c50795a4900d0302c035644a02903190a80a0b00445407410401e2030080d5003000502d1596440f161695a1a41c045600c103900405120f445e0f140024003101254020103845d0203441e10b0300045288c01c1c11802c10b00f00004410500504041c01c10212480019000c60200d0450f60b115807c101c02c541414001d20181c54140c01c0c0440700c2d84007140010b42540006160b5021500a23140903000700b00003902203894001407102c1e20040c02c0e00304000c0000600079401401e40000b044000e00c1d80395110100d81c1c1074090007100880000f52500420300011500303100ea0382d0448001c40350243c0c2a0f245901103400845100f10403540126 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 371193165 1250 371191915 371191981
    0xf0801090c09170f06070516020d0201051b07080c092710020a031a03070503060f060f0d0f0c0e10030809060d0204030f0c06080c070f02040617010c0215 67
    0x101800c0c1800243c0458806060681044695103564207814081511507114800c0401ca14500910868407a25440034200460311141d801b402107072100c00c07000320b042100030000015202012103801e0050003004001d080981d10308116149001400e0711024802c503500300512002d201151146110111003800c0790381c8103e04094904e04101800050380c0c41540001400359245615500a085c104034540009822a031182c1c24180c2c0d0303c01d140112071300b5910641c0032410040c081e451056108070010f007129a08183c01000c00d0a4003503c50080b40c204003155000c43c200101280d460018001a500c0c1c060140f41942000701440b1482c03002802104c0d00080c10720340c54032080210785441b0218002907588594070705e44503010000300383d0305803101120b03010041941445920503030301070f0300311018075401c000d49515400d0403005030f008220f070f109903201c0c1c001401448501d0346c1a0a8401d0f08000140701200d08006420318151a08078017401c0550820004c00c81c2074400741c902001c4d481000d404140d4 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 371194415 1250 371193165 371193167
    0x15010c06051005091005040513050303070503040819030203061e0307061809051302011b030e090612120c0106061403010b0f041a0d0b0301231306020309070302100f0801090c 76
    0x1d00c10f07004160000c0714982044003145160303110f0412107806030390401460341c400e03080441040070303424020180d130008c00c0400d1440f4403c0e4051340d00580180f20143c54190130b000398000310401c4000c2da00c0407075008810407105103001081c00c85403611820700c0d00c0320040b407007001a84400103401808184040030300702101c9020800111400340039106001c001da4203084641c6a60600c540b10102c0c00a0f0180210b16411b4115003d06980194107440e0a4040d14880c010401035800040c6241d80002030300039604900001042010308544176503401d16079452000c40f1203800d543c0107410450500800c03e89110780350244c1800c40b411101d034046419120120580c0058080c81103901c81c02d10515501c1d04208200e00000017040c029450950400c211b90710300c800c2c5820380c0c001005620b05480f4a0100c103c0c2c100107400c12503404040c19601e85d400055560700c041c1207030010b44846c0d07115400401c0500c1141411407800d070000069003080c01c02c0d40b00b03c0700c00505540d814098805181c0d159000800c2407 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 371195665 1250 371194415 371194441
    0xf0f10030b0a120c06390f0c06080a020f0906030a0902030a05031c06080606220c09030b070302030f180c09180d090b0a0e0310050c070b15010c0605 65
    0x841d0000c052201c0e80b9581e22101c0001c40b810b40040d100311184a800003001402000d4a100300b410940e04810a00b081a5040d68807031086507170056810f4440c6881c8001a07580881030b8400e612841c600a16582013000080100c00c000309401a901e204201d03081c40c2240a00c15100c03220720884440e50f4030b41d5440d102c803000d4041e00300000e41601c6074068030b400b000801320140104110403090b5088070407070120000180c400b14030407101150004008905641802500316003130304482d01081192800d801d102400b1903501c1001840060490081801081254444690060071350710781503040d0308000300203031a42c10740a4946580720700703682920070404e003042c050007200740b1000348140e006240514951088039904411f00d002030181c3c05003602140c0c003410300e01055401942180782000f90f0160251610b001c000480c5a06104008090301c04000c60b00420b48145180002951076089501c0c2406512001904949005100c0c0080c150266070040f02600ea0319004480891980c03661580303102c031 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 371196915 1250 371195665 371195681
    0x50d1112181209130603080a030b0a151b122006010806010e04050a0b0f0708180d1d1c17031911091206010f0608060a06140d090606030308060f0f1003 66
    0x845c2407075400402e20181402411000806440c01d110b81d00d0414200300368011640078005950b000d16003a00703900d40c442c2d032182301c000043c000100d11a200070344610019042c00640c840014214600b230300d801c080d000362240507052600c4001c000f04e50500c00821f454001c140915401d20784030300d0000f018001e04011703580340c84c0e40058007081035003090540401200780498400c4003050400011550341e85018103003081d40c5050350080c02410364484c1c412a626500d013402e104070b205404004100c7c0340d07140864156040b003010300f0024648020302d00400c1400d42600740c80a4000144108202c101008000c02c0150f06410400960318820040080b03c0c1d004000080d030b0030010007003c01c9c0040e0390000d0002d0581d00c0360403203080c40942c0c50004a0740304100715102508011048402c01440340034003100c110a0001558045c00e18440950320006c03180803500c00d4490503111801001031540007541c9a810600a8440d14524100309010404050100d001c4900800d804080c8009181c460b51042070 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 371198165 1250 371196915 371196949
    0xa1a030c13090203100e0907030303020a0504172d0309010e010507051005100b0405150703020a12020303100f081c0e19080705010c03081303050d1112181209 69
    0x40c58860307a4402c0250011203ca1110b8012500080f8180c540c840440744030700660402040494250381e000c4020703410259034401400014400460003421340d032400c1151107900001081c80d81a100d80182014008040954003481e003030b040d00e0400347c404411500e05510a0810107600a03029004032407500c00d0700f0f80900306024240c010751b082e0501d5041240100d04810103111902c1d00d442d0f502907244914400c40d41d10003200c0d00c104030399402c180302804200e0300a0050721500700350394542540c0303000800683c1340107030400030400c0352080354502d4400c0079000420386c0c2081e107410007050700ea64070001d4010300c0b2040c40d00c0b603905600310b101d00d446100b941c402a10752101ca071a01c0d0b0090918840b82d0003661000d000b00c0001095a51180e5494841a138156807504045d440b10800d19401c2c544045e410f80401070100700c1a5104100d078020041c1e4082603103100e0fa074504003001024045000503000c40040e101000701c0010b45440040d41120224403000110f980b1040d0070b001070b103000d0048078189 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 371199415 1250 371198165 371198197
    0x20d08040603090309080c0a0e06040216050f0105101404050a0b030708101a090c0d061505030a0c08010806010614041d06130902030d120b04060305011a0a1a030c 71
    0x714036107901d600005036580c0700362a201001a1a1000d440c2c44101e1080c05a4110702c040004004c034004031000c1640020016100600d051a032101c04544178501002c03c0c3c2d42648181d01c000c0c50b20b5401d101d295400303a01400e541c211941041b140307820a80c3c00c000300900c515100c01c0810001c0c0482d078402c92041390010304a5954542e1003040b2034132881c156524207911403a2507003015031a0325a01482e070309200010891901c0d9a90054038001e10303006043e010b5003640e9030b114085945100034030504520800382d1a0b0980380d2510710012801d4503000360483c0100905c17030740104190840001c10f24151466414007035903034409002d00c0c60050107160701614540c1040c1b9801c1c0e019002806200340500400c0ea80461040020403480094038600302c0000d404d6404041c210000ca8858403105180c60840000802d900c81c0c2400042c00b504c1840e002510140d65035543d201601c404000040140042900c610050501c0c0800311040d07030510031001102c080c1c00000250440582c0401c6403030080400e21aa = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 371200665 1250 371199415 371199419
    0x60c010f090c08070605030108060c0c120403261801111f0608060106051c0b0a0b0316110a0c0302040c02070806241206131b12020306072604020d0804 66
    0x990700b02e105214802035400307183c6020401c14072480071281030341d000d000103000b141c54140f1074503900d500111b80f009040c000d9210004d020310b01100184019402a0001e4000217400ca4401008070041100440c040104100c884685e40c0741c103c0c0034403000d9003401c02d5821040c0e144e00c49400e058004112003800400c07407980440d401c4207a1b21100648805000310745c000e80c2c80320002d451602c200d00c0d0341c40014020b503122408500d8560000500414081c04d01010180c1d07038003c1d004150002c0c1d80031600c15201c02e04001c000d960104074192290017203c0200048059615a41c0030036449004c0640200c0d103c40d452070419000304901c00040440c10119803061900030100d240200012109582604804400320018605a049209c2c3c03415070710b000c1d04441c0c807113030312011005054240885200c1c04000c0e840c60b04000e01d4503846c006206041c510350400782a07204150038401d000b00a02c00740500503602d140032407401500a81304507403841e404003140d100c0303000103181c190305e0200080032200d00140c0 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 371201915 1250 371200665 371200673
    0xf031a06070f0b060a05030601090509071502030a2a0206031003080705060103051c14033601050f0103080304021002010e03161406070e0f04150801270b06060c010f09 73
    0x10700b00700c80c0200f0402185841d0801080031108040c4550f42d4980d00400c011300c041c81160740016080300d2514101c0b00207a5940c0c01c540c610509880305080980c01c003080303201c466038124941030700d015095000d41c80b8003085d03240207058050342204040d02400e0003100061160010307110724000f0395000619280c0b81c103424900340340c2d141310034002100d4a000c5c01c801d00e10318081c0300407440d480d80415200e01d52140304010040754141c20081c12072442140101d00c401403003405400f0114211941c680002c03642d920704e03c80301d081d180007070006d18007003404400420203d4a03003001d4980040c1d0454180b041c0450080049000d45a191040140c0d4000019036034520315030b42506008061080c2c030310403e00440c051f00d168071100c2c1201c0b900b000c0f81011842d94694038243c007a201806200030000694195051030058400c401600a0000e0b40e56600c046410200180c100c14038200c560340c071880485160355102c0b035032050003421980c011040030652019081c0c7c203411241998040303000800c5a001e01d400c2c = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 371203165 1250 371201915 371201933
    0xc01020408061f090b0904140a0c15030c090f0e07021f090605060904020a03030305091e0c01080105030a11062802010603031e020712020d05070603020702030c0d02010f031a0607 78
    0x208000700c3e906070000e110140741c012040491002880c11200b0b55540d25402401c2c011803d1100c0603000e22103229002a1801c0c0111020300072840c450219254400f4014040718010794849c001d00032206010000741604580c03000588081c401c4210040d21343c184141d00c1d06031480c44a40049101414800d81e007015035104801c80d43c01070401344402d49818044c000e02d000183d8000c0d41114420307030300b440401c0c080c2d00541d4000d80c11008440099010342a043c80a240a042d1010603421a074000b4801e9a4882001070250004501411041c04159242900608030f5158103010b24004580300c00c0103101552000d59288842c80240240031011000170b00030500c40c0400c401080540403044e5044041007414250390103650001c3c05603a0805c1c980400e00305188404903407060541200034002034090200800400300b9840158440c54944100341c103107880040300c3c0740180101c00344c000160380e000025240701d0882c2c0c28005155040c5400c921014031041d203040303401400004e02c102c1004000c00c = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 371204415 1250 371203165 371203201
    0x6040b01090e0a091e060b03010b09060f15040b0a02030403050c010e13050a09020a08060402040c030b03030f07060e01021207090b120f0403120c1205130206030402120c03060c04050111071a0c0102040806 89
    0x80c02001039603048010440c5240bc00c3e150203801c0564140704001034142036450100000000c1003040c242540c503440d040d07403603010308422001070300041070030410000c0c108007003104074100742000710600d8420400308040e8141c056100e01c9135602d482c003003590350b0200d40c0014020358014003203c42d03017030700c0c3e0b1100c950310501991b0403801185070409841d9014424030505411202c0140690b03d481562000041d00d03800200082d50141e90710390321301c20042024401810b0003d410f0402040314034003420064840381c046d600203c28034200300100880300044041d1a54011620080001181c503a414200e9800c11990040ba101c24900700701e030b20a060700f01d1410f003482104c49206212641c0c8060342c1c00030042c0100f50080d04401d06001103070040c90f141c500b00007502d2508040310740207500a0b00007441e084007915004003980c00050240080d582c01443c4002100e290310003440d0051030000341c5607403080c1c503c0307501c0e00c0103401240c08100001c080d01120010400582102c509003094100403070150012 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 371205665 1250 371204415 371204419
    0x120711101a03070305031804181101020f030f030a0e190318050103110403060506180f15040209090f0606040f080c01110a03020a03050d0612030806040b01090e0a091e060b 75
    0xa2090710545240010349001542d6020000d142080e2255412495010031074840e56480387d16a40320000c100b0003d440f400c0f40038003070358114041401045c00a0f04203c03030184a0002600104040b610140841003241d422101c26500054800040229230b8204441038822900d4600044994014940d00c4401107801155501c0d100d40d41c90b5941c2c00540896a4903840024002400d11040005c600030750310a41d88000007500481580314940f0306e40c0c5407011704031080055650540140009081e00074404000808192000c45c03070300040e030780029013151000f010080807141c0400000c41ca0f8861800f5640102290400458099140d1107004e0301c42e4401c9842038001900505580394a2000081e5180c1540c0c2580160403c0000d54900300c505502c0411051603003520303000001a03806400000b00745550103581c400c0e100307042c40d0f810030090f5004989203e0400c50450014001c81042e80d0207140c01c001110350000c0d03015601d2801c500e0074080760b40d900c00200c00100401c41031200039000181d2034041 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 371206915 1250 371205665 371205701
    0x5040501092d06020a030b190602010507030b0d0204110f04140906100f0302070615030f060506061905030402120d02070f1a0702040b121e010f090812071110 69
    0x4016008180da0b00c420103507007141c0714a010168080785142d8028031402100c1c0c0380100e01603100e4008591511015801c079480c0002d094030800856a0a10400e60001c286103828001007004a001504001c0d04020180c404d642d1031807070209400b034010840b10342000c202061503c80369149030450302010100c1000307000341c0105000035400c0c5407803001400b4034809621549010000844210020b4001c0c0c0e00c00c40d502540c2e0080130940d02803011a0000a500c20030302d44010100900c0c21505848014040780c2c020481070001200041003900405841000d9151440d240d50f40c9000207640c005031410342800c0ca001d03039680d1031509940031860030309903580c040704413805507516400314140000c00c404540f02c6083c24048030006141603003081c02d112000502d1010103401c01c802c05410401880c00102a1014452041103da2000c0c0580a500300b04c1c02c80401129145881e02da805d0700c0346813003e40000e1300000c000368030503011703c0c11150304117900411107858060227840c240041040c503c000ca02c00d10 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 371208165 1250 371206915 371206943
    0x10605030303090a0f03050d020301090b10020a050c010f03090602030c07020312180607230610090911060f0c03121504091a0a0b03010f0b04110304200f040504050109 73
    0x40001c116805008104028201d0b0122030700c1d0b040e8814225a400c404000042200014140075400510301802c4044000606140044108090889040c000d001550450b030074600100d0004105030081041c02e0824015596818100300c3c014452404014440791021090090700a00d20001d05280703842070702114121049124401c02900a801554000c5408507108807491704240300908403003445100d035003695a211503418254410303601c004130655401842013045074441805803400905a4a00030000540c845e210301c2406450750002600031040001c4910228a00c5001c035101c14810109694845001e0130960030820803c0d101c1d1100380710000c00750401444c140c404c0149940c0e015126441c0c0d914200c816584c0194000e01e4855601e030b03161003007205500d007805005c01c030580c810000104119081c0411007210152020142556414000c200000d898080b51015800c0750a10710340151804a0000f1043c00a81c2e00c060780081c242014041044815040b100c4440d110b500e0007190301c8 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 371209415 1250 371208165 371208169
    0x4020103060f0e131505090a15060807140a0e010803030a150612110c0a0305040e0f190b040216030309060614010f0503130f03080106080a02032e0513020c010605 71
    0xc641070059192001610000c110403107200c000c611480341c4034517000792281c22043e003030000321207040f90100790b5500b01c0c002007410000400307540400520792240c1001040d040c40c010310307600c0c9410300501c100c88041c003441405982c5c0e104003440040400074850006581c43d0714510f520b1b60400c3d40c50b2404c19040001c0030109040c98070380042541c4c02d60307840303e5901201294117005401c48048900062108000005000d0000d0081240c014000d4607010303551450500e032402d40c1000148036081075890341040c402c902c81c801e60840c07404010134101055468048000400900c120100f0414200700340c1c40140c00c050b05500281e9109003d03070700030010503070744050940000382c00c480b6a500058280c6030100d2024003030005150012150124004007e0940d901d0444220440c41f054020403800e000420041d9840741090342c0c0a02c0711001035085040618a8100c10080703810001c404000500030340345080c0000000300e00401008043d082841a002503110080d401601d01281c0ca50034100003003214 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 371210665 1250 371209415 371209439
    0x6030b01020a020d0813030507171014040311070b0301090606230a14070501060e1008190201030e010f0603030e030c010e091503030c0f070617070f0305090703020a09050402010306 79
    0x54000e0710700c03031340414955206200d551000445640f003541020300800440c2c800c1203610040c0c820440034601251109101038a80640b080b08c80b00ca442c01c1100460750b8140b8800034540145c0d1608020701d09048000c011030601c011380e04007038030345240400005055441e44c5c0028080345e060703840d01009500000c0700c41c030175000c40090181c00005c0400800300b10318403484058041101c0d08044e10b080000700e664243c00d5545950180004d0041c03902400700321141e1000ea00c1c000d044070401803840b849801201100c0020801002e4107041d03644617000c041d0042034001c1215010701c41000c00c0201c1d05d0b4034003e03004664452581c2e0080c492400301c5031095004207480741c12280000c000300321a59410400c0031801ea04040d40c01d4040c041884022a403240800080c0746c0382c10800c002d000414100380780100001c410728038154690b6104014006186d80041ca1710246e0316043c0380215041d51754150040c608851507000035008a000b1b4400518180c481c0d100b10f01a900c00d80e402c1c0300c036070343d900b94522030 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 371211915 1250 371210665 371210683
    0x11d010207051f0e1b0a050a06020c0d060b0405090f010f060b0405130b1008040210051c090c0b2a06071209030311030c190201052e1e06030b0102 64
    0x125030701250300e0b4101d000d082c0034034181402c1080004101d0813124842c19003401c003681024020341d040c2e144105c1300f51034504900c0001d05825a1800d4046162101c025541c00020000078081c414109080d8140682c030780204801c2d480241091103030782407290015544070016548664a546032900c1c80c508802a80100021605558940c605140c140b06c01c1028103403242101d60301c02c5941d1500001540c1f28501c4050705405243c840001500d400e0043c410310f122402041c0381001000c0000034941c40d0840c40306968210b10a8002910451503e4074000c010090b41010409000108600b40c6020102d6052500761100c16035070b05660083c410100d65400007070f41c4d4a03010030541e520b81e520303103c05503000355a814000e00c0c0103e00c2250720102c00c50030341d005071102c0d01290000242c80410001d132102040310034601d0300c02003041745008040c1528030040e000071820700481c8020f5483c000c100071034410018140d411204403003803d84030401c42c41803040b0b10605001c2402d00d00404804c2d0f0000c249120 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 371213165 1250 371211915 371211923
    0x20c0418021c0c080304170304061b4e080f04060b060304111207030803150a2103020616050f0903100c0503060429060f0c01020c011d010207 62
    0x59500e0039400c00240492000350851500c100c0b0580d00c000c201204011001003078a40040c690316420420201c182859a107086c02440d0300c00c003c1084069440409950a42c00751151013400001c03a00c0c0103074401038000c41c00c0024156107090224000320084070310900c4c0c00342034883c480c1550f043e4924814510b012400101140b0003100041c18aaa500301059204d4070236680001c0380c015901c0025815001560252040c1c940d42c1d030111550308100c1008400c00b1006001007003807a14565840d0610b100040860400402e124160348190701c071041940c0251841c0030029542008130714010341001a03a15060b0010b00c0740a011505000090f500c80201c01c5140d5100c44c40c1407056002480c043d030144a00c150184183c102040c0c2011003885003c0c100c0e003060741e485680e8100401000184c3d402e003a02c00100704481d004201c41c1a1104241c12903c04055a14507250502d000700c100701c40c050b03001d188149500014a00000c1a01948014050040e9100c500480036131500d1176400c038058948010 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 371214415 1250 371213165 371213201
    0x90705040f2309040c030b0f043e040b031b0306101a130b0a090e060402130911130b12010e040302030702192304110901020a030c02150c0d020c04 64
    0x8074107188403e264050701400118440d65034940d22000c7c28201291080408104c910502041108220303040380c0c50803020012821001d640d0220219110f0a501841d80f00304c0702c81d0802c4010380302c68001410044008040c0c64801d044c000121041840c4050540c2c03280c01000300254841100e00c003910207981c80302c1441c019940410b1a0a1603541c004250500c80c0c2c00c100740006100000c0740002c3c0f00c55201c650312202403c1c81c00350382d46500714014244910990040c061591901c0e41140240c0440d00090710220b0320002e00740c10380ea114403600c240604814014080492164034080081034080d403d00350034881c13680e83c3c940c1040340300c0c02501e0050060f001006914098074105050b00c40542c031040c0c0760303040240d4500548010721010245c000d4883d41201c1d11290500c1c00c9c0c401c0e002c1110001e20b1683c07400961900003501c80c48004001000d0080340c03075104041d500e44140c0100b5100005015135546d1803518503181d07444400d0b401e080014426a61420120f04150084528150070041d1407 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 371215665 1250 371214415 371214479
    0x3110d0902030a020a03140f1b09100b040b0c06070305010605030a0203040606180603020414070f0f0203070204020703050d0f0e030318030f03010e011e03080306010c020f090705040f 80
    0x10040c0400e5001a07a0600c51030781d03400b02581d1100140d4005500c2942ca01e64100b21083e0018209032140d0044c40d0142c1040c41c5030701400e084940d01d41c1111310b049690440307641e103842d007140f085240303078003c080079200c04500803503591007503001400755907200421200c041e034610318214296917090250a00051041c4007095403c01a90080e6401c240705410203d10561502c000084000315010f405a074141c466500300258101449241412184450b041c00686005d82c030103070400c06468500c17820005064496450b403031080c815920210781c010015035940d000e03401c2c014081d4000000350b8485502d0284c104400d20054458907200c680007002460a40d5580114600c070362140d912a8903c40c00208003d180103803105008501804509880380322a5041111090030300c07a01008044224a41c020184085080c0000303581c2e10400901c1e055444582c544041291051311400c61500312003480c0500001c10380000181c416038500c45a401401c03661003840c03400500d074400004001704902260 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 371216915 1250 371215665 371215687
    0x70e0609090d0c061109030a03210501140d2d0b060108040507060e060403060504080309150f1b19080114032a0a1203050702030d09050108130c08030f0306040c0311 72
    0x45d480d04001064a941420710070000300e03003485030740f010031000180e840c2c1d85203400da0740030340c148120414040400c000946c1440e000303d0440d41d030f0300143c038882c1c0000c120460401140f001229001510700b200c500303225a42000e14224040301c1c08040343c0002c07662000500c00c0d40708540c028440d42d000001004518607086058414070300c03220545030011020480030020500c08e001c1c8a00036881000741aa580c03030720750390306420405502540181340c261002442400803512849940001000c08515100c808062100c1a18880c414108030050703244040250215008080d5504a98120945c0c2d61045403a104050b200d9000c00c0c9240503564001562140f21056850000d86161300900340302580c40c3c468420a0006100c10342c11030000d400000ca0000314142031000b019411804d045c00041d0a0030b01c00040c1c2103d0009142c0045224000d03c08000e219401070440c009010301d50075260780703030b00e50503506025038011036040d0300460078040d04e0081184203200311000c0b0942c16041c54104000018 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 371218165 1250 371216915 371216921
    0x9010306150e01390507050a261f09030206060108010f0303080c0d1b27030807050a020901080703170a0203040509100b0a0f030b0f01020714010201020c070e0609090d0c06 75
    0x40c43c001c0d40f0f030395030303503110380c003140000424010100001d03100180f40c401d00d4468a03058140c2c200c0e46c01800c0c602c1e01042700708105808140302c1c10364544108180d8840780075040c58040d240c20081800c540d03100710305010780e503143d03c40541c0601030f40c03d4408a03668070005444a29083c03060b4032280c01411003c0003c640324820310b640000030b0000d5a440c060b020350b807600c1601ea4000541c081c0211955550302010b401c00d403c400290011604c107031038401007402c284000c501a210141ca00440007603000c0412031305000304d03c54103500070666000386d615440d03030644e1200316000c02c443c1c1025116001c40180841001d85a500540398011491b0500701410700ca02c1242c0906400080c240224011845442d050050104e0141c2c60351034903810304843c08014141c0e00354007035040c0240b22006030051640d0f400300d140002d540310603812590389007400d40101c2c0203106010b43d080b198024030381d0118180078100002809903204440080060315200d4100e0380b141044074141c808a050300349020000741d1150 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 371219415 1250 371218165 371218187
    0x40b01020120130f050a060c0809040504051c0309110d02010216090506011d0a091a03031209010e03040e0609070309060e0d030c0207050108060f030705060c0309010306150e01 77
    0x88004a6080303041c050046502054041054a01c0710120b000e00d480222039a2810081611307101800d503052405011944514041c0203031006c0000c214035003000d00140c00102c8444003805802080341785454142341d40c54540118601048143c3e002c14500814030a0190803c401d401140c000020121075042101802c2e10b20022415401a00700c0d41a0034200501c182004102200003ca000d14100000414007001018158408140d1428442d013540340e04540500740c1d84030701c10000301d200070380c200092707078000c00e0076400e80c507100000b2242009502040e440e4041d260090081c0b00d803404414183d9140c0c051303801440c10303081000000035807900e003040d84250030852a0400080880c40c03a1510340c01e55031040c100c2c914561006010f0300c4440e030715105241c040c800c00e10103003041d04d00b02800206460b01c09024103100745140700c0710f0103250b642030115600600d0010b0190342d42d02d95908425031213030004003019000c20314140340064030010f204050016405290707541446260010019141510301d0 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 371220665 1250 371219415 371219417
    0x50910050f040e190c060201110a0807030e030c01090f0203060a09080313060b0a03111503150f21060103061a061204050a1421090a0510030f0c0e090a05070e040b01 72
    0x204c3c1c0c040011507054407000200d0090112207142400c0080180c00d65818050704505014104010b00c2800c0e840001250072041c9880c01090f40007410191071f1440c040c180041445518007141402086801804030000c1d920907410345100c1c0e62180c80326030449005d01d1014000d0101000020b1094800000c40c4003507910484001496124003008a503501c40140c00032181c0c3c20710180c5800b420303c1c0400c0b200c42d0301d000c0c021450b4135600d024940780e410750200300c10b0035001703598880e8084a035944210340c00324222580300010032141c640c400e0305542d9034002e2009651a910b07040350220010700107103003822003080c05414103107404040c59034001e01200003003040c0c500340658020b40380015258141c41c06c601d103820006061841c1c840401050500903480362045400c01040300751400e85803940000b0031100211010351210103c1d5030268058840d400214080501d00b003005401183c224400500820064036204082e41e1b8210f943d100315038003940e2030f001040d80068022003a00d07258000b54440441 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 371221915 1250 371220665 371220673
    0x90305070813090f05070e090601120c020f01050c04170f0c0d020103090b070207050f0103021201030f020102070306020a0306031106031902090d08040312081e0408030a18030306050910050f040e 85
    0x52643c010f0308403280c0c5036414000544a00a1022503540080300600000d011100d896080c108800081c2075100a82c8070000c1c00c2d512200b80c9001d00e80244041052680a00000d03c140d1500c90041034042e0710a00600000251074580003505c0d5100107100110300c00c41100400e22402c1d51000c01c1902c0e50700c18022410183c8030407000d00060b40f01d003400ea001b009c40760000c124003800d20003000b455801605106040610500c8241c86d4000848002811030360000c50640d581d803090700040303007028220741025100300d000007481c1e5002070f410b0788040c00320303801084000c0e48004210200080d61000f41c2e410651150b1580110000c40d103140d005160103a4002c0c000068401c056551101d02c1c0c201d5071080da180d03003000c50404c1084e604100002c1c1d201a200305860501c0c0407840174000c00a0300504090700441b00840080c0c0d01e2059a4089211907414024010900049143c000c014202c540038441c00340c40c20202196205c0c0300103409000345c89004042411015012003848001c0241e11150003007849 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 371223021 1106 371221915 371221919
    0x411070204050403020a120c020f060301060e01030507050c150609310609061409150628030204020a0c050d020d080708041403030702100b04090305070813 68
    0xd81101c0c002010340311802c2c00ca18004059031b00400d85011918420070b10b80c0c00c50b140c180742c24401c0325490030064041040c41440e00082c8602000309200000e081000d600a4102e50340c0702c10545446400d007064a807190340792419600c1410f0404060708103120003414115141548000311240c945105080b2980f134400010020442100568000f2042c804110342d0350040d40d07505820403c203200740403144c0316100c10390300c080d200c44540307114800c11380b000d0075043d880f41446404000c00e050321998280300d0381008440d07540380d210140d0301c43c1c00c3c02000680d0f0300d10150581004607503644585005514285151004003c17039502994840c5e4484600d50750311034401c5a0180c11450030741800d032203a180166030107018010400b9540000b02c02c21103034690015802e5000710b800c2c0c0d0144894a02c4106000c203c031680040500002e10801c85240400c00210041507090100c1000b0000c50b9 = true := by decide +kernel

theorem cover : BRFrame.Cov 371043165 371223021 := by
  have h0 := BRFrame.cov_init 371043165
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371043165 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371043165 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371043165 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371043165 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371043165 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371043165 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371043165 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371043165 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371043165 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371043165 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371043165 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371043165 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371043165 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371043165 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371043165 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371043165 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371043165 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371043165 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371043165 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371043165 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371043165 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371043165 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371043165 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371043165 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371043165 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371043165 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371043165 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371043165 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371043165 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371043165 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371043165 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371043165 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371043165 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371043165 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371043165 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371043165 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371043165 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371043165 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371043165 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371043165 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371043165 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371043165 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371043165 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371043165 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371043165 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371043165 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371043165 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371043165 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371043165 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371043165 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371043165 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371043165 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371043165 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371043165 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371043165 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371043165 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371043165 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371043165 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371043165 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371043165 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371043165 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371043165 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371043165 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371043165 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371043165 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371043165 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371043165 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371043165 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371043165 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371043165 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371043165 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371043165 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371043165 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371043165 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371043165 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371043165 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371043165 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371043165 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371043165 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371043165 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371043165 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371043165 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371043165 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371043165 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371043165 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371043165 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371043165 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371043165 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371043165 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371043165 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371043165 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371043165 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371043165 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371043165 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371043165 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371043165 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371043165 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371043165 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371043165 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371043165 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371043165 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371043165 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371043165 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371043165 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371043165 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371043165 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371043165 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371043165 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371043165 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371043165 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371043165 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371043165 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371043165 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371043165 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371043165 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371043165 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371043165 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371043165 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371043165 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371043165 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371043165 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371043165 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371043165 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371043165 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371043165 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371043165 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371043165 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371043165 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371043165 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371043165 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371043165 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371043165 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371043165 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371043165 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371043165 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371043165 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371043165 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371043165 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371043165 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371043165 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371043165 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371043165 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371043165 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371043165 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 371043165 ≤ n) (h2 : n < 371223021) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
