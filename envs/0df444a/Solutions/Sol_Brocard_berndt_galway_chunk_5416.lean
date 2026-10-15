-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_5416
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T15:48:07.317588+00:00
-- url     : https://prove2.me/submissions/3a91c0ac-50cf-44df-b3d1-61a2d2b4c6d6

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 973920863 ≤ n < 974100719 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 973922113 1250 973920863 973920877
    0xc0f2c041407090e0c07020d0803043306080d020601050105210f0405060601020c030c060717040303080106021204150e04090b10050f01021612020d0b040b0610031817 73
    0x1081d2000304250107802c258484182c544003809a84d1607074074001200d9841c8114240250000c040204410014101c603002d181c00900c1204c0c05041307c00041c401c00d00544034100c03481090321005030b0340a02507000784541c1c0007600e0b603280506a0f05a070725030041d540c0c60301841502e0400ca0300080804e1801140c801c034011080b001d000540d00c80c10840c1482d10705c20019541602c882c0201c10108110390b0000400c84440b40d8058040d00c0054042c404020140d0095001900e0b00706100050503090781e14003000b000914865201c2034415410440004c0c5018607aa280c0f00e10100200400e0102c03102e48200c4050015032864a90303120030800011501030055907000401e100040c50901032105500a070100a560094482180911a52004995544d4040f91045042015107005c0c130000d08142c1c3c540b0b20b424000782c841020032402c2d90f900c00f10641c0849003035550341652420712915140918a180c00f040d42485d040c007170101030444295181c1e100e144000d201d02081005600c0044c644001e1350f0312 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 973923363 1250 973922113 973922141
    0x50111120a020106060e090f0414010b0301050c0304060c0207030507050607030509040513050c150f0903010b060a0809010b090403082701021201031e050a0807150e010c0f2c04 77
    0x228507190328082d02a20040c0a1840460102040f0003454181048020b00c5500c4581503600c00c0e4450f44c80c0c0808480301580d1103802c2d07549030080305410380c600f405218010320215480c50380c0c0346001d0420f00d00300c8101a034440300b1500441000c00c0882c5d400030707002d003d4403001c0b0f96440c3e0321007042c40c054501d80700d84d05140e6003060030078003009055090f00045c000046e0140b800c1c0ca90f040000d800f04600e100d01022080f5844070180000d801d403803608000362800c0007001d000044c40202c0b1030300103a1150420307101200010480c1040102429080c0a030300101742d41a25408030320b041c1a5009001d1640043c146412910324074000030304082c0b08412094500e45203402156143c514440d00d220b11002408140c03841c4001c00a00d80c02202001e1284103aa60020090403450049945884150740010400d864401d00c0241a04219199104401d444600e00d000002ca5012050010f448081940e4811061200701960306890800704010409a02d050825282c0d2010010000070020030009512400b = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 973924613 1250 973923363 973923367
    0x130b0103060506131815053705010e1006020106060f050a140a030e06130f081c15150807081b040308030106170a020a020d0507020d060f0f0f020304050705011112 71
    0x151a10f65103800303c841030141c5c2c00e0301180342141000201f5100c0695808420010301079000d9001040d9202500c0c0415201307050b031500714001d1029006450080e0400b0451154110030301600101c00b0a52100410050000b40600c4c0e152410142c8440c020003910003e1103800154104030600c03a4190400010851a0752602c1d0068100300900400c26480084568800c1001083c0001c641c88480c054082c3e2040703030b4180050503940d03001c5c1c0a4001d000c2175090f0300201c209a004e04a414020307080c81c20805020303035035054036002c451160b20750751000520600551300c0900c088140d01c003140c65440238480541c114220000c10558040c0d108aa0000c0c2c400b400220002c51250351010408180100e0180031400613210520890104d02c14000b440c0007581c0300c0c1c030780b03012407078064000342039081d0008000c115a41c4603a00d90b2010b4400ea428a0820295981464034400310b041c0710700759a02521480031800c500d041d80d1001e81e202018007030603060024001100042d03900c1040a080c00604d0540556 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 973925863 1250 973924613 973924631
    0x905103308060a17060604200c01090c050415210f05030d0e0f030a1409030a0b0603010c2a0602090d0b06030d0302401409130b010306050613 62
    0x50101e40140c0301035100700414440060394824005004848000c072001410740368450000300030043c151a4502164000d040492400050445000d486413402100000c03070000c5007850440204006500154070441c5002c41001c03101110309683c4080c0e6031401280c20840034805074000c8849600a0010421510b0340a50410400003001400003145920400c0c040d0103ca1140180c50344403424200029034414800503402601c148000b182d203c00c014211403500c070510340441e08180c0d00c0c0700c041d10004882c0081c010503003024440d8420710161440d00744800103448d02c0c1005842d810340c190030554800d2140c080107002039036040b10307443c51008140124000346458080100b01041311168800e019860940030300c0c50007402110303240d80008042c0300c001c04c1e0703220134229100b950158020026003000c0713840140540f1810440c000e0914191800e0203800200100551214000c2c0b04082d482d5401002c50000f40084460343d064941c03050001c42c56603288008a0440080c0f082d28580c1c040c1001c05c2d030 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 973927113 1250 973925863 973925867
    0xf0412021204121106030f04060c0306030218041103060c07151113031502030606040312121e060512030f07080702032a0306040507060e0a0305032209051033 69
    0x948030f4984504198510350703400c94200700c0030340412a0aa240d000c541c20009002030581d0384400c081203860b083c0014644e4030b1360042201d80004422806100000340d043c4003d200c0000410910004103c0c000c010518201c0c01807642c80c010f103100244012103107000140b4500081d0002503942a00c205000d859414140c01040c8859541c4401d550722003c100f441d004e840031a000720380c4200d01c0582054503091440c1e030340c2d00c0740d01d03214190075080002507c00c49140b50501d008103000d0701c0807a84c514041c01d038a0034516045401c2503110b64030500b8104669192032501005407102d01c92103c2905440360b0050600700000d2058180095043c0144001402c2009030441805410003041d5280802085a003081c5a6241da098034050400e61080c03c04001484c8620f07a801c40444024110390407584c3e82e5645e0505e950080c48070240c07042c1071400c40c40c2440d00910034030380042045580c24031003070400b0000c10710b6080c3d140c0242c450032074120040d014031082c41d802030031901880c00c40d0030420000c44100 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 973928363 1250 973927113 973927139
    0x60d230903070308070201090c0e040f050a030203180a0e070318050f16060309050606090603010b06072003030403030905092706101208120a060f0f05030d080f0412021204 75
    0xc0f0080382000340842c1c40c040c414461800302d0b40e448401c120405060082003005008002d00448403082051801d200140041c000080d4692003a002182c40300c0003484149071601c2d07101043d07070192400400401c00304440c2d1312380c55000715660070f000031141800d51b0400d02041d405100030b0580e00c01c40c220700d9825030300060a1103104581241d5aa04681c40c2c0340110151131600d1405031582e441480400c0d4240380000b0101d800c00001000000c40e144890045600b5403c6140180d4981100d0048455408180d00c04184000c0c0700301c0c0a1443c05080d9a806490358031140030b424019080100010312045006030700b01e480011800d00d9200c05041d011030165250f07011900c40d40d4000d0100c000144d2111a15600a41c0c7c0364416003141c140090502501c80c0140010100c000703564860400003070120320f44003070901504d0341420060803203080409140c60076090000d0181002a44420856054803100340b182d0007aa200c036207030720510030140c000c0b4035009620128410741c20300050000ba005410003c = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 973929613 1250 973928363 973928377
    0x6060b0a050c0c090601050945070503131217161220090402070f050a1a10030b0910051018110406050d2702031b060d230903 55
    0x80352040f000d140305001181e5002c1c0ea010307011032401c3c00008102c0c500320008030301c1c81d80e460780e0b80c01c0c8201840030070320f03824001c030600d8040950b0346c0c0003221000186c0d02c0c216513000c141070400d40e2542c20708140e4a0300030415a803003c0c00050050500140d010b1080320300900c10118140e100b8400c0c209001a480300000740d0302c0f288045014411380340c0c107100842c00369151540b04684200c004012910080c07c139036001252003a44284c0c00c20a4900058400300c5c2162551300913401041140d00507c1c0c04428080ca20b5a641502540d0404008009020340321500940b40c0c841c001c0c0100b6203030108800d103000202c0c0701001515042904100c1060700c0701c1c0c90350007280d9200b1144181208551103250440382c1039100c0b682070f518100410700002e0f0060b0300410681a00c038100240c1d400440d20141d041070f46079400c1a140b20450720112055140c208400010040c40e20341c40e01480c001e03500080c40c5c610030440b01e00d00c0152a44030b00e05040d800e85070074401500301000054524986450855203e9101d03103 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 973930863 1250 973929613 973929637
    0x703060c09090b01080f180a02130b090a050f06041d01061e050406080312060a030f0b010603050c2b020c060408070212070803220b0d0b0a080a03020307020d06060b0a05 74
    0x1440f1482c041d8840d0003280e000e66101c510540c01c58642c5030812090344820800c0800e1441200312480c01a156054410041f14408000080a5403400200211030340d028101020203818a000d1002c202d000e4410240c114104480014070401c082c142d150042c5098001c08443d0351800e90700184078a000c032010910381400868040305a521582040125407440c00355003040c0e0b005100c0228590b0003429980d40002000f00a403c4956481d075504c4080c420084044500a800718010060190980506030704080110240703404c10b084180b82221000d00c45001082400c3c81400301c02002007982c4c1110070f06919101902d1803840c0c2810b142e10680c0c4003100032406041542c510021856002c210354041c0e86030003004d50f18054840100003000d05c010440300b68440c05601300010101d40000c020190b510701d5074804a40d4107015020002004040e51061315540c0014031100006030340070049440703040d1704035003ca51000080c01c0100c010482500001820100021080340040e003050291001400c50 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 973932113 1250 973930863 973930871
    0x231f030b041103011502120c0d18080a060903120c030b0f1f08090115080105090706021903050315040c02100b01091d0703110406030914120f0703020703060c0909 71
    0x2290074001281d0710700c03440001000041c0014024000c01500843c9050600d104940b0030143e2040c64010301d5025250306d0311301e94016224403140c0d03608036203d030a40a101010b40101681313050501c41c1c403840c1100c401084650386003d50004c15005080d25103d5140c00c0804100010131107a003d0014060301510702e00c05c0c0041d20150890380780200c0c4009825021403c2d929849620060694a100c80941501c407036540302c0040380c09000034088110007c000410000c180780c01e00c1c848407401c107021030300850219001001500400207035054211000c59052404c1541c0e0303691590151020b14200800b170303900900300a4150700e40390340090004d07050079091710308100314409103006444481e118861104014168146180c000e102c48040d2079214249003804102070507600e502c405264850342182001c2543d450424045c0400994182d4450b6504c0008080d141c11034909104940603004c84001c900c4000100c402c1094800d00c901801154005010f11640d1250003018000c0031560050030300ca50b00d0 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 973933363 1250 973932113 973932131
    0x9060a090c1e020a030941130911040608070b070515011e33022508070e0f0402060c0712030507170a0c3305042a231f03 53
    0xc01180b40c0c401fa04040341c0e50003080002d21000d030030354614103a611041817a1443c0054a8204010350300044203d0300044104c1c080c40d140054022161030940518581401404003940025800b81030b40c203d190a035032116807030b151091402c1c14030080256043e00701000011f01105000e5035840d11255080c1d18405681c450006520200401c80c840c1c841009c80c1004005420410070703a0003981213548180c8180e0b40418070705560b1a0340207208407540d036400c04001c10100c2c0090004801500440702142e00c01d05144030201409003015201a20a4400182c12011514100025001000c003c0010040d0b20690305018190790401c0f541626542e40003001d46440c0d00003030342150840000d6031940e12508800340c54806090780070184000103080d4985a207800e50140c40342900c00c442414002107410704d481e280440d001c01c1c140e0712100aa044d42e8840001d4101503048180584150710000106d4580315004d101030124400f525070b41000802c62080da0250140e68041c0301000142c50601c5041d070 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 973934613 1250 973933363 973933379
    0x424150f050d030807030207080706051302040f0b0f090c21071403040f1511161202150109050c1903020703030501080712110301060b1c0b09060a090c1e020a0309 71
    0x40d80b04000d00248103140003884250295010344078160181c50ba090600380185d8902c01121000d85d0901c034071b150603d075144114901801707020b400307064802007441030111140104060036111000607206200e0500003440c1c80146000f0356030f0014072811100311002d402541c000004805480c0300002402081201002c102d05108590046500001c40d44a2074569210081d0001c4009154854140c80d05188140245810043e007410483c0d103900c05014403080c5015a8400741e4582c90720107540048041490440d00881c0c240c0c112a0340ca100171501e540e03a0f240d080c90310310a141c038601031115104140b42e03086030316074080e2061611944003007200d80d03200c890207543c5510764032035403144481160514000800060541803912000b4001040c0141c4036092911150864000e4030368441c8107107801029401c00b401542a2020207460001050400c0400b0418a810b00d0085d052604d894071800440d80f4410700e4080b400d40c1c03842a0400141000140c029214030300268190001580c07140040b0380c0304 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 973935863 1250 973934613 973934629
    0x70f11102105161d10020c040f09030203030601110a0507030f02030d1806181d060306070903230c0d080a1409180912030c0a1e02060424150f05 63
    0x1115144030f0b0b85024210780d02c11140d05080c104c944946503419070b24402c0c4c50b00c9030a082d00b1001e416402806903646468240011034901123001c1c03007400e042902c40310100e138001c011280c0000d020320301039000e200c40317680c0140f40c00c000040040c0b041c880c020000082c00444503991419500c03c909841540c904002e040325011a0b0b041c5941d13400c89040d20400c40b00380a1025004e0f44900f842400684581d00c0b03038002c01010030890140740750030155040041c0c610b01800110b074080140d00f0f003815118116122100040030080403001000340150f000c54120700204050011b4102c0100036094000e4540b40040150f00f240c4030800c0400c10201895482029080540d4101500a00051341c40030a0b4280c1c2d0141c03510162075000346000f685400314160800d5001144621000407400f60f40300802d0100804080c500e6651b44181d60b034261010f80160790102e0251382203900b180031981d840901c01c00e070144001c2c45101c0e00c948945403281c419420704107a0b050708201e5038808491103202e07176a581400080 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 973937113 1250 973935863 973935871
    0x30411090a0b0108070e0a0e0114120d0f032a110606150f0717071b0506040617060402160609170a051b07150509030d090b070f11102105 60
    0x1c507415100041202c0e1041c561b55078801c5005106a200b03a544004c0014039001c00c3e005110b1509100041003441e0505280c1c10440116000041900d411107820040405c4000c1c10a0f00800d40c5400b140c200700000d480410740003240e8180390321003000340024042c0014030311030384241e900e021311800680b0626202007408201005c0603c440c4c0303000b2021040c030072181d0010004841e604000420f07014503616040c05040c0c03092089503800e0790751036040341640109100758020340c842e54040006101c02c690003031203038070182000d4081c11025100e40c00003c1c064014030fa95002d9181e1b410740c0200500140c1d82044410b6802004081000c0f074003007140040c148529404100400c900308101c102450040f642a521007408500b039812540e00e8403c080d41c0012a0403c51001840100d008102e03450288580341403511203040c100000c514000c9200404d005030680500a40310708600c103018050403500c8100c552000800c040d00010242901034420b550741d505541c046441d0741108007558160384212030203 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 973938363 1250 973937113 973937117
    0x3141c0609050c04090209120106030803010915061202070303090210050d0e0705090414070b16060b0a03111201020417070612090507030b041e03110d03090c0501030507050c03030411090a0b01 84
    0x1130075080284800180d80400042600401038880e2412114801e00c80d18003d10320440a66036a0b5140a440e40180da035a13000d20b8020240c00b907400c02603690440a5490525030042d40540c40d450507040590007001094400780d040b81c00d070411540c00540c4440105240c05094900300100604400080d6880303a40e402500c0d08800a4008074000ca0030400100501141c5101210425915800b81820f1500304840c602d14001e4803641c07000c1046124001e05800c0c100558102d44042d00d192500465002d480b004240200f00042c1814079000003901280c0c043d2408141c10320404060030039080c1d861416200348800684074840c5a0b00ca8410707400344001b80b540150041c00c05c01d041da01c40c00c148102c00392044440c243c1708110021003191500404410501035226140e800d07026014140c00c004502c0c0c4080d04252030200c06000040141994809803142860005000c0c0c3ea4060140c0b1984100709140605120100c2003000300100a225104e8a440a0301d1540a544840c1d00c2d19045c0d4030302081c0c41e40 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 973939613 1250 973938363 973938367
    0x603150405030421060f0b090702060702151506041d09070f05060306040204180606110c010207030b0901020c0a0501020408070f084b06010b07030206011203141c0609050c 75
    0x210706001002400b90020b13034900701040341c80466403400304a440d00710500c040341d078540d042040e5916140b459283e210151740007400e01890320403402900c81c112030004400800c41500484c513001410380d0300e1400d404000d080d160791503885100403417010601842c4e03584000010400581e0144002c1251401c071a0020542c10a10781444100121074100801c602c1d0055401d00c4001a03c0031035421500440105010019038681043c20003440e070075541d440f4140c164443c115020043e640010000e080740d03042441341295807220140540644940100c1002d00d00c0350790f114005021040d80180216011903084407503059075035541100c1303411648074401700340c0c010201e00c60f100880807100e18000e21465440180d50404a00c4a0f100314080303a52a0242c1e603200c0b0140481d0b004100201c502500c116120745007440d4060b5802950344105005591a02304880701150405014088494101c11000e01580d1515910380803400d00544440d204c0c3c2030242040000103107000c0c00e105160260a450030114 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 973940863 1250 973939613 973939619
    0x20f0304120c0f03030902090604020a021009050114190c0c030903020f01020a020a0b120c0f041a0f120a05100e0a020901200105040209100e070809031c0506031504050304 75
    0x10007451480410007081c0b10040503140c0028101c120010b6065101740c400082c1800c0030b00610640b0b501c000c103054065441002004207103600001c1054032a5620352010a40910502d0500d014180584418400b01070076001c4c420a074842100d400f40f81000044108000070111104036102d0750422000f0b03010610205040c005402e081100c50001c01040c0115030305141e25602260200301503a21111118102260420070002640c40341c0380c02010078003810b8200001c0031425440c6104502c80c04403c2c4a0f048840c84040260200f1b982170041902c0d04592103944030309442c103141c0d1003190f0302210300d450400040ca1803c0864920380039200d84920300c9109507240d8410100a500054195040c406941c1640c07021101c09540c0340f1000d00d83c2000070466007440e2052001c982406400c10254203000d030414010145042019030f8000d0f0720780780942c00794407080d51240c00c511030305c481403003c0ca0750300a903da2820015042a40a080e0580442d0fa1040413034400841c036410075240100707180c001b00020 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 973942113 1250 973940863 973940873
    0x6100b03041103070b0a030f02031b070c0b0307020d0e030a0b18030904020c0c0913081c1d06010321080105060d14091b0a1d0c1e070b0a020f0304 64
    0x14590281c03141d282e048010303014500080c54032650740c0c0414017003680011121170069040c01030b104241c801d40750950442c02c0c45601124139803903803c20038205800210386103060000b0502000010032a2048569890509000081d281c0303040700180d0000c50081d5410000505002807600642c83d00054041030b01c1e111440110064440c442c061000b920080c000c1c0701c000c0d074441c401401e0410048004245542043d01407218201e4010401303421040034070795440100d141c0e0b40482d03030b105403940003100102400440200080010042c030070410800e042d840e510300400003400b54182c5c8e0107202281e20200a60f60001ca01c01c0400995400045400004201604103c0c000d170502420b615030200e8912042c4100d8003040004031280c490551102104140c204840c82105200f4082561140c4c84141000454860400001c219507520101400025407141c0b03403c2c1910058803500b510b1800d12000441c405c40c054200420917901006104040703903104420f0b10848280718450510b2509507543da0b120 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 973943363 1250 973942113 973942117
    0x409090c1a0a030515030723010f02100203040804270e03160b060307091103070906140723010f0204050906090115050a0309050102031311041a0d0c1a1b06100b 70
    0xa04000c1860103580250711b50341802048058080d441e24003900795160400b003040e582a007107045040c0011400d03c11420f0350302107040c070740f20f04020001503a65101c80c44e0400507441107602041041c08590228030203403104140303d04060400007814042d8981d03980086450340328908203081083c0e00340e00110001500b01d0708460b030083c002070507680c00c195140e003404140d40301d400c0c2000301e6100c00420800620f4100449001800b40d0345071184100546124000765845580805040d10301d02c0c0d0106070f881d96a4003070b09040690044001d02006907403c51802c080e4100b4083c03284290405800032b040741c20040d52041c120b0703c003143c0a2030342180381d2105407030941c06040308100701500c0340112404240d01740010342c007030303c0e503180c0b400850310017424428504000d240a5a1089040201a82c020100d0084100120314116585c3c08400c3c6903203015103c0d80c1c0c10782d009051034000d80c0522500748820b1800b0b0300c0c04000708044150000401603050342c89410803075503048a4181c40354144580640840 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 973944613 1250 973943363 973943371
    0x120a0603051606230d050405211303110f030a060c142505030f030f10080f06070e0604030b161121030705091c050f16030f03140409090c1a0a0305 64
    0x113915031038444c205244c20152803044030b041da1180d100e180c6680711034480c80c0903161292940001641841c610400010300403080e440050007002080a41c04101d50b2528849102c034100101110380c0c000071786c84c1c4000a0140c0e0907844000c20100d11003100250b18113022540502740501c0796040c1500079001c00e01c461102c4500680d45807005216100500103407000460083e025400802907e1511410300309180d121074121043c150000405c1005403140000d1064112829003409000300b41d00d040855440c1c0a160f00140c203d5204009000707015080c080ba01c111300100c4da03602c5640030003041c129030b0f580d10ac0301d40a1001000d030510444046819101450300860b2510307000c0d2074480c4010020f800e10f20182004501c0305c901c05040010000100001c1038000052400703010004100d480b003403954025480080c1c048040550b1074010035111b00c1340c800b080f651420302562603a03220000107009100c1c40300111101c0d21000000f1030046200741c030074002030202e81c04191400140041c00c50140c58050 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 973945863 1250 973944613 973944677
    0x120610093603020a1407050a091109011d0a0e06150a14070309050d0302030306280501050c0109051509160311061c1e050f010f030215120a0603051606 66
    0x130345240000700301420742c0d044120303c40018400725007040200440c40015500c100400d81c6031010b0614100c0782032040d203424035001d003085c0f00750001d1704200c3d115140318200342d1030303108008200210301c004920840301c1c06480d00b5508003040d080000840d40252013052920f0000c035085041c00030810701c51600406203d442881c00014043e40c2c0c0001c0354170112a40401c41c0580c0002c400c0000d0380c1441040c408503544020071401d8900c00341340380a26120f64a0207440d0400a00142016500409402ca0300740281c0c00002c803003480e4003a809682d0b141409039860322250141c4040d0310000784c1222643c10990760080282c080007801c44080156640c071102c0320140c401d618044007541656a8490314100c502c0c840001602c0c020400c80d610221400101031003100c605d2480107019203506200007405030b03981601c6030107811155035910700c0345000c1c0051030304000000c0020855001100e8010404803032066089441541c46886c01d041c018005004900001d00301500648106007420740b490245243c407 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 973947113 1250 973945863 973945873
    0x3011a030c0f0708041d10090b0f1818030406050d05070c051f0f02041805090a0605091606210209060409141e0106020c0103050612061009360302 64
    0x403031146500c94014640a99080e071001c034040096481060728006c000220503003201003803410a6290f0940e0381d10707015660400303a031042d4154190300c4180b51764034640c4006041640b40f00114400c0400901e0807210340c400c40c0a02100744104c3c01000041d00c013a5080b50701c510741089a00c00041d0010b2000800c4413041005200441d40400c0042c01840514541507e90300713202000403000d117080e1f5820400e550f2141e881000204444503c002d00c02214404501c0049816160a46628505001000007a04035840d01c03085c07003407680001504080f00025150000c4107680e5a000680d070b03007040d90003000c1c02c0382c104007030801e042d0605900900c403040b0010401070516480e41e6640781100c808581d1150550b00c0341e0213100444c40305024481800c04a0003426000f50f042280094440141035a05418540ca580200702e59a480300d09068003855402c0454100e85401c840004501999201d40c1425604d495081480d08040702c07501c0d440e01c2010030090300420264900400e5a081c1003005070214020 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 973948363 1250 973947113 973947127
    0x7060c15020309070e0106020a0b06040c05043201030203040f0308180d02010f0f3323040e06070507230105100f0501050405010c11040609020c15060603011a030c 71
    0x8540301a50040011000404c000303070030b200c0c0e410400501a0400011f5521020280d4001140c0300030340755102400b40c9011031800d40c8048152a0b500940d086200c0300511044000e490085c0a01c000c5c650f001c0c3c0b2580c01446440042c019030480c801560701400c812006080b48002c0f038040d100c02a0842d1650450440c0c5100f42c0d0061410300713003480b03041d500507512034402030310848460244e81d00c082038005040000358849280e40c5607450f80602010031443c03d15100c109000e1000c20440e0041c03d2800111000030850030f540c0d280c0395008982c8501c81c0b85441491502800000748143c4601056104c0c4c03450705030347c2d4440e40313000214181300308108000604c0136001c001c0c0078003a0078020742e040d84090044c6410030443c075410030490380010381000f0040c801088641c0c1e012000c0c8040301d81041d08603c02035441c0c0c021401074072103900140d40c0240001801c10480c0c800140483c4a0300c050590007001c1c0d00ca100801965110038410b161040a51000e0f141a031034880009541040b4506255450b18003 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 973949613 1250 973948363 973948403
    0xf04020d15060f03020906100512130b1e0907050108130f140a020a0b090a0b0703051215030c01090b0928030f12052703121917070207060c 61
    0xb03410781200e01c90801c035000420071814034480040d004030341100c40c0405100700c40380013801d500542450303000e40341955001c1984e0000d20100d10035410742168904584d441c2991807111001003e0003814001307441d0780d00080183c2e070b0104070181034510581d01c0910303640303c03032030511070703001c0c2d4110151410200110050300041c0344012164600481d000500b0082c0b03014010031803009000e80c045450008100070450f12941d80143c05c45c251a000441c40f43c807080c1a0070121280e00a07603950000d101c1d010024400841206103030140b11007021003c0399007481c05840116051400c40c071502d032162401780818180c80c904215500d40044010300d0217400700d0381103182c02d80212940d60090b03e205255845010502c5981d04290340300e2400e50a041f0f107440401801c401124200500c0c00740d050012030000071055030140014010510744a00050711380b2224041e041c0110700ca8201580400d11190b08828400340140070700f4030460b40c5801030800a8030b07001c0c0070398a80300030a0b022a005143c101c170084140b4 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 973950863 1250 973949613 973949621
    0x160e0a0e0105092b08010b1c0507031a06070b01141f080a06050904080306040c0207080d0e040b0301290f10030c02010e0c030d0516080406050a0210050f04020d15 71
    0x9000c801000789402414144c840d454130b2820f118800300580448008032038014014504450a025016950341c00b040b1450801941e4100c005441904207811311480a51540010000c410400b9040081d0421042080320358070450070700070545810100100300c5c944001d14844c01500d406000400f10080403140a50303102a0b420031400800d14002c184110b08000780303d070f08060681603c189501d42400c1c4c030352540c03501004041d02c2c0f01e25194003100340d1440c400d010840c014030508049414056181c00042c00301140900030034000d9242081180b07840c541401079460750616a10170b48420501100c43d10100c138205448940c01000e024190062500d42820315a0005100d58000a02c078480034002030955000c0f04103207065921400030f610b42c1e81e801180400c41e20302d20781001503440780500c9810401080149014011080c0440c0000e15141c020f0000d080358100f913030950360b0030030719240e040085480544003400c1030302c0b16a00240060030001c0c0389001c0d45000390f003c14091003c048442c07040e9 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 973952113 1250 973950863 973950871
    0x5030a0b040c090603150903230c101a120c06031e0708090d0e030c030d05130e160f0e130f0e0f060f130b07090e0702160e0a0e0105 58
    0x6625210104420710a11126071005028a04800e000003891a11b403032100c8002e06070540c0381150f403800c62030201401801d004885c882d1040340141811803110345405581c00900044185000308031000d84004034910500090840b090700900d030160081c400c0c003803000481c48240400703100b00b92480c0304a5a4a002640c428003201013200304121411040e2883c0c0d07400a02000d044c0011401401290034001c01d1002842c00640781100802801c0000685007018101341e007a01030242c5168480043d502c000201940d0b81c85240c034008450395000b134021039880c11108405c05224100c01c15205620402c4841400c04507894050302039803041d4001485031244900301010a03680d080e0390100d1032581d0256101c812440b60291065103002120340b601c4100081202000c000c222000a0108012291000219420494a6426203001344002d0191550340c041c42204000120004821358400501d1113a0b05442c400030401c81c83c41c00f51060740c1c0e076030007405071a0341c15250f041640c0e040100b40300b007603c5 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 973953363 1250 973952113 973952123
    0x40b03011b142203230a0803060a030b0406093f030e010c030f05071d0f0a23010806090c07061a030129010c0b2d0103050a031101060602120c030405030a 67
    0x240392071464803034003052417040d41c0e5441380398817003141e258a0700104011001681120045680390303581c400007a082d410f990002030032103800405010900030702c1d034807904100c0e20410000003403544000c03544600c040003040101c2c05900d011a1048074510300780e202081c044c11810045103140c2c951707001c01e0940383c201071064002550380740c1d49200d1090314040c030354229005050182c0c011350141002035101c010490300700c0c02000c400e16640c165488120001c001403144403840407094847ea04007100ca8114480d074540000c602c003011075414a0085001405030004100e16482d01003c2da5601002c1c1030800f12170940f48038100c3c0c40d15a50348003802a807034140750399141360011580320304895444030002c1d28041d042048a015801c000340c5495083c0e034001040d840020b01c3c0c441d01145030b0041520090040c001410701000001c200100080c50301c50a0b0301c25140c1301d0703540c01c80d00106401c0350602e106031001a07020040a00b011ba80840007050190400001d491030103440d000031a01d0803070800f60880b0 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 973954613 1250 973953363 973953427
    0x313060c0e040903110d1d010e0a1e090b030d08041401090c330905010810050604180c17011202120d0807020f010209030d121e0209040b03011b14 64
    0x70140200b0b00404070b8a0003103042c05d041003c201855002c281c98020309290612a00c622769407500d50302c100d0032000500c170700c480b414010812403031042c01120f0148503003803881d820000b150707038180b4011480341444040c1c0d56411490b40d03101e85669907040e0071040d005855550352041140801c2c0b0007408980509405420302c25140f42e0f00410f811007400701c02c1c2c1c01010b84c852a85581d901c0c3d034081c2c0030200300c80c030034603281d00030381c40b03040e41d50303a9808541c1c1c4016400038001400007034210504810300c907100d03010b01e000c001000c0400c0b0161091a0030303280f541022444140180f00b00da10a80744500000e0004d0800851a00014211880d0100404102c1c01140b0100100035849504001c0e03000c0e507101c801c00a608000d0000082590b482400d405081031241340511080002c1c85644010f880801c00e00422030102401030207040258060415070f0b0080d82004565a00c17401d05024004042e000384004016081c2506000c403400d504507200c403400b06800f000404038420446032441e104401c00344800d0 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 973955863 1250 973954613 973954637
    0x81509070e12070503030d021309090c0302040516090b180312070c0b0a0c120e180702010c0c110603091f240602031902070b0c0a15020313060c0e040903 67
    0x100d4000d074802c44003100da01a40d0107000759140807003034500c5098070402c0980c403147c5d46003541e140c003861508004c581918200384141030014000c1071604403402910200700c60344a4040c824040c0c400c040034030004c01e1a00400b000100c0c3c0d00740040c851101000d600c04d00c54114980001e0600b07007540792540c0c903a1004034000d4207002011000c00018014800100d142050b03c98004d46098071455015255441813a4110080c502075136440701000c0004064182883d01050b51500e95441512980b0041d880c0c41d58804225005a403c541c103190068030807044949102c08100c11a40024045001400f4802a03280b0311050207998056140207504040390f040e03000802c160300500b00321200c02c490705001404000c400d4008c01100c54506520b44c9204410701600000d9180c41510b9000340c1c035450303001500c1c111506000c147d4480980c801c0d00a122421826003915050303000076900042040c5040481e100001d2407980465001411030a140138403080340c4001808941d400d240607008229401c1000d = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 973957113 1250 973955863 973955869
    0x15091a03031207050a02070e1608070801140d11061611040b09070c0c0b04090605010311071109040611030c03060f0a0807120305130f0513051501081509070e 69
    0x29044500040c0c00031420301d00b0b00d01420320190310103091442403100000310308803014400c4c000e02d80500450810310519040c507440048452420201900c0025030310004128914860000d0fa81210b0240c04106940d450103030810080d000c01c02400c84c0d0180e0740c00308600b00c0b40c8401d8094041d61180700d1450046201c6420003141c902c000c0041144982e140c070100040c40d54031081c1c526046140c5240c8181010614070b0000c280804035000340301d46c40b00c0450b0008041c211074001a05a90f404c2ea018011600303000c440102c103001c0e00100500c8840c1810104219041c01c40c1181d6101d40111004a049140d00070340c0001c0b5030013507071450070b1ba4800004124107400c042c201544115015540244204d1400c0c2d0041d0f1a00f4440c0148501c80c060b00b2030000906200342c0648103080c240c0d20f18400d1840c0d6402014040400710710030a401001a00d541541c84140f503c2407034482d50341c0d03215044030001d003000115004440104103143e42d1845400034661900c0e07050f41349105049036180c0d500d00070307035040070 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 973958363 1250 973957113 973957151
    0xc0a12020f010b090103080a050d1b02010e070f090b03100f0203040c120c06050c0a0501060f050a0803180103020a110d0c0b01051507060209060415050304060f06060f0c05011509 78
    0x54141e4981c1000389140c5140c542451160440b074009800341e4030740803940c104640f20311032030351040ca52900304100c100c40e00c14070311604a4001099002008245110303042c19842d401300c2e12400c8000700c00c0c420208034180d000d800c031141c0010000e0545403240800742002003110a201c0107105a41d50200c1003108004d5001450009800884140d003407410550f0394900c1c410b24680075035800c1280c04156040002c5003041040c0d0310b50342c000000d02009031a45180b130f072032021900c14140316001da0031000a56010103c1121443c3c0558006145016000c00c0150007a40c00343c0004002c10105460b6040b030703108280f144207404c00403652031003462081c4e810310104c07c50301a000b00d4407964503820701301001001c00c4125481c043d4498000368850301c407080051070601440e4030070101040e1000e1031042ca2548075000f148070f01d100e45c80402010a0707500c5070300116100340c02070002007800501e4420a050240ca032811b103180c8100c0002c64042e154040d8403640c101964805001c2a1f180e0000d00700030008201 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 973959613 1250 973958363 973958383
    0x90803040c1a030411121218040606031803030e07050402042304020405060d0b13050c030711060f0f0424020c0106140607030c062c1006050112020a050c0a1202 70
    0x40c04900750b04103a00c602c915030070b0100c4124800e10340b04240b041c01440510007011050b02c40c0f80b5071f41e11440d040311021860001c40c40703a144030360302c0e280020039418020f1083d4001ca0200301101140c01116680640080000c45a04242d500c944000028140e640c0d00050001e0949204206050304a10606044035051448050700c20340c01808144515150380d801c0d55244188040003090381805400410f140304011814480e945044c0380402549044680055026110982d42c040c80000030050051701e4000a079410f03a1034140a20202d0400c0c07007610075850300300b0f0240460400d2190100800d030650980c160000c12a50b80103d14405c00304428416500205143c07001440119a190000b6140c1e104003040241441a00754021052010382d9100c2448400100c1705455450280064a1000b880c0d041c5100c10601c03030214031034400300c80e80c0221011244103840f110240b096100d940c1004e90001000d005c1040700c01d120f0114004030801c1110075803401a05903001150781944001d0808003014 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 973960863 1250 973959613 973959659
    0x31603110f060723130b070b1503150c0c0106081612051009081e07020f060a0f050c0f070e070201050c03091209183c040f020103090803040c 62
    0x60410007265000102c4c030251210070300e040904c00355480d50303021041c010400e1140c2c903101d81510103c1c2d050b02d0701c4002c200c40d0340a850401203543d96000d0703600b1181800b550068054100300594035220554140d0590000c20f01c0c90301c0b0741004801e0b018182111000c2d4410240c50344100228280c1c00000c00c02000134003121803030304000c26100c0d02d03074a554800030078a4040043d503403000e92042c444a9000c0d00c54501d90300d0b00c0f0b03160f90250224013100e5130b0001c40003a031007105c1d0140300000c546000c10480d407401c4882d071a10300c83c14503224001c0c0d41030340020800401d94015440b2644c07110b50188541d502400d40f64560041a040940d4000d0131a88001d141148503142001844100716000130300c1032820074403490699445100d05c0c0480d00050780088031b00d59105164090103994494003da285d18204180000b8441d54414203d4028000c0c4618541100399031000100d0042504e00385d14440190041c10007041c1c440032a502c9501c291300840d002d42e521214141c0900c41c4489421502e540c0b50801 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 973962113 1250 973960863 973960873
    0x12020d0228140319032609100209090a0903090506041205060603010527070e011401030c0e0109060806060702100c140c09060618060415120903080f09031603110f 71
    0x29801080d9030b6032010000c004029840d560f40000c051181441c03031000f8000c1840004451110001c62000c440700f40c84040c0207001c0c02003011100344480c070070f0312b110b5032004003103034481d8943da44948002c0c40950819010440704080208964131951700400c018846410740108081450805506042d40a0700052007a4140028068035080381b0f40141039018501d00c0038036621a10407181031801d925980814815201c01000140080c0007a0584100031405c1c0c90512580101705012070f00203200a0502e80421440b003c2401042c0c03183c001c1a92040d0054036841c03a06883e1340004000e00c5000482c040022045d0f1780410401030302d00ca030800410307140c8004004296044c400038800d02c4c0c001b0030850007090003181c900040407620041c0614000068040c0783e44039107455560b40b5000b81c080000000c00c4048124030818429881013a6909406030b40f080f1164481c010001e1000c5009002e100e4a0b00c41404500c0280350741c50352001c5140d03c00e49030200c0458100c000c10f0b09080000c200d00e05942c2003 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 973963363 1250 973962113 973962149
    0x105060a0b041a07020a1401110706140a0c050106031b0b030c030a02030403030b15040504060803160f0c08060703021c29042c0c03061012020d0228 65
    0x524159025140302540403502c9480300f00ea00c1085000708903005e544080c2c120030004842e2111000020440b6007a07840c442c885400784152541d81c3c209100341300c001560801e1405843e6024806032900d2450381c40c0102d001082c1d84c88090a4030b4568005a80804000f0740c0d03000840ca4040c0110300820032000403908514140070041031031f00004050f40c0000ba000000541003500c0707540b00d84001400140344004900071101450601e8000c0d00505008604c1d084011400040c0001610307400c0512a00425000700150b440c6040d041070b2100440e90508c02c004041420102840f03400e1140c00a0b550042c0c0f6003513260b4050500e20f510640c81e2a200c0c5c03420050100c42d26100765003e131092061020070f500c1c440c080e4003203802801402d0882510442500304401213952001c01140410b850304200c5d502c94462408064460400791140d42c020030050a08002003420005968100c0e4001402500440c0a68000c41c640c4c510002d641001c9c03c8032310540c815844051000c00c0e0181c138910140d1800440 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 973964613 1250 973963363 973963379
    0x7050a03081e09040f09120207030209040f020301022104020123031b310f210c0e13020307140d081810090f0602190809031e0307050105060a 62
    0x1064415003019054503502004011a0103000c0300e525500140041008004111800c001400501000c44890170f87c4a04200f1540c400103c0009a9400030400e0105444640e1090021070f82c1c044200d130195024002c040480b03004c1c074a0341070120000c82c075900c014605440010501c0052024903600784409241500d00541d420041e00c4c0d024081114410704641d0b0f4000c40383d600e0150301b00d0310b0034540428454200c041d0080c0c3d4914000103000c032400030444d4890110070f29241441c019040100f68900c00700314210454281940710a000d480300c10301841d1100030180102030704466000108031304c10400702c21802d003000410300400e400072121411600110000c1d21403621441d01405a0501050181012210b0300c002c0c44043e00041034801c1451440001070305090b050310541e284141d500f440042d10a00200e00c0070720801030040c1e5540000076554446d412604440c0d074003501441945150101428049119401040290000d689a0703d00d86012425180006c12a0703026030004441002900 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 973965863 1250 973964613 973964617
    0x9050313082b03020a090f0f090b0603090d051b241810020d0f02030f010f08190602250525031101030506191202011b020108011401140c06060307050a0308 68
    0x2070240340140e5114035585e030403a200c50003034103d4040c1c0301040c900081c00c205030401010448406d0003040c00407520385810030a182c04111500401e0750019528415442e100d60020720301195a82496801c90b00c030a1082da1a04644640c0070100000f00501482c1c444601c860b8580d00c8210010261b14040741164800c1e1101e0109207240c0d2103a40110303164020320344980202c0c07110503a0307000454a916104860b00b08140f000c0c842c452401020103c04500b030352010518140d510440401070002e40c200340d844e40c0c020350101c1d0b5124211a8104814030140040c5408800c41900403801001d43c00f4a041e11414402010210504a0000760500708000b51911000e814085002d080018180d039403640814810800b41b96200d98100d001480842d000710f031a0840809039000ba42c0c1c02d5540c848140b000b00c103540c2c002c20080e01142540004220322503280c2c0414030742e0401031409400c1d1f03201081d40d54102d0340210284c0300b40c0382c20400421140c3d04041042c80000c2030115109140d45203142c54002444c = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 973967113 1250 973965863 973965943
    0xc2713051e061516140303090604020d060e03030a050402011d030c09041103030a0c200919022b05160c060e030403150f2d0509010905031308 62
    0x34000100241180d51407001180f0801d45007600c0c10f0703694203000900302040c0c0c800340040380d921210030940840e000c40042034034884e5000780010221916144c0811580012192040311103d4803259440584a03081c0302460085043c5000030603242403500c0098840110140b6000c1400c2d000500c007052541c0008264112200070782d02c81c01c00d51594146840380881e010342c0e150b054800010b0540c0d54507400641d100b1082d010328112180703500024540440b1811071000c0707a83c000c06000c085942402008c0d1001000340b00854010f2030150800d422502c07030020300700b40321141c110710103080c80c8070507072405801c1e40261031161660118280440140c12101c4412003d004e490381ca840d18510071108004440185800c0320081019000c80e03990800601003450f6480d009500f410409840b42500c0102e290001400009101000e00d699501d4801004002c2c40a8115900c48000030085003003400203200082c2c480703890f101d8444c01c01c503402e880d0150041000d40301c0880d6040c0d502040c610901e012080c = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 973968363 1250 973967113 973967161
    0x506071220310512030c01091b0902030c0301061803020a0b07061104031208040f0c090603030e0d02030c01050a020102121501020706020a08030f06010203070203010606021b0d050d080c271305 84
    0x284d070810f44c1405146003d01807034000d09618000001c4240580000e002d001107940e095001012521540807500303a000a172103401c404102480144040ba004810344400e440c0380c102403447c0c0b81c0d520340000d071302d843c0c496004c008402c0000542c81e09000040c010343c8032002144100070b01d80f52a550761041d815681d41c2c00360b020000090081802c1041c1110882d50007074100803410809030b12981800c00402480c4012070210b1040d1202941ca03060090407010b00d25002406420f08002c8007006651a601c001062411950700300f0841d074119460b078003114054201400303a2448032814500291400d60f007030300640305643c84544120001006401100d910a000240d4a5890344034840140d10b54000c82d2030095040d400c02e0303000724240764009441d41440542d40045003403404040148401c0d82004100070700142c100c0080c002e40385016541c056085117a058420b8640714503820b403800800e10000c41608244541d0012900e90b00d003031901c3c0e5072051101c180420150411446d05031404110181d0048 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 973969613 1250 973968363 973968379
    0x120f051017030d0203091b03150a020f0c030409020c01050702160b07030c0b0f0f13080f09010513030305270d0b0403021002040602150f0405060712203105 68
    0x54064000d00070f80d9050010503034199120300700240f285840312601d4803425440c04008400103614580000d008100c0107a06c80c40080c1500ca280404010307610040740e00c14111000c01100055180400040008000c00340005888081e100e1100d425900d016246904540c461011010b41c1d104001034542141d005c2000141e07108020f14042ea4203080b5003502502e0040303c5000c01040e003074902036046c85408000601c00041e90750044012507144101005054200c0900a840c56000801c004020558050500f90b06100150300f00710001b00d0342c0d81040300020f4012540d03004c0c403e1000900d030581d001c013199082503080f848001c201c84e016600d102a101c80e1150011178241402484500d21503100072609560321626050302030b42c0d442c2c800200042d201010000229030756505001d181c0520750040c09050151600c010848032060301079603da003072035501e1110415003081d90340c5102209950225264a40c00080c2e260184034003804110307a03100d95a80c2441c101026503010050a448041343d15072 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 973970863 1250 973969613 973969649
    0x61a0a06110c0d0b06030f0303070e0f040605031213060302090d0b0a061a0711040209090105090408090406061205132a0302030712140d140c0a050706120f0510 70
    0x1030b251901016140d0b8129803400800c41c00d2290041c5030600c07130501a0101e4401080703242006a5a12044a03a0750000380c0744140f1112600d0603503008140c048008202042c0c0340d86640009080c2120308001c1c651113400007411140780101407800748003c0440d400c0450904d14000046025502034401c010004146800003c0000c811b0b0b0307000f00301524000541050080d5040c0c0c2c041142e41c0051420b950307048101341c0017a0b5910b0507000700c0d05e0007100901140c1140e440d00303051244004019008569400c803d01c1414101c3e1aa0b101e000300601c2103076183c00c3c003121007100700c4003150070150a42200799044c2e00080d0104d1008182e0000d02a030b0a4084501008203107031643e5500e0503034000940c94000d6400014144074420920915070f40030f121088140d81890048a5a4040c00d01c035400c0465084030b10040180059400307000f05803810416a03020f07030043e0b517403142031500c25000a4040b81207040c1c20b4018040758132449c2c42020a03490b003040503091080012400181c24482c900c0380c600340048803 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 973972113 1250 973970863 973970897
    0x3080601031d060106030213080102070f0215040b0c06150d0b0f060126040b2401080a1b030905070501020f10020a020a05030a080420130c050412080403061a0a06 71
    0x10188400c02c1a00350750180d61a03800c010080e600418444140303010045004c41c00030700c18401c841da02039104026401c203000650034803600c0c205c50691800444010f02001036010070503001481a61145000380c1610315000c820103603c4448100211301038215401100009229281d50030381151005000c401a6070b2038900403901c0324039000350f1003540d10181380d00c02030704108460700034041d82c440c1e9003070541030340d401d028508041c01010350350794840c65400300d515465005110071900103a14070004030707060703014402410a4114030441c01c0000b0b40c0d20114042440703010b002ca07102800e4248050030700c0d12429075895a0700ca100e04801ca10f41c2d540020740b034104c540208400081e00e640141500c0e00d40f02c0b032510152078038404450a0302d118250402190340d9002c03028603c0b9410700e00400030150045034000c00002451034400000c240a01040b021451240c90551314181d98840d16040d551a42549000f03c145c403c5002c800300760444d080342c002403d075a598440000d9a0300d501d00004449007031014 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 973973363 1250 973972113 973972151
    0x123040b1824090f0f0310060e01062f12160c05040b0a0e10030203010504150c021219090302090108010c0e03010c1b061b090914070e12010209030712120c0308060103 73
    0x105c0c0d540f501c256100640348516941064045558007400340d00c150780e0f21030007540c1001403000700e42c0c0300c50203010f1a0a40c042c030315000001e581c014a030840c2c00118500000203041d906c0007102d407072114030039515081081508a0040702400041d14184408ac2c1a6000305241c81218002d40e00f071038808100180840c5400d002210080d500240240243e05181c10700c0c0750f20b920600e03540c0d1400c40c101801164958000150f40e5010107060300040d107080303100040c102617040018072903010803501c50000009603440d003e0142c0039046110000600500040025052901d10b80c1401c2c002d07414009407000180c0c1200701c59004203c50b60542182c2645441c0080092410401e4210300042002c4c021003450740c0000c40c803050314110b640030807501c2d117a0800c0e003804d03040c111942d60009414580100703441c10900c0c0280015030b1082c0000d81454500340010703040000c01d4001003481c1006108507030500a04540301b5500e440c1c58100320b4291140c60710001c1607002d00030a003034141900d51400030310401030460 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 973974613 1250 973973363 973973389
    0xf050f180a0504021005040302150d0e0a140106060c230a12030b0a0b070506011e092f030921070f030c0b150123040b1824090f 56
    0x5000e680d00d00c0d00c8401d5100070001500d082e4014400d5040c02008240500122400e4075001050348010658a40c0c8045490380003030200031ba2140c81e540e80ca407140604004c14020f291040720844100c8903100240c07030846840354882c00400c170225403130402240601203c1070701d016159580005411820a103189048444403000301000301d40841a810141d065100241518040b41d20510003651012180381c80e0064050107003550304507600400a0b16802617000e0181c121150310f183d08681d4074a048401c45007002c60070141003966807a49000b14402c5441d60540700f999080c0f142c11400c000c407a49640b2000084401d0f6076900800082e940000301000380e8448aa1000c981c640f140d0072860001c1c61140c2000c800c4034114901004118202551068a0401c04040c5d43c1c03183d00d480995022901d5120428060070f401c030080001041510300c150040a4000c0c030311400440a910300380030300007034a07004484849003075900703c0745100007902c030320072640b056601303d811030f1400900b01d0000326015110a = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 973975863 1250 973974613 973974649
    0xc020714090907180902090f0f060108070e15030f0a090804030f1704060e6403031103070b0103022403090d0801120201091502031306110d03060f050f 66
    0x302500a02030f0f04e03a00518152807003500d0030400c907100e2400d410400d0340c0c140d4910642320660000070710756502c140b580a6025a9502c1d10000100003a070201e1001122144491050b0f4000410002e0302d25000c14507680241004008000c18152a290301e10a030090340001810f80111405c0c80c414050190b2260500100341d02082d0f40da43e0b5118800f600e12001c40710418010f40c2019164452500102100a2003040210684401e400103400c40c050304040c421254aa4114544030202652407280d032001c0780c1d81121502000460031824081d10f6041d801080049951041001d44c00141c3d00c180e9290446c0e506454412814254011441054104042c01c0d850b9030008010040c0101c000200a01d80c0c13049511440400c1c1d0329090592490b054480d0302901003150240d0130000c9501211440721003150510540e42400041c0ba01038a12070840e03400200064607000351085464410300c501c1040350b4090808008440c42c051956007040d40350310440d80318095081001d6000e07200d51000c001c0c07018000d = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 973977113 1250 973975863 973975889
    0x30711010b1c02040515060405010e010201021b0109030908070b1b100e0706120506031209060c1204051008100303030e0307150515010c1a0a060302220c020714090907 73
    0x16142d00c01c50b2010719070203a110f24181030215100b01c1042e00b4004008001400d602d140034105070056410401159510341159401c001c6500a0390000110304444081b903000404c000000c0d080052421240d034200320b101d5000361900b0040143c21004540c44144041011055241410101820800300128014007107082180c1c0081c035640104811050325195103500b800048000421400c071501100c00b541c01d68015440b14807240c0c215070103172100c640018001d6152507410802c0710b08040013048910228032012405100524240c8407203001c91100d8900703a03440c0e18004c03800c8400243d0620024090690f00c581c880241003050040750141a04450060b1021174130455070002400103e03018401d0b20407000000185611900c1c4070903045030003442e400b141e44083c01c08090f05070005000804c03403903175503040000181c40351001100c4400200c0729000009074002644402e60b040101690115000300005019a8148400340c9100388010384e11030520355604100700c0c1c074168079504004c0c110516 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 973978363 1250 973977113 973977139
    0x22d0a20010e060117070b0d09080412060218040216030c171b160305121305100206040203010516051c110301230d0b06041503120c0501060e0606030711010b 69
    0x400600315040743d45000c00c0004c10100b00500b1602e86d2814021980c0000041181030032440c1150060403071640108982c502c0d16917651a068078223008058129410394010520703018032641040c402c400000e064800303602e272103045030740c0d0100c4851003d002018031000e041035206010480705110101407000d1003569a91281125041d1801c80300d240d055120b11504044400760f0564014841c2100c0d03202e0300400616a010401c0c1c3d199400c03034414a213003001101c00020725580c50269041d84841350781c01610040c01e15005241c25603500608100c00a484c03030301c0b030340f540310350100440b02c000d464100d21440440b26602e17084094091440c3c030007020706000c400030444e1100c20030304c85460301042032280e1480c00706c001805141180684007520610910000803594149500b02161348007607802120041a125a11a0703840c0d40e240180c400010340410049003002024450705001d042511409001c4e4a4a000080e80621009024101300010707219a010300c14425045040e00300750080604582d002 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 973979613 1250 973978363 973978391
    0x409110d03021f061e14011112070602030105041d0c04020901020f060108060f0a0b060403020607050102092e1b0602090a0314060403030b01081003020405130f06022d0a2001 76
    0x3005000f100050308001201841080c2c031050654200c40d491110f090414032100015180c102c5230801051040c05a10054501c80034108000d01c41a8894038005031654140f500f400100d0751f041c500000070b110b00c42407944078907500040b440c2000404a03800b5035601c001200407402c2c19641c4100e48100d205040c00400c100d800030440030b120341d02c4402c007806203030f1341c800e580c038180c0305000721440d00200104018405070170943e008203030160142001514100c203901c0031441003e091076000f03042c0031400d26126060110601800d0300b0082a1030004941180e003040e4000c18a80c004000304041d5000505881940720740342c20500070354000200a0100c0c2080d40d81607118130341100e08030300003403802c0c04d590103540c014006203020300700034641c0c070303580a0440d400d2100801c006041152540070042d0540300045804c80060145840703410056110041d0840d80c003a540c02107811207220b145240d48102002d20744500361803688815240402c0002588d1031200d640048224481820754200554041c02d00 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 973980863 1250 973979613 973979621
    0x1523090103210203071a0a09080315010e01030903081909020907111504030c0b04030212070819051c02030a14090318030f030703110c100f0801050409110d03021f 71
    0x26002220320500144142d1049131a84510300004001c02030300c08a03054a4801166050b07405034850070001030010907074485204030b80044030140c0b8440f03a11180c3d003042d9613028461419031042820180000b4030141c0c0c0282030034000424802a00400d41c603d244101140d0304029100354024000d02d82c0360070080001808a0004c0c0c0910103039104101c1d841a240b07e100a04078416a01980d030810b040302c2554a8058410018100340e0441c42141e400b03901000c0400001c0140724426841260750b18400090741000380c1c402d000ca2824441c0c10f100120010514107440f00c4d01c2d000e000700041c0c0c1c9a9800310700d0002860b403a005c0c1e0a644500300100f012642001004141c2000d240003413004c0301c05410205a503803118000044215081805840d0000707004815100d5108240b40079540c51850700408600103441208011000810640350407404c5e41d080803205004d85002d4500784810314443c3c440002c00388440328100d0060b0000241c050905100b4046501c10b030242c2d03480707188800c41d00c900c040c0c054 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 973982113 1250 973980863 973980893
    0x6031c08011a0a080105040509010f110c0601080d0c240501060302040e0f01060f0f1106090d08010b090f010507030e09011502070608040528061e0605041523090103 72
    0x1070740d01d00d00c2e4903a401035518140e4003008030954800d201030782400e0510025080c0030780407403259921441820440803141c01000b0703000802180c140e4680b06104010b81c9015010790040744186c011100342188a0b522909519210740c20144985440b802c01031041c003076030a070031304c001da03500c0c40c02001182196154008108450300c3d143c08070100e0300d582c0040b84005100380b1881011a0030385580b40e0300c5a000e20b132081030800c81410803070050004844658240101150010380542014a600104542040201d0302410b0341c250000d041c0000c000114519140c41c4180e141030200110f184000c15124015400e40c0c000c010740155a556520100d401c0e05840a45412025001d844004610984580e035041e10a5410200901401c0c0d1301030099251901503045203a20000340c07030a02e401040141c029191000c2c1c000c0307540079160003500304410464906400183c400c6050040c031380940924409114290f516941000c410300500c200c03e0002d01c20962820783d080384111000000f80f0030810820444c03 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 973983363 1250 973982113 973982129
    0xc03031f090b0d02011407050328090303020a0b0c09060a2a030909090f1a071701060f0809190c08010b0406031509081b0c030d030203070e0906031c0801 67
    0x8035480340001402e4445100742070b50044407501085025604c174410210b883c007080803046203081e000303880341030031640441c105082c800c040703803c104221154101d14069500852a1945c1201e08554000351110a803410140c48140a000480d11502020301120103114008150a40d11104580d020f0724a041d0003040205811013540715151111400703c1c0c92031a80c1e89039480c010b05d107041c003251100605402900781c40f008200d0310700c403000441c0d90421101000070240c40c000c09280c13040009000c0044100c000e1484c6906000403c4000c0c0c20082c03201c2800da050038851740c59524248017600d40070701010100c010541080865050201c018410400d0718006402800b22408400c20300054480600c80180b8500d00c003000650010510b031301951000c3e03c50200c5c030385811a8000c80c809111414032201065800008001d06945001c020145900103c1d040070b60039031520810140200181c1801c0c80c1c050729061002a501e035034180664000c0e2914800600b0400d1002c0c41c004118800901031061 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 973984613 1250 973983363 973983421
    0x408040909110942010c0807051e010605030307020117070309050319081303020316030302040b190806030c10031806021b16140d0819020d030c08101403030c0303 71
    0x501904913040c060380391641c4480421011080c1c40111103905105500b550b01c5c0030148007000004400344820381005d4040c180c54a00300c9461342d001801c65410b580704503c6036004100b281c0c0141d03003003141c10240d888202c070f100d41c8030f6840c05010307000762084c0300c4001d205000008103884000301454080d6403040c540d5442c015240d48035a8a00311040b8180e40103800b690042c454403e141149a04110a0300c1c840d143c09802c0c02d598841c10820364015200d003070304060922a1780c03031165a100740c031680e10080c01c81c0203024040c0e012001c106507059101d560020142c440c001c0c000a446108120030711980c0c000340c21552040c250001c0303844a011030111740c02d40d0144060710700d0281da58490303030000d66100340c88903100c131440102000004840c3c9801110a50010300a1011000300c1c020700d04405009d5070090f0140700e80045004048480201d00c0b00705001101041c03100c0707400a4207200041da94944805040400400006032840c09400c51102a602c0000208506603002d09101100d8001c0751038524 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 973985863 1250 973984613 973984681
    0xb07020d02070302030604060e120c07060e19030210141909050d170a030603051b03060c1806030402030111030907060f030608190309051c020f0904080409091109 71
    0x242c07600300074030010b5031642c0440041004242c2c03592246079120380c275404413110a4040c3d510300366150040b0191801e16044100100704d041e030090000b21040ba401c0398000c041145080c581c182150403804080e0250f0201031740449400c0c054a1466154452010303c0740d01c408054451081c900d08040000c400198506000141800c0c58070b000300f07040341c1c00f00c0c51210016a030040651190800c012410815840e09000000b00e44140114841d01f8050520003000748400b600b07141c0740c00c0c0c014000c030011510800040011440ba001d5444000408886040d52034440b400043d014090b00b00256058403800010700c2001d410010701c030001c450340da07151340320060160308042d0b003210560310807001c1542021030310302c040c950b944000383c0e112442400e050f0062520741c0e01154601100895508071202203100380c2c000c0d1314000845400321201143c8144451400d99a0050300340903d03c00c041e4015200d0000c6002c01c0660f44207542040c0e0302802c512510310f4603002c3c030b40405c01e841507424541c06800c0140c1c = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 973987113 1250 973985863 973985867
    0x60e12030903070305030405011107140616051c11161203020a0e010f12021308061302010c0f0312051e060901030c05220204060f02151608061207030b07020d 69
    0x40da104000c4000610306180302030b242501d40da413000b4002c4919541c1d4103240d0007520f001d20043c0400d01d0240780036040e915515903d052501e080504101d00c030300d84101240c1041e40e4484219400f464148030505401c10009090502801d424140d0542d4144003180700d844c0d0900d00f104407240140580510000529010400c0e0704a202d00d4582400042c00c1c030455018070b50044800c12030046240c50045016072901e0b580e0402c0f600301034601807900f1402601000300c1982044641d40010a0492a6864054650020300501c00f558030007400045007008103428140101d41404030074000c820140054034100e032070303032800d894041c11355200000c0000109180d400c14920380f50507280c0c860260742c4c0e482e0a0400300070702c40e99150307007401d07420300d60072002c032103a000d50700162006040a880b0722400805400c8080e0078070420342c1040044e1b007400000c210100c850142e58400002c00f50400001ca91034090200e03101a0382180c04007000d01c1402c2c400010410b440040502c9500300c1d40c01c0c0c4085070001c85003 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 973988363 1250 973987113 973987117
    0x60f12120305012114150601030c0216170a050a080d0507110a0b15030708011413080f09060d150f0f0308040e060d05060702030706050c0910030b0a05030307060e12 72
    0x280303100e01041c0144200c00b42061300d40300d101d814001c0b0700749403916118a0089180021260715178484024820070b00240d541c25004a5640d400c06002614114403a0164881100054131900c211031281c4504140440703c180100c00e28180c100040e141c1958450416607150703488032880c0d2441a250600041c5c00d02d1044110404108150b070185c4044802e40d1110405c4100c0901407041140040303001d150642c0d02084024000c150303150001c9910425070701142c940d240b0081c0001c44080000501000041c45001258620055003500c1911900c40c680403c40c0790046600d05090640303454400116196240d102808032211361001c0e44003952074030050300881c0c2c254031008001400600040c060b00407250802c0e540058090001000c40c844c0741c0328240342080540d00350015070000128a010b00c0f100780076041d03006c00c400c4207080c640881030f40410010201180b4040130565140700940d020341d540703101d80c40103050081c21241c1b10032544c240240240074a00c241c604510072070322901d24035000002 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 973989613 1250 973988363 973988369
    0x90207050601211101050904060801140f060913080d0e0f0601080c030d0305130f0828080c0d090b011806092d06120b0f13021c06060f1212030501 64
    0x200600f283d80701a0b40c3c0b54421644681c445041c0401800202c0032521644221001844110004103247c28600c0c100303512000050099410752800000300091516a10031154204011980e015200901030402c06d01c207000d4000484c190506000d00381c056907400003a0001001d81a100b620040c0c0d980301c85e0959030b10101499160140c00c890000145640254445a4032204000d401d174451142990f80e8a98180d10341d608440e10840461090111000c58240340d01e1081003100c1c201a6a01d5080040c088220080c14203200c0080041c2c070081039242c1c1d030841c401855120382400300658440c02c107000003910003200410241e181070384c0080c00b15018091080d40580c00c1780c03088a0b070400c1e041c0c503000c0321184a00c05441c0783d807174000008a01003100f03050305140e030080410400a050440644aa0729030140412200b146c41d0546400940e42d243c01080c65800280034580d1a03c0103843c003c005081c0c554040d20b07003285030000010b10100c5241c924205188241d40aa8103051288026400c58400780 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 973990863 1250 973989613 973989659
    0x30c0e010c02090a020d0b030f072606010e04050c19060210051b030601021c05031803090307091a0a1701060b1804020d09080a0e0a050a030206071e0c090207050601 72
    0x440820f03604d090325402010103511455000c0b40141008000c60300c1d119400c0210042540500c01c00c1005501e0b508c80c2c10341c0d41600c4a07400c0b1300010380028081d6a14418050201c41c032040f10046002c100040044c441030400280140d820303546a10712581c00308000e88107280140c01541e005505000417403140c0d40c481c910102584603200c6881c0320040301a00010b0985040d40701d1409410700018803143c1043c0180c101d41e98480e900d183c0103100380c1d10100580c50041c40c1d50300a101072940f6580128403002074075080c0340300169580001c02d0420401c02a945215040b40382444041480024241d40c2c000b00108034000b4007030369a40301c445440a01c20405e0509140680e03038441e03103543c82c0540042600e040b4054000c146640c05441c0d00d4100c1c0d001000240204080c100540890304200507001c00400084414144051443e000b1824a20034a10000e14000d0804403990071000004641c450003500000d5205800e5140c0740050025842000700303881c41d02c2001d0001030a40d00644030007107020014 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 973992113 1250 973990863 973990879
    0xe0601210f141515040c0c081603093309030327091a0307050102030406020322030503040b071b06050406050d1d0109140102071a0a0603080a030c0e010c02 68
    0x40d403640721408040361802c901c80d000da11403100e10049400d900c107001d01c88000c114400140c5810401044035545100030090003904c03080ea0000c00e2084090300c084081d0501c903203410061070b00e811103035201103800a60640e010000d0489100c1c0700048002400d82d001303051180801d40c0300300140d80030010391000800182521510802c60920300c4d0300070042082018015a0150f2600300b85070079076600c4004100003c413203c1035441c0b0352804111807801080c080c0065450720b070800000946a101daa003004040400620030500201d4408164500554010055030340b80e54407105004556480440b05884450b03511031a0400c07000b0b22058281141d044d0b80310146000d00c1d24400756130075000141e0311000150364442c1da0001b40543c0d0301c5100100078240000420300c080d031508404000140d943d00c2d0300381c0c0c030600c241400544441500b241120308010030048035036074261410041c0c480381d00b0090204c42c0201f038980c1000e8058000c409250110f8a0b02e0001500380d00c0110740c0c107034603400d02075400b000da = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 973993363 1250 973992113 973992143
    0x110c04140417071208190c05040911041e1a0c03370206060a140a0504021c090f021305060102060f1e0c120c1612050d0e060121 56
    0x510000300b8511422070944030300f82400f07500d40c005003203000c100c41c0010890340d07810440464581c0c1400c0c910482801410091405401e400401a008074000c098400fa51203000b54044d0070b5101c1514006c2903d403039145800098414046406100b1b0311130f0411400e600740d448080c0154240546140c4d21a03103000b5828203110302d014090b002000040c1d1080e01100414942030700d8002c040c00030705103026400400c014103084043c06401042580007034202802c000202c0c00f00e0741c0300380d9036008580e001c4030003586400541025110380341c003c51200c6141490090490100719264416141c0c10b13008503000810045804c0105064841c125040c03401a04000c00084801c0c100d454682c0d042061400ba68001070101c20300100583c5042c0d071600308449011038040700c48401100660780c880d04201c1030500303050185464114001000030018074044c50907034404080ca100c1e80654904680382001170003028960b412090300e41e40d080c0181601c0103c1c05a40b00c580540f4001030048156001c103000c0d04004c9 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 973994613 1250 973993363 973993373
    0x1e0d020a021915020606090c070506010b0901020f060907060e1215040503040f090b1f080103030804030212040b0a0207061803140f121222141c110c041404 68
    0xb030307152600e00400740003000124070205150503000c84624590010803503810321404002504000820b001b2600e0800c000c00c1c4001600496480d0460f007611444645904042c40180d0400454150030303281031140404001c40d0020004800f0100d500fa40c5500310b112900794188010014440c001030f5a80d449400900700c840c0c90f000c5040d6002e4003c0041e02e0030b1540b00d803401c0981d000180d12001c46241c841d854200649840300b10209400084400c07910a51000480134260300414800a814480d1580c0042c0a141c02440300c1d61400203420001a030303503a1610710010254001c240e6400044c4620480458424001c0306208075680003185000240ca1550303403400700326000c00d28408a10f00502102d500d03103c0c8104900e84403155848880c5840301101e046041540100501d6107020b02031507100708144040200d803401c01c598014481515002c0c040840301d2400703158440444801c0c60408545561942c4103805031071115558040e15803502d2a10100010785410807140c070400d103151000f14001031 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 973995863 1250 973994613 973994629
    0xf010e0618070e0a0e0108010f050a06150f1b081c110f1c020409020403050f070b091219030f1d15030402150f070b0c031501030b0a0806091e0d020a02 66
    0x16030084c1308031859a124000142508400e03031200d510b1f0ba456142c514a03404880c01500da012000200c00c0007854a41002e60200075003000912051002ca020314002507480f03483d02040c0b248804210366028a070601e404c0340d40f64000200d00100841485403103058000c280a250920700c0151100303810001e07012445032655119500310090000900782a0410390190b0024000400507030381c00584941c5503003007890500e054101d0308040d030b0700584001d1021080110644950354015503d0a5800d651651010300c2c0c00c000090900101030501c8044041680c42488982d07009030341d680d080444800440c011076a600040c440c0717544114034034507174003121610402443d8086d00041c00c0204d0312500d07280443e8a540407042c3e2160340c200c00160031040c021313084a07094124914400c410b245240c1954441c8071392501040c034904058580f00e80e00c0140d990010792501905015003550b8090401d10b141325078171032031901d030900f440c842401c000907011408203a20501c0c801540250102d0280d40c1d08101c829 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 973997113 1250 973995863 973995887
    0x706080702011d072c1b1c0506040b010c1713150c11270a113402060a030b240306010905091603050901020906030f010e061807 56
    0x40d075880914403085040c80108404010400380a003180c181451180c14481c4170140c000100d12180d4000501d540e48591a0181c0c014180010011845141c00a01c0711504c9107240c145080d402c10b0030354000040d5240c0c0120b00a4204030390402400440c0401540c110102600c0070300001d0380c03480c0010268101d40020036a1021400b098548161141c010f05280c030581d03c0b0400005501102e0f4908101424400312140502281d001da20110f0403010000c50348841c108a00049450720003091000030541c0101d0301c8654115583d641700c01c01c110347d9000c110780007501600408400c140b0489002101c0d0101d00304903401070161403401c001a02d05901610300d0320f28aa0708210840d0000d6040c0254000700300154403000350040d40da08208000400000b0f031508214414070880313040c4262888001c04400745080c1351700b008034940e6140018140207002d1842502d8103c107001007003089180300c21007028142c1d2100c15440b48603403613920901000c80d1000740d071410a05030610100300114010360504241c = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 973998363 1250 973997113 973997117
    0x4060b09010e13150917030103031101111c0e030f0903070b160b3c0a060602100b0a030b10050a1706060d14010f0e010b06160303020901110d08160f0207060807 70
    0x104d042c0d07990351416943d41c18134006e00710034808401841055400b82c072000e584641000280210310b16007203c1140c0d0300c6801990105251802d890f1140c000540d0024124a250002580d488601c00480310815034000c800c82482400768010102d40c1880ba007081e2a994402d2000d290388800d4141c0d5000342d086000713030110401c0100d02045000c40381040341000c4007041d07842c04441d540c09a0700c2c03050300a03000c05003100850600301234003400760540c0020b403400d07002600740c0c010946104620204581d801d581c0c101504400342c40c0f0406c885055984070f100119101030741c005286c6590f0760b60191081c0c40d404003410041d0000b5001c100240783c00514860403030f0080e121142c82014a1140908440d0041c040703081c4152150799119040c0c00a01c500c110628007584d00d240307080c1041002400d24012124010700b030550100710303041182d02c55881e9100902c8048201c8454003000074000e040c0c80021911421f40440b43d0147c01030051003800320216150440d0000e042c5581028002c1e03e03014001048802 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 973999613 1250 973998363 973998371
    0x40f0c05370e181e010e070c030f090e0411120303010f140114070605060108061005030406050c070f031e09032301020c0106030f020a060f020d0e01030f0504060b09010e1315 76
    0x2035128440d03d12402012514410054800d0440c1d0030622240142e11070600c0c00c20000c100410160041e80c0c2ca60711a515240c000503510b240c19040d41c4502031600402c903940907200412041142c1514002c8130100103ea0f11121030002e0a0855608e00c0240038800c074200c130b084010031070f400d100301c82c1d848100c00c1418110b41e060503c1c1c0c540c941e16004003505688076a1100d0600c215942c1000d05035030001004d907481524002100740203002488090401000c1a070f031140010f04401c90f01c000d0342c2c0e8159100d00001c140e00800c1c14020004014541300c1c0d0f10b120b155140b4203810502506a035003c030390348031130f12902040d10141071010f820010001001135540801035150000000e1180c80b001d980b1130482140010b0b11401407150004042c4c00180902038508000c9402540020303070b0b112200755518082248a0400004030040c003a4010f150740494100410700040040c1900405985d8100f074a000800c0d030b0384c0f0000c5210481c0c4c240c1d40104900d43e0329201401040d1414110050855078610105d = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 974000863 1250 973999613 973999639
    0x9030708034311040b030d0c0b06030c060a0f020723120a17041d040c030f05030d050103060605040c0f2102090910050127050f040f0c05370e 62
    0xb0301da1030104000303c54001c20000c3d0384881c0e181a104c0d20600354004e40c018145a050703940d028101d066110800341c48042240001011070341d007000a0a80740c00003078140c03510345035031100181c03c1144507180c174005805011030104051055080704204941e0141c840410700c2020000d0140901541d10420000d00880d025440486c01c26a003948417018461304031079030f8500d0042800080c61003041c490050401d08001d1101042e0005c04900569412828400c84800d0390b2410030700d144680c06070700c01414240000081808042d0b409981100e805139003c2c0000c1e11548403c681c4180130000c0c0c1408241d416080a020020025001c10040061030340180703401501030011303400c071104031f90b1402c0b00e11400c04c0620855a00440c01003c0c003d000010000070707603803100d4070b2402c0180350040c5c9000740f04180742140c1036541c507085881c0e41c0032508410421800b500100a0660740449254410f007010005a810003112100c0003108012060014003a407900190040347d07104c40310760340d00713074804034080c40a = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 974002113 1250 974000863 974000977
    0xf170910020715240e01030b04080c1f050123010f0807110a050607030b060301080316170c07030b0601020f1b0117100e1501050702040e010e0109080903070803 70
    0x13042d04203016140d003d082550080310341c68800140d0080c0c0c0300c2803243c80041000996405e5a0358000e0340c030802060710b41c0e40b04400c081c60401c10803d50300c06e00003190b409010700d916a91003d0f060f0b07111082504410345030b40e01c0d50203d80c04c0c1078501f240062111400b844030180301b1400b142e041017192502e40d14400154150a00c2e0a00810b02621590884428003da042c0c06114450b00c0302d1064900700d00750f615022009890b030241c2d08044480c88074400c0d5100c00c00000b202d40c0c1c00201d9a081c80e583c1c0700d2260800c42c990715000c60004843c0c844948011504540c0000740c51002002d090b0700515400300320b200121036403424640050f05000306009401d403c81c1c0000e118902c103401e000d62100e003161600c40c00040700000a42503004140c80e400d1007071a2a6403107800c40f91000d0b0103a0b80464010000c2000340d0041c60450612040d0354030b0a83e4280030464800020700c41c90004508851031a81c40d03020090710b078400c9501c9050326600036441f116a424403050411500c0d1082d50701904040044080 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 974003363 1250 974002113 974002121
    0x1202010e0d0815030c1815040617011410030303090f120f0311040f05010507020a18020c160819030c05060c190806090a02070519030f170910020715 65
    0x1c0440403400d0b110402244a4540d5610b000307140c01140100000c4807040f01044590245038484403400c0c105100040300b1b9901010302c80c139040800341081001d61b55840c8164107400d00316a80c1200b950a02620307450150441c00c45a004201c2c07415420301c050300d5a50142c0083c070307001c102102c0c1d2225146c1800c0100e0300003100c0711807001007a04c5a000801d4080c00041c1112261544c01c8a140c2c0240410f0244a485020071000d80320300f030800582e00c1202d03000081321154140e2100d0028505203224446202803900074110803e824802c644814106012a0000000358010420740307034403aa0800300618248500107211a02070b00713003003104400300d80f60103080c60030032039001e802d00c0740010b8a00d0340381c0c01158034910421840c2c03070320f00158200000055034842020704030b10031a50300800d0742c8051282c1406603150103810085200c0c6500a9403502030004150460300002164a2141109003c0407980b00c01c1c0c400c0d08074a0242c440d040860451100a4101e660143e83d0440e510703d02d503e044c1c0440c81 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 974004613 1250 974003363 974003383
    0x14030a06050319050a03030e10090503090f010e03060615071208150612010b031b040e0105040506060c06070305070504030209070c12030b06090d17030408031006050f03041202010e 79
    0x40392040c10501407525100400c0900c81014015050380740214501056000801d58149008a540d4450011091820216a26860b0214a04010081003010000080c4100402501c0d920740c1e41200b400192140900102180e0300b68100b040007a0709843c04a0a00c45a00550303030000381400d1042c2c4500032285400281400401c1040c001d0000c841d28000b83c2c092050000c407010b92425030095529080d1401c10712550840342000b10104917084406080c0300304101c1c20300c1d40184c840b039071070100c0c812004007841503e00a603d00070216400d400c008041312030603103030031000f4919900c2d885c10032401080d0003045042044400d1102000580d16007000714012105603840318000b44181c14012911030191a082041c9440c002e2120101d86031002500d003406001c88480d1603031a041d0403c14202c0580001a00c50718a00004003c108603640e03000e580200748080040c201d240c0c40300b101f03643e1031060360080214520203000240001300c91340380c2d40b00d005141348000300d0712061100700c403071078807000c2e01d = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 974005863 1250 974004613 974004631
    0x30f03040c08060a0b0105070b180a08030a050a0606080106050d0209150325020a1106070512210606040302040e010b131d2803020106051c210503011202011403 70
    0x710041102039010030600340c10404641c001c00c0301103025400a4030521907443d004020043c00030025200450075a80c0240c4600c0d00d009840c02030a45103025005c0703500032124828251301d0500440c400d40c0342846070070300b60742c1562250102a424814240c0329604030060042c4140e800308100c0d232140d11003142007440140305800301030b1281407080200503009040780c02901d4948520303500c0503440f540002d6142e11030342c10501e40c040d80d40d6200e000c640e292041380c1001d0202c0c4074048440010080d103100900302800180c1c008a5407800c0341800c0c4000074030035111194012424807051000d4038296006120080791a000045c01040d2032010a80480000707907445055a40ca24005123070181980e4171000050841016221407512445600340070310398420441c4400b201c0300c00c4601018001d6100c20041e002c010103904014071003000d25902e0b10768480045071104000800442c1100a02e0800c0122039039a0302e4482c1941e00307102c0c1d4804e04104a0301c0984c10480b0803c070b1000040104801980208004 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 974007113 1250 974005863 974005883
    0x51c090b04020103050a140630062e0b0c010b040e01020414091003120c0611091f02060103080a03060f1205010c0f0806041d0f0616090f090509030f0304 67
    0x3400094115440205039241d01400c10b001401d40b04008041035502000032103010074561010b4000403c800e910481905003100820032800c1c0c40d1500251092242d4bc54030100400c4071403074001d1800400c1c001241c180e401c10482c40502c01038100070040d041c051114000050200d1007100040c044c0c50000c00c0820240c0d40c000ba042c804800c894694064045007605c006003d4204840d00500714801888003a00e030f42080c060480c41c1a02c00c6204100550b004003040c4100070a2940e88103c0f640314086091051070003106118201c00170000ca040c0010060700608007507031031911350701103030f0348607e011004040c0e46150100e440c1a1000b108005000c074000c58600d91425890841d08407040d54440100340907580029007c0c1e80d9106601c954041d501742c1d40844c240010b41002d40d41c0414544661049000b042e400c1014207200095a51061410081c450031040c0f02e042c00780d9141c01d0b2401030b050107600200c020f011043c226001150000c5607107084038545001d14071840780540043d83c1c2252a058a = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 974008363 1250 974007113 974007121
    0xc0f240e0708031215010c0c030b01050405100302010c0f06060b04091b0207082a18071e050708070c050d14070f0608040b040c050301152d06051c090b 66
    0x204501d2024004000056103024000d0200b190781401c02040815040e42420345d5a001d41d1160303d10080503940401440d84a03510380c80d18012881090003018060f600e4880040c1e000320304860f10108903501030712000c080b1140c07600c90b40f004000c0d082041d01c5003038903018001110f07840100144020701c122a0001001d0058000000c814549424040308544c090b20050000c01c001040780d200c20303480710f01c2205c10500b120200130704881c0c0000c2102d5102403d8504042118402c054403441070707034143d442010802c010540d01c6213603084021103400080041c0400c4000030240001132011600600400121594420000d41a05007580c8121615810046140c4175540c0c00c01c2444046e248000d0302d011004d040aa000304003050003400580000c01c1000801c0521015078251400340c14045c0c024092050a5610782140450601c100320708000103809058240c4403249483c0e443c5030b1075684500000d4580b040031a1135401010103424040b88000000008111300e111341c1025602c1600c0007041490 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 974009613 1250 974008363 974008391
    0x181b05010e04020c120703110102040605030609063a020910031b050907140733090209070e030f0a03020a03110a0c21080f280c0f24 58
    0x7481401031400b550060159044046010034250070568100070045c1d103d900f90705040f600c0c0c1c0c03c1c0b141c50341515440014003203452980710340250301c1080306640d00981511018240104400d0140b81c10820b498081e4a291840c264220904d41c4102101d40c6034406001c26000113030348003000c0d1585461020900c0701042006040a00d41c0000360800301e0014282d45441c1c08655003a0006000f0780c200074528008040c035140304400d640041d42c010041c404400081c0304015811002d000304541880742c0080c2c0ba4003203201e60301486078115805002e414154580b0072083e1920000084a02c3e0315001d10341003846104410000141c940d070103640200502d603410300780903140181840d02d1040981004c2c8003030003c40d429280e00422030f284030b07410446000c0d20202084000006072801004500e000401d0040e40000c1d0014020740d2004055400c0600000f8411000003102c2e4201c1c42c01180d0700303d140d0030200d8550180c40c1d800d64054541d415114170300300000d0320000803d503d035601e51a0396079080a500c0d0 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 974010863 1250 974009613 974009627
    0x19062306030702070506030c070b0a091b18020c0f0d02011e0e0a0308070201111606060915230d050610080f2d01140405010528181b0501 60
    0x88025191145941007141c00251903405074044c090140d40c0010208e00a0740344801101c036019042401a07949082200a80010304003001c3c01303460441c103580740d5003030381054010385100701c90140520055400f1040b00702d001941141c02c2941c42e03801000040c20501c4028042c41c0042d80036940001448030015604400c0080626140c2d084240b501c1840403c42030002002d078070300c035090308103020180d07146030b4201d01600d2000c0640c15410004a0010b1750084402b211614980c03049001740206a10340244108a0380501c9500792003e80403102003051504e41194481143e03d00298441d002a814004c904c4c040000c800c1150700390702800802c030404080c840960301411125014051940118015a07036450a0070303280c41c201c1e000082101244900ca048003980034540300000d0128100101b0428101c4504035010b54040d402d007070001da01c0b0010000c0e000c0c461540b9042c203501c000892031780d0b038000f44194142d841070701e140416810041a08101006200220002004000c60034500010a01c07 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 974012113 1250 974010863 974010929
    0x1306050706060e0105060406050d090c060f091e170304051503160c1203020d150906061803050703031116030803240d02150d020c01052d0a051906 64
    0x791640c00014417690380c2c1e001c1260200da405d850910340703400300c61541c00e0061440810080c205105a28000382c06071304a80c0b80814005142c5500008655030300410740541c04035a50302c552548421424810060401780400c00300441c4e03400c8900f89500c0d1404a0900c08030000d404080030008030410111000c070958481c04106070340b40240710000c4039602c0c1d00101500071070301c1050540129040c0b0320020703544e019000f800c1c0f14203941a0034583e143c99140092160380120700004020810514401400e0411403089070703400300040030304900d903403000c0701c20701e180100030480c90249010994210020401d4a400782d400303108103e5581c100380c4801071401c12101082c0c00404c000032011a616543c00030640c0440e034042e00c6003410388203003801150140c8910403003080094030201d008403d060f0b0541c17006202d106508507003c1002b0b160081c030427401160140ca151084403681c0080c04010241e00000d0304224006d48200481c00c0c00a0fa0303d003130300c0d01030b0404001c0c21a182a030184405060358a4812 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 974013363 1250 974012113 974012129
    0x1020d0b0a120c051c02131d06040819030e03070c171209040506010c050a06270f110a050402040b1e0403020a030b150402030a150501080c0d090206130605070606 71
    0x490b2400e81d140b0000741d496103c0c2a00c954410f4070710881c0328505428018440d503008002d400014a901c40407802050704030b551240700078415034020b00510001500742c0c0074540000949040c032240000e502c401d0f4280180362410988c95040b2500480700800c00703040c81c1d52150028590050400300018051718010503149159803100305105140f0640508503043c00d030b03090354081a2690f603400141c0c5c41329551280103103140b0850400105000303203640985181c0b000d21103c80403d11911110300417001012502030000c000c02030420b0000748c40349d5000d5510110180c01815403542d64400541285c02551000e106e0b440005035504000e80e10310491050b00722500380c00d80c1018150f401140664500c1d0000170560481a008103109015403501140030040003002556a481c03e140b9040142054000c50b1070b2b02c2d0380188000c1001d41c040c914070380c480d850003c5901c0c1408580c82600c805801d60100990300900c2c100300c07901116040303007200d20190031161900c2c0c0e0303122502d00d86801102c80984c00b600c0 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 974014613 1250 974013363 974013389
    0x20301110a0504052b0c0e06010c1203050604060e24041122030f1a070c03270b03010e0105101b030e1f11011a030a020d0c0801020d0b0a 60
    0x70003a03801c241070f9000e850307007501d030480b136060700c000e80d2503001825800484551403001c0c030000400c408154000280c4040b603400c0d02c240d864080055480c404c180200410142021002d1060544654441c0354005c03401032010034404d1780c91108010000060710780c0460b80314484085a411010440c1514500806803010004000c5006009001d40a0b01988070204030009001081803030400e8043c401664001502205c514054075100700250400503120300714652502c00103001e940907004a268441c1c1540b0b0b11a0300f42e0503400e1020000c82c1c01e81c82d11642041c11740c03022038807656000281d8040c0030500907802c0340b941450304004900c64241d0203801004019001807a4018071070000c101c40341c1d0316051041508049200242002c5013508030f0540c40c88403c805080e841d40c2c00540003540da0b509100800c036901042040354940c81d81c0e801d009800d0344c419004a00103042070200b1076101030240d42c43d41043c0362070b0781115003a64071070b4000807078568071810100711515040240380004c101e000b00e100 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 974015863 1250 974014613 974014627
    0x71703090714060328060801020a0306060305060108180a1a01060e03060705071b05030307060b0901060e06070b07140d091208010303021f02251a010f0e04020316080a02030111 77
    0x501c00d00c40280a600c41d1764140407090081096802403444222000340188921600c503503030035000b50003510703060700000d0070034000080250280c4682402402c040e51400c400b540c0d030403040410308401d408604042e1040890300b1020684a204c00b40076442c040380c40c80721340e5161220081c049880441c07014482e82210041c8051a03030010107c4044950011500e4907980303400c0345078541c14200f82c0c001a050300001905000300040350380b141400243c2124101d420380d80ba40e404884071107100c080103400c00300800104004c1106080300e0b9030304c04110f24040c06800307200c81d039084180c0c000c2c004142c2111b445801040410244a4696803040c00500d080d407565803640c1c40084d50760403103260152000405881d4800d1034101901101c0f0422495000004419240740d01070201012600c41502d000c0140440014444c40141000f412100801240180750703041c00100140c2a8000d8000ca07814172401c00303400b1542069241202c010017141c0060301e141d11450041c5800d456003140101004103040103c0 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 974017113 1250 974015863 974015869
    0x30d0e040f05132901080a0c080309030309060706020412050a110607020a0905070e040608030a111203043c1202070e18011d16060215040b0c071703090714 68
    0xf000700c60341c20001000714480605400c5609502c1600908010034010300045034442c1c0c0010f4026500d4482d00408850075641c00c1c2080e16406524100307a41a002080310710000d04d80800030340754203402540010725150792003102d01d440180300703034048545401a40104041c040e858001003110380d400d95010303140401c2540042c40c0c0828a0289058603541d610101380418850040701e0b030750140180080183d652110710659907a040031440d0000901e03146030f00b0682003400308401082085103840720341180c403103540c0e45185000c0010402c404940c0c035059410750342c814084042c1c00342022600058000c4060034081452004030b000034040d540b1442d803c10005909521031584001d5455861882414502010323014000f0641c1c00426042c007444042d480c16404143c000d0b0070f1200c64081e6031441d90f00c410582e295081100c4508443c14118000790201e124958202e03408107034114028500b00c80d0382e403007d0a403608442c3c40140d10601000b0840440010040c1704040d00c4180072100050b0820000 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 974018363 1250 974017113 974017141
    0x2070326041707051015090b01022103070519030c030c050903060106030b0d061b110a0b2229060301060b190509122a0f041505030d0e040f05 62
    0x3604001d002d0000b24002440300900080000d207803180f0082c030010301c80c61010982c4208030b020303520210b40b07000c034003620542c0001011401d00b0003c000c1c4a4221440304003048060704014400d02c04e0000030403511a040120382c483e1204549140c4001a00070b0f51448020100c0e03100c00005030a01c101080300ea0003ea400182040c1110007510303020070b189035258045800450070303440043c0364034201a920011201849003446040405941741032401c40111166a81c4102e6160040d103820756510220b05050a0009004460342f2046948176195070b0039a114205800d0081c0c40c3c03620410055802403c08440c4441240c0111086000340701060406010081e181300c1d0300040f491060150205c50109402102500c04408004103802c0f41060704022054841c100c6202d030888456401c008550011b0000007142ea8015002e4070740340c404481c1d0b00610000b803030010500c1030404400e40d40000c0c0c80d501044548030961013a038031a880584074400b4441980c000d105061852410a420400c035803201c028 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 974019613 1250 974018363 974018393
    0x403020c0904080405060c010203041e0804171504060b09100f140a050607051b04020a0e09040302010908130305070b0405310906020712090f06030f0e010207032604 72
    0xd080d40c1182c42c0c9142c002503c0c0700340d601041e000178000c00d0018a40d0010b40c06184118014202e0b5035a07800ca4081059900c0c0d944800144105010700040c014044000e52114a090b0b00b4002c54042200400c0140c09604080303401305c50079500d98030321824a0801d030b1030780da4000c940c80040c0c017000c03410080d44103269803181c020034050301c0014901001c0380c4d48403a030031070003803401401060381c40d609402d0594036001e906240e90b08103104c51942810904003842220300001d0282c0e40c940818560108010246002a005030300710741d250a004004100703050700071b003903031304030024085412803440c5803040c03c1c40c205911804900d6010311041001b41ca030707079020000c950030384c10060076280034600d1602c0c00c0705010f61410f240030b413404a001082007015401041c102c0c2c003400c0605c0d11080c13070749000c40c1e225001e8004d050542924440400059019030085100041580c401082c1038041c0c02c0300600326048503030150001908a640041c8003644040c01d004400c048c002c41c400c2615054541454000c0781c0300c = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 974020863 1250 974019613 974019619
    0x803040b1501090e0106181a031e060d0807030e10030c1b0c09020f041226130513020d05040b011d0f0402100c151505010509090402060a090e07020304030c09050403020c 74
    0x1390004a0310126816110107008c50141e41d40c2d4010714010701e40c0441c1c0007161140112000d04628505501060404610800c0d00400c0858980b040344d440d600c0c10341100c1411000d108541c03141240e640d031065000220104580d8000a00c01c0441100814044150100c1d450050702d81d058000030038006445042610700c0f00e440560b1b1050300a0007c04603105650021140c6a0000207035010001c1840300d0b2041e482207040360300c5081c8084050341955201c1e8040a07890341e00003100420260600c00c2c507103000c01160030310040c00c25040c0014441500c4040f607080741ea0010f48401406541d41082d0800f0b00c8040001885017140340ca2141c040c80e09801030130280c45542d0000da40c90046220758407150416500c90011740c801c040f584002ca01400c080b081d40e502e94420b034000032030954403030400c2e02c0c0c0301e1200801100d0740707444507005e00244c3e82c051010a0100b02d1000d00200d200000d85007002d005945940c0115610707031a40c20f00b00400b4000703810007454142004103101c040383d40021218100c00e012 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 974022113 1250 974020863 974020877
    0x30605040302032208011112040f02060f0a0504080f060709030b060619080402030c060c0a14100507080f010617010e071808160e0105090c03130803040b1501090e0106 73
    0x541010b0b451405003a00000001c1010040021100d03e1651150102c0396440007d0000d05c0c00d0940d001c000d40160450944514071030700000740460030b08001e001301d240c00a4202490700a5a0480340d606500ca40203d4012900005040104c458100700c069a03032031a440140815013031010008005000b1403202034400304151300403460503580d18003140ea6801103034400c2c601118140c9405030502008075000d92003405105041402400c14000300c03a07400750480081d020306807140e03840301304000034032441540324481c1905114801c1d905100e203900541041c1c03258012464030300381a10902070140c100c04100110303050808110305100301810f044d07412102c145500c5580c2c01c40f04841c603401c030b4030454030035400280340003ca00d000450305c100154000b8024880d0140c50701801c2a20030401e215050300140c002e800159802c58010145401c00740d180802070072280703d600c8100c0107400c1510180d50000115091080d43d60000100c024105428241885071a00c0d281041d401c0900c140329010602c1a4 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 974023363 1250 974022113 974022121
    0x2d0604020d06110a110c030f0c1e09040309032f090403030b0409030915110706031508100f06231215040b0403020105060d0f080f1209101802010207030605 68
    0x42c0d80000100081d20040d8589500050000415281642600704001c0c0160007100441d418041440d508610030040208001480c1d10203210100c00b00d82044010441054920352240d990494020302940c06a55405509421804c240c2304d5000c00c0d900c0aa01e004603a0307141e00c3d07400079042d003406401c48200c075800c4d580da440c3c0c1015400341c020f00d071200354000c2c5882801707410141c21050742019900b130300500d0201807218203004e48070320541c440a038449501c1032100304241c034402d03040b00c00e600003102000c96507e56101115440c1000170890fa40d070305611261001e0504a140c450704004104e1000d040807541c1c040040f511020504180b054042c120b03840041700252400c02c210f0401c0e0598a0a04405103040c0c100141c2c0020207a8081340103500b040c012504c64600041625400c0780c114451403032030086651079000541c020090015008001c3c00001400c40c0c00307040031440303008010058244810100c540c1803c582c4841510030000f4040e03600540540d070300045103001d60745c2c06880011302c1c1d11 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 974024613 1250 974023363 974023373
    0x9100f0608060f040207050601080c040c08010b0d11040602010b03150105061606150303050d150302030303010e15090a0e0c041505040f02090319030207080705090a0c03090c082d0604020d 82
    0x1011203003c1d50000d000180960400c000050054121a4060f0075564443c4402081100796406040d249000850b010014090312405200a243c8008040f80000340955905410300c1260403036404000942d41d00d0b4610902400c0c00d01c281120705070880340140c0b240d81040b0000c0c0d0b0138051041004189620740e200c1c0820818141e10016008101030300244401d03603070345002000c991000740c0741d020b0103042c2100c80d802c2942ca00c684100796a030003800b0f9419607080042403108104000d042411900381031015142d2a2280120709004400404012920703000304100c85141a200b100481c0c000c0d0b1403d00d200c2c818860015a103c1aa9421900400c51f41d4007850208064092007150a606000e4191000080c5d0240e80ca080c14880c8a5000d480c0215964a4060744503243d80c0306094001e01c0c000001080c131641580248014449400c0018204500b034072841709846d800d0b0809a519440540300e20741511000d0f12000528503000007594036420001a515204c5001900090103500300441c4082040 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 974025863 1250 974024613 974024629
    0x28020a03110f07140c0315072c01020f0705011b0507050307090608120f09040507110f0120211308130e0a02070309140310050c0909100f060806 63
    0xc004444070940700d20b03104952210607400020102d4100b0340610144020b444003184403180c200c0014003800c44031050280c0c070306842600510170303c00c00c00c02c0c005030103541e481c0c0d605614800c2c40d00000940c47d83d5421001910305841c42d868448640d01501c0c04202d240c0e0710040c1602407a8010100003403003507a910f441d07490012a90000e50381802200404141c5000c030340d00c4482241d498408640c81080ca8000c400b8440c412141c00d1a0380441c20072140550341000e401c0349411100c1c902d8445104000181c0480c109215103154465507510390041d02d003049040e02040f2036210001959a181403583c1c40131500d100031414010035030603c2c0100181841554050107012103803c549a1543e440d042c0d4a051416034050142541c2902e9402c0420300c0c2485901c03d0305c100c0390b4181c0300c0040c0a0f0034403061411591a440d00c0b03d5150bc1003000502d80d4006900613503002e4010207210549801640c0c007084001c2200030007041284000040070050b01c15a00302d03403800c44031141020131454984a000c074640d9 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 974027113 1250 974025863 974025881
    0x10203041212021b0c0f120304060509150d1a01110a06110f03070909060b0909040f05070503010e030c0d0f020706080703090c0623160602030603010b04150e28020a03 73
    0x10702414054400710500105140300d05c182c04030394420f80110b5000c20882040041401d2410f9544180411300400d0b000c5c60061900800040400d080e40486088026190340640000c1036069120084620703c40304020347d40074054800d0911500d11400311134800d039181c00000d00035000a496841c400f0107940282c084840303c96180085e80ea9a26184c140035110f001144a0b2106e80c51501c1c01c0001c8038044081983d54014008144a026450f01e450705221500142422345040c0540040000e0b2982d0034820f000c807401420001d141c8403040100d0307041c06c103202a00700c8800e01c00c45014500c6069804140c58050301c285090040e00750b12240c40880041c106880014106041c40802041a68002c0d0034034103070140c0c2450041c4031044643c02410b50b07004245007078500120f11036500c0002000c80c1c001c1c640c005800340c0005542c194100003e030a440e41100303244865100e0700024484da4482e041c129038480c0510000309003520311031841e01c02000c1c0b0341030005402c950200b48246540c0c413940192401c = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 974028363 1250 974027113 974027137
    0x3010c0507032f030a0809010c080a0902130c0c0c0e0c09060c01060b0a0305271905120d020903150c0d090f0f0302010c02071205070b03040c0f080601150201020304121202 75
    0x840102190944c0c0c0da544010305040104007100300041561205004040202aa556030420140c030b9580b43c00002c0c10b41d6460490740b02e04d01d140b202c0c0d0412820f20400381000364941d5290030709480c44c2482078002e0003030341001003881405020007150140d0601110f44154042e88c455039560225034034903004004035007201d101050001181c5020b41d40c1350308a180168804580081a510551004441c03100c003451070312526044003502058800300040d08800b0303640548251030351405032404003803040c5e20141d0708680250b80415402814142045000c02d4181c0f20303100b81c040350a1000c3c80207424040c1c081c0140e00c41351100c864104200c03080c00114407013507104a40110205052401030302800c01415481c005114114001484130030380340c0e50b0341d84c0c1078214003c1c1854a08007088403409900007801600d200034800070004401004d41a074500a0a1000140040f5414803204801d10110f0001c11411a8014400c0c4004203010101302d41c451051030610040c04500d80322004084d003d41c03407424031 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 974029613 1250 974028363 974028437
    0x4020303042705090a0f02010333060311071e110306040317131718061804060501030608060a09050f0106091a09010e0f06030a0f050a03080603010c050703 68
    0x2545142012940c10400c03042c6030a01c0703155501c0140741da9a42540c0d00c0602070500f10b42d90000594060343c41461001da00c0000707131805003d03240c0c100c500d59200300214400a9174041c010072805134144a916100003402d4280d51a02901c0d40310702480c00e0041c0107800b1703114402c02c00d4508000228807501c60100010303081e079100c0e142c5418080c101020704034502000c520014006012414081545207005600c64003020318215280c405184a8120002001c41c07031451400140007075942202820350413986000d0322110001542c00d010a9a580d98402814141800014440c00c1d80106d103030b560140490000080340006d90030581e2604680c10040f5021354a02080884c040c25150402042c0402119041c00c002c40c4003010301c0501c0d8403d21902043c0e240c51400320b00a0518400c1c1d054001c00001e04480e1a40a141c41740c0744403a40300c190403100340d0700c0034800800705038001845a602c00006c400070400141902d201074413a2145510060810881c10701c400d4104840c10a00f45031881b000d5980709c = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 974030863 1250 974029613 974029649
    0x1140d2c010c020d0f1d1210060501020111040603020c0c04020c0a0303050c0a050739062c0607031112091504050d17120a1e020f03010b030402030304 66
    0x30945005520300c40c480d5500700105028114000030302090384040c990f854106921305060210380308030b021aa0005400021404201942c0e24040d900c030048000e41c024210714070003055120100c0303601d40d1099055905001001d503582900703400b0380d01210114100541e491601904250500340c031786900d154400d20100c1c80c0d0340e404500084078032030780d842518200aa91908449003401e4050855035000040040001c1400680c03208050307422405088c8001d070074040c461510020940310901d0800004420160400086500000548402c2c80026a005c0f1580c01d490803880e0042c203d003030150090000003691010141b05114031a540c404103c19a1020802c2c140c0e4400581e00c003800c038600c07446034004114004121501290122480140f109010300420b5407415001141050203070900c0b43e0030302c0b43d81c2c6505400c55600c1d00c140400c00001a003150b40c0840340d00c0441e1000c1c20841e1031841880b039110540c031a4002c690544078040daa0581700d548034030000b46944510b40080c0b1102d2402d8441c4 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 974032113 1250 974030863 974030921
    0x60103240614010e0406032a0305190c050126061201020c0a020307061409010e0f0603160801080706080f15060403030302030402040609020a0e150d0c270501140d 71
    0xb040300d42c0e800d90f10030000c402000c04020964406002c081d0240c00a02608402c00314a11300d2071801c8c0c00750b048012009030380d81d110710341030180328641030f00903c03100b206d8a01080803d03c0c1000140c202400c00700c1c4000d40c0c416142c3c000d0440c00c0c4a00039105210350214041d42e90380000d0150a0b40d1000c0295652040c1008603500c0318281d03d422130080c404e840300440ea0600071b290143c2e010110016050a00354030320011a840c0289401c20f50704081c19001d4405e0340d40741c00d00110b00c111042025280220700d42c0d00c009000b044140e003d030303200b608800303401c2c00070f140e01a45c81600840d45001c0e4180300e4480f5545005c20b198204852903018500003000010184c164001d548602d00884042010342d5482c12140300703900c500b440b100c001500c0501d1000c000d10300004092002034081440500385545211000c040307500c60300c50309020840002041d4000c0424400459150040d10300b50f20045141600191103106419002c00d6100004544910074900ca50302c680000320341c60ba5041441010359040c = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 974033363 1250 974032113 974032139
    0x3130519050a15020a1b0206070c12050d030e0c090c0f19030c0e15360f0d0b0c032e14010305090706031e050c210601020601032406 58
    0x407901c0f0070030850140c203108907620030303120034034200c6d2611860048041c91618401e82804d5003280d10030b030240b1465011030720780c8000740080e2021100c40030300c3d17100c2428200d1a00311001001c1d010141054981c80d840d05010621b00301501081d641c1100b10b4441074128403580c000d2407051002400e010030780351403503c49049491841c90140d102009800842e40c821030700024002d0000d5040310701c0307a168034240070f1706200074030030407010004168030030f03020580341c0d010790396084c0800240006a4010750f019107046c140440201f03400b04d5641c07080040c16940e441503e00002d18000d441040440000d1007a040101000d841648510201c0d0800c80c0d20032102048030020300905400c9203840035108103550107407186e1801082c0e0580106209071414070101c01601000142609510b00313190407440078032480c0a01402030034541180d41c0c41d100b0407101e9101800300059052080802041400a141d030041950b506413500000c0b17020405607061204a2441c1c91082050949460300c4e10001d050810150 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 974034613 1250 974033363 974033383
    0x7020907020d20060f070c1a161106070305090a0b10060801120b01090209010909020d140f1311040605090f010510030b0619141b1c050313051905 64
    0x15650700e064002240148001e843c201c000d102c0d07603c8813003c6020307039004420096110f14903140c031420f00700319652440810354120b15481142d00c2c4880900031040b008981005140c10607141c801d0368070707801c15001c03070355082e002e46000289030b510f4000c215401014001000004d800407205001c0d400e06c4801c00e8140402c610503000014542c5002040901e414440e03110b5540d0450b5182010703900f80600e0000940c41300103d281481001c0c040003450441900203400595101d000004486d0200004070800090080c11680940e5401c1c0800a0030a5044104000641c1020100c3e40301205200400c004040b580c02481d409060306080000c0c107000300c80d01f203050fa40c040e82c0d0f03c0e690344141e4000ba0151010b0b40d000c254011420710691030003d8204415000c038880c2c0307142c5080b050314802c40d070751400d5020b10005164045941c2d0020340e01082041901110b5410480001c800e03402034034010090301003d0186501c41014030380c0c140038020204003081d5890484482040841e000740f4000790303070380342c446 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 974035863 1250 974034613 974034617
    0x315090f1b121506131d0a1404120c080315010f030e0d050c011508060912041a180402030a0b0103150509060603041e030c060e06060a1202010507020907020d 69
    0xd40031548019090103542d5449512814510a07441d0a040009454040c0f60681d0300b1000600110301030501051081008205c1c3c82444002c0820700403130f5020f0f0742002418000c055051004400d010f0074903100c2e03940e1180d0400a051981c08812100703c13404a405030001d08a00804414040704603070110141309060000d803100c0d00c90084040e0150305803903e030040445150405800c030802c050184001f0100c0c000001c00000300c6810150f54440f6851036a000205154400800c22610000070410308003081d80b4451541d092500d000601442440303031120b0301c030720608041521880441c421031510700c0351900074015503d03451b20200e00c100500b10318001030300107030a00c001e4580c1103400044180c1510302c05040500c09946010600495a0025000326040300d010061000741c3c444600d41d00030310078400c0c0e6800c1c0310b0b01010304110042d91803002c44004503400c85002d100035076031865042001c40e078440c440c03100c0341c1c002c500050303525000f80c0802a410000c2c01c030800454640c046500c000f581216 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 974037113 1250 974035863 974035891
    0xc0e0102010c031b050d091e020901080a080d020a110d0e04060f030c090203040206040801051f140904060b1810080f0d0f0c020418030201050406060902130504020315090f 75
    0x7681c0850a441d0000800311a08090003441070703240344118000c084070711740c200000c01c1d0100d10790b03a2030230284021480b5103048521169032504502d0005e001600408541004200c80c10041c3c81c1e40c100e9204a1620201642c2d00048180a40c0e0180e421038403c81407180075207048504004c0003901030004480300b503116a10380403000c1021851179180d103054030380106031004a41c0c10020028000d520141090303a12000c1030000241c0d42d4030900034544108a5800101c48500b4580c03000701c01410141c00100d115200c1440c3d030320464503a2440390394415003081002c2040c50320640450541816041103a0704001c150040245c048103c81c02d090031111104101c4180d4007901d004d440e01c0340705445480380007402d84000400710300c3c030504100010600003840025841c07000b054441e50030703109220440142c4d45074003c000c103110213446010010304003107005501d0181d5800241c0c480d0000b42c02094840e40d03001c404a02007031001d140356400301201412010403030501240b5999071a1007101c040300c00d201c407 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 974038363 1250 974037113 974037131
    0x801260a0b0a1b050403080307170106021c0309020906101e1e03050103150b040f050f06010807020705013e2104060801410102150402031c120c0e010201 67
    0x10121841c3c64200c00b6036519040a007160ba07441c94039440605028108040000080400844090750600829041e0000d15010140002116511000202100900d464111042c001d070b11082c0c0202c0e80040116110000200a103034240c9880c0c01d100650303640e0b00c40b080070f0351800e9500089035510a4101c40300320010409801012015a0000d0100030148003180742d0049603048035800c24541c41d40020404280d00442c0811141100c1c1e0440d409641d400d20b42043c0445941c1020070245c2003405031016240c682d0905c4000303401100b0030407803c091140b00d02c00540407041e840302800100101c4e1743d1006030308081c520300940e6540790301c0725000c4000030b0b4040c0b2805074442441260125021612030b00b515a180002d001000600f4070b1a08150031216000300c030080303250004140c005c0da00717403440b580348010410009141601036420200105006000c0c00701507540041d1040001076180001e0101c9112518116030050500c14a02000c90030700b00070540b0319170021310030072090307800382e000f04401d00b2 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 974039613 1250 974038363 974038391
    0xe01051002150705040312030f05090d05090d0533091b061606060609150201180609020102070b0408100c080622020f13150503070801260a0b0a 63
    0x150411038000740c0c0c005008201c031442d001000340e5010016090603410a91707603445800b018440c107031011000981c2c1324880703200d042140c8034a9401041a0005210080101c82c02610034807a05070329a200d40891a0b41c40c1c1004401c04c52500d98450f0088007600024840d07641020301900c1880c510522070403d0b00007040018001242c0c0d401140401104084400c603006000c101e500140a5846001944265101203119070181d803000341001d80d904055185020b500e0f540b10002543d020301164148590140c070024440400c02c8429080240040d04200c04d20051b031600c05070b0b511a00410030081400640c1c60300100e9001d03d03012400b1414456400381e0002141c1303655040324015801101e0310b0750782c142202d680901070348548620300011b1500244003107114240d0082e418004145148800c1482080504044180e040e402420b0040c11400d028030302804d500014002c2c071100c04024052102034608482c2d840300c4c1c1c03e0401043d102c40300305038248008010011a10980785a0903d40301d00c2c3c042c1 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 974040863 1250 974039613 974039629
    0x5010801050c1306050706020c0f0c1207060c1407030b070201140a0e0d0c110a0306092a1514030901050a0b0901080d0302030a1d070806130c0905062101060e0105 71
    0x4036050068040c29410994181c85c240c00841c020b0300c00e0340c1c0c02d02c030041e4032003002c22500034500c21100c000c040007034264041000d040e9042c008548280c000050403c01940c200005041c0c0581c051141803d003c005400c01e860b01040303900c0030b020380c0001020700601d04e4042d4008a02000d00e0008612180d44844a042c280c4403408294405e80e030182524104861041d0540b0b40320324440c410151703440319400300061480003240c206880d040c3c1d07160800000c0214a2004607481c90300300386928130402107007454010b044454480c08003001c4d5501d017843c2c10548160704030410400000b81c426282c3c142519403070300034a030840381011400d2500c2c00c1e4612528140d402c20f412110b42034014400c01406120840103504080c084441581e2100300b40d0041c40400c50071003000944e40c200a000340c0f80303441d4116242000c094020110529902c10000105106140c0070703042d00e040302e06c0030030700d0703200c01c004100c0003043c12840a5802d1f03d00084c0342e40c4000190071480c122404d14410065690321102088000 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 974042113 1250 974040863 974040877
    0x15050c0a210608120a0809010e0a0f08070203060a0209030c09040506131110230415050906090a030c0f06020c0d120c1202011b030e0a020114040302060d05010801050c 73
    0x1203a201e502a050880e1140400407540c90103000115a02d0f541e502101c0c6414034840d588401c00c000440c10381105a44140392641c0520030038000c2c84503601c900641c544403610f405002d4840903e1401c0001403041e00800c43d003142d940070f003c480a61400d442080003d410080a072442405155444110f615080d0147e80c00707160800c010781103a88031541c64102c8201640021649941400d0414240c1e44e00c00003a00200340c40b0751150350b02c03852f4010700410001011000c0c90076400c4240024441403d00d10304800400640d800c00a65400700e810015003503006401525501c6130b0503980210400c081a0030f100122051360200f0780c21241c403150103036203529a0354055134202031492403000100d0401d6465804460305410100740c000d516880b802c2030b040c901d66991026070745440800090100c40242c40c116403031145001c2110401c2c0c00c100c51b40340c180040000c1d042241000040d2044032000c030403a4025503004011940c0e40001007070305006070900340310301407155280000041082c007246e0229100 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 974043363 1250 974042113 974042117
    0x21f090c08031201180e031b01050105010c1a15040905010606020607090302132c06150612180f031318060b0304080a02010f090f02150f1e130315050c0a 67
    0x6130b82407540301141300410403804100d00b512070164400940d0103000903c0200707a10a0846034540755083c4190940d40180d1003070341004816043d000110b91403008a00f260707401000e9036045a180d000b00746080407101003665501a107807100d4001045015403101c4101c90564003610019030740c2c04020741d41007181d444003a41000f01d4040005228101d603006500c183d002c0c00003da00d1087c00703050140c0b80c1d4505068044103500c08000e0000d024260003048410440880e501c81c640f000212800b0345600c00030b00030010140c104d00425002d00341c1032000e03503840d0998004403901d44840000034914007e05200c0c1401c0f4004000c031044800d01a030051009441007407228618685440d5035564441e03200036080c5046540c5d6511a204a0314180110f15401d0b0284080a1551880340100302c9d02540004642808600c200b00c40c0350921200d800342c840078406000200d10304040480000268821030810740e25910002c00d0200401c00400407030102d00d21048802c026503514440800d06c03a100e042c0d45240 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 974044613 1250 974043363 974043397
    0x1c0c2102070e2814070c0c08030f0f0d060e100315020307051e16290403020705010c110d061d16030f030512010b040503010c02150f07021f090c0803 65
    0x4030265010591201801044030000742801c2e03075041e489190b403400d98000c0001448071442c401032111907da41e0f00540b502a01841c07074110000803055040c410b821740c225411501059803114580654405801042115400a00c501e0480740c0100140c034140411185602c00114840d5226042d1007680d11805141d01d0f210302d0034490040380000c048911112891040d010000d04070302c03415020f2044a811310508a00c2c003041040b6658115003c0d4010390000520803a808000200b40c4c005444001c0f81c2c0c0a09103034455001c00d041030040c1c20194600d46421283e840151410071400d5804241000c03600070b09480c0e4020a86092074841d806040b1562080a4020051020400c10498000300c54442d003802c514021005509060280090327101c0241d18502090804c42408c007030042004081080c4003802900c1101e021a043d62080070f08071103800d007001c000182c2d01500811181824200f02e9210300800d0b400351354000098103e1500407564022003910003e110721000041c3d414040d80003206003 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 974045863 1250 974044613 974044651
    0x100902030c06030405030d15051305060a150e1203030709120807150204090903090510170c030a11070f02010f0314060d0203011d010212181c0c2102070e 67
    0x20410f50000b81040d07825020130004900c44c51003600c210048080042d41c410040c902d840100f00c812806410340000340d0382414204401591504007001c00d8840364403251407901840c4608841603a904c0c0541c035000742043d00207401d2f50b10000042c3d407007400f003541c3d90300c3d43ca502c482d80b608540105a00081038040180880030010745210f015424248558800509142c0d0301c09400c0140c1d10043c00540c049000210b061091741400c00300c0440d940300906200c000004e5050050050500081c00341d05942e40200102d44039030966040101030000350158a503d50cc06030801c0844620030810403070101e1842940305000e10700900810300001c0301d00344c40c03032810383c0d0794400d03c22000b04000741207078155a2048031940d036250550444d06506030310400103803111240e00400c028941c010b4000c10503d0b600314510010b1340c03800a107401e0030f01d0408000070900384854501f5100e2401c2e000000b84018201c2080c041d003480d002c0d442020300703c0c003a82120325443c0d840ea05010048815100501c1d0100203203405 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 974047113 1250 974045863 974045869
    0xd061d030c0a1e120f17150402130f0b18010215060f0f040c09060e040204080c06071502030705030f0a0e060615041d190612020f0316090b03100902030c 67
    0x1003904440c1401000040341c000c3d625911131100441c480d002049150303c9440c4041d0740b06100340180303460800341880d039040c40800100c000080150f003e10464002402d15642064042228001c2645442c070380300c0140c13100007650759600050103108203c003c0008000d069840010b5000115046854041d40d684846060050864400301d03030075040304d4140e9202d041c5481d6441180c07e41e008c280e0701d4410050524a000303211200305030b2080d00c00d40c01400b080c040703803402203420885540c2c11101d0b19035845041c035040303020320501150350007001e00c04420011090b0700500114800d01420841c00460b68a48521034100e5240280c1c4421070381c4070340300151060900300288441d01c0c10300e004081c100b41d580d496090072415480d078400308801c520310074044e4444508035103100110361a00c0a000d401c1c01c0c030103078010f50144160064400d0b006e411150416807014171281e111a80000700710380c07020781c0303c3e42204040d01100340224002e10425100c4034010036036100c1d054165a004014110100b003040030 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 974048363 1250 974047113 974047133
    0xc0306040e0c0306090d03060e0c0406030b1507060b1302120406110f03010305070536131202010605120114190213030c03060c050f090d03030204050d061d030c0a 71
    0x11410318481c00400c9030780e581c2c0030000c1178402c0c05c0b01c02c0140041c446a200080c1a2101540001e0b20f4001d14401c5c03001001d0301406403001e5030310628000a2807044240040c1c0780400c0b410410185840010702da40c244401c0e90400c150541054038600d9240000410030707001ca03c030b510041d015408030200030070000346179078102c042d414050000d0f2505204c0074a050a48941c001c3c0c1c000c4400350311840f010030903401c109c1c1d6411240215101400205039001c06c10b000c8012001c0030160301420f40200040f24900c0c0701c079212007000d41000010401f603406941c040c0c002c00d424080c1e2813003070401500142c3c0c441014040c0806652407102802000c1d22002040103020f0315496400061940034400000d0082070b0342079a0000710f00441005241629500b807801c1200d14040c404010000d003007000e41c00100341c2c90125040004262100c2d80c4c92505418210700a011320b07081a0b50248543c10707040d0038080940c11440071410500c003000464000030601580e60b120f50150b00c41d09400c00300200010030b0108107 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 974049613 1250 974048363 974048381
    0x140607210e07091107051e0709090c0902040e062409010c021c05060a05150d080a0903060f0902120f0705012712030f0e22110d1e02030c030604 63
    0x100701c800303280e1101110020341c0c204d044025548100030035200103200d42081001c04440c80300700c446001044000c0896103604150041a4100f61a60360150402840100e40030042c090440119100ea4856605050039074041d00c1b42031141000d440e03003846a103d030404802c5206800e21071249004444401556003654290040cce138045040c1510381200c0e580d003072403141818402e0f00500003601d00015018101c41001d051000c03901c82040b1004100d0301d406804071090341e0412505615280590070468032620310b5007005106a00b400c403078003034a1810340c2201445501c2126010810503010105a07070f91003848041d480e6950002ca0104099401120201c024140d02e51003401d80d00c03041c41034403604c2800b985c40088807560b24030001e001d165000d00301c8400b0704014a401000011003400044c40139400c0c1e00041c901114052080ca4103002d190701c03540d010040c4103034040c0c45080907241d071801030408610b032085440c09100d14021b1000b00303108480c415808502441e00755112942030000807e0740d44 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 974050863 1250 974049613 974049641
    0x31c020c0402070f0308010b030f0a02090415030605090c04020f0409020306012619090b04081303050a14060c121f05300a200a0f0314060721 62
    0x600051140c4640c0010843c01e4051408800c4c19640b038074004060140c164404c0030328010a1040c8a03642052040d0b0075000703503a07a9070250301c0340f407001e0000d00208500e440c0d05c03050880c1c0744400010460f45411042c1325800000a44200003c400103000580c450000031002d2a80200404d0000c1c44880e0b000d150050307070600d8480d0600b0904c402401c0420101048040c0c60f080007410040000284080103290400d0203800b404401c0107a52050b043d8003024200170504c100102e0b0313a10075842c12509590003035410808481c10200b040c1054003000500c04c0f0070b15142e004160004000b0702080d07044070440050407001034059924009556400c1c04410340b5000490309035100024603940d05110038401d08020500c881030480000d240e02581268a641942c00e50088050000814000324200c40801d0303000c100192403404980000e12506200d0b0422130807400790040c044188143c0c5141003407040022001c0356500e031a07210341500c6000c1c1003041c03c02c040d0410015004035481e80d8200124013102c503 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 974052113 1250 974050863 974050873
    0x16020409050a0510140604020901020d0c03051317060919030804032003210606090111010209090106020a06051b040b0a032c1c140c10050406060602011a031c02 70
    0xa82d0303403d42821442c1411041681e11464041c11544d007524074541c00c0303107085808519112140c0000307511144404c4042c020322071044904000e02d070141046481b1b00b1f80102c0401002c2e900c910100345070205210501030035200b407800285120000240c1074151242140d03080d218410035607411110420014011010040440610300301c85d20f4003000c8000a2003514051526080c51600c484800381c0320402e40c188286001050180c1512000100d80d031100003882d00440420325500a507000e0300c1491103140c1c0240e6442e0002034001d03030114140792002d20400c0140084e8603100301200458034086111a0107140800041100740056001040d00e40c095040101e010086070081448410004024007034480b20a003d0f02080a014840b41c80f10180c0e200351110442815070000f03004082c3d0b802e4041401400040b000c0344200c0401220700843c616100c02d002603e00343c40c002000c0e0010f0301c20140076600f08007003624903500007205c1d42c54460003c2e004110500c0701602c6c018020400d21140e10a500071 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 974053363 1250 974052113 974052133
    0xf07121404140f041b031a03030c010204050a1401021209030118050d0909020f03130c08010c030902090c0304020f060313050a0b04030212040303020c06070c0e090a050105010504021602040905 84
    0x40041d10003041004050348548840400f400104150225250b00c00c1e4074252081c0040c03503080090f421480244d03d8000348120480c1070784120340c03040700da00c01e62510000c5000510010f05400410984600740c035034900c010358034004060b00c01480400c080c0560000303860895140b0150000d0b0004690050000c9640c00c146440d5000480701500c050b21140c0100400302240c64002611000034412103c04514140440a200f80c0c00d0102502c40700402d506482c482081c017440130142c030040e00726039000708580c0300c010310050000c00078101b0480c041d860711000100e03855090f0f02039074402c0b5006010030400701510b000b045001e6100800c8400030841c1e80d017011001c100c0030000c0e03621480c40344040c3d61050400d800c1c0030345400401d900042041c4420003003400020b502003104203090800f641c05c2d5441d0500d900c1c000d03001001d26080320003414103003030401004940c00200450740c0c41c001c4008000341c0e6201e009120a9210310400c09011303400c1c0f41c0b0b4140040c185540002c80c1c0a000e0020340d858298 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 974054613 1250 974053363 974053397
    0x303010b0a03021204030306052d0d05070812040303090e07020c090a0e0316020406080601031502070309230a41090c210609010902090d02100f140f0712 67
    0x50113540980010395284e00c00d09c0b090900003c500316812030100190501e040a6591503400d1580304600743c000d034960942d00041040400c81c0030301800424060352004a2405a6030005801600c001e40c0040c584210000c0d03005081e8017842c0c01002d04d41d010300b030509140800d0140c0d122015180b1140c1c0c075954108440c008105201400e0760700002007902c05402c406004110584600380c004601540000c4010800500f103184004507062403035101507115480341c141030340d60401551201310415109140702d11940c41c03890080d50b83da00100d403030200e4940ca1740c1e00d8407504002c0042419050a05019420940e541c4601e10051032200702603410013040312034042440850b09803124074a000c1c005c03a41c1403844485521400719850400c180b400c640c60050005000c052044c494200b10940c00a44682a80c0b12806075826280e000341c4040c0c1110850320000303107040711442e481c03030000308da402e0f005c5060004c1c0c0048400d10050050440c3c00c0c801e4544404a07420624041282400282d4180c600284 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 974055863 1250 974054613 974054647
    0x20a090e10210309080102032e1a2205090a020f1c060806091203041220210304080a05030702190f021807020703030815121605120303010b0a0302 64
    0x142e400e280900d03444000e0310303002c1d01101c010b41108a050b4010300402242c0030380d01c483c00b000c2d030304071421501c6000305000c204004402140c001065000d60020b8240059180c9c81c000c00a40c1749400344607110000024a03c0710300c91803401840e80c04007401020410207552500908004218103900d2850481c40f12542c0c00c2d20b000100b4065029504c0d04010442048140815648040c00d07001411071919000544683e51200400003000803030715043d00480903110325040312b81c810014072076441120050112956a0103910140c2044007410300c807004c1d0016038041a07034001c0f0f511410881c14815088010381e41034100a01c3c140861140c00204100c8a05018079101214090008100c5403000780c01800800003440c090b101503038180f5403d000840c0e9000800b207003113079014174102d00c0907243c00617000e80c000e107540d00e02c650005040c0460095000003140d00c0180f0701007070603600701560b40c0750b06001703a040d610000044c20340c00520040244c0c03602c880082c003800100745001498282100c44400c0c9032 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 974057113 1250 974055863 974055899
    0x1020c1909150906080304030b040602030c07050f06040209060a031104020c0c0d060e120412260d0605100806010f080a1107140105060909072603070b070f03020a090e10 74
    0x502035151081056101c0c520030a8050306044006d07500d094159101c002c2080c80107007008104e03940c0000014002c81000055412031070303104040c1c401040340003200966600f420344d826031080f601ca0000c03c0091908542290449070b000008a041142800400c0000d40040000400b00d014500c20001e00f0740c1d400c99440c070312601c03441d80080c800107001901403070401400d0440c24038000401c0244070050764414240480c40e4040c2200100d061100c061026802d0009030820b1030103004a003c40360150380350860703c2580c0d0140d40f00320138421403c8c02129005c1096515501140d50070704480e1400d03125040301980000c180d003000c10b001035855100d0702c4a034801c2100382c4207101a1022014030000038041d040d08070404a59042e03460520540c2d04c0e494400c40e00c10000008005450103000070242c4d40c01c0200c1003c804e0030742e6101e501c207060105020204891500c0058080b0380e007406218003034400d46d81ca850f65540c0f8841018100b00882c95040b00c050454400200c54950001d04500700c1c00c020204 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 974058363 1250 974057113 974057141
    0xd0b060a17070306060b090a12031e0905090906010b160c0f0e0708070903031b02030c06070804052404090e030712030f060b1206041515050301030212060601020c1909 73
    0x80e0303c0c99404c01c541103656507000445103103410098041c080c1d0303c0382e40d946d05903607000240d80c443c62610b1030300b80e842c0c448410303255030651101ca130840001a00720000004440c0b0503501030078950361f0441c1090711030409014910101c5028400c041d00600d003040c0c1c0600d00f034422007016140d01d480d9140c448044c50385900500d80c010400c0e081080c043d52080c0c40388c1e048907460610212040c2950343c040c0c4030b09400312220b4040700c2c2702d0300e40e43c047d550304000018000741c010b422141d40f54035034100700b41d00e83e03c14010980110010b1006a98003505105010018440290308501702420030007048082e1849141100c100e1000780956800f091203c2e42c0c05036248031603100060030030000d400d00c005030350240e0300c611158407040c40485107080c402c2e03040e01d0b4010000c85000648c1927044410800c0c0c0d0744c1d1604103541d1344440c0780c400748a0301d030000001d42c10b032402195940c00000603100060358a80d001c0b9000741c01a003041c034190030b985c1803152a01902c40071606144407045d0f142c09900003101d12484070b0b207032 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 974059613 1250 974058363 974058373
    0x1d010905151b0f0c180402030c10020c19030204050606030c0906030a110309060f01060c0302122808070305180a02010c06181b050d2310380d0b060a17 66
    0x2041c1781c08000d81110600c0b1412013076491500d900020b880d500341720841c90080b8519508011030f94400d00546d079500781d0051980000440000080541c480c10340401ca00030703807609010075041d1501c0c07410f0302e00c601483d9014620740b00c01e110138012603400141840300c145440d1006502c407101d440001c0c0d8420202e443c0101102d151400100d000300300706074400130500110400c0f1102007580030a00340450a285115981d4607400400b400780ca00004c80c04101005150090303080b25107a001c5856400b035075650394107002649402c0042c00b81800c079500003c4442d4400910240194051030a2520060141000040c404801d00c0d94500d204100b000480e81c0074000c441003004086081841d07409000d0540d180303c4011540e0b83c420300761507d0050111007036892190b04805a0400f00f2900b400310002c25418420540e501040d010f200c541c610010385840903544400d0142c40c6203262010321004024603034500d189a40e118025498805010b05400010607140490380c40f2018000d0201401001e0041c1 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 974060863 1250 974059613 974059633
    0xf190c170c100b1008090c0924060414041509051f08060f040314070501020a0e0420190507020603250201021303230d1d010905151b0f 59
    0x19040c201da5405000c0b416141c282491460b0b251001480124000740c100b8446540302d60240c1032614030308201d51035200b0f44000030030a900c1c55000700c020020030042101e00d0032020803400c200ca039000340d004e801c010300c80e2110341480030301c4c00703400540d90909446100024991140092011703104206c4041e5188440383e010500000c0110510500400c884800317014541080c03a0580c02000d800340c005000c00443c031031442c881d40d140000311091264004021540e4044241004c0e201c410f44008041c4581e1402101941c05541da103082070791106041601480c0061150f8030703841c0c0500ea00c20110810206204d0240180c454400075401000b610140d40a8044503803c4040204000c80242045900610000040114a01450741580c0c2e02103c02d201020100c160074140c2d108054034240740e482603900503e51550000301c03071800c0240219040c0c01e030210340801503401c40c00a10504c4d4004411580d15a00340300d080c006806100d40e0440c0105014110350365051804100c20480c0303803141c002c4034100c = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 974062113 1250 974060863 974060887
    0x3050c0a1202070b0f0409020a05040b071505090609060708070e0409080d05130c03080307050d0c030c1e0e060717030709140d0b04030f0e04090c0905010602030f190c17 74
    0x140c1c0c004c0c140d00340820700e45100707011140601d0103107108040e682d135008900d00c101c05000b44107540181c2074004180d07440d1801410154000350303c0075a007961461411010500c03001010507003610503036031000140410346524008840d0310400420040820000717103600d00041e512401400285170094500c942c540103881415411140c018014007050714000c00d44400291200c135420084940190656840f41d485020680d000c2c850b09850428903440d20400003240c42d0103038410300c4040115074070801d03800c4200440048141602c20b40c2d0001c10802e0800980307900cbc0c104010610a84503d80511011181e44a10b8201d84c0003550301c10045860b4000c20302584400c1c10b2180c81658003121506940407242d20303081c04610001c0e001404011740c0c079501c8481d041c000c000708854984060410010f02c4240d00b0a504041d1490050644440c1001c0002401d10300c0081035130351955080d54010300d0000d440d01410030018501c0941018004990514004500a00e014484071a00182071941d1a9a61801 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 974063363 1250 974062113 974062123
    0xc180e0c0d050a1104060306020d0509010b3a050f060910110a050901110304080a0605100509060123030a0603141b0f030c060d0902090a0b090703050403050c0a1202 72
    0x140310701580140c11900082403000500d50b600c1030300b00c00c00750a2843e045010601a04407504064545130000660208113603655101500c02c4240c43c008020005d690000c1240e0080d14074200c4e56804892503c0c80b9107000c160144080d52620101c81750f02080301d0341c0d919410144443c084d01303281e800c000d003000400c50003401402c50591a200c0100701d0744240741c0040d06540a2070601d4030030030202003010b401c01e9019130540710442110388100da41755640c0d06611130342c4402200c0d086070b00c54100b0340440c60004c1c83c140b9801c103450300100310a40170b588402c01150011101c20303894907141c00e0a54000e071805050340056004410103a0302255060445c14401d1031014a161340c1c00b42644402c0344071115010030a1a00045082207820003259001a00001e25141d240103070564040c01c005280e02035005558020000240300b95001012640c0d8401c05208592401c44150b1b004058900000c241f42c0c4a0751280d07501a01c241011820070000100c01807402440c044101c6607440004500302101d0340400c1 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 974064613 1250 974063363 974063383
    0xe0111032415031f0f090b031f0231090b0d08030108070608060102030712030e030d0f2f03060d06090f030909051b090f0d0533010815040c180e 63
    0xf400c02d02070310b0b0828010341c50105200340860310781d4032180018562313001e018010044a800c042d20000d43c20203151702000354850b0200307070045241a24440c100345070381011448100d1a4100d0010200e24200e44940944100320680750b000304c600114400013900280518082c2c20810010500a410642c010b40361850161104d81990301c18854000010100c0b40302c076405050034a0049020b500002600746140a100c1000480904203250b90a0038440c681c0404a6131401c41810781f5406003000090032042d50880488088041c00c20004149060039205810407503c03814001071001c110ba121481e02c8400c070942140000c6080000b00249001da0140a030410072180f0480c04620307620311941901d2140d208004c0c0900407132404200c4c2c507035409941544042d00207007610b00c48230f510380d00000c086500060240001104115420314603440e0400181a292214000d00d00041081580446c400d4000d00c00c0758107007020034005c1a801d18110a4004041032100c0101c1d41d943c4104005080c030700322a03 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 974065863 1250 974064613 974064661
    0x1311040917220b2a03040f031505010b040509040b151f030f0e1f0204080607050a02280209180d030903020712170d0212040804090e011103241503 64
    0x300c01c440c402140e07403a03014500c003401303414103010458156a40d4114050342d030007441600741501000061000088142c1d4071500841c00c200141d80e01c1d911b0148490195008090b0010b0450f0300080006a001c00c5868100440480b13008003030345204001134080303103602c0c018a94503104200444801c1c0c0c040c0244400c800242400b0b106441941007003550714140122800c0314242c000642c0e02c5200140c1e8100c074007030000c040c1501c45900d00b015014146d603201d500640700500ca048811071140d400011103620281080800c42220300c20750b000c00032400e401030140f10019580c14040a000441042860600784079610003040c0c03580c1d60305002e4100310003507104c56501c0840140480004980007038210030008007218081d11440880e003588c00074011760200d8030001c3c140c50180f00c2404074003000360049030307080c103418084458080519401d035150705c0500c0700d4100c8140b012078006103c0c0480c0f091008814115544401800380000f00000c410645000c1490800014840300440883c0c0340c420900c0c1e40 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 974067113 1250 974065863 974065867
    0xf020a0c030606050315390406032f03010b030c0c010519060b0f030a0e1507020309102d0c02040207081201050901030302030708070c1d0f1311040917220b 68
    0x414006500c0100310b031075141f2645030402d00c13010b011030030184401745a2a5a0045440310344a1101030014040ca591f0349000041040f8070b01c40310000c100c005007600a140c000203007144d1810100311000c1c0c0004d095a10301400c00c0c04034000341482445a5071007040b8400c40c22441c0071a0f0744c186001c848640d00201140601001b601c00003204030401c40f50000b40c08400003404042110b602400c000249040c40b445400070700c140240c0c142e0000140260036411030b5400e072441d01008090300d003001200007103820384802d02a00d41001c0c00390442812001d6007030405008038602c0d680003800300c0e48646022120810049294070803060b2302c0103c07a024100a9030004150750454901a60340c1c010207400902d05900003c415007004001c5030910020030035030f4a6410b10200748a240d44100001b00c640c2d0091404a80000700d00b906000c00c4200c08035000040c40d801741c4603403070902c006030003101d0054a0429450071150041010b00c3c005246840e240a5100064045da003100e62135251183d002080300c24003 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 974068363 1250 974067113 974067121
    0x5030d08040b0a0213060c05161410110708030316050705070b03040c0e01080102030f0601020705151b030c0703050705030c15072409021903050d0f020a0c030606050315 74
    0x8032411503001604200303418241d503980200b60000e0f200e2030310900e00710010302c8000610207800c051040100c41c412000c2c1c0f50003c10040b2a000220364600c280c01c14248101c16800b00d6003072036403d071000800c05280c164800f00c400d02e074940c40c00c500d942c0715070354540c030000c10001207075101a000c0340d83c00741c5440c0c040d20788185621229501d2407240900b52681c00c0c000f000c1810040c80c082000020500480056100d6039241e141c24000d42046400140880c3c2290000d4071a6201041c800103848000b044460002043e41c8107040716008a0000c801e0324000f00100da00340300b0200701511408506400401005086241550801074242d1125003c2d41c0f00c80800b01084c1d6a42408500041c1c0c1103c40c4d5843e0801c50905070320315080c440c83d844481170031030f00740c41500765503401a2020314001c5c0d074051200340703080d0b4494105e080b0601c00500140c0000d06822403291003246049034100403481114104180c0b03855040300c55443e54412580903541e003200b0012410306000748504c1030b0200250b01510701e4 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 974069613 1250 974068363 974068367
    0xf07030309060f05070204180209130c1e1a09130b03060109110909010e010f061409040207050a0b25020d1202030c120f0405070e160305150d03030b01080105030d 71
    0x1c0b4082d403000c2c4503070f04400039840c0344604240c4d4010742e0014424005502940c0601302d000e024000240d0040c4146000240d840400c0882e600c58158846405000d0324606103400501c4012210030a02d0761100410025810000540602d14100c11204144e81c6515280800180c064020740300c02c841ca05120ba600300700c0c0c0c1d0104800381120780030180800d448501e000c140001f8031441d080720380e0100d4900c0003c40d00d500c8a10042d416520000c440340c406940752002580d29201d104500d0b505803104002588050078250040c040140c403a001300c1e01c00d4011a9600d070b1610301e0854811410032000060f0a0040b5007401401c0305c0009980090310000032480d10040034602c8215000c944142c0000204402c500c821085412042c0c0c600241c10349402c2c004a0064011b10075117080d540f0b4420312402141b85288801028020292909283c0160707050b01c03c02e4019081c000c0036498640207030520b014241d02c0d4549040300c894400c0da00010311441e1035001405203041030704203a000317501c240c019442044d = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 974070863 1250 974069613 974069627
    0x1a060a080c0d0f211409030714040608061303021006180c091701020d1104050a090f06031a061906120f11070b010617060904063b0f070303 61
    0x80426207401d0074180450504401600f04002c0080c50603030482c4002514090f6141c0809000e04196148a40181d2082542980c0d0180d451030a500d40c00000c1c0030071400500d1103400301c2c038010141012941e103640c3c140b20350510f94100c13103540700c401d001e62004003015414420b100768032103020000c0241604019200b109001303640740d980310700f96031480f4020b911800ba40e071490080450740680301d000d00c10080854007070740007500c00300d1003e800c00141c141411604001d65050b150050302c2c0b46c1800b0314000003c1c01410340c8100e0031500a549040201c04101016191402051200c0207001a42086428040342420b070a07404010000b041c3c005110030740d030141c07241c08904681a00402d800014031001402000100181e1205d0070000541d5010400004245d904803a0b0301d488204500c40b001c3c43c01021341000319032071988129040c00107400201158040e4032000300141105003c43c0e100031071000d080143d404c4001d4403000d101d881c00301107102001a004400301d01000382c9056172456030302034040 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 974072113 1250 974070863 974070883
    0x1150c0c120302241005130b030609030403021314241c1a090606062101081c09031212150b040f120b0412231206030d02070311010903020d1a060a08 65
    0x1d030082d0047d010500603141c2040c2840c40c4002c080d2a40ca051410805039a98060f05c42240039030b44916210040d40401e00c81c0056203240701e4030086e4181c0d0340001000c445031488400d40c50702d1140141807521600e0b484034080e1152807408034011454480d003003e051400101d0640710140000030204864460003248054101c4426140d02c0d40740c00d4407201c040f81c070303096100104c0080302d500c80000445810000710805408040c2d00c01010b00e541d0750710101c5403900c00b4000036040500d03086004907c0c6d841910b08030440b21041d000080c034101d44449a808105a0740c0c00120b40d050701050500424940d102810000c000070942008460001e5456510041e0010400341c000c44104a0081c445e6015045501214440065800d40114106815a4660085005400c4001d1150b0004040341000034600030000c0480d0010101c4900d540e94820b1125503580c01c150402040410010040c2c84c0c1c201c4405500307201d113110769075152401c8a401a003440080805101d1440030a003080407280124444ea54 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 974073363 1250 974072113 974072119
    0xe1009090b040209060309030d051605030129160c0602070e0a02180603040503270102100b0f180405010f020304080406050f13090b010e0901150c0c120302241005 71
    0x1c0700020020b000d20480d0796008070300042004002a4040f00170818032160300070030821a01c84030340c13a900e03d0b0420040d12011520400c0140001e00410482c003507560942030001d492403800f030060345a9500b1503007552b01002d090102403010044007002c21030142100e8402002e8561526100320704001000d000114019400600f0705201d5aa031000742410060260545130380e4149890495034030380c40110980c0003e060006003000b400d40b500d602c9056031005900404418128210700c6000304032130086136502010000c07004129880c1c210641c10009810610b4001c145001c0c207041d42954642780c1c0410000744104100030024803840c0c00d881c2519400c1c54415142c200b14444c464082c46072111458011248001c0055803455641042850440c00c4ea00e07903505440301d03001d1184500080c080c241c0988007008891078414421103c0406484c01100d000e01c920b9900d80da10441e1040d42c2000303a0040c1c0066446d40e101500201243d1103900e04000001e0183c038185420701546107180c001d280c8 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 974074613 1250 974073363 974073371
    0xd0e032503021506030a021c02100809070b1804050a0e120406020709022b09081216030507050910090b0a0503160e0102060a09030e0a14010e0117271209010e100909 72
    0x4a0782c002c111055401507030140c4441840507907040b01801d800d0044030cc401d00d0344594440803405042c040d05039080d40308401003d04034084604100409410014521103003030303654058403a1140300400403d2102d00c0c001140d16a21420094004d003050019044030440500411112481d1002d4104204040d43d00b0804800c0130b01660940d10b002d0144800c02801400004c1880c4500c0c0700c01001c2680070300410007049090380b03003000341981030303480403a039800c0890000d00c5101010f0404100c6004980101d151800e440707070704c07035403115000e23000303c001034000440210400029050105c08401044100e042c9203070b12016480000f9965640106841d01e0180c940081004141c0210f050405280004000701d10083d1192400b0040b2800c4440e8580010010260180517501130320b07204c113200341c00b80382d03481c1c00d81e45003c1c0c0305d64000020384c07404012203a00a501140e140c7c040c8a0490006440d020082e81c801c40701c0f0004014100340d5070780a01c00c450b2550b0002003181c102000e03408231103540101217 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 974075863 1250 974074613 974074639
    0x61201060518220305210f160509030f010c020106080a080a120209060c0f010f02072001050c0703030903050606010302040b27040c030609051b0d0e032503021506030a02 74
    0x40e00c182082d5210460200380302440303e08254114014181c1804040d0b030b0500d0303500c2001c812015104040d00d261250403580004140c8140304019212103401c02e50070b0581c0f61404107408246085a900356554281e5503900c0b030010000c5e0b0a015a000411602004219072400d03601c0c2e4510b184288030f100010300c85400e030b00d06551182034041d2510164020405c5407500c1d200c040712a216000c0c050700745070b1546040c80d103e04038840b510130b031849181c0100070751070604040d10740d40581000209500341404000c4c40b400070348080401500c40950304c0703a903c6541a501e1494151315000003d8046030506005000911204513008141c410002402040b05541030780c81082c4011308011010182d0410305028280d80c4c0c0d0754140d00700c001100e801c80d20401a969030726810000380a1114840405135108101c00700428800e50404a141d8021740e007038900d40f541100c000c00e1001e912680045a0000e498241424544c0510101d030140049840141091611000180c0c86450b503006c024400e0310169594 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 974077113 1250 974075863 974075881
    0xc02040f110f13120b071202040b040b0c030409060b0d0e0109030822060e010e0601081c080406060510090302030c0306010503071809080a090f080a03050901080a09020315061201060518 81
    0x5034000c003445040701d02c01c41c000c5c1c00e0808400e00304a80c0c003000308404042d04010000a4802c8030212202d00c00200d04003070611590b2507040d80480000d003058442400701042840040c0b00b004000c0a00c03002c1142d0750090391090200341c800080380d0b818142d1415007004e0210303400c01e80389948405041c241c18000c000c80603210026071698000540f03058503040180071040c00c15404103031040c845408071a5503a0b070303400000d81d40e10082e0340342540340084070420f0741c04180140525504180320300004036101e80c03240003281c84402c0c42400640050f507c1d0000b0019400d0501080381152410740c050407030f030360400340420b0351605540310303820150f11090607003d03e900d01075000307d0603580d0088450703640b9030014000500201c3c0502405240c1c2c82c00c51000283c1100018480741c06c0740c1e03d6160b40e410904010019a04600b004200d000300a41301c4900c040140d50500c40c00c8240e500f11004142e5509080c021310410750703000900801268541807080c469541c5d07810010307680c1e40c000384006121395035030010 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 974078363 1250 974077113 974077147
    0x30b07031b0e0a0e100311060403201e30160e090a0b0c03132406051c0b070903140708120306061605030f0a0c02040f110f 54
    0x1d040425004032a10140031a80b002c0210302d44841202c041000380e84400384051460015160415806214032003000001c1d004030321040036010003845241000d03901c0e01c1c1d000c8103400c40344400c15000068000c04072186000381034080302014840100340301800400100b45041040314112101d20501911403041a2080301c00d070320141c12140580d02c11031002c05c9040c41d180c0050146407061402c80c000140d4900c00003400c0114107403c8480390740a0b44500091001e10307840501038540a62110983d003001c103001c00f070010000c41c403001c4421407004038903122004899072500490720440280b80a8a102c4c0614400c04182540021003143c1d9521100c0c0c080d6250070440d48014481c51030440540c800c00c5002c6080c20485070150143c0d0b82840514486010500c4103c2c0c220303074401818400d08214040540c1c203c3c190b14811003c0f03910b440c15000d0304488940101c07409100203803444041c0821400c040c02a0034880c1d542900a01124100c20400000c1d07003e56076901007400d1001c24015001640440 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 974079613 1250 974078363 974078381
    0x60606080f270718050108060f19091a011d0c1806090f040e0609060f13150f1a180103030806010c08040315140609040201020d0c08131202030f0c0109030b0703 70
    0x10344d41ca13903403d08807620040c080034812640d42d40103c3d000500c0390722001a44a10401142c80701310048092012407500805400d0b00a8581a540c103018041d00c4214414041c041c020031400360042c8601d542c811103100500400c1450030000030f02088048588421100320a81d6040b10203035150851070300411501400f038605594003d017090302c03403983c603036012400b18002c0c2c00070800d494107560703064a40b01d982c800c00c1d1000480180c0c0074440c0400b20310016481a0001c40549000c10300b50651404841550081c9080c03070032602c0d09102e0803c0515212841811452034224070960039859910050b2002100602150601c5404d031410f60400c01c2c003004440103154009044d18080c0182c02d482c00082ca0f0346e9469141050424010810902d008003005128a074141e0040118042d001000c07941c921500b04100d40c0c0401c103004194a40080d041c43c000500703c03500010400203201c0c01090710b42049515905040d40114109066a90380443e200058907000902d4014a49034100c04600a100d000 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 974080863 1250 974079613 974079629
    0xb030118020705011a10170a02090d020901080c121501050103090203030409050c03040317040b061201020702030a05030703170c0a0f0e0913060c020102090d060c020c0d060606080f2707 81
    0xc02d5205030705c125403028002895040e41d840c03002d00c1544c801502c01090074140ca4840c1443c0500140b546009034009003001c0c3c0010f000b40c20862019030100c1e940f11030a810062450300f000c00f1825131818035080c1c0680109201c1c0007005c0d2050b1203d181035009c03a042c0990341c1015200e40c04102552410011203005100015003003200d480c050b084800a1381080d2800c6000550b020002c882d501c42e0b00034014000c40c0c000350103610076112001006500100e0048002c11550288419800b40c1d40510085c04514001c901440e075902d41498010003640c3c141240d500c2ca0800f81d814042481800002c1c0d0b0500e046a040c02c0c208900c00318001d58002114110142e881400142003021044010031801c400501c00c4105200e107041a4000380c1c01d0b130281911050b00040c4a001c5a00810110f8000030403034151030040d502d04000c40d001042083c1444241034803215180c00040142640c40304103940d0050100f0f041c07920710f041c074030741844030001c5075584460003000e5002c84c0300c03510b00107104d003800400c001 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 974082113 1250 974080863 974080871
    0x180b04020d0c0e011409070302210604061205031b010e0d080a1104061206090b130902060702030307032601030201140c0c030118060f0902010c021908060c19090b03011802070501 78
    0x1c01000061a000c121460701030046d080204c0c003014007034020b03154600781aa5583c00b102c040d01c8240701d500307a001071a40d507116440d41d00000e245607141c40c840c65550701410281d035542c9142c1c0c440c206054424414042160b25181103222041c0c030114036049038015a160118541c0c07213081821b40a88921150024107610000b80012070341d800103070003240c0c1c180100c0240515581c0d550200f00312488504420703000380750755014030214403541e805082d03100d03c0103104504110300c9030003182c0382d600310101c00ca003c40c01c0c144884080d2490092044140218111007444960460740000c1100e4110034078484402800728659101c988207019185451300d025000304074070851030205982030b40d10765a05541c030b2850151203840d001c000d0b00922901a8040c0c643c0100c0f03801c10307070904c01c2da962007102e14151749045040104003454180710035030003260908a03c03a101c82c3c0040c0c00c0700220000254403424002610010004e4228920560f811a5038503000d00b121581900000d0300139100ba2640100107500e0 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 974083363 1250 974082113 974082119
    0x9120703051903140a090c15120204060c140703170a0203221706060d08070219090f0501051804030302180a09020304051c1707090302091603180b04020d0c0e01 70
    0x1041c2c2c086104080d440807004481d4588040640031141c0d4594090b0001100c00d500342321003034040d42c400c49010021b1621000c0c0c804550100d50803038202d60002400101360407101c0c0b050101c4c400d0081c085881d048080c01100785186d46848080f003a1a0290480c01004629040e40600038000d403412220720881c1140ca801501824040401d91401070304140e00040e004580e04420026445102d0100545462485081c0361a0702e001d40c0c01895040340e000c91040d00d000c02ca000c0300301c2000d0040c503000c0c8001c100342c1070910f03104055910581006010700711f100f0142583ca9003040701c1c01d40154150400507030721245525150102c40d42c080d8166007001c1851000a1114015401517100340c0c028004d549800781030300c01d90507480705140341c01400186450a41d022080d68054100d4001003035003001401540d5940c089542020200c3c2c6030003c00e1003000b08200000d4240c02502984032540041e94001d01291313955031500480940083e000b45840d8190310104030744041610054100300032803452942e9 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 974084613 1250 974083363 974083367
    0x30f060126040203010e01060303171317041401030e0a0b18010911040e060f04030f02031b0a030305010b0301050604120f0b0f010305010e03070c03080309010902060c10060e091207030519 82
    0x60142d074100d001c0c5d803070b10f14120341c0c40106102e00425030354156684401c0700348900d0f444c42110780240200203803ca080a034070001903001200541910f45143c00d19880b1403804d940c9103011401c01c0e40080c1418244100a8620080807407062440c40c2d003c10541d07a1511031525081001d0101400800306610b84061003040c40b00410725440160070442e0300307000c01543d4a020030780f14042525828500410300f40420300017402142001a441a10302c12641410120240c3c1c40081c60909981c07403446c5c0040307461105055050080718058052041da840c659407504010035074a00c11031140e8054050800d07502020804000040c035074a0380c02401ca02c00d9824503528040110100f0310080300c6070340ca050309840d9100804800e94400c150040002840d081c5107489031186540000e00070300b5207541e103012480060380c3d5540502829100348004040076500030300340e44201c844030f40003d841359107280100003422000080d000e44080c101c1e01c000303803a040546015240760003034800035041490008080b8051a0b = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 974085863 1250 974084613 974084687
    0x14060c0c19090509030a0c030507051504150c02120a03020a14070311070801090b0a020903010b030708061605091c08130b13090b1e0f04051501091703030f0601 70
    0xb80070000c10403194450303420303041d640e2050071154004181c1c0c1000741c2d00828000d0380504007640c0500e09031002a24080408900340b10100c0b01100c00c58808440d80407149400c6c8600d602c0d8205c640018007241c01b0700300b0032151038001d404c01c0340c04058000030b40361265031180c408400080b680c0c82c8280c0e10f0b81c80d43c2c0b40240070410603142e602c145120300c00c1c0008640005008071018980c1081c22015682c0310020020040c0d484509101e816640f140000411620208401c4004101c110040c02c0c444c1400140c1d0074100c00d0801281c4d0400c03100707000749011039541c02c0d1440b02d400c550003080c0c040c2d9049450603401a004045041594412000b00080c0000d6070b030008010b80c2c07504102c20b0b0300c62500c4100d000304448011031070320f0f0080030403400001c0c200c40d05804164554001000c0303c0c0025524030003d019103108070f9a0b072542c1c0080710038072700c100c0d40c1000007100030b80000040c213001c00800b484120b5a900000707181100303c0d031080010030700c0e9901031648207034440e1114075080382035044070301012440e07 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 974087113 1250 974085863 974085869
    0x120f0604110d021803030406050a030209180a0903020d03090312052e08011104031e02060903011a030705030316080a120906020a090b041d0916060206041103030414060c0c19 76
    0x1c10204e681074020707240110489040c0e42ca11f85402e170134030b2004c10088009403c490211a00701c580254908a524001c8051500ca0a1140c1010034403c08502d00282442403450480c411715017865044000650400b1422050314280000040e030780e80d03405501d00c81100700f140c440f10a1010100b1184061074600241c50030340341d405000340642c05034280041175030300c80d03440301070152410480b8580007049002d51141030380380014852410001440000f13821140b001c0340c001d5074104049202c1f642c1d41018070a45004000450140d030801345a0802c83c0c2584038400e60040c142c0e000000c95519850007298122170302e0801c18000c00c40103500f440e15600030750215000c5408904218400544042003a04503070660325005001c0110315206401c4980780c1c4000303014611140208901200390000e140403400041c16594010b000a04043c24502d0301200c08a02d401e01a40040105001c40488122104001c54040c1d070179903a5a8800c072030180c140012440c1056100058040101c01240120700031ba040d = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 974088363 1250 974087113 974087137
    0x62003070f020c13200f0d0b0f032d070e07081008031e07020d0f170304050c0d02010e210d0336060c020d0311120f0604110d02 56
    0x221400701841030341e4550905040e02d5004500b01d1000518101a801800100b001031155101d9415902c00400298001c240304400402c0c0114640c011001903010b94890541d0039101000c2c200032100c003003074480d103a1003cac0341251406e0542c2c1110307100c1c00066814000c2c0c4080c040d83e030310b03d0300d810400400701802e44000c40016600c50104a00c10b2031044040b040707685c104011898078100c03003440b050800c203142540015410900c50600940caa1840c20302c58140328105415900e106440c24000394815001e0712051040d0600c100f000140c1d0000d001d8001c1042210390b50060512480100c40b0144500100e54000c48005507031400d4202035008100041051070075a1400d0b010324004030119803c00d40072083c100081014405c01c1d100c0803102441c6001850040903480d40f845e114078050307400c105408070041c3c0c81136046d00d10941c1d2502c50030850001d05003426180071602c8640203408032015020302101110700740451403607595075000107405000d00303100588941c00d900b007203402900480041c0207 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 974089613 1250 974088363 974088377
    0xf090907082e0e0604170d090501093302070c170c01030c020a2114120405071710050619031407150807080405010603060f0203190c0e01080406200307 66
    0x20208101c0d0154407120841d841c004c01003607440da100ca051100900402c106042000c000380001c0310407501662510718003803c000702d00200c691500841d0302c00d01d081102960f03030043c1c0a0301651050035041841c805124000941c40d4562810034154140c032030fa00c017480c03c45150102012440300800c3d80c0200c01001d8800b0082540d41400c10782c2c590a10140c01800c0f4a260200c0002e61802d10501c1c8040303808a01c1c103940c010780710100c08640d5502104007103010301f51450400040140030401c107c064000c03002c400b68808405050a0b90343d40c09200c14108090b201c200241d4907481d03099180c103480804204050001e035880c1480a01c1d61059010030000d07008031000812420800c0c2500249082c0507075074144240e1311000e0848402501402c00c0321503548800c0000045070041c002ca0450010560300103030340342496408a210018402560300b00e80d401c081031160615000743c01401c5e00407003070a0640040d91149032800040c00140856495000001000b8a0440010010398441c5040d611350384 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 974090863 1250 974089613 974089693
    0x180b03060703050c0906070f08040b0d110f07060b030a0b01090b040b0423040f06020d0506031603030509100306080105040c0608090a021e22020a0315050f09090708 72
    0x1d043e01d800320b03403002080070308200440440c00c010000302515401440000301400341075854040b20703480f6a0014500328408242018181010310a400100303005c00c00c010f15090002e01d000d4480c6c0500303000604010b50b81c4000c1100394800740b003040301d251b030700c4480015190784612401d0010544540391900540c41c000d040001d0f42020300c40c41040781c842c0900c0054030100041780040c81000208211044101c01c00f20707500090303a07800648001d911403d17012030340c1d00d4004103140c581807220042001d80c0320821020404290044100c99000505503a8903095502da58801d84c00313040140c0c4044210b40ca01030400c014081c1c0b002801060340c140d80d850034015118511803594802c08500081d500c00000301000712864201c0b03513060f2003040040c01804144150710b540ca500d4800c2d42c4981b951440d0001019401d90f603241c440e40355900f00443d20550310a04141c0481c114445c1481d00a00038480c2d0350202d000c03020304100700380c002e0040c0c0c81251849040c645194031f1403d030b0f004090381c10a55040c401 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 974092113 1250 974090863 974090867
    0x7111f030c05040f03020f210a020f1014031005150c070e090c01230c070e060406140915060f0a1e0e0d0201201c020601080304140604180b030607 64
    0x540c01c907404c074412440c0545c04c40e000c11030100d804074092980150007158681044c46030003034010466592001403ea01100c2d0300502c52050a441c1040344601d411a03400a83d80d03400031003100c280100003210a81700c5d902d0f0414406825120f81020b175202078650800c20000d503c4d04001c1c103d83e01e10005a4004543d20b40c00200401c0c4291b88031002508001000c0c100c0303501c14185126081c600400070086603803d85610a03840d40441c02010640e080440c0c1404061540b60000303402480943d800c200c4580781c203c0c0c0703203401c121120020740308620880c04100318540180b03120b100c49400405a075514001d1821104c41980683c91b01e1010800820307204008043c041030203490241701d9165040080641002c000e01340b101104d04905000e42d641d8000c08050303030250824070815020b03005245503034034155680549590040312204543c0f01c40c0041c0f001c40c4010064404844543c05003900b007140103000100b142c0255041001030403a04030794031010440301d030030691890b4029016580030751100318007 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 974093363 1250 974092113 974092117
    0x60614060703050f040504020d0c020c01020f03071709040c020f01050a110702040f061e090f0615121b031b02010b010e011809111201060914010507111f030c05 70
    0x10358800d20910440e40802d02500c010900c509a160341140b40581b650000340c126000035520300701559a9841000e1400c1d01040140c101c03010900090a510401d40f171034503500e1080c844020540910690340d2490241044195802c0d980c0092082c40002c110a070001e641c2d03521100c1036099503091001052803107145115000841110b060303032603d024107540070300000d003680d1040c803c2c0301950340320300203811440101c08e404179004400c40c3c913000e2841c0002078403e075600311020314080c615180b010086440d4000d400c81010003030303040841c280350100c1e0b0003c008111700f034588050403004540300610150f160f84007055040e040c140c00c405a080340c2208908071829043d070b180c041144a994021f107507028148910b000d02d01e800d51401042d031200c6e44101a1046500b4a1000c400007080c059490040d10010358050700b414908014400c3c54088c5107948200f160640906102c800104402030020140d42d00d5140c0002030841c5ca8035001303407200c00c04c20a03585401040084c0c90800d2514040e03100e402 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 974094613 1250 974093363 974093399
    0x220302030a0605060f10050c2a011119050c01140316030506041503150b1203030a0b0f190e0106050a02100e031e2203122003040b03040606 61
    0xa007140c0100c0e5031140b004010103040703154040f484203079403d41d560701c452050508900503583c00f40c07242c00140000b40342c0b411844003842891005400e80304040000300740d0401d90308003480c01d00c1e08001d4810003036040c000075030f006006001c1480c00500a0000000c0e5041e451b030300a9a41140103401d0088111f054042560300070552412841201d5101d0700c01e410040e0030440040c00000c010307840012100101e04664001c4698a00460540394401428842c0030341c90342040d02c0c0ba0047d00c0c1004074258492000031300c603a140300d55484900b80d01c1d403100112000c00350000343c007240040b01d290380300303030b04140395445005104485e100012a21034401d85c1516142035454004207403001070819404007a1868150400c03c0b072001b84100030402284000c4c04101410001126076102001e0724000030680414900015441888108000152a03c0c00310400301003145801007949200d06526841000381911351f600b24800800c000c264040000004e5004030b10494080114681c0c0b010340558940b071201c = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 974095863 1250 974094613 974094619
    0x6040905060714041d010e0109020708030103080319050906190e190f0c0b0703020c0d0b070c0c0b030c0c0105090d020330040c060f08010b1b01060305060705220302 72
    0x10301140c49a4001c401c058000f042d08001030b0700b0103446408010354991800b01048001100d1801040b030180350054540c050300401400b545003181c180c0701c003002480107100050204100000003000500c012951450584158070244164248000140e0742c55800703407a00742d42e008804032082c0e100c2580b4428020042c50b0314024005070385895a460000c2801c2c1801601e03d0307c1e1840c80d5400180301e141011001d42280082107444051300e0500071314000e076003444d803400746036091003d001244040e440c280d1f2002c103030318089010b8541403400d208004c10640c090001c7d00c20200c107102c500c1c840700002c2e09040840c14000c012980d1201d9109641c0c0005181d95030160300300704031510305c800d0344500c040c21042903005002e144000326481c0030381800045a0544580b010882d0910000794081e540c446040d01c0e91070500305030b5040c034156010b1403103841120074008c0b065006816005a0a400c1a1b00540c1c1001c1a144c203423400703600c00341c40c41d0b00c181c9041c1c08002c0c90b4010070414045181c1c1c0c0c0400d494000d = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 974097113 1250 974095863 974095873
    0x10e010c052a090103050105011703071e02060702030f01050601230f0306030a0b040b070f0e0a0b091305040c0f0812090f041407020d020609071d0a150305010501030b06040905 77
    0x10003201c080030441c030b140501c10206041d50401d5030f49500f0300050003144904000141985005d02866a15020030700303803840c542081006201245001c520800300da01c0351101c4411203005840042e103107100d4044020340500642c1544080e6000c107520541c415a030a8845070b8120302c01c00908903030248022001108007801703221218254206001655001c0750160480741c50950640b600041807004803021100759211508000003a40e22182105c204078403801c1080c940c401040c0003c0d85d0210600a642e516075002c6540c03e0599284d8606141d007140c211010000f80c189801c2090f803000c001d00500901c445850300c0007440341c2c40003603031050300c203002141282461800020010038200d10300403550f000703031103490b2202c800081140c103500484680d0000c081600303c001019042002c0103201f0600798200110402800c000c102c00d10100a06110b0203100f20364680d42c9641c010b1152208101e502000d081d40030080000542c0941e0690b4021460000d00d640d5000c204000e660000b00300900d02e07042 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 974098363 1250 974097113 974097133
    0x6060f0f051c1d0d020c1e0111030415020c0a06020303190203131212061401020a080f0f031f0902071a10080102030c1b0307030c1502090303070f02010e010c05 70
    0x202d0001410340710b8425102045a0041000803100448a9880200180c020b034001514035a01001140004101945c0e10380580c2810441112607242942d016030520611415144072540b00344200c50140c80054040380400d0184031009540f0540141d0442c0120710780c00c000320341d00780000140c074440c02c80d843c0ca1400300d6100d015000702a4002808030850034030102c00d640001510346400c241c1ca104c10359100302c1500220614002680d0540e8000e016504070301d410046c0c1c0d6640030450300e600c81d0b000000d941d65140d101d001090148550f41d4020148640807085c40f280b10640c0300b10038174010014401890668507003140f88124440c1800080400c03040641c04a0001e000b5001d1547c05081d80c046450100e6541c054242a60b01c01c8a410600717000025103600e54480034103a418002030020010760910072150380c00360500c0010b580203440103009088078a8441d9094044808108010f000d803516844a4035004008040c540c0c0200e0204800c445e0f0310005522500d141d6000c00d0b0804000e00940c24 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 974099613 1250 974098363 974098387
    0x90a020315091f060e130b062e05040510020f060c0309070302010f0e04061710020c0c0402160c0e0a2d0c0306030f1b05010c11040506060408010f06060f0f05 69
    0x280c0c803110f40e040c20f80c807440c00154820400611601c51142c8400c51100400d41c0e141c01145483d000b02560700c0344040280e1210b851341d52154142c2c50240a050300300038a05010780544036801150305c000c1c1d2028400640303030f030020f03030200c0d01c26440c0d100c44c011190b40c0e0722101140314450000f22900d224030b621402c800c04c00340d88110341101e10118a0b00380405d4000ca4030020405595446e009144035941c002c6004c008580204102d8005454141c400c50505262031200b0340c4980c0300404140c41503401094505940d41e04c02c3c1035114050b40800d14a650300da641c90400031100080300c549443c9072030002d4090001c00805050003220040540e0b1600051213103d0308030040c5810903020003010383d10000800040c0803030002681040c00b4081d100145805120b00c4440300ba21a0070050400c46030a58210009409021102e0b03403101c1243e000c0781950300c4101150560141c0d5004400399030801401c480071141c00c0c0c2c06582580c0c540c0d1f0392403182c0d44100e40b0950748022401c45a0303002a00030031142c10318203 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 974100719 1106 974099613 974099653
    0x21c0e0d020a0c0b07110a172b2316110d0b0a0b061e1803030a050406030e03130308040f06180923090a02031509 50
    0x244443e82c80c0d1112450030b2284070b500c1c0304045000820404004031030300354404007a0039060400d5440a2640314482240c000c80854001e110746108000005400302004004a641507120b500503068111140e146041404000d4003140c00520b0300840440c00524040d00812a00c1d00307140540d05200c1c0d010112011100e110384070700f20345900010811007105511481921000660300e03403c0c404104c0c2ca100b00c10750529123000d5240007220315040400585815020b42500300089032803d07060540d02d11400a9a0340400c50901c02003011520a411101d2040c20715400c4e0f90900e000c408001000118a40088458032800714080c00b0850103d81600b000b0700c2030703140040d0440750174442841a030780240903044540d03442d402c6460745641c400c01d005040b840c03604070045142ca050158251a200100c008920034003880003e1002c041d020010f8a028080c01d1014100070341c03030548606022 = true := by decide +kernel

theorem cover : BRFrame.Cov 973920863 974100719 := by
  have h0 := BRFrame.cov_init 973920863
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973920863 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973920863 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973920863 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973920863 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973920863 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973920863 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973920863 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973920863 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973920863 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973920863 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973920863 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973920863 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973920863 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973920863 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973920863 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973920863 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973920863 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973920863 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973920863 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973920863 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973920863 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973920863 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973920863 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973920863 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973920863 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973920863 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973920863 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973920863 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973920863 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973920863 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973920863 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973920863 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973920863 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973920863 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973920863 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973920863 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973920863 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973920863 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973920863 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973920863 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973920863 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973920863 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973920863 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973920863 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973920863 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973920863 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973920863 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973920863 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973920863 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973920863 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973920863 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973920863 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973920863 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973920863 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973920863 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973920863 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973920863 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973920863 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973920863 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973920863 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973920863 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973920863 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973920863 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973920863 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973920863 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973920863 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973920863 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973920863 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973920863 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973920863 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973920863 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973920863 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973920863 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973920863 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973920863 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973920863 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973920863 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973920863 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973920863 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973920863 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973920863 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973920863 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973920863 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973920863 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973920863 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973920863 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973920863 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973920863 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973920863 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973920863 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973920863 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973920863 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973920863 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973920863 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973920863 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973920863 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973920863 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973920863 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973920863 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973920863 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973920863 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973920863 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973920863 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973920863 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973920863 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973920863 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973920863 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973920863 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973920863 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973920863 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973920863 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973920863 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973920863 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973920863 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973920863 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973920863 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973920863 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973920863 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973920863 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973920863 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973920863 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973920863 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973920863 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973920863 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973920863 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973920863 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973920863 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973920863 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973920863 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973920863 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973920863 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973920863 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973920863 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973920863 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973920863 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973920863 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973920863 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973920863 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973920863 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973920863 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973920863 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973920863 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973920863 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973920863 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 973920863 ≤ n) (h2 : n < 974100719) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
