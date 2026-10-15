-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_5429
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T15:50:14.341219+00:00
-- url     : https://prove2.me/submissions/34307aed-d20a-4722-b6df-a4670fab3041

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 976258992 ≤ n < 976438848 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 976260242 1250 976258992 976259047
    0xf06092a040f03060605030303070504090225030203071b080c190f0605071103122b0c030608060f0c0703080714040f0504050604140106030c0c050604030f090b1806 72
    0x1d80d52503100042c451100d50009585450034802c0005180c14008200da2142c0d910742d4130582070070f0814444174041d500c07c401d8059080e0b25804804209030110013200041c51080d0004c42c2d458400e880c0c010b40811261880c1c080e00b40000c0700c204a803d2010459080011084811070450422900c0d840c2c165a4550869546032407250130100300345e50071100520b1143d01030b990010389081000105a0b0791218184106103092081c0445400000c40302d1510f1561000700c0d00740916400c150110f00c1c1158200380160000940720301c404c200034a410b0151603080584140d0b078010300e103094160001c0e01d200b110b6000b01004036980000741c902e44142d080707441c440000d000c5541e80d1680c84240d060b8146890280611035440c0201184640c5010300c1026221461000c0c4540c1d942c0c0703000c0d0141e0007010741100300428454800a5200000c80034000144550301c283c5400e4011002a54000c1041d01503410000346d041c010000340340c0183c4250141c0c02010000c807490b9079035012200d8165025000d0348181d02c007 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 976261492 1250 976260242 976260247
    0x2102100b03190507060206151f020a05010f1506020f0a11120607020106090e010519020d0908030a0603050d110a0f020111060906061c0b041106091f080f06092a 70
    0x4100300820101c048504950844609444048c001a40b00910351000c542c000c00d0190307070120055140340d42280036062030058561060302c50310b65a0a5031040c68003401d1540d82c03440102c6021131009800c8014001c0c610041440d22504000240d580144444c05803039801072400d0a615552030b505200c1820002c4015036400341440140a4040c00031402802da0007414001e0360245004148241c1e03104003400010002c2c400410781d0b86900940c05419240e8803d5110b080003004034034810300840c0103940c80c80d400541c5501d1402d0150400706004640010842c1e519010240f01c1c00c005001c3c80101c9c0c0007081001d03035412510059a10510390390390840203000e58070402213100404184148102421769080b0082083d02190410782000104002c0c54200f0a50104000c40d0030810030304004c1d9805805036141c080c0d0f141c0040c0c1e0341c003044200362500e50070154090380500c2c3e22a105d10b070031211000020045003070080000f2590040240840042202001902c08082c1200100d41150031206c01056 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 976262742 1250 976261492 976261543
    0x70c03050a11010201201c0b03121b2b030603170901030b090c0a03020f0c12031509040803130203120301081509030304050601051203070206040e042102100b03 70
    0x8000d528060b0392640954a40014513140400008101c000000954659071428501c2180d807405446100342c039107174140d90380e60703441c2d483d403010443c5000746007144c03d5140e252460b040032100840800f420001282d0040440c00482e000c0a862404103000c40c00f404132101c22010600314018a03040c2c0c0007800b00d2100300700c3c001500514034000c01c0d03202400e0764180035849141d010700a4480c000e81d424140d4071410450220041d210741c0c060300c3c0a04005e0b141e28075100f8040499480d00120020b2005502d00020a000c111808006a150560015503441c44145000d454050103800010030054213540d154040504640c1d091104560070b80f829121103440703584501109a94218540141d5410000b14000c01c0c9040710000c1034034400c0d64400d000301426030030401404030746400000542c0c6584414018140103a41e0000030344064580f04d00c8400544c030341418020b07800390b15080b5031203e0a284102510f00a41d0106810074035000000c3e012681d00070321000320307180bc01105042180d6080040501 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 976263992 1250 976262742 976262753
    0x2090109090204050a0b0f060c0c0d051e01090305040e0c12010b0306011b08030103020111030714060f0106030207120f0521090d020d0912080d02120910060b0f070c03050a 75
    0x8007541070080d282003005681e01d0360500119104d40e050030350300103002d00c42e9050a28100c401440032083d0f08003500e10544205e800700c1d0511603a20004c44030303500a10a0300010866562440b80c104100c2c000074081c144031038070040c05130320640c01560b1a49500c1c0b030001c3c0307400240d01c08039400d244000c04a0155980d461a000d00c83e904291525400140c1c600e040304400441400d10a50482e085144249103901e035a00642c0c0406440907450b180c2e0000380240c81c0401c03243c2c0030300d60207409080c0c041c01d541d00c1e00c14220424240160411024117105100010100313290b0513130300408a6490400100c5c00b0840c26040e291030142c94601d0340c080352a40d809038010b12740314400900498030030040b0f82c802002c03160140d0311080000d0300c030400a504000c041115010100c1d503007249030300911403646003c1c00c0400d400141d92182c00c4201e9421032081c188001c014080104000110759a4002c0000e0743c1401110807852041c000d94660800010465409202410340301c00021603004048411700503040c94070 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 976265242 1250 976263992 976264001
    0x30b04060207170a021c09030201270512060703060b1908180307150b1f12090b01080c010e10090504020315060703080106110d351302090c04120305070f02090109 71
    0x403804c03a8030906d414a01c030a40280100b2050380d40c145c48890800075030340a81166041401071070b1103e0350a51030001125141c0105603107401a10b500500417a00d802e0f400031b0180d8805910031550b5408c200102040510620413400d003a09462900046e1a15907160114134403248410b02195400700250301e4040040600d00d00340300d80c60380081405241e00b9002080a0719146d0103403103103029009040c2c082c0b45480380ca082d400400c01042e00040040c140e84900c0d04582c0709821880140e030200000044640c6c0142c0c03c4400c80030211900014008005402056a030f15489800c2c020f580201c040340340d003004812412690003000d0121fa884144c03508000300071040c28890355001ca4000c02006084110110300c5400d4204185c9900d0194460030b24984000c01440c050721060a800001e030040a03483c1900450060320095210044441907004009940e02c0c09400c54800312010401000f4004070344070b02c02d03080754150400300e40b0340650b410999480d80c200d1900139401000c40c3c00102c2c034040264031 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 976266492 1250 976265242 976265263
    0xf03030c031c0b030c010c06060b0415020f01092a2324030408090f0d0b012c010b1303052b3006080303150f0a030b04060207170a02 58
    0xb030828694841c8065800c0729500070505800d5000b02d000b060265003e03000001030284034040001c5c1e00e640d01c40000c00d42d41c1058005d01e00c0800c0c0c0440600c92554108402240705a0800007040740d007130305a03101081d070845020300d81400e030f00044081100c1a01022004000c4c144608412101c070408000d036078408107004080c900c0340f91106100030460803002d82404030b510030030708182c1c070390340f1603442c0c1981d0b44d00000c00e01c40d40710008168244094840d001045204c0d403042c800c01c3e07034030b5040895540c0c0911610161442132a0200c4c240500d50888400c1e090446120f01c0b0f402c0e660300441c2d0300311850005c03580c01c09805841000030030b0005104200c15001c8146446050800c144e40c2c030201100c1400e070500c212280721040e0203000314000088500c0034040040c040001400540d80c07100e043c2550001c81d003606d41c0030903492240005090024911000d4032040300d8200d10340b03045030380740d00d0500e80180000d0034250340403411030f0402145601c500c1c0031668001425486614924000f90b03526031000 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 976267742 1250 976266492 976266517
    0xc0e0301090b181c1d0d0b0a06090209060d0b0402070c030c08070b0c1509030c010606020c1311030c0d060f0b0c12040b041820071208060d02040b0f03030c03 69
    0xb02d01600810001c240004107440040b408200c180051300200d0f000038545601c0c0c40700b0442c80495a52607a0b80298805200344616000090340c64020014012100306900941c0b5850040000101c80d54401045a140e41000c220000d15401c080010400901a2400007005291510f50220504c2590181d1100b00d80b0528110b403645a22200484172a003c0c62200342003d034400000c000c050fa94008001d50300052810031a410310b0480c941041c251043d982c000310140c1c0011401d002c1c00d080240c46004200388041e41801b81c3c011900d01d041c00c40c44000d090300c0d0300b040c02090030010542e060f0051401045031041e25000c041c0c40da141500654071050004015210324070099100703403c01016141100c1010040604107842e0020703614402c441d0600c0c41c001240d03034202c0901c401c044d0040c000b0748058050000743e10345e8624030f0000306100a19602d03d051065103003c000c1f1076580d0030600402d040d81940d021481c10402404655129000d00001e42c0c14000814070724940540000a8105e084011 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 976268992 1250 976267742 976267771
    0xf01140301020909070e01020c10030e1c090e0c04090c0e120105040209060d0305070c06051918090209030309220606030504020a090903050409050712060b1c0c0e0301090b 75
    0x14081500703d02c81e0200480e0031100010020740310341d0040440d2002e2040c180161540e2415600005040340d0b440d5000d02d000c40d940383e0700070001640030040c0d090080441d982142208460b00700152080d400c40c0f00b4500b84040500018a60f12418070035240207145031007040c07020b042e44081c0a07120800c1000114020802d29000407a280414060f00340a10303009007140c0d0303081c0c4800003449021a207807101641808010004030f800150383c0c8800034000d111554882d5102e0b180c3c0e40c6849101200c0d0008013040000426a0300703e0004c03c00301c00700407101000e100503540c203031078070110b4118050080030981c410032002e00203220a83c105100d80c41001d041c082008003585584c815401c45000b0354010390400d280900501c2451038582c050307803007103009040c043c2c00e01d40d643d01c401e0300b0303140308480c10780005150540940c10207460f4000c0c0400b03020b1071803880d81041c002101c5d1551003030754441c010f495162110100d0290078061002070030107400c0940207200c41502428102c80c0b88409031041c1d079510411 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 976270242 1250 976268992 976269029
    0x1e0606020c0d262704053c181603080d15031b050918030405060309070302090106020f060a061212031503030309140708121e03070f080f0717040c0308030f01 69
    0xe4420a8485c03c40048641c40039004c401c0ba03420895040317003011054070740300170304541c02d0300e1f104036054841c1e401a1048900c0c0c409405c40795040411400c2d21854100d020311040c00000c8a503401e8070903096540c04006541c00050459400704a2503074805026201010341c41c80c9206104d002c02c1080d12030545505000381c5032000c4003a4010341c020745011651b04288014000351034a40c0c02580c01c0520002218152a104e400243c21040d0a81c04600036900c8810040e5a0244c180402ea500000b1480208806845d014980b00000e010318001072102c0c854100241005000345c0c00010400d0124405021682d01e070b2401031f0040a4051003511f11880d03008100041050001e03103041a200b000b0302501c00c3d00c80aa0700c82c0b24070f030468608890b242c0c0072160641540e1003190007542c0b1984941d6909100042940c001604664000c3c02c4118120580307070030495a02c0c0c00c108081c0d586011510b01041d580e0f21810506440c201d250801481d090000041c0507031004840030103410785900d060f080905e590b0 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 976271492 1250 976270242 976270249
    0x9070609080c0906040e12070311031306052a0a020111070303090308180607080304020108090d051e220e1021151e0606020c0d2627 58
    0x11248281d03645980046020540c82c10840d84154001101410100d40782007074030f041c5d605055000c00e40700f2a001010891400f81584540ca080741d030403c0001441c0782c00b0000841c600078880a010703000074820001a0903546901090b920700388084140c00d603206024a5121060326a00f9440060f8005441c04030540e1107001c001c100c24080341e5160b1203004860389966110791060704050070300d170008294940c2420709601d401006148662189100310740ea0301c2e0510000d410000b000d0003564440c0d000640d08141c0c540c00000315000c42400100f034048000c0e40c071600302154410240e081c541908028a20181c18020805a42c01d80700f015459040c035640b50400e0314942c1c44a48944020f8244105100c00e450719074401c0001d816000e400149040001041080140d0308110000c003080c0d03944440d04603810a052181601030001840031300038200e2aa00041c034114100e00014050640b03820122415a0b4111208181948003da80c2500c8041141e402d030015078180e1042c1e806250300c0f0f0501c00d441d14 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 976272742 1250 976271492 976271507
    0x70e090708090c1e0d0c0b0c210306030606131d030d0c080709140103111803060a0e06240d050109050c06041214160305010603110d05070311010e060a08090706 70
    0x103a0218094000011080c10000c4440580c50241e451180703206c1c000c07a51034003210061614000c3e50b001172001542d40210711304008045c103104140d5201c11b10a00000780c1e40840c80300d801410032a000c1058280080e407010040c8074004500f07880e0741907500307184812600400503180702d000c604020407210b503070001c00b580e115104980f400002341e4203003820300c2000300f81140809003401c103241c0012002402d40c4002000c0e40311003100c010060f0a1030b0510820f103003c02c8040e41c016503900d414001841c088040340d95802015182c603082603042c0c02448049090b94141c50201e8000a004801c0d03001c3d5030074014000c1c40c4454050302d0034081d44154582d24100301e401c45045070242c040f0401204041e48a1174207503541071188203090302401d5a504001441300c1a0107001d18003c000000c0e4491440c80e201c806903150b06034181c001c110b00e0708000080b0b580494034004894200c3c03101003c24101c4c8004841c9015001b90a85e400741000c1022078105600180716446650301c441220b08180d218141030f241807 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 976273992 1250 976272742 976272769
    0x102c0a09182108070f031407110f011a06090312040b0d0b0d081b120301090e060906060901030803150d0624030510150b0f220518070e090708090c 64
    0x601c9010208208a2203840388012003c01c600d40080c88548100c000b6840d518240c5050000868407491091560b002b402200c0c02411080006c001800390400f0410403603200e00505840b0f2840450410070944007408804020207000e40d031903588070340b030b0b8003c07a03056040721030304110a501d08071592880d4142103d1010403c1e80002102741040307000203000d07001d400c0240c5203c0040c002c1d03406c403044500c2c040d0b01640c0a0001c10b8004542075030b40c1c43c01c082c0342c00c9000700300b000281d00c54001d02842d6140c0c210400c8c1582c0d0006d0581380c0d81e0340c0b1054100c1c480e10040b4131881d08140086985028010381340e01a03a514101044610075810800e0000c04880c110ba000144c26500402081040d000413603210010250025440c01d031b02c65901c0840e514940c1001c0300340c0d11444000910b5010000c1e01414290359a40d40401891001d07080602098003030482586500840140724085126540180030311800703648010040c403c0d51600420003018244140d402d11464491907008100034030b848200c0340300c45d = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 976275242 1250 976273992 976273997
    0x14030708031303021005070e010f18050d08120f061206062b05070807030c050904030f0e06071e030f020d050304021504080d030506102c0a091821 64
    0x11078035100507030040000c10042c02c030150f01c909402a401c00c255030040911641c8192240c207980403007600094603528030614000c00308044c1503a0349000380607812007581614800d5581000600f07540c41c040610340300302100c04100c4e0310404100031900c0c0b2901072041c030421058801c40030003441319405543d44c000035941c00b9880004040c001c04071102044c40c10b1b07481c0c0392604100c482c1c80b407a902c40c03e040c070b01d15400402090b080448207000b40480ca0f0b022200601c0d0507a0700505510701901d005040040207a1054204844040c0c4004569100b2040e43c1009030800540d07a1041846c18100041105018003207021421420703034412880d00204890302c044000d0f4a860749540c0d169400c00060803101407251a03229024040401c1040741040b0a0703001007401d8030002400d050010800188a080340d191104220300302c10000d00110303003241c141d00c0780c2d500800500ba5140321030000410455075600b2684603a483c000d03052091044c003215484055000c0c4015a40c80a200700c0742c0440010801d016801 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 976276492 1250 976275242 976275247
    0x20d090b031906090608060a050106090302010c0f06020f0d0207200a0306110403050105100806010f0302130b2202090103050a0902060f0d0b060a0f080f011a0a02070503030d050414030708 82
    0x6101205058000442d400c800014020f5161512901100c1c415045952254441c000b0070080810a1240340c0c0035190b18101605031a2440e03000030880f44110a000307002d501e511158108000154050302c5512700320541e15034541900c0184440290041c107002e884030341d4080f29240301c03859058600070712140040c20710b10207103083da11020094400080403101052080100201180080c03060f2401003001c402420403052034a031040e4500201a00300741701c10265210200016076840c209114003440d5000e0100d19103a0100020f18280420f007a410b943c02c2c0d00400da0f42c4191181e5005100f0300d40d098800708950740324040500215032142e0760080d040b02041049101e80510080900200041c81d0340c0810415442c03004103120342c000c9a0707910017195081f200c0650b0785030008481c682c824072544807480e0641c0f42c06201003015900b2001c11040c01e030b000032480c90300c0e031082c031110000e814040c003140d40d90b1480d90542002450115010758000740701911808103840084200c6600701d401c240d0150 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 976277742 1250 976276492 976276501
    0x41203050903060a0c1b080f040623180f03190302010606110613020603090a0f0c0e07181401050f121f12240c0320040302031f061a0a020d090b03 64
    0x8501c0146c9400a17180d4081c00e0080c00568600340700100702074291903a070101400c10061081560074404071399411403440c18005140aa20314405c0228480c20840e140790304840c0c6540401d05006040c0c080c400c8100b5a03407840b1081c0340d0150403ca04540141d9945c5400d090100307441c80d00d805095507503021003043d00e00c18801620b4180055030f00301041400781d8540f0b10703c0e540c03007040d0402c002c6000c440041030300504010307001d40e40c0e824a0388289581082003001107120000350100885004200722038150305078034031281c0d20400a44018910404e0001e40d00c0c56a0419010035903811203000340c4800d03252160310007206c10304403410300b01c4513101c445c0c0d01145041c0d580e0000902c000d140100a100694244d49898209400ba50380720b408070703480014070140301d5102d4005403e07910b601040c06a80400042005890014182c4003440300c2c0820200703810450f8081601030700f00340d1300091620340c9101c84403000340340820003055000d4a54085a4000d51050001e607004032181c031480e0401c16013480041e = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 976278992 1250 976277742 976277777
    0x601050415030b1503030a020c0a1202060304061d012313260d021c0b01180e130c03050f061e060f280314060112030f05041203050903060a0c 62
    0x201c0d0800d0540446a41c480c113044080383c9180c0146606c0750059004042110386401c0190041d0701800150206400d05651a00811018440684010076050b682c0c1094044440503801341502800c00c1c0009220a00d00c0100003403825109d6140c10100c0610349000c1900030303030203403c4000840c0c0d0051045003c940312410003080170403500502803401c1c50400899461285501c001c0141030000d0500c0502da0701d10310702901c1120b8084840b10305005203110300001003007200d0b00c03602c200c42c01000410010703a507902404140501190340109840c0d00000040208a40801c0e6411030b030f1f0004040310380f26074841c16948181d1602c2008800c1c040e4040300030550720f040001001010940c080c2650402070f94910b10350000200300110460112443c003403d10030070020108400c114403080008002c00c0d41800303e0409000055035005091060b030604032400d460007130f000d40d001030230314600e610300800e10340c2000b801c1c03039000c002d289109001e000c0005d49c80038500d00c28260700c00f9071980d501022680d110002d = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 976280242 1250 976278992 976279013
    0x405070813060b10050309150426090a0803040303080c09131a19141909020702120303190e01092a08011d010e2a0a15020d02060105041503 61
    0x540d0b0b11500c45190a45036100c0f4650203a40d001503582d025aa8982040840e060005ca0795080440f84216800e00c03010620100c07a080f02d540b0510b8000502503111a000c0641d4032401d202107411101320310300000c4008000c00600100c90080d118607000b55a40c081058035803107502c0441d030388414014894051701740daa600042907401485225a0250080d03000141030030303000701092034801c0003c1410310840b404101c16000d0b00c902a100c45280d408098bc440582030720354024420510350111b0000d003950b554141460345048180107032642c90030500c5014207411040b4850001403401d0240300460898140300b90314056412610700c120607101d2007007908000d40c00b809007401640040038044fc07045000e02c6030100c07138418084052558142410481c1c203682100e01c905085800041b802c9450080061001c481014940c1102d055040318134001148190b04c3e401c21411380700461441143d090b0006980c6401c4045a0203c03407290303a07190104001e544200e2940c0d00302070400380341040011300c02e045 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 976281492 1250 976280242 976280281
    0x6020a0f080a1b0f0302010b0d0309211a01090507140304060c1e0309120206010b04090b0102070b03090102130e06010504050415030f05071706071d0d120e03070504050708 75
    0x4012100000e4250543c0b5000792046054425030300c0c102490b02003580901c188101413400341d035083c4000210f602c0103008622148503165086030340c050b04001c450184140d00440e1540000c0c02c100340301c004040b01c1c1582009002d0840c003e890000411541409850144000c0003110781c101c0c40c503500c1d41d4035070002c2c061810151090200460320400c180d0000000505650229a40010f10007400d0800d40e00d10418002c1c9c280554000c0750041c008024200c0031203080d910307070f0140481c0003609000100c4c43d1100581c4201140300c1d000c818800b07040e8040d001802c03c0ca0b50400d8645001d0788410382c5d60407642054826a022a4080000300603a0525411940d41c2e42084110b5119803681c81c0c40b155840e2207088400c1301e40c0e8008407000c0c00340000400e2120100b9080c100107040500c0d040901920b45100e600314000d6810740d040e903542c0c01d6a00c0003500e0035405e5111302e000d44444280f080242c280078540714541d200e4000c1c8180441c140c206807003014070505c082d90392a6020788a1595000446000b5030 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 976282742 1250 976281492 976281497
    0x30209130e0c1309050c1c030807050702101e1812030509090c0c0f07030c0e09031c02030901180b06040e030f04180b180f071206090e010606020a0f080a 67
    0x165412076550b0342d92680c0f0114280d4500400c80e45558070301603040900c00c020440c0300e0348100c4804850781c07484c05d4003440a070b0745c1410081f407a616051401d5615004000c002940500b00503c03507190719074495824501410004425034400241e81d8040e900706020b084910b07981c0d80c3c414020010a1450010080a18040c1c24000c0c5030a4140001c40d11a000488094090f010300007480303440000c0401003e0070502c40c82d00942600b80c1559591009e036801445070020302c00d80d0f030707001c80c0540d0070a101b190441c0010452000b050380c02240e610019400444840f106540b0700384546803032203554481d05092680c481c000480f150388100401009252a00015126100c1070220454141c1054001c1c406080380d1544c4c0410204000300300025a000d0642c1607028281000c01241700d55209140d80d83c02841402c18103250380e031407041c00c940700c103600d45120480350b05007480006c0c48122079102c410b021031480700900143c2d0301c401090307030ba4000b14038008101040c1542d00c1000700f035010010b000c801e080391 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 976283992 1250 976282742 976282753
    0x13080a0903020303071119030503042903090a020a0504090b1b07020a1e090b0616060f060b031906080325060606030f05060a0b07031b05060903030106080601030209130e 74
    0x203070086840d581140c042100c45d0701c0d40c900c45000d00e24162030000d503564a05c40c0748011f4642140d40c3c1c16268055071142d00c092100341541d0b403803e03071001c0e03020500c00820480c1d00c031740700c0c9003900b02165030342180340040e4001c4044000208a17400e16005448415401c18804040707501c401140d1058906080c80c005680d40b410721000b00141d85201203d4000c00040340d401c081e00d444a00710701a140015444004200d10b4a0440821525a0380640705c2320051100481101003403820500041e1140300c0810709000e04d850400b00d94841c108025601440b40714031641043e007c140000c0c0304890880c0104a0213038014401c150700300c400030340f45456941c4025202d6000e030900d951550251130342070b00032102180e11000c944c0d070744051a201e0194415001c440d40c1e41c180e860710901c00e80521845802404001034441e914004824545480d04003d500a04540f01c500d00103030b10b561603410a0240d903001a500001052640d0720034020b8036071040b4000d001c00d01240294000100500d00c200c413101c0180281c = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 976285242 1250 976283992 976283999
    0x711060c010c090f05010c0b041e020307063b0d05010906050c25080301260a03020606090708010308030a05220c050f010503011409090a0501090c0609060813080a09 72
    0xe00420940882d00e4030b903041e44906001c3d40d0018050550805410004600440000314070f0340d0220a812a4204a02c24000015012000c4404d640d400c0003a4040c13283ca1400161141d02550204210f00c200c3c0c0e01c0702a0803041b0041d104040140c00040c552140944404806482c005044011507845600001002092542c5000554800f110108191100401c0c142851030100c18410180c072102c01c01d003000003806594801450006002e6100107c40155181030700c4104040042e222460309002c891001009150096540b80219000f6011300001004582c0c0c2c00c3c05000c2850580754080545415a9981035600006002c0100405540780e0f04102c42070300c0100006d085040c1314028000000080e00b07010034010105480c04511381080020001089882d2020b8034601006504407000b8819448110320a407030040b1180024101d5480c007d1b01c10100700d616000b040454116450300380e600303a03451106440c0030808484130f882d60b0341025280400585400c00400903200c45040400003180c8 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 976286492 1250 976285242 976285267
    0x7050103111c090b01050415060f02010617240c030a0c032a0917100b030c180f010605030c120604060b0a02030301091401030f0b07050d021c050a020a05071106 70
    0x1140d100400b481680c0e0a4501c0500c403c00e000b06000d004240e409100078001040610001c0040d40300e90b038200101c84444c0300d5080c0c1300b90841d00007051041b0062486182610743c942d01c07807203e070a010001e00c21143d910901e6041c0e00c1da5441c0715020b8000c0b001d00b10341d02c1c014490050603204043c42c0400d5641c51218a04483c100b03400214281d20321448100340481c01c2018024403041d40181d4643c14000c1c040705180710002881c43d080e200040c00101c0c0c030040402c0401d14284000080039880f18526601200c1b82e00750f0102988200d10706442c90303d55982e104000d0314903201c2038664050840d0100305045249060b00d80c80e51300600040c00004401c1e4fd03424601400d5001000740c0030040c1c0001004114040e51801640d442c0c2c8010301158030194034580d103503442c501d010305005002501d14400100824024000d0b503c001d00552429551401e40e10024404880b404c0c599000303241c030306808958440300c13520a2700c00e4071010f0749440749040c010740c603007034051080111000d511400030821600881c8 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 976287742 1250 976286492 976286527
    0x10302090909010506120c032d01060b070312180206030624090a05030f07060c110406032102011a040902062106100e0102070b0d09170d0f060302030705010311 70
    0x20300c0c0b00c00008290500c4420800c070031140f0105802d040d44114502d4800b0b9402041c0180e03500269100f40082404034140840c04006158103800d03194070f45000064488007040007424664031960351a0b65406c991070b1010101e4001110b4010404009002d400050030442d0013160490310051001e84400503683c2030a210091702603142c14401e502003240342007400c1841003400030f4807045024005c100304d00074450f59601c03010711800007044004180d800c00e200c12a03007007600c00000030f841444081e40341d0a00c04101d48403284075074109204900d40110b82d62041c840d00a1440300000c040761204020000c12001d40300030a4240c5c2d1004040010031080d9a45450241c5842a1280c0e40c0d052454020100030140e0700285103403050010328510440c445ea4085000000e0350010300442e62641e280c2d030641c0000b82542c3d0b0006140d404d0466081000c0900100503260401c4c0c41c403030611500c2c4005241c5e5003911810b100007034140c2c0c8605010700866019421041070b0155400002d400c2848043e00101001d = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 976288992 1250 976287742 976287751
    0x70c0807061a010e041b0503060a09110901090905190b0a080a140105060a0b25080d0f0606020c150c15010b070c05010318120519022b021207020103020909 68
    0x84000c40d440d8551300148250490f00742220104403c9090030004250494108030900410030000001107543d0350f9140741c48042c1800c0001000040710000d44050550300100d44d050128505110001c0c0c2c504007805210b12a00c90405501e1540005202d004081c2c92800816540030a0358030000c038849904000b10080d45000e502161003810242407400d08440d40075001301d00505800e141031085080c0c090880e03070301e4400030002090394000c5042c40b929503892070340c0040c0b044d00005100b4410040c0d0750003002800c522040100a841e50301c170740503642e58010132081500050100d81c1e10701424007227401f4007250460081542d541c0040c2aa0300c0318604000d0704600d01000d4089611000c0c0881d40b200000602021700301000761081401c100703405c4418640c8003e000780040700742454428410025035094407001009104107250208d4042d4444c600c41c8100c0303c01440c1d410f000b003440a501d04242030840d28030b801804821603540400b403095444910281e050640030441108a901e444414500c00d = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 976290242 1250 976288992 976289021
    0x51f030e151b03040506040b13060f0b030c2b060219090305060f070503190e030d06091404080f0307020124090b01031e0f0b09070f02060c0c06070c080706 68
    0x440c6821902801a25152034009860072414804c01001035800141a80c0142d000703850b040342543c5003010581910b01c5448001c01031400e102090820b0241c94001c80d000140031001c0d00d44030304040e024020300040d90615020b0030070104005514030110b10061102841c01032a0142c1b40500e68580c202101c101601c074180011000310040003030200030310100340c125105020507100d03400c0490005040d400044d180c0e115240c040c482b20ac2e1070807600d80c004840300540318180c1c0e44030307015890150000d0805105141c4128240750208001d00741401c1c100d8415a1b00030107950801806c0485210940c00c010100800d543d038910400e0800101d01d010015a0102d19100306a0503083c00002c200f51040d80880074141401c2a0800080c1c0b610142d42c5d0500c0a0708400000b448543c030303001c141c058503841e4261900030700d071102072050f215840420a165400c40c0d800b122a2601c402244a90b14030840c4910101d94100c02c01080e4450304c20b986002090f0700a18989003001e506440e607004840903e4080c1c040d = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 976291492 1250 976290242 976290283
    0xe0f0705090c030108030f1b011a24030f04022718030313060f0b09090703020a12032f030c0c0306010b0405030c1c0503040801020409110301051f030e 66
    0x441c900090015444036540c00c4480c115403500005c1940ea000d030303041d40301100a000c90817004021031070b140d01c040200d90b04002d205000002102e6405440c651030001e009138400c60840c42005030500e18030000c0b090244000b465030307a800358684030312000a44126400509403440070034401190100e00a582c0e01c10b0801801800e0842d5a0314452104682d00705094205104024514060302c0c098544d00d80c1218000c1009000440390400030590302000580c06260101404040e0400081c0c91064070f109a910343d1045446d21000c0b181800190801170005401c10701c80c0c202800107000071a0940b040700d9001c00c0724400b03d00c1c8141507400c126031401e0707180e0110380e040c1316038a000c0006600522511000510385030030b04c000300340ca5000201c5000d00075192170540015684819003400d041c01d4000f825030391580e44448a0a0203035115100d03001c15107050845a010f81b9824904490485000420044a8407252038100901c4007078000048281a9a04880d140104091040e1500d44036540c1d102c52 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 976292742 1250 976291492 976291499
    0x140129010305061c03120e0a0309030c05220b010e040207060b01031b23040503120a0f05030618150901080a0b0109020a210608010f2708040501120e0f07 67
    0x5080707400040c1030f03900c2458102840c0c2c54403450750302d01842440d0140381500000e1a80c00100000e000001c1c0401440d00c00d2404900505600036008400d4a1042e90b00c141450381d240100420f40c45095510a505240b4402200c04240030368444011313408103061a1640b18169800101260082141a40c810362644600599581c6c03510905100804d80745010484415140005100d54012040c24801c2405404042c0c00c403840c640030340d002860020100c5041000c508418466a0041804040400c0f038411440c0c4916000782e062728810300016100c02130300c5007480d12420700300c03901405040091076040e84158042d11900c00880c007a110240c010312014139240344c500318881d016401800345a1060080400841c4d00c6440d01c1e14090103080c00c5050104a1900b08009000d10741c0810440d43c030f8566114004002504196150300c0490800b904010101c0225018206d40300f1004041c0788080200344070b00c0d0f003d5180c0c0c0848100e066000607462401c41642860080504100001644980001c0 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 976293992 1250 976292742 976292747
    0x30c1804231308030a022b020a0207150c0b071209060203092802042406211503061d070f030605091b13020f0a0903030e030706020a14012901 62
    0x19600072040070403840701c02c5456100d400c01030001404c3c0c0410350740c000a9140c6495115181008000105448043c4601c920360766803000307500c13000d0090054000d140000400c80c0c40305003084160555602e8000b20b07021607035640f00307842c240100f0303100900c40c400c02401000081445842d00452184a0050792400c0018040f07107020a070066000207400c0300c0500d0b013820408000740da00c8666040d0340c04184010810f449078010b00340c1103010f5010048a07040003607180d41c01221a01051050704524044a5030303c00c031003054410420718081c620740f60000c2000002c080d50300944a5180d500e000402e5181001c6001d410100164001039411401a13820f1060100520815822030840c1d03001703165031840c0700c20b81158207071141c0e0904d10408a5215408010400b5011204091503100000b1746c0d400f44d64501400120701c0f4007003500001c0001d03409071100e00b80081d00c0001d80700301d07400404418000380e591404101e500d00c100030445d501d400b0b25840d14a04160585510120140403520164241000 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 976295242 1250 976293992 976294061
    0x2003180109120312020708162f09070f02120708091c1a04050a020904051606031512080f07030c060f060b030a091406090d1403010803030c1804 63
    0xb5207810540080180019030850003050b0b03600141c40c405615080c0c3d41c24200f00d940a8007031340000c40b100d14104d02040082520b00c0700b0400a51110561034002ca940244134034a045001c0ea5800030307250000701d050300313014602c99040d0425900c12100c400c400070910603c540c00400003207800c4100400c5103406403402801529038030005000728464806180c442d592114024500c500ea0014038202007014090140300c2e86109a4000e0004040c0e41803500c4d00550710040b203c0e400b0401500c104002c504144640944500342d0484050212022706120490b540c038024060110742540e02001201e0760003541001074a042c0d40244c0394501c08280e10304105040d1103001c200550f109107050010312084440750103076508404642c0000a10b4842e0b850045034240c00c0700c004012521800f001c10a59240c0040d031702500609942e6940e621803220300030109140001e0081206c0394005000080310341614002411988141c0240c82400030385080100f4101c1d0241240c4190f0103441c8551603c00c005030500 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 976296492 1250 976295242 976295249
    0x703050d17010509100b03070216030b07080f070806010f0216090518030a090608180708010c14040f05010f022e270209060a03020a0b0a090f060504062003180109 71
    0x100e44029192610b40600490458006c0c2c151018012000c1868148200710704049070300440c0c400701001d9100c5c10301d800f240c04122070000000f0020000192407058601006014500c0d6881d505402d466440c015107401c5c08107040354085200324001200750b250340120b100000c1c0350310007000915007020000950074080c0031914601940c4100404a16964003040080c11511145451010b5869440400392a2280c2c41707519100c912514034081481441075204965030709182c1c80f1030740000f0800c480001107025611900382e504c04c440c0b07010462075005076524410042d00d803050b1a40b1560400107030b540401c90b1092045862000007126503840d0080c840c034000303840c02e0016985040f0140400c40d28070080c54100a01503d81c2101007074080d20b0b00c840d8580515401416881041d486040c1d00c031154208d1000e61001421241d800108611030420600c1079412550700c2034909400d00106541601c5811001c80d0402100300401121480a1001d0800f182030030300001301e0000d0840004200d9a5941c0 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 976297742 1250 976296492 976296499
    0x4110d050f040c170604080a0903081809010909020d15021909030b0a1b200a060203040b1302090708060105120115020f03270312032a0a0507020609030703050d170105 73
    0x101195081341c0009020ba50159000710640ea85000803802210a0070103640024070101000c1a124a0358248503032300508250160303400c4445aaa400c0e288080d0350503150042d4200b0720803032542d40071440c60240e40b141c08039100d03009880c0105540307580a8082c1409801c40000c0e000300c0e0b091082015000d800740d0007198164082c04900c40da40c0d80d420040504220b1030b42807210101c6034003d002a000c41a1100d0903968080c0c5800303464504000c00a1360040701e04507071300c5020b07000080c04540400c081103070300d9030054081019543c62100030b8800c00e0001c2c105034144041803080b6260b56903281030040c080c00f11600108001124003501a02d000354859a2403140e800c2845908000c410b0115045650050841e9200d41d0001640120f8100f101c40d00da4a0703c00200003040101d00c08000440c0341c00c1021940403400d02d5100138501480340d0044c82240d100040c1c041000d00058600351003e4140620003c05a500d1141d40c0d581d0342d460210700c00803140206a080e0751012030702d808010160300411054 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 976298992 1250 976297742 976297769
    0x1505090c0c010e1605012616111603021c0204051e06010c03081605070803010e18010504030507031101151e0e09070302040c120213050a0909020f04110d050f040c 71
    0x1401c107584c0048443c001d03203041211900805580110188040c80508524205181c19007000c20302d004500300c0d40d504a10106148203200090840000382e0b00d031030100040024440d4030b0440d42000b86002120041c501e080480f00c60000c0503075070300d200d41c2c0e01441a41400f02441d4405035450441c01200804440c14402240c8a074008031703400c80e105690111484880d03184545403e038050700c2d40d01a1900280901502200100d5040c40f00002c550090400d02501501c0c0122800c0050036101d046a0060024109000c98800240248181d40d003480c2c842c0004203a041c022207400340000740765840380320314243c03841c15802410340405950000d440107440e601d9185c540700703580079a10600d40c0b100a0095a4518103903840c240b08180d4483c140b4600ca400b90350b41c812030610040700c48194011540b1078487c0f07500000740443d8a01c552900c0c1540940050343c114452020000244140008040400c9042003540c030340c06040d01c60b5503c91102003800d0686420b042c100f00031217841c5604030a40c0030150 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 976300242 1250 976298992 976299013
    0xb100b0d0c030501050d05060a0c1101021603320304030909050406060303140a02071518030b040605010b030f062404060915020f030706020a1b050a0501050705040b0405041505090c0c010e 82
    0x30230810380c8070040300380104404292900444258103601d540722030359480450b01e8850180300c2c0a000009a001780d03201c03030341d00141d8607440c0114920400400300c0000395003483c1d22000c7c80600550f510a0280c202080215651401e903415034004803011a903460341c910044c03081540000c0060750320840c020a0300d09080c0c5410010f55075110a004240101010342c1c0201015482000070303200ca0310250989880f0342d941d83c0b9050b51850b5083d50101c0e5460b040400119110b0b52081c162441020f45485000c202c1e00d81d501849062802042828140b41f0181042940c0183c60801000185429992801c50514028030000348103203031079040701190004410310304040030000030349240355081640181c0e10150302d04d040d1452031515085040c51500c01d02401c00303101002c50300c84c0c010f9020308000d00c06a950b07914211100c0c441c3c0d01485088030414481440141006ea01c4003200b281907000322440291a1b0000030003000080b10243c0925400045d5034007003000c2806007005081050004000f80d041 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 976301492 1250 976300242 976300253
    0x15060e0f090a060503071508090303060904030c0201030f1104090e0a02030c01120b03010f0e150f1303032a12090c15020a0b0907081501120b100b0d0c030501050d 71
    0x103050612500c07440c6071802207460901143d0084008100090440d40c142d59202d407802d12a16414070395101103151800041c0e801c400201c1100c1c443c5000400d1303101e040e40c4654081d41d10300c211140603030415a8030700c010107045119100d050301c0c01d0b2440e941c00f1703240c070301d031400d11010740c1c4404007011400d81040341c01c03400580340000d42c01e04600b801d007401c0c041c0324401c0c025032009281c2c04100d1903066080030214041078245601047c00688c1c0030702500d03100c111801035a4902074007510609200c4035071500140c2040910702080030154420b00e00898031060340e049040d5520f00a00703003402c0c02d58078213103280341603600554007a1448454041c10300501403107485001a621061144500c0c198001480f40c100ca40300380031029550768490541403082c20a801095902c0d003c5019036402807148120040d01ca000b900038860490307510a041198860b8070ba520803080039000340c0405000079603500040340001110b4041c140344500d440c400901440c008200505803801a40654011454a51b00394081003 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 976302742 1250 976301492 976301509
    0x61201020c0607050913020708120105040905070302010f0c0b041a0f09060c2503030b030705010534080c030d1512031d061602040c0203030c03150a0302090a15060e 72
    0x50381084ea03140d662032400b140c020300c3d01000c0034545901c002484000c101c03210018001c4400304400c800e809a0700c860034042181e080a6000e41103510100e410001136101d1652036054040501d40055905820baa640c84031201c25201191854003200350010072006003641c07280d02802040d091102401d2149000391100c8001c0e0000031022400034071100341d02c0350041040c4600820a04248850006007001030060a11040d074038800d02500c4000103041d07114105072840e880561005c400c01c510f0b000910701c45501440c1c080020283c10f80345010203c2c40780c0707010304107030704520300034564070429141c01c1c07421103000c401c240e00c108006000a1168a00e070aa8000615505040c0980040f0142c007204501c1c0100903e016400580000c039142d2000015003c1c240140c8240c0c1c06204140c0c020b201644c42c0e00048544400e9000f0510015090400d1803240c106005006440f1070a01c80e2a074011070001390b411903070103402a07240d091400702900402c101c0c00003858586890718420f0049400a404c04 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 976303992 1250 976302742 976302751
    0x5060a0b07080c060703060e010e480c030405040e0c03010207081305100c021017010b0903190f020d03030207050a06061e180f02090406090b0a0902030c03040b1807060305061201020c06 81
    0x103951000007400400410701360b01000f21811911384606040c020805003d10101d11102c540c2445803d01442c2f104000c5069604281444019500345800c0505002c010100180c0c102402c0c815281d40f00c10380c0d01c7c280300034200d01d0701900500f9910b4009000011b003080c2c650703000c0741c044c0150380700d01188254000218171800d0f504584590840d40004822614801da036aa6198804d41c40800020038800050051200560640030345071040c200303890030460a408400082c0c00107580c0d940303040042c13400c03020300008188681801130910130303191209403074400040c0741100d000c1d554880c1130111110809603000c2c025107100c500a005800c2c00301e00c00103000f0741c0080d40491501c80085036101081901510b24900c1c000d04100300050b030380c480b104090b184c0220074034020601c2c043c010489091900880c2c0c456006400c1051550326259120400795000034011401c0800e0b166803900f2003001407080100601c1c1c50baa0101d09401d008040003419032841c8001d20792607104210500340000003081d0940d10 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 976305242 1250 976303992 976304009
    0x302030d090807061121150d0318060804020f03031e1303081c0606110c010c03030f18030905010c05071203020307050d020325020d0605060a0b07080c060703060e01 72
    0xc0290520b0120381601a49000818031400c018040c030108600201424550704010395405090010b40c40c3c504440605882130700d03100741c3c07480c0c1c2000da03410003580d194205482403502403000c1c20b0060700c1042000d03050b000380700040e00110900c01507240400042011507022070140d03140858089504e2341000301002c0d081d81c080c4010460044000780c0220080095030446e002c55910f494410322050002c90361600c05102c3c529110300851032510490311420300a072904020101460300f040195600000f41804808240e01c40c141c00e80707a4000c0d40101345540c143c50070490b20403074291230302401c9206150803003410001c108170014049480003030307100c0072110400300306085030b006420100d042d0701c84c04001510610421540c00300361680040184000e42d6030360300305001d9a00400080d030144501c0300300a1342c44050121000003180301c82c0e0040d40c204800904030108540c2c0c8030031215490300031503c162029400450f500010020a205030b036407240076482c0800125041c000844080741041c065005d1 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 976306492 1250 976305242 976305251
    0x6220302310905031b010b0907020d0206012d03150501080309060d051e0f10060c0209070f182c010e01150c0803180f01110906090a090207032601030302030d 69
    0xf03004081c0222001d40076400101e40c04540040b070502e001c1e2452040d100d0050314070b00005502c0e07e20104203c8041f0007941e010303003141d0f441e1000c40c14010f03031204003601c1c2c402c000c0d0303820301089003200c0c81040c0214070800c5081000000341c5811001c40310143d01ca543d45800401001266940b03101c1150405200b000300000d0503192100c00d451010f029690085164071031409100301462020030b0b0303c0c40342c0c04206040760f003e40c0302c4038129016003203024002d42081115000c141c01d54000c0f1603030200d1054500c3c100340d08010b4440345040c01041c66100e403201c8408a010303200c10040890068001800074030065000c0c1d450855a0803440105100d944c40c002c541c82c800c2030302d445c41441c003025400c0e000381750141ca074145680c8240d801d001c032029103c0b05204109549981c400c1c1809617080480d88180e80a08000c0d10f08140941903000411003a408020800041050704440c070162000c3e03800799940340c4488003500d00440d08481281150580c03c01c0820040001030b40c000b0442d0484c4031003160200c0d = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 976307742 1250 976306492 976306511
    0x90d030c050409050103030c05071401020a08180a06030e0f060c07030f142101060e0a090b1c060b04060b120402060703050f07030e0f10080103110622030231 69
    0x7100d6010340d8200c407010500703100c000402d143e07000d240014100d004505440d85180d441d050704451300f020358140c81c0580c0000600001013001d58014141c4010740134494051055200e000581e50045030f04050086540c0708581407400200308a070720030680041c00100388509100c210f6201e0740c09140002020481c2060715030f55042c1c41508443c000c01401c048803915039613074003076075910442c5010030082c051011000010b0414801e0301c265040c1d25010b00103040031802d0103031840c068001c0d02c0c01300c0d40090300103d081c0200d01c2003070070224880380200f4000884c21000c204000681d242d0b40d002000002c002d002e496654030307500c01da0383c2e00030b035040b240f90f5950462403400352002d020360406410021404100ba005041d0000740c00d80715242e00715040852540e140042000c100d0110ba81800015000001400003c1c0a44090f5442c43d00041105003084004510302c0d110100781c09110305881c0c0321041c00c10450031f00000c0101c1d01030401213029011100d0790024048600f4106494000f0f5450300c1d50742 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 976308992 1250 976307742 976307747
    0x6090f071d04030905090103140c060a05090d0320010207020411070308010b130f0b030a200904020d182003030a0f05070f02040c0504031407080a0f030203160c030614090d030c 77
    0x2090b000e03184442e40c2d0b9590270312401b12294071100e540b40d80600001c5001914004040760316080c41501e038641458101414055141915942281486800546151400c803c8043c411800300c2e0a80050b98407549841400103031002080c0320002094184600d1001071f411075141e41c19200300c1046152103c0d1040d281580d8445103600c40d00c8064440c00010030442c80001c001d520405140c0c80500c28444001c5401c0000c61900c4c141a004010500204209107050f400420412000680204003140010303004107011a001b9030441e1440c0d07070f05c03c800001000a060700180e021084010b0750401101d10406131014281c3c2011204221f00021802e0400038400c08810a8640260040003480036003140545550300c0750000741c40d1140c640c814079000c014009200e90036100c8a0003d899407268a42e100020111407480031002d601040c01442c52100003550754a1080740106032596005180d4104203040340d100002c80e0a0f01d80c448020800e40b98800140d12400041314a0005002808003004 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 976310242 1250 976308992 976309007
    0xb0d080a020a021005040608100b09150d23071106150d1704090e0f030a050a0c0506040506160e030c01111f24030f030e0f030f06090f071d0403 63
    0x2580f229041860310356040d80031700031340180c500b03176100d0820325112a0f041002290007807003048200d030002c0142000b03600340500320701604410300b900790b801c0000400394041078950b0841d1401c88200300b103a8010880859148640d00803036541850a407540320302e42c900d80c84034070080054000f0211500c05c1c485a4039440030300701c105038020704817001103400c0400c00300c0785500c00e200c0c0007140381c28004da03c6040140420310381045421031000318901001c8440580e895003080c2100070910042249402c00b040c410702c1400c0c8030302d114002424041c42e20080c0d0f0909040429410420400c1e8103004ea00307541c500180d484656070090030a0440e04841c9040c0600d401c0030304003050341698401c3c002c0c411080c001c0d0803c103c2000034400000c0800810000000801903d00c03000e0001c80c911a040030109008a4a5984a01000c1e00c030711410030114003c00d250103511b52620240d64411001c000804006021040100f00110054036543d0314103c41c02e08440340c0050691045502c0301c021608260080300c1 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 976311492 1250 976310242 976310263
    0x20a030f0f02030607020c1f14070c03050d030e1b040b130504020a120309060c020303040b03041a0c030114010e040b0406030c08012a2327040b0d080a02 67
    0x4103010045441e15240072081e00081d8100e001c0c1c030544001c6500203001040d100c00c1d0b0071000e802c60308800044104114111182c07140b103403d00042c500142d2781c0c3c1d064040205005805640003214451540c60081e1030107c9001100081528040c1b10514492000c00c011030003542c050b50b668180401c0c8800600105501c81c2d9055001e403001040181d150300c5a0440343c842c1d802111405440c035178680c1e50b110b1800b40b8142c002c00007a0400824080c0230301444080d20040e00140c102c03410b1540310180110380303034800c1e54155400400e03840c0819100f955030142a82c0921307440c07541429540340016900007901050740c000d050000000e081859a01d45074014408554001c1c001d00c071041c0d5909000e900303916280103010792942400c4004c8045100da480c40c1c0d61104e405a6003881080301c0301c03003c40302d0031032040c1d0600304041d0982c041c03180d601811000e0b10628402c0a44d104000800a00d00c810030002c801c3c80c903005a061680e2a402a44da00b00d000d00d907150012178a0340e840450a504034280005c100 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 976312742 1250 976311492 976311503
    0x80402041d07090f020c060f100b03251d101101020a050a11010c0801050d1511040603140c032e1509050301150306020c030d020c01020d05062704020a03 67
    0xc0020441d110001020400c80b890386100b0002524000b1540060740318005d40c0030740a520500124180c061035100c135546c489200c110100b0b4140d2140c82c440410350013074800342160301604030900e0881080340d040700b007100c800e4200300f5440042644207072918018030560500c2403042d00d518000c0d041c050409601190300c2c0c079000b1580c074110460043e01c1a04031094031400a01c280180c0c0502c090140702d01010f50200751500c4040f40e18050070410014080401104d41001c88460b40b10540624000e180d911107040000b01d407a10b040070700080071220100c1182c6021981c81c0c060108100c1101c04503500010640c0307029003800c011140720312000f03041e143c1c50650100b05c900005420501c44c100410144c403123a442820340c0d40c0e190101800d90300c00000071070008410701401c000081c0c0c01c0e030041102c03881990503641811400b0007201c0032a00f2240e03840c01c080c4d40003d84190030101c02d2060b244d00000c101e030314511042080c001e845900b43c221018003480405040450203640d02d40c03803030000545c4d010 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 976313992 1250 976312742 976312781
    0xa050108090a15151502010b1c0204050a0b040c1d01170c03071107030b01050f091608060a09140f09010c08010306020c07030b0c13051f0516080a020a17130608040204 73
    0x2c0c0c1c4080460000d5038505d000651905011150601d441c0d141300707100c130880d0919016442120340801005050241100d50301d80e5035103102c400300d62107034020002c98102640f00c000255407442c0d042c80d040e46880c83c103541049204504411043c5140a10310740024071000c02607142e03030782d82c801590a0f00118807003c00a108000e00001008045600315042e2001543c21441c0000821709014401e6070654480e0210306240000f50700c03007842400303071070341c0808011b002198540e502c4010200700c0f220302c114900b5040c00081000741413041e80d1041c54110f02008001c0090314901c030b40c010518001800300070645074000079049248202001880040c40c1c2040e0041c81c1c038180220485588e40c0210108650004a050005100d29101012050540400d60760369001d0004034000c94243c1e212541002ca0050307001408004542040090000ca80c1e90b500140040390190901005505207841014a090b0080025140030000049414204c031410b0900680f95240c0f440081c014103018580c5006a1040c4c = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 976315242 1250 976313992 976313999
    0xc13091a09030406120902130b0406210201022407050c01061509031103060f0109020724090c12020f04050a02090306040c140a0308090907020f0f0c0a050108090a1515 73
    0xb200030401c8442d00c1d120000f804601c9000740c81681c410b0381740a94443d2155280920441d2550859145031000030800219291144503856290010b007002c806085040038403201156010480650903490340e81b2041c00c03100d4132903c048252000242a82e00704000480c1101c02182d007500400302a2100306260080c032030b11410020095019807000b0380e01005003d25124060030045000743c05483ca26200d03034001e0b03007004c1104010358000c0000320750b1421f150080f0602160390070310460000001a0012981c03000c0f50814120789152500405028034a640c016030042e41c8211070426412000d44010a0603501c13002000000d00801e681d072a00340c01104100001c00c06810148401d540844039124044250700f41801008007150000414030308041240c0303070031307461310100d030580c0403042d84100d41c034100c800c40704241086c114891a01450740500c0840b034403450241c5000010b0325080c40d260b101c43c40d010b0300041d40d400d8203442c0a400c8a441d00c000b001c04040e15000b06400c0700010902d0502c0c65907 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 976316492 1250 976315242 976315261
    0xb0a12060e19050403140915041401080f0114010c0311150702010e03040806012306040f0320061b070b0a02160503010b130f150b0901110c13091a 64
    0x401c0718210040b0405100b242c000d080e85201d51400b03150140d488034040300c000104110b0360341c410640c8541c03101c80d00140608a203042d00060000d00911180c86485010460026040c1745000d064480c0101c1d8910041c0070740020603a804141c54130928007107200f18540e04043d90b00e20035005003081c1030b0141c2203050300c800d00c071000490f008041d13a078000c00005402d80312a588902960148540c213802110040249803401681d400d1400b000c01c0b440c0b0381e400114000540107078050b80c800741500041540030030500c49041c09001481d0540725120b440000f540f00000e01e948903c2c00100c424060b80a01c2402c2c1400401c4601c01502022400035a5420180d00181d40d940c07040000140c01408100041024101805400020f25014081c02c2159440c0103c0ba00582940b00d1040c20840d5940350f0100c1900d84842148018036102460a0b91062094001000541c3c81c900d031288560100d00030031030340d44400409414408103408009443d00e41c601d00340d032082940010741d410b060030000601c040c001 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 976317742 1250 976316492 976316519
    0x40204150302070b0916030201050c10020c0f0c0a0f03030305190e010f0b0409211b03052101060504050409022707020d1419200105240603010b0a1206 66
    0x83c00b13400b1101c0581c0e2101e000c107903210070b0822210016810520700f0001940a40054140444e010058800300103005140d2800c981100030b542645902c50076000603070120a0140035a1300c03005590425080d8100792030fa000140403840000c080561714000a0004207008000c000c98074001842480404500340603035000e4030210304078015844c541307850002c59207001e100f040d40c101d5100050b1701442400a8001404507108401c0c002400342c1d8046064010581c4243e800c4400c2c030a4968a8841507000455100302c2502000c0004202002c00117000558008003a41c0480e802128045140c1c0d0b003e1010502415000c0152040b505081150707848514201d1a400d00c00e04041d800c45941c1c90b2200c070300325400e040c9240c006e982d2450030010190f02c920012420303000303110542009441a020f03808503213180080a07100300c7c1c1c680d56501c10300960507000b501d503001241c0c99160010364044035000040c02c074813041c811780c101e015001600440c1640600d0314203240c03101200341080160307912034440040c007 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 976318992 1250 976317742 976317757
    0x714011d090a051e2707150c1502120103021c080f09090709030f23100c08010501051c0e07050607060c020c09090307030e0604230f01030915020702040204150302 71
    0x385102038001c201e903491440900c5a070350940402e100010840d01702d214846040d60080b45402a290041076400404414005209565958000342292800e03c2d203448152505d41021190041000803040d84001c8902d5042d81d404841e0b00c0700d90540220140c4007081050001001d0f0400890300450703600d6080060000040b05031110300650f520594221110349d004d020003803180e07906065010124504a004003a40d240c0900c1c080361490000e026185840f509241500502c2c2d01c600c0c0c0040c80c00d5110080e0740c010703c401e0a0090a2400c10030305294a14100329400401650b9008401c0c00614104010300040074040e143c10358401c040d0600030b01419001c80c480b4054485c112004007142070100c3c0d200d1064901c44003450a00005a808407581b1810704042a8000020b2002241a82600a40b444000d40d0030a400011151210601c110142940b1102e41414503000c80a004180504450b09041c0003402c801a80c4455510004000340915045805c498001c084610701a03609503000f4140d1 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 976320242 1250 976318992 976319011
    0x1002071d100602161403010f0f1e0506061209100504050312090703110d0c1716050d03020319050403150b130605030c01110c03011b09080714011d090a05 67
    0x400d0301c2e20401c2c3d0b9600d0400c01028500c4e108a403003000343c400e02c3e070384d003042a04008002141041c07166040e03500791404000c00d1110a81e0705c0400c5100000d0382c0c0f240c44401550110103000c1c030326003100000e903d030046800e400301c0c141c2d14500040c40000c0c1405600e403d4103860f60100698149810441d81d43d41090040c5048050840c0118074603440000d450011203510000c641d50a41484083c40020406084121650b006084020074400284813020031601e49640c01060b401c0f802c00c0e0045c0c0c10500c594070040c09502152208400303c1e0380807084a840c40d1103854044101f04010310101d81c1403042d81c6c80a86003200c0e80c04141c8058240c1d03003054607810412100b4000d80c095070104441101c429110b86580765100501565255001d0015021010b02420680b0b12030445074000ca0709440103160100040001449a1482260000d01401c06052144010030f111400d040c407071007003528a01c2580d17041c040007004105000244804452480300058064003031800c0000f81c5001401050b10078548 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 976321492 1250 976320242 976320271
    0x2072106180c082e140103150c05030f060105031e0406140c031006030509190c030203010e060c2203050a0606050f0f090a0f060f08031c0c08061002071d 67
    0x10501000107071116880300d003501044e01c40d050f20a08040c0c5040e1422141032044d00da42c07540c0090004800d0150096000d00315005e0040c400c2c549190494028458640521809109000f6044404144a40e01c40701c20b00306607560341c07500c6400100c8586605c4503a01d610034800f0400003003010319000702d42c040110f080b2010305511090700d404018007080f01c00b074104104094081001910a412803604050315105036603069001c05d03050500c00c0540b100c20f40b0415446902042142000d00c41c40700c2a00c0310307101810041c2012881c044140c0300300d820000008000d643d8010200356800304a01c021035010040380c90041e19854a20040c020b2031007120712427418080c19010320700300b2501005800c1802015403050f41d41d500440d81c0103002d66420602c40301e917241400700d1106071401200002c1c0080a0065803a00c9104211031900c00750380c18405090b030704140c1a0b41c0f40c280c201401503040f4400312b4444281e0300c0003120403442e0410540c8011240740f0341c0b8880d114010712803460940030b07200d190030941d13 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 976322742 1250 976321492 976321499
    0x602031206120309310902090708010f1a0f0a080f060108130b0c0903030f040e01050d081213060203100501021c020d0f03060b070c0608090d02072106180c 68
    0x1001c20070018140c80c00c0e40080102c0c01d03061900c0c0102001c000b07601c8107517464420100c030210300c80a034030410482909680b140582c0552034400030031075000b10503140c400c00a6060942c002d0030302d07149210ba54050703640c032500f243c0303000c24210680d81444070250342c554580c0340c400401890380e0b0040d01c00745014824035012034015442203031014801e01405500c140031802c0d40d41e40562a4100400c02440c070130051085c061103603402e02c01040b00c501c104c2c41194466050646416010360103a00003846204005075000000e60305000303440d0348406407002404603989255460507004200354000f41141e200104002d50301521200044c240c6030f083c3c1c03c49101c101100d100c8601c2034124010f92025038085061042450300c541100011580c543c41d020a00b255605089841e40c0c0004e0350484070124180c4091140c2e6500407039003684044040014025078560071000b1b074079030406014506200e40408075502041c2003c600c0701800980c85181048404e854002500c0c440c080038804031542040a503000 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 976323992 1250 976322742 976322749
    0x3010f020a1b1109190c39050708011d0607020705010f03022116050309100b0d050304031505070c030c0809180a1b02030403050c300a02011e0e19050306010602031206 73
    0x1f80c02510282c04410800340001d07030244440040c0c0010a03040240308400000751060080c04000c0c0098000402c10782c081c0c2510324a0441c185445078003951001c010004027a0340015564200d51082c202020a4044150114040c0c442c01e00c000c14469006031038800c0d01d00519401620400d41002c10707941c0025002d9040301c4500c130a43d2106480e074003a024502c503400b55940005801d2900511f289034109041e546d4074115001390b40145c85101c4c03220641031540d02207028103039001d4528035000a080d0b40c0d541d0040c1c0302d5290910064111080440c2424240d181c0324030b003d603101c92030290010f0a1034078a02c030303002509681154122414524125600e03640c00041680c080d2540070002e40034089d00c0364240106d242c0045205c40d5000a104201e070200d4032003c00314110200301d03002414032420540005002c81d85044181c00d5000340c02598400c4055000c0480c07038a0007002c445000c0d440007450980b00100702a5000194140116400040c0c42500000185580082d02200903103e81d280d1042 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 976325242 1250 976323992 976324007
    0xc0a05010b03030a1e05040509040303090b18031c0b120c0312040e190b060c0c01090b0414220e0d08060406060503010506030402210c03010f020a1b1109190c 69
    0xd1001c40c1e1799000c1100c3c80002c6031480c40d0400307140c4c6800d0f810b03d40d40d02e00040701c84070300f40c40690100b0340e41c42250003800551000d0300e5011509145202e405444040c3c00c1c1ea507445560000300c14030792040c003000c0d1181c000b60408034038050028600c0705c6407511000084d896072600ea0505100348240c00c401c1d040c0509a805840440c1d541140b11600c940d03071f0b800751205600001401000c926030302e02e0026002c1c0e440c0c00250200c450210000e00c80502001c0005d0144600c0780c001100f218001d00c010480480c00c060f8090903502c05036001071498103045504408000111100300d82c0c0790400304e04d8000b07550005800c200001156070f800705145c80c0c280c144400c450060241d00002541040140110b0601c040110f40261000c2e14101c03030541c03c0029082001c0b084070440b9065040001000d45500d0b0034001c5800351502c402d8218940182c04001070f002d030314101c138443d0560310900c440d4424011200d550545009019100c01c0c014a40b1080081a01003c1100a4042d03032074104e07071800140c40ba245 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 976326492 1250 976325242 976325257
    0x411040602030c070f031109040510180212150601031a06180a06050c1207080c0706030615030506030604030c031707050a2a0816230c15042303030c0a05010b0303 71
    0x30070820804444048c040040350051081d16140328200401c60f0400951082e8030120103113060541c40681c40b0300c1000380688081c013203494907601c00814807030301c503010b4601103030481000d00340020240000c01902c10102100311070954004400310f49a1101050020b900c1d8407035074101d91029145484103426606401074002da40e2882d844a104100c02401040061031110f004410950070801c903c0c0c0803514001082e04003c001940381c0d8810810401c03a0042c04400c8038060030140224500080071030390700c4600400140030881c41480e140107050180c82d101030740c54025284083d00e40340014014201e58030041c000d90000701c1c4c102104250944001c2d803680d0080c032600101003c00090344490146400c1110001070405901c4c280340002111b051030084600c0441d4119055044d20380a074508003111045094010340500b104c058880526000b210280e80000342103c200c00064400c00c800403000000b103d03050f01c40084c0b1400b05140c00503450105600c0f94000340a104244402e0585034040d00d107 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 976327742 1250 976326492 976326503
    0xe060f0a030f020919060f05090f04020901031104031b0e0405150703061206051b070b07050a0c1a06090108010204060518030c090c25080304060b0411040602030c070f03 74
    0x1a000d118400e0700100150340404402608080d4400001080b415021603113009030780650000b003000c0c54010341c11007042c00742402e026007482c81d81800724454003903d025152081e40d00143c00409607020790320001c00c58000141d4a512680ca80c0307002c0c2040c26112079041042030220900003900300c450031a4a1180360300401914030030145c40c1c014900384d00064820810f1503156903000c100b031010800400196070007014049241d051002035100200341c00c0b80000c10120301088000045070316001002e81100e8a4900140e8520301080101c0d004030603420003c080b001c0e003142e5031105216460700d403401400c00300e42540440e40d8440d081c500301d1065100b0382002c20014008000d482d4103071002d00c4070004024080c2c8010401501c00034203d00030843c0c40380c04040c2c02050403000900d01a8100822001110307510340b040556403116803040c000200300410007030700c50f4943c0d0410349503a00049a0700b610401e4140d00c8540f9010081d4903600070880807050392040d50340003c0c1c00d80314202c0b458101d81e0001e = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 976328992 1250 976327742 976327747
    0xf14060306100309030903120e15090604030807030c060c030203091516051c05090307050d052106120706030f140609010306022203061d03120c09030a02040f05070e060f 74
    0xd5402d5000c2c1081d44d0098083c01501d00b40000483d2110240c1940d811443d030ba01e841141700d060800107490700c014116198004140140d80741078985000300c6050301c0e00f240e4080d8969282d890101c03040041098028081d60030506c8600c030068142c0c01460084503200165014200c000c1c0c00200d81c20030071103a4929180c12500000812409030006043c164000380e40500ca09240700301c01000d550382a1101d0f0040d07407000074904140300080c48295801d18151501629000700fa0040c1140d00303503025000c44c585c0d2241404201e07147c2d00c0443c95100c82c20810f081d284030980c1c901000d40104240100320700094200700a0a0783c070950601110320422004000402c543d00310703104c01c0c000350410402c00440c004000214218003c1c1680200006e500c604800b080000c0b03002c543d0f006599940b101c030540da9000380142c003450b00600c82e105a01211102d0f8480d115a01b0301c3c0007900d0a9560b0320302035042840e12444040c41340203a08814403800580c1c030b903000040132440a1101c17601c5210014540b02c14203 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 976330242 1250 976328992 976329019
    0x6091504020a05090a030b01031a040c0513090501141503070501021c05160b0601120606020a031805060f25150e010b060a080a0c020712030c1505010f14060306 70
    0xa0760142a42c40110b03d04141405102130200780721043c46c1d0010395003102114010010130a0710042900300c401400042581824150755002c508181d03800303000d11450001404664800c4103500c01509160010003d011001ca01501000045029600c1c501150340b4000d40030708900b000119042141d006038000c24100a0100084007100000c141803410000b08106012030300d20703002009100c09024506c16001c40c10920005410401041040c41c6603a041440402c40340e030300424084c65150f0542044088007075251104000c110180c0c0050381c1c402d50100d000251540303840d015000321a07100650300e01861a603008051000110a0003d01c0149414104020021315030410940d40f6158400803421800600005807150003181303040c800510350781d040003c0c240f0907000fa0900014240040d201c03250401450f200c80d00500312000d401d0100722012002007081e40c0e2250070100c250400c081101d96101c8100314007040c1075114903201d05c4a00c0c802445645007210880703010710002800300c054030b2030 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 976331492 1250 976330242 976330249
    0x50a1a041109041506110a03081807090203010f03031b08030601050c010f0908091014030a150f0303050405031b0d110d0501051906140604031e0804030614060915 71
    0x151494140d9881c04203118400341520b5601841d0691a0000400c03038402c0e0800c00002c01c24104600035041c03d0f440102200e010940020b07134140c1100600391126042024140924603000351507011940b1030344000000240420501c20b4070f000c2d07901c039582d11070904c080f01c9400803103090f003400040c21074101040420450740c0264014a560010900042442000c0d035071001c00b00c0345d0081d800d4a10b03600000d2071350242c0c80c0c600b042c6008806141007600c400c1c01c00d82196419400010030205441d075854038882c44006a00710700c42c00500540380c030041404e86038076004000703420600c24a406403080c4040f0341c555810340200e8401d030820141c00c2c01080d05281c2c0311081d241c0740c0a03d8898102c1f04080038140490003c0c042d003441260100621000464a54801012035801d030b80200b10740b448059008042d03555003400c4408403034208140784014910315030600303900c0e060b08200401d6103000040000030000703590070604c403190042c1202c0c8095034078041031002c1d80b40d040303d03103a0180c182541050041e19 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 976332742 1250 976331492 976331501
    0x20708030f07140102030a020d0b040228020a1e0c0e070206040809150d0b030c03010b01020a0b040c120c0806010b0901170403210203010e0a090b071d0d15050a1a04 72
    0x501801e03c5840191080c1c0d040e0b0308a0340709850214000c4d8000880420b050000e000c0d140740c01006071070452a003c22100034040c10704022031807130b42442401107448031051007002008600b07600059641e003400c1c51b9000d200135a500c910811034071301074507001c0011001111001d240c461301c0c007900034240c583c0d550f503260340701d660000c0c0600b54042d0384610705091502a00010704050225141c0003d0540040300805160000701900703a44030b6070400c2407610007a607001c0b9038040c04603032000c040201c5480d9454005030128068009201d640b00016101c2c09000d100c2901d0b400320750340c80040d90050b0740c850300306030180c0c4034405034180807501a031044000c5040390307403c05900500034544070741781c00d4074085207600088000e01b12030f083c0c07034000c4010b011030200304c0c9072541c001c079030801c0812101ea036036580e4440124001b4801020710603a1003902d030795602d00003071002100390002c1035444004000d26103d03003040013099080c0f02580c079000c0020040c1d40d8520403025203141030210b03558214503c800300800342 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 976333992 1250 976332742 976332757
    0x12030915072c010915020a0609020402090409031e02120a11010b0306090a02192d052e0903020303180d08041706070c02060904050421080105030d020708030f 69
    0x800e1608001c0c5140c03420b403050300c1450750b2006000c00e20040004240100507000024101d60384a90608090740015145880307641c80701000c00e2002c22800000c000b400382d601a15000750170403010000305a40312030a80030320900400040405a040348041340d031070145035110601007000704059503481f070140642250303041c100d00000ca00619554046801c0c1142074500079a56884144a0011403800c1841190001c03e8400c0b001c0000e468803d039891280c2d0225002241c14022554a00007a01c440441c5409440d02401c4443c0c9071024144000002c4030414002d601010542c3c0d403911140d1003540d6147c116074004001358104100c3c025140340c2180412020380d4007410310010540042d4442d00540300820b0810005410103169006c4103081c610020101000c0101a0502d440144d81b00c90a8030010841030302e0002d80c55886140081d0150403001c2c0400c515200744003182c0c40f032584080514103031141503081c1c030111914010185d07580c0d0303003900625140e50414003080310706441c88800381188 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 976335242 1250 976333992 976333997
    0x4050d020f040908040f06031119050c0a0f0b0f06010e040b03071a0301030b01150f050f0706090c03120314060d0809101d060901050901031a1306081203091507 70
    0x6030042507001504440041d0002c94624002260811600c030340381c440c42c0001d1000381000d103c0305036484210a6503120303000542d5041400c55241d49812840340742a82e0b800842142190340341d20480c14603840828078200b0480d0040b1216000450095040349100e01030f40040e1941043d40b00464104009172002d00c024a42511880c0c80008412a00000300008000704e249025a29410b50412090114050b0800d040c11841c91191010040d840310a9145000c840c0c600036407240511456010244182c10002d440035042103254001c1c8010a20071300c080781e20071302524500070380401e000d900360b030000f414022460340c4140004500742451034001c3d881a1245100d03d14140f004400107202d01683c4100030001a5010080d9140f080051148252008112001c50502400c4c0c4002061442070503440c0781003613140c482058070350b030b000c00d0184182c1100419045614010006c03035070040060307124000d0070b841281d40004401c00c103c01101d02071031a2002501e50183c000000300c41604025140d07804 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 976336492 1250 976335242 976335259
    0x905010e03070803090105150307030807051c272303030c06040c0303020111030f04080a0903061107031d0307052b0303050403114b03091306050604050d02 68
    0x30451092004004503441003100b2512410002042c508440f030040c00b03800c170b032043d01c1c0784200e40ea58001840c0d4112a44218115903c040c4c80c90164180400901d035942b440014440384200c20784c0019804090382c884042112101e2500c4018610076642c5102d41c3d10100e02007400585041c510b0b02c5a44440386003e03044038a00381b101034280340f0782030086400303a4042c4161301b4180105942030240b50b1004000c1d074844c86c11420010403c081015011340001c000c80700000710903070400c0c00749000c4001183c00840801c906901c000c2c0c55403403544410400c80000301d0b1000d40e58055401000c403103c403d4409802080c20504000a1082d04418192134080e4108041010401c072103042d24038100d410f2280d0340110b103906140c940680044c03080000d00c0d100d034022440130301788000d210f202e00301040554074000c3d040c2c81118004158006e21a003100c1084046422000c21f40c01002005152100007650305041e005800e21074042103820301d024556010100304003c029500c0d11240750400d180c0001c14010 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 976337742 1250 976336492 976336511
    0xb1c0507120f110f0c12030c0a0c061b02011b030504050a11011b0501060311030d0f08130209181e1507090e0405100f0b03071203030608061305010606031e090501 71
    0x49994002d1310b0010300d00300740001d184030f4050080c007030056260034a80c40c890450924051460341e5020742040c85007046000228a01800742c2900410107600301d114440303160050b1402d00031b010b890b420b210303090000301703c2c031100c48080c1c03092141134460b50300100070f804a04c00a54403107982c4003020540c00d04210702c00301c0510b00f03480c4c3d40d43c0c40e420b41c03403151000003441c81c6149001104900c0c084100c174800e4009101658002c0c2e0000d51050000c006840d107220303655900800040e541c1e16664010750051140d004000040b40c0d40042c40c0000386040c42210b080080d904200c60b01c003c8040d240812503000f449040030300780c158207119030704450142019004039446642e04080503d084031b0036a91940258800340640b829403191001034070210409012140250020981e01c051034820003565202c9a444d5405041c0301e50f100764050a1160300b0344400b4100a00110a03c0d421040290791039440c00b0707000203909019210341952200020070516800c00c030780c8006c0e0010000380f002030b12039540307851910 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 976338992 1250 976337742 976337771
    0xc0c11210f0a0b010b091305060a080a03052101032f040e01020909150a050108040f3002150109020a0c0b0a090c14060316050c01060b1c0507120f 64
    0x1040c8201100c000304916019810030480300340040e400031131203160030001b14100e92103d1144541c00f0303094100115940e00c1d00c02c041000958594486416070081c0d00200080541c44801010080c0c10742c5414280800c3d01800e014800b2028030000b003d02070990042c400401182082480e12a05180b2440c000484400881c003504d0b824030b011150360b5030000320700706a85492040d41da00f0403c80e02040c0c4102c1d01100c041600c415940c01203a060010140018042001d92416211480c0d44a03002401510fa01c051744980c400175480d0540c0c8142c24200000c0e40c0a10004d14107044034a0034003203000b0b0b41d2a00b64080025801903080008100510314800045102c1101c11800f400b1041c00004100009042404003604550030030f24038140030b1a2900c0441c0ea6030070989400c1225950b50010b4000d40c2c80d001d0b50144510401d400455090101c000380845800001c0c014065083d4881481c84260315851f00c01c07144200c0b290b030041140383c0b068000c040d016502144040302c0c4c40760002400c45858004 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 976340242 1250 976338992 976339003
    0x6080d090608071e0e0409150c08130b01030b0c0702040606020304060e04020f030a020f0408070305071502030a081512011506020106150c0206090609060d050a0c0c1121 74
    0x8090215a00d04010400668000a00c90f4059568a40340d0501845400054012441825410300b040f240c4000c1101d43d542d543d1002103072590041c45050704208860004000e01240200361011600c0440000e960594000007821815488400f43c1c8040e030840d541d180c01450050151010341c0820310041300161114810313a40642078076001180c65515080c4010044e80001000d20f008600510900341020b480314241c1380c10115104015071540078800d680720303540c0103550220300c091055520001c14000c4c049904400e455074000c0c694070700034084005a030740e44242c00c083c9000840d00c500160045e00c00c660340251601004094a102c840401412400d40741d14650764501e091020314100861a0244a24030040007541c02101101140700340c0605901d03940000a03015480008142056a40d004219542d00300c0082144d500c030f80c43c0e190107600500c1c0c112115a801450703c9507c0301c2090040301080c000992200494600509030400d002001d40803c0d690501c0e01e680701f0404000d84014002c = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 976341492 1250 976340242 976340263
    0x406020f130e0c0405031f02090a090606021002030103050c09090c06071a01051503130318080102030601110102040f060507051011030907141309020d05300406050304150608 76
    0x16854440c03400e00c80c50b010a96009003903620f812504010800c410384011652003000311052184600100a2202c0311019104170005c065019440300404541c240c0658000026078800744d007143c01582a03034640b0000c80c8001e02000c0c045500c020604074962400c400c1d00340d8030880640c282c68071490f0030804030386680c200340e108450440308040c82140754020010510300500d021a6852031542c40c1d10805c40583c4406400002100144011881414081c10420250302c0c64100200c08440d585d061882c000d4105450070f03800541c401071641041318050081c4c8091b1030070708100d811824607102c005d9645512503d4111000e00075010f4500c490045446200b86504040b101c00e9660710306280428282070060300710100a50303104620340c040d5240d00c8000030341941c13004400502c1202d140005041c00035016001403040c81340800000c1448064801051150400706501c41202061001d1003400e00650282800084040c0b00150100300c2180f0200c4001d80e06000004800d0b44416100e170030004a075a = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 976342742 1250 976341492 976341517
    0x1e01170903090f0607020120120a03020a0809070b0414010c0f0620040617360f030903061b1e180d030f0302030c1303061b080f010e0406020f 62
    0x10b441200341400c040c0000440da04640c0c540c42e007545a80040c201d280e521051a00d0f45400d181d100315a03910801c1540a0404440f0700c95460b1044903000030b005e5030012210f03000140900b404169030380c50000d00ca0042d107501c10f54241c1418204101c04082180035600c0504000340790420780d02003a0609000c041d1640501801f05103c031700000b100c1c6a0358400c42d441301003440b080000708071890b44202c0041400d2100070500700185c0700c0c0f00c40300c0d866002e1592403d028282070140d2441d81e030b00c02a42040c0291900050324490150004910303101d008030901c5a405070071800004030726040c043d0b860096403460b109418145440740124100c0c1481100c4101c2202c0d400041940b6032140311030755102841d504690071581608695801041c648460b6800e406140c0c0102c0842c01003000130b420b540c080110000ea00e040c540e540e0a190014094081d910700c0649110030000070108c0c81050341f00d02c107c0060302d00841d16442d2120080d20000c00400a581090b403e21a0724192044107000389020a040e4 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 976343992 1250 976342742 976342747
    0x20f040302040b180c0a1716110a05031806040e0a0207031403150d020109270509030903030313020406035f07050a120302060112021e01170903 63
    0x14414001210818000144901c0f81201d407210000c00c13001030198008020300c03003240c03988000d034001e840d10040d480c100f500f036001d400c08101c03080300208540c00d40002999200e001c0881c020020341c2d1210340c801d50281c03468104000004060b520300c60120704103031028140714a802c0e5a2082c01d9075080b011740d148203d03030b41c000031003106045e41300501c242c0c9410404144e528500f0004840900712200041d0319008003614802e034815680594101001000554001c101003c54412840d40c00f43c4100603641800b031800000c112414030000c143e0741e88850103001940340d601c44460049404c0440901242d00c1512501c0200004d4446c90036074a07101e400c0300c0320b0f018000c208681d810201179105d880450410a8400d01300d01107503016001001c103440741d5211034507800351103440750900e00305410094012409480014182443c0c10102d51a64060b41c01d0302c14990700c51a8018050200c070b078020b9448102141d68910301958507280b201000014140304840c5030340d40340170b40380c0b40c001202c2c0400980c101 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 976345242 1250 976343992 976343999
    0x14130e060711240402010909020301080a0b0f012106091a01090c08090c011b060203180d0c080702221e0b03060415020f0c0a0b0105041d1209040f020f04 67
    0x2c848129015002c41010b014808084a1201d40204103619102c10742071a0340f0200f0256401403000e0400b41442c02401c1d0342e00c0d80c6521600b40d0b5840d0640040312030069440018101c03c0c8a100a907060b10b00c0300d00003200103003e07803010028070800180196001741e0b64124410000f07070303010941c2040f000f0004590505625284001d01101e15081d5183c090180042c01c001c001c003400b2034014141032007403c00e209101d4580c4502508401d00d81c60051800e4800800e11551300c5003201205898004402264a45510300c4021611a0000d55000b84502811f014002c011701e404040c260b00c0324054443d4140d00014500000c0507680e0076040030801025106c42c0c0c080d6001940600d1802d5103003900181600d003851b0391040b13a181c00c541c0034031140550214003e50040710810466082004120403034003910418208200b0014086c40742e5485540713800d004610500d0301c96007079110100103801428140d00c0300102842603501186c00207a119544048140d102042e078030181c2140c080300d000b8241c4407400d = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 976346492 1250 976345242 976345247
    0x213060e100e1809030d2a020d122c100608030a020a03050706180c09050a0b060415090308131e03030c060b010e0a080609191e08090a0305060a0609021314130e0607 72
    0xc00889011034009e0128154129048140454072051160b40050002c06600c060b582c07600400c001c3c240c00c0072003e050350643c00700c0050111001400710300c0030049141d4410300c0710b540340f050071803000241c0c020941280200703010b500a0050640189808203001d00d8028200341110803100040320b40d03042004060003240c0507403180540c0300c2040710f400c200e2602800c0014600d8051403284c1c00c1c0791030484202094482c4903000c0140203592010304961540311514070009510018002c1035100b03491036400c003a006e0f1600000e00101d98140d1260102590f842c1c81d0a00900040f01c0b0803414080c00300c042c2c0d24640c44031080500101143c3d40940100c0c1809400142480f21141110701065039542201004c80c01d0404402c107400b40080344241c406001d0f10f080b00c0c01d23000340043c81e580804091400003e02501060f0503102d0070000500700203c5407100c64480480c0a102d2841e18001c80c004c10070b004981d0035a00120320754000400320716980404100c10000e880e1084034142c126006117007845a52034 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 976347742 1250 976346492 976346561
    0x10e1c0903021c140f1906060b19110c060307030902041b05070b0109060e18010e0109202407110306070e030724120213060e100e1809030d 61
    0x4803000c001e000d40100c281c8445a0b1030301004410307103210003207111200400c5072540c020802032a41310080e2b9210040d07a0403616440f815844070344045002d44140403c0d212022400d5200c001d002844542191a06481103000782002d801c1281c0043e600d10f0860f00c0152a40054002c0e59030380c2d0b44070b030b03610f094501d801241041c041e8000c50040d418100240018410300c000b4640c08004007a0070303421082d08050351809003004012143c01540b0f00018401031010089104084503880035030502c490203140c0521001c11f102001c800011441c0c1c05184042038400d900400f1b09600034020b0100030300002000034106117042d104000403e0302411084250300b002c0c0451001000350003100c00e1217078074032500d04034845850500101002249240034403062140d9060302e480790303842c001421607141c483e4000340440a4001c0e0b45885104021000c0840c14403030200115003e80162480317444e0240c400613000d804c00054002e210600080c0a442c81900c0342d4031035840054000060200c44e001d40948025030136 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 976348992 1250 976347742 976347773
    0x30c180d12111911060d090f02210a03050d06081902030d050406020a06021303290a150b0304020d080c060a0605010302250c120803090d02010e1c0903021c 68
    0x1034209410310202490100441803505030800c4c03511240007011000210170303200703010b2902e84013890b00005c0014007034601c2d040c0480f0391003070310750848501500711401e00341d02e00322000003581d500049203440081d110703034060079002c00c800f00b021640588501041d03060a4400484042c14416100c201d8198901004240c0c0700703043c82d0508500d05410451700a4507a10340032000707480d05800185c20413410000510510046802100509032503490908031300f070218041c01d01303040c4200c40b8400309014602d240305000c9502940590b0203400e51030000c1780d1802d03400003001603a01c9414841c882021a0001004196001c100006801c8500d401c1c482102101c5881d005241007500c140709084508422060302d090050800c22420b491101c0751a014a0303980e4160000d0040c0c50501c1d90800402c021200994041e20000c1d0585036034005101c2d04034201e880b0b00c1542c0079075900c10000e03020300f6100300318010304580252802e482000c2e04d03500862088400b0185101c0110746040b400c0040c07010340500c10040 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 976350242 1250 976348992 976349027
    0x9150603020306091f030b01180506040e0a06050405030f040f08160302012a170d0b0904030c1209080d08010510080136050108010504030807050f030c180d12 69
    0x154203254000c25056400107107a4805c0341c00440c0000d129117010400400219840306120503591786580c2049060303403c5082140c1e40070304010116241c0e1400340241800000e03190700410041c401a100ca40c05420003134815540c0e40420403400f003480f001d400c01440501428401070805600c3c00700ea192505034950f50007036000d0000b0900f81700507a846501840e04030003140d2444507404206c44030400b02c0120500007440c8905031a1056a0340741d80001500a00c22892010400d1501c10800c0c0b00c51984100c82c0203000030000c4020000080f03090900047c000858900207481c2600c8865071440c221582c1c100c0c60229140d980104440e00c1c000f00c603222400310610b800c1c0c03015450145295070716803058034041c10b1080c540c031000f40010f600c0640d601c50885840c10501c002d59503800218004c11050300e094000410010028600a010303104803100c402c040c50009140d40d40d411800381050300140e0208038444540d00342c0844030f640d8140c0000d01180100c101c03440b02081950b02809180c9401e42c2d4600 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 976351492 1250 976350242 976350247
    0x60e070903140d0f03020711040606110d080c0d0213031a1b0c120c030915070b01060804080a1803020301050f01060e010c0b220c031113060509070e01180915060302 72
    0x515030026080130b410000d4100940c0f52180ca2415a0400054a001540092074454001203044e03100500c5840c40b8423490503100161070014088039410411903060055034010040b00c0c1e16144180d009081c56807456038a1581a6100d0740c500403042405502002608004401e0040300c00200c80701c1c0102440d0803440624082003192401c6e00d600c2034500c640120807010480801d07c0c0c00500c11a51095801002651251140c1c0400c01d4203411a4030162090704c0303c00300101d80c131070041d5005800750b904540261b00302021110111086183c403c0000000a4280300000050b1000d024031400340707100745000c0324a0340c140f490082800304024a004d042100103031b0290080b5602421040e04001d81c210356a10b8008002c071035039131000c100e840041c4007000700c410020504c001e030700c100702c820581141c602070340c00b07000d1401406868403400b50700c0c0d1124611002c585070174081d2103510303a007010604018000101d0015100d410841c940c3c0030754801c1340c07a40501c52000c0405100c00026007040d007021030 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 976352742 1250 976351492 976351513
    0x17190c03030b0f0d0b090705130207050601050a060507081c0c0206070206091908090415031401060b04140d03030f02031810050f0106200102030130080d0f060e07090314 74
    0x20130042c02c0000103440e041d461008588250801d1154401034030303000c3c0074101d083c0300440da15002944210410340d018040e41d00085820315083c01540119119551040d040450300d80704c845c003541c028100d010184044243d000380039207090181c40540c60070354024140506d41040c0203402c18000034401006500b1800704070802d000c02c10b50340d04440760030440c12901e650300640400e0003042a090302d10b007a01d05029000040054035000d144c11310f00440005e0101075038070030102c42c075400395004442900d01c4584000303440d801c10f0011045854001e15000c900a0007035400e10b000c80e0310560780c01600b00c0d031552560b80094010410b5641021210f0300400041c50509000c2c1c0e504507041c0200010861351000c001c0920480c5905800c1400d1804000c665035656055541e03690300d401060780101c8640100200020554040c5c14000c154020724082c0c500401a00c0c400003c0200300b83ca1140b01c1d036a0100030601000720f2225178414060340d1a408400b5081d0b00345003001c082d02c00481d08142e4000c4c000c02 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 976353992 1250 976352742 976352749
    0x30b040606232b02130c0912030f030c0507020a0b031e04121809051009050c19080a02070b0103050f0c1009030213090501020d05220302060417190c03030b0f 69
    0x111042e50b03c20100440c6044214504400219050340103035100c1c004c0c41000703c052000b648000d01000460702c50340d1b400740c1d0320480400c41c80b044810240201c0c0c40a441c00310728500a030410201c1840e00d150032860150240d00060b005280f079040000280004010003241c800e00050100e0380c040c4131100851140f400340c0d682c110f00841c0114500070440010800d0492904500559021b8500300d1424072441c68000b805900d9010680f044540590400010410840f84c25040b200e071514161586104031580b000d06444584000d03000c3d0005079400c01004000c16400c60313000d0b01862181d23028080c40404407140500d00311030b441c03500f032050301c2124405103415041102c5e681100d606894044007464000b060500030811020040c040e5400007075040040d81e0381e6846548102d00c0010060210350103c201c11034a1081d041d00100503900c4240400c0224040240b203c01f203108024041340f504500030211a1940030b00105030000c00c400141480801d9098081c03440c2842003074400700c8a0f00300d010b002 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 976355242 1250 976353992 976354009
    0x20109120206040b0f0408100903020c06090303031605090409050c040510240201090c140a09020301062007050325050f0105032d07090612151707030b04060623 70
    0x1050400c1d00b00150300e0700032800410071b032001414010700741c81d00c0001c0041480c000d0030f6010f400300e0040c003c02d504940c00d440e200050701c01003030000e4011415580c50044a400c82d4280a0a0301d003800001e00c40c00b00c035a9194041c00703101c0c900c548003038a800070f100d1083c4401d4a2000e0300a64070034803c06414480100d03038065000700710000348446107034500540401c0c0e00404016501900c0380d80404c3d008510200d4220038010f580f0300035079401e941c070760f5030b2440d090490000b0b0203007000049408805212881c910f880000106031100d0640782c0d469a29000685012050309030b1100624115480c0b00125a0046481c1c00a09090f501542e05240d2040001e1091000500078082c02959035008000e1541c40ba41d10100c02c041031148411504100f10064800000343c8103000009016080c0040ca1200b24000c0a6006203d2048450414100714407090511901c00a000c0c02e84200c000000119641d203080d1400f40d801500005107040c10007886006510f840c90301c2490b80e4880c10781341012900d64400 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 976356492 1250 976355242 976355249
    0x16060e04020403082b1a180709091a0a29070203101e143103080903120f061309030903030e0301021c0b03010507020a0b0f10170a02010912020604 64
    0x8010302076008050081c81d081c01c07110108041740c500005d1200a035034a085007166500c00710b88035040091001c9010998050883e55140002c034180d0040040d004240c00170583c00104000003140000088080742a016035603101c2820380b03079450b003502d81910942543c2c3e42c4041d0482445403812280b9004030360340b00041c0c40300002555803030b240055883c040324078040d90101064814020142030440360400700c24150361003180c41800302d100e1700c2d0b01034040c0751021448207610755810003168a514140c0790703500000c000f0318603030100308030000006400c4503203070348102449200785d41581070020500c22a600d4032562140c10510740014138000c00e400c00d0070f07e800c0726418034041d0412089103001c40d019000d041903803185908618110b115000742a04100c040c201d080c0c000304590750358090100c0e0b48480601c0d01800b41032011003ca01003103803420280d42c0c0014030b0b8118464107955524005840c1c4500d46612009407c007a50300401c66a00c075504000421224104015103e40b940001d55a44564070 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 976357742 1250 976356492 976356517
    0xc080f19141801030f0c0f030b04141305190302011e021809061f030b040513030c0f0503190c1202210702040b090c0d060b0f0f030604090516060e0402040308 69
    0x203889000d81c441d40002d05d00c04c159002c20301c0300364007107030002e4040c400c405d20a201180c10840b02038600d050038420b22050b13160205145442e0b88070b84025109070000d000081c0c41c0c0b0300610000c1030310341a41c0d0411031007882c401d50000820000404000001c1c44859550074500c034010003800d82000c6c03081d0309602801004580e40c400689507071000070141ca90b009025480d03000009401811a070b010750208407104801d55052200d50341e0101c02d1103140c0c080e8070380200402d01102500002c80e5146244850b2144500112454141d8180c21341c2482d550624400707000403915041c0d82e04001c041c031100c59030503103140003c04141c43d25401c1601c640c2040759018484d003802003240015940d0b03e801140a004010f01800401d0070014102c11a5034440d80d80c0301c0c0051309040d00042c0c454041e90488002070610301c019401e0080e022942c0344540e1029003ca5481601d035112400031820038000e5241c00c8028480c0500003529000014100b03200600c1510b120b03d10502080000c203018a0490b41c0c4507101c0d1 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 976358992 1250 976357742 976357777
    0x50a0e091005100f0305011406030f0c0903070320120d051c0c0f11030c030d09110a080309120601080601060309210207030308060f1e010c080f1914 65
    0x15000059400e641c0030581c410038543d408002a40c0212100e18240c1d81c03643c080c0410780c0c82c0e02c0b00c8100b440e20200d1854200b5400c10004a8003207c0e10400d980100c10700f000c0310314200d0042d000a1400c00290800e0b150306200c2d0100c03503003040b9001c940300f030b15820944080520340c420001542e00d41401c0fa82c20024400c0c002514404514100b40b038002c081400c800030007121a9014006054182201d5445d010846903000103107094400801d84000043c03100065180001803a041c07800740c08200400c5030300c0c002c00c001a04040d43c80f907600da400f90950320000d64459820030b04101061803840d01d00009504000018010a003001c54040d0540c0c0860030041010500c61400c00d03400344012908007005200d00798004291580420050f080724001d50fa4001c09031210001c020054844540184c2d020302c80c4441140e1003800240c0804440a050400c5410541c1c0b0b602c4008250348038004d071101700d660000303040440c0841c1b00f81502030861286491030300318514860b9107269101c0d00419640c0e03425003 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 976360242 1250 976358992 976359001
    0x6120b300f030415080619270504060b01030b101b0f0b07091a09030a02041d07030803040b07020d021203060f15030a050106050a0f03020f090a0f09050106050a0e09 72
    0x41015010031004501100d03070301e95803841d1000c4a0012401340b500014855804a1480d140007030380481c0310040c1902c0060000c1c500920202040701003011055410001a2484003400d01751141d58400c0303000700004100701d45140001011034135030641c4588a08003441c45210020b50000d00420000703050082040b0700034003801e08070040941528014183c1100908001c4101c1c0d00518103c00c0300c481c1185503040282c0c800800c40c0c0390003a4603016405900c0b2042c110b015103401d802c28007907240c0401c6960402d03100c1500f0a403d1154980041e140350300000144030030041441c1003d54010042d10103011400b0000708025201c0c8501050509200c10110114820f990384890020055038010300d441d40d0010103002c890325a400c21038111009030300d080c0c000910396003d2421945010460b50320344180310031400007070b8004e4102c0380340c02074907180c180103103041919440b101c8405802c01e038103401c0c08140b03051141d0060741c005801040070010107011103084a9046100c100801034100d8800f03405546 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 976361492 1250 976360242 976360339
    0x1401170a020f0a052e02010204031101050a1709010c0e0f01090b030406021315110a080904020c010e030a03061e05010c0803060f040504030906021605090a1e0606120b 73
    0x68982005501c591001200841706001034090303406459201d141600001c18488143c2c01c0b80181d2001070003899240d910000590307c9a0700426080b007203401c02002d403030300402812501d11002c07142c030341041e075440f1003603100547c010102d030700b42d000704440e540d40031810140001e0107450140310354480d00070084040360030448140c05850348081c1c00e4041841e03503030fa07580c004240f400c4261000404901074481701040c5841c01305000004607000035400303240515040501000351f01c0ba0000110556840036044240641400146074001d0556404a8114105042555908001240c1d0b03040504201420007e990300031280c200d8194210360581d40341d64522020501e800401040a40d20514040405c420160403a501d2401e0305e0f0150700329110b64803108001c11103482540110340c0d10000c000c001481c3c1c00383c642c1040e0381c118480c600c41e11498008410708029140207410000100d10340c803c0e040103002d5035224601610b03408503240c0090620300c8180780355000390308240c408145055800c1518148 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 976362742 1250 976361492 976361509
    0x7180b1c0209123027030106050a1202090c13050d080c0a06061a0403031e0c08030709080d080c18010918020304060612200f040f1401170a020f 63
    0x104144259a00005184c0d4064011a00c0a0b2040f0b08215403240e80424200c2440a49001c11034030541d40003040c0c15000d0040c0b0004602445560564032000c01003915150f008040740180030380c080d200c5920020b44104080508000d101640b00c2d00180019204040c400140c1006c60300103840308100801c29041520091285203144000e901c11078600d90b04203c01940020b00322805032001c50509800c6619107a454416840b018000550031300b0f140140104500c600b004920750340c1000c03940b41015988131b904680046402802203001d554003000701680c24003412064904600e000c7c41246091360580105004914800551500c482a100c8a59000e001a0070140001340743e11780480741314140c8a0040c0d8004c9070226001030a0100006262901c0050b07010800d5000100c0703041c8100501c01c0c0c0b0307401c81684ca0301c0d42c0d010944c104060300c151903a2141e5868031010150104818004074040380f041c80041e1300c40203c90543c0011841c19140107d420501e0b5036044908060542160300000d40c1031 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 976363992 1250 976362742 976362769
    0x4080d021c0f050d4b0b0f040603080c0c0a030b0106110705120c030f011401051c080708040510020a081801020f0312010e01170c060703110607180b1c0209 68
    0x1103240020f5007100c0c2049443c0203041c00c042441e0b0140a1001d0101c8008005d6000141d4010024000800c00320302090f4000314060170300030741216000642003000805440682c3e00a4a1030074001504645044c01403040140844040d01c90038411455580c4407818420f0503c04c510800c0004061101c2d070030028012100140002002809045018510140c40b8826a0445c51180c0304001c1106401c08040c01144104455000541026031034041804030107544035440d544014001804200023803040c3c009000c00c580520f252940703d80c100000c0c0320040038031004079420f5500c0540c1340b40021781050100c6244400c207072a0078800050100060f0f01d4a03036030840c9010342c0d02000c10640e6944a0012001d8102c484850108820703076601e840107100744104d1345c030310b02080d00101c03800c4606003444401410400c0c800d22f04682d180304110013450a00c0c009a94400014401c40382c4120801100c0f076811014242c0300341c0c2d1602d8414800ca441c0b4100c0c11031026005a242c000c03400c20420382d1515000c1001 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 976365242 1250 976363992 976364017
    0x609060d05160f021506040c050403080304031701050f0904030e0118090903141c05060d08070501050906010504020a120b0a03120e04051303051608040b0f04080d021c0f05 75
    0x1181002038800d0342d8040305021201c002140c42d4003000c550f910000307800c9008100d0a154940a4444006002c040e0421417180c01c1400302c00c110000000764002c1c01540710741d000c0c1d510b240364540501500c10b17102e0341c1a03010320700c0b5100e000f0780109580d5590740c1e00d0b0341140d070500344042461070210060700c94403150803401600d0b1150f01340025880030603800c00030419100381d07a4011081001e031400c58090050562400c8600d0b941001110041143d60020b5004a80140310100b4000c4035034500c8001d43c04413404031260b0751542c0030300850900c00c0295030b02404007210198203180010000405074508604890308158403440480110388608003c1c101841c0c0101840c03041c01010000900420145000180910716080003c0c0360300b41701504424001d981543e84074504424810b00340100007840c04203942c01d200412000941406090060044d030780c507072091645451a2040b040e05106c10b2104046c155080b2144941500349420103c0c41d480400b8140b0500e0350107071b03100448060058501d034814 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 976366492 1250 976365242 976365251
    0x1d0703030315170a03030504030318052505221803020616090509010902030a0608100b040b04060b031927050606040603260d02040b09090a0e0a020609060d 68
    0x34180d2607001540010a250400082d281e501d1901d40c89824400b21154000c0c0c01644204000a200c2d4201c203410501070316002c111450501e901440d140000720044815520050000d001c1204035040640c1c007105001c01400001c2ca0800410031281c4c2500580a00c2c0e58160f503500c00001072a400010407041c8002e00f0f44107240940f50203540c2e01010307101b800e034410000307221269251103003003500c06407030024089000a03481d02c544c0001070b41020708103400c0681c403194049102c440c100401e031f81002d89000e020546002c100244801c56110107802070045003800418010016002c0460750041c03158030b010b400d5003411029800050090307003042420001000304000c20004605010b1452354010002d42d40c0d1074644404000490701e65100040c080d00260140c5160b100c0c071240725110900b081c100051902c01224140c004070380c02a04522022800843e0481c403509090700010b602140c100f5040120106049005a0b43c4171445030007440f82c94001600549078444100b84c1d9100c042c514824031 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 976367742 1250 976366492 976366499
    0xc11030406300b090c0405030c100e090901021b06040f020603041b08010605010f0804050c09191b11030408030405090604020702180a0e0a0201171315020a0906030e060a1d07 76
    0x14040d060300c03c0ca0611900a42c800b0650032040c00f0121412070704000c0c0145601e0100006005001c00303024407002c14424110b403908a59250a400580704451a500060399414010345410000c5208108165241d2000b02000005620701070201c000540444406880341c0d100c1c074050700703a040049052980062004c07800541500c054006106551090701e8034a01c0c440b00e00000c0781c1d4201c04482c0a00b465000343c440400d28100450047d4018501000d50040101c02c0214541950254940ca00350742200c92814030721950b000a44410302045400503500d050301d000c036500e03034134025400f80e1885040000c02060682d5600d07411600856400740c440400102c018140520031303441103c00c0d0040d00c2c1450707143e111002c404540c40e8425507058403201e00684004104400750350b0010100e0820740250101c400c04500010381d80d00390b105003800d0240e903039620014028000741c03080d4060020b050070110524801d2101045075075000c1c0300c100b80014000c120950006120304a1501c441045c0500c91021 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 976368992 1250 976367742 976367837
    0x1d040813090903030b010828021905041502120703031a04090605070f050309070b0d0207080412110a0f1404150f0e090c0109030f0807060c11010c11030406 68
    0x103190b80c1c001d8904011600c00304005551004088032a03c0c5069100c480840e07401110600c6d1182c00a0100340040c00c0c4224030a0814960f1145007200010680c0481d04120300d446d00030038081070742c0c45440074080c181031540d00c0313402e54014480c0003000d15848180036408550340c40d13003500d05200b00400170b12403d010b40c10301100a001c1a102c250005855211514041340540e003124054071a070300040c0710607440d10394030100c0354010245c00315209400700040c0d00030422440c058405411550080c0c55880024039114a02c4450713081030500900310100c08100300030744844007008554440181980c150313000400140184500321100e01c81010201c0301103045039200350380000340c400c1c00d0040138007902d030100b01660315007082d00f041d80040c010000a100045860104a201034403401c0f0480c1000c0740c9a603680c0036140d03103c5004002441004900e00c03807250901031420107506034103000b10380e100c408013041e45900c03a43c0668018450004071641d08d400c1c00c083e11021b4940703400d0b07034250401d0024655 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 976370242 1250 976368992 976369001
    0xc09020a080f04080a0c08040509100e0a050f040209180610081b06030c0a09090e06060405070815060a090308030f0a1d030d11040b0a020c03161d04081309 68
    0x35080022040340c00600000302c165a80e82c011500090741d81d00340210440d0888103100c0165007200e40d0201400001080e450b8117140700d01400c03400225000140c1400000380d458800200211740d420309040910070013503030002d4000d810540513140100c00c2c0d030300d8414500346201c0b0500e102d0214460803082005806a0001c000107851500341502c04240381c0201006203140c58840e00c40c2d101d5010004507007200e0510b4000c026100342c604210300c0c0c0d240d5034002c000031a005442d10341010703080103040044a18083c403500360303c14080c4c2040300c40c0c0e0826100010180100070016400360b0740c0041e0700940d03036000e2214200150740c0803a40e40c1ea0792a0205a070100c10b8000d58044c0406410480c1b07105500742c000c0c18811400a07440c00a50500f040000410081c3c640030003200020501008041001c0244c000100f402c14020340052140c20b465406251600749000382d1008405846d075420f10001c290180741c003a12821030004c2c5022b5460310b0801c5e10252140c01c0004c81c1d032844040c8001a4030506411 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 976371492 1250 976370242 976370257
    0x2071a0f071d0102100209150403050a0203070f0e060d02030c0a080c0f180c0913240905070905061305040527030f070303020c153603091c0c0902 64
    0x103900e61020400c480b039514416000c502240942c0291801c20307410700b8140d0144c1082c04008000b00950100b01c64641035946c4282c0041c0e0b043e4102820740703010750604200350b10050a101040100c40c0d40781002c540721280000e00554400c402c01000482035580412503695684002010700b03018075a01d86169682e600c1c038500050148035000340310710861500015080503004003412030402aa034100d4000c1041e400320b0381e8194407514609120342c3d56007152060b003101d00013038004841e4102818201c03c031000e0065009138161400d000070801e41b26481881ca404403102510b00036142c08045803171901516458003c00e82144c0340c102000450480c08c503c1d082d5139646031002600061001c06501d850f0b108403407611211250400018000074860303402404101400d0090310740d100101000e20072101000d540948a902c114a43c41030044000000103d0302c101c428542141e814006c1407081c0c49000720034030303144504156500354054284100e10481c407103600102010f81311740c407003036a600250403220 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 976372742 1250 976371492 976371497
    0xb040b03040f240e0303070c0f170f0a12060b04060c0201030207050d08040b09070609030f0623060a0e0f150612041a0a05060a1e05030f0a050114041502071a0f07 71
    0x615220044c10b020041302c0c0a2141e0f40d40d144d9490b440341e15651025544002c04544401b0365030121074888011001526446800114417992004810300003852502220065646e5a150903802c0100503d0383d01110100c9030203080c01308241a06000690013400b0b0f44030003405602803114900b11b40307030303100312180d1080d03220302030941d03c0347c480e0012203030340d030125005510210300e01c281e050000c140d565145403640d0303104038030100e13604805809e441200c0403000e21000401042c4014402c1c1c074034003148080050840b1400040252615201e2403541f1480602030440390ba0b20710201c0300e8980c89400484291102400400c036241c1012320300020291242c0b0304100d4090651320208803d5034030b034000d25010301b4005011900640c01c0880e01600c640a0315500000b00403000e60004036034a0502a4180581d18000a000300d232100e400c1907070a50304054240020745160104200001e05907009820100c00300c01801a103d20f0780380348c60400442080c40489108010318200110b400c00070440500c1400c10341d = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 976373992 1250 976372742 976372751
    0xd03181a01031218090b060712020a02010e01170c0a030b0901080a02042909270f1e120901090306022a0c1c1b0e0108010e070b040b03040f24 62
    0x680f022070f20208100180c08101161003010400c102c0320781c1140042c0000181054500b652036510100303c0b9410100b00000b60b003144000c18103540e040261900d0241084c00e080102800149400c040848000c2030b20341c1075540410100280f92181d0711101440c007002e4007010503561550500390f40c960101008a11403810180802c01198500031051081046440d501c0201c0c0d24640400007103c4005100540f1089150060952680744045041e01c1a440c030002c1d0554500f56074141c0d0030030303452100842d5007030100d01c0303061401c0b8000907840e110b0070080d100381501c40d02e041004982c4c2521940c0b000d401d850003c01d4500c840011034800030080c2c41d010664132009451250041d031034581c071516480c0d100c00400401c1d0303410368206d011074140074418150702e80c040c5103441d030070861190603030481c440b030600e2540144044442441a4400110781c3c00003000c4103881c4c42c01706000ea00c55401855107054010010078100080a2003449929502c10190804d401d00507421940d096290030b280c07040c031800d1 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 976375242 1250 976373992 976374023
    0x2d0e010806220b1b0d060512030c1903031e1b02063102030d02010b0306010f15120e010c030209040b06120a09080c160501200d03181a0103 61
    0x4000c101d26880d071050246202c4105911109900100286400b240c449445030f01042d01203d54024004815401c0000600d241000b06119815518032482e0081340d104002000e80d120002840582c1d1041c0030366008080c082c24503040b0054800c5034081406018a80e290240c5018150402d00c213820081d8844410840b05100423032340c1c0c0782c0c00c1e0ba070b16443c001c42e0700c2c81c4423542c1c100e132540d100d0500d41a10700d2104085140d0100e0701e440e00380d440740401030b59600502c0c032040c60180820760041109140141c2c4403410642580070081080c03280c4802d02c064406031144441031604107140a42e2420002c00ca81200d400300600650b01141460348110b00d00b80307090400d40b5011b030540e0314407e201d911100b000e9855108040051441601c1030b9070a8100b4032494075903d208115046660440794240b003042807410b8000b418840c1011a0810307011301c455403500d8400b8000490841044540c0390100e041c40020b0b480c82d004a62000f001b603c0720b50380049042611115410680c100d9100c2c43c448440000d5 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 976376492 1250 976375242 976375261
    0x30515010c0c1503061e14180a05131a010f0b13051017100905060402030112030804172703010e03180a091a090105060a092d0e010806 59
    0x200d01d140103184041c2c02005004010410400c2c860344001400e00040158071428141140c17034a569920500001d04071307080c4205200f102c64413840400c1a210040403104018001c0100c0400400c1130041d999904c4c0050541004010a0011b10760028000e0700c818140010121400409000c0c0b61113003001030400013516403401e01142c1502d0a0070b20340e10003050810303080110103400b20440300200415100c045c1c540b0748540096138001d214000a00580314500341180055500c001d000600c00c500c103000400c100e406111801030415070501d003512039036440349401a401000c00c50114140800854906010b070440d02940d001140a4907084041442e90410142600c000845400c220303002401001c00d582c00d040d0112400a10003060459001e44445299085411030100304811400c06002074030300741011000140544005e4a4644c940741066402507c6207500703200d03070701d07001d0782084452a11a403c4480c82c40c070b04101041c01c21603299a5018400c12803000e0081980b035002d0200807500045 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 976377742 1250 976376492 976376507
    0x3031a1509031606020a0c0602010c091403070902030a0e060f0603331e06181f0b030c120106020319051803070b0c010f02040b09060304020d06090303051501 69
    0x18002000c0c8210031409468121998201c0c480d600d030103100c0c0c041d0071009444640c3e2004081e0425a000700360a2013a41002c103400070480e4400b00075640f50041080020f80c1c000351800507103036058100d009810001c000f20307141a00d1035012050951012041c03015921050b0441c8046a90007070840d01e01e5154a0b00c0b400000c001a00d81980c1940300c1c0a600c844200e1b50000000e002080f10300901440103984864805010103c0e0301805002c118201c0c0388100030000015504040140c2e041d110040301280000d4001002400304003540040002c1a4025808040e40750080c10070018034580b2400d108149142c43c2d0480c62288507070581071000420068400003c1d5142c0c040440341e0072030007803501341301591241d00c15003003010840200344030020355072010048000103020b60250b0130f079500034402c81c650031544d24940c1c100c21580100410014025003000b902e00c1000121001641c1c0d45030383c0b000030005c0b0181c0500404280c00d02c45000103040c3c03d0381c0110302c107030100c0418000318a8900011640c00 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 976378992 1250 976377742 976377791
    0x809010e2b02191203081e2a0409060e06031b0d020a05060a0f0f0912120c0c0f06120c0f03110c070803041a040b071e06050f040303 58
    0x54107070300c0140000740228030544580c5002410143e02c0784540c3c040d0700d8114100c1e4011030800d0000324480010164000c1c6000d44c00005003590101c03a02030f9400c688004c41000c1c00303849801d81e5113120141c8070400d80c500b50240d10041311000c2d60f1965260115405000c41c1e106065100700c6d00f00025055044c0415800391400c12821200b40080e0801e00b0000c0002010381c2c280e8201d0b0300c80001081903107811009202000c21138036002a2818441c60040035440d910408004010890804100c07142d041d00f04a03108682c800405290000c42040440782c011005c00058241594030600283d01090700c00b0030303000e0303623059076074a552081c07550307608001e94081c424104000b65503907900c50100c5219034429201240c1c000c075500d1070138200541e0640340604a40101145401c000703420064401e8a41e404160750204844950a080c90042120702c14003901c00041c05480e1603502c103480b100100d09400300201c0d803100c010440c50404001140007500c5c02c8508a020a1910001b51105038581e0b00d40c6541c1c = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 976380242 1250 976378992 976379029
    0x3070509040b0109020f0712030203091c120e03090303031303020c0105030f1f1a210103050601061224031a092a030d020607080c13120f0605040809010e 67
    0x10b40c0d1070b10000a000354014083d0310400301080c010400090403515540000b0907240d540541c503070800c0721005050800401d07620b004200c12004942a59801c6075140e2031401054000007103503460a048203046100c0c1ca00c040e40c1c113000010130050405426501c81c401c4501079401c0b180d00780c0c90031005644070b22040e15080340721a20600003c000505002c0e400080450380308070f0180d5103903184132a081c00071078100d1181310b0341c4000c110f0a050a5800120030020031503003011312929450364985a49600d8180602c030100564802148402d08182d0010190003603aa20350200c0702d42804800408880780380021a0503016131a28510042c4002520354065440d180190480c1103008118a520038907802c14502c01e42003443c16804196024446040704800f40d4002d4503941c42d00e00d02c0100088802000e00352101014088402182c041d02c0c100015102d400001c7d08005081e070608205001c200d900003058941440200030400c0310140182c00681c07421f80300c001c1d2190f83c1c1420440c0280110610090307 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 976381492 1250 976380242 976380263
    0x1202031e0702180a0b18130b0621060411010c1109070c0c0815160c030311041815060f02120703090302060c01050105031c080f04030306080f0c0307050904 68
    0x905660319009200702840104103580b035440b00c42220007a2401140c2030307507009a07105c4d00b0074010304010300c59010301c021700e824110f02482c200c2c01c1640407603204c500140030030301d00200243e42c42d160540b001064000b2078920094803281d26640b903949000840c1c00300c0d94421190030303141c1554050710711100b245038030540b649180040e48040c0441381100905a00400c81241d04c400042041503c150b009002164050005400c500c01200455000900020303817021000c0d10502c14103910507100031080d549440c021800000340e801e07039400c13809181c205401c42500c3c84001180d4941c0c1d0740c400f5001c80d128401c1d00727210070364900041d601a21400400030268000c43c000303075400d081c008010300c5128820b01b00083c03010340302d8000c20041d400500c0340c01c421769900d80040c4040e2404100c2e8403094451a0a454680018014000d04c8141e002c2c03e007030f0800c510f103000b040c10103000c1d4002102900d140301c111501c01e4844c0c9070032562007841520641c0a4040c2c2940400d940c1440c480ca60300c140c5e0058402c51 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 976382742 1250 976381492 976381537
    0x201200702040903020c0a06050c060916030b0c191805150711040f0219140f04050108071707020a0b0c04030507050904080910080a050a0615032c03030103120203 71
    0x2d0020b848003101140240038040840c1d030388400047c00034009a17610702d615422500e000526040d805001c3c01d90a60001007a006090345403a4000c06a940c0306502912a807604c4200302c005002d40303024051254228488200042d070b01610300e000c25084010120f0700c0ca0740d180144a0220140076800d000403008004000104074000c0c00302c0e00205015000103440190305090800326001082d54407a4070092112a1030300c2a0300c400240000f000301d00d2914500407508405141600c82d6201c0d5506001c0c4040000782031900502500340109000c8003240158905040700940350307081039038115102e4103900049240e5010300420f540c01e40c0da01c00c00406065060100b000110745005104546586d820044c40703d50351500c2c1488160312840e81c890b2039490516544400c2a101d00402d030f15000c520340b040401404160050a85180380c80e030030001340d00300110500810303018110001100480024001c82c0201e02c00100850480b4040c400c02c0c0003200f119842261280300e4900054540180304030390a = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 976383992 1250 976382742 976382749
    0x6051e0609180a020306070302070311060106090909151a120303040803010504150b040308030709080f0a0312292107050f01030212090109150204180b03010920010201200702 76
    0x15000d903080b8045410740c0000d540060b2500c80e0846070302001940204130301e001c058110300d80d000d6001020380a040e0755814a040140140814419203903015143c2200e0f00031b00c00c04000200845150180a00c02000c4203007000040d001d03185050340c000c4680e0702d406900c1d06008000c2c0c030b008551020be140e1450b4078000411000e04040003038815400c003030500020305002080c00406c010361054110742e07213134035200502414030f020355808200c16403c24034032141c000b180030810344c088173f80c1806d01c049400c844010396802820410300341614403045800c1518040f02c020120b445030300c0c1c00c4610705c40c28003081e4000d4150034060024460340f507100c01c100780a50310302350036101130b041c0040c940107080c078645031840f1051203002d8802d400c3d01d9544200c0102807000c40800490840c0c6240d10a40c5489d1030202444103007070103030714610b014554075507000003035035001c0d04040b00586d000f01070f650301890402040745460241007901d5015602c0c1401c01448a14050004d000d03420741081c4813802d04d0001d4007031 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 976385242 1250 976383992 976384021
    0x201090b0a0e0d0f020411040e071107050d031e0c0203061503120d05040510060803180a0b07030207240f030c020f0d05070501290d0f020d06051e0609 66
    0x89001e1000b01c1c04040c0d91601e980000180c414012988126000031500510046640b040034000050300108010310040e51940b40268122000340350280e070821000341103a081c160942c000b5580704101701030240030f15600284c103200c68030401315005090b810b012000d61312141101d6009405400c1003002079050307000c1c0d036541800c03c0d501809942a0549070f10016a05074805c404c64420143d492040c001801340401084030035124800c2e040000310709100c121b80e920701546a81004251700c05004030131544408420f14000c2044401c242d844098919000c0c2d240c00807030141c0b51a04200c101d803200c942840115055000c0c03031903200c24040d402d5850f0b04401030082c3d4240041540b251900b40c42740580100302500d10450b0341c0d0b84581e15500c00d0f28015007520505240c0c2a1102038220342048400314688050408070412a030315980700d4518070700303069002c00000000e548184072031316220a0206030341025220310302e440c1c0c42e00c0b007c03111042c1b103d102d02016108250040380a20000b00c228038028003 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 976386492 1250 976385242 976385257
    0x80304170a020a060c0f0f20031614030a0b040c061412010902030718060305070f0215070c02190e07030e01230c0f030c0d0c0906210b06030a0e0c0303070201090b 71
    0x40c0c1d00a5075266441d01f1181d42d041ca2400c50f12069415400500c01c01e90082d00305900500314041c24018040a40010380c1980502413401084c0b401c0c488500556806c01070310607072941c80088008030789410709140480c4030451141d000030401c0c035203a200d2500800012600400c0381c01008891907402e2070007050003500014480e100303100c4246141483d035850602c40c2c030014a8140e80105103440c080000421a01d486c0000ca0190340c090700d402c4a031024071210795070b40610381785000f44805805000141040d00c0c0083c8020140702c00620100d0381140ca50200d03849202c441d1400c2c820054022091802c803400c105441d1205503d11190401c1084552403254016200840c81400c154034403020030310680c0b0989034000301c2d00001403003031640394003406008040c800d40c0c00c00030206442c01e00040c10740540b03888901555583c1c0b4408203020685507200c6401d41d100034000548074500184100000d06080f002c00e0b034a8030a940050450745800001c8885844d410307540c400c0064600018511507820001 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 976387742 1250 976386492 976386503
    0xb0304030822060e070f0e15151204050d0c0b0f0c04170c040e0c010915021e15090c0f060f072a0608042d0b01080304170a020a060c 58
    0x840340280b07100000700b0302c0e038940c042e03400043c44400d080c0c0d2043c40c041c006da104c4408150000030070404603814814032540f141c00000003082e0b07149a00000780203807200074040000250081541c2d05241181c098440c8a0307807190b001c40e91140001d280c01e41d1851810000100410070a03c00a03040909a00340e45400511545c0c03800d00b02901c0700640d5040700441a141c48003a0300101000c480b078a440c1c011003518640390301c00342a100300b201c0d0008000079102e0040250314004c413001002240e108200d440d81c40d03840d10142907038001c0003c95003a103610224a1901000100c5808915000e10100301c5040001d8010500c0b445010761230b0905c0713940d80084005031502d2500b44054001f141070121906c90703042c3c501d001c100112150884201d04114103404c45030030844400d080100142ca411425088810f0302c0340400e44852140d01d41262018a03441c2c000e000c13a080b1800003401c040c001018005a500305420500001402e000c41565185078040c0654001c42842c400c00c4254003c55500c4041405203 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 976388992 1250 976387742 976387771
    0x603060901051212041d060f100c0f051912020d080105010e030f010f06081516050c0316080a030c032c2104050a080a0309050f04020403150b0a0f0b03040308 69
    0x1242e4641840d0880c0d48031201181c107646c2c1c0700140d00b15200340e2607481003044440440311005d00c0e010581d500b110342c101005009525401d0418440e02c104d8400003194440b084504074166803007010824008a04119804031002130010310160000c24111070059241d0340d0790749203a20306401161007948000030b02c0d07010b011b1580700116115080c043d6000400c948140400c24610b0240c100e481c0120048512200201c00814418030b01e100e10595040441d20780340480d00c1f008084445411440340c40701d18485c1d10b1003098010100b02c1c006014202000003a141041b1001c02008150240c402c404c40b40d1550300c41662a03201d04520580e41628800d40600407650300720002c0101c0c040c801d0254140d0824020007060420803450244081c81c09043c202001c0c02c24014a60307005081d456040c09042d1040003182000720032174842e031b030549d03004582007000e1070083e81c98012003030014510150308074003c02c040c140102d584007209140c0d40031654503684032495035030350303032030031900040090200098072010 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 976390242 1250 976388992 976389013
    0xe040b030303090109110102030a0207090f0b0d0c030c0b07050303060603090a05070f03122d0513060305091507020a0b04020a030c0303052107020c010e180906040302060606030609010512 82
    0x800142d4801c51190b000000c1e000e542d41000c19000400f200f40c1411903108201e1041c40315808107162045032010340c0c011660701d0304480b914001c1c010b44202385030441f420f060070409000000034140200c034003440040c520b184e1110391001c00e51052450140603035104101280b11414500021a8031401d0581940c00100f5280d450900f041e02e0307039119120840041c0c5050051100d001d00c50a072202c02c43c1880340088210004000e100104502032840d4865540e041c0e40761940143c049400910310070260310805600c4243c00380c000c01c2c1c240e035030004512581110242c0345090300d00c00350040c0d036560020521881c030f030b94800c41d80b1840113104903040308543c500000055400d007520000b562194a4141e01e4140115201d0605014104a020340b5520303801071100039500071688a4400170280790a880c0c4800303580201756944405091516840601c400b000050322022961900a920a609032122520b0f0344080003420f0000350b50090b800000038004000b45d103040600003c24610341001c1e500c44550 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 976391492 1250 976390242 976390249
    0x140f130c0c05010506190618150906031d15040f0f150e070501051903020408060403020c031005060108010e07121506020d0224130507091413120e040b 66
    0x42441000d004561440320007401c101c028007565901080c151b94500c0305412080441440036944c2c4160024805200007194101c000d078941080601071001c000e849140324944020320b1030a040c030819001a1400502002c520f210301c1280c0611002140242034420b59611000105000944200c0d04040355104a0001a401d00f0400318000e010b14105500000201042c209941c08051034640941281f24288843c1ea008000e443c5109207a810882181c030710781038158028402c0341c006007940d02c02c03501004200350340002c0141d600002601600e008503511749004094032801c0d61102d01081c8510010300484110744125503220f049840c1c200009143e01c85c845d0102c84401002c040c0e0070032640d8007484003036010400f01c0f810b01514030090445282082604000e450406d01001c0b094034014040b400c8a0030a40706400c1158108042e142d2041d5106140c0c0300421040031641017001d100c10010f0301d0b81d4000340b0703900f4103541c1103400003c000c0c4c0d003840122030307903085c80080300d501c560f5030b85291401d42ca = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 976392742 1250 976391492 976391501
    0x2f07050318190915081609020a0c0218092104090c050421050f0a0812041b0806070e0915120709060902030612030f040312090b03070225140f13 63
    0xe42c81c1000141a04001d0461451000f80e030490400b46d40070540c1c003120181509510f800b216843d92006131a4154440125448841003101940c001441c1040800098a8038040350044c004d64045400c1c88203075103540505002031480b090440e03e0b00b4002081010503580020404013420f14046180c5600d41c030382036000010316040c00c410324510315000717000c101d003c000d0908405517400c01400321280d150b5030104207104010082040c4803d0740041410408180e5041d00300c0c0072207030b0a4070001a11022210b90307a120460f006d80c005604032003448c903a802c10307180013070180400420005039580120103000b1410905a41d294482c4038000c000214400d141c81114041c00080f40056a44e09021080152888250a80c81919001000b4040c0031145800481e01100c1d8010b911540000c940710302900c2c02145540300030180b00b400000c101607550301245025503407510400c200d80200b0b0080d60404052854005c604c1700b580c100e407040c1d01c54940a400b00e0903262004142000010003030101c9001d85 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 976393992 1250 976392742 976392749
    0xd140403080c0604021503060a0302060c071d0a05060114070f0c05061606150b0319020717070219060f0302160c0f06120b03060126012f0705031819 65
    0xf030704201e040c0700c110714151a0811010640390701c09070039030501c034000400b401c800c0c0c88024821200000c401d05103503400c1c0034100003401c04182c0514452545240240d901001300e80c0200903030710b002c0000f40c540d0b000381109151004408552400e22942d65a5143c40501e54141a100500c2e4130400250355074a2500411500c01036016a044d098a0352800c1c80566040084148420040520521000803d10f098075489040c103850b1041a2060001d108000c7c41941e49c023601514608803040c0c07014501030300600805200342c0740392110018403104005a84024001c0340c00003216a065010400e20030740180c56081180300d650810b51443e503407801501501a4084080c800014200300906500045030031010b030100b9206103c4551001d00103270306c4480500071080c0542c07140c1120b08043d00014000903891929000070880c0c0941002080411034025841c49035980321099181c1051800b041a1940154071031300440c10082107036514043c8044600ea0f040d08011000945181c5008440022000307 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 976395242 1250 976393992 976394017
    0x13060e120a05070617090d030c0c0510060f060c02010f030c110f010e0105071419030b041404150207030c062004180c0c0503030f180102040e060418050d14040308 71
    0x3ca140c807401408541c03500d124900e15a03000e804000b80d00002041c1401c0d98085840c0c002045040448252086024490068414802c011040f101a081ca600040a4803000442d100d0216510740d0110307064400c0d0310000340001c00360300d203000c91540a0b8204484101090030103401c510ba4210295180094400e0b2605150f9110382d5400c10f461000e1044a0700950a0720705290a00403040c0070401c07078400c3e640c400d515041e111205410491203903103d41d0250748014400e000f081000c05110340d00c048241c400740c0d03480c41c0b0b0412641c43c10380e481c42142c0da400d6150325202000c10702511a00c00401030500f14002034040e20064000c0f02400d18000c0c005801102c10545000781e1400c41c071011541d00003102e0051107043e042d1500814400810749920445401800c0030507a07c1d01030000340f28040c0d105080082d8004200814071144e002026031003180b00b81da04001b07001030700c06242214980c0c0d21002d0302c036030802c200b1074205c02e20500c0800510303201c141c0804e203030642d40d03940e070051a4490704a82c0c40 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 976396492 1250 976395242 976395253
    0x8010216060b0d1721010602030d050601051e07170c061803070c09020307020705030709020406080c030c0a0c140604060c02160e06041e090812010b13060e120a05 71
    0x800185100b030480021054450854481c050b948059a07420340c0d0b401801c4c6180041084c0c8900340114041c0400e41c03810320103540b61541d40d00c5010b9900d4021440e500081400e100c00590513505c14415202c5130524420500350310821240311010f00d078082c400c01d41e5030003000b086003400d121200f4001c00100600d107000b41060710308201d013810031402810200400d90000c20400d404112550340940c19110300800c01a500d13107035000c06a10700803099101e0394050045c01800120758071198007070400c4400c9919800c0c0d1b240c0d43c0c140700000c0351004651a42100c5818068140402d200302c0d02e070840c043c0320b0b4030504c00c4401c10750459464880200c0b0700301c5680d515000d80390404c03503060203640914035102c20300041903402c2130041c21004d81c0041041d030081390381e4085074440d000801c46040c252031624a04000390030040c1804401703230b0f1010b802402d1a54a00380001031288102d4101c07080010000340070f016150424400322000c4010044180e4400b080b90340010b81c0040601c035251482e8840c100410 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 976397742 1250 976396492 976396537
    0x60a08010305150702100b0418060f0b0102030408071208040308040801020d180320030f0d054006061502010905010507170c0903151305010b0f1c0c080102 68
    0xb0328014038408003140000703050041c844d520b600025441c01340529100c0102d810800740b804070300100002c03001c403560600c1586501080c46003c0c0e00910035140703600b83c2440742c0320705400160f07038030721440c45103060381c1d402070108114107102c00b072041040c0e80c4114605450295240c0b40c005c4603030170a401400a0381d600094014184a46110b10103075958841c1d800061940f2985002e4030801c0c405004810824a03984000c80c921f00c244103e800399204c07078000d95154140105100014481241c58419180c142d641a88880307001c40a4201098020011008034001d607104100250298540455405440742d1010400004001000c0400c001c10b600000c0e4084030360034900e00350b46003c2c0421051080301040c6081d00f0502c454a02d60210311084065038604208001c40d00d030684c405101600d4181520601010403141d41d940301c86180984020301410a2010070040498080700865500203101d01c01081e00c4901140f103128918020704d11151910f82c2c556805081e0f90120000329202d080f01c03122007 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 976398992 1250 976397742 976397753
    0x1c02041a0a020d0e09062b0305120f01050d030f0c020a060503100605030903070206030402130203091e06010b0315030a050d020109031d0108010e04081608072604051002010605060a080103 82
    0x141443c10385103820700351000c1403408144030203005001c0c5c500401d2000c0b9400c0d603c80b0000340c00b01d40c2c018a50481c03414242d103820018002d40121041ca603141d11244007048090240c004064180c500080000300c0c0d415159906545440700c21006d0130502c2410214032003d41c3c2e030700c0b806500900050715281c2d502d180c01811404084a290000c00c2445824018081048030002c261546a40d050340c4103580c030f48a07400082e420940302c10801504500000802c8080000400c01083c5022a80c90191003004411012611a5001d0141404a000074000185280d01079006021101c0010b002d44005c10b07220b0700c9441c20107442078038250141c3c0d1548050010564400254829400c5550300c0c510f0b030b1056040020282e040611861403000110004a424005401c04848820194058440d03000d2080e291843d03c130317040640190b0b2400780d600403084ac01d11502c082041d4070300e100f207049031130642454100300c003110340c00501404565131110080f6464440d040100250034440e00c95148540c075610b4003 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 976400242 1250 976398992 976399003
    0x31c08311203050601210207050a23060a0c0e01030c1e0e010f02191112070801050f060d030c080d020d020409090221070e150913031101060b1c02041a0a02 68
    0x504d410030150381103003010100304481c1c0c1c0d1540111400d01695508450801c0791500d009202c0103411512021070004180310b2001c009501c07180c039801511255a1000584412181c50808500210701046442c031015072280d4490a90f0000c2c1c0d0074080300070411100d40e40e81c03104440e208203000ca00391845a035280e6810078210b62800c0568030060001c4640f00c0c1c400b04a441d0301c20f00040114545401022080d0764038200158080e451030308681c47d03c0e90701c00255010708001e0b559041c40129100c042103e50400380d0f50b03050015016200c41c1420f18950381d46081c10b41c0448240035000340d0034003014045c81114001840200703140403006c652089640108018000c40034045182805c40711030802c0700362000308000301151088000d1000c1507480d885141107a402004905a001842e5000c10600341804804180b0f01c038005c1c1c1c0c40000600d40350b03440c2401c0710f6643c00b8840a040e03060010010440101c1080003803101c4424025040075075901d2100072003010841d4120811001284501409904002 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 976401492 1250 976400242 976400251
    0x10081608070e1812030a060b03060d2402070c1703040e13020f0909030310050603090a0f081213031101060e071b02150702031c0831120305 61
    0x98241061030300c24019030340e00081c407905280c01d810b00c2c0054440c0031071102080c0f1514001043d80c2108206003000d10890b8001c8911403a4980f8106000c18114118401c1e41d12984000d02400030703854a540340e820106442050100c840905004100310488081c0054040307107200e180714881240c00e11403207106080b07103402451600d44c030030700013040409240c0411681210040c0c8400000d0003290000c0340c4980c8440180c1a0080260000d21540348000401507101c0c014003c00f1401c001c0d00c076001c0100d41d20042d180c482282d4440d60000003c40e02034448101c00d5842a4182403400d440700440040c20f190445012901c020044107075000d144d0401703030031140f10000c2d1008200250621056502010020306108100008038040d8031010040d09040000140c00070409001c0094001c40103550343d11403c01203029005410340a0b80d50540c0d001d01002001b000c1d25081016690104d10a030102400c2482d480c00c80c403c00c2000e0580861403484900300e03802840f0880000444800240aa400250 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 976402742 1250 976401492 976401523
    0x72609091b07030804050709020a1e3e0703030c02100c031b061d1c030213050409080714240f0402062a0d0207060224100e1008 56
    0x403032981c0c090124001c40c1d032415030508105500b62950704006107020718071f0f00a0091380c2e10010f09000c41c541c0103400c0e100c134416030030200038004400410440d45502c070048a13a08005142c0c403902840b800c4035135200307100389890f4501190b68020380f0416140144541c02540425003441040055003000c1c0c1c0341801c03447d000d0038040106016a40d0081075104500d503203110b445c128080d24000c001c3d0b5500f20303140754038800d007440c070540784402d00c0d107034035018044803041c044e41000403007800150080c020780344c40c0c058200604010601d48406d000141c040071108450002c1c003081820b000840031031a90306205d403094010714a0f40c042d003040c05221411a80381ca501c00c0c3e895420030808035101051f06500650541b000d9440d81e800000b0f45404103015105c0407150341080e400c11640c072500140a1400440c154200c450b40365a07540141d8079100701031248100c86e805a84191500c0e15441940d94011004662408040750f9864164401103010388200c100081ca20301c042003044070401c0785c01c81008846 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 976403992 1250 976402742 976402771
    0x2d12130806061903080304170d0605010806040c080c0708190c03080c180d05011b1205010e06010807051608120603010f050112060e28030306090c0e010507260909 71
    0xc81c555414058513220051032032100000043c1042940c00b180c0d000c11215950b855201c070341000100c40074016501401d400130700389900086c01881c1130b0141040012450702c402a45495034020450290712800003521100d804001d9600d10b885405d0010b140322b019990b486182c40603034500181006009880009406000e100202586414000070100143c040b5007805500c0890b03d004c0b40035050510005907142c1c000c4001c0f40e00345401c0005a031003642a0384c1d0810490ba00d440d01d201051005849481c00908804009481d841c015402461805410b060074014521261789003802a44214103910101e800441802030a080c01d009e00503010744515000d008541c1400003c04100704d080340044c00d030b56101c8031030704107218003441283c024030810010907425000040800c100b50840ba00110006454440c000440100501c07510310344000e1a640c0c00030700e1080710b004440750b030171550090f2517007150348180c00c0034030b40c08401c000300c410001c1505903101c1020700104101540f00400c565940980b6 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 976405242 1250 976403992 976404019
    0x1816050a0b0a03090606080d02010e03030108150c0c0d090914042604082e050c0f0a11160f06030b0d0209070c0f2001022d1213080606 59
    0x400c403102068440c8440081e8580c0311a040c01c80c06401c60000c080c01c01c0e0300e401c03404100046e010428422031890380e00244044003101c0c0d00950781e840244205049601302400910700e107021410f0050304110b40c903004506007401e6041042c1001e0851403814085014400b00b0482c41c501d030f002c8d4803800d030400500d200e00c0345026200e032903002006140c40c20580081c030121481d00c100d40425100a0b0445904881e007408814a41200c184170340c1600071026541c284502d1a82d2900b409258490707000202d1075400d101400114414540101c6000707000c0c0081440511191740c42049003002e4101d800d40041a454580741e13000745982580e401031001c041c05c202c08000303d07840e5a81c05182c05035058401899070303925003900b22240340c00c00800902e040d050013044800d210706408040300c42c09600d05181400d038400001a80e4070318050121401d09448003000f0403034031071004000310580301640281d844414105000315103e07403086100691240000505125460081008951110094461865082d503 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 976406492 1250 976405242 976405249
    0x200c0d080c0307090902090604170a020f090108280f0b01050103052212181e2403050402010e10021b0a08030706020304080d02040b030604050f162006181605 69
    0x2245d0181c10302c3d8503000105280d003502d030310003140c00403d04242040c200c1000958820340721591000103070b104603540a03400c4440c3c68043c034914101c8403001d006003403044078a801c09941580305074150141c1c1c100d044110010500101c483d0320301a11412820307806605040024007107030741c00340c061208544201c40c1714403124107c848101c000340c3c00c455814801c0f4541541181c0c51400f101308000001c902c5d00000035054464034070800326014405a105107251104909070340058800603c21704440c0710800c6040e118003a6000c0c0d0340013801850030311488036050700404c08441001074031000591201c1452007004e83c280c00185086401111901c0007030385000e2001d9500c4c001c15070082e082950001c040350800807801d00711100104a00c4056484540e40c1285103d50b4104035106030046042c1b5002680c00c030102003400c5d102d808564800e4042001c6070310200c402d8050380c04620f0501c909e50000491404040044c030348034410300c03402c10540d005044059400c0c9501c1180481294040303000a1040340d9 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 976407742 1250 976406492 976406507
    0xa02031b1c060602030a0201061a0409021315021506040507051e0c0d03060510030507051c0f0f0c1b02090f07050735040e0a200c0d080c0307 62
    0x30551940980320010081c000c20281000e0018000301480e00900161054001c4040c003202c2c0842d400802070b00365180c111848140c4c045545070000c4000308814006081503038050103035804e104020a01075a1a00b1603140c603004014110005a40010090010300f0740750807200d80c0c4198250340030b0000d42040c1001803c1400f440d41d0100300c002c400f5101c1c0d5040000f030002d8522000c0004100c0d0004200f80303101400400c1d182c000c490003007030001405080140240a424010038550703031140c0c501011032803410410a20341e1036020905450b824a01c07040c2c49140a03075107602c06482800111a10300c04006030001c04804449450100d00c22000d0016a8a404015038840c58100c0e0685483e5a0000121110310820300700508109550210b0035070040e035009910440303814290284e841d801c40c0208081c080c09103200e54040030003520001052055030f908041e1013660750b00814005c41020307400700b41641e040b4002c0000554048a000d00803c2c0d8403060440c0c100000000d0146141001a00100ba04 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 976408992 1250 976407742 976407781
    0x52a040b1b0f0a03120507020c030a080a030204090212010f151704030339050f070807020a0308041e0e04030203031f0810060906080f07140f090711060a0203 69
    0x210150010392200001c00c0c00030074500242c0d10155541a100d0f440d002e007943c00f4500500840303c2c501000601620f000251465568200400a0441000b00d59899070154414900310f01007603024080003614891a0000d4284d1041842450310258100b032a540d16043c00c40e4002031002c80d407404840c0c4803c0c3c019207040b0110b100010050700590b510309040c2c020348a0790f03004030088030b801c10030004509210035a03a141a2105c5100c4101c41700c004208607441c1c00303548407e110a2008004100000e10503100070284948080c00c00d4881c80e6032501c82405a130841e0340049030504540c0794200712012603802100103010031400b60001c0b0f04140e200203549020045c40f1181d240d8880d0400c4c080400700150b40f03001000058110f400c4611101d20132006400e01e8810b811101c1d0404170701145010001c01c40180303075108a40203060151a005942e0303012101c03421019004a81c0450050182c4c0f61602454446d5440e038482c0c58505419100d801c0c0703002001011030711018814420711034252880080038510 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 976410242 1250 976408992 976409017
    0x11b0210151215180b06010e011d0103091b08030a020c0102010204030b0103150603021e0a1406030403050a050412141908180f0d0605090d0503091e030c01052a040b 72
    0x1000301146100a0240090404d031840705201800208002800c80b140b0940b02a0b0303801d035220312001c0064411620800400c071a038071210021940355482580505e1610b0f00415034488581107203000060108059007000d6416080001c4030054603030100b0003150842e000780300071841e1034039646480544c1d03a01800014a10341350740219041c034000c036801140145400611440120202c000c038001150701000c1c200d4000c8412400024a500d50580c44994002003e4034091641d95039a400316403a40c04415143d00b846818030010604521580701403002c03905c02c90b2211151904564100e02d01240c10301c44145031001c00150800084504040c0c3d1110340300303440d6042d090390801c40001e00544002d201c10380c00020310b02903c4244151500540e0040001c9019280c000503406002c407414442110b801c982540310300702d810541000900d4080742a41140240c0f41410b420910b0304d0b080d2202a9511b401020a4102c100d02030020034522041c4001500040389c64903241c1445142d1900440261130035 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 976411492 1250 976410242 976410263
    0x7181e050d052d0709020c0613021c1a0c090a0e1003020d05282f0409060c1d0d080315060c0703030215010e18011b02101512 55
    0x2049001c0081904060b10160840402c0e114148128441c08880041007551300c505440011210040e10803201c5101106000e82050303031b00c0c1210011304100344001241c0000038006c0b4004a109610f40c0d2028640c8100e9400c03445545203400200d90f07000c040c040320150340f0100200c0441e44e940c4d07804c8504540c404250218982d0f9505224445403005500181d0024111510355003045004681e0046540c4800032540d081b005041c170070709000c500c0b120018a1200c40341030560102e10045a0544d0a41c03c07446013019100707042c0003040070789240350811500185c840290b0076815800550210041d4007020070309000841160001c2d81d141c15a031805090120004003042d051540035102d10210303600a40f4241d5213044400d40656104030500c0250014050018118204000c1c1e0702c0e01c90480e48000d941ca80b2984400303011450f014440e118000c490341d0b8035030170110918190914a41c403480c142e000780100900d040c00c200259182900400d000840c040020b002800383c83c1c800156040d0460017491 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 976412742 1250 976411492 976411519
    0x140d0201111e100c02010b1e1302070305030403020606090601021506060f040b03100603050103080301090534090b071205070f0b0a0603021201050c0a030c020c040507181e05 76
    0x24100b100360100344640c1c0c05400038440751402c0024900580c00d02d088010014451149000c81c00c0b580e00494107076102c0541d22900c54000076400d4080130940008005880340310800740584102c0e440308504802081000c400c0009143c0c062008540c841029948404903280a00000303450300b04024558420210b040041946900e40030b0955107090688400c09503142d850f0070150f155078004403a40d10382c140301c128002c235101c2e209010b41c074100c961145903a401c503400c100c40003026210007080016900300580e414494100c840304410390800300f9802030505685207080c020019451904442d400c500c0400c070140000d01342460310847e030354043c505a1740340c04140c0341440c50381850210140001c0503000078801941e00a40c000801c5074030803100b01091110780c4440e1070995804594422543e04284880c517103203030003038108030400580e03841540c2803082014001400c403001030752440002607002c202c48242504618004010303101c0080703a0080640d01150740c240c464003502415000c1e002d80f9000d075 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 976413992 1250 976412742 976412777
    0xf090803010617010b04260123060f04050f040f020109031a0109180308011a0f0f0405100531090e011a04060503060f04240e0601140d0201 61
    0x1151415808a051036803942e490320b00070728840340c82e9008035919100a0002603088281e508441c211014501005185201315085541031240d012241440d5501d81c0315015081544006401442c0450302d0002a10b050400901803141c0050140600952808041c00a200040c102050384194080e80b25030741d814181c80100d40040d200c1d0303c0184040000d4195031a030502a40c40d00b8140d901d907000400c2079068404003401c0d00324074104041c0200700c100303005001da040404000600d0420342c520341d9203000c03680118113140da4400c01c504c040c000004503040c003880c079101510390010320103032030001e00704215042c80b1400f1000354071945440102026905107000c1c003205e9000018200f0440820001e01c5c02e804084c040c040e840e0220000300c5003001c642c1418500b5124090036540041c005009950340c1411340c40c0b40040207001a02c2e02e44488182c0b0600c420202e004c1c0e0001405900c005c94452541e0500074503004042e046800b030580b900c4a002800c1d1540340d03080b2182c580902c1e0050040d4200c4504 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 976415242 1250 976413992 976414001
    0x405040f021b0a0b160f12060b0d0203040506060f1c030c02100c0b090105010b0d11042d090b0607030302160c060c020102060a02030702071511060403080a0513150f 72
    0x320b0142003207100000300e072030003103441403585000da0201c468513910030300d0a914802c10882e003940401e080c0003030800d4061150603076a4040101450000d2103546076901e20201d6000040b04468098002081004000091012070340004080d52902440034075840040c2d0341710100100f0b020102c94070303004c1c0c030181489401d0700f81e800394000e0036005102211400c002c01c014101407055480c11140070118030181014031a244c12a149001141c0c18070a03810100741c0500030b822400940c00005020110b03a40c00d0000242d1190050284045000000c4000844c0720440355400344211034a003021480194031400b00301e50b411640b5140069a0f150f20349050b44071140c010308080e10300a0b401e200400c900f50810b6072001060f000b6000c80d109a40c0e003181c448160304c011175207000141c000100800110840d14441c006c29200b034103110310780460010001c0d141441c00c542c02d400043c039000500c0110300365486510341060b0072030105190071500f5160080c50000550300001350310741d90510311185585a500 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 976416492 1250 976415242 976415257
    0x903121b0d05010302100f020616051e190c02060427090303020a030b0d2022050a0c031b110708071404060e011203210f0606140702060405040f02 64
    0x51a540768020082a40002c0c4030900040380101d14048900c00b529010b80c5440f0900034469005000a40d55040561319400d0341c0518001031102c140b00b13900011020f088445075170300090f5151901c0e0045000b071100f200580643d00b02c20300c0b404081800150711184211410303a15080e10010f0080e1807002c410880740c404024200d801ea03c0d100d8103208040c2d050700180620400c80d5424044501900100084803d980c48014000c01e10348004502d08400e255415080b024020f21484203006880346d0003981c00043c02c1e210840302d640e0402c2000340005885802e20000d01c51800701300b0310508603c02c00e0062040b8501d603040c05204050b41e807242c0740c200040d40251441000303a9900644c0c603104e840c10300d1140c1020350305c901c1c24070780003095200b0403201880c107c82e060041040f0142076900e050740c490226842c1961030101c124040111030050307000d5001540680900040c0d110300d000c1c0c00030200d0603840f48510760384600b080700c880565180001d8900341d0b0001c680000e107030a84d00052400034070603c203 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 976417742 1250 976416492 976416541
    0x10903080a2f0109060506270c09131e050c030f0604061509050406090e15070e091314030c030714032b150b1902120f07140105090312 59
    0xb2165620410306401c400c018038407607481030165444503420021041402c11115501b444030419202c070190b1120303100390300300e052030005074988030050000c608628000b051212170540c403088821a000c80000f000100c00301c46000401c010308240d0500f0303445201c0a04914a84801800402c507036550f164020030040c412500600360400a114020b81912003601c1598070817490b02c40c0c001960030340e40c01191003003405c0501030b1034681031030103220b58041c2000d04403100b00640d418101e01d06403a0350099034000c162944218004000e0fa16000d54401540e0b840500150001d0220030000320000090321107450f800310300c03160091140c2c04154510302818468406a002c40b00741d854044e00c0c007a004c0540000c50580a01c01164030791110f0840140390b10500d51640313000c0143c003d0070300c10070000707900302811407040d50240400010550900d4003c03003080341415a00058a078100111090800301c02040c400080c4032171b180800c0c0e002e4070b03405001c2c003102e142c201000c0010000d89511042d0141722603c003 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 976418992 1250 976417742 976417817
    0x1030b03070803040f170c09010513060e0a0504060c020109020a170f1506030f1902011103130602030a020d02150708181b040507300204030b0a1a010903080a 69
    0x1261080005c001c5445078030b20f000c3d6582c1c1241000040411601074401c0083c01c51b85259107440c05201c3c016031144041c50020f507441304e01240c0c070680e003201c02c0d02900220a020841d0306103400c10030103c401041c640819680741443e50f00058882c51039003011140100c2c1280e11b150040303c207042c1003003410032081079180101d1245004860740b4041190040c10107400310ba00c0c10f0941d41846555120b156200d1704250840300c82c40d070042d88290300d11184203040b2000ea1f41001c0c0503c000e002d100115800140c00740e00089041c804d0b065040284032021206071000b4a0352031400b66850034103a034040c00d60380401c40141c00140080300740c00009840755241e8802c9401d4151034000c51014885812400e5214608107008580130a20400380c1c0c5180100004000408044c02181c40350001401040796940342d40a1200101040c0900c0780d10348505030120010440f4240c584070803034480c1c1c0f8507208505000b648034007440800c0382d8100f660007910301c07424109072005084400c0291141c2603002c40001c900b40 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 976420242 1250 976418992 976418999
    0x10e01020c0a0c081b0d06110a09051e0d0212010b0306010e01080615062205040f050f06090c030c0a03060b0313030905010206070e13060509010e010303020d0c0206070201030b0307080304 82
    0x260b280e500b80c060804a03025940303e121094130348034220480042101e01c1d420700c4c00c0c03a1405a0001d1070711440380d980000c11070702c2490510340c079030425101c9102082400700200f24908000301001c408141802045040c9038801000503156032171000301902481c1d0305170602c0319241e0300750b102d03000d010001411505190f0392011000c4028400f4002c0220324003401001c6100620546c07d031000320800140041d0800c0c100c409280020154501502c0c0042142c400c001015100d501c00e03074940070078010000c589031426248a082e01c203006003429020b101460b0030081c28200c500300780c9403c05032407100306649180040c1300310b02411040c1c00000c000003000050018006140c0c02880c0460301c2a215039500b01c0d5100010783e00c2c1d6500b210104042066003450300001d00d040c0e80d0006500300403500002c0c191340c0300c102042c2c0d2001d00740c20100ca5141100f00500515804001c08008030109240412480015a02040090041700740080c107054945160580b0740c0e9080c031002e8040c201d404116900c484d80d = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 976421492 1250 976420242 976420267
    0x120d1e05190c02061e04150606021b03061611120a080603060603010c0e01050708130308071b03112b030201020a14030606070b2e0608010b090a0501030e010e0102 71
    0x86500000403124508480b01c580d0600100d10340348105883c1c20018042d0103407080f0036104040040c0304442170b603210b4025600c5c560b002d104c6c0394003800c0103900074100410880262021101c0f8001d609101c0d9110383d04000201c0e805c1c2640b02081d03461858042c03441020801c10b13501d0003051000b00c2c84203080201d28140440d41c0184124070482c070481c210381413902c0301002d0500b00c40f200d840200c0007641c0320000c5105c0d07501440013010128480e0350501e241520000d180107240405410860380784200049031020722408805c1444040001d1030704000f114a19a542c01350b180e8811002402100c1f2503031114031050700c0e03124940b84c40c120000569a48506441e00034000e62101c810b1901041020149008100d8000207803885440c001c0c08091074042a9120707115151402804103003811860b14400c1d002c0d2402c14400840909820411840541084409406e1140503007160207a10380030302c060382180d078950822030100d500c01c0c00c0010f0340c0032a0b6203402d805400b8600c01801d140d8000100c6041080 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 976422742 1250 976421492 976421521
    0x1512080f2d0a0e1c030809030903010510050907020316020114040b0a18090204030b060d060b030307032105060607030809010209060f0c240a241401030608120d1e05 72
    0x400b1680c41400b01d21a203010460745040d80e541055080c2c000300b010500081c043c411540c0c0080c3e40c8411241010141c0c1c1c000303400c0d00d400700d55959000c1c440b00c0d4104428240111100c0c2c002069001450828100404041740a101140301a0401200b1080804000181ca040741d002d0f1200e00e001994895030050050425041c1c45400d01d00340d41c0302c07440014145814420b1300c05903503006d50806020b840310390030000c02452028040d2030075070351000034110a40e810030042988a1003621000781c2e1014100c8041a819040246042070030309000401c52141e40303490444030b000c0d80c0b60410003501d840e10070726503009002e401005600680001078031600c0b4410300c0042c00301c807020310044445030319501c1c0c40755800d450190420520499440c01040041110303802480840c0c802507440713200c40c0307007004c8010300519140c0d01801c502ca0080707031a134041d946d140c0101e0010b420b440c4010841512951a59089445820f18501c181581e4000c08950000c640d080482c0c25a01e82d0400c0c0840c2c14001050300120 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 976423992 1250 976422742 976422757
    0x90f130c06020f0d030e0c010305191415040b3706090305060109060509160e03010507050c06090d0801150c0f08030f1518150307091512080f2d 63
    0x130721900a80c014128881e0240848501100780074004000c001d10064000d4240034007601000f642680068201912034811241d42c220904090b010508099032500c3d00b00c03500c481e48030700641c205140302025417124807a01c43d03c009206103042e00900084005601c0100c0408460741601460b036000500e10b5201d02c030001a240a4015120141d036203450040480f0100d2165603004100d01c80050061134002030503001380c13542c9050200200180c02c0000e400c4400c211012000700300d0108407541d012a08200c1035038007200341001000181c50b0f000005d000e8600520a070307494803401501c1d100615104003040034540d5403100a83c5903c042510f400710541e001128030b282009401070015540c46042e40c019216414060038282d1032508921503134074182c1d0000c0a03544000b07401541d5001a40302000b251004182040d400100000340101d1105041040d500c94030100e510410741201007220641116204405c40c1d409654498010588006401161020003c00503803801c0400030f00b8980030042214 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 976425242 1250 976423992 976424023
    0x708010e010203150f030a06050406051e04170a03061d0a11040f092706090507050303090604090e070803121906060c0b2a041a0702090f130c0602 64
    0x19003a400503080340011100d480345400c40c01c1528149003002400745903e100054281c0b81d014643d61240000d07610180c4040743c409680703204015040703003c0c0800c050340540302d10304240d013400c0545510303104c40300403130345601c038401e00080c4446172600079070017800141040c041c2d400d51072000010380035800304103c680c2c02e0400d06002d100c4490412480842c0d046e0354000c40d400030390605022041e001891044108104c8001c01b0b20300b45182803e899001940c2807280b00081100441c43c641103007480f0040d4441802548140310210031995203034155070655442c008001208060281c0607460720310154440344440c08002000401c4143c0c41000c2485013500e03002d035102075592081084212101845140d0010303003c03500c66000940849070140d007018402d1042020310700440c0c4928081f001c3d0250000c000040010100701014481c03000307068030007011400e11304213903003600400c030540310003040480107450000c0041e40350341d010003500802980201c0c00c441800d49458010799900b101d200303503032107 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 976426492 1250 976425242 976425251
    0x160302061617070c1109180d02010c051b01140408040312020303040c0605160c060215150d122f0c03070b0a030b04090b0405150901021e0d0207050f070801 68
    0x80c81e034000c503014040b040c00c14010303682d0390351800d10440d40c00140311011a041403150121760116960503801c0d034002c04a00210460380014000b00b186888440a940819a4144582803d04075044025903200400f004440142482c20074035003801441e080c0200c1d036640081034103000c20b0062440c05001540d10030116070300c0c0c2c115120402d9030b50b40030407200105000c03905041071103020300c0384014122041c9801702d104404421b86d500c420a00600360054401030b1300854003030f030241d0070041714141c01101c050001c400c04a5a600030600e000110000501030030070800303c201070789103c3c0c02c0c1c14105c01d1000249910442840c0f0707400d8100118801c82c552a0722031030b83c04041620300410f80404031501071910b5803070000041019009804003c0050b5071080e03031021600082242c06c106107200e00e2040015204440c100c00f0042c4c8504800381a5202c0c90b881800003004d0b00a59040340c2c070013403a03d0b440c0c50b91110714090300c48000c5e02c0780e810018102c1c014500761a5050400061041c2030b662950005d01 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 976427742 1250 976426492 976426531
    0xf050d12051e010627241b060b0f0d26090a05060c03160b010f0e090c01080612030c010b031c0c08030c0408030c010c0f03090c0e060d0c14010e0f0d02040b0616030206 73
    0x407a40d605580c08034261501c01c40704500090308270f6002640031000036000700000d11420002910740c4402d02c0d000e803044400c50170410500070801000c4961300125030b034003a0a0503160004181c001c0058043c490148100103140c6004074010010740c0c480b0790094000019046203494001d03008e070b2080c4200f6141c1c00d2402c0c40070404002c4290f6040c40350b19075100401c4039507106001124580030150010703402080458030103010070005c0c0020800c004252001052010055041c14540050a000000f603c00c64211007801c10741e000e021141da9a401c00030707680c0c032501c5a02c0c0021092189a00040c05e034400041d080001000c10741182c4083c3e82c6684800d070807010300036820b60030b40e00b10750802030510450103014003e4044481c411038100c030014100c002d8618032581d071b058404103d5044151107000d94150b01400b07682c0300c0304414111700203803400d00304003081d140410110010f07854005d21503a11860740d00410b0b01d951094510044540c01c101102032002c5c100039446203016038540a00e147d9105686 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 976428992 1250 976427742 976427747
    0x6020607050a0c2003100501030c150c1b0b04091a0604080d1101110a180501170708090a06062606040c120f050d12051e01062724 57
    0xd0b40301c0700c4981c03102c02c8100344a64602d5001d03004468414065050f611181440d61000c02c281c0c030707001d4050000000c080d4118240304d160f441d5141d210188050031808034210b0180d0000380d4645032944400e03081c00c41d0032000a00e082d1880150007040c02c3d42000f14000070101070a40241814200900d084c00d2541e1015003400403601c541e001d0781c0c1c0c03141d1083c0c14808585114500701c003408440c00000203804542c00341c1084a9500218608001908940329140042c007070b40c5a4200815090900d0215807203440c603c80c0c200100101490180080140020035400d01030003d80c0886922040801045466250b500003001f400861404245281002520012800501c09000c3c98100740c1c0000b080e843d080020103a40d40240007200c54402d81038002c00015402c000c11072070040f040c0c42c0c01340e000021080c2030044031801002c407040e421814842d00307031040e4803500c0281550000d2130512036990f284061003070440c40f1000425040d50a2050018482e00040101000007100c2070740340007a0451007504 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 976430242 1250 976428992 976428997
    0x316170103030e0f04021e030414010c020d031d06070f09050a08102003090a02120604030f050903160807140907020309010c0204091a0406050a0915050c041206060602060705 76
    0x1004140f000c240b2012904d40b05000d040a41001440546400e05400d00301c00b041540c12903042a01e01d01000b88410001c17000c00d41c0081615010080041000f00c1038001d58900303c0c00c2100b02410799850440d46800d0021098440c0041c0b079008959580c1005a001441c9010801c08440012103050f4040355602d0074a0f43c98046600340030082010410081620008000542ca640361084403510140c461440700005544200554005408000c4142c0103000b50800da00340d0300307002d64028008010000c0c1d0010041c0326690b06500d446510360801c030011070b1402070b400340d000350810b4210200003981c1100081c0e200543c0d9580580714140c0b11400148444484140ea080c80075810a07c00110694403901d007000070b0f00d00060010549252a0704e03082e0704032105003645d6100080100800050100d82d0003101d4115230220400c00c926010754807006049001180070a03038941d12035001c10004070401068601a1009095601d00c0c81003034035211004005030702c100781c0940511000980f0740c071700980a = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 976431492 1250 976430242 976430249
    0x6070b06010e330c0d050304050c010c0b07081b0d0b0a0801020403030909020901030906020d0506090114030709021309050118050a0606270306060902120f0402030c1c020603161701 79
    0xe110b80748030155a0001d0074542543d10010700f01038180425110341304208284140100c16440340e17582c0382014107109040c4807000c000541072010759098400081c1c40c20204940c40a49464540d8180e150191503500c2018002c9005000d03c3c00450740c001012510361003005210011104106007555401c0024280d000e03a100180c003089920404124030103140e00200f040440514001821960b690307654000c90300400b07d0b0402c510b648008110301424049009030150104400110b15080c0c40c1d80001c3d55154a401000c00c00d5030003096000702414121b48440103803003410300038820341da16404c05444501f0b00701d01071444103060401080311070f5100d11a60060301d001d81d680c2c040d00343c42c491031459203240901c4201c03c9104034900c0040032410f035124441c00317003407002c00150341c0c1d5890320f0201041080203007800e0071184140c418800142d800044100e4111002e4807801c043c020540c0c0e15103180b524050010350070120000401c411250800310b040c400088544881c1c1c683e4203400c4100005800902 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 976432742 1250 976431492 976431529
    0x6090509041a100b03240a080706030b0111030309010c02060c031b070201050c060705030714040524130b03070314100b1b0715260f0c0906070b06010e 66
    0x104800b911601881600780d11107520b040b101c4a1a944500484007580300312920343c142d5000c8030f0001802c100382681031050880441e84410741034101402c007030721940144661001c2c544d54107503500d1140d003d0403500014442c1e0702c0c10b07a5146c1c42e103071071800c0c080c1001d4000d11006000b0100080c008514101c1580c4c0075140c0c0e1012543c5d1007a920810300d103180c0c130409099051000a0000000001081002e280314007074a55036140c036414110350152804280e0000300003c000140b0052201e5240d45c43c42040b40d00b5412085000c040c00000449450701c01d1448644403a41a5803001c210001c801d0011402003481d40d4007080802118a80d0640c0001c041d11100c0d0001c0b5060420006880c000d4040e0285120911254203030b40010a0b51500d010301c00c2d80240c440d400c0c1c031003c0885460300320b003140740e030540c1c0054006504220084101004400103090705d5034a09c03540045146000004140c0e0024900504096135a04903800d000075101c1c404c550060008250100503007041c10f2007030302c0559101152 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 976433992 1250 976432742 976432763
    0xc0408030a120b0d06090b06030120090a0e2d010302030c04090c090929010e0c0c01060b070f0605090304060c0618080406080711070b0a030c031d03040609050904 71
    0x144085070803100c00c04030954840d4440c0c410303c609541d01d80080501030301c10400090862490b15108035442c0000b40b5051003649000c40d0f0303240c41c040c0a01120900038100d101e80b0b40e28019400040c400450a03007141941500c80010403120580e641e02c000340d0382ca80100c403050b807000c000c0150f944601003400001e401d41c01a01d84115507040c580c01140b07000d40305148000615490741400801c850b80e40f00c00f55540c0d9600072400d42c0d00d0590700020380741c03858604081501981003100020050307502030560f034030507000001d081030206c100303601440140c80c0019045558401509040c013010200034801da80b02031910000c00c3c0c1078000002228203ca40c26101d268800c202922014000e000300021116121141500c07400081c04d4a0700400103040c02e92254221814407841c001c110f0000368031040003640c071040d018000d4000403030544807860f4030341c0f4001c211142d01c99012006054800d503440c09204c0b0710581000d490602001034002c0d03651907580d00c1c40d03072903540040088032107060300d002c0d10b655401b = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 976435242 1250 976433992 976434007
    0xf03060909084603050f070c0212070e0c0903010c0c0302100e0106171507020c01080103022b0302010209180f04061d0303090c18070f030b0d0203120a080c040803 71
    0x3002a50502c84218001c4000d058001c00c59003000403040c0c0303042da80c500c110807510000180c041c405d50b5000079003650010103901c0d00b044090407000e01c07000701034460f001000401c0c00781e6070b0411610707010b48a10b6021104c6800c00602600ba240c201d40403580c465420700b43d10f1200c461040c0d501f0604150103a004140c81c0d1500d4114200410010b2000c1001d0354a80c0000300d00740d06c5a03004020400d0700c0d54002c00500c0441074200003d10000b030000d40840d041405052501e0307a01081c00f074113698046450351012403d15110101c400c01d02c0d5030401c800b41071104c9003c00c0c0760301980900100402500d03041542040e41410741648081120720301c2d03183e0618800704000c203803154041010b4050000522002001c5950340c203285401c111788104090384034041040039402c1c00c1000c400580494400d0001c43e0622100c0501000624040c031400c05580740d01d111030b1683c03003e89180072585c000c2e007540d2100b030400210480036401900b0325400304540354041a991f079184800c8a040722010000346041000c0d = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 976436492 1250 976435242 976435267
    0xe010512010603050910050c0409060b130501080a06030b1f0b0a02030d09020f130509010c05030f15280e0c030103020102070308030601021e030901080c130303140c010c0f0306090908 80
    0x74064044070446c4980381c4025060171462259601560240b00040d480b0b501d440c07944000c0e90100d8100340401a41480745044880201d13000d04261a0242044050750323035081c600a00502c080e82c0090712407029003041c407042d09500c0301c010005000e45c81d440907100740c40700e00c05942c0d48900062103005900400450052019513488801c82c07520060074942d5402407000050414900c100410144983d070310b00b400a51002449006104409030400604503d8000020710000c480101404a607141e0109031000381d41c0e0380c42c0c0c00d100043d1a642045c195940120444550003080e008414041c0808008142c580501c41d041e00d0489a059006024050460756520441e4002420550542c41786006032005c02e480b113145903c010f41c010000f10b4440700300394001420540c01412141c1203500c01c20141290ba503045a096003070326013606140d01e054402071405013641c0f0400546840231f5281100b0000900da203c5030351400d91100d640c05010b642d803101d0703015080390341e41e1900519a90040041c841c0841c2c = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 976437742 1250 976436492 976436501
    0xc0b0f04111c08090a0902040b13230603041112031b012a030608060703021c0b13020c10180219050105030a1a0a2d080a080708280e010512010603 64
    0x1c001526601d2400d1b51020303000d090b40c00c903400960052201003000d4000b40f16540f403000c010060300210f030380c8840341c0c4000300066052003091a4003415000001409001100560491002002e0b280707400140c0700040e103d0b107940001c46000f52075104400402c00001d0140100d06401040c2d00310805000c158520100040c40c505460b1ba013403503200c2c200052202001c1c40100c0c1b0605454401590740d4120852148014002d8580c600c030325841e200c0c0da900652211012a020446110340c010f80d10713442e42c6800313460001c09055550000b03043c4004492194411020040002e2080d2180081c1142da041c00030800c035481c3c0590383c0060002d200040301c81c10160019000b10441c60707144a40e16492802040072a00b041c2c00900b104d4250180d011400a1440c400f4541a410082801c0c1c8442c14400d12a8480d00d0015026088940100e0103409002009080b600c072180c01581e1008101c03111070300b00d40360940c0d41c21030402103801a08500415401002120b8483c400e1480f00022a03080440a40051 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 976438848 1106 976437742 976437757
    0xc0405121c050c0102091c020a06090b1225020622080d02130b160b130f0b0702100c05031014090f04030c0b0f04111c08 53
    0x38800060306001c401c00c0c51802941e01c10705203c02d94068019110699030002c844685205c035942d418000104191080e00c075a1500e82d43c41c0000d40341210b0700e100b0311302000410065083c64040190b0025031107080d165000e4100c0c0342100349112040e8060f5600c6015a20540a004111012515008410744d03040c50396a040c3c909540d0f55a02400358840b2010926008681c8034506090600820040c00205010030f450300d417040d09104015496841c01e580b003011000c0031400003022500c14001250b04000c0060707040f440355480d018500c5009040348118000e1506a40100c00c9600171581c2c03219881e516680c1783c0c20122409500c0c1006903003c40d031115640840c40ca903035145d02e03003a5a4407810001e01503803696203e080507180d0350800240104942440c804000310800e038840f4150040b4014001a0741c454105024084035100b000d10a4540d0f440c1e079411240041c0c4d0020040160 = true := by decide +kernel

theorem cover : BRFrame.Cov 976258992 976438848 := by
  have h0 := BRFrame.cov_init 976258992
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976258992 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976258992 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976258992 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976258992 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976258992 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976258992 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976258992 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976258992 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976258992 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976258992 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976258992 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976258992 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976258992 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976258992 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976258992 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976258992 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976258992 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976258992 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976258992 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976258992 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976258992 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976258992 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976258992 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976258992 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976258992 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976258992 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976258992 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976258992 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976258992 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976258992 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976258992 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976258992 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976258992 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976258992 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976258992 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976258992 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976258992 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976258992 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976258992 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976258992 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976258992 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976258992 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976258992 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976258992 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976258992 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976258992 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976258992 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976258992 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976258992 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976258992 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976258992 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976258992 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976258992 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976258992 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976258992 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976258992 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976258992 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976258992 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976258992 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976258992 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976258992 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976258992 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976258992 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976258992 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976258992 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976258992 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976258992 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976258992 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976258992 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976258992 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976258992 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976258992 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976258992 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976258992 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976258992 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976258992 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976258992 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976258992 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976258992 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976258992 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976258992 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976258992 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976258992 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976258992 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976258992 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976258992 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976258992 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976258992 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976258992 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976258992 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976258992 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976258992 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976258992 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976258992 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976258992 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976258992 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976258992 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976258992 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976258992 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976258992 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976258992 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976258992 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976258992 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976258992 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976258992 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976258992 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976258992 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976258992 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976258992 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976258992 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976258992 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976258992 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976258992 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976258992 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976258992 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976258992 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976258992 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976258992 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976258992 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976258992 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976258992 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976258992 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976258992 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976258992 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976258992 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976258992 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976258992 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976258992 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976258992 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976258992 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976258992 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976258992 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976258992 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976258992 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976258992 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976258992 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976258992 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976258992 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976258992 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976258992 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976258992 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976258992 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976258992 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976258992 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 976258992 ≤ n) (h2 : n < 976438848) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
