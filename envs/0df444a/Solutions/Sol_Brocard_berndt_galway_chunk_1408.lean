-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1408
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T02:50:21.454601+00:00
-- url     : https://prove2.me/submissions/c58d7163-4e65-420a-b5fc-d0c7d9fa30b9

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 253057553 ≤ n < 253237410 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 253058803 1250 253057553 253057579
    0x40e01090b040b0a1502210405040e0f062409012c0c0405010c0c05040c02240415050a180c140619050903100c0203071122020f0c0f06010302 62
    0x2003030203141c0f444800070340401e103c035150054002c89601d02c00f03c00400c500500060480580c1c8840d850b03070074200c0018205441d0307402c000c04c101c210340c4424031620381c42d8010303a64000765030070200c0d442e64010304240044402c0f003241e401d0014460380005145600c200000e001190841186000e80b5842003e102906035401d003860424210002c10380d04d006000c4000e000801c07056124810501c0c43d14480c0011440681c0e40d00d000c201918010303107120380540c100e100442c07005000519164198000032548042604054407032411102481e80c002c1c4c51140c494000032000805904141c541d0b44445110f520300c00c059050a0070815854014088140300c840001c02c4603103480380503140702030840c44241c03403210211007090307419034405101e00d600350140c103c181c2c41110359403160300070700001c070340255030756403210302d1300032000481600d4427072058039040c07481044040c00700e4590003070101043d401a6035151181d880601405200c0c084040352158904900b81c0340004a000c0307040b27a10944400c019058 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 253060053 1250 253058803 253058809
    0x30f03020a14060f0402090c070204060b07050d050f03060f060c0d17060d08090907020a0c06020f06180309010c0602130f08060a050705120403140a03050f0606092d06040e01090b 78
    0x40a42d102200d0f4804c0382d0100d405468502c0103550041e0401d418149401200c0c2e000c00c0a460701c0754020743e0902c1c0c01040c1c29040c040c0521580c80e4100310740c43c00f10f2800d00040ca61005070300000c1d004500cd5012003104200c141c90300c004842036458610125084907a038110010105440007180d420290b02c000081544c44c1081006910322582c0140030b20b0a0464210238040343e0507004005508511480e0510030200709070019010242400354090082e04440940d080d14064014142e030251800f5100280f010800110030740e100d1031000d20f00003401004608207076019000e800407104031071441c110001103102c00c0c81c405c0402c5882c018240c034019035130007100703c1c21518102e40d140081403007080b03860340444440c84040c1c3d01a22a06262500c2c00685c034002c1d034160042060b074804a075643c0d05101914051001c8207031310070012160749142c0651071b80842c0c1450b00400c44040c2e40d80c0303840c680349036000c2d0042107412043c070050902a20345660f403008d1011000280b00b0041901d241251030500b900b = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 253061303 1250 253060053 253060063
    0x20a030b060c030d0b0301090f03080f071d0907110111040816030c0b0717030c0307030e0a02032a15070215040f030807020303091003050603150f0106030203040c030f03020a14 77
    0x2294210181d4240360524403904c1c064821401500d83c10755942d0705010000f40c036507640f0340039a4000d80d12201c1c180707000012864071001c0a007549d03013440349004603200030312410007881c0d8420500355882642c64580c0d070005d07190016140d001400b19420b00316074060b60b0318840003070021100c038203040340d008460900b51420101030a020207043d140e20136400740900d51000c00203090803407280380c150301c0c40145d211000c1281e41007034503032030340101d8000140300c540d551500a80408020b01350103000028201e82c002030791201c442d800c040700643c0003005490140d40300140e5900100028100384218051052208065030007140100d20404803854401100040720050300c1c00c1d1a00150f001003014115250b5081e5504204001c03030f03261000f0480c020098032602c030500d00f1140141c030082070600b1b180b0109410011074a0f03407102c40b00c3d400400c101062503903000c9a41154850f00780160369403038070b00f0920307444019070300702410180e818501101015400180720b12840d003e1644003880100c658940740e00e031 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 253062553 1250 253061303 253061317
    0xe19060506030417070c030309182307300c1b0201030f0204090e0a0b0a0b0d020f060403080406081f0302060703030506010509030a0f11090f040b06041e020a030b06 72
    0x105080c000100007840c044104c2c00005400c0c00c41604104207030744c1e14460031901d5042200001d809113000c1100000078840400c2c1142444da080c400003c50f0801200f03500001201e542c980441c8401161104d8018000c0145501d0350305520643e0ba45520808c03811211404450070445180500c0c1084051003611400c0c0a4111803d044081e1141600110041c000b20045455070b9582000002000c0da0306d413041c142c403104024040d14400d5010b08141600a400909445000d4100a16030034035589022006030819412500c600283c42d200c00841c8860140e41c100800070200000c0100342c407a0000b40003845240312141140002c90030f00305803800c00700d041c840290801c5003880070f280028042e80155034024030602d00941480e10110001c0e02d41031829405036200c900355880e01007803205000c05000d4035881070780c10010f40c1c00c1c107051001243c02c00500141140340c101011803100d076940d4000502c03204142c44025a071904048455009510000890000c46e1404100d52611709111040d0703105 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 253063803 1250 253062553 253062559
    0x3060e010b0c100c02010f0f020310120c050402070c140307030b0a0b12030d020406080a05090712050312012403150b070303020705060f010f0906080d0c1b0e190605 72
    0x26991030100c888609801c03002d609800b501503003002c0c000b032060a104c0d1000806540d030000c119401c42130204c1c0304030b07010340c449540128010010081c108003200c25081c12a0404140042101d8103800d2070340d0302a9940e00415440740c00040c20805100e00c452065080d07035061101900054021307001c0540e6500d1902c0010440200000082c2102104e41e20420118001410003c041408000f8590540c3d10820240d0300c032a902240a10445600c880e1444d84058010020411814072488882d0341d101c4034403529401001c84134075001000801d02c20707905074510b00b00000480d03584407441d0305000359840305804580e000740c0c45101c2d4101c0c82030246805076442c0141c4000c034030341041c0060480b54850082034051503002c200610000b0b208100d15442010203030740e054010350406071907042801c860b80c0080203007401c02c081441100703008200803002a005040c508500d0401c1c1c0350018003034407940b0003d8011402c4901c0016100c041854680c400c0c103001c0e0060b0703858100c0c414500c0c00c90780f56014007a0 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 253065053 1250 253063803 253063829
    0x140f09030f1f02070302010b101809060807090917070605041403070309030b1f090507080903040609050f0a180902010806010507050a2306070e010201060b0f090108100f140306070306 80
    0x41c2c5000d0310b030700414850b0b02a10011488044881c0410001d142c03400020001070820310405100f28408082c060181080078000d0044500e40340e401ca50b40d0b0382c5400340d41c0103659284844020059102d1100356010034000505e900c601a84c1082801844101da0a50b00302400003170101106a0200465080951644503c0d441a0858481c1a1080070003080c13582401d1002c0100c04219080d040340300001c04200c1e8012440d4a1702c080010300421021340322210380d90040c0414000c054103e1030f0b84041d0f0324103070350100c08205258009810340610745c1c8415030342c900165810050b2140e90304140c50813130013030702c485c40c880e19800c00440740c9202e4280042c040b50441084207001602c228001100c5c240384d0b0540c1100300c540070075224200071b011345088001c908942c58107012560203000341001800072141650810701580044072140c495080c1c1541000000b0001401d000c4105501801400411120381c2c6942d441e0160710075220794030440304d44244502800201c0b01846801000700b40c600000c0b060f5 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 253066303 1250 253065053 253065103
    0xf172208160b03162001020d0c0c020102030d0c0306090603030c060c09080c060318060f0f010501210b2407023a1518061505030715140f09030f 63
    0x6130141d0031120803000c00841007080b1001e010454840052a05c0100005070340e5500300440f40b007111100e0006c541480220486100940c0e008825181c403413a582d000440c600c00c9400381200146066003008410918020000c8107060b4400440d002c0c8030f00c111400c0003021070588003503550306290710865031994458042d06600303003080009150012003411004042250381580141460403c4806024544d81c010800c208543d10041e40e0703004123000c3c00c00c42160050401c004040c165140d061640b030320b07140d10643c0e441d0744881c0410550440012084080c00d842008140755650102c03c080e4412a141103056041100c0c4295086800380d58006405c0b0540c1100505000960007550944c1c01c190040c0b04140c41021600900c80d2010315020740401c054030502e0070f501110101e150007031040381c500105100c980c400080c0e610541e08101150300e140c0d08401022241c1001221403407070341c00c4011941040d004040e0000d4015044210150b603100742e0007000060381c0d404400c0780c20307454450281c426 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 253067553 1250 253066303 253066321
    0x506030601030809040c140c0c0a0b03070c1e020d030e01021b03070608060d060606030501030212030909040311031b010b1c0803130809090f0a050105010c0f172208160b03 75
    0x8908030795040c140070300b00080ca0308010f947d9400902e004d0b10290000140204280b42c041c64003c0540001d101e01e5086040c40080100074010030440246039035041da151183c0409440c0310004090740c02010034080d8261860018014004010702d5030143c4160405004088401c005e1846001e001800403d50707149002c0c0121060240642074903040340c42c1c42e944402107101400b458014150a803004541c551444c07060000400004580e28220342041c04101d681da0b40710303041d080d00030350145011000e031a14807803218107500c901480d40d4a0348502c0c221881d45035a064100e003100d6041110001c030380007aa07105450a8100000d0014004841040090440c03980c4001300020309010780c0480b0b050500800c0401c4c2d00500903502103019550348010481b00040f14000c490241202703182030700c0341c0119640d4030b8007001e9460038000d09060000e101a03000d440000c06964520a043c15000c01c00070b001846001040d646004113000b03405020207003030506100b400c620003101c0b4031f503001c41d00c0c603580c00c500 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 253068803 1250 253067553 253067561
    0x110705030a170c031201030308010b030603101a10091706010602030d0207061b0305150301110f07110907080406050108010b010c060903021213090b0a081f0b091801050603060103080904 81
    0x4500c40701003041c410b25201243c10009810351010718800c000455040d410003521303294051b40041a00b0b00c0400c20484107450210715038900380ca01c150041804140c001002070082c180000407508400e6030010b10340302030307802000942100c4100413094000c1c50404110354407011b0901804016034000c0000c2c0d10401155401042028040ca20000d004098000440d061141c909101300000c2e84900520140928145040c0302c1c007c001c400812016480b00407850442c0500c0580001101020030401c0501040b01180201c501c8c0c0241002c1c6145810400502a060103a5003078030340d00d28200010a0742e0005204000440c04143c455403941801c0fa61018080d1000e04c4044003103010314001c81c1c520f105210042c004001c011681380440509298403403088605003600544540c41040042203c40070200380c4940c4842e62128841c1d040c40e841005038040c1c401c0d043e800ea0410910000c0280c040e601c804124101e5580ea0b0003440315489010402d580c4017800e00010740f40c40c0b070800081490b4641648 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 253070053 1250 253068803 253068833
    0xf070b06040b2107030507091b0c21030917281407020d060f0203010623090d140307050606090a0b10120e01061202040e030a12110d0e010c110705030a 66
    0x11240c009841b5515141041030035404100203580b205a5003002400704490490100100d241480031510b460f25950a81c00d8401c0300992601748014244000078481d0308510291074200b04158400d5000300c07a0140c440d0301c02d0b401a21568040585110858100c0c0c036a11100803060b034801c40c008400c045a2040c1d540941802c0b60300004140703c100001d100c3d4040d10040b070340440300041e141d43c50890040d14142e08400240000720003402da00c007030091280d080d03449007d0151740341c1c86400490f10707000b03842d82000150103401d44000300d40c0c5c00410100058240c41541c0956031130b40340340c68410f41359003601c940c1001b05920000c102d0181d201144100c1c0014115540e1721000f017880c0e8241c50300c0c42e08481650700a41c480c1c9001c4550102941050b00880740d1181100000b1498860312a0005113051444005240e0b01d80d110a41c004059600c0740a903004007c20034010010400124400741c0203080d518150400702e04150400c220408004c6006030844078058080d0001801c0b66942e0070a0000b511 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 253071303 1250 253070053 253070119
    0x51809130b0405010c09050a031e03031503060203060a090203070804140715021c021c03090f060f14010911090609042012060a030c03080c0705060f070b06040b 70
    0x1400c0c050105001e0305240d8042c900900000816000c00003000b00700407540d802c080c0c02031032000000c0002840e428000c06184803c00e1408200b140c951a085024008482da200076256480d840801405501e0780110f024080895002c0302c003070303030b0380d02001c069000c01c448150121745210002400704401c07100c807007072008001e005e0701c0b080390b00c40074220901100c1882ea440140d00c038006071581c08003000072081005196000400640412420061071540c0d00d6100c1d40401d5228402c090030000c3d4003915171021503000c2400d20480c901010104010b000900100f03484910420000805c40060300c10605c0c80300401e00b1407450040c51b03806100c21a40031400d0290060750b42c03064a24101d440c81e00b9003580305030400050342d0380c4080741c0b0034801100c0040d040c036100b9900440e0800c00038030092400b0007129030020b8855102d02008501c141002110b900c0207800140001f00b9001c4010600018940030b4400e03880400c0079114403061004644c804200180c1000c0c2604d400000003181c2260a4510050710b = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 253072553 1250 253071303 253071331
    0x1509050a0f21050f0109050f0102040f060c05010609021b15041707080904020d0b09070201060e04031d120706032009120a1e020a06050703120519060b030601080601051809 75
    0x583d50f0902d8068554452002a556202c0903c2001002c0c0450f00c40700744403c000390f04042c10440c0b85150100b041c480c007028411034a040008000b0300f03402400c01444804021516004200410008183d400016015500400c00c42025003248800742d0fa00540e000528108010002d014110031984104800d03681800140010f048903580e500080c40c030100c94120100e48003400c81c050107610040604102e0540e41804d6040c8000040001d003142e225800d403402d2030462512031503100ca103842d0884000d402c83c1800110300d10340c1400241c000304641c410b5a0412244480031820952202c0c2c8800c0c10030240400c02c1081c2a034501020a0504042e0b61016200099555138403848144680c0441111684009501900790700d0b0005c03800c4000d0031581415480e04640782d400504200b06108240c240c0c40d0b40c0d80225118036080d640c5980d29800284c000c00800e5210014400643c100326219400a810309000800b0381d441981900c40c400454403400080245100400c001504010240c4502e80d1607 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 253073803 1250 253072553 253072619
    0x803281401180207080c030706050c0a020c0415030506090d110d0206061306050d0b0a0627050414070602070f05060418051906030803070809030315090618011509050a0f 74
    0x204004200b00121b020042d560b0302e020b8035144041c0d520041544400c4141844941000d640100c0c0d101e012010807180011070468a46c64101d44510700d070030140c0f0f240300d20810040340c10000035206a44c0c08542e145c1d1903090711b0641c0510b0ba240040311701c040050700705401240e4981441402403112204420002c5441512040441d042902441007520142191018009415424450030004e0825000d1003c02d10406082c1034010304810084065007643d83c600140c240905c00c201c48a00b2256001a40e007000d690b030340000d41e641030500641501300708000c0e0005e110303e040300403542180e0200380400380400d8a5100c250003030100a00455801c03440c0c40209996041e18440d02d006544035010700c035142e003410710000703080f9030009180110300d920400c240540404550040c1ca44007404855440850ba1481d010400b407280d07141e507136000070030f400c00040340c05400c101e5454084956680c4000010755510100803c3d00701d01d1007a81d161000000c81806400c484040c030b210309200c40810f0400c0610 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 253075053 1250 253073803 253073813
    0x61611011112100626090c1005120108190314190903030806011706041107060c02010501030203240403120b0d03120b04090c0509130803281401180207 66
    0x31000030005142c02030502000001034885440c1e0001d400782d4a841c140031014280742c4840141511038040c0c0407a00d8800285420600f004100c684040142038113a00001800000d03215030801d441810030729182000101d040707440020390f00e0300b40500e4241d2640f0609030352002d0320f0103050612410340022007000400c10740c20b6002c400011405441d5a400003151450500a281b500d001e003500e8104440d200c4580c3c183e0760716800507034101100700c07400600c0e91401c00001c1d5092040c110001e0106091154018109070190300c818101c0c0c3c0240c0540d03e80019108401c1074510740604000a00c1201c4c2000c900400d200700e00301c2c442d06810724400103c000303000c40060260240c41c1000c60000fa0719a00781c00d5005180d01610500c19803e0b40c0034850309801c1c0e07640c07407525182c034019140580324110018601844000d00c0e40e403180c1d0851810f560302e082150003d0715203220003004030b45001c0c0115600079468003d2044041102c48001203204036420240025100110309041c0b040c601d400b8001040461 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 253076303 1250 253075053 253075057
    0x30f0a031404091503030306060e1012020d05010b030a0e150a0f1824020418050402010e090412020d170f07091d010f140d0b1306060b1b0616110111 65
    0x40c4c0f80c80d0f4602c1c0054035524005007555095046134003003088500041110b0b450303003240c0e050386c410380c0e0801445409044040c10000e00941e40302c2c0300650f080400020700f418050740110b0080301150424007009501c0c2c000a43d46003028200300d260711030700100040101e0031540c0150180c0c08856000f14011001c0b00f80800141062542034852412a0320f0510740382203204044843c600b40a0070940c18185450b260003149000c000a0305d100d540c5820004045a1064134411034040e4000c1c003003844e40c102401d0507040c3c0041860301c031002d0301c507020030103140078050010320001307640c00444080155140c41514081c0300014050100b0711250302c0c80400c18181003041501034040f1102c401403d0740c582040f4903c00841a445282d03011094500071066403511500c8481c0e440d00462250300503154440340d2424003804150140c203c510745580803446821840040c44100d0148a02c100c40161521246458a0b020b0710360345103000501070040000307401488400c4110b814500006010010303400040019 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 253077553 1250 253076303 253076321
    0x608010b03070503070b070303020304060f020304030203070b150603010b361806060f18030a03050d0b0108090622051506010909020406080c0c030904060b090f030f0a03140409 77
    0x503511114a46414201004040020315040b802801c5051501c60f10502c64410102c2c05020190000006001d1140c03e810440301404400011540c070320701420300940b6078008060440e001c2151901013188080c11001d10004540018201407a503403070a0100e610550210404202d2190445000e01300030b42c0032000340041d2a0540604041c001d402000c2050003a0190109960240300d44144605500c6070019100100c80c00030b030065071079042000b01410401c2008441d945441100180820164090054203000b000c0d0030b024030003601e501e801910003407003c64010340c072540f11030f0000d0f003000c100114503407c001c00c50000090081607600c4a9080580e000c0c0420202c141035424020389507440340b03100004207200c1404505041c248034000304052005452070481540200d00061655000d008880da00c10005004019a80c0d564208040ca5008646440d00c100b407240141200d500740840c81240701e0140001901c21514241ea0076984211581e102e000c0030300b4180808109809984102d90308 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 253078803 1250 253077553 253077569
    0x20120102131205210c010c030504080f070c0b040f0905090a0f0605190212010303081e01030201140d020705010e16030f0204020a0504030b0108150c0412330204080c0a06050f0d020d06 80
    0xa12480f8600170781c00e5440c20500c040c201407400040101082d0002c0c103458581c800c1c1000d250b52941107003084d00b0703107201d40d40181c00000c1e400103000070b810400c10000c10803102110b50501540d940c00401c65140ca0342c1201c00741507502c01e054250000b035140d07880f841e403160f1025005507a8210310520001241c20103c0000b24044201c001072040c5a0404a00c1c1c0e4402c12600c14000b101c030101010102c4100b062000906001500d646214100046c0c403d40d85541b200c8002152a0506c40c00c00314013821003411180c40e01e002d014030200303e00781d002040d0710690742c02c06510f0200a81c02da00740f00c000d510100301041004001d100110025198083e2140201101c00c01000c0a102041c2d04115240c03000d0700c40213040604000405c08401054001c0c2c0b00a9081907103040c10a04034604030443c0b038040f1088403420070302c0184425807000c9681c09401620070030011144920591428081040d0860040e440450130a102c0da0300515580b10040003461907080e0058140030000440006603102a04013040f = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 253080053 1250 253078803 253078807
    0x3050a020a0906030201121e0509010207110f0a0b0d0e010606020303100603090b0a09060b041b020f070807180e0d0504031407060813020d2012010213120521 69
    0x105528005036400701401100c0400c1250620310384c0080c003c410a4445110240c1d1594010310781c1c030005101c021081e00042200740f00b03a28046000e14000c0d0312104048800180e042a400e1050500308420304081e0b401a1199042c14245990110300e038200b5800c1c0510180c8071f6000141c60300c2c00303000c4d21000704401c1d00210b0300c0781042c003050084046983c006804051070b120800c40403801e2401c0281c0c01c80c840d404000340c1354903036060807005041c2c0008000d17009801d0500c8404a0b2258861031194040c89509584907a106a034005444201a204000f0142d000c003034280600384440700a000390b00016540040c4100d04c0304005821300c0b0501115101144c0081010024014052035101000c06910050440b1a08041c00900b031604050700c000c0030b01881440da042192100114425840d4001d901ca0b400454021040769900d01c000d00c01a003e1703200d401a407209160305000742d45c0c514658803c8000142e06081649850090980c41610188030380102e08403007070070740440010f14a0300114415 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 253081303 1250 253080053 253080073
    0xf1b030a0f0b24060a030e150f070f0219111c060204142710030203030304060e19120f0c08160311211803030a0804060f050402030606040f060b040305 66
    0x40b880c803e81100d0f0000325415140700b074040f503492108807068003103c0d00780000c220804c2c51010b03151120422041d4022100d13101849509015a58603d100e81401e940e2580340b0001100c00b01e89820300300e6200b5050502c48040c800c002609000b80300300c0e02c04080c1080404c0d03044004080c0d400da424102c20b98403141e00007401d00c020940100c22008036030040d00c6103294000707100390045480042034200c00c0703103559134000b0501c0004039219481c021030700101201d480741801c1c10200028006490032000e0b5101c1c140001c45d580d4019050010b145400494a1803080e013551016900440a003242030b0810001350007444c00500c03c0c1020b4a4047c849090804803a0424600a0034180f6101d60a1000e544864940c0c1f044c550702410b1821520300c0c0c5040315489039000c00b0510305000300e80c1e0115a15000201e00041d460f588260154030a900598042c0280c44c0750980703a07811030f203060300c2c040c0d0140c1017400007036031506140c1c00c070700305148054100068182c0c2e140c1015003a900a03030011281500701c3c0c0905 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 253082553 1250 253081303 253081321
    0x2190803070507150f1a060d0f110703050c06100b160201030b040e0f1e07061409120d03050619030f14010c0c0303060b030106050405120715110d020f1b030a0f0b 71
    0x1124203a81c1c006e5185408000f13240091624014206074038030b4291a05044841095103030080c2071001c125202c0d0f540c49035141d2170050080c0c0c10200c0d4006041c8101c00010b10320403022820002103544820900b482d103d0140c0c21600d094007a00d40c1a41070580711283c905040d1103a200d01000040c00201911103040351200d690f0414900007803103c1d010323a481c80b0420103000045019003c0b503410742424061003005e114030200c00d0040008859201c940e41d03c0c003112a040101d00b030341c803010f1540d0341080707540c0c0d407142000602605010781800f0320400c81001c1c80010128140d860703089000c0e00058800050510742c1c40d0035664a0302455001506d404901020950107000c1d8402500c50607919a04540c1081001003080c01640300d43d500c513168800d030842a505040c0701010240c090040c460880c0b09104001038040d4020082000140c898820700540d07440c40880e9071500140704e5406040c242c0e0b0000400d181000352141201c1c2e15000300a560700010300928002031405204800007804c0f49044110 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 253083803 1250 253082553 253082561
    0x602010c030b0303161a040809010207091b031a090405070612060305060c1b030406090609060503040210210e0d0e0114120a18030c020901050102190803070507150f 72
    0x1805042c1000c1d0030704095030740801a980010b50705c800c541d501a0150400a040710305090407030b02c01046900a000c01c0c0940440241125502078084452160350b134880d41c003c4030a0a07950009403009540002d205a119410480710f0411107481c40d1100040707000020410344041c3c40440385039200e000100074441c1c0103048116545500380041054518517150644c0300c18008019410700c0c00002240a1040d4502c00d40444032100e850440c1d440c0c40d1a10006400031040e40941408581034031400914240700d00c0850717120740d5015040c4403000344820415070f0485c20340c030b8445c0c00c001c0402da01d00c1c24902480c865014004c140c1d0000381803c5403a03140c007501e150303804000a0b0402c00100c070741f5009545124203d440c100d03200d410700c0c07040d1b5a5031001c1c04004d000e03986545078504c0714551081c2c1819170142c50803039540e00840f104583d50f6640d00041e070303403610400746000101403400b9a10300072640d440007643d4418400d040c000d10304134441c1d0b540c0f009210001082c852a0380e0718a401240c80140b841 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 253085053 1250 253083803 253083821
    0x1104090e1f060311040905030f13080606120c0103050a0e0a03270518060d14150c0310090b060906030106170f07050f0904060b0d0207031d1f03090813060201 69
    0xc0c040007060b045840e410413958080c4482e5014607100c030340d00010444100b0440c3c41d40b603401c0a04035142c15600642084407506445540e50314030542c0301003001131902c0c00340c50000c460210000c2c942c848040340198040c1000030001400d0039a40c2c0001100703000140454540d00307101c0e990341c07200042c10406154880c01c401505901c01000700d4002d0065444090039062280000903e203c511f0703558a00207500f0fa2004140203012110342404604450000a1860f44c9401d40034050841659080300c003900a0004403956106c805c40038808104a458551041044000140401c0c0c83c06c0c0d42c8002090440c4e100782d0180f00003601c0503003104203000301e01460744c1c0c00c00d0600550311040d0a00490081c8240101460483c2094001070030060b10369840c1c0c030040041844900d401d450b81c00c0f00243c4030082d04081d03016000309500c0c0410681c114445800d10140e540000c0942c420013428000c080704036080090000c0c140b40c0c2e2200c0b03000c040b41c150f1028060410061a01d401070b1418a8002420764082d10 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 253086303 1250 253085053 253085113
    0xe1902101808212506060503161805041205090d08120106180b0f0c100903050316090e07050a11030409020a0e06130302040c02010605060c0a0302120a080403031104090e 74
    0xc45608914810f120b204980341c1c0c0c01c420303614400005405c003440140401d5200a0780f51051000d8600e1000c10410808111440c000c03907006002d11004411090300c608407002071200801e601d600c4045402503005d490455000b070f19964041c85c5a945139405988100e2140c84c1d01c400100040152613480200b000c2c00c1d1b82c2880d0344a0f265803403d10b03441140c2c0114600d5003505140815006040e2004000031880300c18804018030500c074590502400640c01644d2841642561041c01400c0754000c0b192a0200c40c00341c8180030003959a000100c812f40c2003030440708200281c460500c80c400100300080c1024000030840180d0b034002e031480c0904650b80c03480420f4065001480141c0e10442a00a80c00490350140c8011440b5400110700300c5c01405682c1240c3d5100360042003640caa144001600680c061098007200c2844904200f07000e81c2c0e010b28403280c000200c1c12800200083e05c0398010707110708501c4001e40d500306612403128805480301070409106981c0818040c5540c40e440c000c080c01c140031b03e0 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 253087553 1250 253086303 253086307
    0x6090a0b07170c070f200f060c07050d050118110118050102060a0f0b0a0311090702011b03020c1e010e102c030904050f0106030e190210180821 63
    0xb8852100744000101642d8804402180002c20302c021500306841c1c42c3d80c41000f450041b001c2d03003007500f038105604414500032081d940641486007002c80c202d5810400b2036000704155454001042064200002c0807640b40d500e40c0311251400c1021900e6800039441044400501d1180800060503042e0070241c0403103080f240c22003009180d07004510b280e004042c0c5200070458001803042c06c1d000c1d24005110075003010000710000140042c0c4c0b000000b0502046500559588030100200d099944500004282030b50700400a143c6a001ea8000c00f1585101825980b40c210308044e440c0d084010910101c489035143c01e1510a90324090144854032200304008001d03150039085082d00300301340c44500040c2503030b101a401500b00030820a45544800092060109250840c0c1801c40d6a40a100c0e40e8046800c00007200341914001c218805a82c1c008220030b1443c3d82c80d9020041c02070f07801072240f000c1c03104911028030707001c0d0f08681020141c82048014003141d04800d03003c1c4211200701e50004154842 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 253088803 1250 253087553 253087577
    0xd0f0209010507060f020d230a051003020607031e1d090603061f03020a0603090506130809120f03070602070b1b0d050606070b0a020c070f0509040813080304140405010b07050705060a030e06090a0b07 87
    0x4c075082f10702039a405884950b158441407505036102c0503103c54440b2015101240d2084140d40646c8800082015510b41040502d41d00140112503006035090390b4560404000603184031101e40c64846488280507000015595a0b008104036070398a410020029480d804c2d091709004d8108421038220f0311038060049407800c103407540c104a00440b14460303c5842d01151207a60b68000f085000c0805900100f1f4030b0b41c0300c0d01490440020f50050030708603400401e03140000c030445400007840004450300000c440c0344c0100e001d60403004000040c41d440e88007400f0311084010515190b0380501c661842d120060f0b40f0116283d64602e080900e83c410504421100030a1111b61248903a07141c210361300c01d039440d80b030720200c07500340d00b500780d5a401202c0503200100e8001030181c602500e18070801c0081c0e5081085903224480440b0b02e1060034005410741e400300c0e0007040a414030000509101901d8900080c2c21080ca1501c6801e080342503c184555502c02d13002c4409002e400c404042d0090101d04101e00c101c06 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 253090053 1250 253088803 253088821
    0x618020405090f0c130b0306090706020f0601060206010306092108011a270d020603040f03031401120b060f0d0606090b060304020d060b0d06110d0f0209010507060f020d230a05 77
    0x1600100d90b002e42034040c0000174808083e0007141d00100010151650f5203044801290744070120f01c42c00006102c0c007481d000005001040d46030580b68a940078080b140e0843d1619000b0b010780c05000c803050280c14007000e200e0003503d40c540448130b0703403030342d500b01c0e1540341070084a0b0400c00821550303413a02c0100000f030070b400d0040c120420b13080c401307a041038a0006a8400610745195500e000303900444000208810803101c51042003035140710307480400c5070f0318640d6021441c1404c240108078088400c441410301140040000c140c0c0603070024082501c0d01c0800000c44c190303240000d02180c0c0b081d100c8400303008207207440c05038001d41d500a0b01c50904500d03181d000120145000e28010b40b60958401507034400d903d03122040700c1d0468002c001400013000318103a9025560220005200403407500f030200003c100240215001d900059441900303186641e207d08004204008011542503402c00007084004030f01c0c002c40705060a50550542c04403440300c2d443c8280c050042c8a490304a1401003000302c012 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 253091303 1250 253090053 253090063
    0x12021e06071d04090501180309140906240a020714033004030f080901170c0d020a0e041a090f0c0d020d0f06091e0e031e070618020405090f 61
    0x1d102c05080b01c0c0c5004010700400d00803c0c81880140c00c65092100381c1c0e000e488059643c580180c4242c0c1d0b241002c4c1d640f0030240c600b8000c11400f0644c0405060003168051400c8400b007008526008041e601f040860400b45c2c5a81d4480044a40960000c000130041c04a02a0700c0c42aa0328040d0054003d03121040c041c0c540250206900c1c1454400f4218040c04080368103003030b41c0242d80c4c44801c9200c452182d090011140e001040d600740010043c14400c00ca004c05140f29a004441c050710842c1000f8480889a007c0c0d00150b501408009041c665580f4544e56400303103025820000f003000e800441c00b10284003042000406400c0490245401d0004241c5107074102c07203280c0031031900161501d1300c40e05244050040840307050b910034101440820440c0d40303980034050351040c4040c20300c0b20303c4050681d60165110400807006680040c006d20035545940c0c0b00e501d21800c44450a28075026135a500d140c21503045682100d0904a415000e008608040c03003141c0e0041503000040c40da020380d4440c5580c0d54 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 253092553 1250 253091303 253091327
    0x6020c1f060803090901170307060908040e011203020c060901020f070321050313032109120f0c02030304030204200c010501050906041b0f090f090902041802090f06060712021e0607 79
    0x2041f49200410342411042c4242c615440d444441800910f44505080760981c00c5070151103030a076565400010307841080101c5185090741500504218a9440200f0800303400c448a0b80c0e055014000d00c0000705681800b0742c00c061840f0340c2d01c2c00580303080b99445000030344c0102c880c3e400340b00c420401d12101c009151103051029515140c10001c6001c0d11100f19007144194000b4402142400e0400c4108407802003c0400c01c0440c2c0d44a444154505108a401e0010094065015042000280b01505040e088103500071030400720701c10704c409a0035891640d81e01c09092220103964820042c045490b10300551900030004a505102404175440001104269101c0301c6003401610030301e004019008600c034000a0025100c900342403556060020068400c0354412842540b5000392040c0001002c07000c9c0042a070050300d4500706035100e008610480c82c01903d550781c800c00600510000820322a2a000050007175405881d20080c104800c00d010b114140041c1c0e41354110808200c51207901c01214003074 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 253093803 1250 253092553 253092569
    0x6091a040b3f070b070f05150903120619290c030415050a0f0503070905031f06050405090d0503090312070e10090308160602220611030309060c0706020c1f060803090901 74
    0x31341140ca840c0c0d1030300c400c02308500100c17101e080403c03054071404001b90601d440e10321011401560780c030040012020550b0342010b00460100380c1030003a82d2000b800b100b040d2000c1078912000901c05041a0070507000300c4280f00789640001003d03c06190494040c01c43c40149050042c2044a1084090120300c60444010200070022001985181c46514944c00070600036003500c6142000c0784031001c85a03070406c08842c80605100d0001903606040c4a4103115500c40c0b00a01420710540c4012200c550000c0d01102c02c0740700500901c2d0f00301d1303140c0142500909841e2141c0100d20360000600c102e40c4080d040020078001040420404501983c0c11502c083e50b007a401800541e0040c0351160082c041e042c0d03810400091504141e20b80441302d002802560181d84a0850000c02c4d4030442c1e80e00d11040399043d050360844ca01050705e08903410b000d0801944205809803d20862013100c03482e014441c0041003503007807841c0b4103140c0c01d406072090b000982888000b0750325151309040030500084c01031050702c4c0 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 253095053 1250 253093803 253093823
    0x20306030a0204050a1407020d090f030203070b03040f080c0604060c02030c0c190806010f0501112806060b0a0825080f0402011403091006091a040b3f070b07 69
    0x2403030706100d03400600c41041100d20740c0300c6e9080012009560703115104826001c108410004219a400444820201c83d8001c004180c1c2d9800e01a0354800340d0800b074400c989014514451400242e8010050074005038400003c010303615241c1440e0741551044010b10303082d03400030401c0310650070780411a80841e0b40305541070f04030f0045002c44520a0380c001c2e030200b0315a00404001041030a441594003085840903030340d1044030020303407d005442e08054800020320101d00740c3c3c400004544140501c06960041400296071695201c41d000540d004130384a40005511000700214014107e01c0341070200d1404040040d03590342800c01a2500342d010b0050011040c80304001000c580c890407100c008403600040d1301e034682c202070707105aa6460030b14600814407400d008002c500707285680300320b2035220103012000f0f603035444140c2484010829022096003021245c500001e0401407441c1e030040c2e103840002403019180308007414070a840070050031030a5a4000305020008030010009a505664000200907 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 253096303 1250 253095053 253095061
    0x18110d0212010c0903200a18090c08030903100e030702120307020319140d05040608060a0e0903070209010b07021807090305060408031905070f05160206031513020306030a020405 78
    0x581c1c610300c8000e01840540c01c100e0720400d541c1d8070215100071030344251082500c1c101e9001c1e02c8120968034100d11500010f0040f001c101281c03865041c0c203645d80c4519000194090b0030745032245019060f410441c0d10fa8000500c3c4c040d2401d04000300058503c420404000292491140944034420700c100a842903400822280c9440014000ca42c40c0c56401412070384104001140600c030340404000c155078034061442c42070050039022a0700c10340d54245035241e40c46c00381000010f07078014401800d02500032110034400710754801c0c520360b05801110880015511548540304006446034160443c3d80d0315042030203a080161540d58201c0d0100c1c18040c070b003820b540d803120412071314071206030700c09882842544240001c0c80b0301240154060380c0501c50010100294994040c19607400340d885000280081040a014510500c013401203011668110080005c080e00042c10342e40058402800c082c01d1610210a10300e00b449148030f0424201200391f0451a0400000740c03141498080a405661140d00103 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 253097553 1250 253096303 253096309
    0x3090b0c19090503100c020312090703170a080604090f05061807090608060a0b0118120b07020c010917121201050f0118050d020d02040504060903180f0b0708120c0c0118110d02 77
    0x24560b04c049d281d00c0002140792510800341d80d6002d074401501e40b101050181c1010205035011244062090b80b21001c203600c1d14000d200c010a910941580d0b00c2e40000414000601c0900009014030202d071404019483d03402819410186268080d030384840ca030080410001c0c3d00822080e52045000c0d0b00020600c500200603100100c2000c3d101c86400c0c450380000c43c9200d4a4110049040d0185040e0085d5070b0769030400b43d940300980300c1d5207808a4001102000840350070351116420b00305000689102e6003048034850001d420102084914181c511300511950801460006168409107013444801c808440c04450100300350041da4060008e6610a106540300c00010448642e030290040210b0f203020b082200003004400c000300d0004805038280c2ca061066400c07054142c4640c02840e004162070408500c419510104003100c002c04280017110110081d10304c1c13688140c4480d202c207941c6200c2000c1e92400c50342d03003d454114610801d204000824100340310660110800e0b508024000001c5c000 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 253098803 1250 253097553 253097557
    0xd151503050d030203090606060c0a026a0f030b0913021305010609121103060403050403050f01201b071211090702061603090b0c19090503100c0203 65
    0x4094031600c1a10b40e4401d1982c0c0c1580158403d8840c00156111901c03460204019482030481802d5258803500800001d454454050746010403220140e13980082600e060f0201c00c500c2062005c408055a040700d1001c400900c4125070003000f41c0110390542c208007424140c103412514080781003000d00703203d403080c0b58000c0c3d02144000c034005041050303038580310b10341110070301c003070f1104078029940b00900c03803414000c0b8001c2c541030f43d540d5111403840e20b081c40c0c401d1079102d2a2800564041c008210000c0198a080c0092400741d030003541c0e02e5031b95070b065003400351078110013203080310080e85007400c0000303005200c41403070b4046404410038a60320f50709503000f1410b07440c0d949022600c0e07018060000a40b6035110a0110034180304032601a8805800c1c81003000c070041c01c49082000d40c0004d0001204418103011200300c1e090a4140050500d401d034884406060b0300303c0b108140010005007600c1c06c4580d40301004510340072440c02c522814180804261207140320007895a5440d1210800d1000c1c5d4005d1003 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 253100053 1250 253098803 253098809
    0x180b04050111161505090307032a0509060f18040507060206101409040f12050a0e1f050306060c0703030e2110052a0712050f040329040c140d1515 64
    0x722860a42c8904002e005045080ac003040b0100e45124006040020703104042c04484000709a8600795440b00c0910000341150020030340c2c01014103460f04542402805001d000e14020030007001424100700c0c000c1e143c11070251520b5403510182008101503100251308051138bd000b070701c0c074200545491400341a641442040101403250162540c02d820f41e100e000381884ca18244e03541c007c1c0f0365200d814803040350b110408103c00b421214400450032400f590080d60000c7c000351180e840d0149a41c6903c0c10420301385c00c01c500140312449490040c1c0b800c0d81e68510310408070540d010601d82d40e40c14450742d8101601c040b00440352103030001440720800030760a043c20004403000e850111101000070b00254000b01701260300011001c0308000052044050720102020b0146282c0740c40e08584800801003080d080e4001d2546004000704000114114168000e44c401c0300902c0500e0b042000b0032a04602401300c25020b8015074034079402041c03004481c42098500c088001918000110240514400d0b0350 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 253101303 1250 253100053 253100059
    0xc110d052b0c0e0d0305031f0b220902040602061501020715021509010204150c060603120c020916120513020d030c050105060609060702040b01180b0405011116150509 73
    0x501603950400541c120075200c0b92595260480f4800403010001e051446000142c000b4100b80700080f018100d11031440090135809040c004003598411162003141c0c0280c103600d0080201ea40301f01d0010140b1070918025201420301903050078140705000b035031803000400a43c5603a89990010301164002d01c290030240c10b40f02c0810b2134100032500e000e540c7c0c8141c3daa1703141070361400200041b2000300601c01c0e60103540d2182594034204101c000100ca01004501065460301e50720000080042d0055803100700010242d00c95820f0318507180104100c0c524014002c0c0034802450540003051940900c40090107030b0b50410002e090b840d403c1c841090071900d03003402900444011101c10a141d0803000212145110700020310103591100144030030750280500c43c07508403200744100300040c50203803c001640705044c90900c0001d040c51784040d08035481503108683c3c2c1c0000140500c9256405200c00a0700c4801c030f0010b02c0000c0003000130302040c040511034060051140076002607800e00c0384003110310141f002 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 253102553 1250 253101303 253101367
    0xa05060a1b05160509060d03020d0507080f030a0b041409061b1201030602090307060f090308030a15090b12010204030206070602030c1603080106110c010801060f05040503010204180c110d05 83
    0x1c3c5104020900d00c502440c0c0c4541c00d2038001600301e20308000702c2401690b143e80a440700c00011041a26290081751040320407000501c00840c4030780c02c0e58080c40c031030702a2520100d08440c040041c842240e0600c1d07006070741c002490003003001602000138045e0f0420440044d01e81e00c074030206292140c5000c3d608451103410702c2c50b400003041c041c1507005450203407c1141500d090030394407041690020105045180459003100c82080403600c2e400c051a07124030707809000b00f000078902a03c005101c1c415004490360664030180c150490403c4030303842d009400c0c074000071840c0c00d0541d00050150300810740e00404041d000400a0b82c640c0c1c80d030040c2c841c2c074107e60300c02ca01d5107040ca28020302088070901030400000c100d03a84030450f0356400180300300e50303440684900c15a0390a294044940d00402940c42052020803c000610354500748001d0000b070050348001201e40344103018900036120410340c1c030010400854840040c0c1c0340e000c0340400798021603007059980c9480941580c3e804407071450142e1501c04207 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 253103803 1250 253102553 253102573
    0x306030c09010b130f0305190c2c092d0a1b0503100204140d050106120c1701020a020d0807120f140f072a0f080c010b0a05060a1b05 58
    0x8100980104510058249041600d0383e001c00c0174818140300c09425548803001a24889107061400324005000300d0060340300c40d48520b0900554055032441d0f544841c10058846040c41424200a03001114400500ba04c242a40800340380384520700c13440343e40a9000041d00b100140304001003402c55074802da22081280c0a41c1d203c030a0b0160611500f17000b4040d4980092201c0c0e041c0c0b00700c2c0c0659601003c00a442c061b0307101402042c501450301158659a0744202080500c6610045240c03140329441210040b820247d54800800c4060303020b48507a030061120345450b03500410340891001e1310b4a4465000d1352030300320803141040c2e0b031100385072603c1c9030a4101b0001d00040d0424098507400359844403031034540445942600c50216250400680405d490446e0404111814420a10700d03d051110804d1f064480d041c14004441c0c044481000010b02e11062a00038001c10300080030454007080d00c240b920011440340c0c4203c0100904019400540e044085003a81054100b15003200490f180405 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 253105053 1250 253103803 253103819
    0x905151201061e0203070201050d0b0d080d0b04060e090a030c06150603020c0105060109051c030c020306100302031e03041413060303050406031a1f0c0f0f03081e0c0306030c0901 78
    0xc54146079407003100f014140c2c00340b1600000403034400c6681a0760b50b074600b15039040c81800400301000100d6000100a6155011400d05001382c02e421502c10000a1100c03c0603040104884a603801800c4000b402e80401c215400c000c95911038094150414009060651a128000300040049040c00c0d0008000c0414002d1b4185e01030031f002004103000f00820b4540000640d071501c0507107d10769105480c804d1741035004408001c00c60721103129060041030544c043d0300181c02c102c800c8400341c032802a130800030820340c0b800b0885410b8581c010f800204102405060940e145d111f0b500901500d021000c034100803c1e12184080283e41e86ca89000700079007600d914008000784d100c1d119110000742082841a4620190000c00480a60080100b070605c85408410084003048540d214140164000a2000b02c0c40b0030b401c1000b400d100300d0580c0e011549500d0064082c04001d404a01c070700c10090b15280d403a105080e00c00b50020079210f207142d100c4d40e4980000b0b01d031034090a410707a0082c0c0c4c0d030000012004 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 253106303 1250 253105053 253105067
    0x9040b06070b0412030f1506050c150c12010510020a06150e0702060916060504090b010e060d0c0201180210080402031006060e03010c1107030803040609120c0201030b060a090515120106 81
    0x141340d40d0521903004a503041400342c401180942102030300d580303000c0044c1c07400b41e0020000c5503004070560b03900f0703a41c3c880080041c0d42d084070000c0e5a0b44000806515a00420304420701401c0d088505925800148400039a52030301c14000501c80360f07403441554022100145900020154001f0000c6c0c0c1e0300d00402d00070348409056440c1c030980d108546420707030200840c00c400c40641e03095030b8859040a00d002090406030030800440d60600600d4240141c65440d100300401c03007621411004207841e100c6050081c2151603141241940e6101001701030010f070b8a80c1111301a0354100d01e0a450181c81d03a00020b030800c58507508501500d480d00600090030340d004a4440420303a8202c0003006504076141e401e8914031000451280300740c00001040c400102c018000c0e40c2c2090240300002203042c0c1e90f6075020a0000220105070100f480200c05204669060042481410080e070703101d03003003402d07660b8061b01201c0b01e4002e462056482000c0ca5040c1501d000c181ca40101401c0000580b0f03596525000d0078036 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 253107553 1250 253106303 253106333
    0x3071d09091606080c09040f0f0c0c110406050d0602070507081023040b040b090c0a0603062306090103090303090c03110108070c080a0f020a1406150a03050309040b06070b04 76
    0x100301a000d0004600d8010f8980b40d05c00c900d0194980e103800d164800700310017403103004000c0040e5a91160300240c082000e1098003511401ca071134445448840381449001350b003843c0d00c0e0a00c254201038040c040c1d0f844109030034004036800600507031140c1d21840d00d9414200250429a041c2c41403154213042c17280360383c0068442c2481603e450900c4103030000180c01e0320000b2100584400a84030120b00081c442c240c17190792080f0301d2400d0b60f2203440d10800140c00c00180e130340035500098803605c0a0051042c0703140c1c0101c1441c0480222450500042c01140c540e00400714040e05143e510404482454081d4100c1c100c1c0d031354001082420543c0b24908208030296100e4010b0011340c00c070002441d01401000d040e0707102c98010103441d05180305404101d034080c4031041541c0450090350000c2c0000741e42100129200c0f0b0040014180ca4a4203406000c1a44245d1900c0d52081041c4c80c82000899000b108959403171505840210310380d401c80010806a12a5500040015203000200b00c14806050001e44075 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 253108803 1250 253107553 253107583
    0xf15050a0b0c0c060309071a040f09020307020d030203070207090f140606031014060c0d02100b030d050403110616030201020301030209131208190f060302120f0303071d0909 76
    0x41207880c0c00c040152400ba10040c048140e118596442180c5008006107070f02c4034040b000c0310811511410b80c15050f0302851401b03041e00c400410f0500c804600c01884101a0076002c2c021070a501e0503180c000e59440d8040509030900d9030000c0400c901c2c5100f8808800a004c2590080c840b81d80c10700d240800512001d8a172191400c0d000c000300d0343d06c5c81c016084901410760100c030074031041c0c2010660005655904541d80d030080041201c524244020b100000c0c5040464020b0009c0d0740c0c551421400f6509080b42d654030980004d000358541c1c1e43c00100303903403d83e40c01661403103603e8400c1010800078483e0303418030040a0400b09082040540c1500150705030382c403e8454120b070381c6482081da10380c240498801008040101250410390b4070504c601d5512005044070aa10030100b44c0d040d20440b0042c0062074a900c4d200c0605005504200000740810a04030004050984120000e1030301e901003c2d0080b020030109801000d01e60001d02c400707442d2107000800c1c101c52401c10000035581c40c5990180f00d00 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 253110053 1250 253108803 253108819
    0x40311190c050f010c03210b10020c03010e0708100b0a0308070b15091306050403120e0a02150c1f0e031c0f0b0604050d0606030f03050702030610120204020a030f1505 73
    0x180c00d5100380001d102c010340c03640300c001e034903020a81f54004100c10600e1441103242d0b03036582d08600360f031201c08000c04101e6079009009100150010306080d1140114071030f000b80d001070010010110001501841d031a02c40c200059001c407050001900000d50390b001801c8044003142600c248444102200c1c064041c8111520f41c1c0203104091195458040b5980740113072841c42140008191a81c0005501610030700c1c0907400c1c1581e001c48581260050240001c42e07a002521002c21810405c4010150443c015800c604107229411141e603202560741c4811092080418031034407201d101d4005e0706000e15480f0560b0348484401d02d071091040d03900d49000003802c3c18031070480d41c2e144180c45a40302c202c0c07001c1d0883d450241808248211070000c05412209155100e0000000c14011040d1394100b600c00d0b40c03032903550f600b2801014a000b1000d001c032501000228020007183c40405913005071070b076041d030b030150f1112030b40081903005001000e040c0f856682003160035010007034104114410b0303800850303200d1 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 253111303 1250 253110053 253110079
    0x1306060f03050c120c1209071505091c0206070c0603050a050601110c01050f041d06040b1f0c031103030f0402013009020f1201020307021c0503040311190c05 69
    0x10181c0d10107850094028a041004091840d1303007803c29a4821003400005142240c0c02850354050041100c0341909500110b40c01c1c401c9568004018010020174035040e8101a10f00e40003900071a0032282000103403c0e0601d1000854a4070000c1d00c0146400900d200e488565564014000d400100c5140314100d1400c00000e80c02d40c001c0c0d20100482903400001d0a00024800064030076511120040d80028814480009d030340400303e02d4546034060019a44116042c54800d200030365600d08191481922105d0481404c40020b02400404000318584803642082c1418103541c00d0030484000f000c030380070000411054195108000e13005030301c00e0740c9929981c800c0d585440c0d041c4138071400c0c6807100301c240d040640100400c5d4210020785400201540c030008442d40015007d070070307500700e50106650040704201115805000c005203003400c07690030144584207200010058440140024103010801d1805040000100401e508101181c0c908000161b824100116801942c0c0b003114451542d240b540 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 253112553 1250 253111303 253111307
    0x140f0309160321110a05030c070b0702101d090123041116060e03040e01090e0303060d02010302071a010b040e090f072102151c0b09070c02010e1306060f 67
    0xd04100d0b0380007030380d07802c521280e0700102c0040c841d0780b000d0f0810068068103c0702445014010144a0742c45440110b1381c40000381d2095080203400d41c400031035000d0030b21a050140c1c4660103040c6480da02480d00304407114152294011410310550015000003107100040b0300070011300c1c095100d4501c2c00313080301002c000b0b210810040c2c60301c04851002c040410f0144891800c1ca40310040d071400e129960200300035418208040c59a00958049185e0100d03040040150350554865420594100c9007c0c41c59481c00300007103000c9216026000303040650003d442c1050006844031483c01c0d0b200501220f074256901c092001058009000d0750308280102800b1581e040c1c8001602800380001d4005040458640096000b100980b4500a1100760503d4000b4005030345102c000407115442c0e0042c01d403241d80a1030391028600000c540054200e15061054440344e80c2c0d40c200c59881512403900120b075405501c012103a062240f4100c98002c1c05a1b0010900300080f5001036041d01c00f19541c0241c481805001 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 253113803 1250 253112553 253112593
    0xb040504030f1103070f12140f03010b16060c02030d0c02011a01230307020706120905070314030412150b01140909040c080d0f182301140f0309 63
    0x20045841c0c0c1c00d2001c00319000f12420f49a400c00142681d013440203507125407850716204001207584080f403111990226800c229409084415000250704000c0030b603920301c5151006006428040b000440c40b00c3d15141e902040d40d40840c2d01c0798090080c500c4140c0c0c00381d41d80c1c100c2e260b2403075090f00344042c0508180c0305100d40751400c011011401c1c0203203102401550610340a180a603031104280381c4060701c081c00300004501684107a40140b216514181002b80f550900c1c03016982c41364104140d4a01068000407903e0549410003000262400801d40191452085030301c00b48007200c003440d860301844000002c050f00207810b0102070180041000046424580581480081010522a04000e400c085101c0b59001d40701e500d140c80f0607a202c10545e80380104903e607101c00100f855401c0c4842c26842036514000c0d04045040741d9945091808010850011040042086c060200072281507803140b950702c400380200d05021a62004c05408002480d8822030740058140b00302503c048134405c0e4000 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 253115053 1250 253113803 253113811
    0x40207020301020a020d120207020906120f0a051b01080705030f0c0c070e0103020a120510090609020915041d0c041109060423010f142206030204030c0e0c07080307300b0405 76
    0x840bd1b80c26580710400c000304a016007103050b00920481400d402d5030300c2c003040344801c024010001800c0c7c0310030180c21810f40c01c008050761810040c4100c240403489802c94182ca42000501d0b12000540d0b0b2190341c408500d00400a1403011441070307140001e2400c02600d2120f050b01d000b0b45000490689500d990009030030220402403040d03004a10b40742c03002e001ca034051508a4401c030300210b4400520303000103189500c10341d4000c0380d990504007040303c1e61929100703c040c00e680c0300c2c40302c00c40c000401c500b42d62220030103121180210b440b0b200007a028210b10301105d5030080020052503d41f030b2107040ca41456003a0108a5200f02c07070300960006558055127414924603030940d01c9403404020001b104015402200c006612044403007203403038548040b00282000b03881c85907801a1500d24500b04150420b0032940030703507582c48100d028441014403407022182c07180d4010401c0c6d035590b02c440f54100d50705020181c54508a50300c4400c5540450b10303c004041c001c3d6031404050003100e8120b800c100c1100e500741c03 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 253116303 1250 253115053 253115059
    0xa1202070c0b0a090e0a020901020d020606150f0f0a0201020a1b0b0105130902040501080f0705010c08120c1b0109030801080d0804060b0604080610080d020d1d040207020301020a020d12020702 84
    0x40700820124080d07200030400345400e440c2004142da99280341035948041541c4000c0c442d84c020442c0802c0396030402c0954034403c0188020319075428a0b03c0030035031022900d003803d549400b001805000c0240358100300c3d6007209565142950b90b40c0c0c1018002d0007504015900710002c4c408180698203154855014880290408001c1c0c10f035919050802ca00754401c400c100a01316290a42c00300542e4851042c14000c100c0703074002d0084076030301403515810002290060380c14403400081c0040440d00c414165145150580c50700050398407060070302403d41c002c650a00da0400d49111000860389c2040d00110112407007501d840d49203989034680203440d2011043c40100054195000030042346440d001342040e144040e012030b1805850380c000b18184401200e0108400c1803c0400b08141c4070700304807030650041d4a00c09031603240c1e802640184000304501d1640c00c08419011b2203c415500e42c0d04559085a000f0001c41da1040c280b50042d454146d0034100d1408202c0035141000031711075030700860307900503401 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 253117553 1250 253116303 253116323
    0x30309080a03050909070e030d0e2d06090a0509040804060f08010509130204061e080d020f10020d110a020d1806090501030203090106030204050c030f01060e06040323030a03020a120207 81
    0x109040c441840c400404220030820142e40c840707d1618180b0103140c00d540b0542d01c02d4104401c42d010700100900340c0f202e81c1d40300005205001d5107255101442074102c0b034120740090740c1e1a01100041c1034140c2c10b412840d803240342c2d0410f100421650307e005000700c400e50b88524004445103001990805800d105240e00f082c0c01000081005019080170b400701c1e88000c00004695072640c82111612060724050714160130f1118041c01100e40401c12964229800e10052801c1941c0d080d5450b240c400c0a070128100c039401140c111030101e0755400c441c2410b00ca0441094590411782d41c001d40e5000c401e401000819141d00341949020416031030501598115110145070350b20700001103000b54070040092095541c4c51743d01000680d100e001c3c182c0140c1d4541000c940f0b030b00b86082c680d165079406030700010034424550a001c0054079100b06940440e03802411896005101440703450b106601c0000307040700d600000646400d0306415501a05450201da03407802e898100802515040380f0070000090060514 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 253118803 1250 253117553 253117567
    0x3020108070c050a05060703150503071a07080903030a050d1a09070c080909010f06021207031b060e06041b050a0b0d020f1c05010905151f110a050106030309080a0305 73
    0x91030000c02d41611071000c036160500a91160750405c1e40651b1618006a03e07001040070a4910700c560401801c021005080e00300d10b000f01c004500d0031054007810000c2c03000320341801401407420558010120207803d85e95250748000c0c000340135a10209100f880c540c60801c1e0002c3d2440c1d000b060700144540a8902d40041c0c959071400d0791080101e03c0d003210389a10400c800305041c0c4501e80514000d001a801032000c240c20560081d040c00d203607002d001d41100d42440000d02090744203194401d03101e1084186440461181441406032441c0d5580d407101e031003030000b44410130010355111a5404126440e9905150301c510801401800501c160b402d407650a0140c06a00705055006081c04003180341020f00e07044424103941032005214104172100303540c4000401c45001d0300c0c042d49500c660000a555051406040060486c100e1a11490840109007142c203007041e01402c21000082003013400c13107a0a80c1a442d05901030308150000b100094041c0030700080705140003030011241580340d12110304003d5 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 253120053 1250 253118803 253118807
    0xb01020d03180204060312020f0610061b0204050f0a110f250203060c030910050610030906061707080c01110d0c11090a02341502190804030e0a0302010807 68
    0x2c0c0300e001c05211008021049030059596200704d000440c03080350500b8861091610180c03c0800c06104075819800500c100076081d101801c040703050300d24506210a600c552200c1c803003a10092990002c0d0014500300600c40260180d0307c0b07191141d0b06410092040e0680031703d500380103005901da400341c2c3c00d50921210090700d603940c03d0400c86400b20385d12012820f0807500081d150100030b6031803040c90280003084c072079a802d0600000d54487c00c00d007070601c06410007401003000c4c1c1103211101d40405a40b00c080200300419608200001e000d11034914112000c4101d605484840c1480303254194481e190080ba0b031540661070032090741c01c506020f05905a0440c50580c0e00e964441401c441071250922100d604e81d0b5044162801038440c1103005856030442c0c50b80034040d10718802e512a80c5c01c40004c10b1040c0041e541c9020307800070390033610600f9620300e40c2000b80281c02001c1186940c101c000150446e155440100b45115500036a98240015104400c0c0802034146000c080d0000e1400380006050034 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 253121303 1250 253120053 253120061
    0x50307030605062709060a1104030615080304080706020601050312070b090a02030a140c0d1709061c0213120206030406020306061308240c031314010f060906090b01020d03 75
    0x49400341421000d80c41000d14520101c012160041d81320703040c1c1040c030007940002c0005580c01030f03201404102d0f48409032014a403e0003070744001400c02d03448849102c4841807603401107000f004514110380d00c494595001f685c07a84c0e403d0084a0052240e00c00008840c900005c0e20384020070407000b40c61410400340c4038861391680082c0047c4451080110305001600c04103e503192086c0508240b50401c000c6107a40d50070304040b0346110f84070388040ca8012000c200503202080c0301d00c0a482c00e9a5541002c40b0105600b80210190044543c004a0310740c4815400c0c0d400418004450b02014200282c6410300548505804200690450000c2c0001000030b0f1680d8021500030500410342410844076401c15001c55401d504154200e41011801003049e9402c8120641035124100c49150030b41350507201c211903030100500a04a580c14804201d007400383e080c0c1c004507144082c60092003072011001c0d0540207007920b403040e1016146080070000d0801d08901c202e42c4c050205078080c00f0111081c14044000d0 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 253122553 1250 253121303 253121311
    0x50603040611120a0203040b071e0e0301181506061409010e040f020309010e0f24060a0503060403030b030c04020a0e0d080c030d061d0601020a120203040b0c030304020f0307050307030605 82
    0x207802d0401c902469114052001c0d449048480d4002d0380d02d14142c54402c01d07108000c1d001c001480448100e2480c11618294500351070072051a0515001c5d014800003030150181b880c146000030a080340d440107000015501c00307540500b80302c5c1480516659034085a180e03203001500c204010080c0000c04666110301e8144215080003072020900c00042d5081000701d034426180b000380f981d50b030692181200c0040c8aa82036000e40500130b803a000d100388001c052440b50020300c3c222842e00300000581d690341c0300a4004080c0c1006411240c0602d064900640104014070340d052180c421a010101e80b4540b90003120152402550703100034001f520001e122000300480030449903040d0500c10517444040c2080542610b100c4000042440d0745041407082021140000b1034a03160691030420109980016502282a030702102c0403003c7c00c01c0e000220704601850b007010741500c0000401154001000001e180514000c94500400f150317494200740d60391a0342c4c45070b16055005840d042003c12007a03808250700c = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 253123803 1250 253122553 253122581
    0x50d0c0c12150608010e0c0a061d030a140d140405010c080327150606040803040b0313060f0c0f1106060103230903040f0b0a0e040e03160803070311040506030406 71
    0x315070b181e00740280988410780c020b5a0706070b54071320030300180c842d08010411111400340c5801ca8101d04026000305080341580c20100000300b00900c00b00c464500b08072840000d50040c03440804a240301244585400840c0050f100240e03100c0711110040b20840e04540c1100c3c416110542c54002d6a50b038030047c2d0300020045580404200101781158018020102c51001180041d001c00d9040b40c440c04540c2102804803402800148030900403110001300321002c2d1075074a10160744946d2810351226482e403000000510361402c0c802541c80480300364200003032031101c40d00c4140350300044480c05c42d211480c15480750402d81c00701c40411100d5000f980300c0200d1404600c0c091401c04080003003440c5d0b41c0820364032600c1580c00000c0c108410941b80302000c0c080c2182d512070a28003040904018000711240720140d219941d00d10789a42d02d140100201c4205003110061705940c40c0613030604c030000703400072076104021a0a1040511488803d44100c43c1540c100400c0142142c8842e201c6034000c0480141c0141 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 253125053 1250 253123803 253123823
    0x13020120150109060602030304150e1009060b0a080307030f031104050301110a08010602030c060106081003060c08011e030203070b0f1c09020109061b0209061f020604050d0c0c12 78
    0x10158606101c9448140d000070160002549403c00032421640b807030388100d08541003401808009a4641c0d01b991100d000c1c0d20010079110580d408184c100003907031000c00501ca00c1c05091108001e1035400904c802740307040f1345602042c0d646038040703a241d22841d84014001840408030412450181c0d100c00800d09072004560309003030710340000c01d00311201c1d0060500524004a0075000d03666204002d103000d04000c2c4007450505c1543d001c1d0543c0c801c81030055000b4400c0e0200000d20a070024510359004541180c41401081170800307022381010828020703d89100c1040e0080021107143e071090344c04496015004241e5246403200705400d43e04006d0044001c1001044500310144114222040f04800a4400a1000810702c0050107030b02d090b5011130b003404110411034815607180000850070b01c0c0c0598454045a07505000203030b050300303402d12640c05103040c0d0100114450b800078041e0304c124030030b40c00c4a11a503501d0b031080e69801c6030005c0040c0a0940f02c1e07014030040010517001d5450300c5c4950f0f1024 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 253126303 1250 253125053 253125107
    0x6070b0a060512060a110a211e050415150e0901090203030c071d01030b1302010c051006030c0f15180815190e06060f0a050907090e010905130201 64
    0x4040c4810f440030145594084010f00121040310300c102101c0c0d06039254254546a80814050f011140c0700c90007103003410240c1d008210080322504940d072004450011200b5040c104a61040140f00030b0f07400f600c4141d80700c00580e00e4417640b486080201a42407192000807841d140261a907000020040102952504090702c0181ca040010f0030422100f5400703001000d08080c806106102c080301110614801040100080380c09040101d401695100121800422900040c2c03070b9008001c1000b40140b1809014030302202403a80b004059910900c11519150354804010508200501401041010000d00c8038015802007404403541d207010281100603035600d64001342800e41c854004220074004d44d080191440f0607007000301e40307118900000c000380c0e04105501961418010995402016500610301d107581e520034102c00240b200400240072031404020051140c50750748560036070700e1509000803403072580c0c50041c1d41c0300300d0380300e12082c640311141d1700111404c7c808545581c6400805070511 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 253127553 1250 253126303 253126309
    0x303031808180a09050a02210c04030209060d02100e0f04150608100b07050c01030c020625021002030a090c05090903030402090a02040509090a02030708070315020d1b020c10030b06070b0a0605 84
    0x2da2041a0388080180c0b10208141c19010882c0e241d6003140fa80150002001243d0f031089d025902625010354440079a9510500400c0358000b441202951081c41c2075070003000c01d5844803404000341000d4072210310385d40d4054144801e65034103a81c0021201401202172003914030450b1210f6101002d00700c04420070f039071007d503c901507001d907006407010b03042182c44604550b0940240d80b9641c50f10700c01000c251030001d01e48594100061a03803044a1031071000c2000040c400c102e10101c40d100b40c3d13401c5549040a442180c024010401f040f21440070542001401d450000c0c887d82c404c5001202a500e95a12035080100070080100101c4203d54203204c003188c10b132514241c251050f54902d008040841c0b55004140c6055001e6011004960002c0010300000f4490a45071502d4107100401580711501d4001e103102900340100c5401507228030081d825221940002e0744181204181c0d500725003d41d14407803c0341070b10300642109410510402c160800036908400d055800244100001951a15a400 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 253128803 1250 253127553 253127561
    0x60a06020a2f100504060305070e180702010b040204060c0506011502060c0a05130803070b010918061e090b0109050702030f03280f0603051204051c11090f010303031808180a09 77
    0xfa000040d801040902025806106031034220800c0d080051082d4550f07800201403d0407041085a4680f440c3c0101d1003841c001d4228042c03c010041c425902c0d280c6a1000070310450b0f000400762040c1c42440300000d0101d1480e80140e00f5600581d0207480320b0b03684c110056645038845011a810072404104412a514499565001a094000240d5a600c9003418205811141a084880c09500d40003890311241e50301c02000100c251300580c046a0070080d001c00045264020301007406186c00c0081c40c0b020030040fa000c41c0c0c1079601e0420100011346507460200c0e540d0158517a000c00f12041003003c2110340c010070b00000c0c02e4080021143c202010749034240f100b502e80a840040440ea2242c00610410070144907005032002040340c2c06080624100000d00d1040c2c502051040c1c058071030302404180b14106404410341003003d0031000c00c1e030034150800203025009100640010740340456189000000500f9200c0c1240c1040c1b59600f00502c1c0503020158600c2c20307445035804041d8400000d8040b2442c05 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 253130053 1250 253128803 253128829
    0x100504030804030b0a05060f061e0d05040c17070e010b280302040f0b031303030e0a120f030b040b1f0e030109060f0b0108070503010b0904060b03040b060a06020a2f 72
    0x404c0d0301e0349080c040318550907100c018200c688a41d03d800120540782d105c200135a20254242941146055003800c50303e8002c2c8114a4540080d50404003000103010300340c1c3c1c1840807101580c042510001038542d115468000c10b0080c0070a0001c100300400900e078000e40509694541065800c00000d442004908402140310360300002ca6000309081118a280394844d000030181d06c00300d02c0c514544541c0310460079a840e00001d080c0751765800c1d0041e103d042040074042c0290700c9001080100c11480025202d1084d2021510001c1e052180040b42800c050140501d0100040d0441d403141400680c01d0f85036001c2082c80201300900d010070707202d05030307002d0007046001c90203460000388060308401d0746010344203e000100e060181d100c041c0014154803000b140d0440e50401d4582c0d8a6006240004010384015804010301e032a01000380404c1c01225a42c0310b00854003185e480c0b5038281d40d0a000e0b6102c007080b03030b40601a1045d40e60340e6203400c0d0038210503420686000819030410921500003540740900d81c6 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 253131303 1250 253130053 253130063
    0x2203020c010206012312011506030b0a140906010807110118020907030e0303130602090a090203190b0f011803210908010b1c151a0301140c030610050403080403 70
    0x2050311141035070140407480c090102401d421900c080c42600141034043d100c014940124900c006c1c2414060080d4801000c00740c5050500480b50740e03a142c002e01030954125800c0c49070000d410300254014a40d506240c00041c0584280c100b550380400556040720014070000030304c0410040d035a00020700f0311906c07614030159031204501c1079450041c410680c03001400b0740d050520f450580e4014920010036070b6804402d504540741130b4011460008080e001e0703030000d00d8000500000215034a48140c024510610034038001056041d1003040c0a070503620115422a00701034034400e4618103502c200894540b12809225104415a8070381e52440d40d44019002c206980c10a0350503002242c0c0c0c0303c10150024a00d201c001c0c030444078088001121101c40252001c4e80d140b003141082e0800010048170561034850600c1044182c0c10303d4096041c800462038082c5c0310b9447c008079035400c81031200b2240c0c02143d04072503880c1599140000c0c0720301150412008828050b09120000008001034000c00242d440341c = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 253132553 1250 253131303 253131313
    0x3020a030e1c170615030403020a0507060c0201020f060115030b0f0307260c010207180b12010204060212070c0e0601021e011b1e030b01090f030605040516031109220302 74
    0x5528001c182e040b550b1038050740d602010051114035030352140f1750303680740c810b1034811340da40c0e21503182c00d0b45054240003000b08140603242c0001440354000c120941090700030b0702030340e14184469440d140c55402c24011104581c101506865901c0d100307a1021030744490141030704000d4039640000038079020701da511144421801c040110390980300c0b0040c60000b80980c0001301b04210030240080c3d110030b000d00039a014a50003810004689115030000c052449018000b6940303074800d904094080d502130702817280940308008000844030050421103c980c0d820507003c5044070705105140c080d41402901c47c50442c1b0900c50304403181d401420315412070507890700001400078140b00e40c5490351f001e038003100018880840440c92812032444a0515070101901c1d0010b1081081d5005960220840c4c00116042003041e4000c030800c51107600681c00341d4041e0040fa42c42c400000320342580340c41e050100800c1511402c8a0704040d00700710341020341110809500041c116401009030b1141c81560406900581c0301c = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 253133803 1250 253132553 253132603
    0x20f16020418030503060603100e040c030507080316060c0c150f0606030e0606040e240a0501050a150809030f0c0307110411040512030c030c0f01060602011b03020a030e 74
    0x701d8850410691030914840119a900c1d0314082e1a80c00b008241c0360056034000001482005c28a40c050064655201d00891034200340c03c05d0403180c8014003080f105881101404034030b01030000180c030843c4800340b04c0074081040941c2c0340c9028182001c40c01060204140042000404600c2d20014840c08003500185401c01c0ca8465000c0d540c81d0781c0314100781460820301142c0ba40000c610294012000e440100d8a1106000303610b160158881c4501c2d10b8510740d880c07006090951000301341c01a1446103051005980301c00c200901020b0354070401511980ca41d01110045000386822940701902c0c0007079a080035031303040d4100e10303d62003034070903008079000002e04030301308a0340c56944031020806440400c240010508002c0d000e04c0750380600f07071189080c0101d640b0541c504000703c4035851903a00070340c4d44444075000d04d549e0310b42124915580301c1d42414008a4940c3c0f0500c2504070005058070003034040c0c0003e03807094000303511040c0210f08054941e040c1d09600760042050b0006042181c41611340025 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 253135053 1250 253133803 253133809
    0x206040e16030f0203060108150d0b09031206040b0603060108180604030c03110114010b09030f030f090a0e070f050319090c1503113906040c3303020f1602 68
    0x40f0402a9040040c410300a00082d40da00184181d0b022156035101c0e001010f103a4000f400c031441c41c01d0003c0000351010108040c490700840540000c0307085403035050050301c5010400060301c00c010403c0b500800c0c1440029403640c480c80d240c0e50001c2c103400c5607040400180c00c0190420b030088030280c01207410b1503018010164400d115140a00c840c0c0000c00c680200c06064804400c8107100701280350394045400c2506680611030300380c4034600e490481e5a185124203514030345070004000540301c1c03800b07220b000134003c0411841501c181304907600c1502d141e1004005030b5003500041c0103c4140044014a800c580516105822601340216a4100007d00d07240320790b070320041e80d946074408040c10001c1d074a40041410041e6a41c0c0c804e11011204044605c041c14801c0030140c1008600c000404100b01d1141800440d03903500540c040c4000c089029100c50030803050044641480440320801c0350032905044a0003680900101c071842c0140c58110b0b05c29484c281030300880f001143c802589901c0c00218030b = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 253136303 1250 253135053 253135061
    0x1107030c0501090b1c0b0103020909130506060d03020a0204020d1122060c2015160204180b06040504050c1e0306010906030b072709020a020c011107120206040e1603 72
    0x9942c040d40c40c50080e0000741a0300394a174400c100c580713464448516005580c0240c0680700000005016404c1c5032418070901c0c104000e02140035280d60280c040400c0b401c0c1003418640d44110741680003481c86907190b60a001c001e40c40b00c0424000180d543c0d14041009140304014040c00a05d032405901d49004170030b406c4071200b0554410703402d200f40ca03502d05001610102c50b42c031840300500205c00b00c502183c80070505030003801000d40001400003840044c0f40758031502e8884001e001f0348003080310b541c440d140c08581d4150903601904070020703480042c3d02454103070801075000e80309106644c44400c1100c003040d00f01c00301c4000040542c43c3d55074240000e0904120090062501c0d03030042c07040620f9526203140360300340600844200a10030b0a640707a0f8002d095501400c03000003c28000700d00d079507852504000c0d0008202c03c1b0040c003640e6020041d540c8a591320ba0090351195016043c010728005d00c01b4056015000c08a8106406200015006003c10400c9100d030034600c2c034022013103052002c000d0803a = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 253137553 1250 253136303 253136309
    0xc0712120206060a05180417040f0303030f060b1626040602010b091308030702211206010c020307120203160806160801061b03050910030606030b22020304031107030c050109 76
    0x4d9156060300300f02c507566105906502039050041884a0b440b40d040400440c1580320b1141c0c89040b0000e00040c0016070702c0000350481340070b0342d420499038410b00c5a281c1501c609120b140c400210a204c0841086a0000b254602d01c0c030600c038002c040000c07890a812080c00c084046680020045010400c494082c010944440310071603c40b03142e4a08070400742d40c541c00e80c0c030001d03182100102c00503034024003c203d462000c480402e011070720000007001d000e81c0ca034851114640c0505001021442c13950158642c000c10039401006010b007141031062801c1703107a040c14420b983c140b14107a2001c0300b040180e04810f02420380031014151a181c43d141c043c0480020404c2c410820035070f48010008254030040d503850000c0b40740f030401500b4a15050460303990058104407540f1001031074405210680583c012030071101c403901c05115031151281082000d00d1107018180c0e8030000d00408440007225540103503846846420210180038041c41d80519154280c1c01c200c070344580740e6200780507641c1c001483d0b50003 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 253138803 1250 253137553 253137559
    0x20c0315010906170a080c0a05070f14060c10050603030702040f14011d0a0c0c081b0c03010e030f030703110f0405041802100818101e0e0a080c071212020606 69
    0x1243c0800710740b050345c0d01200000540240340100301c035074003914140035907080396800c8006c49602c942c9a4030001003035a054804e42c004201c0c1d52000b0740113828490142e800007607240014040c190103484000000d80320042c0020350500081040c00016a1203200e111751130a038025000449555841d44051503035810303001030720114603014050540f0810082e106501000d628004140948104002e684c0741046a400620400000c228100b40e80728a943e507441121041c011601d03c29080340a244c00c803150b8030584401f42d0400c0152403c0040044c004640048481c41c000540001d60480b01d001c3e50800003484069202c00a820401761406028008240120b0401c0c82c0c406241940054019046c002400003072044032800581380510a034103c0c003941003101d09466250321681603070300060401981c141500c0c0400003ca00700d18031240316504084405500420000c1300940354007581d608120041109803003085c2d800b09560107400c5111a0142c13154001000031804900c0c045d00701540146100c0c0 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 253140053 1250 253138803 253138829
    0x414030d230c070f1509080705030a03060b0426030f360a0501030c02010b1c170a0e0105070c050612011409040c09020706020d0614090c030705071101020c0315010906 73
    0x408038040102000c130195000c0340d44004040069071500180085810142c01c030740c0003081c0c000a204000c402003140008950f802c00c545901c9165049440c0903501030345042419441d484d01e51510000c19100d1802d2010040300d0408160300c480d410254409004181f1009000c03140424030b1400b03800d420001400300c0c2c02e059003520000040340e031100c0f55110341d17130406450364504941107000b9031100c504408050040303180303580c08035500c124010300c048046440301e40c52a03440014410b01410b940320342c1b1450303950031a214901d80046031642c2101100792203c1c18004000203503075580310021700204030742032548000c9600d40300500c1552000c030164a07011760452020000050540b110010556170305020058a803000c908128000740a51845000118a05036000c100c1b258040d00c1074284880880b8020805d40e01c911030341065001c19180c0c42c000c07900601524000a505d6009041d06007010b10482da114900000004d15062040b021503001d00304500060000001e00d0066101a144881300d0078 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 253141303 1250 253140053 253140067
    0x4030f02100528090f05010509100213030605071e0e150a120c2003120c04140112020f1204020a0501031e020f07080408010e0118020105030414030d230c 67
    0x2150307501514001e08040e02c503c006001c4140c410ba441425030316000a038550b000404c40c070f407590007010203980c2d040c400d00c2085072100e84480580202c0b00b540071840905c5c201c6901d140d0b00d00028000241c8030f5801c0c403030140107000201165413001c01c41b60b55503686500c802e656034030030302400c1c5554480450407080108004080a03400c4412014000e105c0680011203d000020031160014420810400c0303900540b40d8160f100d900002803c4c0841c80d00c0c1340b0b8031594a903118503150724402e80c4121034140e040420050314070b40c080c0c074a0f45100c44034040094603104102141500c158081088410000f821200388401e41c00d10b198200003412080c00c0400500d1100c41005850f4a20342240944441e000160265070101100903503840315401000c40d0788550325000450701034002165080000d42c03808500110401014001c881c21136010384880d8910b03152030305c480228207600c543c0104c0f140b01c100000c01080d0314501c01c014403402c2411080500030030507480c0e140c00c2117000d0a4200740c100180000 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 253142553 1250 253141303 253141321
    0x100504140a030b04230708060109050601030509060a0b010e130509060601031112040203190b040b360a05070f03020117060f01050705010e1002030a0b0a08030307030e0c03030304030f021005 83
    0xb00c1d04580c1200d0095010103588004002002c00c44e101205e29006210780040d40c00c0380090750a059403d4004107003d995180001102110022078032070030594041c2c0c01191980c0c2d01a40107583e0214103142601e130072540d5402040e50259260103484070a41d58004100c03a5400030b00100d50484400d203020706c11955080a08007460241d4414000b0b401580008141156000c01402d071b00d8120707103030050524210500f001c1d21600002c68081d503100790a4000034020805c030704070300346550881800400c08a0300b500080309001000e42d600200e42d202d100010300c0460302c100b0240700100024000648402e0643c400140002482d0261240d20348840d42480340c11358840c410000440021b28025450300d0490505502510802802d5625401005000c0c1c403208140e40085110b0000b00d10300b4440d098022051100d000401e22072251503802c140040340c5550700c41e13000a1400035580e011911003002050000b800e43d40159002c4010070802c82c140c568207038040c0070340750720b41e20480f0b000c026502e000105 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 253143803 1250 253142553 253142573
    0xf180607020d0f122d02040506030705090d0606080f0c010320031f06020604021f0e090606040905011805011a070b0a0f050a0b0103110a09030f080702100504140a03 72
    0x2003141800401080000014400d80481c0c0740700c030501000f8803017070b0841c0c2860f59202c8221001c10310082d03526401c0141d00c40a5000f00c8003103c0000d0902455517841030000c551f10307008824001c2c5e0104507501076101141060040708042c11120018002d05e2011800700e510b81890401c0050605050100da24184402c1e02c00a101ca150380000032603980c0d84590390480290f20303020740f180300e11203490700200d141c65000030111320840c82503404151600c01c6c0c81c4120401c11092008070006004110f1143c03150a00d22015900510003900c1c040c10075440c0c6105a080da14260080180c1d141020030b18042c80c006805114010410034007214101d0165409480c0315200301d000140801044002050703500c1c4440e44130b070510811410041100f070400403840406030071120709850001e0304000c070040c00082800c0031541c210303100e03442d14045189580d40d0780201e21500103082d22080e40c00e100720400358581d9510000d8121841c1d88003940d59060600040091000004090280d0103043d000d1000a5200003 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 253145053 1250 253143803 253143823
    0x90f030b0901020712020601050306010b04080c0d0501180317010902070b01030609110d031101110405030d031109090f010306060e0402060706021317100e030307020715170f18060702 80
    0x602118a075641e0044203029200301440102602140f01d201007106602165041c16030b0011402ea8140740d03a100890400c40c000e90040b50704a401050741c0000d03a140c845401f000c01171055001048807107a000015141c4500d442041e80030542c0c619250625845d42c400090250101e00811405d00740903480d200540c1394140802810301d992a44010180090000704000721080245102098202803500030300000d002412207a9560034000c4007503803416900c00b96000d890300034000340001c9000d10000c402500900c0e0325a02c0c0702c0003c00c4051051b4803042c0c0c515101d01c6001084c0259945540b41c61400c481d42d580c003c030015800c0405020060360741f01d0031102d00580051026840e0207001c1e10780407084071280e01c40c0800030180c8401d49000c1501040c81c045848000104001c3d0100c60210544c40e8172080b5268001070b003141c070003032084514080300c00340c04d142c40c0e142c4030342d04e01210410701d0103000d030a54010f5503100c00301003004071141003c0482002400300c400508498100780d14080c1d5204030480d = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 253146303 1250 253145053 253145063
    0xf090a0f06080712090f0c0509090601060f0f050c1501081006080709020c03090a08010b130510051504170307140d09030b0a090b0a0501080c09090d0f0c050a14010606090f03 76
    0x800030690454982203448a0382c2c01c4260f020429840b45801203847d03039240b0496000d6803800d00000d070704100c0451039a040703c00603110084980e0340303e01c04588651102800105120b814454140307400c0080200b21808400c182070703044d480d414035008a14107003121407540715150034000b05204c80540403070307481d003164039160b000344c0c81d01d0b0983c1d80c1c83c0c01d50189031811a0891595070700040c100c0015003150b164200141c0741c0f00505200501c00702d0689100700c80c00e8058801c440410031a41c2441c46803030725021204002c0a0401341c0340e503000100708160015841c040e51010814105100d50522000c0c00540b00e9402010070942c1c420b0090114005440090003107421540018030198941c1c00c8417214aa20500104091a007454010018034007801035401341e00c90405986001d04100801d103001e00b1a020090138032070030808044030508074104030070041240041c5c844000400030007280108521a100103e039681911082908441080e80030504202c03290208000502c168403080c01031b00c1d005 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 253147553 1250 253146303 253146317
    0x601110f03160602070506090105040c120804120303060e1006120623130207030903050c121b010c080304030201290a030215041d010e01080303150904050f030f090a0f060807 76
    0x5043ca04000e003d600400303401c1c1d004410421035038200640c0414440e07031003501031500f610340310007115400c5581550010a0700100300404e10130b0342102010001803920928000c10b07015101c0c0380076514010103071a0342202015180c0c0600c1140e8200f0081461340721818020004075180400640c802c8640406c0b003030201c50003888500f499101c0c0c0e100d10804c4410100c01b5076440036640360007001000306201c2900c0b1401000d0105c042c600d00103402811550480004041003668021003108206001d41403906004441c80c0b840c0014440201541c4668042d400028244000113440030454440507000b14521000303444403080c0d507480b0610701042e01d0f0185c480c40220b4522031b84103c500c1c803071508481c01c07910f501411080b000104080c0113050b905955541d9900f66a14a80c0682d00c1c0015207d241c0e0f000c0110701c076078405061624031558442d0040c1e013190310060380140c8603130542c1d1003c550100410000182c0014504150004800508110b0401c00c0c1c01c5141020003440440050701c000100051 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 253148803 1250 253147553 253147597
    0xb010b0703110313090605100207170313060e03010c030c02030301121104090f03021902011b02130e160e0903032703040b040e0a090f02060c0a05030c060601110f03 72
    0x8034442d030701c0e200711103401101d90301c90203c41103040c0c1080d14480d403003c490800300e000c070711030600e03601810b11980c55400403c4041c0c1040034956862010110840d1144070521108014542c400034002c02004241c50300c15054148000b0b140c20343e0302c1d00704050281400c00f1003000750164000200d0b81100c4c60240c2c100140300ca18684550105082d1205a0780f160908071800c05205c5d0a00300c81400d548240c00725000c0d109880c2c0c01e4405684005000307804200c401500500c12030385c4031409044c507031005201c121080ea00380301000855050081c1034a82e58400080c100035a0618880c00d0098240555182c04520340311020340d940740f10040003004528086000c0021060324220341c41c000c034004030706032070301e85480325002007258109100719000b0303400100108550500c20310829100d150064500c052040440c0c091094070703801148643d074548a45829030307004c28030a0000d0000000203102402a6042c480001042030010415540043c0c00070400d40c08900341c000115203041c1c1c50300c0415016404 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 253150053 1250 253148803 253148807
    0x80109030c020f180f0a0c08010807060e060d0f050103020f0f0609060904062106050601080c0a110309040608010b04110a020307030806031903050c1c0509061605070609080c0103090b010b0703 84
    0x1c403104c0161401080c48082c0301080c5103a8000d244901d8020004000700841800704982490f028030034040e01d41c208007002c0c00914801c40394014406009080145130145881c44041116040e50840700380325600c400600071031400a60f8140d01e01000c0300c071003401c403040d40001220340c4501c403000c42c4540700000b0320810944550b08100300626404101000141400200c04540f000c0c0350b408543c158a49800211107602852280c1c1c0605e85c0070b600c4030f040c682600c01c25210a645800807a426100c1445130072019556170052001500c0e4002c000704180316141d0500c4282c2e00e20610340da4000728140f001e02c52469002045d16200c58251602e404161901c6010905060524041e0081c4a400074514414103400c20000c0000500c20000c0311725100c0300c00c1101c1c22100050020b800000c1e020042c0f09540e190481c050b140c0c5d9212444a000d40c003080b5680c00c0e05d03201865203d503002c2843c01908000c03d090501100c4005003017800c00b448a01d881d40e81e40381c100a014080d80740c485002084031000c3c58 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 253151303 1250 253150053 253150069
    0x1a270703050a0506040b0106141b07180905070503030304030c02151204060c08090c030709020d06150e010212030f0106080406020c0f010605030705031c0e030312010303080a06080109030c020f 84
    0x254110050b14a1050141080c0392126800c60301034900075090303000019414801e4201c118421600b20009082070f0101c54000080580c44074018001c0c41001004150880e0310010840b540349a0b400008100443c0d00c1c1003801c1100070340c0000d11030b8100740704100109800039410401c40e94100c1e0314101800c0000c40d8200c0c14003905551801ca600c0504c02c0008000341540700180350403581d240c1c0c2c1c9c02d590707640000700c0d51126004080350301500010741c00c01003480c647e0054a00c844a00301c1c00720b02c03151200c08449090440400010008220f202d080700956018400c42e503074103103041c0c1c3c01841c0d46804240500d0800d41071003a81c0c1040001c0000506204142c0c0c10b8404415044055901c1d5810302d8185038041e12079070080c11302c2805822400540ea150014424000304c1c980034a610400e205040e041d980103190050080e0940810070111031541108a0100d0103140b01c1c6d19410550f06113600c0d00404c49960342c0018405a01d003c55090100e6040510102441c2d4102d0f03842e80790300d0060740802c0d415 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 253152553 1250 253151303 253151309
    0x20c070b070303061706070c12020a150212011221030b1f09060e010c0b060111061e070903030804060b010e040603051e07050108070c0501271a2707 65
    0x1110380422501d041507070540051080380c006101d0300140d00d03203120707820303480e12015904840071620501000380003e0961a041602e07030f4140c01501c4030341c015a2268240c080f411020040e00c950700041d90040805001c110f540504000780c4142c0010a441c0d40348030b0140002400b00178010f0103019080c14581c4245c000790982000500008000030f50b040881c0c84504c00110001c011075107100c00881e040d4442c1e260070380e4240c01651400a0380031551100d80040401500c0641006410310041c01c1b1010104003040c0500308101d0600035058151050110b5540058040c0c0100191443c08002007540302451f2504141c0080700010f0000070140141c48203403281c1c11441e0010705118000040c03290100d024104492000710007404070418481c1291961000d00419001c1082c4030701103440107114030092038030140708200005480b126a41d204003542d80d456819084c400405080a04010141c2c0f000c1440c1051911750344528104034030f03409404c00300c06440d840b426075036640811134200d0401108000f = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 253153803 1250 253152553 253152569
    0x405030a0503100b16060c050a051204080c0d0504092a052d07060b0a05090103140a02030a0b041e08090607031701030506011d0f040204050c130e06030708030c10020c07 74
    0xa503650080408450130344500702946c205150030103e0040038082d4044400100c1c040c0d40c0c00c0d00d00f0f501003190482c05080a0400d58035640240040c0e441c08404201221a618030f03512095100c500d05801501551140120242200640c00743e5009031121036003007107188a00c50030116140c0b181001d441280386410003007446444000d61903101b42c589404001c0c2801c40c0900000c0c410701241e0300a004561740d8a204894101030346100400208008110040824881c0d000b992824001c5800082c83c1c12000c040654450b1524002d020030450000700c034010100c11959030400c94402501c034414940039a00c1c42c00e010b02c2002550b141090f01c20030600c0c0a010500681b140196102e08280d551150240105000c0d458207c0180800303044d40a0060311900981c00c5208ac10b0762a9401c1c00007910020384411108001405640100481403000c9000340c0003403036000000349007407000c051809903141d020303e815410402c0f40b0154030402250031092014000d2025a40b8061448454503280380355204990f = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 253155053 1250 253153803 253153807
    0xd020d0b0a0308180103050114011b06020f0909060904032003040e0a0507030b010519030f0b03010507030b040c0e0f09100b0301081c030c02060f100f0602010906060801050405030a0503100b 83
    0x100540c440107803a40040382d0700700d000701013810340040d802c485084c01081c03c0b969850349030035103642c8070301300c2005070860100142c0f908413019500d80e0309903040540f0b039402031900424802040e0400d4101181d0200c411201e020365030506840142241010406001d80111021500003088404204032001486804604441d0b4038210b00164028001036034a0f800203030405000a00661041060ba500351800e00c205070b03010070312010280c00810451031349030050345d102d0340010ba07195000e01c5910320404407a140802c00000302400c102c00c40300d055100c601404540b03240c03010184c40e0303c11420200c8000762070841c0070f6114050300b01100141980014004a800000440e000c000821640210319100d40d4050034248045003d4054038a00748030744006910260020b604a500c4560554018480001c0207240c2078880d1041c10411203644c100d00c01607912800318108100c298030481d8014a20140204001d04103507488644920403011304000300040030000c5040300e41c0c004050401855450203141d = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 253156303 1250 253155053 253155059
    0x40b0708030a060b070506070e0319060209180c090d08090415030b130b071d04050c092d0d141e0f0606061c090b0a1d0a02060d020d0b0a 60
    0x1440320391089031070101150030035100040ca82c1848040d201d515a00ca800381201e035481d05011100f00e45140b41c50b03070381403092820b100c0140710f07c0c101c0511000c1c0500c50260b95001c00d00c0c00d0280d010504a110300411042c8010840070b150000300b40c52150400302d82403600440c0a08081c281030040c1c45149901074070f0480500c80003480244810f0441e40b14000c5040b007541c854100074180c2440c01c0016119450420010348064031880141d801e00420b07160060341c20060501060885000311854000d8407000a640007030703450f210380315030030000c6a0306440000241402c00c0c5a000c035412f0141c280503420a08490301000200300350000000c01103412a500b203022001d03851041400c10281140a009040d41c50344c02d090082409807282030040c08183c07a001500001206900780c1800003c5095510504075001522803a06207001c1d05240002050010030b141c4000c40000050703d00f40e650364000380b5240010303182d040503100001500800103859510203441d000150803080c10440d407000a20b2008 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 253157553 1250 253156303 253156313
    0x60301090603030f080c03061c0b040b090c04020c0705010e120d080402011d030a03081807080307020102150103170702061606140108010c0c1b05090a02070b06180417040b07 76
    0x40702168000d0b941d510282841003010703129501d080d40ea480d0312940801c0080d00c1d504040410b010a08801c80740c1400350304150f00e841c3c0d20400140d2341181e000c0050401e02c10074940c2005a080d0a600403030342189800c0b50094040d03514941845014188028040711000c140c3c1e459103081034000130641600c03900c2070220303002050032b64100c40403400300319000d54400b241020141c040c1c00440000d0000c010209a40c0c8007565040c9009200140442d44100d41c559500b41c01d021207002003100d4002551075202d28800a41001088021039a56030750850040020805250500ca201c60182030095900d10441c000300e541031003101c07058000c1c1040c810080f8100640c940c0311400c4035404010400c2c141c0d0b21202d81c94240c1b81c0c0c5164010005114806481c0454103841c5403d03035041f88442c2841c1e409558001243ca440b03005c413048210154081020700a200902c40000e6000384110b400c0710301002d081c0440d4001c000003a2010303101c60010b03443d0342400d900303580440b40034081d0304400d580c883c0250310309 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 253158803 1250 253157553 253157561
    0x3030507030c030e0607200307051509030f031f03080316090905060f040b04020921010c03060e070f09050616050106050301020301150513050a060306170f2a06030109 73
    0x20010b464055100040c0d8841c3c400d002e28400c3c0c0c90302610840d2035200c0d0031690b0306041d00c00c0b40d2001f0080844120700040810040005510500180000078050021580c2880c001440f03101d045e001000b0f440400c02d01101140e901006510143c43e00d803000034002071807010b0640005084c14000003d01c091044c1c165040b003100c080300e54441000307603150240c0b4401c0c2c8030291a41500103000d4400f401c80d170b19207900007200030600548018180380c0a21f0010b01d503050801d49041204c2c107042400d00d00c062007030180342c1d4a62080e003401d00c500c0e8507110501e0500800205000200040069043d11441c401c80100004200050040307484a03101d681d00f1650401c041000c8510b9860140300061a050600a4074125022840c5c90910405881015034003030342304410175007140a503000045202d648542444014240640d80000c482e4105000220313a0349826085006641c8042c1c041e203040035000070070301c540c8414428220b0541100d4443c3c61004404500c80503032040b0040004110031200d030380 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 253160053 1250 253158803 253158811
    0x3050909060f0303180402070602030c0306100302070302060601140d05010b0a0f18090207020604090509100f140105011101060f1e230616050a120305060102070803070b0c07050703030305 82
    0x5030124180d112102000900c0001807150358241e0001e11006200c8424400007841117003010300003502c0e2032803560b201800c81c1d1003196030903500301e07011007400a1424188070499010388642030451408100c1d45001c2d584610041120741000703200301081c51001c8000f0141d0720000c5d4207039403d1055503100c3c012031308150451208a40082d2041c8444400d6510408401c0c06041c2600c415421041c02c1001e060040c0d44401c4060343c000b41e04200014960500b44a460303c01c9111802514210041c0140d030001d0399903691084a826003000318000000d00584003440c1155000d0030610560040b40c140c190250840e41d12a0b08101000c0c000014030300004914101c0c00742880030030080040d2242010412044c9083e500345140c8424000c00400d802c25074000d0000e00015800801c4411995603100d00d045240d00c01160380602400318540c126070103008464000e507090015000b0a8142a0855641e0292010181c54030b00c410010560b051040422200c9103504001518007583e12414050042c0109507 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 253161303 1250 253160053 253160059
    0x1e040807201017160e0612190504051507180618080f030d09021309030e03060c090f060304290f0604060605221e060318030816110703030509 62
    0x204007190b610712850150103d24a080d0382c0300e00c0c07502e50010304113480b00580c400c201400b00d500840750860392000080e010f0707400d040400d2415880c2800c0803454101ca41e51440354820300700001d0000080c008240c030303222a070010000318800c0e60380141c01c0301c2440c1c0f01c50249099030442c19002c14071660041041007015001c3c121130398030320b075103041642e9529001501440f07150004c0c806031040c40065080001e03214002001d02900b040c048840b14110fa1042c0d20480c042070031940c0f00340860a00384403855000d00c003407400d14140248080851110345070494001e101c2d14000001600b0018040011082860b4001c1d001000070b040801c5c0e03121030407065406030000b031244000900c083c50700303000c0c4200750340303955403214241400501000741c0d04200b00d003090b120f00c01300d144c080b134110034400d070f40000d40d00048481d0b03030381c54900034000c0c0c1182c6020380a00f011a070421944004039030000c281c10341040310300360421001d981c200b104883d8541c40c454030300c2d2280501c420010501d030b40b01c3c01400c080e02e012 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 253162553 1250 253161303 253161319
    0xa060507020f06040509040f080d0204171606020c010c05010216050606120105011d0403030b04050a150905150609010c060e060a0c082a160605040309050105031e04080720 75
    0x300040041c180218490701c0da101607008001f50000c1c80f051000585144608541c5050422101401c01603801075006295202e02403546481000300400201034000300941140900c1801d0440c000e48841400d54100e0520005009001c02c0020035030407200c80102c00e48140000c000b25281c4161074920559030548a5249541c4050014006115041c12074040d5884a041c503485014483c034440401401a0245540d60240c2451a00c640c02114400d030103007200001e41c0000a40f48540c082c1850300486a00da01d040100a90080e0010f1070000e0f101c0d040721030940319002c2400481c4c80440c8090300034401400c000c44404406030004100d801921200001d20824071185070440701c405080364030a0004003501c65402075104480310000c2e211082c01f240031304c4c00c011703140500b04090850034125142c503594410030050551111311040038140034039155140d07080040c81c140c4696940e008a010040b2120080342c100600318044403403c0d544824240548106122640c51200c45071084500503040 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 253163803 1250 253162553 253162579
    0x10e0a02190807030f11030109050a031e201c030504050105010504020f180312040b12011a04030809221406100c03110a02091006030f0b061204030e0a06050702 70
    0x5807a040301540e008800600c5200d20b5070301e0b40750b02021029819140a00000d0304501c030364800307014000c6014060700003405d00c10400e103030040065007481c0d0540d0002015400c03108074564441c40c480810302800440045851100400a007032a420742c000e2001c17041650803103e10540c054019600c0b8500420003007007241e80c0e07034040c442680302e82116a012860200007a4412100d0800d0280003c0b074040d04403011b46034a4444401c00e81d0054100ca06e920b8808a800c840340b03c100000e80e4054996a03410584161007419072001500460000828090b4045084103054440241c9990009004c225a8110b181d81c0c02d500b2005210252103c40790f861302c00c0000340a42058086c8100004040d540c00c00300b00d50310f88003105c101041008205803030103040e08410140c3c0d20314000780d0289406405500c10350749821b03c00f8040303402064070148042d0604450780320130ba55080070b036030301e5411415000300160382d1403908030750031302c00040084da10040c00c40c80400d08a5011014001041c4285c0311001c0b4802 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 253165053 1250 253163803 253163839
    0x8010b09010b0703080901060308210901060518150303070c050306092b020106150315060f090608070509030a060509160f05040b030313060e0a0b031b031503010e0a02 73
    0x4002d002c0d03010561070030020100000c1c03240308050350007100d5000001d0000c0e100e948680031035000ba5840066400484000f130700d080041a681504601c44000030000079203040d01055000c42015015040241500d002807002001d6a17290b00c07405400801f541d58424980c5003640014015005181c020721517080080d6800500081002241440c0780307101c241e500b00b40440044410414020310b085540381c0d0000214651207216000148034651004110700c079280750708200d000c0740707a030081c010070840c4d94000e070b001a00064814150380c01c6140043c2d0503a9043d07001e4480e03224000d0103603010700c540500c0006101da20fa0010b4050b44200064401101044a00c00c00760607581c003c0f1078a002000f039003081145020342c803c0ba207070079000d03041c1d1742000c6000145083c15102540070030302150803035607213700d9031a01c040b50002030030301c0d48201400d505040c2e00d102c880d012246011044044c00102048444514407850b6541c7c4100034000c2c81220b0380011155120b000344001203000c0c011414001d102c00d1 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 253166303 1250 253165053 253165069
    0x1120201052d12010e090606120c06120609090a112b061e06300f120305070f0206040f1104020f0d052503020913020301080d0e040203130f05240108010b 67
    0x89001c4001f84240c1e11508100f0035040d1042d0807020f000d2003035841030420380e102c072070183c04e9203202c440c6002200d107010418001c00c00b0000303010a0307540d000581d4000000702960000d044c01c180035a4805800310b0740d420750140c280d0038101558105d1b0044049142004640e810822514206810103441c04030f10081c264144d0310320b0300600400c1e05081010040400004018220800b104030002c98403002540780c150f44207a04603019605100d0344094010083d030503008858000455140a800b540300c6000000e44070303003000d44010034051440850909100c15216120702e8118020000c6569070105005141c89600295105e11001c0c10480006c034200b0604604038400220300140c0d502d00300030301030101c00079800b4042a50b88a03043c81d01c80c890741d50b0644050344c0646124001041c000c5c031f0404002d81070342e580c00c1d50b4038031650042040109010042404881581c1d1020160310a44485e28100c2d040c40c4019583d0034501d00980f4120040c4080301d2040c50480300310100810400348014140000d030 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 253167553 1250 253166303 253166311
    0x110705281e11030c060a050f040f03140105011d010306050403211d0a0305040605130b070309090b041e0f020c010c0804030f03050106020319030207050604050304051801120201052d12010e 82
    0x400380c03d100d145599801f9a0080a50306103064440c0d2a06444894040620407203400644203040c8042c500080c5080912440c1d000d040c0e03201c0032102809404561929034001400000c14154640e00407404060080409003595955030600c42009104001094010910041940504208240c140c000d40d07030041085500b0b150195a202d10b86402c01c00c050720381d0b50064540161040a500c2c0000e54965204d000c2c1940382c0c840d43c1c07400c4645240c090703c803041e0359008030b18030710035403402d0315910010490751542c0560f0501084082030b507841000046000b801a80742c400800d5081c5281c0380c4c803103680008601d100710321076211072102c0c04804c44100c0440d01d09004150148e407042000e18004004a584004404011316000d4a04506036075640d05041c0d040e01d0407500365002190030f004514101c1c1850341c400c07000c054244a10740c90209240b18004440c00c0103030510a0024040c80f6a88030301c100c00c05007003004400c2036040c036149094400c46500002601c1041e0100800101e203c03a150b00b00b003405 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 253168803 1250 253167553 253167559
    0x17150f04020f150a0807120203090a03030b0109241412011412032209020a020703080a1106010e040605221104061707030204110705281e11030c 63
    0x41a603540c0d080c811200d000e01201035115441003d240110304641c8010505045144c0c0c901d112810201c00c080c218240701c0100290b8940140100302d58604005055040a80c061030045004c0400c0030041e111100749403c030454241041c10014100d940f4490160004041c950f18264008090121038070300d40036150102681607189001080003048090303501029030750040c8102c54030410501c126145a0241d001e0b21030442e03c045460702c50414514100c0000d2101c5441503107058181440203441d000640030003400740c3c03004aa4800101d20070041c1303c0092407413004503416540c4502ca004c07044082120b049070828100400200041c610581c40700011a450394800070110099842c14144000340e41e10700c0d00b1035039030080000c0f2110b40000c0341c840c041440c1c01524280b411401840250f4800a11034122030320100320003070000d41c0002c0c20324401b440c107a03590a0401d4012000c0c8003600c42c852009010503914542c031120300c0b5104444952106d204072a286843c1007454149600c840708682807580c = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 253170053 1250 253168803 253168831
    0x10030606050304080a140d050a0c08270a0c061e0504030c0e18030a0917060411010f050702040510051f020309130b040509031306030e03070201050c0114011715 70
    0x1000840304c0025001d01107103801e084001d400006020100f98120401000700681c5a03000d00120801c10320960501c05683c1c178104005281c040a510355180040e0b03614070b07541c00b001c004840703024814040d2095481d030000ca522002541c0324030090894900e4410300400011214580210034015030840d421070341c0c442c030201c41a9103000304041d41e03003000810283d00e0300030440312030010340801c0c0001c1114418a444001c01182401500c0e480d01000751580f04440c2d011009110104450311f002c1c05400c2c00901e0310146c0c81c060201d0440c5d1500461100a40050404080c081c040301c050401005541301500d264807a681c1541042c0800c20b0000c01c4c00000d03030410003400807036060414030007103595502c0d4001308110000f14041400c036a411981500d00750008103900050403200b103290801440a45001c0c801c902603150029124400d00e04024184180018680301100c42174110301c042d005412202031081d0307522190f00b100a00340007407038440c501030340210000200481c008940034603a0007580321 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 253171303 1250 253170053 253170061
    0x1003030c0b0a0b040f06180b0607110a1502150c0a0e09071b05010203013b101508090d05070c090b03070f080109020306010f0302100c08040b0711100306060503 70
    0x100740040549180c25107503c6641c5210542c0b04c500484e80381001d030820000310303180703040c0400f400744c07a91b4141c0f000e00506003490415260b0391441510415504080000e2101981400148074103400c0d0384a410091040740c0c502c214182c010551002c9604000d1a280312a9105150000e4603c100e4041c100801e0324040c4e0740840e800c104962a40c000480d05080884130349846180c100308024001c2182c03640c4d0000010301c031200500c2140151840c10391842424004050103000540c190301c03454400c0c050981d0002092404020041d02c001c11601c2c00101c0c1150410800401110080301c41d05e03c1c9104407442c00310800d200c0e1045900094000001200391782c1410595405020303509102641031180c5003000c200744000240190003000c3c00b00000031100d010784141814458160310640310712243d00810005130f241d6950312000c2c0001e6140c80100419a8503042a90340516041000c3e50f041c0400c6070010403091072840680c41d00205d8284c084880014400c07016601c1500030703200010340030300100f = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 253172553 1250 253171303 253171313
    0x20a0305280b041e090c09090b0a0b030316030804020f0603240406090c02031e13120303060e15030f0d140a030207062a090320040e071d1003030c 64
    0x100400d0000420114035a00c0c1200002e1260900300c0e55043d42e1a910a1707010308120f0030511040c0105003c240c01e000740c109640f2032500401c4c000b0404801107850b08020401c907030b0f0500c200e41050b020b104401c01e00d1f4403e8100140861001c450881c02104181541c036040d01d000c1c000d0700c3c45010040c00150940941507605c0000c4c0b0f0343c201c001c6803c603440e01d00100d180081402421342d860365640c015610341762201980b1912035250384000d40c0d600300070444122400e030b640724454281c452109030081615604e25040300100301c0c0d40d010003620030140061101048402100700660030084003240c012001003003c039030f29961003104003804919901c0808200c201040054040e101040c03c0040c01d241c1c9540b070b00810358072800581241a500c14581c0010322640e031b41400030100d1140340c0003500504550300c07541d0004005028207a080310780170020500d80d4958000e09580e41100c4140c8011503500d85e1041e007410340d2003000801d606545000500030750941d560610440c6d4046d9291011400151a0 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 253173803 1250 253172553 253172561
    0xf04051501110a050607030e0d09030f0201080c0c0f0102030a0c18061b080301080c01090602011a2101020708030403090608070905060f0c010c020c040c03060b090f010207050310020a030528 83
    0x24003058020008910003190085c05042d200d050ba6032030100d402101b5543c410b003040c003210b0442050020000043c0045440000585070b1140e080c02c050b038482c1c9420108803000e004542c4000b50900c41c1c04807508451f241034014501a4000060511190001000c11b5030400c1510080d104c640c003801608001c0941f240701c502c50681103216404103210019107503440d140d032098010407200d6101200b4400c40b940c2c000b0f408002446544001c200402c074007000100b000080c0840c4500c035000001f040000b07a040080e085640c4188130300215500c048602e8201000e810845055001c6503001c10001181030040c4010361082840d5502e02e9809420b1004105094006080700b401c14002482820408c0200340300b181214142c0c0d400500100b110350041006880c914803a1200300b43c1001130800000f2540350695503000421035420025194140041303103401c0e1954041076061080c8001c0e1002d0724195402000300301141d546c1032020fa9588025035424030841d6801007005419001841d400e0111680 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 253175053 1250 253173803 253173827
    0x17030702040b0415080a0201020606010801140f010e0301090507030b0c1612091502030c070b0c0c01030e031e030405011406060304020913150f0605030708070e1306020d02090f04051501 81
    0x91480c01d80f0703544c440320496900311042e82d0784851441d8040d0b41e0100007040e48030100f407922503070310345c18020304688843c408070102d80900c0300700812200680c092920300702104c4000d07008001d1a00941860360b920787c1144030584074034400d007001c5017010402504444035141c0c100d04090241c48d142c0d0b0b0300d915000d04144a82d0420181b0074020510815180081184c2e0303c180d0b00850301c0714545510030b800c1c01000e503c00589020108880100a800440d40c9c400e40790b0242000076259584100e514210300c20201c803000001105105000c0d6582180c0207503010300c0c00740000308000c80d52088500d0344100d0075a11103510420600000e40185041d5615076481499540199516510341d80c0c0e004000001000600d01c00c0c0d21034260301c2c40cac12410701c900d4000b814100c0c000c1c0012481c06295684600080c003403c80801100c100040d90380e0190210000b145034400380c11941d46c0141020b000c0250860301c3e0b000d118080072241d160301490207020b014010340c41381858151034103480c001500c680b01628 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 253176303 1250 253175053 253175059
    0x109030527040609061403070303090b0912030d1506020a050a06052703030610171303020f0a05010603020405011d0a0509012711030d0801090b010c0204090f020a17030702040b 77
    0x204841d0259226401148002c210074140442c0443c00c00607800040c1300d40f505141d000b035210400400100741e01610510489a02440349951404e114000c074068071f400c1c0310610041c4c80300003103a565911050303110519685c5551a02e0340100c2d00c801c1704980b12404014054942e602c94211131011841e1b50344015003050440b95001100d6075548061483c0d40ca010300c11840300e400c0030041201030f0512011000c400e0351940340610182c13555140080054601414022203142d102e90002c04240c0200222030a450280086940650191030034902030301080c08202c2c000e60030403000040c1c0c01c142c00c0740078041148000c0482101e03a6800010001050024110f48c41507484000f120710880d19080e040d444807075030020b214842802d6042c26221501c91141c940d00a45c02201249265680038a6080c150360810707402282c80c40301c4000407184c03803401c0320b0302039405440c0025903410050990107500004c0d200b5241000d44581c3c440c10b01c512164803207001e04040e04204403540c0180707400d501601e5011802 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 253177553 1250 253176303 253176367
    0x103030e01090e071b0b1608060d1703090102090d0f120801052d061c0c051e03070306170a03030e03031311040906060305030315100e10020a0602030c090a0801090305 73
    0xe440350f40d06a91b058501003050360800c083c0402d503aa1150840e54000c20694000419000550702c0300796500701091100b10b40f0f1400b001240700d515080d011600c2400004111042200075410b080200b0050f04008840c44104054121800b40c040d05460b41200c1c1e00810003d61040c031050004035680386444030f4035614241002d480c16986e10070002c0c1c80c1c3c0088542c03a080402e10711061910031603250348005018080705100c100300081d075100c1c8070101c1700090b0b501d5640700c0d201c41d4020b13005400c0980000b0b207100302201c1c02c850032200006120311154001da80610501014503d03e80d03c030301c421748200360b00407a4000c60401040e0b0362002401840e102070000200d040c0305850324400c1701d0091304111142d8000005102000701440707003030780021404803280040600b24040c0036042030b5030b00c41c01c0b07401200790044a4042c14000d0040e03040507034014105541d80c0c901100e529501d075004a00c481e06c02e541109001c51300c203e052040c0001e059050700c0e0740d842c000851020849542030391349240914440 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 253178803 1250 253177553 253177607
    0x904020316060906030b090103050309012010020c06150a060309170d320a050a0f1b0306080703050303010e18160905180a02060f210103030e01090e07 66
    0x945060100904881e40c40f1900c039810300c00001c061380c0c22001900e10a580100040c00407940200444800300780c00d00300a00b00b03400c4080d48004e03030f0710345419540030b501421256044001381038000303054030a06a011b40c2c0040e0341d030994200c0492104d178081a00000394030018808580280c0c03041240318003501e08100c1c6000c4041008685610030718031070200c2781d140d01e00c17820f103090303012025090020100b003103680c0950103400113510503000500d86014a9260300c0401d140001c6540310150311400c4507000e0015000e24401d515880d43c128141d08002843c02d8800225100d0202e20031082d00da001015518503403070701848121182c40584004400c100000c035145400b02e080010844404440450a140f20315040032501140d2004141040311408002e03143c903d00c034041034061b0055070458090340c940801c3c508e49003e41c00b424202a41c2200e0500074046400d0011059030b0480303120741e40750341d46501400c0044403900102d106a800b003400c0440031a40c154040e55043e418908036403d1003900c861 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 253180053 1250 253178803 253178833
    0x6070f021011040312110a02061c090f020a080c030319030605061c0b0f0f0409030e0d060504111507170f3105010212031b2107080609010509040203 65
    0x100742284010030300003c00304200100000310a101d80e0f030313604080d0300303240250115035141c0d906080c0081c8034450000300c801002060a00726811440e0449042007414141d1400308208034501c6400e0788110302e03100c00007845640005d481405c8141c06401f460400d035011102c941f040c190012000c05050716002e0101e803e03241c190240600f0310b8400400c6071b121044050790000c1305e141c003032500d016141408440c0b00c02d423903004629800c81420746001492100e9800c00300c900400c0341c54050303408075031617042c082400300d9600050f00440c09490307041c5c0014441410400e02c001031410400d50f02c841400341c000071038440304200c05151096042c0b98030344100c805480034035520607000c1c81c2c6420707510b2120036003540040440c944040c500511a9080504000c0083d60b00c1c0034901d906180386400100051100c909045119402c050030413645494048006483c6011050010100300135000400000c1c450b42c80340d025075000700d002401ea00c040740d091005000b00400700400580e0144501c85641c0d041d04 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 253181303 1250 253180053 253180061
    0x1302090607080d06080c010509010f020f010c0203120a2003040c08030a1d1002030f0a030e01060303020f1009020f2b030e01020708150f18031602130e06070f0210 71
    0x41c41401c002da515010900c082003110010b41007405e440d8003401c1030b600142d07000b104565003030300c0034207045292100020303040740b03441c0d6060010716071075080020901c80070780c001028049101e4034075152030781e41d50b41070780c03020840e00a02c804443d13441d02054007240d80310609000710740003406003603500070841e00c41c07074584d107140e1010704210001501000c0c6003a000900006180714850100d070b544078288a00c0000a44c0d0b070049517108040400001444a002c5009900040d1340c81c400340003c0c803110340d59090203520f94003500c180c10018003425020426258117803048000007a8010040351074601030341e080c8200b00742802403520030390940a60301d1000300140801011090310a5503403980610301c010009090400941c480d000c40e81c040080407074001c000043e40b5a10401c2441001d400d660769081c01710002171030005040541c000000e0f4034001031110b01031020568002e455800d040e41541000c00210b408074410040e4079002440802e104620501041c2c580201ca441200c407860f0100000f18100d0b = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 253182553 1250 253181303 253181317
    0x30f120105100320130e0109020307020705030f12030a1d010b0102010606021605090601020a0b010b03010e010b27010e042c030304031407051e010f150b040513020906 73
    0x5840610010011071402e01c8500040c1d91551a081c051114004520b01030082c940c20403005004010640c0f1854840c8000050000c0c00c0c1000c2803c05565580f8000c0025401641c0650050088600101e007a06000a404511795034800040101c964074490b82400c6400151010901136200e001d070743c1c080214010043c0401501000028118007660006821685141e003c5815904031a50107a104603945602c10102c48042d00d445401d5a508030040781000a030b40d10082500718824004949600c01c100518142c0f0303001004540c5030303601d682880107035004d41028190001c2240e00b120148044040c0f030014500300605050003801d19102c00641614590071081468500c014140038004594102001180c0303112000b071407a50400d920020440c0138044222581014000303884000c000c2c0400c40c0f4050030705e0900c0414014039125050a0180c43c0d000c0f81040d134907040100807065820400b00f9002140c051901c0d2602e05460013040c00354110040306000c0c00658240b180c1c009940f13a0600030118 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 253183803 1250 253182553 253182577
    0x3050c0d02150a11090a2403231003020306160e010e13020a0201060305012405090621030c01050a05040b07031e09020a031407050a1a030103030309020d02030d020c15190f02030f 78
    0x103100c00006000942c100d50405150405080803999408408088100b02d0007404810200300036641d0a4070041c4ac1c004941e00081d01482a9010010400501d45084180a455941e150b8014050800440398858030094003a1b11a0544034051080700e4142d0040c4814072450002048a99480d1202400c40704e4031030306501424041230b96501080301c185090700190a00719046901420b1250119040340d403040d0b0000c000c409001c3d91165444010010b0340d00c041c0d201c0000744100d01d81203189101514007914100c43c65491000420021030080c010200004076500e0804000c80c00c002544002e049100026030300300030441c1c004004100b448015800c080c603484010180e40e0325040500404444036807100e2032011000850352218401941181c4c1120b40600d004100c004080c000591000c4240700001d42c14410400055082c0b9000309007404c2d84c005c103d81820101120071102c0c801c521a03040b04400700c0180e447c0300300c1020300481080400c038132103104070381c142508544074001d1a0302c56074640b04 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 253185053 1250 253183803 253183829
    0x60702221b030203010b090105030405031b0c100336061d0f0a0507030204020d0b060a0806090a060e0f0c07080301090f18030503061e060703050c0d02150a11090a 71
    0x401e45070004003103541d44a01d0300718910740c5000710707804960094458244c10408000042014004104241c0d03d0407007203843c0e5102c207180d40340e0400d80c2d910308011015005c0d03460b1415039201c0901902ca101035a000801e0251401e601003c24050060282054410024040c1050030f0202e2203910494034500103403490b080c0c0014082889510b8141000c2c0760402c1644030404d05000120089404422603034195800350f1034070808160390020f40311500101d9049500403401070240799029468030f01030103041c1e800541e9621109000000c0e80d4190061841c0a040040402e800e1042118002e9120040c030891604201c560307071b20300345598003c2e444001c146480780b92902c803141c5244200703c1c0d100104007072008504913658001d40343e400300400701485124191030759010190312406410046000401044e071341c0c00c2034500a03210390000c481800c0745106060441d61500d0002401c1710f043c00f203505001e410707682c2da640201c001c1d20940140403040d09080c4201149078a861940002401840807000 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 253186303 1250 253185053 253185071
    0x504090e070815010b0a080c07080a020d030b011d09040807060903090806090304240306051215090f060c03070507060c0804031d01080a1503080d05010515120606070222 74
    0x280c0f4100e4618004011055020010071003202508211003510300c1c541040100c83d0b0302d03542c521006025140010340007403c00038a41040c2903002ca9164150056500d0800c80c058942e4011900b203400d2203024682c0314051031417500c0500d8064101540709105880fa686406503558500003910301c410422000316017611010706c0000010300a0540c05002c650042d41030030b1038152890b00e0000082214140e00b80160a100b100511941082c0013070440076104800c110100300b80700d68bc0f1154030041d00240030511011800f0440c0c00700c3c032109826910340c02010795440361401003141e64009040181440420801c540000380386004036036000d00315440301d406a01d400e0134050002d840f00c540407801c16100c102c60b2126681c00842013500419441ca0000e4581901c4182d040010000d40000d0110300012400c07a001d04010b400c614140c9405540c0da003112088200c0102040c05114406100c0750316103400584681821070107401e0080c0010001c090004450803080c1c4201c0402076180c4005d600c400c001 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 253187553 1250 253186303 253186319
    0xe0d02071208310612061202280305060906010e13050a170c011a01091d04170702090702060a180503030109091a1503010609020f09100504090e07 64
    0x2010142031200503450266503480e054440c80008080c181c072442c20f407081c80071824154a03250742030b0340d041c5010b40e41c031044090800f1040122942e0f80a09292001c2030060103802c111005940c003914031070a001411404214141001001c03090400c020030300040803070b0082201e00d000d41c0c851000b50800754180b03c4d001c81d02c0c800017400e1043c02e111407040b410009500217a0214025042000200c00760281c0094550503c10020074807a0f543c04c0902c8504100c07108640507d043d0007d0f200c2d04185e998400c41500c5140160065a40018002c00000d0100f103018032070452030052070b111646024a181e00095072504190303007480040c2d0052040201c0f5200030320881010380c116158480840c8400e07650340e82c1d80c1c0300c140160310b061900c8541810400c14618002c0b2050a10f40c0b00204551600281949048103202030f020301c2503080640024005c4181d100303d9888000340341500d0714181c00502030003820710790100d81004000040000198130180c9201e4041c0d0260340902401d1218502603130 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 253188803 1250 253187553 253187563
    0x130b0301030201171510020f070905190c02071710020d090b06040b1e0a090c0215100e1812030a0207021f0c150b151b0a031d0406090e0d02 61
    0x1010b5040401306101c025441100303034140c0800219070040310007107184012420030b0700500340d00b08148150303100842c52640300c0d08164403819003c0303c071160000c02c1001d580140c0e0108001d200c052381001105200800301c2000341150041e810303003140c40d400900d28140d012a84110858401e26a440341c408040103140304240d80c0044c02150b09110703020114000814040c0741446281e00110b103444811882d4035021420001000581c00800610031901c8029488403000c2c00c400c1c04426410b40003070441c5e49994840c106039242400b02e0000b51b40e951024655030103800b9800c0304144a01c01840882d14010001144111030b85400543c403a5010b10600c03062224040c07980490b82800d80300520950303400201e2440740340c0c2001c4042140d9680e640000010007a40d8001e58010550846001036960744000a02070702e1030b8001001440654000095143d08046000600181c80200e0f42d03c2403080c0d20225207a08540100005003560780d42c5110822110194442c00041d04400c003541011901801 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 253190053 1250 253188803 253188827
    0x30b070915140301050d020109050306010b0c06070306060c0b250f022a150d020a030903080105090403020a06230a0f0b030318100c0602030406060f050a030c090b06130b0301030201 79
    0x104500c1002d50002e80c06124041405070b070380200c80c84035044056a04c507484040003000003030203803141561100a010f00650042162815030321545021640c030600c80c1c0700b650210380050366a2504800144c0d07545502980c05082400d04200d089146204408403645020344224151507003221254140800ba00300304980d000020640d200080079003003015000c15440e00081e0440b007070f0503803080314825035040f40030b50400441c2503840441c9a82106030507601071101140a0b40b1031a203d82c3e82c400130803d114108407401801600102c01c40702c0060080d0700080c030070100c416007108008490300a4003100e10300844000c1c001c0c40c2c540b492640344840500c6810317050b80b016409540750900c410481403554144c134080324024200c041030161107078400d44036480340f0fa5108034103642c1d904107804c20602030702140c051040d901082c030800148903d094544c400c200c0754495220800e030b41c940f010b82001441c000004640182d0704000e00019203883c0e6520310003a000716105140c0365415130000524040f02a1 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 253191303 1250 253190053 253190057
    0x11030d0f0f09030c0e070c050304030605190203010819060b030d0207090c09051f02010b1507020f03011b050d09050304180b0f0a050d020a0504110d0e0105040206090d0804030b070915 80
    0x800a00114188105007011750740c0070143d801c1e0070344440d542121700403080c40c809003150102280c00300801c400764018a005802a6102d00f0390b603c2819561001c0f44004c2c42981040d50050300110320545401c04e181c030351580690b4001032640340604c08242400003141e00803005800c41181404500d1b1184520240159545060040b841c00c000210b250064240710700b0031540558810092140d200350080c054040e005010f2120341d4201d04c00008840d0400e1104030b00c42d00502000c4650f0b41014803a00c02032000710b203500c801e80c502d502c07010341d0b1340d92086c00b4080d50143c0355045540443e004200520080c80c1200b03140d86000c101c91441411aa0301c1c450151141e40840c507058956aa030b100c80e2425a08108c81c00074080705944002507036a180d50303001940040c20050400d070380c040510051300b007400b50200b00703101d1248040c14080c22504c046070002e61000090100c104603007440d0a40810407842200490b00e0640c494542040c6150115407140014280f55001d00441c02c0c6490440c0e00700480d4 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 253192553 1250 253191303 253191317
    0xa02011d030304020a030f2904140f060c09060d06030b2a0301180b10020319020a1502030c12090105160f0c06050c130f05032a04020711030d0f0f 64
    0x341e00242c414440752101800d080c01d9002c80e5000d21081800c006080c21700301238035000401c1c000c5440408402c00311002d581240900c00851074801d00440c459a1444101c4084c001a5443e201030706202c1c2c0040c9803440d004441440405c043d40302c1d9200b201c0246004030040710b03880c82c0001d03041c0c01c089120102030211042c2c41e00e0340780340110b030708050324190395100818402031940f5800702c5c001803030403446455204040317030840e903882500400200112280901000f443d624103031000e83c5d880310200c2008000c141100082c081c010100d42c045e40e00f0184080c40c0c5480c1c01c142407810841d8410070380d1b001403c3d95540b400d201519841c800b1800000c855410701d8800c1401d0403401804c1c7c1508124082d08040d05c41c0c00180b05540417000315119440d20b081a04460764844140442c5000c941c000c0d513029100d0100f1101030840091250983c80304600d064200b511804018800650041901119000c50b02c4400c85410741d1300b40300002040d8029910012030f141c0e81540208600090440300d4140002 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 253193803 1250 253192553 253192561
    0x1107030c030e1f09031407050625020d141e0a0f060b180a0606020309130b0d0f14010501090b0303070605060a080f07060e0307121101030902060a02011d0303 69
    0x20400340030098160030842c40700742c8544080381d0f62907200c801003a081007070710116002e01c54002c2c1d00401503d005040100c0303110386038111a540c500349801060750261062242c52503002103405043d20317141540800c207006452503400724a892a100104032648001200c5201a0110401071100850039011050442c4190844001d40301c1b250b5240250000611540100c10320080343c00091110401400760403e9001da4100c08588000035198210114100100001d64a1000099075aa180001e02e80b03403180174042d03c25001880c0d5808043e400500d981603800125500f41044a21980120f10700c480c411200300b00b242c02c40b0340c160440c5054902d440300314a21a00c0010603140b06542c000e500094685175000020000c4026034451051071051100602c065100850400c044500940300c000c0756150b9001015110301c118007966004161403002e01d008995174000c2000e50300010b060001d4401707030b103801040071544400e100c100035070345420001c40c00340304040b29440701500002c0a5829070030 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 253195053 1250 253193803 253193807
    0x80a11090c0d0504050109020310020a11010504020a062105041a090105010308030105041d0f0102040f17120a0c02100906020709290312070606030c0602150612070b030108030706110703 81
    0x241c42d918203812640d0300005802c03c942540041c1019400030112203205400400c0c100c041e6001603403040c0090064502c240e200e010500032180a150300030182c00440c0e0403c4400c0b80c01c00000309016240c01704282e0381c40c00b0f0107036920400e402035014914440d02181c00d92011088030710090034008080c1c0c5000e0042010803c820203480c19548120350110b10910040786041076003942c00d01c000e95034040c100c07d4482501056000700f0444a00c45c85a018481d82c1d801503100c02c10565403100255004582c1d680b0014120100031300f0f826030503081c8010b0401c450b4001c28541e24240c1e120740042030410405102aa80403c0040014807040b44140004000400d08140d07c444100c0b01c40d84410340494500e05558040c00300400b00c540d10b00300e407030300d0b402c00c7d00f086409000c19100a03601c9400000000c10080e20104e04030741038043c146d1060000d512290300348035240c055500c0c1c24046000718a00890035007000303801180280941c0004584803022810a40200d441848514a80c12810000e00307000903 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 253196303 1250 253195053 253195057
    0xe0d09060e010e06041805010b0f0a050904270312020715051509040507030618030c02191e080c010c170f0d0612050f06240a030c080a11090c 62
    0x110685003040d1070240d0480141c40e0360070031152140d400900450003140b13000d82400c0100c0d0b00442590f0500869a03140c40351000c80c03103a81810312100343c3c108070b01020a40184010000d540c03020b00f00203240880000e264014090700486003860040c0100c2c10014581c0c0b1856060b00d0343c0409404514060045e1f440440c2d6020032030700304c8041c90f210310004000000b10305030098501d1010340050154a002e2804075180c40740c40c002115101c0c82c00280302d02c1300304001d6100180d20703419212119043c49903000c0101d15510505a80d2200590b9171010851420509141c0421500c0741c0d01d01d0001820100702034144840300c0442030410111008a202040703411810048444e5207a40060392811b002c042d0300300d40d2140c60030440e003041c104440012900000a10030018a0094060707070440c1407284001034840c0f40c15203001381800d6200128904e01a550002c0d4002101c00a0060f1a00c5660f981c400400e81c0c0140d0040c200f0343c11103801c2d0014041114001c0d000a071040351b0110b054904054120031034 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 253197553 1250 253196303 253196309
    0xb15040e0307031d03060106110609160302091305030f0c1b1008090109060c0e04140c0d020a0512070809060f0f131b09020301091d0c06070213050f0a0e0d09 69
    0xc0703c1105118161070284c06865400400502694036542c0c407990090080318160742225242d20480000034960718010031700710703e00d004030b0303070380180303061030741e000c20a402d04040c2c0150140c02e0143c80c20b400060b0100010440855006004d507140c6198559260419070320000c800003041c1d41607148000c0c1c2d5900010300030703c800d090520884a032140c4101300d0042401e10f0340141202d20b888000c151031500800e405142d00740848052216a0b01181c449201540c1540e44500c1c1141c14480502191525000382034152590300c2d0181c00c040e62080040e4100c0800d580ca4008138241d1030502c00340e44018808142c5c04007414011240b1421f040c0002640400001c00056510340d0b07a020f00301c10001d00d401140c08584035080d061200d25202c1d03003004002e40c028441c040d40c240c50b213520740704050b9010750f5020300201040702508802ca00b001c140071080e44458401ca82c44a04030030200d1500c642841524010310142446a2141c03400c3d18400c0116407811418080680c484200d401409600071f0084c4d0503 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 253198803 1250 253197553 253197557
    0x20f03030f0702120c06160309020112020309012405100c08040509151201050a05100b0706021e0a021c050c1c1112090f040c0507030810050405040b15040e030703 71
    0x705940c1d0403412030030084400030524010704c0018032100500720000310a03024070514462010165250791081d02100d1141500034081107040e02e502070318030229405107034400c55107400490044c4001c0441e04c5602c034241a005416402c0b0314081c0300500b841030189039002e40c1c60801040c070300400d450b00702a40c0507a104a074070841007000040d00b11003980c035a940c0541000b804200c0d20141d13101640d40a0700080b07548900c2d00d8503000004900d5010f0350b4801080341c4015400525250043d12800069403011107450324100d4074045412130451284000d00f14281282d0140c005200c800c06a0104032618070114010000c00f44404581c074031000c2080910001181d1001201c10310b0708105803881c0e405503c00b9011401601407031090301145000604400c113080342d80844440100c401c110444052085241c0041d41c103100c0800003178010480203810200802001919a5a0f500000c05541c0201c6040300e16880c04c006100b12086c1c0300b11501104d44d4111014002d4480040080c0d40c0d9008161020301 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 253200053 1250 253198803 253198831
    0x1060c0602070501060b07230613260a0c0519080d0e10021605060a090c050904030513060c0303050f0103020609131409030304020a0b04050d080d0f0903090f06020f0303 74
    0x41000c2540700717a00802842c06100e13194500f40c201a00c11341141c22060a502c03903000c2080c0c0798010007041003440b03030364000d14134840d08905d80c4072500240d907250001d40003040801c072401c072910701c0c81015000700da455a8940c41c0c85203941c54075500380a40e4016000710762001e5a00c00c000145000d00fa10b90000d80703403000043e1003080c0c510141c6003401245092030758920000300354040340c2c1150b4204040d00c2c05641164802c2e114440a42d080fa042075070042c00d120f441c40818003043c9840b092807500b143c081c0c503000d801e1003215030560751680015803115020407201d4401400b095018015254080c841401006456240d034021400b10b10902c0c000511580742894090305c25201c0d0b034019030b04011600418081842d094001d0341c1e803503000f918183c0c49000c14a10008002200d2021142070f80d1000c3c200001d9000d05503600c1c00d068224680701e40b011601d40324000a100503920403481d56030302940d1000744817441d181e46101e0304d03200742d04800e0454005903071400e0741440010807203400201d2003841407 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 253201303 1250 253200053 253200067
    0x50609010e180c0306010f05030603030d0b030f10150b0a2111070b0402040509030c0c13062304151d04050321070210050708240604090905070b0301060c0602 69
    0xa101d025180b80310002c20400b03a0a2007030b0003244902840c070925003a220084410300daa04141c84500007101c0e03995160f80100014411a00160042d006080000d011141c000784601c0da07081c01c1ca00354020318010b840e07031100c1c068003a60050042d04002c0035251862032515100c120018903070040c61703640810f550307080c600a03000c00000364001012069840e81c00f5840320315525050420701403c0e0f07400e921850808021824600300070007155100c281040040c02000703651804e001d0f80b41740041141310707000d50b10072001941c0c3c1c8040d402d0700c0700d15000850640c0790035003003800c000031180006100000d2849100d02400423031303080076140074822161402816156038a1070154914828209090000030f61100b80360044880304581c203005015170740a80350048582143c0746c0451b00308440c1e00c0b0026103000045030b08000c14113a0441c9982200310500d180107070020103e09990300c1503122005055440f042101809000c4c01100060443d4002c25803855251038802420708410600c0604455070000d001e03 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 253202553 1250 253201303 253201309
    0x30203061f1a0304051509100513021201090c06140a0c02130c090609090504110105211305120a140a03090c0e0a0c02010e0d052203050307170301050609010e 69
    0xa1001002c82d4107000d8034202001c0d8200c00c00d0f0f0400d69040b6407500c40c0110310720102d65607041c81e5100d054802d0040c0310121580315018041c1c14050042240e00012180d10b001503251369a030700c2c0090703100f48000324a40030540345c0581e004880790b0002041041101481481a0401c4125001c035110362a01072425046800059418003540b080014014681a81229402e40122070f0800703c81403522140d03da00e54880c0b402d400c0d02e4080381c0042c903240c8030071021211503004074003508182090b888801030014250381e604004c804181c840300c601181101c1c0301d604120042100000d4220200c825030704100c45aa00a4441d0120203001c0366948008940707004010b2195004a055603000b41c03490006982d0f0300c04152042d0b100340c9042d0801810071000340794080c0140160800c45140301c0051410031304280c2c1c11a4903801c0403044418101c40d01e000d00012101202c015005507000d4006951b898241d0701e0300682d1140f40102001c0500310a10040110396030b524241c1d900b100f03003800c040310811086400 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 253203803 1250 253202553 253202611
    0x903020c0f0117040c05090112050d050f0904050109020d0b1806060a12050109090311030918090309063712020f120702150901090c0302042703050706060f03020306 72
    0x102c0506681c4990802085c00854040c500817100e007940e00380705690f2640c403030402c80801c851019000707501415080304034510030b10091280014101e445030a10308040e00160031350700b0130b901c5601c1150700031070314810910f854480c3c005150021541940c2140f0611050481d070980105003d100c1d00c4003007043c054403400b0701c81d01000c410854904010641e16821400c1c010a0b045c0c80642c00145111112210711800208aa0341031030002d001182c10b141c103e80c0c032f0381d441e8002811408680810305c0260016110309001c4c1030300c41003480180d40320407050414032a220207007490554a0020300902060a1601b203003501ca5030010441d00076a80e030007030039070004491103006070780450040e80d00104200c650780030585c3c80f0000e42c100000c0d90191500c82000e400d075044d5105c09801c00e440c2810400040c0b03450b0b44070f80f404030b54a80d00b07041003841007007001d0500b4115483c1500880c2e00011414100040ca11401c4080c0c8200310f40d5002060550f004250354003001002c6103e410b841464919411140e860 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 253205053 1250 253203803 253203827
    0x703030c180e0a052d0f0106141207050c16090b040b150c03090a08100c0203131701060306020f030a0f060e071d03190b0907120f08120103060516030903020c0f01 71
    0xf0000c5d808609089442c5910340049828028820440b00041505440380c0744404c4008407280100e070400700c0d800d40618001c0130141000b010300c58200f060340391840c01404007071030108880d6548041e5a00d0000c04000380c8001c000307024416860000d2110066441009105610024411241c0c580d40d02081c102c0c40c1d40324942c0305a0b44400240e10000e900b110024000c0101c18244070240410480104180d95038003e035032000005109a040034090013203149800940d000080b000071845950383c0d00d408003280d00c210030407400910000104440003100303008070035603004840c0003041940c1c605078a20115401c05400041002452850b00040654004003a00c80d1000181900d10101c1403011103080051100c00441748d56061500291241e04003103054422070b0a0b801c50b141100200b0383c0d41c080003441107141115007110a000044004008202090185114440c0003883d41000044c01c040c0d6000503680300109424000c0e070200181d8089180c880550041e12001d00604640006860445800e5 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 253206303 1250 253205053 253205101
    0x1f0b030a060b0301120201021e0c100507080406050712080f0f0612010c080a0c090807051002030f03010801140f240301140a020a0e01050705031903060302060703030c180e0a05 77
    0x103c00490907500394a680c802e218801d808075181e07042c0e44401d8607070301c01940300020403a8022000b001c4941c28450780c1c89001c1d02051074081c1c98041c0c1680d4a9416030007640120001070004641c0800700800c280c00095909620b05100c80d80303140807000805401802492401860005800720342203131911b8014503145200c0c04024440100b8040008040d214201d0301c0002041c10011030309105805600e00340199003e09018200c007d0402060004000c6403a1640c021440308008000b003601005003c0c41c0a131140d0400030684d500240d0307034800c1d40c80026000f85820040c00003407180c00503a07074240070351904c041c00f201e040810009e0000303401000140c0c9100d50703142040d0b00700000d043c0640d000300303d001c4003a02d8101d00c030072000c401100e060040100090031076004100044850b02c000f9102c04180c9041d14000c9401ca41780d60120748942c00135032003100800d89074410b1000c0582c200440c08060200031142a1b910307490900140403500000d045d89030303410707a01e2002c110b680d4202e00c4850b070300130320301 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 253207553 1250 253206303 253206307
    0xa0302031507030609090201020c040b0a0509040b0403030c09150c380f070c0308090c1c05210406080a0b04021612020307080a030c020a0c06090801051f0b030a060b 72
    0x107480021040041100c12000007454440082041070b014422a04aa501a401803a501400e8002c1c4801000c2c0c02a000f940500900c02c0003c030784d43d03000d02c807a12561203581c2030300190a080c40c025081d505c0c3e600e028424041c0e00b49090207143d2003107015810403c80380c98008482e80ca40e081080c200c1501403102510505541c1002d002002c01d1007048001c19450315041015030303110a07250b0b03840c403426102e5000150f01c202040d00801d00c526920b81e08034455070251820f188424000031211040c1d54240713100041044201c60510405115442050140c500b200202d00d4002c1c0200b24207100fa0b02542080c060a40007080400d560b9034441c2c103c000e00900308550b10108402c10340242c4031000800c0307078a100e015107900e04072840031003600c410580c0070301c41380d0400714112410340140068541d45030440c816081e1200109007143d49420040040c7d484000415040c1101d5500b920b40081440c44607070b008a001100765405002003900b180c403c0c05805803692202c4103008041c1815030f00c118014540 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 253208803 1250 253207553 253207573
    0x1a0a031b0c0314030f0105090c0903030a0809010507020106030506160504080307110a060c0308040f0807050d030501080c0f090411031908130e040c0308180603102c0705090a030203 79
    0x841d00007541c660003600c3c0e41c08225a03040a40a480c4011903020b048441448010070a504003840503e0b044000042d000c3c2c01c06240d070000c02c4c61038100c00412400651081e090000036042889007542243d03140c0b000380700460950715420381c1c030180506050501332040e81c0d039182140c4540152400341501c1130950303550f07101c0c1c0d041001008500d0040c0328883c0e500c0309800a81d1500583d004800598180c0b00e409095541e511840003407141d011058401c01c5040007004002170342480740a00082c1c09840008413541840c0d4102d1510f084154914003580c581c03418402c40e50740c0c8240b4194419404154030344060704c444080ba0030841c0b82428002944811180401080500c0e4043e20070300f00011100640295200c241140417001517602501440d1052024404102200700601700a02c406840006100f440b6011076480c0d03100715480456500510020700c1003000300e020560713003540d6080c4c181641085070a0319440d0303c40c001e40b145e000d0050018000703050b03440701c1c18a8801103800405a41c00c0a003 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 253210053 1250 253208803 253208807
    0x305030c0d060e18070608060d020a050607031106060102010e0c040c02160f060e090127021b030c0d050a12090309030f030f12060803040b090f1512060108011a0a031b 73
    0xa401c0c1c80e10581900c3c001c0c0081241305000400504440a039950b0865907141c0d0700c00d0248890a002050384c02c0070740d0f0301002c0313195190403004051161080e5500a500d04020265906101c400340243e8110390410600400c21fa20018008800c5d82c0c0480e000600c451000c1c03030503032508801c52000619503140c135100007682034a071040e880498949403a5181c4854200082081070a002d01840b0078040707280103240894084103420344402c0c1c511000041c5000c50148042c1082c480d01e40400400e5031000609518078801804183c00b052310900700b090800c0c1001f040070342011300b50f0341540007480d96441c007181814810812040115004907100c000c0740b01d41d0400a1042c05801e100101003011041c040e0006140c0e803080c1400c4401c0c175009035003020700780002c0030120b600610201e9840100407008031215a5000b007001c400801001a0a548120005410301107a0009001d94140309502c401000504c030104010403602450003006562490381303e40c00c6e40200075903151110f036013020100d1149055 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 253211303 1250 253210053 253210079
    0x30e030c0304090216060914070918080a020c130b01021b0906091b0a03020c0c010905060a11010b0303040801050f011418131407050109091a010c170d0501051215040305030c0d06 78
    0x100803101a276100303a4903203042000b5925402408038035402c5072050040407406201c040c25078071903644141c84c0900300510029a50381180d020384c90003d03540790303105000796030100131809a0907034231800b00c1800038840c00048c08401008040c64010036100001551401c1c150010603c200c40c50491283c0341e841c40c030b0b401002500715000400c0d8074401d05000401c80e6015021400880f24028103081c988055444100c40e0080649500005992140303c01045503906001500203000007800008892034131b016800d001040c1030707000c41105161f0418a0607071342c80d210f40315a00006410442982d0761907503c07060016402d032802c0642480d05110148003402008a0310004458003683c43c6266076403204602c808a0300450a1102402003008030781000754040c0103a00c500c2400f0710082c00080283c2480c5410b41d62000c0c0c01d043c2d01695510041c0014600180f11b003514090300c3c0001c06101400340d00d041c40b4910301502c01b5050010100018170191a44402c640800c0c1294406000c0d4580d84c0030b01d11005 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 253212553 1250 253211303 253211333
    0xc03080d050604050411040b01030b1503220302030a0c1a150a0503010e0309041a19150507050309010e060d0204082109030714041d030901030e030c03040902160609 72
    0x2450070700001c140945050b000f0709000f550882c81c5071100800000c1004000d0400c42e03c450305061b2a1060b40710150b841d10711428221103008100b07903891410304241200c020031618000e850340c003640e034040702081d4000151504281345003440f5090403060308288925840f10000b07200b40060900030064000110030056008540030f58842e1040b03038031002050f00f84c0d0240601010300d5402070250808900e0207405c042c0399071252024144180e105000440d008821200d92018540700114007003202032181d0620001c5440c0034035203e030801020780ea4280e1644248103410381006110300c58255141e0302c450854030100c9005c1c604554850b41c80103605d445d600b16030041062420040c1d400442211040c7c100c4001c000000c0c090700310b580c10300110344048000b10280d00d400960b110b180e07081c615503601d0b9424031400424015516120040d00043c02d4070000211071030250403d21110000540000a80b825a01c00e98400741e11040b020311981c8041c0071001c409001d06040c04040418003103812420040 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 253213803 1250 253212553 253212577
    0x6051201140702062a040527090706081f0b0c07030611070203060103032601030309080c0301150b0c010f0515240703030b12060103140d0201051b090a030c0308 70
    0x40e68420b030b000e80e12280708580295285482100081125540c040c0785074280e48901e01c941d09207030302c802c0410310001d000000c2c8591070000e03102d030704900001d01880e542d2080c016001400e5003800c00134020f0564602500403815078001c44070715048500c408045101a00c40d102c5490740320603807002c00d035503039164500c0103807080c40c030b80181540171004070400c6840268019004080c00d91951398101c50034055516950505801a1384100c000c5030a120b246000f10b000ea904d003c4941d007040c100038100200081e046200c2d0303242110f02044d103040300c0005000c0340d11401c20346842c2c2074000c80c114090650714021507480d901e0722042044450803441700500c0712006440340c80540324039824040d4803080300d440006031b8003c248900700000b8480e800824650b034003d0100d00d01841c1c8294502c3c0782040a070411030f1145001d40c84e40340c864400700885080f5940b00d100a01c143e05201c0b4055529040310046003404100003e010b40039612105c264100950748411652540d0f42da84c206000c0c10b403c03910040d40 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 253215053 1250 253213803 253213841
    0xd1101110a03081905130803130f08090406080624120307060f060501050c07090906022206030506030115030210031401060c1a06010806040504020f040207050c0405010e010e1906051201 81
    0x1600003161013118882c06c1000d031148450074150b155941d55400040174034049500d070110000004241440600354280f08100654a40c0d0b5143c041200303540d06a04a004039030b01200030842c090704c81c185202e541003569880c030060115a09d010880c12021a24202c032507100004c0c10740100482c0d44e00c040d0001085003420004591a400119a035115401341142681e00600060201d58241c3c1c3c0040c0c0440d1003148010300d8054007403100d10245102c050b1042840e803070080c1c10000a03815004941e403020017103008011406000041e545500c1090001901840307540458050146c000e6201d80c4849112060741d580940c0d482c4030080000c401503204680c4041008040440c890032200d02d0303402140140c40c0c40849036580d10500c401000001c1c4260f0b40003000bc0c18060039922a8801041200d00480150080307020100030b000a03034030113034084003a0040c0d85004112280c5840c50454002c81c0c113440c200c1000d8003040740000a001d0a81041c1d601412201c100510f41805611540e108424500121 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 253216303 1250 253215053 253215091
    0x20a0909140c18010909060b090901140d0602070204020903010504050d170f2d070e0103060e070203121023040e120a120e0d08041703060d1101110a0308 67
    0x4607844416290301c2e48209042c0801d21010310500b409110b402010b250840603555150081e8044e02c615512111195400041300f1956041c001703405400b41051503030910203081240d0101e59140720641001d441d07150b0124041c2c045550f40d404850f02d0900082c000c0c0540d0400d82480b9846002c0000e5840220b410b103001c00300d50464814450b4851040103100440360307582c10640040810865505c40c081c01c01d054a840c400302880803c1034001c00c160750f9007107000d2490000141c00c446450b00141044034400c400c01540350340c00000c031800740070610000a05515680c988808000c0a0703001820703c20026140074141810394803604e80c0e040e104840034411207101140094981c0422001802d41e01c82c03c0052000b80c9000d5005070b1114180c1c00000181008441039544c20320000f40f22440005603c03005020a0240c480803035840c4410f016030440c83c5050000015145022803140100050302000044da441d80c0200e105183c0d000e13101c000d0352140ca49600e401059104100c40300902000c6044140d = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 253217553 1250 253216303 253216331
    0x130608060901090308070804030e0301060803040f050d0f031b17090f040506010228140109110613061b1208040201080a0b1c0c050d0507050307050621040302030d020a0909 75
    0x3c1080d00d0f8064840d0380140e02c85d80011039041c14028029070510050100851305c1d41c5003445031000a01c2580b01542c0c489080c2050092800001e9101c24464049001200301107000d449424020300d80c1402c04100c1e4000c228441d00321041c240c84040c0a146401490404564a00f4000c2030b0b101021601c0115060f02441007108841050b81c4140c0141d020080708001d86201280c8208018078803140804200b1155880d040c1000e02444004400d94407aa0b0010811100c0c00303400e840d05d9011604607003442040080580c0111184c8250b404208250340680003404220401c81d5143c2d4100715030340482c00300010046c028060588040b80000d40b80400a41c40d0f802d50b01c500010684010f001c0c80e031031035070040340440b8040e001070b0036205003042d80b100044540c3e07124086035050744100c025048480c5000c08150600c1c0d55680716a0250404100c07000d1065a0341080e0344682840c500b10800c0c03511242012450f50080a075007900781440045e4000845400110090468814000074404c89100e0700903 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 253218803 1250 253217553 253217561
    0x70302101a03070635060409170d060e010905190207170403030f081b0417010209120f010e012d062309100303020a0807030e0a060c050c01020a0510020901020c130608060901 76
    0x91159001d02c1071021800c0e40c641504540aa1030140d81c81071001d09c403d00d02e6110560000000d0320b243e40e5039072020050810310004071030051400d07042c1000326182408400003800e141d070400b01d41c00340d030000340d81e0b081007140042d02c80004140d81c0c2007500d41380c46e45000b4003810040d6002101003540440001c032200d0306c0c3c140300c50360403120750200c908151500510109503042c0c102d10004c1c554080c4900416a00c1c3c401d81401105000d070000d2410b80580e049aa0840380c1125000322203034101004c4455001c017441e5503401c407403210707005908003801c03203c0414024141500410b00c01204d4000c2020b9084182c1050100390004079070a051039181c0400c10000002d07103110050140c0c1010001201290201d00a410454000d040c11840240c10345c00065280c0080d4002d0000b203040c1c0c1808005100d400c00100030031301c1003030006001d4541240c4440d0307669a415110002e0480d00019604a01c0e4400d201081a010000e44401e10488032020360030701411035809100500d21545000580403141401 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 253220053 1250 253218803 253218887
    0x30c010606080a151505130e040302060717040302150a090b0f07020709050402030a0209060a0b040305010f06062609010605030a081801050708070f0807050303040b100b070302101a030706 82
    0x900000d05ca012080543d0f0642240c0c41018500c0f881103000600c2c41030b100d10701031048e0300c0b0f980540080c0c41c0100d0040c00c1c0d80c03441500c0705440e40c3e092003008006500010f02403981c0004030003002150f60b81c0303c1444081c1501c42c40040c180c060307070003e000711441d0042c0c43c0d5028444640030b072480f02e1703103540c50581264422280a541540a1b400700300150034a04511a0003000103015410607541796075248040ba44a0303030080f101a99112a01d040c900001d20030000a0180b601d4042140c044148851f405503580d080c0d40421340700c103040030a050300303001d501050040c9009015512000311034200010250880a510b900c5407007800b114400c42e601c50f404071241280e010f01598209000ca85500c40e003040c104204030b1700c0d071030104090740c04520308001440c4150f110b945080c03510701c0c058404840103a00d9901c518070300714040c80329100003500440c070800210440c41d00000d0241c42e141000e00380440c0e0003281c54060207a0b00d004030369203520500880d000c115441c4106000c81e00080d034610088d003409 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 253221303 1250 253220053 253220069
    0x1051b071a0604020c070303020d2c0f010e12060109050a020a02120906070b15121f0515060403080c01050105061306050c1203150108061f0c0302030c010606080a15 72
    0x38101156106001d0a0030790060303009000142481c1c130341c15205180c4a550780064000d40c1c460450846d2850340100310007044c62584203503c280d03044006100007141c524026551040d001800c8a840b50f91188070f07000e400341401010700701c812031000307075a50311000d013806200e11490500c000100d602e079a500071075041e100d265000740403141c021040710340c55400440d10329501460402c9200f01060310b4400300c0380519204800480721203100c2003040703180054411055100d8110200344180310444501d002d00e80702d64800003140e60754545800d10740c3c100079071207601c2e80308102081c08018050007401400e03120321001c0c02048181d03203a104000321400b0b8403000003144c100749082400f0361485440070340001c401e0b00080315214007190103518403580044400844c221500a200e502560b40704c50741640080f0203071082c0752546e03007401555a070044480740903020b20001c584507008261080044401eaa01c8040003044016160791008051103c1600c0401520303080c5140600985400c41c1c800d021283c1c10 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 253222553 1250 253221303 253221323
    0x708040615151715060a0513090203071209050607181502030702010807021914010b040507030b040c090b041203091508010f060206100e060d081602040c18030b040206190201051b07 79
    0xf044c100b02c4d180e0700000350001005420f110900c0e0018000e034104c00580031905001d84c8034501030300004c1205070340820900045003807010000100d10041801178010b8041d241c01444d03480025859018400c203a80300000c0f407242034040902c1c3c65800f00150a03550f100740c0e07803040141c460a008a80d1280c030010288050074111034030400148012074440014000b0400210303001c5000e0000600303c03027048426602103070703da1121041c186000c0c810400c08000c542095003501c0e0420101c1d0010b070040e40624040003120004190902d4022140764005141544954401071035080340140800c10a21a00620088524002c02c1c054004900c10b449101ca00c41091201461b16840e80c644030b10237003900f60007400840f00080450500002040c0e00c142d091f440e50540d06003403050000715107141060030100325450103a401d4040713034042a0812241c01c44940700c540c2d00c860001070340b1880b64281502c141020424560380c0f0716010740000d0300c5040440355044134140440c3d100c601d41d2140c000010100648 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 253223803 1250 253222553 253222591
    0x12100f080607080f040c080109050708010c050c030306040c1710090f02040e0f04140a0303021305010207060c060506010509090f091c051e1210080610050907080406151517 75
    0x84d08642c86401004031034001070380c40c94200c1c01c44040d0310341914a84c0200f0010b1088803024014130742c0700c264501c0d00380d01d094281070340651130f404058110351003203480d85582e040403403003005a0803842c40303841401602c0c1d041843e9545c40c510100d1145800460600d002065202e0300741c030071383c1c0455946151400c03444e5200b102c01e01481c034005004980c45607600c060085082c800308640d400813482600c006070740300d40d0090b928007070b03915683c0901e045500840e018480303039038803101282c4850340c08100031a180d240c0e00d0060f289070107802d800c01d8000d1059001c2142a000c0951114011980d0b0000c0c0c502c10700120111103041d02c03110b0300f00ba01240c000c00090002d1660f80c40441c442c4102c0310b0200d070400440483c14900c08400366000441411420800d000500c020b100164000300300d14600c0101500d41804600d82d9500140301400307104840300044d0078041140c003c4c00c41c50b4504440d100c621611011a080402c007140d58020004e0b12000142c01e8210040c2c030000d000d81c144842c02c84480304 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 253225053 1250 253223803 253223821
    0x30207081903080a110d0207050615030703020111030c0111040303030f1521020301140f010618060305130f030306151b060203130c0806071b0b0c0a0512100f08060708 73
    0x202c06042900c132190740c1c2c0d104040c8496150040c1c4401080f902003d40d0714102400c049281c810040c0040d483c103200303804c02c24601da900142040c1282e0342800d1042e01d148020248900714052006404602d50030211030f4403049e01c0700c030f0042094038405d8504004041c01d4034662011aa6505141039403e4600700080c021041050949460141c44150521101800340c0c0800d003511546c0d00748044501d50035091000b1507141180c0c890161049241c450003801a012556001c0c0109202d072005069451000c14442c05410000b90813164010800141e05c00395468001c00030b02c0c451042390100005804206241b0340f049030328101030b6083e0f00000042d0a00fa03152340d0300943c005001c500b410b550304414030002941e458a1a0020802600034201c14a061203004d40003504546280700f103c490720596400091900035110b4010201d08a96500d84424090556140c03103240b80341010070380f185e8101f0030020300d040c44060035500c00f980c12200e410350759009030b82d480b02c0c240c2d0310b84046111040001d4940c0 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 253226303 1250 253225053 253225067
    0x17090c1c050718050f0705250b090f060a020a0507171b01020c010b060306240d0204090614180403031808030421020610120203160b07030207081903 65
    0x1492200d0404110003103aa11645004010b501103184014128001644181d10348240307544502281d0400f401880c3c81003000f041403203080a00244007a83c480b000d5642e1081180360082d0b03541c4424403e0150410003806c95481d082d0041c26019403040c44006141c80280307009a60114802d901e400d401c0000c1c5503914811069607d00404004c081070111551b2580503103410040e006012000507501d8404450301c5003991440c800f80c1d40500c2042081c4441034582e01c060780011240c03444810f911030003489a2140301c2c8a02a544184640003140c04202200580c0c0010308590980c41031301c290600f5a02800a9400c543c034980300c003c8000ea00003004a070080d00034556400824039048040341403991041c01c507400c00c0e035040c3c0d1100c0040c01901403100d9010704901441501d8002000b96281854448070404407034001c0b00c030507080920f440d608544042180c0181c6903450b0300303950100c1d601d900041c0501c0c1c0052005400510034950001183c1c00b002c01c07002074070b55811084c00ca4900d56601d06607002 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 253227553 1250 253226303 253226329
    0x30405040e03120c0a11070605090609030c12250302010c1e0807030e100e0906120f060a090b0106090807050906010e0901140f0405270f060c03010617090c 68
    0xd000c100b0041c40e02e0203403041640e105a08102d40f1580341c8805800c002c1c03011b209091055042d40c00307508140120358206003030710f0320b44e81c00716031681d80d42c00003001080c28007c60034411a049404c00d0b40000c422000400c001c00ca40800b0001c80340f0b0090a6000029541e2043c8006404034040441d640e010074240488a141c042240c40d40c0e417000350035560394007001e80c451503040d0002030012049400d1450886a11000d15000d0702d005950140341000141d007a24015180790f00c11084d40000b0b030101003080c41041d1b00d5103000c20585400707240290011001d0400560112400d280c860000b085250180c440c0c04281c50000d070081035003d09000a0200d141000750100d4103100c0d2461041101380d441804244c00303043d00d510100345407110340c0240b080459041295030311990402040004c104003070061a40721403006061000e002601d840014203100011240c2211405104104945040a040118101c072060342d581d080a1045007086c84a00d40241c44c103e40c96000f800d52200c10345480d08100c0e0348 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 253228803 1250 253227553 253227581
    0x507031806080a06050d051e07050a0803090909030703080f15030307030f02070801020702130203040f0804090e061003120c0302070f0e04060c02060403080c1614030c070609050303040504 82
    0x10500c121503025480c03054a0380a80e001440490400002e1800c0d40203100c0189025130b034140ea444016500c4c0d80e12001028440d55440301c7e0145032801c0d400c0704019803401800f0182206140a44408105031070b5070004260501a44c00c460210341c08480000450f4056501980c48440c00e4541200302c11520b5005040104609c50740041e24001c0e6400780024086948280c9030790f2101c0380f0584020b414040d0981c03042450782d2041c800d0380f004d42c451100403000030f1031901c1e00580ea540c451a000e241b8468511024001c00313004180414440700c10350203800c10000010840e48680d441c0001398202c9105800020151074003803408000240c06a480001481d101b07005903144240c4035aa844902d550551050104005032001d110a01c03d903881100c03189056031014010714605507d010f0003a6402811610120600040c4c440b8a8082c025510540725072100c20340c1905000701030410303580d400010004115005420001900f07900441c3d03240204c46001e4007550a00d0701c0c02d4104401040d0030060144 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 253230053 1250 253228803 253228817
    0xe0705030a020d1b0e0307050109080a15021e0409111e09040b04022a06070f1808010c050d0e0c13150305061305070e07020304170f060a1e0912050703 66
    0x83c030b0f13520880d040300c401c1456072a0107041c5641002c040c900400c41d0300c040e061200c561414001c1d02e401143c600b034420f400c40034140708486182130580c024401e1060703825601001c148840250694000103208865298009002c0710543d104d80a015219a8090083c55008156415a0661248040d14100c0c00003000010040c5061010405130b910400300d4020f41d42402804200d045050300d401081d0400440082100b40380802008c0d0800c8002c5000704107100074010003031b4200701051001300c05001060300902c1003c000c08806005a00100d100208090419140d900c0e001000140307289400802080d600407c6181d90071980109140f000e8400110440360010020644c00c1010318003074540c0b0701c0c009050242a0506e1400c240c03840d0000f4082d030403114288203100f80e000003a502176071011009074040c2c1045400c0b4500d002c2ea00010603009000d80e104010b10300350f196100d81818803000d2041901e0108085c028401c0780c00000005103070521b1000b82400e92031140e0080c0c8001407181c01e10740 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 253231303 1250 253230053 253230071
    0x50a0209040504050c0418020a030627030e011209030206061c1b03020907090e15012006061203071a09010b090906192a0302040906080703020a0e0705030a020d 70
    0x1001d0302d00c00c88050f1000e6004c2060844141410b101d4005c0040c0c15244591900708a03074005007181a0718070014140e280c48609421001140746440c100003000060f002c0084010751074041c050008540040340802d102181c581080f807024011030b021a5030583c0981020781d109000c104112030f1038410480c0c0e0800008405000a200b1a2910718440e9094002d03020a03195104020b099480113041008015564400300702480d4061565a0000001019541c01c0da540da4012202d07158614102d039480e036102c00205001072801321b019400380034180c616401c400b0b03041c0da0140c0e4034403500c02f008000d1005a160f1a002d030200141075500a45040c0000c94101c0c0540000340c461703031003990103604ea82c10039810720959203020541c0d4000840c0e908414040c0c44081552511b1110b456181144100541080c41e140369200340c0c1101d000d003918400400c5556218881c0c10356804050100b280a50404034011903005c102184491241d03e0b550307901480d6507100320840020b5000542c0688410703444021003 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 253232553 1250 253231303 253231309
    0x32701060f06170105040209090c09062802070501050408030a0302030405100203010e31061a0a080a050f011122212303090409020f090c0c12040612050a0209 69
    0x1000003840b03140d403040c1d26041089910010800306a000360700c5184100102e6600c0d41315812a95405401100820b07110110980800e072544200b80140144080401603100c50720084000802d04400760b034210b5040a841c0e03801504c2a10030380c026a00960b00078852201003070b01c280c00456010384140152101d41e030380300e222203040c2d030070070780200000c08011820002d08526080210703046040129903903445010030b040300380d41d0600008010b821a0344810b41550003503070b1079815500c0c05d48064100090f0396550b080050b1500f1440030200d680d4080d24904007070340031050041401c102e4100710141d161041d10304050740300c00504800703403a08444410b0005a00c44000000c1c02003c1d080034070317242000845240040119202101a061480921041c500203100c00400e580103100709440000b820140c038000603940c0100d5901c86580304001004202005e850b110280c014250761504440e2100000084104513000b107005070400a0340903c0220b02c10006a04804d40040034407400504c0c1540780408 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 253233803 1250 253232553 253232579
    0x10120203090c030d091a0a17041101020c06071e03020a1403040f05010f0e01050903070b03160e010f050304061d01050a0b0102070f050a15021504050a030201050c03270106 75
    0xc0d102442e00004200c030302a0905102c0300440750f40750301d000c3c184941040c0501d60303514402c1050401c07550300822014040c84c01840141050b17810b00d0340d280030515252a0011305086420382090043c0110907140d0454105403003030703d86666005841411008040030050380c0c2c00d00034041a0110301c03c0494140104410308101d103a0741444801031aa11400c040703640850840369403045042008400c0c91613402544001d80322029031003441d2003599440380000003450803202d03030020040b002001062100d805411003484214000a0b02c1790314250799800019a01d201c035030942000401c00402c002400662140d100400c0103004650305407541c0445120b5a08452040302d00c2c0c040c203983c0b03c010303911070b60b0100003680090024842600d4940d0410012070540c0c0a2441120030400040146296040c000c5c050881e10f55424027600c1ea051a03d41081555664101405e40240d482c03c004581140480c0045a03c03404501e040d05100744007035803045400e40844080052955600c506c04204070584c803c07 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 253235053 1250 253233803 253233811
    0x20a0603090302060708071b08090a0b040f0504060302100813060608240118180b04030507060b0604140d05160602071e050f06160f1202150c040510120203 68
    0xc0c0c002601038040c54081e18200000d8489000c2c080c4e540104484640c1c0806c50404a41d4032240c6400007454070700e030a400350b019607035240d5401400454081144c0e082c0314003a02c100c1b0051525059040c0d55501484200e400502010707400044180740b03103004500400c00c054010342c0105550b0711510087c2c907045d0446600760000c0c400c1e42c0042840e034032818860b0903100e030440b1840c0701452031540b5040c40c03441c4403803440d1800004161110058a031550402c0860517560340c100e00c0c1740c1201c0ca071903d0300401c99440044e084642d07038074010000801d81406c0c026281554803030038402102181550030081c2510340c0c1801180d1030b00c42c2d91440740c01c0144010b02400100080e400401e1070a0401ca40311007010700d080004403000f130000380200003d030788982000da50700300b05a41c0943d944a000c0d0a512041d280300b840601081c20006a0000700170744490540103501c20b5900b503e6004070420301030b030720204055580d00701e094000d00061101d0f180c00000021580135606262104040004090703040c1e0708111 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 253236303 1250 253235053 253235057
    0x516080f040603050601020f1e030f0301260307170702040b03010c03150905060604050904080c241f140409060e10060815070f0504030f0f020f0a0e01050d02010c020a06 74
    0x20908001e86a0140503132500300c21300340041d00460b118800702a584034075001103902503010860011040305c0b030130701c2260756107401e118503941d070ba41c0c445c030030000080b6100500720212904031151135004400407082d290300540c00b90028500c0080440d1451054108403016680300399943e0b06015196024450300b103e0307400e55240410581048941d4001400071a03106009003424542009410f603110800c41d81134640c122070102903900d550900d0f044501414490304254861340e14a4513119040d0b81b1355001200040450108940c1c510760000c1030482800301d00c440c0c1394004541884448020103c0c4502c20744090400074000072161141015210b02212158058025000c0600c04040760b008410103051030100401c1107521340c0191082d400c0f4014449400c0095001c85606d001d4407410880d0029030b041101403145070441e080c840c60851420310102c0c45580c108010107002c1c2055941081114015151807415a1074481440003045103d00100e040024a003144001a9a4690140040c140d1a = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 253237410 1107 253236303 253236307
    0x806060f040f030c0306061703030610031b050319060e0a090f0213020310050915010513240306120b180f30070c0302010516080f 57
    0x2150071042c40b119648600000340440c400640c41624001c0303c04003d0581d864142002c800142121844035403c2840003800e103281c0340c6401c2c0516541e0b0b00f000300b030400752100c08200d444032400b4003401003800401401802d0a41d06034148840256a60801c0b9031414101d03418030401c00203050705036641d1074202c8003040000300f102100000394007920806505c0d8200190a000e900221980451804102d10000d16407a2414540e40681e417032003101420882580d0044800d50b111420055460100810010b2681c82929001500c6004a02d4910b16000b140c03030002c041d50f48036400120310849500082022a10303618800f0380004d500004215422000490141004130308032011351107001c2d040000314545400118181d42048040310042d05690031010000d00d401801c4018180382d02195040c001075000e440208035000018441d10f141814540d0782101a0f80b240240d410b100e000 = true := by decide +kernel

theorem cover : BRFrame.Cov 253057553 253237410 := by
  have h0 := BRFrame.cov_init 253057553
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253057553 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253057553 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253057553 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253057553 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253057553 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253057553 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253057553 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253057553 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253057553 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253057553 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253057553 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253057553 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253057553 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253057553 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253057553 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253057553 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253057553 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253057553 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253057553 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253057553 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253057553 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253057553 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253057553 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253057553 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253057553 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253057553 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253057553 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253057553 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253057553 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253057553 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253057553 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253057553 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253057553 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253057553 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253057553 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253057553 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253057553 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253057553 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253057553 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253057553 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253057553 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253057553 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253057553 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253057553 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253057553 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253057553 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253057553 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253057553 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253057553 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253057553 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253057553 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253057553 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253057553 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253057553 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253057553 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253057553 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253057553 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253057553 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253057553 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253057553 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253057553 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253057553 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253057553 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253057553 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253057553 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253057553 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253057553 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253057553 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253057553 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253057553 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253057553 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253057553 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253057553 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253057553 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253057553 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253057553 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253057553 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253057553 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253057553 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253057553 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253057553 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253057553 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253057553 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253057553 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253057553 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253057553 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253057553 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253057553 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253057553 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253057553 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253057553 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253057553 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253057553 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253057553 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253057553 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253057553 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253057553 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253057553 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253057553 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253057553 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253057553 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253057553 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253057553 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253057553 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253057553 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253057553 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253057553 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253057553 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253057553 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253057553 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253057553 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253057553 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253057553 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253057553 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253057553 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253057553 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253057553 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253057553 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253057553 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253057553 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253057553 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253057553 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253057553 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253057553 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253057553 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253057553 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253057553 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253057553 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253057553 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253057553 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253057553 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253057553 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253057553 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253057553 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253057553 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253057553 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253057553 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253057553 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253057553 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253057553 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253057553 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253057553 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253057553 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253057553 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 253057553 ≤ n) (h2 : n < 253237410) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
