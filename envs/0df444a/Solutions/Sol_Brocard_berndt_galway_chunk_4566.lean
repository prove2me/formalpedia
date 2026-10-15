-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4566
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T13:02:08.164716+00:00
-- url     : https://prove2.me/submissions/5b23eb41-e15a-49c1-a3fb-d0d559154f09

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 821043165 ≤ n < 821223021 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 821044415 1250 821043165 821043173
    0x207170a0615050312040302041a1509040b0a120309080303060f060c010b090c0c0f03160204181704050f15041a070b010608150307030b07050c0a140d02100e0d1407 72
    0x1e02c48003203141c007280001b03014030451500d88161840c08aa4040ca5125016108007141c2c0c500355100c801c81d00444086092012940d40d608003035100c03d801741806007080c0e5201030903250004880d80031000702e0b10b10140419034140c004142ca20a0300000c14000b11038100c1d80070b0183c10345c800c0d40282c0080d502c651040303a00c1d4980b071f610540903107015504a6034800c0c2048815003030165016841039503400c20040d60901c0713402d695400074800d40440e00052400d010314008401c0d8201a80d00034040e0000c40300d081808074004c009002121f5003139445e40c0484400340100a58140c980d01610700080e01031005104d180761400c0000b212028040c10365240454913180c590411400368010070015680008100c942c401d841e80302a1103000680c0100796460070741d44ca44010000040c90700080081c0400c003007800c45000c0141c2003409403c141040070039400c0444603512000805440c0c0003610030170811441898442c420488500b00c3e1001610030303c403009208a405802c00c0340075507424070050041c00045 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 821045665 1250 821044415 821044423
    0x304120507050108010605040e0a1e090b0a0b01020703151805070f1409130303110d1505030c0a140d02040e010c0c26030a020a05070c080d0207170a06150503 69
    0x480d0281004018481c900000100390b82d105803c060b04001003444108840880840b905030409540c1e64082000c615025444503212010710001102c141419010414810305101150080038100810300070b000c3c45800590b900c8000d8400100014114080c0c0c5400ea50141d000d010381c40d026203205580c1134416103841d032414850f50880055034540074020401d010740342401d100e041c402a66058414036110205001e0f1b00c56290380a010306403100d40307036030450040b28211684456a29000c0022500b08103140d503292941c0c1c02000d0282c4520740006c80540b918406400032034404842100c0c011748c041d4180800c140c04042d0032601306031501d80c1c4004046081c01484070a5103540c2d9001214907142c24440e102c40d0210007040d650355480111803207595015002c89610007403229000d0707900e0900030011902e0b84500c6101415182420002140340f0f40b0206001c0c1c42112503074222200729840740a031000c07410704005901400c1e4896080032000520301e810041100c0c15400d01800c0c80d5a807070001c6818 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 821046915 1250 821045665 821045699
    0xa0b100e04050f060a06060e10050d0614030d020a3507030e101d040207020d06111b03090a12020d0507060c0201170705072301020d05061f0e010c050304 67
    0x29402001c0f00c1c06003510100700c4154800700240040c0312244c58102c003d040c50075010702031401107007105403ca020a000d1030844449480d52442004040d40d518600311015030400310f003510070f009000c03d2141c0d06100281034044030760451081c140121003a030045030780000d0f040101050703c0780c43c0d07a01141e182c450005880ca480c02500c0d2000d0700206c5004000c0f0382010540c0c00e105100c10481c960081409400c068091150241c40040e0b68201f1800040d4600401c07001c002c2c0340740d042c840d65061301e806030809000200c0100c0d03150a200382031301300031503200e000e80c0d0324240c0c000500304010004e1000301c68031048042d0000e0303d5010841c15035202c69007844600c0e04101e011601003031150045507406812040070096850036984e0700d00307120000404902c100a40948a088051503a0f29041c0340c202c41151341c150400002c5558031841e40800000d40011100c1d0b07442900c1c0200701c00720f0b0f000c45100c040303982d9215994001c140802070700196500300c1c5211082d5002e2006003c0410301075442003007924 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 821048165 1250 821046915 821046923
    0xc1508040b071e1209060606050901080c04050f0f04140106021b010203250311060f150915060a0203042606100f030f0213050f04140d020a0b100e04 65
    0xa5803626007400a80c44201030038040070041415a440008026a886111580e41e00c0c5428183e46a0240c4480b02034803598401500c490b01d040c41c0014110b40050051010030400e80340c16460755110341c0c81c544070340100c0c820700b0f400074440340010780c0c4c03480c00b025044080000204005128259100215200e5209800240150f03025491a9000d42008045a8600c0401344000e6103000c07081c1007010340d9921103404062422101c0310160003018001c40c49030485003001805c40380e05183c16100725400301c070309403520651620080c500300c0d644e00300100703403c1c030070300c50114030b0307107240742e0180a0210980c404500030b82103002c2808041018207429029000c500d0640600c0d03581d01d40c07a020b109003000400b81c001d10416410640402c0006110f0301c6100c03c417a000300c8401d91030754003400030a1240c0111946140000e18000401003140880001d6500850040e120794880b100c1d112203450355140c0c1c540c51000507a109001240c0026440825544d00a04002e21100f001c0d54911203180076400030340d0211 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 821049415 1250 821048165 821048177
    0xa080d0507120e010b03010614011b03020a0f0c180b0105030f07140d050429130516080f0c01021b13020403050a0305030910060e040b15030609070608010b040614070c15 74
    0x101086c5000d010b0319000c1e00014100d404844800790000c0c002c003110400003034a4180541580d02414000d2101c108410342101802c042840d6524040404030414000d91041d90741c00b50401e482c041a500c21031000507410784500d45140c50300316070300140d1070b4010448420821250403400071068603001800d290342501d6008100c60819140943c60801800c402011241803c032482c60302c0240321035007503000030046851924441050402c1410031600c00c581040350220396000162030b61300000d0f100b01d02c1e041c05041e201424000d40049844c0d02044400c020318500e5030300c10b07441600d4401c10080c486554004018905642ca5441d80d007800040300081d07020800200810078103e100b0300c070310030544d55003040411440b4104042010121030140c0060440c6901c40c0020710308080c0352030001403c62004040300d02d50310b490300880340d80756414000c007030000ea8440000660300110f2020381d4183ca2454440710015a011084030446800050b030960700da5070044400201c9681c2013240a803540b595035118 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 821050665 1250 821049415 821049431
    0x131e030c0f05090a1a01120212151009030b060f010201020c070603320106080603010914070812120406020a140a030f050f04050d050d06030803090307030f020a080d0507120e01 77
    0x12003d10b0040403494000e0506803003c10034051245111140391007403c0150040f11031000410090164901c900d0007840039400340507007410f20b81c064502a20080781d40c10706c5035400e00e0007182c83c01030340d00c001400c80ca01c4001145039880c00b01103512006e141031000509150704045000c0c81c01d20a980440d01007036032048034405001c0c8030008400940891511040102e82000490a102d6414801d98003048230f0722010901030740c0d0a41148002540090400302c1c00d181d44000705480d2503c6210b100028424045200d241501240596020059801c008801d035030300c0340c4440300070b5407003035110302d0802020030091700409280c0e40c0908000791841d6000111030038451440800c0b01e8002e4203140d44000c01d10100f00002e0070008003440040801c3ca48242c468080d8140715000d080c540d08000c12621000c010060b110b00004007810b81c4030301907613030421261040e0506903211520f511019056940030001c1754007100b0b071608a50f4001e51503240058508003602c440004840b18980c0100c11a5122421 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 821051915 1250 821050665 821050669
    0x2030919050f030f0703030507230d030b0d050c1311130906050a030203032a1e010c110d0809030d0e0a0302010f050c07020d02030721031103131e030c0f05 68
    0x1207611952020b070018a880c1d540030004c580c0d1040c10388002400c01c9000035201040002010700280b20b041c80344505142c500d03c50440c02d0304c5444c403038000400285031000280e1503141084c010000b5a401401601522015109200302c4404800c48500b2854850008030300d00403030b003002802038051100d8a84070540c203040c4201f0654203554419481484031110500c090b9402002302c0c0e2400041c0101e0030610346248156000200090100103800d010f0b151162101c440e80c03100d21103808c8080700080202e808981002d5800d00301e00483d5003615842103c500c041c6500035020140c100c5400803c072070800807503442000541319891072440b0150081401c0004040c0c090241100900d4070010a101c14a046504803c2d580a072943c041c3c400c1200d00d803c2019520140864405800d0a00a18840d00404c440c051146030a05a04800080240000c80c4600e10003005170740f0074540015041c50a1860001a00d85411041c0d144240b8400c47c0e003000800224000186c1c00245190780c42c5503000c91501c41 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 821053165 1250 821051915 821051929
    0xa0f02060108030a09140f030d03020405040e070f051201021207051c050f0c210a090c0f0302030a02041d0f0601080d0207080d0305072105060a051c030f0203091905 72
    0x40410765a038000e11480d41030540211748203069070440310310004000c005c0000500c4d03810040400301d8040c040c100c0c110061a9040c0c00030010380741c055405104000c80207000c04e5680c1082d210300c07a00000485c905005901d803451600341002c003070b60005400e2004203041801d00500989000012400c0080c800000d065201c2c48202019207101c4100868a03141d0865891aa4001d00103102201d0001340d8008801314079000001808410890b034105280c00c0c070848004003a4100240c03030134203101d1000100c0c0415089110181d0740c1c06009850303450703070751b5090002410004604a007103071f081100c1c440b030184080103c8042460b92100030021549040140c604118078070b800f541c11501b2000050154030000144500c1c01c01040c80c0014690340d07031640031581304035880515101e0184080244a90f04010742107507000b680d0840702800074568910400c00c0c00d0701000c2d01076401501b4085910013190141140740b615101d03074010b072850280820009a24018026039526200460309028411418168 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 821054415 1250 821053165 821053169
    0x7030f020703080730060311240717070605060a0801200c120d020c0d0306060c0210030f0e030304060b150301090c120912021b0a1202040e030a0f020601 67
    0x20045242540c1510000c10b40d00e001810507040c0512600c1080c01c10a100c21140070352021000c00444602144180f040540b05078403098803201300341c1c44100007620b007035955044092502c842c2d1488015501c0094012a007010405840321940d03010210320304000500103000c0c003481442d00240ca2b2401030100120b540756074100c082aa894a40c3c0380b038004040c030080c11503540c01c07280b90a071203140c614002454030154001b50300c1004c002090070500701d280c0d90050a47d89100d0000d440c030303060680d030003201100c0f445c1c820200050744160204025041500299425208525000c40c014000003204801d4608021120516600000400050001c103209488142c2d0b0229a02e180422071080d10007510301041c06102c01c110740c1e40d802c428445018800011928001000038000115581420101210443c0c1c1000141c092200e616210210f0304034000031007080103007510310644c28076520354000c04001030f04a030069683e00c1d2900900740304201070b042c01401c694440a10000c0001c1c02803d0040603 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 821055665 1250 821054415 821054441
    0x140307030809280809040e030703120b010c1b03050618120705121305030d0c0b0a0b030d18050904080a1b1214120a0501080139090f060201050703 64
    0x4060700c140512061444299000b001811801c1c508403e0300b05500fa80c031500c8555648030f40307403c21040d0743d80c5020010f40406030180d01c881b200009031490720000e84181c0300c0300700d000991428202c00040c9500070700396014110604404e502d01d88940d03506203014425514a6101260302904140240c2c1c05c0006042c60140c820001c1e003054134554509568603011560600c035044042150381c03107a03a1b62200440184001000c4404405900700c5c00341500064000544450301c1e540700041d0b40d1909809041c6030094054001d00b04080c5071802100e42002807800c2400448034600700284541d01c0401481c0540c7c020300300035665550007500030388aa030020b808045020b5000951801041040b03c9800c074806050924048041d240c2000520340d1040c0c0e203204140e007000b00f05200003030603203a01c45411380300d16100070880500b85e480305114036210314070105c5c004c0203c401452681036403034881400132203d5003030081990361242203018421810f81c02c5400143c0d59030b42080b4002e5418041c41c013500c084 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 821056915 1250 821055665 821055673
    0x311070b0c1014070c02030f0118020a06030b01080103081305041e1b1e09051905030618030d0209040612050a030905060306090a1d070e010e0a020f0a0e0d140307030809 74
    0x56100c1201c3c21000062001d41131018501ca400b0035500c082c0030280080540c88001c2101d055100781c0500900141707101a80144280c3da4041441c0d4000c0c428010400416140c44000e41c0c695912a10107610060420503240e40082d0300084540f0b481c001e1440d0400480c40c0c0c08074960512804000710340d030302900c00703107008074410781c072009540c100626824088850000507110030036203c2c140c401940030741c406508604400c80c000002c110054400342519012416250381d9100c0e00c2c003c1c010103004814550b4590400c01007004e00d03100f598002e1100c290b01810201d0690794600390200945000ca000340c500d50030600349402015403002c4a400030302421140c041c03c500304003000c5400b0300c0008000fa20402c0c0e0b20031240c00e02032584084038250840ba101150301098607030080c008030400a02c5200400107601d40400d090440500940307000c660004006410036245050440d004682000324542000c02d4503214400316014941c0d008455a0080055607982e155290060010307100405041441e08 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 821058165 1250 821056915 821056931
    0x90a08030301033f0e060403032304061403090a0f03020d0e0123070c170a06110708030621010908030906180606010c081213150203060a120311070b0c10 67
    0x8035413104400c0a00d90b5803050001208100002d40b00c400040442d280c1c055404078000040661101e901c00030a51115043c10360622403441c0c9d4000c0b4001ca009400c00b280b040c0c114001c2e03003d50300307010316800509802142c00000103600c5081d90b80000703002c00d40c01070700700c0c0319012003c2d9000400c8417605402880c2c1074044111018200c2550030303201c0d142c8501d83c000001e42405000c00b102400f4003519009000004130260500419610003107410115801030a0410401030702030190705845086402c0490b15146556890400500812071125012241d2901c003c05000060074410000082e1188241c107685c0e040c0024581d00c0d1080007011040c5000501c0c00f00b100c4110041103030354020f01c00f820600d030054914a00340300d0a00403102e40120450240c0100910102144015041c041c0982c41e07518000341043c4404041c0c1c4011580240c110b1800700702040f8030360841940b400e06500914081c00c01075050030300c0070705000e45c507400311356410004110208a4082800808114031a505040104c05 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 821059415 1250 821058165 821058233
    0x216031b031205070512070509011206050906040b0a03080a0c0204050f160e04091a01060f110303010b0306010c0203100b1f090e0c040509010306050403140a080a05040602090a0803030103 82
    0x10884980ea040081e1144003040b1691700039400d071000800303003404003811460300b5040108150400d0382130030300040c10301d03031002107541e202d200b40000e132840904600200c0d40c0d14814031002d85401c03031555400c1403034968004003040c42107020300b204603820754a0088100c0c0e1401000309841f006010b5106408000c130610010031096983e85424241c54100003500720403c0300002d00900c0c02d0b02d0040d20741804810780c8402003450800e0700b81600c0c80c83d10f40040003a508a811940c010003800071b107410707900404c018044051040051a808401498418403118580e40420305148000e00c0c5080c03200e40710001004c0b90b240642030700c40c1c15020a10241e1000c101c00c200104901c0c450720542440f110604003040400440780f048401a04019140114a50392490020000d2204640076000a03070407034440b1000c110b0903800c0b901c0d07500312940c2d81907568039012130840080c50040e000300c3c0e80c65402c004603462a110032000d40e004009280c00345449616500b4114280d0941d84002c0980c51000d207034041c920 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 821060665 1250 821059415 821059427
    0x4030c0608070c030810080d032003090312130c140a050102030c03090d1a0f0a0606020304030308061905090c1e0703140c01020d020423090603030d0b0d060216031b03 73
    0x6a501450419581e451b031151411040419401030040303401030200d44e2240300d4040e088016403100243c1015a841c00207525152140029650307201643c00402050303405591800040e6044030020403180e003900400d61f11803403420441d034003406070b42c8000700d80c0108030318260401d000185000e001451821109089458591041c20100c42c450403181454005001a18a4a01241008120440d42c60801d8032031120125030450300e03c088030307060200c0426034130301c080141c0d0101c030380c1600d45170f0780ca4540c0700070000d0105118525100000c00b80340c0c0081d0076070b2200e00160003048100c0035280e031602040f030014403202040242203001c0b041000701c2c80010b54800580d151060508400f2030316a4a000d4259000e48035004408550f680049804200040108002011340103008080e407a00c22182e0140009400300710b40c0c841d4180c100344040b43c03003044683c12552048800403d403000781c4003142c1e140822a000010845010800d800c4000c08142d00050b4801100041c0760380d041b4040f5a41d60000d180d = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 821061915 1250 821060665 821060687
    0x20f0a200d140705010e0111070b1005090403050c01021e090307120b0a09021207060e120a110f1503010e0703050c070503030103120c050d0e1f020303180c0303070804030c060807 78
    0x41c02c000501c035818048203500607992030401c2c400134003a100c048001c031505500004001d9a100c0b4100e80883c680030f0401c0926021503402626865540d03556840076107964002e2248444295000c1004001102115210040c02030118034555100e40751181414507088543c1c0200500c0320039076000c08046500002c20f1680401450303c0030030398481900c0170601c2800c0b10510100248a802c0c008640c3c160080602499410300361003140b00c482001c440950764244c410800382404039180140c400c642000140d0341280b4801910005c800711401c403107195281d000342e011a01e090310340e000780070081da80f60251a82201100c420142840c01940710161684410300c001048946d1442e00241802e0181006400454101d000d8892820f00064090300d1186281e4006101e4501c24880e00030200d80c4807a400103042880d801141160380305175000600a1040b0f1301d4041030b12450252240581d0100300412525104031a225150703480c62502003507410701c6030401c41c1030000b0750b010014110342c48100d440d8 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 821063165 1250 821061915 821061947
    0x603020d1226090c090705031303090b0d0b040c021203130c05044508090604080d0f11010c1205100302040f020a0206010f051005030406020f0a200d 65
    0x584035000764000c0da41000041c0652074580810000c0c0400161800d031060f208030441d00650303480110281c01c12404003411100200455003e0010aa5101030001103100380d611030304003450116121490104590001141d5141c92603c0c4c048081c0d890174107018000300c131047d80c0003c0ca00400c02000d041200d000041803025480800458034007445080c034240c100420010340208004084041901e211070164044201d900c01990030700d041c0d58214402c0121f03080361402404102071426582e502c1c0c154072500c43ea0354400014800880c21210a201c001a1015580c03560000c0e9064010081d1620000c01004441645450080703403086410000b05000c51001c0303000001ca42c3d0301c03d0781000790400642c0002e50498a48161290b0180060307000b0810000c05d50204c41c0b03540c0e80c83d401160300a140f4000c2541003000d4030081c1c51160700490207590007503c2542c0241c00d12030300803500341468000401d030034005100c500e01350603004007440c0e0512001c1c040b0000380140c2c2007401d001420212681c82825 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 821064415 1250 821063165 821063183
    0x504061b020d060603110d020303040b0c03070212010c320a11072312120714010c02100e0610060f0210060b030604050609010315020a2616030603020d 66
    0xc00d4400e03101011025a0051403030000b1449801d0440c020941404120f82c01700740400111803901d08001d488014680c000c0055143c6410980c2046041d0040c644c8c91009202c2070081400591380c843e03180c05004c0c9000000190f00d0040d26000f0000c00030780007214a68644410782c64140c80720301c160580400d4800c495150f0b02d40c141e40e0201c0e18200d801104403441d004007840810000340703c1c940384845030f50301c0b054007540308002010002c60015510800c040c5500c5105022070305841c03140030b0802c2c580034182e072820010301e101543d0309642d0790b4103c800060b0050000405003000314811200a50f40c50742c0281820300c2c0058400e80e110f0101e015843c20b05c5a07807a0b007509914800c22451964072040d000070710a6541e100d81aa01e16001910414450340c201000203207203081407000710341201e1300402d003051200c860081e194000d6100110301c2c400c01840004081c40709846040b6881e0381d0b146041042c1f8a031504641340503903400103900000405041ca00d04002507030300d00f08500d4006400542c44 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 821065665 1250 821064415 821064437
    0x1303030605010c12140f070c051509010c060b0103020c100606030510050904020d05160e06030f01020304031218020d0f05060a0e03040b2802030a030507020a0213150320010207080d050406 82
    0x4e400d01d4010708416041c20600010303146c0408c1040c5180100701c4009481c00f40ca0581459034070390241c060003000500103030034074824001049085d04040c421a2060400529000f01020b0641c1045108001041c4a03521800308003d6a80d00d484bd86520030f429815241400f0b0910000805040010340083d02ca003403d00e160742c0510909201011441200044084405549000ca40328541084030185d21030300404a4044003244180212841203501d81e41c1c0084001c64204900001d10b2a20044166002c000e669900141c0750034041c01c400500440f480b1000780740502e080d500d018402001c48008a0608919034040c1c1c0307001042c0e07420394800305595502c1d440c1004100700c3c3c14880d0410005900c0d03440b0145625960080024112030010f61303407c0c0f006942d0500181c0e030343c0d19490002500010b4448a1094030001c0d07900c184601441d00d60340458095481c0c03690b124041031030800b884c542c040038008018a43c1c04000f801c0040c4040b41c05840700440c1d902d03000e441401188500c800303200042c285 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 821066915 1250 821065665 821065697
    0x8010f0e0c2109070f050303070b160302040306020406171302010e0f06071b06022503020103021b010c03020c010b010918050709150c03030f021c1a06031303030605010c12 75
    0x341c88105007240302480b41442e1245002d540c0c2d40c1c0d58800c03000941e00ca04408181c504020044603034003a0060b65071803050f10380c1140796100c01425900a010941e09110110014000340000c0c0001d00340d558900d0304110240040c21440400580a060f81c246100c01d041d005076042030705c0320714a00c8102c4100b07490990020224081c1d102d5110010103400012131b42504d143d0b5070017504801d60381198200c5140c2042e051480b83c80454000345070344445c00d0404104019071090300205949950741c0740142c806000d100085003910022451400820340105a88040440901c144d070040d00c001d02e444c0c68001c0c034048d600740c4824254507001411070749900000340c0140c01032441d00010016a00040c0401106201c01444200c05d100102c002034140703010f10b00781407060300984030314108008000c1c03100c01180c20002e00070310104840071122103071030118001e2aa1503c0245108002d0584462690f40c05032400804443c080d4201d81e06000c01c0032812004520036000f98a105107860400304880c21b00001 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 821068165 1250 821066915 821066947
    0x1d0604090504080316020d1b0303060e090f120403110d1e060212180303060d03031b020a020a06030519020a03020403080705100b0f03150a020403050111030708010f0e0c 74
    0x10000d6400d0034182440200403200004501c00c0e22106000681725041d48030032603d512000e04c54800144001e61148112414183c1c0d6a100c644a8200010300555501c2d895150010441c0d90301115001840c1000350301000384280031600821280301482d050440e900c00116150600c0b2240c040d05a111003442003119499072103007411a600c3c905480c1340c04c54034014000e944080d01010b00492080c02150302151404400c000090808020758115503452041c88041c1c0d411180940c00c26807100075010240542e02c001d400340d01c50342d50185c048160b480c01402540c5040c0e91192040510b001c041140300d03580d641519410000d90f10015903281c40380803048010b4043d58001500c807402c0003030240e08014001803407085281c1118802d0040d1002c400c1004000c4000d640c503250160442d40c1a06c4200202026950b44440030210050409840340c07200ba08654441004040ba86000028860410340208900380100400d1040d400002e050456224855001078040303640b080b00454114100701d0411 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 821069415 1250 821068165 821068169
    0x1062a1e081305030d0f0c03030b09070e01090b2d09091302040f050c09040c1b0f1a0c0904111b1f02030408030402091f0e01241d0604 59
    0xc948048401a401d02a14a901248a1000001c42c00300b001a4508011604a1440d12162500300e10071307006000582d1141003c040460800d641e55290fa00f25541b801c0c4a140500700315070352010610906800508030421580107054001000e10030551702d10400d180045080e40da0407040200c502c142d582c898000e0040301c41f4150711601d254100411400c0c400052640d05008880620811845814800c03c4a40c140c9105010721400c0213052803038201034103e40100251450805078502c500c129800e9000d1280d07604070780340d504208080046c840011082081c800d4014072127200b0f030038504142e041c076201d203803881d5004075141c881c1c00107a000e42000350b61500000c8094042c0000300340c50030740c0c0c031050740c2c5810882c801165203241042c0829482500d1169030300030722207440c54880340c08201146c00c0080800c4254691004440c1c1c100e501c45800c140280199149500c1650420f0031003080b1015420140491011310a0400d000c158010350350030100d80040d0909244007001d60106911b4401c1da = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 821070665 1250 821069415 821069453
    0x15051207090608061e06150f0f041202210c1003020c060a0f0e03040302091803070f0b07031413030f02012d050711100209061303110901062a 62
    0xb100000414190100324513208492881d13050328151807400780c480c22038078156095500502980c1d0340001c4000c500008045080350311100c01d04162640070303110f25550060300300070500003802101d8411424007520500300880c0740500b6080f50011616143d0340e42c280604441c1c402c400c1681540c0c020b60007541160075112400e07050b104245000c41e42c41018140c6550502e40b114034000e8506500c2d00e000c0140e50540b54005c084121545400b4200c48109013000c10042d4503010404c007d00012b8041b00801054a01c6118031103154944190003900721410307408641482c40802003008801c4074a0a83d8854a50341800e001c042120340d00c104a004240000604d02600f164030f400340824407401d201c0ea140720f940e20b10140000d5980080031665501200e12220050b40a41040307a0011215005001e813800058413090401160028072010340c101a0300582d038801254803440c0050400020b200c0c0542401d0620b0524000080c600d44080c0d0b0040c18240003200044403210308100d00d6541c2c5040101c10 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 821071915 1250 821070665 821070671
    0x6041404060b240a0206090304121103100903200109020607060509120d061a0f041502010b210f013b0f010b10030b031f0b0a0b1b011505120709 63
    0x30f00c88880e86550000603c60054441c40c00080c090780720000132030303041c0d0305100304400c003002c550707550116a0100302001c0c0e80c0c140904508082c591846200d94031401c0e00a82e10404248004150400d01804030720783c4864507410128600701513200c9008842c8455440000000c0507514800c56908180b41902401144180005c0c503848402c1c1a400c01e40c25528158028002c0407428410b00900380704148880c61000000d000411a00400ca102a24441103e00000c1020001c4000240b07800d074002e0102000000c00c400c901882220400c6989170405c00c900081003d01440f10000b100d00c0e00f8041c501c80241c44684d50700c00c0700c51070327501801110140b00c82110207181e450003040c0d010f0000f0607101c500889041c075030300000600c01c3c0a0205000340240c040c000e48080d503900c41d1031800c040a00401900d4640000701025164452002d0083c1050451103032500691a81070554841411000c00e4070382c10900d80605200c6c0400600b01100c00c2124040d05081c41d005080d414041e5650102c254a45 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 821073165 1250 821071915 821071969
    0x140910120839070617060f0d1407060206060904140f03070f030e1e151b0a0302121201030b150d1202060c0403151808070501060303230a0e061303060b0906041404060b 73
    0x680281c8007903444249e1001d0700e54840d10781c4401c998540c4211035103a4000d2501d40854080707607000360340c00400d62900c07081e650710078420a66140355901c550801c560703004811005405040d4000e06116070309000300c6801c8020231a40303200b5400286850000340c401c0c210380e01b0400e0042480301c1128209503007064107e0844c1100704c065170700c2e42c45401d02a0050b001e45511f01d840d985586048460649666248020341e90940d200d801030b10900a00068261107840c04007081c650350700a040d10040e204e02a501810005140000e0820a020b0805001d40f0350074802800040c0c400e569504030701490510000306812400c0c0803144401325580003400c0200001018001d005041d0010300540b8081c2c0c441e06031303078096480d411070143c0705540c11503e03c05041c4002c015a9103c0c481d150307a481d40c000c25641c101a442e00442145040d964070441d0541d07594007105000b400c00c04095075100104840c20800301a000f4011242a00001e1004080c03e40e6507036090104d5480c0c02210361643d0300380c01c5180c8a41 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 821074415 1250 821073165 821073173
    0x140f0a0f060c1a0403080a09111809070f0812130b03090703060606020316021c05010e01020c01050c070c0e04060204081501140910120839070617060f0d 67
    0x70700003000d07545090890b4200300f0b030a501c0c0041070700850345503482d0f50b956a99220050000c2c18401d100b00d60341101540d002d0065601c0078200010354480301c8029009041041d02c291414103258008000e148030030804019030200800c50007074540e0310124082e07032186c400c1c3c00c3c080042e01640001d008010044240841c0d0480010008160303032040364200b00361921840700782d070383c1d01990032500d20340400d40c840c50005041603a41c00c40301030300714030f583c0800800340e0352107909460207a904400241e60104200012890034020310750404100207502d807400c0e14a45801c0540402c601030200b40c82c5408002c50204881941102c00600b49002605c1c040001e1191582c0003060030304c544c44802134180503080c040d1030031480890044803151451206913140c40c1801d00345140e016420740720131005201c110b0f100c0d0b4581d200d590b60752840d141c0c0b50600d180204e110a014138046034900d10940e11221081c0842508801083c068003542001c80405a030b07100001400b8020302400950002c110004004c200 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 821075665 1250 821074415 821074427
    0x31a06130f03211403040212012d061e0905090f0a1b05180f0a0b06030109050f13031d040609020712090b0703052203020d050a02030d0504140f0a0f06 66
    0x14402c506808403d0301000303c0112150684d020346440c50f082d040000c10700500d0302d2400480c20b054240e0011580006074101e44168218089011108444203020f28045145900c00c1c00701074000c60149660203141501010210b080901070050119a542c0c081900c22100f00b01350340322a9640d1007161104070b460324007a004946425014000217020748000f04403440e28141103103000c280c0305200745440c0d03a1000e10b10a24000540401116540e940b801021074032040e0040d0f000c0c012000b000b0070300b401e207040100b1959070011325103101002c410f003403040000e50002e40c18912030501340c0d0380041444ea2000042c001c00343d0341d004100e400d100003003001c10000c4200e41c1d60842c3d6026291001d5080c1e4170304880006208020005000500c200131043d07e1407961162048c08585010004c0e041030344030387c0411800d5880b00d10503504d40e4060b43d6030000310320f820010032503042d1441c0b500c03905242c41d00f00c00c1c0c03544065047ea124407503110f0b140e9600d4191079650100c0014041500005082c980c1c0f04005018 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 821076915 1250 821075665 821075693
    0x16050a0b1003060b0609030307060f0b120a11060a083111030625050708090312030103060b0307061b020d051b0102070e040308061e0a0314060601031a06130f03 70
    0xd0f039420164542200d1400d001a16405ca2000d03029504c3c04185a40301030042c410514001ea80b02c0d03882c0050700940d01c0d46120500c00f81c1d50b060050038480c00c9810140f01042c0882c00303292042c01c040003284d0b1400c0c3d2242002c1e405c91040740c0241c180000040454030f82c3c40440b0b5680c00a02d1600c02400280003407500c14104004040e0b040c4c400f9a2220000703840b40f400f003c0403800c2000c0c0849400001c2904c904000c150850103000e40c01e04058003200000d042503003082e21094644800f20040c0144625407044418622080300140039880c0f41c14406050008080b0250440c1105500c1c2c800640d02c8001340e91121541c403270309444602074400c4a90380c0c03607604140f4039801442007542c0402c03555506060207004a41540b071307015141d694682008001d031010180641085032410307100c101500c5465140001d1403141201c1ca001900e0b01c0b59461070407100410080c1014200740c00c0c00f0350020508581a0040c0f016030b03070f96660303402542001100307125076840004000000394001007440f242209000b0 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 821078165 1250 821076915 821076923
    0x1b0509270c18010c02030616030609090b0402031b03060604051e16020c0d170a0203070b010b04030605092b020c031c030c0f210605040f0603060e07030816050a0b1003 73
    0x44002c00000440c0d0040702440005d4140e401800401c800b038100c0c03844240e4130358951030042100d5880e07480d000e068030301c8401d080303480f8001d020522045280a0004521607104400b41004200342c1c5800265540c0d03015142c180039580d180042820525540c155801c1c00410031090b022905040c100e111b441031080b51040018000c15200c07081526010680a4140360842e01002d0351b9170107800e56504a5100c1d509000a520003000028001850342040740d008140081845403074501d9801e00300c060760350041140005030080c0781014001403e03465840c4030300c010040c14900040c41d0311005d929041100c8081d90f0b0504c01c1080e0034200e03036405000c14103401c00a030390030700a1120600c070645650115021503404240000f00c1104a50000083d5001644004001040456891011404581c41000071032000c0382c4480d0244103122060084402005215006002192554842501c54001d000c1c02d1842059481c00070f0090000801c2035080d001e8024060218038149080014401e0b095444202c0f = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 821079415 1250 821078165 821078197
    0x30b0d050a1707030c1202030903150109050606120714041806052716020102041815050306090307030507050c0a060c1101080c09060c010f0c030f1b0509270c 69
    0x7030303498401415103850f1507050b00d400202550311755603c2444505c242c2c60a0844c4011f100407811503900700300d102400c907083c111401c1c0701d504003142032007954801000540558004c10020b46140320908026502c481a881c3c80b13003100700f8034071076901284940d0b8003c500c0c0b003650011400c480da44941c40f00040b2102103e20454504040889014295410008072004007604001401802d03443d01841214005480010f01c0e15031503030062a203600042054243c070707a9880f290a4103500c40d080400b4041c1904400402da2480c0c115102079503441100340c0101000000300d007440410000b0032031203024885c010003c0050310384901e0010300081034902c00ba0740145075190072600c0ca5004003204c40c0a0401d21400e60328048403903041c01015807049545807499940e031340042c201d8100c0c0b07210305210b54583c0d40e00801c289c020020064241c6503c1a809046403080071800028150080300b00d4240c25016a1402200011501c01036407001290b20071103c9540300200300541d0988080060182051508402c = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 821080665 1250 821079415 821079443
    0x200616032d060518090a0b18060709051002060f0705090a0806090c15070b010e040f3302034f0221060c09190803040602071e0510030b0d050a 62
    0x4030400d03131040d580e41c110b0350441030700c50300814514151160300210011400320030190203400140341c403400311140700001d40312243c00d202500c4d040e011444c0d04070b071510003012141841c0312201041740d800390008050150014403404140c445080203001816210b041d80c07030714589201100d8444141c05010b074460300402c1f200007645181401039411068000300c103902545c0c2003410841295034042c0c400d88050110160303810004048d10382c440300049a8081802a0b4080b4400907806243d8800078082d085006204000001d500380708019600c00c44848070200e0b403e0034074440d8030022450744020b110b51001052029040e030400345c011207158400d0703810b17400c00c08008804580c518415007501c81070390401e00201b6050500c80014040b001401044480340300c00744400411900c94650100301542c0002c1b500b00b0050340c0501040c0010300d90300342044154074100003001e404507594058540304982c0004200b0141c2c0c8254008501100003900d030148482043c00c0043e41c0ba10311500880c4e586980c1060 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 821081915 1250 821080665 821080699
    0xb04090e0f0307080d0e0613020301151202060703090e0906070e0d350a0e031504030c030c0c1a070b0c090d170f0307200616032d0605 59
    0x601c2090600c0c40000e035003086480d0356580f1060340b0030b40c48104120b403542c210440d40304060240034003030340c9001c0d520310301c0034801d00c1418292203464640c0d0240d1421420100080c40d6003039590301869504031070b2103644021070719094a000355540c0010f4a142d0b80c0c1c404204040c100040e580e40a4401e43c0c446080000107001000b281c840c4c00c02d0002d280155a01000b90f42d0b202c0010080e440c074100c0c1c201020105181c2502d079060740c004c1c1d0040c0c03000441419894016090901610849031181c4003141924a01a100900300d40c560840c01030400c000c843c0ba00d0284a4540070106c040c0590700c0915200401000929843e5007001a0942d4010244004150071400e07a0084500c071310310242452070a20165101c00c240f00100380b04100501a00704603403113801309004020341c0315171216250500740c40c0d2680408038200c0020801004076520104c02c2c4415495100c04890800e00507280c0407a002d1030941c0c40f00700e00c007048000c0c3d00b04980300d1401401d10303c80c2d0350881001d446081d82c03607006a03803000340 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 821083165 1250 821081915 821081923
    0x91211060f150906030c030d020109061401030b180a0b0c19090f060c02060403020402070c1a0711040b0d150e1510060c08160b1e060102060703051b040b04090e 70
    0x640b42200144a400368105007007807030380168010b0005050311013429449000c0b0742840300201002c0e0060b5902d030184800c0042921407091440e010180c007500b90f41c1190346802540c140504020140241203c0c129440c0c04100542411158880d0400d0024209090111400c3c0c20804500340c018003500308014010703224440c684100d561a00c040056603148c880155111041d51100703030b8128408000110160b00c550004061643c031a05171001850710340403a00002203051400031000036004c0094001017101c95211201ca61811140000c0c0300310860b00042410019450051081c41d40f0016103040030110750001520106080903252203101004030181000700c1100c8541000da8041002c0c042d5500c605a00850304d44500f02039454035000540e0030020842c01c5c0300c2150340f00d85520801400d422254109100c11810901000040c100000080d4945500074903410400da652400241034288034865101c409284a0403c2c6d0f4860704d030854000e040c1d0081c0a1031805504107200c1901d0500001 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 821084415 1250 821083165 821083171
    0x61103040b0403120e0f330705030a0209300706140c0313030c05010e010806010806090408160f060b09131101031112040204050c19030f091211060f 65
    0x2490030490b03654958003541c41c0780400c40300310401e036070b01e06108036524002c00091301c0c5100510010000c07058402c8201c480a550f40740840e00c035440a0340806c094518007010b50ba00f000d21814415160340e540c107410307402030089200403a8008900c0610301240c1c8044518401c0b01075030a000c000f10394027050b0499035500102c2c481c920004022042c0382c5100599500075111010408040c0d9280020604803985052203035002552807030101c1c0401c10140d0307049140d41d00440c0c3d00b030914000c1803034100c0001e840500000c250b940603c0460f000501002804003c0341c07142a011080e00c054043c4505052140c0d02d0b000d04100c90403031602c286180203160030800c0600c83c080c0004200300c01c14503031361603462003032940c691941459111002c0312403c01898014124504414948011500d440d004000590f43c0190480342d00301420402401d40228030070381c2920300c1c03909050101d441106864804020301680a02134010710741b54200400c048c1e070006100c10840017540072104075441d111043c0000e42c0d015 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 821085665 1250 821084415 821084423
    0x5070e21030d0221010806010e0906010609170a02062a01020301030222062103020c0f01091e0504060e0108060a02090108060f030c0a08011b0e09011a1e040306110304 73
    0x81c4154420344040740c0062181300103040b4200610303403828000c040000420303000169543c120038014045802d04048440c1e00844040c0108102e516042d030140444846024000b52915400c0d04031a11400030000c6900c0f140d8007401995a0b1a541c044021000400c1c442101ca0f8802c1c031a640307000e41c0340500031359040e07940051280405550741d038001d1703100000d115150700c61207864810008086200ea007080b40e4490480010181ca0b400e18980281848103622040c0d1064580c440d200f9042d0340d1120f0360702d080c1c910707032a01560f0200031a40742c4160005e041e84159802420b1810104403039000200941c100c4003110111103984d2200c640800c180c1c01450030550004100c0000900b091406015100c241d0030082d081c3c400c030803410808142c102d16140c01c1280146e4461101c04540b40720301c1816200e40c0004c0c60700c41120001540043c030303480f40c10302c921444400040c0309440302e16003071011650b1000c1030303d2002092810325030f00c0001642051101fa6510b9292990004c0c03416a0442104d1155500c = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 821086915 1250 821085665 821085667
    0x25080f0f0d05070f060204120606150f05030a150305030d0501050d031218051603120f090311061908040302010c051206090a0e010c020f160605040e1905070e2103 71
    0x1c008802c940c280c000100585403503000205050215299100500c0648907041038456030394902d0504005031006644445000504103804100c215800349445686141910b0712643da5141c041602010b010f90850450b120ba18081d800070030020004000e010703030b01006005006a0707030303283e0400400b075400d400068041018101070349040005a4007910b11000c10054a00803e105520b840e03150890140c005080320008400610a006d19020a1090000300d860540318014001800402c1403080744030091950850f83c050400715a070303040c10750308048088045c6c8031100d1070410008007003c0d002d942c19000365203003101010800f0f11035002c070385050010b04842c0c0030075120075090000c4240000c10106030356517030741255128010b0a01031100a030b0000c1d801020078980c82c110b264103203034601e002d01140c00e841560030088290014241c808460765200d0003c0d07150b51752207441c100c005481302c907140b9681c074140403c801c142c1c000c020850b084a09443c1da102c0080489640b6003041445580741c1d8041d84 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 821088165 1250 821086915 821086933
    0x8160e0a020a09170a0c0905250c380114040204030215130321080a02030603060f040302030c03120f0912340605010e0f01031101080402010225080f0f 66
    0x740c0940b03880c0540000d04179141e0341899154100320000b80d4114944483c2c4070003d01003400e0065034a0b42440d01e400e11640c9040b565510090100903000741d00600b035442900a00034003a0280e41008042c2c0d04040f054038010b0b4003911140c9480760b090192180100090070442e070503003001c0c800c0d0703016280c1c0a840d05054540a0079000110380000e40f41520102072008080005100e104480d0350340e080b040180480c2062014002c0d02c1100014501c0041300d02c18810416655400076645401070a50102000280c0301c0b0b080490541c8a07a41107010b1900c800511050032141180b443c0b40f04103800641002030b074592032007150326100103800700d022400d4180540001e0075030040251b101600b40010040d051400b08011504005d1544000c1c1d1b142d0790380b50010049007035406941e9600c189403800140d515030650341d4072004400300c4c020403410800080e00250071a4002c1080455009072402ca02d040310350030114a0000e40700030700075681c40b4055011840c40d030700000200c41c00801c000202400d0442 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 821089415 1250 821088165 821088179
    0x31110050108030d092102010615031401120314120609090303060a0b09190b0c0114040c1503020f03040f030f020d0e1512090a2f04090302010608160e0a020a09 70
    0x11100040658901c041e003134403201c40684035014003031b00154540020440c1407400c034500601240351170448040c10304122400c10301050300e010960540e41c0c075440700103018015007000c850300d02011074243c0212600041420030f150041a020384503480880e4819178680da494180c40c3c032408107590880d0800143c0d5024000304407200050b000c00078014040c0e2407526000d04a210081040b41d008a0b0341030000110641032604c20700840c40b03001110702031100981001e584804c8540441c1c072542d120b078507034407003042ca000d48290101c9903050004890b00c0e407a0304082c100721000c01d00d4840c00f01d0200700543e000180c401d002007060014000c5680356141665900402d000c280b045041003045680e004100300800b4054a4401c1c0d0300500e1560001c0c54001c81a140c5051420004120401e08841c54070304221a030100c1000d41740030010544d00030070604240d00d410b80c05041c0070380203440039004422900c0040c0002251010840b9400d40c01c101d09611a600014100d20030041101c00080101e20280610 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 821090665 1250 821089415 821089421
    0x26041103070905010f08070303140a0201021204050c0111010b010f030504050c150318031620041107061514120703150e0c0a05031b0a0308030103031110050108030d 72
    0x1401048805221406000020304041c0c040d04035042c25039441c40103005041c60107503d00060a06200244800c031b0442c2c4001d844121004000800500001078540c1454800c2d0190343e00c0e02500105000c140c10f09181084c0c48240004159001940200642286203414010883e2000041e1101c42c2810800f200c01c07009014001c205840911130003e0303081c10b60700c1d43c1c030f5028540d00380001d00d00e881b401c2c41c0c44841c0480000b00c149841c103520a120080703a034101c0c0703a1503512955001c81d048002d5103100404e03948880f5042504c980c003038540a00410304d043c1c1d240040642510955041090520322400b22140200300e0103024001760204d00c1e8500d030b40c209410000c0d01c00e103010307044800499807a5600e0042c01040d411205040d5100c010745294a00b04101400800c0c2c030854180f00342a041c800070070703901e940250a120107680400b047c1329113521a6034907140a580c200500e181d903503849040240c8080c1400d000b0014902c9040ca1892000d04640300300c5040c0c500c2080518545501680d0580107 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 821091915 1250 821090665 821090671
    0x3110f010201020c0f060f07090506040605090d060c0f03062c07270e090a051f0216200306160c03170f09010c030e030306100302040b0a0302120726 65
    0x150b6508100d00d40b8a03510801c034424036507404200800003464180704660b204000917110700148105800180a681c4d0f03144c0558094480038a08240c07184103003030000c2e200b40303152800a01003d152100381d04215a01c54006d8a10181e540c906120603551a40303164a520581084ca41c0d110b6140d104400c003540020949a410070302c01d207032502c1d40003200c2c2c483c0704400c0038402080d100d2034400e60b01000395140d4203d4481d4040640030240c510a803c0d611059211502c40d107218280015070343c00c0300d03000e801681c103507801300c3c14038851254103004515150302000440700c140c40c0c0c100d54100e0f00740f00f503180008066200d042e560380e22650341e6078050030a4400341c1441c6421401d101c440c0d11114000000550542c4c0b15050024611605082c020000e0342100d00007242d071420142891203200c01c5200002c03c4941155003030703402c000300c0081008c084000b4051908140206200020441500c80e4140c02625040000c081c080320b240e02c5208043d105406440494003104429034404802e641300f045181d82c3c = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 821093165 1250 821091915 821091917
    0x15060e2d090114150913150e120c01051005060f0406030f0f05090309120303070e3307050f0102041809020f0604080f0106050d020102030922060b0a031503110f01 71
    0x54010784211403d02c54290403558900701018080302c03414585440c00310306800010314044100310b4046511345001845120140d004401c1c0c456000c8040f140080042105007080e034100c131f0381c8601c2d550071218041d0009403284066903e040307001103400e141400c100e515032000c201d0450324140c80e008050b005010b04030070300513050f41c0c6e84020a940250901465210b110454003960f03444040c281004148010f03c0f00044540d4400d03c20804040c0c0c012120000da004111002440c1d1000f5100d00008a10842c101518121103111048180f4801e200989003141c400c20940d24000d010480d490300300d00440c810403005d1000010000441d1119601c583c002c540082c190b144a11031180c08a41258059400280c181d07000b0014a0403084081c4281405401c08581558030102d039900000d5807401043c803101e2044003029940302841710017007001035150031040418080b5665580f4058482d421a8100f1000700c1e0a00409145e052040e242c045c060f281d02c60611510001d80310306103c0a4406501c1070380c = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 821094415 1250 821093165 821093171
    0x1e0f16080a0b0613090f1a0f0310021308072c190e03090a0819030315212915010504030c12120804030e0402070f15060e2d0901 56
    0x44034549800b001800c03401c05000700341c04c02c14602200031044412556080b414149045144c3c55181c2c00200c81c0d5444450486030001045d04200000e82000d129194000000d8400924800b190314039601d4501112010f0094681480d610f000d1807040c3c9561454100145168454103811410904810b541040041d259201c00052071001001142c240c4400c03409160700c0460720984c5441e10395180f40280074010f01030b00c40307004099151110449502e00003010305840b2040c88a0540ca00344105005001a0301941c55412036101203000341502c0c5001aa012104d0382e065401c251002a001540c0c03299400d402181c607612800c500c26503040003a540703410048204400404074000740c0d000000b8110307104e1510f40703400c110b18241240d1401540c400081c444284c0400003c29049070380002c10314402d850150352010706180c035103e90742010900814492100340401002c540c0d662201084e1450321845140e00e4407104c00b00581d010715030384464050105595401c0c1c11103040e00c51207030050741c088004 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 821095665 1250 821094415 821094431
    0x30f0303160c1a090c13020708070b060d080708030a05060a060f0c1403040810060e060d0b0423010203060306060102010506031f0b04090f03020c040212010b130e1e0f16080a 76
    0x1100680e0303c00d0b602e021203584001904051440c0076070b00280b180c9080701c021498a40c3c48d958804541c016100c000d004040c1303040024090340c403a000e80390b82c1c60707a1003090a90381d4651840c024000d50010b581103229680f074100040c0d9242410014132042d40e10f10f880d80c00e8401591881260a901c6a00d4103c40000d80c0a044049422040010300094001c16016240809080d030302d02080300c3e5681d104d000c5500100090055039107808481c004041d4008003240d00c40d503038504107814180710350301400d080c100000c420400314000c1035002c0c5005038800c90030340e11143c840c0700049003601c500340c0725290f054105030f180c81030385520064106443e8a01002c00301d40500301400040403030f0075a06003500d1622106030400100b5070b06020001c085002121704504105032140382845104c814000c0488404000400c2184000b000e40f8031001404044562082494152854001e6802c4420b44882500031040420300c00c25000111600ca142545071701c0c1c8400164803c01c680483c0d0185c2010146540c0f0010 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 821096915 1250 821095665 821095703
    0x613020a14151b060a02040b040b0a030608070902040608090c03030f130503011d0601150203030105040b060c06041b090b0f09130b0f041101020d0903080a140d0506030f0303160c 78
    0xd441d03034031810f0112088040100403420704000c80200340d5809148100001c1c0001c0c044c00095030240c0d030302860f0858494401d0f0400394000c0800f60810400ca00c10841c0c0020582c0c560f4006206981c010755903d0610340300c40d030038156038045030784441e5410340091110300e41038081e54025002c0c0104210381010040ea40b000440d084690611401e84c181c0e4580040d840102c8007081664014001d4140c26001180c00010003520390106000d807900c0345840d407042c0c01d020f5175903805a8840c03540d8036094a07980e0409182c4820090011001040001c0c2407200000c1c99205502c16810b2510b0050810000000810f0400030070620080400c110016904c41c0000404c01407000c2d01d124800c80302d58060b00f400c050510103140540e03100498119400b161401c400d4179884000c240840703520648290700c0c1c4a8940c030584c2c0c6100c21100280d010308001c90198940c5581e0340009024a100307070f046c0d4a184045140302612403008565000f10522884864441c01d88202007903d83c4500842c1d007401c0b0382c41140c1c2 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 821098165 1250 821096915 821096917
    0x31308030412080601021b061b2b020705030703020925080601090f03050a0b07020f0102070c050f0609090408072405160503011a0c0c0d030801080613020a1415 70
    0x50141c0c0d00c1041604006042d50300070307129540265003400100056564018041404050314000c0b500a02c070101d015152030170030402c650001101d90003aa600307142c1c0262196124000d460311000400d4241d40070f00305030350010640f4800d68134007802034140700b0304540034402d1150300640408860403505001c91a103100c1014031046011039996141c50504201000400c1c00707005130000355505105003030400004030006000c820055004031400840c0c0d5606500340d040c44280010312039654000101c40040000c0d980100054070801c036024002c2550010a0082e0340c00b07402c142942210700d64011a000ca502c200c0900141d51080301040400750b200c100440b07080045503d40034886444400344a4205500140c1c003040468520f0b10034190b40c5490740c2d442c45a204c0580700328080c200003600b103000c810140940c200c0c519018250549294041c64000c08a403424400c0685a01403000880c0423100782000310300d50181c008040c40044c0341088940310f4004866a5066401403004e0700c00f00d08144000 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 821099415 1250 821098165 821098171
    0x4050c0d1d070f091b050306190509090d02070e010b07140c031207110f010e0402090f060f040f210209070e0918190c030b100e190f020909010b03130803 67
    0xc80180340310704c2d00d0903440a44c0c40c00b40d2190300090009040300c001650150659070302103422250001004494181d1003000c20b055000680c02940b4101000a080000944801e01220913400c4400190f580c043c1100c02d903c0a00411070200006c01614002c10080780c24182d00c800000141c8001100090011346080690340c54a42642808100c42080c480e8442100d0100e980559800d44090001e0740000c111400b446a03040c42035901107054141500d4444e0442d054000142004d5034a40d5114200c00d100d40092181c00c0e0a40080900800e12203645034101400c1070301c0f82c141c0c8500c52a1982008038001c40200001e0402004940314a92540e4185a00340a41e50010004084401099095080c5018074040403100c503036040e00700c800a25052066411240c02110340b24031764990341541e00c0c1003001d69002504611448060040308620942080f01c40c0f00352003001c00200803081071803401c1e4041c84181a5014518100401003503141030300940d4401d04c42e2032020401103240e5950680c540040d = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 821100665 1250 821099415 821099429
    0xc0201060510020c10050d061a03060901150203070201030f0e0118050607030b0f100201090203120c060f04080a080601030b03030721030203040b04240606170604050c0d1d07 76
    0x61004111508005805802c40c0300c0c00d2025100c50070380355002c41d07110716101102d40e0802800250b500ca10240f07581c401006041c07104c100700c82075841c100d881c120540068500a11071400035000148900f502e03030a0020300a515000303141400030310340041d0010180201c0000b50700d52500c21032403a042080c880d201c0721035200d181c6820000781500b4000c1c50420f0041400d4141031900c40200c106a81c2d40068070715904040303031341c0742c94941c182c4401c0740500860b40c402500f41c40b80c1c040c1d40410040640103406100c000204645440d62140a01d502014041e50301608500e420000c2c3c1414034403400700300358024018140402d1440566010070f00e1544400c0050f1351606500040d0580ca607619000d6212070b0340da500d019411401d081d2191000c03800c000d08001c2901034918402e40240c4410b580201030542c00a208100030360340d40401510f54800316540107600481074000a100386003603c2540d0081d154101058109400c80c01d25070700521040303480c0780d641924840c1017811000100b0021010f0503103 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 821101915 1250 821100665 821100671
    0x19060303120e060601050715090b04140d0509100c051213081515122407110604050705011b060c0f0207090219050306010c050106060531060c0507090c0201 68
    0x11807204081120202c03228804a90881d405000c00790381d01c10152041c07650001c0070f2000c10741a015000009050010b0014140d00c0c0440c00c01080c4000c056120011010303260689100c03201c0e84200b1602031040307040d5194030456101c80c140d00588580310714141e40d88100111250700d0500507801425400c11075440e110800304c040b092001704018003000b0716810201074900b00b981070804600ca94500400340c2c46016501c0d640f0b101b1030000b8100608881844540c10b07a00c00101c0c41000803031484000c4640d040400e4250034858001000069441d200d10f4000000d403c03030a040100450710351402d0340c1414113a1084101320400308299214140035901d8030380f03500100f150b0240d80a03042c0601079000c01d20840c81031055080c54460002d99405117521031500c2a84e0740d840000513250414210b401400641c600030000c604660018002c000c1c248454080302001004c10800c5608614150401c100c503030a221410004a03000c0c401408200f440b94045c0c80d10342c2e44075500041121007170030030703c0c0050391 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 821103165 1250 821101915 821101937
    0x215160b091f11220f0f1430070302041107050105010515030c0f04090e0a11060c0715021213031101111c09051302030a0621080319060303 61
    0x91901d003282c11801154806010101203040f51038094020300b000c3c825285800415030148000100d10000031304140d0f030500e6811034807420104009260350050161b03007621210f2440c85440c0100d80750180b1040d10310199100359080d1901200041030140c0010103220b02c400104c0142c2d03e500922000128004116403a00940d040c03880c00d690060f0b04c818002e40c021441e1140c8644c03020b040f2544203070303c180c1c60341d66003031035840380a400e100e1a8800c1350000c2c5010300000c0d10690115100b9055030041c8017080e00ba40c58a800c129491040d400c1080c880c0e41700340801c0041c1c8804d007041e070a0443c0c0324010356004c9580303000754030380982c0855040800907030080320a0007081104403036400841c0085c078007501c3d42c0c0c140a4004d503640c1c000c00200b0010b48900d01940c1d06840c400d09605010300809807402d01803036134074007110010390810b50754400c40354181074010418250b240000c42e00c0c0c00d4644140c1d050044c4903290040f1507800030700b40d400882805403402c0ca4500c3e083c0900c42c0158482c0da504041d81c0 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 821104415 1250 821103165 821103193
    0x60c0b0c1206012d031b030212040f1a18010f0b0f130b041107150c0504050103150f08010b012015100e150405072c061e09100504030215160b09 63
    0x188905081b40c040c0341c4180010140c0c2d00d0108142944107074081c1a10a8038010b40c100f07000c80c001c07801107a01400c80c0607001c0084894502940703600c05c1c86000024030400301d9111a1300c00743c0b03070041c50300b54228540a40081d02d6251042c0d5004036070301c84d0000022030080d40300c04030b0295400400030340e220400004080c0304001e0800e034001c480e00d4848070200b0440f8603800c0c0090a51046115090400d81c81d0101203003000e459917070f031200078091019041c0c0741940c4c07411365501801c01d80e401c040c003050020884100c0440002000031a00000c1700141101d24203060754200ba42001510344000c010740d2a00c0132500d926034040450244480d8281aa0a99401010003040c0e80d4000d12503030401c03002d22611100c2440b00c521080300321031016241c3d442c0b00642d0010074800d0152000300f07096040b545c500c044031817084070003c00c4181802c2c3d8042c20039011a16054925114a200c020341045a0080e900d6011110300c01411010000040c0710b045405e060303c5502074150282d6038905260000c8103911250 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 821105665 1250 821104415 821104451
    0x1020a050a2304181805070f0e010803340309050f0609130b03030d090b01030c0b071e031202120105121506040c020c0a060c0b0c1206012d03 62
    0xa08400b40c02d150508240e0020030428015441074034207454152560b43d010360a69000810080900c4141d0b148911a500304641e803001244110400ca180c0d017440841e4618503084518143c5002c00300641c035001b03400d00c4500110070703040c030078003140d8844690740d503940503050b030400070402d019503103078440c441c00d00040002108909c05050710a0b0020400c044281e01c4003074000a2414101c60002000507440300880e040d40704104d8003140c420700e050590f508009031502800c3c162800f440c00b04039103a440e042c1c101b81c0c0e48141000a08208111980b0000040483c0030314075401c1e12030326001034102a07101c1c13507600344d801c0724042c040301805000040c440b5084c140041520b00d20100c00078004444007042c2c5021100020700442d000b507072290941e1040b98020414504101000303800d03950001d548000090450b900310701d00311003007072080002c540c4d46418203083d104600d040c007280c0c407010345854006451a04000480d666038845050720340500b00300301d04683c000380580d610301240a01c2c3e5201001a2 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 821106915 1250 821105665 821105687
    0x60f032d012c090a030e220e070509040302060411010e0603010608191a04020d11070311240705031003050708010c17010e04030c170f07110a080316031101020a050a 72
    0x10400d802041011555000a2040080e030301401d01704c65555014002c02c11041c4042041c2441c159014507d04c0e40c00c2084d0b01000e0500e4680042c3c480458491003040758402d400d4038007800590004000c140810441010075080e498141092050129080d020644640099000e100802c4100c0c0130041144500a0f603030082641d0080c003042013100c08000d0030115803ea06c0000e002c3c4c0d5002c0394080700c07c07800754000c510f01c0c1000400d05403100482e00c0c00400c42480c100b14140d1034041d601403402c0d242c04000b030780c2680d002102036000160340c1d0548200c4850700300030600480000f0b10b86000012440c00d02004001d80021800414104a01038014000100321414034200e0300c0d6503801008040341c11303071034150002e0307051800303a4104c8080c2c2050500c01d1018000440d21030800140e1404201c5035000401c074a074403c403244405e59410704100000135101d4424009550001c04c004082c2c3c840054400e850b0351f10a00b0018807080cc08110f1600f260042018000803800020340000001d0b000780140503 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 821108165 1250 821106915 821106989
    0xa2106080f070506182d31090203032214030a0c120f08161104090302060a0e15010b04030c0e010f091d030d1a060f032d01 54
    0x180c2480c2074049035840c07280303c040400017268020708140694a114441000e24030001201800c517060203c1c404800700c0b2040514800d000c001c00350b00c80609105400040c0383c00e00300340010680413180180c0007038105140d0499140c0001c00c1111400c030400d42820040307210400011803802c0c106840c5541c09284844041d1099000f02c0c0f41c2000a0701010b0706c10b095a40c54170040401548a14040c900c1d681c5030742d401880000040b90340d8030389001c10042101c90501070860074541643d801d09000840394265405001a001f00000400018280e00200710000c400c004580c440c0b802201d541c04030440a0300300100d4001c0019040050100409100c4064803440306841c0d8070754541050402c500c1d00c903106005e5501c0e2101c0501405100c00c003e144400e5400505481c0d4a000466002d001010000c034400c0464092082840b19030519500303450030b2452540740700e0b24503181c000e1035041d01e11071810201360030443c60301d5010303001110b04049402800b000c06084001010b00364542d83e02c41107406051 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 821109415 1250 821108165 821108173
    0x1d0405120f04051026090601091a0f01050915090907030204380a081008010c120b060f040e04050d020a0206040909030e030607020706021504020108010b0a2106080f 72
    0x1801e01c039064089078100d410454518018000c80c0505a400e00d032040c951600d90001e40900f4a0300d00c02c0103d50510400c811019104140c2e00c580c1031404840010280d55151544211040541c1c2844c0070034214620b81410300904280d60200041c40600c0f1030304142c0400c86010860344403c1c20044625608501107080550505080044c00000ea14120703101118812001002c2c1852a2181040701c41c50110341501c1c0c2e80e00c2c400b518028009141c02c0d03607a4101101c0c3c2440016101006200e403c400c452a50b42d0400720148001c494005450700d00021540004200046000341107014005c0c80104640600c1603180d14050130140d0400072111003d83c155041210090016503d84003120192035492500050445084c1002c58903a08400c007101e4040c45244140444035800240038812542540e003198802c66240da503484440205840090129011703100501090900e100980380e00e0005103808000b92010314008801da90006400216031a07580c001071018220a2100d0400040f500d0010 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 821110665 1250 821109415 821109427
    0x709030f11010c241104030b0c030406090b0f0610090807142101200a0806040903030f090312110405030309060f0f031003020a05040507021005060a0302030604061a090408160c1d040512 81
    0x548c2d924940100454801c0800000007000c02030300340e100c2005150411040382c49450300744149050f40d941940c40c9803042c20154403d440c0c09200701c081e541924003403000b03416040d01d0800c02c08014a25000211f03407001100d491000042288202c50b00c03149141c00002c240c031580e40401241c07920302c0c0078104000f500b0800011281a4100c0c2155400160a5500151202d080d0904400403d0a085c08210480c1801c3c010010b00d42d000707000462580406104000720300c2811582a251301c030700d20a0039015002030104442c00e240140192814483c4080418030709070312a106001540d0044a1040000c1042ca03014401d50401407101c0c0702030039042d6010869810075a902a42d220500d213841c0c0c0780c0545a200140c101d403100a200383c010749d405800c980582c140352820700c014060340ea1807610283d81010408507a072034466151800b8940200c0c105180c40b4070400841071010408100385e85011041070002180500410140030b41c05805180c107609050a181c07803810308110744a80c4244207014404c2c = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 821111915 1250 821110665 821110673
    0xc0e12030d052202010c02040e01020d09051002040f0b030a02040f08010204060306120b131b030605150103090201051b010b0a0303020109020108011a0d020309011d03030f0709030f11010c24110403 86
    0x1110700e0f0316809003001e003036280aa1002034094200030707080c028203500114011500b000550401c4800074441c00c29250203481c080900c000303c0c051842100340c1c040c0038170b004200d19015000216000204002d0262420f0b88403140750443c0300a59000310316a80d40010704001c03041c0d00d4401c400140090350407450070500700b519007845021010b0010030b02c1140702c2c0d120404101c06103440e80b1640900100504c0316942e00d003006001008100da0000034140310030390b588501d41c420701c50266415816140c213820070200d040b544000062815031035030659a165929002070307031281c0031100118840da0021400c0007244c03000405902044e4460111003250014261406c40c1a4054a80030f4452407030060301d03a911501b81c9401340040205804540c62511034100c4003c002200440c403c42400c1c82e85201501c030f88400312416061844040c001121000c90100001c02846503003510003014503101c514498181ca8202c04040003e01032840342c03403060341910305440746014401da040700707500c80c1d00d09080c07664807 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 821113165 1250 821111915 821111971
    0x603151512050a060609080d0207030f050f061026060105040b0102160303051e03091504031e03051e15010f1b0b01030b090318040c0e12030d05 63
    0x154650100000c805032040c544520240040580007103014450b03410002d201d1002482ca44c021140050320306600441c01c5440024445450241640180181ca01d5600c03003940034040074208956a001c2e000d040410070004004036801144200d012080243c03034050b000480d502d00d55440d50f04240e100c001c010540402080b2a41100d03000d60340410300d2228400101d00340000210627914802d1005e201005065001c006020780c00c51411075400e45400c00301100400740805c4030b19820340c0e84640056413072030300c500001c26003052007402c11042e071f000440102e140040c0200310020010780c0e6a010083c80c541000d8405070480026148480181032042090700c3c4001d020301d0050600c40c0c900842a00d6503c251402401d100e507060b041d10101e030030703490b0202c0707490320a00c4191803120201e000300d200340c81e01008441ea43d2100c040010301808204042c4009001c2ea9a01d15040c00102407000440340c0301c8c8194000034410b480d0155980346c0b94078255a00700d81000e0010440c04041d50b0740a4200c200e014 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 821114415 1250 821113165 821113169
    0x80c1b0f0307060509060c15041a040b1902040b0316091e03080c0f07060309050c09071b020f1002030c07060f02060a020d150303050a030c0813080304020607020d0b0f01060315 77
    0x715040c0da41303561603170200b85940b02d8007411000e98422105240d0506c404400c405029902c02c2c1020302d5010041c00d80c06a40300e9080d02d01425003000ba802280c1107955020139501d03e84175100d009810265500754050751a00f08039841d05d440101c842480f104180e000728110080c088809200c00580c040201074240702ca054040249401000641c20841107001c02c103040d50b40c0a000100d820b41354541d40c0c02009031090400441d1188074075046070182d40390642e5224401d00c1103a5941d60035000b444400f00d00b20f60b255009a81003009031180100c15259895a03402c0a8003d030000c0d82d13903405400d80185020001d500280c20400c200103100d807007541c040390640d08192103a40258650030450020002000c000500c61004a02071100008240d0080041c010211083d00c0c104a803040d40603003a00c8900b803c803500040711514420480004401c5c070082e58004c0d0000e000d06040040340d6002c0b9200c10203540b416110658a031041100100c0a82d6509025000c03c0c6024080900c09503a1100584614 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 821115665 1250 821114415 821114417
    0x1b0323070207180f05070c051b0d12140a030b0a050301060515070302161d070201060f05040c02070306060b03010806090a0210110a06060303230c06160c080c1b0f030706 74
    0x3d5a600080c0701e0681c3c010800303003c0d00d510100f20908020101520740300c2c106208480324040d250201c0c42c0ca0082d5241c034140c80a01810601c461001ca5840c0c0b17051030440c0b03940700305000200e01c950803001c0d62a0f003d170465086948001503000140b004100c1c00c0140d990000307200307a060481c10311207611840c117041030300a070011219444100c580707016418526000c42c0034400d2705589400040840c2c1c1800e40c00c2605c140c80c1e0303000007180c13102070f0304900b030710240c0c007c201402084017420020340c2425480002d03e81c403e0f00c169000151a6a074075026680540c1c8019003503407001c0014400c810081c0013482e00a04050001c1c43d502107194003144052032035040100a02440c50f242007890b0000740001d00031035501100070040e254480c50080d2122400c0c0c01c00700e9030821a60003080550002408072494030010000808036959466896940006030791404c804021840c0781130400251480e000d04103888c101c5000c1d0a6100c40c13082c01662000d856891a88600c91000880301c090f1400f2070150103440f52 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 821116915 1250 821115665 821115689
    0x10320061204060f0509011401031205041a0d05091501030f020409082d0f180103020412060603330902120712050c03060f0a0509011b0323070207 64
    0x60100014298000d140306841d00141040070801041102d40c4130210b41040380c00100021340b03810b034145080780da00d02070302c0310b152290360014008102c1c1c0d5031610310660b0003860090702c3c103600d4004000b080203000080110800380031444807000c51a600480d0340c401d070240300509000c08601801c20321900c0c1884042e01d1800510350080c19516180c01c0700f43c410b42c1080d904ea0395240c08440d210200f0510310030500b00c1a1307942c940c040d07040b5a410103c400d0300c2c00b01c00d281c0d42040d486c0880542c6458020410f14103041c0d080000180b044042403a0103515405400c000415901c1c5044c14046060003545135981c2c40891068040300151032000e410410848042c0000c548406101081070103e1040701c4900e24030500710005040304008070005090b42c1324105039011015842d05041c2d4806c4161003002456800348002002c01c6440c0c3d00c00d0b075110f201c0b03400203d00c41d01c114200352100c400141d81c00000903100c81c0131001040442c01110210500c5058049a41c50b091100a442c0c170f9183c0940342d40840 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 821118165 1250 821116915 821116973
    0x20a080a05040b03040b180c031e2103040c050103151202040b13060501090b0703020309190b04060f030c0906050315040b1009051807080f07021005010b0306010e090103 74
    0x2201c0d400340c030050001410159524181800c02403c000b404407582d0584c0286140402180d103000700d5040100c4a001e8000c02900110458101c508070440104e012140304a240040c0881400100d0301d068104034038030340b99207090506102e081c3c0c01298010606160401052402c000c410301a40805c03140c0c0a101d04020203c1e510000d400b40040894007544214010350030b88104040d0340c007110031584241c840200c001d64400411510340600c0c1009000368009110000c510b09220380590500180520301c04015900d400c614603240e0003e40007540010700030700d1a0b40c216a01071140c080c03114407600f0041949407070b0180080443c803006000c00b0180301030003c0c5541548032a04001d00c80300d4001c00c2c181d0300c00300302c601c010b01d019000d2180c90f01c6001000c2c01e600d4800c095001040c040e0b4183c0c2c0d601c1402d691038908021000001400005c1103215580008aa48489104950182c151015020340e00d0800d80c00050505c3d10035a1014800e0b0058801007000954089904003135000401e05110002 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 821119415 1250 821118165 821118167
    0x304020405040812010f05010908062205071203020309040c0503090d12020c120909102301050702060a020d140f030f060d0f0506040b0f0c0702090606160308090d0f020a080a 76
    0x1000701d00140003001303241000403030b01011844c1d62205664081c0d840e4030840342d48005035a9650070583c0c1c2c0030284260707002144801c90316854441d0a482c090000c03200b02d0b03941c501c81c0c5050380c91000d20541c010380011038146030510300307030141d01448506031600f40c1c2541000455241c0700c2c0c0303242e00003105000e14401041d05801c8560103680b030315940041511008140e002c00b088050780714185d82885400c00c6000900b072401c520b03000300d080c2c6d8411500d5084031420058504e210b84400001c95040c0b00040c02203d006030b6400004180040301c07a806810010034460000d0014482c0c2000101e51036018460f130311810901405982d4000000c50100043e51105004a8407a6010800c0902102c14142c071040a0000003e100340c0242c1c030031003644002e6520000c0f050304840050758035443c03018041040c400940340c00f008041c0c0010f0024801c91400801401118100300e03100c804a020030080001c10410700028410802c005443d410680382603030a4060007503d540b1101001081c004003c00c184000e1 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 821120665 1250 821119415 821119417
    0x200609010e0d1b0e090d050a020d030902130513030306060201051911041a0a0f0216051017160810140108040f0506281419090b04210309030503040204050408 69
    0xa0092642d00141803612140d001e45144400c9601c510b0506c90326800e03407100c82c800c0f421a00720070b545c0d6002d007642c40d03030034503048014041c080401c1e648402010781209074040c481c070545010f4140d41706602002c40591401500f600c40c40da21050a69142008210901c501e080e0951043c6800020000b5500440c0c481002b00307010369001a50f000044505422810014100410509005445c3d0800d1100700c8401281c0d0703501d1002d026140c041054a00b0091803c001850803078906c410300740100117504404880000c1841200d901942c4482094010100c3c0d82005050b6082001410a148100d00f840d201c90040c455183c01c01d0b0403c06014001401e000750300c05584a51540301068404608100c51024803050b100c01c402030b405018030604103400070030f40c840d500e034080c003090804045a555040c40315548000d81c0c54a015140c0326500740c1c0000e2480c0842504c1607100e4000c482c84855203528038401d109000c07161400341468402041c010030340000c150b035402a812030b00821559030382d26102907a = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 821121915 1250 821120665 821120693
    0x200301180906020f0a091a0d020a0c0f030503071214040201050708460206010e15330412080d09210f0e010c060207030e0904200609010e0d 61
    0x40b4034404034001e050907841d200100781e444d000b0742c0c0384001c2544462041c142410369620b22450b605003080700c04c0000c203407070300501034601032030821204180f210707150144001401103049001800c00020884c0070354010340c4603214019076140811005070f0080b0300c07c00e103c402a1002c1e06005020520604000e001000c6521480a8150713904100103120b5601003044a09d05a41314a94101000c004060844802c0c5408019490340280f40350b9180400000c184040500002901d801d4815005465142c0c10384d000d4105c07007184000d80120300c82500303400091100000d106040403040004110503141d0b01072500300c05404c0303206550b80708080c030900e2005100700800146005180000b4040034440c00c44035552500035908c8071075452401140840741044d1380840640800d508007101000301c1c040f81d0140c0f02051003420711015680269001400c4110121001c9070350050442041c80c8601119500c508a02425210f06080101d07410010b001071480c1080140030b000c0d4124090b00340700d02400604070b = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 821123165 1250 821121915 821121923
    0x10801060f121b180506010e060a030b0102030d020a110705010201060602030a141209210301120320060c0c0c09010506090f0d060c02011d0708070621110705012003011809 75
    0x8603155038100c40c0b2500c0455070003d404c130030315280005103503500592010b920f05000420482c501700d0f0545042e402041038a040034110701c024448956010b0f420301c0240021103050b21041c040b080460405071038898250030680c110b905105003000103540000c07c1c1c512401032414044038580401c40c40710750500800b5440c980d05045070040c03000580300071581c102081e064100a4010710b0301d0400004040c4000e22880140321042c003135044c0400e109101240d10f201242151083c06111708503541c1ca040800d944032480020006054201c0b0141003122180f4117a0541380e0003c55031500d00081c020703004d60000c4034010520b8200d0803081d0303903a03480081c0c44142e02010800001e900401d0080c020442070740044030344c0a00c00f5042c5c1c00c061000505000b120452002081c0b0603080002c1228a00300042800224491041544d1f201d80c4036401000388110542c008991607140906000b07081d41e04252a4160f40071008038034031920805001102e0645400825840c1040520190440240760001002e4 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 821124415 1250 821123165 821123213
    0x6090c03120a0e10030b01031802150d020c0601080d021c020c010c02010203090a03050c19030b0a020705070914161803170c060a020702040b03030f03150f0621010801060f12 76
    0x24251315010380c13101403200d100b80c1c3c0c204090450101c107103030000e8400c0f10203507014040c40006214110003200510b03403143d0004000d410321440c4000c2c94903103403003a040003035160001640c1d80c084035410482e004600d0003812118144130026000a51100d106c04125030421142820102c01e5900070002c9a40d08030014180040e07003035580c1440ca88408446680500c1070303002404500c0e8640c600b541d6613055a0300000504075a44450000b94020f41c4903140482d85401031240014104000c2d00c15a114011030508061141c81d04180d000c80240144c554501440203138043c40c00102002030080b002c1e40c0e40301c0040c01f002916015072680c1030090260b080d84900c10320342044141c03603054010700911882600c0c103000e03003e01c54040646900400721004808102840090300c280e0354081084079510019068402404076100403070050341c8200045c005000c40c0c0036200c640075800009190050018800802156041c8182040c44203502e104c1c07000340e11924242c000a02221620070020001450010 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 821125665 1250 821124415 821124439
    0xe010c030e1206010612060303080f04020a03080406170606040e060f0118170708010b01080a0b040f09030810090e10020c030909010305070603060e04020f060a0e030111070506090c03120a0e 83
    0x1e0b600c030f009005400c001032002c174000348146e2240c054031040d243d01d500d80b07403403581d10704000a132400002041668444140117000000c580c100340100090326050380c8207010702545c50a41115240050300c814080c0300104400c01c01103915080103500110b003186e00d0391911201c4e800484512803080c07076903660080713507010020f441c481c1281036100301c1e03200509480106645032441c5080350102d42825002c1881c0000060a03018194407030650b5490003003000409810030580401116060702003200801c03e45828850000000341c04034004268890040c40101d550240e0152141503000f02400c41e43d801080000d0019000d00c00e0301c6142c0400f03040303052103603524148550b0b00d800522955012a291680110300915244002071040da0003500c00d094100b48007007400760540c400c5a00c2d03010049909040140d070b175000c0c000c0520780c6048903800b0b42c03900464145941001720103489840d6507071004202c480340d81c4000c00e25030811900710031030a4868140241c1568003441c0d103e65242e0200000c410 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 821126915 1250 821125665 821125699
    0x140a02060408011d1507050d060b03040f140f03090105090310090f0212121b24010519080c010818030712110303042a0b07230d0e010c030e 61
    0x550740c501280320000e504104c80340b0842e140d041e84d9074900040c004460000e26100c0c0103030300801e000b203500000090304980d6020341014540065600f03c440c0c103c0b4201900038040502c403600c84080d001c102600e030740b21404410320f0380c030310448442605215000c41e11444664040c4030040d4030844822003401409824604060000d4041004034803424811040d5024032030001001c00800442c210001c1c603100c03242082d41b074848800034880314284121940c644005c552055605841007440000b5404e6505007002c014180c17080d141000d99210b00320000704440c09001601030a194002e01744114103864008044140c408624040300d154800002c40b0303010050014000c0b841507045ea034032052a4154405030301c1d102e22043e82c025100c69445a411012412a10b01c03101001d950040d180508581d45d400080f00c076042444107941084640b004c15000034084481388036030041c2c000140030044a08000030740700c508244000d504000d0b1071855041014058100c4010107403008008404050042c91 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 821128165 1250 821126915 821126921
    0xe060a0302060414031c230d1d0d0e0f0904060e1e15090a171c06030209070302090105160501021e032707031b1e060f08010b07140a0206040801 63
    0x14120340a4840c0c0c5501b081c0218184544d58443e00301c42c0e071000740543c0251040c00842c3c09064010003e5182042010111117035480b450440c0080c0c9c0799034685810521460740d0600c2c41c501456800d201d02c01251480340e680f43c000040d4050b404559a2141d038a540c20514020445003184002c58883d20480c0e040da01c00601450700407071480e00461300395a40f242801a150b41080e500c4c261203030b12020414000442c0a114034407480c0d01c00090600380142400b840350284d01c0203580c0100b00d03540385024019401d00c103c1e40c1da4068050704040d45414182d20008182d0301c211034282d65100b1aa21030001001030a404841c0c2440049842c1b0100601044400007960300556540c02d11303036810000345403004000300b00400c404240002600c4601d1540e12000c00d000b032460f0700b0611844000e031011801030420241440009555805002460705010000c0c0001d201091603c06000c0b0342801080300c040e141c0100c5010340e510001c600c08903208504d40d01e1400c3d400c442c0c000c0d0b01c08401729022421890540c = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 821129415 1250 821128165 821128199
    0x5070806040605090102070b06060a0e0a0b0a0206091b0111071e14120d11071d01031e0503090112020d06170c0f030c04110c0f0d0f0201150e060a03020604 68
    0x5042003d529403c034000d08038851003a00030046002c1301d000840760325010b0050000300d10142030031366035161804002072022440380c1000700410804030303242c45c6540c2c0c100007150303000c0c00810080090032000384e10402441c0e80f54140d28100000071849424044051000301d00400c0040071081141050f2064030716401000c1c01041518400000303224010304d44071241e20181141e003006085101055282211460744a4003948014410044009520811450505030500310090802c07025415403a048407005002d6008007034048840e40b541020520110460b00d01038000d00f0810a6600010720413006405804800030f04203280610010b003211803603400f00e414000e150203468500d11400108410003410805013501a400f814944d00b00d41019840b0044241c0480d04a03400c0c903600f101c1d02ca00d0705c0c0341090303858041e030007001c021a111a080511101000c819000900c2100c281c2c1e0035198050031244a002d134a00300120103c1c3c5107848036203004000d55005062140d070740341c88454a0441d41112 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 821130665 1250 821129415 821129423
    0x31311010513060e0d150911010801082d160905060102010207150504050708030d020a0807090302011e0504180e1212190f0e0a0201080c0f0a110a0507080604 69
    0x8880804540c030500407a40402c1c8400c1e000050203040200c1180d03a10204200181c11000b0342843c0c2d404902c100d01c00f4482c8515610002c42c41c0303280c130700d02520603000b140c04142c140f100840050158820110310410007408071702c00340080c03000a2003a07083c082100c411001160140c0100c40c0c10038201d2118480035503480e00410b00c0395440d0000124200e100b071035401350070f0710182e00001c03049040301e0b0491a000380c040c40480d80a981c55401e00da04560262421607086640002c00303c034040d410000065101c03155080c00c100c254516000640f0458150480c40e605143d0442c84807074a41c010025200540044a030003084041c5100c4084020b200d84004800d09200c0d074900e20205013016012990b0103c185024100d441c0c58210801a400c094603440c00d9145449050445010344e440c0314020000c1d110704000d040010040c000500188409401c402058808000081e00c0080070310031100031101034601090304040354803a4505000f100c49009202d400303407810010b600c140000d5114001c40c05 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 821131915 1250 821130665 821130683
    0x5090303060306091b01123902030304020d06090611030a02180a030206040501120b040203270f0d11070519050108130b040609020d0b01080d0e040b090414030f0313 72
    0x18540380a541c40080301c5c0785841c5001c0a07001c01c11554850b13030f560f4604030f02001000c00c815200c01e0a1154a4510400224050540032111501244844450f0559120070f0010b540341d0300301900402d5080c000c402c000b0f041192510318400c10032803d54055050385c041ca108058403070810703500a1000e54071108010840c215a0409100513290840c04101100d5009024030f180c68540b03401529040d1403956511116982c48102540300d0300da0740011481040c106034a2202d902d44549411503440c9480340701d190a61280e2605000f5810001c1c00e600141414249400d001c01c10f081040d28007540380e0040b07900300c003804011115842440502a066401c240ca903002159925034181d00e0010017aa00038102458080111b00894035551042e442d00f400502121a4010a41c54100c0304c2c5900307900400484d8040d84901075415800004074905041c122814001401d034000003d10440011b031001c1e0440460001080c03007410100101e809045180e00300940b0380c41d2100c1e070020b05202202068801c011 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 821133165 1250 821131915 821131921
    0x3072901091805010f0f0b1806040510090204120c3c03050a0503070b0c0a08012709111c020d02042304030e01080717150f040905032203080a05070201020a0605090303060306 76
    0x9094801d0240c8d0660200d41d910b02c60396110100005080003074001c40003c1d00d5040d010428140ba40002c1010384141160448020a01c5c9000b002c1c8003c03662002072104c083e601b402c04003449015a1803c0c2c00c811601d0903000e403020700340ca003120034185e07800180548111010b501c10880c000c0007a014050003041a50000d9a41c1216240385200308070340390002865010043c000c54101001d460f070041c003034141c540042c5c400703074003032104031440c20605940c09649200341d6500d40c41c0080140807c107603846034114038170725242c0c0030600d405006440244100d840300341c40d03850f80115071040c40c407a506104c02c01365541000d0402402c0200f055000c7c50000c0da07880c001440480c0256248403425004081c81d0b1880c0e030782c00e4529100c040188088940c070220b51907450032695a140100010b06021b83c0240da5990342c031001c03165219060801180c604c0d00340510800c0410520000d6400250307560501c55038900c400d02c0100c1c10208900c100901311454401800945040000550701c520f81c15800c40710543c0f = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 821134415 1250 821133165 821133169
    0x1606180e0105030d0305070c02090403020a050c1c06020f13030818090c03180f2d010b091306060b0a03050106120b031e070b03070203072901091805010f0f0b 69
    0x402401000c1c0c2560050202000c1076100386d100f6680101e642c68038284c0d5180a600003010040e066a00364010b0740281d02250070b100c81440041a454403c030b070890000018604d00c80202910f458014106544c0825000101c00e0001c00300c5041041c48001c21012075182d1515091a4001180b90a1401841c0d8040c242d5400e01900721400b89034444034003400c550f20b02c1026034442d91540321190349030148010515040c103042004c41e0300c031841c038283c01400c102000c0d00e510481d0600e13041c3c4c0d2402e80c1000c010203800e4841c2e04040340c004070605261040c0740000e0030120080c00059029421205000070006003880d40340d030015050b280d403581d40307010903401d0712294401d550811200c2589504040c1080e080e400c5040c03194100503454506689100355201c20015070340c1c004985801c0941c2002a00c0c404020482e090103003440d01841d130582a50724413400d140700d0718005015084c00b8503030300c0a010304030601c4611184030aa500c071000b800522400210140505080180041c1c1c15040c43d50b005028 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 821135665 1250 821134415 821134439
    0x40b1306140d09020609031c0215010b0a0e01020a14010c1d0306061c0f110f01020a12030c120c020d030e010c0c0f11121f2903160618 59
    0x300308403408850074140340b62450b1008040f801422640070804015112154a0070310007508042e8040c03071a036400403d0080c001c0d0030481c00c83c80903841d55103607900502c0b410700d06405440c90390856203012043c000c200ca0040c0d207040019500604040d8003580c9400304407005400c90f81c1d6041240e55443e0350161881c01001c0c184406041c0e25503d40c101c0350006080b81404140352800110402d801c000e9005151141d4440800507041664022080000d982e12410b00e003520035000d210138401022446626106d0b9200380d074100c60641c0030551a444a907940d00e05c50b41c004884110000c07070401c0340350003219000c0d503900c000300c1079200820f0a00c1d480c9400d804041c814456040465120150700540c9036441d12828444000111409082200255034545844d400701c5540e48152004000c8011003201341030760b01210b0106c06075a07500700391954524040e01d040541d081d06442c9090a01c000c003250000382080c0c9140d00d801404c404601000a4150f4001e0400f405211413418041f2600d413103010003288 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 821136915 1250 821135665 821135687
    0x1002181f0e01091827050610050d0201052205041d0c0111030906090a0e090703050127140109140a0c0902040f0e100e04060207030807080403080a090305090402040b1306 74
    0x1411074a664140c000441078010004242c6401c0800640c403800000c84e171298070941900760781c0c0c0d6011004000c80e202401c0c004601601007144c0b01c00035070341203500080c420310a40a0800120301e1700d00b40d1030120782c006900d10010f4000104180441c580301d5400102030814009004414491461000d01c0d40d4094803688640d0020440035510300188002444441d50040c0344103a002406e5801c0021125131000f9a18041e02842025241062850600b0390070b41c2ca42803d00103200c10b41c14503141305490004040d220b0998802c1c003d480b01401440f15a00416102c0006030455201484080c980c160110361040800c0c860108040d5403600c40301018103d0146004ac00c51940c1c800c001480018500c00c0c000e6400030407000090441515000d00030107298050720203c81464010a1003001c1640280042c2c4d4408240d2a0242c000c0c9040c0d00d0080195401038980304560303503101061010301d441901207450b522030180096550359035410a290195201c01c0d1850240c80d00042c010031480d00c11591000 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 821138165 1250 821136915 821136929
    0x70b160f05040611030c12030702062d06210c10021c05031015030f050a05060307090c020f19060623130207150501180207051002181f0e0109 62
    0x1003440c0c180b030f00503101500078008407041c912052114010741801000092101d03c140030f070054403814140d03c040e00c1c2610140c15040c0020001042c4a284620055240791003840701c0c511072000d4441d44045680b5110a25810604d01e602c40e0b46203206410020340403a00103c144c500030952a0303941c108a031110121955446060516030113803205502ca48090b580010601e500c11865903551210390310040d101d6004940072a8a4103200132107400e492180c198800c40c4480240481e00e03240300082e0321015039004140384282d0710310001d0740440c42000062000c407841000c1b00d9130b810341135006013100d0502e41d40460b50b89040050115110000714045c1c1410f01031180d91001a0b6204010080b0341c480c8000102c0c20160300303201d214042040a0030701c1806000b03451001400b54100b54142000c2071000040600c52801040b140001800006a0444088a0b40300041c0c90304414584c4851309000500c025038400200e1400f910114903041d0310509611241e1100724242c0c2114005507840700052103560 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 821139415 1250 821138165 821138167
    0x120301030f0519060b130c0e090a0e03040603050f150a03080903010f020f0d061401020c04020f0d2412030918110f1206030c062b02070b160f05 63
    0xc0040c040c210001c144900c5601501c0583d40c54001c1c400b0303400c401400989806880d43c074048228100103401071400050a9000d224604104070040c0c0b80c110141d006c240284841c00009444c4003a541c08101c0f18455402906d9a4541d5480300034042e2800b51110090f13049440c0116036128040baa01016014024202031a4949143c49032421a003050b50a640c1654a0b0b0340c084c50b0070b5003c0c1c07004000c2c41b802403103075548800d402c440b0101210482e410218440d04a41101201a80c00041401040d00100c602581d1003180420030100b60003001080361049003080175613202d40d400d40c0304c40c85006080c2c09040c046156280c1440d01c21503c0c020000d40428411502401040300c14252800204a034003404a4406080c281d41c00e0107522110070100b00c50300201d40406c040700c0d1187c03000d400010480081100048480000d4003034030a5001150603081c04140162108151088080800f10144011511041d050401c50810442140e04503207003070b00f1007400c03020280a041d80811101c4165a45 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 821140665 1250 821139415 821139419
    0x70203100216120e040f0606080718090b060c030307081e0709060302090d140304080706031e09140d030209130207030f0e040b120a030216060f080c1204050d0908120301 74
    0x1880201985a0f996000c01043d00d08070181a1143e000d050320031310100800040d00c6150090090000002500440400440313500c0d103180004004881020745d0081a800200a005d900018006110300050301c2d401c1e003c0442000b46140e00680710f50311440140c140f2846188400041c201e201008540201c04034107006020703c01d0078030135400f8201d8680003810780883d11901d41c4809000d41c095070b030f840e00d4581c00010140160041070144600400e1541814000f0180b201014444115030082007540a640e80300104140042000702c22450165031781541c14501000000502035840050018010042405103115030740c0a80f080f20b6205405988440281203440c800b01d61100d030800840354450f440c1c680100d0a661848d041620401c0c8980007004d40040030715011307041c0142510344503900c4480c200100603542c1c20241340a0b102013286080c0e400340d03a8a2450030501d000c1d944600b038003620b42c9010481007040024943ca194821600c8000c00c050303440c0c405980e5042c01a202d010621024401 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 821141915 1250 821140665 821140673
    0x30411011b0f031206080a02121c050307020d0f080f1b0a0c060b0f0a120602190e190f1703040b160c05091608061f05070203100216 58
    0x14a044041051512180c00d40022411001103244100281c403400d038500d0900d410160003000300840c071840780e002800010301e417000ca2500c422000070081c2c0a40720303111803803140440c14400c03030b2848560141c403095038800c512002003242e08101d0300f0402500c2421207606a50b8055103034028001043c0c1d0300d140180e924245050440f44000d0803440314002222100c6d610410400c002d400500c0032603407212010191400c010341541d9442c2e5a1134041e1000e500441010313182c5114640503170f000b01c052a031186d071461500d44020310460b42e002c0a841e986071003180b4195402000948586021204030030380360315414403075440030200d1143d041d80c40c05521080100310002100847d5600d0441d0507030341000e47e14540c16180340d0040f042d5016981240130702504205091221001130001601c0030b02c4d6a00d41556802d205c208003004003824446c201d80010a242e94149102118502c125203d408030b07082c84e5400b41ca6608400000c91090046071024550941c1c036100341c075021031690f101200c04c980c01e038031 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 821143165 1250 821141915 821141933
    0x61005041e150305030f070201390809190801140105010e011206030602070b0910021206010809160801020c0d0212090405070504030b01080d0e0603100510020304091e0507050705030304 81
    0x2c1c244040307030325080c0000420070500151121a0880710703032564400b568800107000100603118070b10300f80300141040440f845001d9141c0410f2051120f4403000408904156846004c1d81018507480808200c0c10207a1002d482c8941080720305110007030200000c0c108401482900c24000e06002900002d16130040e90301c80c0300001c0301c44602d1007002440d20b403a84c40302d609903882408255490503522081c4110b5a0301040a54410705100c0700440c28100007a000541205001c0d0035241041015004241c07421000d204400c0b000381c0b0142c40c3d0000aa44500c2603000c1d410440c10341d0101e02491202c00e440900200b0104052000304034180d00d0100c600d410800140409007150003003040c00c0c480440003d14419401e4040c286900c003d018802071800004c10002043c3c5049024510a00070702508548144c44101980c80880700070840c4000090200e140d405940d000c4ac0c11319042c985c01044801c0c0c0302044c11000074030801d0a1003c0d98a004042da250320a0010061103070340b00300001004244452 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 821144415 1250 821143165 821143181
    0x31b0f0320030103210c0305090406080f100e0c01210b09041505130b04060506150a0905030d050403120e0f0a0602010e0d0e030703020d06110705061005041e 69
    0x3080001c0c122450300c02200c040e2064075450407045000100600034004407030081c040c504401110392103611482d032030003000801078031402801d20a011807072400b00e0f80ca64118002802e0048229840b202140480c5562400c91820500b0211300d408808175240b0780c0804c0b15606000107854603003035481100d004451040303c0c6054904401e070703a8104402e21395508040c507400380e400b030740030012400310542600040707800c082c1c003c80c03403002c0c901c9007000050310002d10796038899003140c00014541c0d64140401c00c40160361035482c0c41100300103030861440340c000813010181c0e00254200e4400740718440702070b42d95106074000900201c0c411110500800c0c8940082c0c044041c016124000801c1345002190040240d80c00c4680580d440ba8101d803540f5000700720380314a00300300f071420342e60f20303605940401d4076107440d400b001c0d0103003114803452424420280c1141c006c0742d10071a4003555440706070820940394101681c203119480080c801c0011145018000c1410001c0c0d11140601812040c04045001300400 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 821145665 1250 821144415 821144417
    0x80705011805040510030b07171333060806090307200a09020c0606032b091208190309150b011704031d0a0807090c090b03040f03080601031b0f 63
    0x511400b150940391405603d00840110254203105421480e0100700860300810800400044c10041c0c0141e5001d2003625401c01c1c80c039800c0e00c0c680d13102418500c011030034000601201c11718103c403e0070b42c142d11448405620400907006c10080d509c1340d91a607210708040d201c901340c43d40240802da02040c90301c450404074202c21035203200d2071024400030842422542e40810aa654080341007a800380c424400168000c9045004e03040e158401d000c20558002d0241c0c5210b200c420400844001501030302106001d410750005900b0040003070302d0700080d580c0c0902c1d50080790f41e1000c1c030805c8941e4041e0241d00340056200c11080c0c032010340c4070024001848003001850411078002202245a06c04207500b90056010b981c510540303110165500c1000c015201656003d841854410810384001040580c196007502ca80854180703010481101e40d50825004011560000003e10081140c072503180f0403502d100703032203007003c1d41e071134000550444528044c510559031074540302c039500c0c80c030801e0300036050360711 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 821146915 1250 821145665 821145707
    0x6040b030a0c080a110d030c030807051e0c160e041209090c1817030711061b0705090714070b19090b1506030903040e0a020d09062408070501 62
    0x25503102d015850b445940114019000034000c3c41c1803002d40c0780c000a02c414140c560380044050b60f500106840f00000b4003508214060001c200786521400490b00203a5040201203002d21405005045650108140050324440d1010009407130f10742480020450300340700140c0819980300d45a5030307030b0030130103200440401c00d8464010070641c80b1842121a4480d041d0707924200204c5142040c460203061b5041026098bc1c4101c00e2142c0c6e03500001281d8080c2c0c0d00a094203650a024000305031940103003130b4032038030501c591031890f807a10ba00041c40c24110340045800040b00e440d03a0006503100405240750a968400801544022035900d00546411800600e25011010b841042410480300e0408080310b0256081d800c1c480c01048990203000c0221048a60624500b1b00802d81070396403180d441440d21444007480042c0b50985d1580c150b92190b0304c0440140048000e9240642c02031122109400802d2680040d003050315030907601140540d04828000c21030241840c0c01558031910742002400703c048 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 821148165 1250 821146915 821146933
    0x2090a0e190b06090d03051b0c1c06151202040c03110d150f0e150109050a0605180a14090c03060f010c0f02040f06060815130902150a0507021309031704030c050714030d110606040b03 80
    0x84011104004025458004100c80540e104200981d0f0941443500b0400d070500c60a9900c142b40700c0308907034484000f40400214915889071b044801e038803540c044081c00142da41c00140c01c00d440160300748100a04001c0700c040340103880c01583d0144e0140240c40d0840103000003400740342d015000400703140d00340c011610502204000010006090794102055034074040c0c0e85001c0302c0c18180c6500350080c04125005080d03281c0580892111416003110504118550b81b400d000c0c0802803e01c19040c40d0054010702c01d10400c0300710340d0003501691044500049007140014010325a80000300c1c0034400c01400103c032115464400d401600c1d1056090b41e1140c20121005001c11b480801805a00e2503901c907240c484445004111100c0704000c007a4891a0421047d100000d9208810340c00f108001c003a10b901548aa080403140418081802051849072000110394540c030160701d400c6401c0100c045400001c01004200d030740d240d07408085146588902c1c041141490190040d400d0104042c0c21581101 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 821149415 1250 821148165 821148191
    0x30405041112180706030504021f0c080c0d090b09010f050a030f021306090605070507150507050d0305190614130b060d02090a0e190b06090d03051b0c1c06 68
    0x310058490f100030442c091403540f5511000c0c00b50100504203802c0811043c03802e030300807038003d800c1c45115021042d903c031007880e600c1e4001ea004011280e0444c4078151150a00130a066880e80b40b00760b21000300f002e0791130000720718946400325030402806075202d4800a2088000303640300d401010811040c0f42c3c0b41c01c40702015000c50b201910b020340608806d0703c0107615090000e8078010041d0000701c1001130422001000c5280020300c44102c40403015100b01c401e100000848082c0035960009095024001801c00c84541c1b40c0c00a034042d41801500100c90443d56010700e044503524828800b001e030039a0320084070f0b41340040c0d0302002c05540c41c1010441c20b80c01c100107201c5601c461340525240d9030110304454a8200002960042c000d0b00901c1001818803200c0a21004095480001c807151138404942207921a40c013075407000d0a003e080031a501429242c050503a80046220754a0301c40c054590040407640050468982c170005000c00350301c100c505040d8034251300c42c070308241d544544900c0504904 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 821150665 1250 821149415 821149447
    0x90d1e02040b222c010504060c0f02071a0f030405030325020703030813120206191505040506010918140609040b010e0a110d0615090e0601121e090b0f090304050411 72
    0x140c00c1c0c1e13000082d0718602894000202c4181c0d00c1c1060030403100c070041c4909280c00081c5a4207941d9200400407502c210300d10240014400c08900e10802d071008000e000401900101a60281594140080108829064800903030084030420001a4020348041010034011080280c00021320701c580c2c01e0340d42007905e80100c030550381e410842c010780c040010440b00300d1508180e440240b41520050000581d113030740e00d0201000710302400344291fa446012413602d03030068509400805059045a043d003000f007039008024152a820a101101100001050340c600314100c58070817688141c00e503d80341d08200114040ba0801460b00e43e132241e45505840d1030b42c4044000d0b01d680440c105011412600b01242d002c8161000090141808054a424450802d1041c00a64000742c2840c01a0007404020003190141610741c454101031a411101d0130310441c0c1c10340098051034010303104058651548000c401c0070400c1210a035a40350000d00041c00726103003d42000008451152405040805203444030f814 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 821151915 1250 821150665 821150741
    0xf150706020d1b080c0f0307050906090d0b01081e0d0503090312130c080318150f070b0a15060210092a0608011415090d1e02040b22 58
    0x9002e40c01e8200d980d00d0f030740c4042c5003070348150010111030401440700222182030201070110410701c0004690040c10341c031594151b40341542d00900084100c041400c1400c8411000e00402c1c2e42070203840102e0000e411950210408501d07100e0040c482041d64440803103141e04060b0501070540401c00020b0000701d419a0400d00030402c81c0d4404245120f80e2a100e6501d180d80c5c1d00c17800c0c3c42d4006000600d041c080d40404012900d00a0740c0345d140010714450500c5041c441e40c030481c2d1303034044081204c0b0280287c8a0082c0c1c0300f0066000c04000310300301050200c03d914114843c280069114050100c40c00026801980f41c4603c101840d02c5494007441c00020b0100c0707901c0300c003000302c03004180400c00d0a51102c0821300402c6100004c102c0e00e41080301042c45951448403034840c500c4001501c251a44030740e01ca000340715810401c1c1d404003000d500900300d4206681d07801640300d2070500c0c20348403061401d140d80300c4203040d6506007c0c100c42c5922800d40040c0008400805800d10816402e0381c00b202c0d80294584 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 821153165 1250 821151915 821151941
    0xf0c01060b270f0f04051504020406050d0c03110a0309031e020604030201050c2721070f0e0c031f090c050d05010f05241c0c0e0f150706020d 62
    0x140100c00075142c21003142c42d2810051242030100482c41031500c500b1103002c003074202920085895540c54242004180811500c00d4100d44006400688154814068201041094414400924805011400c3e07031600309420311100010080329040d140a940508503040c42812311034115000040c0c0c5a2480a5090820340560030003801c01081503070a1080c0c1e680b01155121071810900e6224032114003a0f484200c0100c0501e1740d02000c0700c29600c04c544003a0408ac1034030261391016845030a075131945d41a11859a8000440c030011a081c450745001703c0c401d81622680300d0a41e83c0b00d2036144803180d64144c1c02d121032100d18901055082550003040c41088050b1211551050305442c11821144142d01c03000f0000f07904030050082e55913034645019004840c01c1010100020a05055142c5c0b01300c02050f43c041c42038000500a0800700d41190011a180d5141e00303948000c02c109116101d00e0103480a540710000304501d0340c5003001180030b041881d018060042c140403400e68107078105d5901c80b00d109 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 821154415 1250 821153165 821153197
    0x215030411010309080d1a030109060e060a060308120c160516050a0806040308061c210807080c0d09060915050709060c11010332011a0f0c01060b 64
    0x4414000300d241030250720340e000c0ca0100510011070700d4914aa0240501805142d40c6440c41e2119a80c003000c608011804020003c014040071460910000c00e00819008070a004240008500502502c112001c807508803030a01c2c980a043c00c500200000000c01018a0031001d0201c000f000d22110001403a142c428801014081c11442c105800441642c0c0414400c0e00340500900000c4400301d041900194581880030680d150000040e080303e8076903250040e41522440c480c014000090010894080350308518120180104422034a52500700d44c5a404146400c0115541301d5846005141010030300c4130000f011840c0341e032020b00307440d00800305a805508500d018603048880e0320540c0d42140090030004034051420a0103400c0000e43d0340f000d0300c9400b00c1100403145134040e41182a0003a51000784000810b00000554618902500d4500302220b07a00b0000c81e20340303030420358110040f01d90052715091200c002c00307040c0307075030300007c203965082d52154000540d0340380740000780c541d04001400301c2d = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 821155665 1250 821154415 821154421
    0x80705060114030102070804141507064b020c070f180504050a080f070803010e0907050316170c03070602100b1e0d022428080121021503 60
    0x50041040e60100c940f190b44108403990009600c40102d90440301d0592800d08540740310400601c00702c0072107040c0b90300b0a9000810380204001c030350040c84260380c2ea0480d400c590029040e01211b50b1401d00340c405104900c1030b00c0e084030540702c903a000340f2010500e0008d031902914900c0f6a00306a07281d48845038010b402e80c018031040e204646420b00540f02070f00104803034907003900c606555070300c83c00015150700c400060281d0104886821074620f035422080d11582c95a60300300000003204102ca01201a005202c000318a40c83d000c1199030b03064101c038000c13541503824901c0e007580f10508030190603281c0c4102d070b8440d01c4948042c044040201005d8001d0440c103641c0d0031b0007900350b0300b19060061180c1103030b084480100e960041e040211800950b824644800e452011075400c12a002c200702c00e04c1e15046079000c0480c06403008001d021580700e80c2d80550380065a0200c0c50405044000021450210050200d894081911641d22418580450040055401041d041440c0e03100c017481c00d010000130 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 821156915 1250 821155665 821155679
    0x2040e0a020a1d1b040e0907080109120e0a0b030a0f0609060305031903020306010f0518041d0708070308090d1a0901140903090109051e1818151b04030807050601 71
    0x1080e0340006400340c0a1640d28942034507130b180344101d0144004019542d00400d9500710200030141c080c20401000308012034080c02c091031002001e94403c0005001a0b9800840d818041c003030724100c4604c00461811a11603103810406890305a0201140590340e020000e5804658002c03003005500a101441e0b65041a002c140b07010f4000e01015001c0c540100103106203641e101c03944000d40411b41c82c0c1a901c9c1e1807503003518504103072882c00e500d5026040001102d00c0300e00d40d00742000540c0070700d8104c408403642c07540d90545030582c030312000d401d03610140041c00d9141001000101c0c540d1096101c1610311481901c1d45441c0001580c180303c280c1e6540000c58078081da001c03c1d80d074100744428015800c01c80c0050009020940c14052035001d41550610f02e49001d00c1001455228078009040300103542c540f0f0801c42161604654a0035010484c41a040d818000841c0c2001810210b0000c0005550380600040d000240c0100c100c1d200d1100708400800320b0440c002034412241b01e00040d1a0369454003030 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 821158165 1250 821156915 821156969
    0x114090c06040e0f040311010e010e0f0d0801140613060e18130f05012904110f180d061109010e0a050117090c04020a0809060f040f02040e0a020a 64
    0x18001d000401003440707440088101c09030b001c615040b80c1440d070790321464100d49030486002048010360808104804140040d041040c03511010011102001d00d040f1540340e485401c4031009010650030300060058602e090b104d03081801024055a10304581c4140041640080c1d138055000101000c814417410724198100480d88112590051041e0401013400c100160a80a00a00c59120f501c0d000c1c041007003c0d0001441c280e2240c06040b81c180340e01c100c03584c02c000321500d00e52160b03150070b01481d0081900c81c2a0751550716800026801c4c000100405081032070804001980012008110f000007125030207141c0d14000c1c0e00d1400b640702d880030301c0094085603d450805105605003241440a66800403041d04c000c81d284800100396141c110006013043c509100242d0050700008600b1845a04030500601594429007101c41ea55620029194051801c3e0303030081c0807040c0540300c4000b40c03901c4d401c0b050713001d0104d00a40c0e000e004154000350380501503600080c412511140e500d044042504 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 821159415 1250 821158165 821158183
    0x412060501090603030e040b040e16030c1e05101103030408180a1a070c050928050c0a0507060b1807020c04020c1905031b01020d0612030c23011409 65
    0x400d050049a056503406040001c884c0740346d50089035103030074079800c60360359030450100880846d0a50b0800301c1c6c2c04903800ea2102a5000580c2c1c0180128000218003400303052010316a151004102d94450500c1d04000340a07402c061400e08000f00d03039402101445040c0003c50086104501c4d0550307a491003500500c01c0c0380341c100700e10311880100004020042c041990301000c1060340c0d41240d030b58002803401d0401120f040d000aa08050200100b083c2e40031100510b070048046121410003000202c0c0a000c10b0f01c0c400c0b01d0000800c1001d21125095501031400f8003407903481508041480c1c0100320100e11562500c1441001104410040c820511703014020b02e05800c0083c1c13402c0d45085025440c00b9980c0d9503480594140202c026410000d200042c41a11040000c0030b030f00100c0e003d00381080343d020390042c402c170401d503605d40500000d04103402c11180e0760742685515001481c070059151503a500ca88212072040da0500300c1c0b0140d103a40828800c001301d05070b068008403020300300f80c000180b50101c0d007 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 821160665 1250 821159415 821159429
    0xd020a0c0e0f0703150e1806130f0b04060b090a1d03070b15040209060c03030a0c1e0f020102130b030a1a090414010b27060613060518060412060501 65
    0x40300c10310026420742d2018950100282c1008101c038480b0304210b0b100e600155200d92030700e00c0d188080c000b1035084410101d415400440458070b07243c4407140005000007510f04001d101c0d490907071424002400886036150311501400c4005031015070f03c4046440150200d480c40c950a5a41c0c1e00100c540ca40c900d020040f00009070010f5043c0907103036a0b0034000c0c80000d000658200e41100e01071403d40d0301c68044501c074002c0904100d442d80c0c82003044650705d400988203080c2603401d15103030742915031080361500080001c2a281d40d850107141c41050f1000c0c0c0008600404654007081581510400244108014040c52140d19928034010b00d44038229400144c041c802440c592000118554410081c5a00039400c1042d1190b42d180320800c041c0101010564907400140000042000780109032110441c8100d1070840401595a039007081010311031409241c2c01c002803220103002640c807036030281c42c0c0307000c0040402d4480c10300e00f000212550002d9111a50229000006604000c07407030191900401207 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 821161915 1250 821160665 821160689
    0x51306020715030e241005030102091c0203010615050a03051311100c0f0c0801140606030a1806021210060203070b0402010305062e020f0604021810080d020a0c 70
    0x501c05604000406a010305080607183c2c030789444d042105000a69203140121818900083e986440d2094100100c40c001c0e51100e02c078200180505040c02160f14004008000105450030041c40c044045007000d0180d07010365075800007290348208584409080030058441545810b0300800003010f86000070032401e04615003204040024500403484100b100b4102c8007003080010700c21040781c0c041581c84000d0001603202142e0400c1c4101a00100203440b906002400007a8071031210f42c203a440d06650b00d0703400038810000620000300303a80c021044440d100311001601c141940328241039070010a4a40031380424207092010256007a43c1c403030000c02450014608000140d21110002c11004101070705042d00d03038002420558810916105c6411412805100c240c1c50307005601c0d544010840c1040548115201542c10302000156584502c3e80280f0103c881070080b100442c902e14003a20500304005141c0020503452001d00c1000f00300c084940c01061080c91030b0400b03040701c0c11203078003030b07543c401c0 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 821163165 1250 821161915 821161919
    0x1a01030902060708070828080a1505130608120301060905150304080d0618090302010f02160f020114031f052d01050c2e1e050c090d030513060207 64
    0xc624090f15615604944070301d80b01c80b1071742020035151141c07010b2442c4ca0320118050807a00842030464110b01c1304580d40d0101e165072680b1000040702c0d004040400401e81d01c040c10401480c107140c902460000c0e80c080412210758800b211450080c121000c1d4031220000300c010b20441d0303802807022000700400c0342c80070320304015444542e01520024101034a80c11000540403080c0c50b15401042c001c0c40c0010000e410703460807491240c01070500301800c40065003001c1d00c00c90b10b58694001e89580f1203402159450000b503550714005665103052040f414011203a00000010003c0000b035441346510090079510302134032100744031840310b20340c2101e44509001d00a0f43d071724140084046185a524803045001c0c0100c000050300c09002c1c4030750aa1061003a0b0401c900090000c0c0110007061340700c91054213440031b40a048105940c031161803070048a1011801e029192580c6d0030140d000721181c210380d86030442090108034524100d50059010600008100d18049880383c140782c01021540301a1513030038 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 821164415 1250 821163165 821163169
    0x60411042912010b010f03050411060708130e01140f040b041b022a0d050a230f07050904150204030602030a050103050d02010b03070513151202100201090f0311100f1a01030902 77
    0x2485c5044806c10181d803400010300b0007220b080720428000b4010142ca845045a240c02d14480c1e01494821711816101c180009140800c8506c3c241650991012480304c40c0601003400740609600042135032158449108280c0341d1aa441403404c0000d0503400b21f400c0f01704110303029292a0304600e0882503014008100c20b801d600c18400811042011582d5020b4400c01c1d041c60703460304d117801202820140402444551200c00e12640ca151004080d09503140080c1030250b0544800b040c0c0f0555401a22240004002032121510070300e803044d2849005051588036140e890032604200c0d80790102964440c0184240001040010700b600c002c4e100030b0100d10422000f20743c07200c14500ca0680100070300401901e03c00180d0f0080941c1c100e030000620012a40c5120340404140150410b0b80103104542c4035004107441070050350125504100c0c5a01c0303030780c00d554049420000500e4000d20f80e02803d820800c0085c0c2a00a1060500300204041482c8840030159000100001401c1d41454600010b100041e = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 821165665 1250 821164415 821164427
    0x3012170c0702040518060c041d040b01090b060d1e05061e0609150c0d0e03030309070b071a10051c0c09051f0f03170408060411042912010b01 62
    0x4107506680c003013115120072450485581c0c0044003580f00d40102e03c00c0211182c01c6c1c1029000311030400345035210b0200490306015a0940c00d45002d04810aa8401400030340d0240e00000314202d40507250754940079620031000e003140c3c20f041c03614881900d0aa0b0203901d0390358a000d40781c1c014a0032200a210003003155002e0044240100300316008180201d0010629902c2540b4411000384241050b0341e590239506409440310000340407031001c206501c20401450a001080d20301c0760040c2801000b119040c10002c81064025400445030142d11400c2d0710382501510301e5042c0103010105031102c5060806082185d800040d1001917140d00d161031054000c5001c02c006441180c0c0c40900010705034503044402d40d0031100b100200c1c8680c4c95055000030340459504904030450f4040c881440d4480b00010703135000203100d203110301c103c142d10000124020611508a1080d10704005100150780304500d00441c088895000e08842080c00324110310b455030070140518130b04144160020821440c850340081d00c0 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 821166915 1250 821165665 821165677
    0xc05090114040e030d0e010603060f0b06071b0512010e0f12091c0204020f0c0f03030615220f03020f150304080d0603080d0504060b030a0203073012170c 67
    0x8515190ba1591104880a1041741c1440340e0414083c081d24000e040e186028001500c0b08a950900e04007130320f91305032803502c101242108020603607843e04002d80c0340c00d0802440c1840104145203282c2d030005031035440c18105021403a00c940085200404c10181ba03041a003180004412a008541095071031b00c0c22008907220008125100301804211000d815050294044001d420900c00940740b18600454030284c44040c0d0804205d424280425010360303101c0c00181c6030650049512155186c18410340307005440106c0345071001d120980c58840180951240c954007841c0200e00e460014429428605d001d15000c1c50b040c1c0c0c1c003005140d0b0403800d030350f100d1100a00107040c0380300c00f1441e4074840900d0303041003001350703040030b2540d07100e43d98214080d0082100b85d400301ea030030303240c544d85c001c407414041400c064054005015101081c07405440e004042c02d140e0610019503413088100a01392514818003203894011040110118826007014000750110000718201020700d204000003e0b0283c0c0032200 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 821168165 1250 821166915 821166919
    0x11060319051f090e160306150611030412020402070c03031107050103022d120132010206010303210e0c01140c030313060207121d01030c1709070f0608040c05090114 72
    0x841e01c4c90014407505228581d42d441040010301d9000106018040d0840b400c02c0015160141c107041d038483c800d07116081c0481b502070b460340091104004600b0154900034070940083c201610300200c6580d0814a0107450b0011804904074128800c84600f0401c0008007409080c2001c40c60300030500055a005411100c0c403218056202031890403503580d03402030360040725a16108201075610340d140c1c0b1285248102140c101c004000d0840791031522400f0741d00c0c04802060700500780781d90854070212440203200d54046101c400190000ca08800c0d180301c2c0034500060800039241000118000525140c4504501c402c032410503c0980891440442125041010010311038194034180c40c05501a0040d0342d0064200801c1d541c101440c6038000c95144002c01010440313480c0000707a40700560484141c18042c0d1b001650001c0d81900a2141007605500405200c0455070341a680d101040d900d840242c220800041045080c0410040c0342215a0090682103603129000c1d0b0610440900078001816868 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 821169415 1250 821168165 821168171
    0x1503070e04080415050301050102060a090f021e0d0602041502070617071e030b120304060c080306120102190e15070f1a10030302063111060319051f09 66
    0x41c040041000844005145862102140d811042c0e801791076078000f44501400b601404002900c011100e224444085601220207403422480c0d0302440300702c862002862074441400301d0742e0280781d0384055015658911913040507030340720b060184684544c04008801c20541d8803899080c84a1604880e81c400030601500c03035515541c0d1200070481d00e1640c2042c102001030800b0344d40c3d210180c0c0c0360b0041c0744804d005403691a0780c41a001c05540e5170340310380d01c21000003d4511402800045049009541007100204540d00803000400a20700320392200080219410081011641c055003058002005000440d062420403d4452112666100b80c160003081616624080c000b005054550004001c448002e41021468180e054028000707940c0415400751240a000800700321108031600341100d0094107035221030051780241c50422001010440d4002140003100000c0e456000155114a03100d030b4031244100d12240c2e0f00ca0460764080c0c40f1801e00070780352a09074010103034000d038401200c042700000 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 821170665 1250 821169415 821169421
    0x309180603150c09040510050102060609090316081c092307090f150611010e010e0703020d1712011a030f06010807170a0903030b10020703060216080c010509061503070e 74
    0x109000e11603918113540c00740c50070051002135042c000769102610020f8080b00c840e17403191010080307104402c84400c1200d0b80100804034205020500c00f500c05881141c070141070400321203134150008054410110a10b940708900401e0056440c0603904400030101d60701d4003110303001c04071a1681c100c0d001d80000d03541c80d00076100d880e408560098000e5280c0010707440302180c56401c002c08080100300f2440c10380d801d000f2101180c0506106140f02094814001d2000030b1555091010440d05928180c0382e010a00a12a503800841c00c024030b048007200c14a48140d45c1042d24507404280b031400c2c0380d02c6c40c4c2024400c2080d913982c0b81844a07048102400c01f02ca00d0354400c40225a02840d0190241c00032040a05100341d9820913003000c90800e101e0b8a0074031162100f90180101805100e2000380141c1c8510300820100326198014510000b40780f40c089100c403042d444840c030541c400b01044407941c0d5104104907400b0424001241c100380d2a030300d002d04c800351090001c0e40d110418026142002c60b44008 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 821171915 1250 821170665 821170681
    0x901031e09050109120f09140409080d05041a010605070f05070b0d09050c1f0f02010b0d03121b053405100612082b0608030918060315 59
    0x10180380c08010300c0303042254034003640a0400300b441120a64038003180e500045006541c003051007403680c0d9038a60700300c1c5803038030159481c4421010960031940d140d680038086001c01d8000c03d00b1000002c404034860420b031800b04400d0004001e060041486100180074403940034045400007a0000e580300398008280c00c0860401d60680e00c081080240000c440040100075003040385041d0060098a411159680c14000e1141c0300d940380500080100c411400e400e800b0700310001c8400441d00c00026598107078070200d04410311800e001d42c0410080160f0400904490003007015004407161142001c1480343d501401c0390040c1c8181c01803081011746c8040e040d084c2d183d00c0150350320b10003030162110002c1d0b0900980700d080321011040094100b50010a00001c1194800c1400d03078070484a47c90280c901034a800c440c80c0010702c50b00c40c000358440000c11a030403409600c0c068075600d805966201c05c2c140401402c0c10180c81e0098024a6400410546039008540c00d80000d40780103820341c0d540d40e03800c0 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 821173165 1250 821171915 821171951
    0x120203070e0a0f0608150f091f03030504170d051806090405041b0b040303080610020f070e010f0806100b0915070507050108091b210a0b0708060a0b090103 68
    0x2018a41041203103500040303100f82d4025020407602c19440b007403c076481d1000400c140c03d8800c2070440c6c002a0015200c3c44604080c821640d100c0112403481c1201445d2050f20128685158016400034001040c144821211803000802c407032080c80044c241c0503005400034025029500c0c00c51040403c00e440381c58030b911913201b1141c10402c0244108030f64641458003003818140a010071076aa07071400c0b0040b0302022150304880a49800d511500e070136a49030744c20004003040c000b04107001c5004008000c0c102020400042c800341c0b4452003c024036604140802030040030710303845958654407640c10301c000a61043e50300c4003540c4e0000c0c05580c3e07854070300e004218501e00c01c2450b007100e80f0001500c481802008511002500e070242e03201d004a44910b404075a9034601d500c482164110b011194180c0e500c0e1070050300b8000302d541c0d41c3c40b00302d40e00d07581d40340d5080503840001503071400fa0807001c100109a011a010f5485403007200c510307010a0901c5c03074554182c0a407900d06418540e4966005818000c0c0b05 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 821174415 1250 821173165 821173187
    0x11010815060a03021b03190207080709050c040b071101110a0b060d05010e032101060c2424091407091401020a060c121401080d052101062d12020307 65
    0x171030125011119000d40f50350340d021041100220008142d0191291b101007a08002c0311074860040c5a11400c04504400400c0082c1081040c07040800c40020f003248201d010b0105c25005018a0012807a4000058400640700314020f442d50007520348480040c100c046170380e40161065070041003c1e54a40303400d50040c5004c204080f034510000c00c001c1072040490540c01d100300e0b4809400c0d00240d90b0b1b41d10980d00c4148a00b001002c91012248c07414003002602c400701d0350142c0f503840220303103d100301107076541d03510f4540e400880035803900130300f405a10aa4003840c0318500010314442c2c2c1c039140c180d1000b080e101c010f00691949c1a4030f030120f003d4a0b8400c01c100320903980c000c0e03c10441070202c00c0700944a100000000d408150402f40811020001c41ca01541215202e002a080e0f00481c00000c0b60a42d1082c020070b03040201142c0034060130b0341260304c561f029140c2034403420308810442011015043c4041d41502c0016042c500c0349106a82c040c9940c62651082100542c8944030500c040e621042c1c85 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 821175665 1250 821174415 821174437
    0x11010c0f030e15090a1b06050913150b0c072103110f03030a1b030605150c0109080f03100b18150c010c050307030c0e2809140411010815060a0302 64
    0x3c000e2141d4514007085210899100f5400c6c1c1800000310315598004a11510444020605c1030040c1c1e80c0905161000b5681e00842080004410142ca002ca860402c620b03006802000e101041021a01c103040041401400b41c24080342091401c1ca1280c01c1c1500c000750005040000030311901030404410480d03c0703075010108054035102e1401e20f0300340c1d0050944031b40c0100000e8030600f0000c500740c06403040205070381001d0180f818440403a0308180d21548850715140c915035989c840c2d07401040c0882c014101140191129941c0e0703003003507002c2070b50b080c2c03c139007110200d11420400e0382801242c0d80c6413200c121006032401c4480e03042244a0060500401d00c1c0f1784040d508000c1d00c07085481d4020011441280d0030b032410483c511100c0412220f00c2e007042105504107150380c0b00a010414080d43c079100c0440c040008010136910740c404841520340d24640c281e04034410000384020030003a0450300122013420310305122645010094014840c00d00c2540e503000d624000f034241551031007501198042115 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 821176915 1250 821175665 821175703
    0x1b0a210501052d1605130b0418110a0c241b140703090b1b101b0804240f0e0a171309020a020106121211010c0f030e 51
    0x92440f41008615031000f9100360004003046401610000c0c1c0e01303020340c2c503a9085000900706150700390340b280c1c06034800b410a40c482110000c0c3c000c60660042c00603246807000381c804420340f4280c180c1075441e0083e102d20b00080a00c09a240385a01c135511804103600080c0806030292110700543e84145510008106281004200d074141ca000c8488080500b01070707903030301d84a281c011010401b5409003400c020700040d40504200290400680035001508103c030303088030a202968401c92511000701140f04056481d01069404000209015000da42c00b500701107940740303400e5072410038080c00c0042e0020f030000085001c4180189a0340005101400c5c41010031518482003030346556600080300446d801ca8074000d800702c0003102c01c0b0568201e184c030a1200307000c050620400c0b801a41100c481c0d0340440d940c401c40003481c4d0781c2012590328658040e1074a620141041a001881302c00c141e2085032039030303041c128101d00f019401070151050010703510740041c047c58485000b50820503401500110940 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 821178165 1250 821176915 821176921
    0x1021209010c0f242d0e0d12060b070309090f0605120304050406051807080433180b1605070803010602071d070e09180d0f021b0a21050105 61
    0x5800342e0401c0d100354200304c101c00840c895006070031784109440c0c036582000c0c00b007643e566001c50f6600f08116000b5410000c03985c0c07014a8022841e040c0014440030004900f05848810702a4501c9024064800013500d680b50480f05c1d01c01600c061100d100d9210a19552812680c80e04043d81c083c5018210041c6441201000c1420041d03076508030340260b83c440c616048000031b2074a061140490107060090b5070207180c0d516405d05450444004206072041071010307560f4540b00c0e41c6031b146480d04d0208956482040c11200c05048216a06101c02800180d880c08151020586144549a11141d50812030070003046041048130315018601d0300a041ca1404800411240d80109018080d02d035055a400c40e00407058622030601d00702a0b81d00008104a40c0341e181e120300305004007984c4004040e0840e0205000b04450300e242600925100c40014030b01300007812569410b00480f10f8508500c0f0b070b900d81c00300404000822101c10b52084545050301c3c4941c82500318a410f203100c00080d008002006245 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 821179415 1250 821178165 821178173
    0x7080f0a0b03010c030f0f0203010e010302270c040e090606090415060308040312080601090b03070f0c050613050d030c1409011b050309091602030912070f080709060b0901021209010c0f 81
    0x106c0c40030800308003641041da002c15254598402c1e070341200c8196242100e242d20315002e20520688140d03060f407003a403180c1c00300341803000c084010a01408011040315030319131508101d000c00c242c011308500ac20b41c01000504c00c0d00d9032500306851b0081c1d0060007d091202c0610113910017082a03500c01880f643c0e000c030f8000248454020049c0d1250415160400320340e0792000111112030840c05031008200c024400719034080c0c402d0103c0507003c0740c1814503058142e61a00c4040c50301c10200c8030b47c00d48c42c005498601c02c0000900101c583d103c000d04090184a03444000504007214070004500b0303203840800c0301125030788203000083d100756900020b1020031181d810490740301c1d0b0065109500410902011451601c900c01004c0000801d43c0d001d58207220010781000610044a0b102400c984102e11002c2060010146c0c030794001d01c223540090180925080e0300c841600c1180d031002c80000001d22407000103903000b040c000d2070401d015810964800380c0380c00691b541501100040c045080c4561303e44100 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 821180665 1250 821179415 821179421
    0x412030315080a1407050301050c0711010302040b03091f020a02030706090c03020a1e080d171e0a0c020c0f10110708070b1803280212011a01120507080f0a0b03010c03 73
    0x103200c080e50200360300c40c007c1c142621b4041e91a620042c0d000c00200d0f012410009040d0710100c01450f015240c2640e42861030104d400a84420040744c01895420700c1501d0200c24000d1443c07403185041d030074440742041c081d44a000b00000541881e440d00151030400258181c40c04c0507542c0100042ca950380c64100403440c11560304500040014500800704880b031000a0096010f003003603403a100383d490510b80d100c0c200b40f0043d040181d0600d00c11040c01030081900100b52081d550710a002420a184d00f400a14000030360418501445400140c615144c40d0b0342c074550f1a91304c807402c0c0460404038200d60f181c509039035a4803010303041c060b182022411180e00d2000f002009582005c1c4c07910b1000c0d50003010740b10301140000307072001d1100e41c00c4011200c04101c070b5031001c2800200740c42d02c400c050b140c0032030a442860890342150440c4c0a140001d540c0c1290341e00c00c200e0686c5804001900e04080702601c0c058025080c00000b848a0000850080030780d040060310711070290092003080345010000c2d000d = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 821181915 1250 821180665 821180693
    0x150a020a081209070608060d112706100314041211101e0e0709051806100614030f041b091505010906050c0705060a020c090106081b0412030315080a 65
    0x107800354513000076515100307540c03141c00b03600010400c80211006540d10800c82c4660507107140c211000038012410100c006071843d07480541000119100d00e8514200316141c101d208000c0c040c10b213400c50071000c200d000000168000d0780103084090000c0d100e4800e03614814100d0508ac0544240d60100e2008070306070300b1110100400c10310040f51881203914034400c0d121001c0c201411035010440030049800960000764122024040c092401c43c8800e8016013001000c49550f425a1482c03a0104296a4051b50110003104280281030941c2015024031040d044044c00141c481c039042401e0381c8180b81e035400b8010042c40911410400490b400720407207509140d510515001c20504080020306901900455406044c280d01500a50b030070310040005682200742c0080c118896112210321075150b0010f114040c1c01262a07400fa80c0c80c0c5039a01007420511020105881e8000b030000304021205001055031481e4541404541c200d10100b808000d0000c2c0d81c0030a0861084407107401c24040c2220b03440318 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 821183165 1250 821181915 821181931
    0x1401020a02090c0904051302090f15191403030f0706050c0d06261b010809010207061404060b0307030c03020111012c070905040503040e10180609051005150a020a0812 73
    0x6c02c0e0340d11024894000c0401107030180d00000c13100005104d40c4000c40c0745c0d030717840341031258100f80b000c90040201d07002a4000540022110781004127004800501ca244d00c000c540c00c500842c504500c4110080040c061841d00416194072100816103058994040d40c064041c115420800540d407400b0b4405001780100104030040407030030a10880000105c0c1d6500440701200c4045490444a001101c00c02030007410540995800c8c460040010104d008042f40a0f0310b00648440504040c01e2180c12030340e0303802c101031203640400d104200041c45000c012088030b409081032100d00a040d00018003501341c10085e25100e484410aa603004200801100810048501212806600c64201a0884000b600c000d4150350080c84100711001d40451116804900c22442c42940ca50360a00c2102020140c020350021030380700e18042c0005034092045640c404400d03420f0000252410b004200070142c01c030b030b03001c1101500044036858a8000c0100440b0140c2c0440e2071039890180d450340c02c001910a0390000 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 821184415 1250 821183165 821183171
    0x120a030b2e03020f0706060e01081f02070201020f0a0602130b040f0909080c06040308040b160e010e06041d0103050607110d030b041d0a060608030c071401020a02090c0904 75
    0x48160070070921988010300d103460325022022003200101900c54004120900301502084010400d00c0340c8006402c18070321070080403904608001040e01e810805801c60704160f48043d0822010703601d1782c00380b0006842c140b000107aa42c1c106000403070801507142d070b000a05205440100081040a500525444c164070034070028803515030994184500c00d40c4101e50b62540c01c0c2c607007401003040d9980300d044017030b1090031040d1510b00c142c40003506140044030143c0102d504401044140800c903482182e11000000b6481e5000051120250120100300c0086040100884c09400680c40d010200c0f0040d042c0d0b203030900345030819500c00450601090104640d02e008440103c2c040718040c41000003842c5204000d0711840d443e01c64201c00408070515115030140d25846003440d80905804014841030003000541314034403803418020251211a40800c450b584100009070300540c0100d4000305440e2000c503a541701c0a00080100d24105036040060b6000c076804041c4144c02da00c803401401c01c103505960034 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 821185665 1250 821184415 821184431
    0xc09051011030405040b0a030203120454110702041503030c1b0504020a110705030f0c0d05030c012306060f070b0702070e15150313080d0b03120a03 65
    0x300c1d044000c0c440d0840460303005002c28002444e00d500800c00000010700f2800000d962600001d2820383c40c0e80003079204c01030004060194103003c1c80400342000800d2050074403410b94544000c5165151044183c4c04000014001c1010342e00000c0c06c1c41d501010182800405810700d08100c250b40059022442140303440c90445e528007001101404807505600c1e200000c140680b59000e201c00900c000345030001c3d808201003160ba9551018101c0400075a40781e80c418030b85824028907045003904814825444628501d60300c010020b1f01c07000714501030f501003c40340901d1402c2d80c40c501408050403a01d508100ca903813812150001e5200d0700c01d05400c4421225258a0b084c4071052140d00040d40303c10314104035a4003c03900c000c140c2c43d003140c1303688121100c5039554000a1603055044d100702c001c9004404d40f001c0186010403100107145502c40002e491820f0080136125412202c40000f0b00c0e810002c00c0c014450402a441380c43c1c1540c001d815607000310850340001441d9800b1440110200c1d20b00552 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 821186915 1250 821185665 821185667
    0xd02010b1c1703250504030201030b04090209060114130b07030f1403180a0606030b06030d03021809280606031109010c140111070606030b060316091505040c090510 72
    0x1107410a40c002030300c1020502c2d14160802541c2c002420b0004015411030b000985100031032180300c107200a641e0b602e445500b03500c00141901c41030083e06210700d08000c0b402c0c015a075400c00c0c40381c005009003402e80c00420509042074850040400060100300e0340d00c0c0016805c50f020f40200745d40380c4259245900c951107500c01366180240034440b6540b030314061001440380d590100c680380c1d585a84c0400c541c01043c143d61001c003901c1c126081100da123030020f028001c440c1010825861841a142415400c100104026119410300140c0b224420203010b4041007060302c100440d00c62031a0307402c100044441d80c0b8100c400c060038581c4175210029180c00c4213030310150031000a40e8803c180581d20811a00000c0e00c503042c10489070720a40e4495582c540d0000d009148010040c06031512507403011032820f255040105a84d20300034009400303a00800e1003150454000c0c1000300a9442000340010488941010110011410f0b004140c00c40d15000d00040d54a402c1982c50007101c004803289641842d074914 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 821188165 1250 821186915 821186959
    0x301031110051207120609050a0903020d030b030c1903121116030b0708070e06070c050906030c01080f04082a0d260a0e0703080d0f1a040903110d02010b 67
    0x56400100b000c0f0008140c800d44600e450003034824891102041217920b44018904640b416034900350846e07038421109003003580521981e9103203040c9003400c009465010001c0380c0c4641c003011038680f20304004610350346087d10314804580515005440814040c45506002c1c00c00f01c0352644100c1c03940309031410010401d0400a0803020b4a43c4100d0101d12615190030a450890000d003104090002005000034036840711009055924020030002600b145020700703202683c01d014025034001e80204100c48000e980104040d40c1100c86a0020402c0d03958030304141555001e4035041000e0a10440d00d00c01c14000c050065607285200c00c0c068510740f1410746016642c052440444450311980101c80c2c0c3c050001482d030817544150301c850701142209030411501e042000f0b07a0000c40703007101c01148210712014030707124000c0403208601042158491070500c50680440e00741490384226200c00c00242058440d00c91860041740342812105d010350000e2010f40a00400e4501600400c0149034400c0040d100034 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 821189415 1250 821188165 821188177
    0x603070b04360504300905011b120e130b0607080a030b03010207030504170a17090d020306010e070207090501030f061802040f05091005040b070c14150109050a0b090708150402030103111005 83
    0x2d214146c81034646001503031228800c45034210300e020858584c0c0c010813244942c20010320010351782c600c11980d600b0104501603007400008000949040c2d1490b2054440c80125107a213074000c107625854481080088011f80080d800d41030f01540041401010103070042e01900c151014461040b00c0c90800c8881d5954070940001c018103804400040c4101e8041c6082c01000d9170140036025a02980c0250003103442e2200a0f0300c04000d24106a04004d00c0700c3c3c0c10300c098800340416540074041175156882c0d0010b160240680984440c0d82e031482d004d00c041880b410724035071540c00381080c818200c48900c40703c010802107400c00e65900582800d442c2e120200d21034184a942e110241c480700d626014002c9842d1403a651089907d40d41d00681060500008c020100c02501514544d407055814500128141c4c0e40240c180d00c03000c1d0a184050342141d840184082d441082807914103001c2c2d4801030110644503030301310420b801c540300100100600148030b04001003500d080d43c0e00b039104a00d101c021a0103101300 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 821190665 1250 821189415 821189417
    0x603200f01030e011d0c030f0610260d0207080c0303091807030b19150903050a140c0a030c1a0403050706030f0b06030f0603070b0436050430 62
    0x400380d25a5540c003d500c03642c00c40c62000b0001071407001411a05a40800a60109030143d004480c0c0905a00c2c003046820048a445005050203040100f20359009110f9802031240c0040484003001c01e40510fa007003140d140e4402ca0496904a60084010391500c01e00e00542656000312503007103e590500000711a1b540340050004034007810b00c05043c400f035680280c4a1001c2503140c0e49400b02c2a0795202135207041410119492190901c0c1003031200360340e40c6000d03c0300f042c020700075010004110301055500b01a500802c21404104164500500f00100001d09580c008115800441800940542c00301076410082044282000c03142c00c4581da0b01461000403e180c0c055401400041d02c04e0300b0040441000c00c4012403c040a440001d600307410444401c0c060380881c2040081d14601080390000400c0c0c5019403030300e45420a60076030300c24603d101c0d078003880038209410300107098803d41c410300c1c4100701c9a0041201d230070301346040d03d1414070300b4814001c68080c0c80d01c1d04461001c086114000d007099 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 821191915 1250 821190665 821190679
    0x51e0702010e10020702030304030f150507080126160603060806090106083003041103010f110307110a02030a060c110c030712061401030c0501140304020d0f080d020d060320 76
    0xa0000f490301075401110101e8242c00241310000000d10b4801500c000c0c1d52099991a018103c044d05500c2160710042c030003010071800800411408150400800031240000d6100184002d01194945000200e8500c0401f07441c0c8844001181e5902d9070000080c2c03080b01d01911810785860001900740ca03a58041d0100a4201499148800c10000a0068940e0700740c0d4030881d420082e11040c50b1150000c03034040d50344c074440c41c03142c0000d4a0300b0b118404c50101c0820301000120503847c860720700b50000402e40024011481011300c035409007000010354496004049480c0110545844809000d400c8124008144100c048594803440460764101c802405001440c0c001d150481c84544c030440041c0c141c40c22a501d2080c0c924a60380707001c42a0186001d1060381c0d5965113042c0006101d131482800080c2e42203014400c0c40010380e104010030300e1250708001d00d84a016100c0c140a0007a200d600c4055800520000d4000f4042c10b644c0c120404480c005d0302c0f5044548200c0410f54104e000306218190322400c = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 821193165 1250 821191915 821191933
    0x50a02070f0e01260a080a0807020105100302040b010309020409061b08040302060c0a0903050a0303060e01141518030703050d23090d0309050d030801170f0712060906051e0702010e 79
    0x4ea854407254504102c000240c40c40c600b81d1200c0c103154000405035000e000005414440303540001d8600d4100c10350344000c01151910000440281c1c402d800b00074440c6440c2c48a410050381b09810900c030954005008001e082c031903140c02c00060450401c0e20021034500e204e80400301d80503548240c071503901500984510b40c2c400c6200507084e804296881c0c03d00c010b281022000c14010040c041e8114402e480014199041118a0010b440164414081c440c910b120310000394032036590b402c0902e5800e400f01074503031040c401c065071080c030302c800003a8041c071810f000002481070000300440c0380f0045131500902d441e11f203039101c0d03280c030b04a4180d6100e0502c200082071903410704520245032940213103041848a034441d000698801002001a0b000400ca14010700040b2050003501c800040103900a00605d04894080c3d900d4070610b10a990303000314000211402d124940e0004191264009004c0142d46040034600c4442d603072543c0b00380d800000d40400190491b00511404803880c140d20018400e01c8 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 821194415 1250 821193165 821193179
    0x4109061b07030c0f081c0b0607020123030f071d100e130608031234030204080d110d17061c06320408040e06030102120403050a02070f0e01 61
    0x6407140d00110104100c00e00b032100810101010642564130599010b542d54154501030164410081c07aa01507040c030707000480702c160740d800080301c544e140e080c2000840d5070f5854021800941320301698195034100003082009421f00444524401c84850b150009803003800140e18032540c459441054008003c2c0b400c0c1d6407441e0040454a40280000345101106034040981c2c030107880c103031f92007016640d00c04070320380550005000040d40d0116a459018507400d400c1341c40480c5801d081002c410180e44840045002c061103030301210094005039085601e0002d0303400d0001e00381d000d10040920507020310340148a890348507400b0032001c8100005000500d0311841e04204c400c5950000400f02820603110380c400080545c06a200841194650a03c0f07490b400ba402c2000030000706803101c00c42d80f580d000c0000240c0c0850039101580c440d108110100d0350f801c00032a0080c4076450418040d5080c0c441000f0403d54440c006098000d041e07800e030303410300350744003107800f9280068020342050049100040c8500 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 821195665 1250 821194415 821194417
    0x3010b0705010e0f030a0e060702090f060a09090c0603111219020705190c0509040302060a09170c0c1903110402070303061a0d06170a064109061b 64
    0xc1e0050000065501d03400708001d1034001c000000b00781542021030039078105600001201919002690f590f0714005250780003602160000780b51240b42c0400a020407219152013044c0000303031a80044c10440001d044c1070004111089100b804006402d00c0080d031003001140c002e84040803000d0751507008a032940070003191644007019a0f199415404d10500c1e010078000c00a11040d07080a50165001980038240016960700d00c0c0c1146000701c120009100000f540040c8140d4014000d00001604c01c501d446c1c454a00c0607034044c0e50340c40300400f041902c01144080b0b0360703017000301c1e0850300f454024001407003183c0301c03910301c2c031000d00400c0780f80d04400201d00300341d002004818400d1a00081d610b4880040c4e1110390000541c1d10001c501c0851002c2c04103d2602c0741c5405841c1c40da5000700814040421075640d5071442c0030080135181c40c0d02c7c40c520b400d8030702038141c101c0c0d110300b0380840c80c1c54504520104650040000940141046001250007004040340c0140180c03400000e1100480c08000900c280e = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 821196915 1250 821195665 821195677
    0xb10082b0915082d060a170a062301170c031902150d230601031a0f130e21040e1f090204030803040b06040c02031909090509010b030f07050603010b 65
    0x1028080d404443c2440241c031050b50200c014903c44c20045003407160500ca00981c3d2900411910040031124005224001421100090f440342001c40c080c6140090b00803004982c14101d0300c40e034a624004289070303022441d0302041001c69411510010110010141d07035510b00744072003200d42f035413180c081c015081c4442c1e02601300000007203a07440c02240c46c0c005811180542c45408001c01c0c030901d403911881511648a030801d20900c1d090140302054100103920400c07015006c0d10a025030200c2c100f10391140c0a10364140007203c0c0c800c100d2f121400d0f0074a42c4031815240c40b502107041007065450180040f83c2918113490100b0086070f11552154400104104688100712041d07803c00000030721140d280c001007010358801c02005449042c186007001c880c41002d0070980c8143e08001d480c500403a03000040c0d6078410000b52001c84d030700490f070303505030307001074440c0c20400c7c18505000810080d014150000c00039541c040d81120440c424105038181c079080c407070264981c030460410040102c10100303009820 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 821198165 1250 821196915 821196931
    0x141b0618030303100839010e060c150703150e091c090f0b030c0a0f02031e13050f03150a0b1207030c0e07080402060d0221180a050a0b10082b091508 65
    0x9505886c100003035071540020040d180e183e8400742d552940c24bc85401100d4000161381000d10103103200300700d02c02c120032040c0194201150440b00103042040100140000c0000706184003022800a5500903d80102401191542441038070001841418242264401d58140c4085030a02d410603208680800c04c070340840045100a1041714200303005840410440380c0a804c41c5a0790300c0e28400e40d543c0000c0160321840c0f10b40d108911031209500c0100341251004080208100c85035592803041008041c14070049810065209240c08000c2001840c40140c070701403200801c40c15510b0250004103001201c0240004039144041801410b2070b1010300110032210320058140382e09081c01203004010001903803007240941062042d001071001d0138003460382c202c101610044510307842d090354403040920003c00741001d031400110041c20801d141d1018008210030744000004c482900c0643c44507250302060000760144200650501800b100f104a901d074103030901c003880da609000d035010140204022 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 821199415 1250 821198165 821198177
    0xf0c09061203040603061401110606010f1101060602030d0e420f041407080304030f05031207020303040b060906130504050c10020307141b061803030310083901 70
    0x101d1080820710240001d40100d136400920580742c00a11200100301d0340c113a50610080c1000550046008104180c3c80402030a10804c0b0b1a04568208e400b032085168202c0b946d40780080110700158040024208820105018071000d04040c00f1035880d16600041403104c2e030300e00c00059104003049881c4250188401401868881c40410b16031020101110359262010110b001c100400110020114101405800618005041c0303401c9681ea0b200d0340c04040d2646850610070401c00c007040003116202038280d8507081a6080a4502030f5590304290350460307014540303078001031072401e00018861250f2001401c030084401c060703d0700300c000c08025000340d0300e6004000005a80b82c84981c045031840b095540110380d03803205410302800c1c2c20030068201455800c40101c00f841c40004404200007804110752050741c0724a96a44041e03060150003526406000210821250104c44c0d14480c00b05c41c0740409513242141e560115608018803a2403010840d01c020b146c03400c1d041c0004201e00350100040c1004 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 821200665 1250 821199415 821199439
    0x130f080d050403030617060103030806150d231b0403080a0c050616110f07061b0c0e041e02030d030b040902030a0b090d05030c04061b061802090106020f0c0906 70
    0x3241610412502600440c2d1900c508000c071001c010a0711141c11000f0f40689855411035400030181d90024010521071166940c195400d00200c1c42103d0118658250400c0000d01582c04019400c01c1c591004a51100b81c50002e1001280009054451045406010302e05801c2d030f69040c03015003040c04d04a00700700c0c1c5000480d0000f141085500d0140c880d85040c1c1741d40c1c401c02071300101024081504181d640e003004405034500000050b04100f91400383c103114814032003000c542c032882c043e402f0002d49445015140002e5904418024a000e28007072480f000d01c0c240043c10303081d511405190300940540c800b07881c01d94224820360140c6403200004001080d400400d40000c1d207404001c8a045d00c00491560900038280d41c104240c52480c03a960502c1810b41c40c010351080818040e078440c42c028099540607181c2d00070300e0007a030203242683c070000800141d070266180000050707001700c00303d006031021000810300c40d00020b0204040d00c02c490092810040c0c1600340300d480003002c1c14036034000701c1346481 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 821201915 1250 821200665 821200687
    0x1209190c030818030d03060e06010509012a05100f06052209020307050d03120f09020a030f031806050a02010510052409040207080d050c09090c09010c080f07110603130f08 75
    0x6540000c0b940c007c5200e42c2040b80c0b01310a001c000c1c0525040c0b000c1000241d02990300804203000d0224044150559034544c1c540420048940d039400a10030300444155440214072130f03110307856110b1031400070807542e6111070911a144178200d401d250421020191802074101c20341050030044c1c40902a079807442d540703002007031440031054000c60110b41090380f01c610000c2035214502d6400346000c42031001d500c5580104a1101c0f8900000e0310107100d844005003850f00446000241044001c098107645642d04d000902c1500301d40c42c0c01c0015400d210204080052520074801036410040541102035040490f40c005411f9a4200e40450b03541403040113410350321031028200a6005480c030f05d5480700c8010741e01c01220b40040c500301a220382402014042d44840d25015444903411955a40d260724080050390040301e20385004102c2140040c3c031004084103c0060607601388035031002e250301910794040100b10b0100302c030b558441c0c0110340c4803075011880d0325500c001058003440d5014508400c07985 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 821203165 1250 821201915 821201923
    0x5150901021315030b2d030109020d0206070305070f1101110627010f06060503090d031416020a020a09020d0b0102011107081c0f14010605030601020a030e01141209190c03081803 78
    0x11152555210140410a140451840b00c401a8001f00c00030050505241d00048444c68820b1029004880c081a180c2c10180100100c0ea64a40c01c411030f28440b248516011020201c0000514002a4112001c2610141c0020300714090414152094801600d018882c801c902c8807240c43c00c4690b4035000c0e6100301808621400000e01129a1015560701c2c041c0c000f14544152114440201850000b8420700305800081e025045203800114a024550003c0c08030318209218002942c070200207040064081001c1d8000d16120401c843e05000700b2003400b0040e4200e5010102e41c3d0041d01c81004a440051407070f20086c1490350312200340c00c0c0082a0750b00d4040880360802106640d49989408607040c14010102d0789006000a2820628500c1c158000035102e0300340910003004d01c103040340381d0343e016030282c50580384118980c020710342c45000c0e40042a10445094619090501070b0000c1d0310b50038440c1d0410031003055000311100480c0c9280d59141055580485030304280c0646480301a107003990280 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 821204415 1250 821203165 821203189
    0x2003041d010f0506030903160c180504030219020a0e0406060b0c150604090321020408190b07090b0a080910061d010e150d0204140405150901021315030b 67
    0xc0d03008550706104400201402c90f070400d61040d2001d00030403032001c20001c2215440b15581c80c06240000c0c4c2803400c0d45600626070010440c0f00b04009011813070002c2540800c1c0f045011360b00b00c541c0c08614400307520102480d01c1019402c136400d0007041c0032219608004540262107a0000075400d5030394141d040307858005000d0869150050160b15400c0c824511400307800c100100d0701048a154a60703406819621140c0300140309000e090903403070310304c80d06905840c000c007850015180b1b4040a441e2512583d0035080d401c54103081030300040b0703a46510501c0e541065555198031245080c036840c0064640140c024808003440c852015030042d802d2582c00b8840c000c142c12150b110026104105a480051050f080042030240b12810000c40c1c07400f40c88c4407143c954055801300394a604900119000e40b08800b02503a0b244101400d02081100010710340d4090300074101c0e4412151100c81d02c80b800d0b40309801d610099000041014400c8050031307005d50380b00843c01e080001d17a03132040341c020603440c4041e4 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 821205665 1250 821204415 821204459
    0xd1416030c03020106091406100c08031e0a050c07030c050a120c15090201090b090a1e061b050a02370f0807122301020c0601050f10200304 61
    0x800384001c1010380900615015080210050240e450180e00700d90700000000c0c2040c0c42040030211298005000307031003000141c1c5e040720b00075649243c82082a030a566032901441c41070301d01c000010f000c2100030301c0745038001c104050025180c9482e0340c4045940302a03140c002e03580e9004000407440000c095103075000280044c1e48270310b401c01081e410300c0c412608003000c8124000c6d003049507580050f83d02c91200d034156644406004e4480c040300011500e04503041c6c0017055002c0d44030315507190000c511a0100d04540540c0d483c120070060701d6403c040c010781c200e00e008051381e000c034031781c00014a40010b0001d00c15030708100359115412070340ac04002c0c0140b51b240321040070403016024452131070603540200141c44114010501e0901c0c1c40c080d00000c0f00c81c0d010190011088ad001c2c4851507001c1540c8018040010b0002d41d2205000f0952649958082c81001d01c212070410402d111801c084c06483e41080b0542c80360b00784d110925541003c1d48000e00c5940030180000c00000c41c240145008a510008a0f = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 821206915 1250 821205665 821205677
    0x907120506061e031e0c09150f0114121504180323031602030c07060806041512020111030904020d1a01090f180906020c030315060c0d141603 62
    0x182c1c06000200c4000103609003d030888000850103038074009002c0d5030b48603120000d0070112404a80c0103060804800000b0340c0b00c085031b400e0108013028681e524402180c1202c1b520b0300b9586101c0196112207a1400122440b50141302800d0a081d803224465031000c0f11a00c01c0140ca01b613017000234122007840c0c0c2d45841c1018206524402c0c141d2114018030404a101c2c2840742441d200c5140065500001f0241003501e07090f4a1644842071081c0151428054404100d0b00b1490700d440c40545550002c0300c2d0540560304d445201e4a1101e4820319100441da00d1031155030a01e1403940044078807103400396014507207120800038000c854599200910481c1910301740020031703000c0300100282c88000c421450b41004050002408090701d81003602e41104d00c44001d00c1c40e294051103014015001004024000745e101041ca1800d41d0b10100045105090301000d211f0280030030810005940101441c8511940c045048070200b28011599003c510356800440c0d030504400c08420050100c0c021011000118 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 821208165 1250 821206915 821206921
    0x6020d091505070507080304020307050a0b12060406060e0103180c0b18100818070e161e08011a040306020705010204030506090c0915012304230a0302090907120506 72
    0x6118680350700240d104a0140603604001500901c103005010000d01030b1040040840c08641e070810941e0020107014214415582d503400080c141130b04024049081005030b980090341914181c8a51416103e458403042c4a001007180110020311400f501464068070502540000c20b0311420310000a00c04038219a03601c500c09078001500d03039102841c032400340f07401c807844c03c030b074584c0088006502c9480c030034514041ca01030824403807804440b584152030510b140750074031044100d0448119a801080d480704680b03804042e0814540d2002c0100701800200c0d01001480000c8074451500c80c120601101281050307129100c0c075080303a1014808643d1360f0350020b010420006d041c802c06a10900350341c050540040d5400110740b01d10001444084c1065000e03110881c60f030f000760b00d142000341241204020303589144c0e81c04030155129001c0c42c1140c800c107040071022406014181556108081c11001180b80b40d0340c00d0044000e40a46000c5003405902c0c008039140e200d1800050074140980000c0090b0b003 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 821209415 1250 821208165 821208173
    0x2150a02040f0603110d05060d170403140303040c0e0703020702030123010e010e0a021b06070819110d0513150b010806121b040f060612050f160c0f06020d09 69
    0x14000d9401407007450700340302041c0440560001500c20a0b0175031a00030940d0798408c030002c2c0c0c2d2243c1c58140200351880c27030204080304020002c06031082d2442595000c80001c40404078a507031b800120f6000b4000302c036041c014000400d45090341900701810f41805070604400b5070007c2c1c25105d81001000c020241030014418412040c08a240144034070107801103a941403a222080c8480c0043c080c24030a5000a54064865040648c01c0b1841d9028420f80d100e0b8104180010460b40d001c0d54560850003800e0304445580751617210380081030b1490412075203482c10001052024010044c00e485008140c52010700200307140c042091015044074000080448800001603c550006800305016640d11b1550450021000426112030070f5400c1c60700c00d82c5090840003d0103840300c0003200fa482414034400082c51a08000c01c0d189290100704180025590020309111000d0202c0704c91f40f444200d1b102180807207019180598100d030148030300e0100c4c2c10182e00c80505a82c0641c031030140031079940c2e41c2c000c140 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 821210665 1250 821209415 821209439
    0x40e04060b090105031b0310020705010c020d14070f020a03080703120e010c09030602031305010e0c1503070207150908070b030a180b2d0f060a060201060503030a050a02150a0204 78
    0x740c50115009007540d410302c808aa0b80320f014081005040102e461411150341c0d04000100c140d02481d40300303540d9040603150140c00b0b00307611803c8138050301c10007183c5400036000e815401303514213540031410706002c0107441c2c1807288096500c046c2d0b0041c0912a01001007000e910082c00818020b85039586030620300d4140074201c403843d40c40c0702c0302a4982100c00c82d0055009008200726900003902513160f0304c810841e01451102e86030014a05c1d071030607880c20980000420500503414085a107806000c2d407942107040c40b44030032203034000180c00205091001c195544d820104050b560302d403050103182c82e20f900c103207003108a400c000780e408000320400c880e1000ba8000e100512042c1081040c10350400d544109006030050154200320184104420300d0440306000305903a40240c00f42d490f0681415203a80540810944019010b011010b8010484a005002e0310013140d402500452600080c440201c465420100107142140030b140b0b8882d40c4100305a00e20b0b0b00a810a5500507642d0740b80c07450480113 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 821211915 1250 821210665 821210681
    0xd060305060916060302301905011a0a0c080c011b02030a0f030e030d15031a010602030702010e0402090d0302100c020f03071506080d0c1e02030a020d17040e0406 71
    0x2071540030540c007401c2e50452400f00c104490441c00d01580391202d8080899120948009500b140340508a0211202215001040c0140810402c90324503040071170000042d00c06c05d018400c07440e808090781112141b006801003d00d20154a004480c0b0340682d035541c220b940c0b2020307800d00680c3d1280c500004030f642035000c08022040e140011454985502405083d6244010360b0f50f06040d912480e80324150024401c4901c0120905010018000a031004555207010350000342c49502c0b1031160f44070310303002041909041c0c440540085040c114680d004446c01e4000081e0103410540070b0000100b142c403900e008c081d2107417194002d0a41c10031b0301c8590a003110003e84200d81194489071041041000100c11074640315040358441d01c2c48030b1070116160242c42ca81e8005a0244142c0710840c0b050f590112034107041e6445240700c100711302c01130a610a4840c000b030b007000c0d50641001910800614122811048040c03041c01282c0700c003a48003201c00b0031500268800721091000e9010081000324511448031 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 821213165 1250 821211915 821211931
    0x415030b060a02061501020717010204080d0203070c030f06180b060103450b100303091a040b0c1c031505030d0203031311090a02071202070b09040c0e060d06030506 72
    0x108040515500a41c0d0b40e074042c180217408403082100340801d901c203025400140c1118421031007008000c9a41c68002e6002e88100d401c0f500407413690030742c131510120440d050389803c00a80cd41ca207040d6128101c05880200e07003240e40c26135604448a01e88551040c190303066000710400500c51a101c000901512440e04480d0208204e19607021020741100305400e209021401007001000000b02c094844030028207000b0b080103071060708201c6030f2001110030324140c0b4402e646169005a9a003420b20780c02c0054084800000000c0c441440402400000b4101d0f80304020304070740c2200f800003200301ca140550b000000001e0340720700c4c0f54000002000d005100a010070340003041c1c9010501c9000b5100d020142c10711900710314400040003800503c6031040300580004120303507042e0421888560095104603002c80e5070001003ca84140d2900100e03488d0308035038403100f100740340090050401008000e1450030740140400104199400d44510015010906e40030800140700b50960420501d0000c000340110 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 821214415 1250 821213165 821213167
    0x705010807120615030c0e19150c050703050f070b0403110103240e010618031a18060c070308010b0c10180c0b04050f03060114040f060509070215131a0601030207080415030b06 77
    0x80c8c01000000790031003c6900c1280700c0140280c002d0f2003152081003855002c0c10b644111f010100903c040402e11440310a025403c503840903607100c100200300c5c05503110240c146030003422081c2007540290001024448aa82e07042e0884d102c108002d0703030a00c140d8000d0030b0604202c40040c0012500302d000c04074800d240da803180781c00503d10341d111895001e0400700100010001c3c404900c500c040c840325800007002443c180d8991380751041e032849483e00034581c00d9000070740250000038980801411039144040000181980c0d60114081d075014007031540d030034510700c0b14a81d0309502048078804040040c100c2c51011a640318540300c2000f11740340d480207a1034481e41081004200340c91604010910080f01a03e0104003000012004401416030b54006500320842100b00841107074049149003900c10101034000c46906d4401c0c04d855080c81d12000240402c2055084034456000804a29031000701450090301c0c00d800e50b6590001d0303800a80c8000f420608520b4031161107a00341c000c401c081201642c0d01 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 821215665 1250 821214415 821214439
    0x6041107081608040b0301080d1805090609092814010b1828090201111b0105131e090c05160f05070b0c0304030201110705010807120615030c0e 63
    0xe41e0341403240d800c0c8203000103108521502004450016100203004503002c8649a603900c0003003641301c1c007800c00ca101c0000e130043c180240207170940010509131907015010120b15558041840521080a0401c45042c42400d440b000700300c2c6005407004503050501c0c0000f504032018a0010800030021002c02d801c0d9040004603c000d85424030300d01d000009a4000060326191424240203441d42c41140c40f10302620f407800214540620b8100100341031003a80e0b9280c00b85c3e0f50360b40c00b5843d03601050001d240d10321000116040d80d0702c510b015080c0f03400c119850b540031a80e10103488018070484a4840c605d04800907081145407058841da400341c200c00e04205203092440540f500110120f504001e1005000d20b02250600200b000084d01410b120b620075560b0b180700b0401710b1b503030b81c00c1031204034000381c0480040c950145020440c4c004640040e1604605511140803e4802103030780b140c6401450399076140004c0303040741c10714040c10f803020513140000ea1180d00c03607006049000100000f4065440f11041c = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 821216915 1250 821215665 821215673
    0x905040b070c1410020711090c030703020702031014010e0a020a09051005090306040819020a02030a02010e2809050a0b10030513231e0709150e07030506041107 70
    0x290355449500e0b481c1c0180380400d1890314040702c4041c07802e07a1a252160a0480b02619295401003510a020b80302010380d1750426405c010259070121500c40500109102040307280c2d000c0c2e00a0091288000c041e142c00e01004840030b07044910160802030320480340001003000ca42a48440e0360402441c450541c900171103a0b030003400550785885003d016920f400e949003c814403038800e880340130f14000d0136606c0904090a1084e5280c0200c114007882c03450740011103580794000181c0032010380e4064050001016181c00540e2019505030105400000449025010000c0c00700908140d42e03610301c00050351402c1107a0402141c100609020301a80b070039600220725a1075100c080700e450380c0d03490b01017665030b5080940b9141c0d030b000040042c50b441e60108500e140054044144171901507100442d040044694460b0501002405d804c4807190012441800b100c0c807039030001410301c01060000003005039605280010007008595980c00250f480080c00990324260003030491240c082071180e0300b4120341c2d440e = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 821218165 1250 821216915 821216933
    0x21f020c061606020307020705190f0506090d051002130e07050306040e070b131715010b090d0b07030b0f010509031213030f0c032a12050c190f090504 66
    0x115440c490000032400c0c01c10600b400c001c140034507900c41c1e410b549a0609a81c065502c400350b00034288100c3c1058031010362081101b034001c0845000d6030700c04d1074584c9003009000b0360b980a002e4403030b0040b045001448c04644104040c0d6a05d00d1074000040e600e8240d802c84403401d4030140c100c801c1018441c0c1c00d00c41050307403140640340c00950803500000d8114048000a14000040d4041170708a10041101d0881c002004070b00000c8407250041160000c105001e419100d11002e04201e40d07810702500180201172655024202108000d007002d410b000d050b480d070302c140a600701c1c2c0420009865060030401c60030a0101c0d04480942030a195060444010000792a5a524400311240203004a0302010b12a8401c1900700255000804a0444112828200032012080c00240c40031090040051007499190f4042880c200c0f07500d030380041c47c50401d400344201e0b08810a050740d1501c0380c203512543d03681c1c4002c20b180460003401c084024951030459010b0758030100b1751150100e0f905e8282004081000c0e92 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 821219415 1250 821218165 821218183
    0x90c060a08100503070b12340212070b0103060b1206060d1712040314070f080901050d060f05180c1b07030605010e0105011b110f040902040203090307021f02 69
    0x4100080720760b55803a1220348000e095440560b040c801ca11000620141010040801049404409600d69a0b20707210442540e5a030481281d0079007603d06880314200c020380001e88620407032040d5062801c41c02841c1c2c420360450b1341e0540c3c0c0d00302090010401c1100d1072107110b12030503056982c52000080c0005840e04c03468014500d80c00b0341d504030001d01c20080b000754807501c140d00850355503465184200714150061400c0740c0032030202d0b1502c1448100c500303421003078070006a442010314003004801d81e201d1450b500300750052030510000b4045c502c10840d0721b019800181800c00e454a0846113480104114902030108120030a401003083c482c0720301034030040b0313150044c0d00700f83c6003403521501141e146080d002d5070000c3d00c5d07140741c240085543c032008000c49048500036a189030101043d8403e40030048043d02e0010044441001e088030541400e0500600851005000292203407170341e0040790031390740200d840c1c80054000040c0341c000c52812901c016007444501030182c0d11007500c240041d41d10010b072 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 821220665 1250 821219415 821219417
    0x30912032304050c0a08061603020f040503061920041e0302060d020d1b05120606160507030b070e03030d090501090f03030e0c0103020307050d2a17090c060a 69
    0x900d461410081c40d00d0201d2034a000700c0481c20385074030701420407540329140c94900a1103034800060000f00c1703800000d1000d008070301c4014800084030340400281c00075070041d20480300304001030000090942e028006507224175444102c000380301503903140c1d1000300c5c2d03217859032445049803401c8501e400750045400e5405603a40c0c400300c450401d0560003562200e03c410342c0002d42c82500040c0280c0451020b4000c0c03e403020304031a050054500c00044100203411295507000002c409000c181c0841e4420b0002c07a40014015018030f1900d25800d000c400081e4145a0a43c0c5640c4040b10400070007444c00d1245a00100c0c1d23251070b084105c4810300003034480c852407425405542e00c9000c0f83c030600500f035100c240080d030300070301507181d07401c4a03c0c000e40a080c080c2203180b968050180d180c00154004c2c001c4038420741d1507981d010718040c0790b06886c80003080340e0400143c075400b0034402c0914415500264444c0407030b140d200d004944a2148400101b2040142001131640203500c010040c1d80700c1009552200000e = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 821221915 1250 821220665 821220671
    0x9030201050c0115030f05010501050d030f0302090a170717120406120f09061b0804030e04410c0a080c2512020114010815040c0915050406050103091203 67
    0x602000c0b81c05002c4010503d2034401035450000100582c04610140d203a11400c000d10260ba41e80c000c11a201440d140301402180010f5100c2c40090f100e68020403411400400c0701c104962034807080850810100e0b0162000e600c40380051148906220000d40740035141c5000705030785155441d01007081e000318803414082c41983d18941020304095001150100002d4008100d00d491504100c2c001d0b050303650051007072595005c4d403002d44d03501ca510702c1c0d440b9640649503070403020031520610004061400c41e0302c107007240b085140300b02544000314650405601c18a0745c0780d2a015000f61505410005d0444008888d040060009050700151600e6001c805081d169444100d10b05450b101c0325010054807c2d400201e10a08040001c0c00700124408111540204500400b86020204594003802260150341c85901070007618541c861030035600c94032503034030b411071190348001c42419240c0b11016010301800c03440c4140810b007020300c03840008010928060289050645a1542d00e82c031780a81d0307808041d2 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 821223021 1106 821221915 821221927
    0x31e030605090a05130b0a0b03191713150e1c3c051e061b03040b0612030f0a09030b0c0720030a06050403021f05070903020105 56
    0x201c411117501c1010144c0d183d4064086000b48030714101ca450714146078403920140500c081c1840c5900c0c2c6401e40c6c0c040b914010304017170f0124054902904050200841865a00100f0400c4822185040840e0141c0c00000c40c1c51070501c00c44503400009900002001008030542c2207646030045250b403851122060400c15142c41c0c0c004440c01881e900e680c1034190312001c900e0000480d01c688102d60030342003621700c00c60b400022081c2c1c4490f2030700300404105500400d2100c400d403101c0c01018482c590300d451780e141d000b00310000d48082d000e80707032206080250000400031580c10880d00324000d42c0310350300d00034010819a0980811200d04110030b01091040c241001611103040e031180543c0305803202c10110140800800308050b81c14490406504040f600a2199600490090380607024852040203a0180a900c002c6103495152801c000c014000b46d008200c2c0080c3d81e030900c0d09550354a = true := by decide +kernel

theorem cover : BRFrame.Cov 821043165 821223021 := by
  have h0 := BRFrame.cov_init 821043165
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821043165 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821043165 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821043165 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821043165 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821043165 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821043165 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821043165 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821043165 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821043165 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821043165 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821043165 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821043165 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821043165 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821043165 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821043165 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821043165 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821043165 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821043165 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821043165 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821043165 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821043165 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821043165 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821043165 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821043165 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821043165 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821043165 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821043165 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821043165 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821043165 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821043165 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821043165 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821043165 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821043165 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821043165 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821043165 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821043165 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821043165 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821043165 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821043165 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821043165 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821043165 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821043165 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821043165 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821043165 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821043165 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821043165 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821043165 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821043165 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821043165 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821043165 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821043165 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821043165 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821043165 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821043165 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821043165 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821043165 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821043165 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821043165 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821043165 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821043165 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821043165 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821043165 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821043165 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821043165 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821043165 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821043165 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821043165 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821043165 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821043165 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821043165 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821043165 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821043165 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821043165 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821043165 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821043165 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821043165 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821043165 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821043165 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821043165 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821043165 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821043165 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821043165 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821043165 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821043165 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821043165 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821043165 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821043165 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821043165 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821043165 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821043165 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821043165 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821043165 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821043165 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821043165 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821043165 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821043165 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821043165 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821043165 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821043165 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821043165 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821043165 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821043165 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821043165 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821043165 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821043165 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821043165 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821043165 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821043165 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821043165 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821043165 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821043165 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821043165 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821043165 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821043165 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821043165 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821043165 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821043165 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821043165 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821043165 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821043165 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821043165 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821043165 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821043165 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821043165 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821043165 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821043165 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821043165 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821043165 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821043165 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821043165 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821043165 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821043165 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821043165 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821043165 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821043165 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821043165 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821043165 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821043165 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821043165 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821043165 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821043165 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821043165 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821043165 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821043165 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 821043165 ≤ n) (h2 : n < 821223021) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
