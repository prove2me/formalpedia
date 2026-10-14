-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1137
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T01:24:16.165329+00:00
-- url     : https://prove2.me/submissions/a7d2c574-a197-4bed-920a-50761c762d84

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 204316546 ≤ n < 204496402 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 204317796 1250 204316546 204316549
    0xa0e1f030b18030307080a1a0a06030c1103070b0105010819090f0615081b010507060f09170309030406031d072d0e06010c0507092a1d09060604090509030901020c 71
    0x81e85d00030f118503a90399015807515905400500711910040f001c2600c80a403990032951032588000c01010540c60105104c10851000350009601c1000b03c0e07001d820030080c1000050007820058152142401c002c0340c2c545601c50652031a00300304105507402450301d220031040c8400c00c0c40c8405150303c900824414405040c1c2c0c00251a2411301c90354419a001c51000440c0411800804048000c1854000d0408016440740c6084d255803643d415902a40d0300017480600c6980c08009a0382c01000381c42c2455070800b922155a60300c2390b40304180070140d80d50703050800241921941e4084508050480341056103440085680742e070a4614101d0f040032074845420800d69282404e401c40307800114412040e0b032500c0064459003114002280e072801466400315494100b4031443e100388112240d14082c0e85032044c40b440b00030543c0310001082c4006440d0740000c000c40d0100b80c4010a105aa0300d2146844400c08964140920341211510901b02010405075100c0000a848020006d03401c44045030002e40 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 204319046 1250 204317796 204317803
    0x2060301290703080615120610020a051b030d02070b0f03220b0601080907030c05040b01050c0604030206060901060806090601030c14040b22080a06022508030906090304050a0e1f030b18 81
    0x150405201f61054000f4040780b6013544040a0940303140140c8800c64000c0d9102410008806030301c640f0400fa00c0380c422000d0804100e8032191413006d0005100090800c65400158010010100256840000000d0360455240c0c62101700890040c4020400d030f100e8030703081c0100e420444071380340011304c4140028150000007602504494000e480101c1e001c0c20321046c0000f9003815080f4078181300341046010f03038141042000c6407040340070303601400d00d0f0304003101002040c6006078040403c108a2806129542e52080e409a8204409080028107181811815a40e40e01103841e2180300d0840824001b4041e100344006241c0400115800c03e05410702c04a0000c1c0200a8001c0c00642c3d440808843d000a865070b000f0134441044600042c0d541e42d6442c036000c2c0c40100100c0c1100d0010f0040280900f40d0802c0000c00d0b00803040788003540c00c2c141041c3c08120641d650b84200c212101c11030f0302003100c0c5d050b0814104034111800303040100b038a441e070400142d000002c0e41c2c1e146100e0104e242c1002e0400010 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 204320296 1250 204319046 204319057
    0x20d06021e130506030c0f04061d0102010204050a15020a0b010f1a120c0309010f020318010f1a0d060605040221131e140d0806010212030402060301290703080615 71
    0x2c141040e04074144801c2c000260402002904086400c015a1078102180030140005040baa607844488070f064514969014041e4161941503a005000c144255919640341200f9500843e407041e0b91041030400032490000d182c4006000c001040c0004200720203141807150560309085182450198484c82e80b2505100e1591b400311705d0100200400c4618006600840c2c0112150001141260655031000102e92054560035401c0d190086035495010342030095401507500208200321000300070403c0000d2800d001c805900c41c0244d800f40c81d0400030b03d684414064040500215141c0104501050700c00c4803044e084105951a10300050320503050400c1c2c003000755440600034a4041c800c202801094104500443e0b18554860602a0001c0e08020a0030901d18071743d542d0002d0b0a02c01c002905019416903840941d640030010803000d038030703000c00700c0741181c5070308150f03000041002e0048c9409480a188500418000041200078903500400b511300a00c4d00311040f820080d2a06026225441035 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 204321546 1250 204320296 204320317
    0x10812040e010b0c0f01050a021e07030206010302270118060b03010807051009082407030b03190309030c1e0e040f14031c0f050c12040b090307020d06021e 68
    0x1071400602884500201800806500c18120380480b440506a0380c2510012510038002c10780c04500c42c8003900418542c50398aa1900401c0c40c0340c0046c07070714000e44640301400040c0c00385c407186e11201c1d4120300b82c0c00c2090b10703483e6803200e405140d616044110090200f0035807a000440c2404400300c0d502403c04103e03412105030800070a0901d02d004c040c4075810100754580010300c844010b0004004100780035401264528102840c2c0300f0700700900b55129040094015402c140c6415104880c1e610001035100c1900140013000840d03035000c0c60201c0d0600d06d213400003048004c11400008180f00107900d4100c4501c1319070b140c012016225000000c0c50b101c119009820304c500b0902d04400b2564030348061700c5490120065074640003400c000c8982d0011007100600c1d900e6958180304160a0b00b900c030341e076042070b01d007500240350846131201340340c5001010f040640051451310114a844004108841a480e8050003d00001d80380f4102140250400800e8191b41030b01584080b14000d40601150402070700d = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 204322796 1250 204321546 204321569
    0x1202030c09070c0311070b040e0402130c0906270b190215010b070c0b040605090405091902150c12030402090601110d0e030a0c030f020a0605070209060906010507120801081204 77
    0x282c0d00c0459060f40045c107042514028030102050003e50f01b00107102030031f452007201c0654181441403010390748281351003041d0382786007001119205034800c004004540303051500c140c2040c00c1c7c07000c100002440220503828800c45000003e101c1c80480302070081440d08d00010905a100648180d844180c90718100f0b04091000340140045445640039100d00d5000c0c3c05840d500c19180e1110780143da0140d049240030135004101c0320b2880c9090301827158002d03040d001502c900301c148001031140c10100d81e00284180c2c5558410103c1c9401d28040da81560404001c90b030200180c104034140380e600540b016402084008006025940514044000c044005c4010900044440011640c0d00301c10026107a2502440c00c280c000b141c01841100041c43c0150b00c40b0901110300e00c10444010040e81c041005c2c0312003845024091383e12441d4490b40301d00141c0305280c2940e107410040301c051181080041ca60711000140074034840e8403d0903a0305072901e04044507100308607a02c8003030050280d0f1007068007c3c02c = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 204324046 1250 204322796 204322817
    0xa0503040501030507033e0f18130c0507020a0503150a0b040e03130905010e220f0f0b090601090b060414010504050a03110108100e0f04110a1202030c0907 68
    0x511030340c419a4017000624000070b00140700100007808a100c8940301950310401040c102c00704020326409041340c0e1035107402c1494040d80c103003006554081c40c00305100c0c600d8418000d0b80b00d0341341c66041034500c8107184d108108071080d00b000a07106c1c0d04810820b0740a280000c0000ca62802c00240d80d14265076001d00c044410f55039041084050031064050540058917811001c00103141003000e002ca40e90345100c1c1e000b843d402c29002200721801684200d01c1c21000e08140526040d0f0030004110010400c0d40018081101d07003000620a15041c000510407580805480e0502298030315050059032600305454603a40c0cbc40b40c1c3c41e000c1e19010080d036544100b0400080141c64401500c50228a506041080c10140d40d600080c02c0b1074503551080d211200940c090702d1a961f486200554407100000e80c4115960900700402d141c400014802802141624046003c0c819025102d102c2c14200501c3c90500030380f18038201d10100c03c4100100c0c00ba124081100b03100e480d2950345203121b41c115030384819502 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 204325296 1250 204324046 204324049
    0x80c0103050c072003010207031716080f220503070209010602210306040902061308160303120c030603120e1314060112090b0a0624120b03010f0c03060303110a05030405 74
    0x5807000c11500c0740c4226200041407417618280041d005003401390320790f5684100901c401421072280207208500e004010000046410f80060b80d480c1c201422600359041940c401c0b1406204074402190600b01c2d03d9900d444500f0007000100400d0145d20955492040743d07aa00c4d0280d0b680c030200c0403c0100d0080648528040c00c104d140956440783c80240041401ca1a9802160090f800040c6005050049136014020800200304000d5a011140400305130310345141c800501001c007026003501c50a8a62211240251094020340051600860003212070070480c074001d410310440c1406103008602240203030403800c11134800c5202c040c00195150b4510380d5000c0044a0081010191a100541d50030856021440d915540b512500c40824001015403c04009040d2006c0004110041c07514081c1421411644641c491642003c29140440c40c03600381d400003400341400900004003e0f180100c007964080d450740014046a0080e11484141801408000d45503081c80c100500a540200810800c6 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 204326546 1250 204325296 204325313
    0x3060106030b01020309090f0103050708030306060306010818150a0f05010b0f0c24010905090318090c07060509100b0105070c0312110f01051807050319050102040b0c07080c0103050c07 81
    0x10742051041c5c0c0e240900c0300e400601c1c40c12042c1d400c104540b5860005004101d020007062000d0300343d2100460840c60030b0b02c005111071200070a141d0403c04220b000c00c8411101100e501e0503800c030207082d0f4584015005002141001c00c071002d4503044d040c0307804640588900c2c80b0b001c1c141e60011219500e8044003c00005017a807114411083c036100e40e0502ca100c8140c034140a02c0e1111503c60806140c0d45403880f60380c20340704050700f5004c2c0c1d500104140d81501580c13480a0180403000d0341d4001580d82e4281c810703010741c09100c801818040c00c210410602c3d100c081607100310610b07461002c0104580e45001150f40d4040d0000082c80740d40b62840034408912040708c400c4030407005141024001c0c04001010342486100e82ca010010381d110301c1400407144000fa003403d01844084018030480c1d01c0d16000958806c40590320301d0100224014000c20302c1400e40458015000303079100980e5801041d0b2000e42d03a0300d0903126804d03079030103041c9022620f907200e401094000e490b0300140c14200b14058540110 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 204327796 1250 204326546 204326561
    0xa05030705120708032803050f0406050702010f0c0509150301050607080d0f09031206060809190501021b060711030a0e0f04090507060c030809010b100807090e010308270306010603 79
    0x110710030140009032078130f001c100401480306010081d00920940404414005d03403224154010f05083c401040030780800e0a840f0365000340c020b68040744580340c2c0c0c0c1c0c00380c2c01030039213040300b40c1c41c503040c40c4514640d140c0210047c00c00c46400d94010b280b24484040c08046030200380280c0307902450030040700000c204000040d10004404c0c0e100044c1e401100700403403048407240c2e88114040b0b43c10340300c4014086040d101b100000e00c0d40c3d0900240c0c40c6040401551290b10a5244101c202402090102070040c258151317a060b40b01c202d00c10364680801413120740c0d1781008581c01d10000d07015102c04a0681c00c0031040d5412650140c58020059004404010351a03400000d5560829070b21302a0001003602084680d0041446844801c5c040500781001400032000518001660703042c03801c403202a484407aa00040310009290142e02d41d20f07040d00480300308109500ca0045580e5101c0007005011402000b8551601c002858140c003000403081c1c0302c5042c407194061540b41e0000c000400c1403070701a030031200 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 204329046 1250 204327796 204327829
    0x4030213052503060e1815040c210602030c03090708010c05090d020d020d0602091504080309060a1e020106090f1505060d0e07080d020f03040308070807140109050a030e0a05030705 79
    0x11201c0d205d407030748205507000b180c0901088007081c0b01400b078598280490410415407441d51004c529141c2c132400480d1041c2e2040f07600e90035240c00a04c055040c040c0040c1c00941e4050300035580c0381010300815181d41c0040d62001da45004442d000150280d052041c81c0c0382006c2900c80c1420b01c0030220403c00c6032205d03808143d801074008140e20340140d440106c0003452510641c0c006844005c40030611140001c041d02140320201f0411090118013030000c181c40c00c89004071100380e40d8441030361044588600140c4228810321780c602ca0300d100140c06410920a4851040c004c001c04482e821034a0190307001100b445402d00d41003e0184001d0910000601c10091940b00109010f40325822003481c16605604c070721055001482c0c2403080a03414880b030a1078444e1003005600305030540d129800030b4070991400070800280003518108215030101e45411300c481c21402049152072609105442c0e040703044088001401103920a4070b83d1078000004000d8802c0940241052400d290510a070000c180c649003 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 204330296 1250 204329046 204329051
    0x513020408060901050103031103210c0f0d05150d11010c1110031b0f14090d0c0803030411040e070504020c03071403040602010606021b0f0d0804090204030213052503 73
    0xc00c09040402c03069010b00380003000015150f01d5410020190381c082c00070501142c00c00c2010101c003071822403100380c0d4800c0f082400c01280c0c88071140c4400a10400b046942841c1e000300d40c0e0640e28081d6405607216100000170301040c00107803400c000d40351b102075000406982c002413400f490381d40300714408030259121709007401c450788007080080e8035840118081d4000985175101e40d46200d240750a032102001030740c02d20200d81001440003500d07108600e004844188004110840c450341c030380102403401ca4110a41058042c1c84001854480d4401c84003139455590350b040d468080d06007889813210191118021702565410034003004060340c0140d04420241c4802d220080100c1d9044c1d280c6046000c40c2c5c001540e0391032420201a0035505560303c04029034024031441e2412080d80c01c0400705980c011600d0390100f0500ca4001010b1240c005400741180c040814049800c030700a84c02042940d00850f11940c440c4032101d180d130290b4604880d0302207110084400b82108030712020041040c9090360402 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 204331546 1250 204330296 204330299
    0x1806090c09020f0405041a03030304140a08131e0828120207060f0203032a0c060a020901020f0106080d08040503160501050f06090603070501050a0201140a0219050a0905130204 77
    0x400690304000024444100f000404104c145454403072552201a030301ea019894005140010740c0700d000040c00500750038105c084d40e02030070b0401d00c802c1c0c41c2c0c0b9501201003a1641440048010705840301e0103508002c0c0c00c200d0260b0010111102c00070304480d4024001d0060140402148039080b55162400d00d4070580c905d06038002560401c10540c1c024102d5008004040ca84000100b865035206180000d6400400038001c5001f44104400e00603400e50660a8800360714903000200c600c22005899581e000c0c03c014440021115001812a0700d000d90071195009400c0c0c00007401c85034284150780e41c940c0f10080c0810164010f100159000b4044c406403420b00c203070250725040b900d230140e07003c0326239941d50800c1103101e80394280035035040481a00e22156615105020aa0391241c40c090760703060100200300414410301c00d400005842c07462816100c070609064180c0c034080c4d0068101211418490070a100603541700c3c0d003e40c0d01d140318540c0c8010080f4900000d004e042401400800f84081e002c100 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 204332796 1250 204331546 204331559
    0x120115050403141c09030b280c0e19061b02010201021308070f0906050f0108061c0f05060901050f040f030e04020a08150108010501050a030f061a071202011806090c 72
    0x222410f0030010400038000b8465090700741c44080d01d80640900070f010100c3c1d814030104000d2584542d0007100c6c0503800c22140c04114203400480f1561040c8004c8900b0450364070000796201c1c0102510040544010689102d18000e00789041030303038014000019011580b015402a801100074210303801030000520306203090342091115881a00640007540c8141400c0011406a480020007408039040800009080c4000074a0100240d00711a041103440300c081049651204041d5103c59905422001010041c1c80e0094091001100c01d60351401034400140c07a07682d040c021f051040084040c14070321644e60769500a6680070703204059041088136074909050b40c036680300a00100301030ba1901401c03454000300c0540264118514941040328480041102d071340c03c08141e58018205090114170030080040d10030060a8030f44c00075225000c400f41e4132908084038001403050742d01a001100550350b000d0400e0f402c0c1d4400d82d2400403215110340428001c1501759004074400c07840b950200340003641c0d0704c0 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 204334046 1250 204332796 204332813
    0xe010c0213021b060903090a0501030b01030f0501091d07150f0201020f03010b1b011103011a0c070306150905040f03031a0901140f0d0206040509100b0c0d080c120115050403 76
    0x180203c3c4406103030800c05010f0400c002d043d40c00083c441c001d41c5065121b0011403040000c48c440d0303605058503200604403580c0603400000d00021182c0080215607940d61107500600707001c00300d0105100c1107140c00300d4014000300d007403419030700341070009040b04181c044101da071200c800c415001155828490325240d80c15410056000380401006a03480302e82d00803406c80c0c8842d000032010410381c508107401c0d007100340032130650341150301e80032105240c0c5140a020101503c1040411100c40c01512004007c01040346e2101d010001e40e81c800302d4501da00c0f01c400741c0440c0d805031400b4050028603912400068403c3e000f40c803100c0d15450021000c40143d42c08110902020b130003060049039110034006d103a042030010800d1001080300c0c00001c0031101e0f001300c0c019110f14012140540b8409001130b8036030850203c40300c0104554144c441c1c6da100c0040105482c3c00742c103180300001482a00101d00b800090000f65003400da92004480308503440e01c0001c5c1142c5100c244080140041440b000000c1241035 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 204335296 1250 204334046 204334057
    0x30d0818010510140d031e030b040207082203050c0d03030207050613031e120c0c021804050601170c10030e0d020a0b090607050a080a060f14010f0f0e010c021302 71
    0x1590f080015410000c481985071030300340100380241c9542e004030011940c0a0410090000030b6010b00e891881da29404402500e514100c0c55040343c0001114420007142400030244400e4400c440f8020f00e4800c0005c2c0303084441d6110140c000d86c0100030b0b0307280c0d82c42c1801500300503034404c2c2801071604c10156941420201d00300c68207032450001c00242010701d6003041d1103006905461041841d0004101e4004d03015100c0703602c0c217190f00b541c1e9000b8a89200c1c000c00500300043d40041107200c001d40c0582074041c0041d002c40d802c071800d000b000300001d80c1c1d6100c4a070810303991280c41c0280083c0074040092008190001e942c131380425854901d9075540020500c40c40345a0b05081d4007405041c2c9040c10710240490014154840c10392082c1d04105900b03134007038203845074030b00e10346041c0500780c40e00d52440b406481660841ca90381061480e0000341508800a6940a40c0080c0c8a0021840d40d094086c3c543e900e41500c2c41c4c0219490071340d143c0740d96208500b01082c0610080c000710764072048050910807038016 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 204336546 1250 204335296 204335311
    0x180c181f081b030f0a0803131b03050706030908040b091f020a06050f0403050a0c050705040f020d180c050609010201110c03030405070b09010c12030e010f0501140609030d08180105 79
    0x160008100c600302c2840c2c030040d081d00104150401841035075a142c426000140924002101142000c0c048201d221841a0013011482402c16600420080603500703120480d00d03841000c00001c0d000340203006840c41d160304220b02038182450318410035247c4d40025140f40c2c0c8450009400941500717000700921071008550300921844031a0714101d42103c4000d080d184104094008000c0004c3c0d00c0400c41d10008468508041c0c00c0c1c01034038001d860031760180c010b55070081c101414001a45440d03400761680e500290000c0c042a401c880c440340c0365840840c4090070042c1110340c107001c00d06041c0300800782d404040c40000f908807060b4a15002c1c0e600704100201480c0c0000040c04144002000f481d070290400260f120f10301264000042c1560300c10321700c024079403602442d6031060745010303a1049100f010741e10700a0121184800e400c200619090103a2090101c404020785891f08048080c1e640d03010028008008075203c42c0c80c2590109801014810f0521040b90f040301c8022080c00307501c3c0905034 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 204337796 1250 204336546 204336553
    0x111030a0b0d12021b040b0f0d0302031201120c060e01020d0e0f060403060e061006080402091e07030c0815010504030f051f02090306060913030c03020c1008180c181f08 74
    0x80c5c0500c04180420344d1215902c20b03030800407011590303618840c920002c954100c565a160304140c0c601681580142c80302c180782d00300034100000d0203400505508200920513000001040e40f40c070800e88000722055410760060307102c920728920550013030071082046000100a608111180400241c3c43e40c4150021160103440e4003040e070401c442002010b80140d40038400c00d00e0982480310080400a0040020340318100907004124002d228036405040302c42e4081d0982c809161048015000e0302021440c0c20010360032000107030343c413003aa06086e00c00e0b28059607800e00e45172442d12102040160643c043d20a4040e8461040401001203035940400000900160311990000200341c2050001015140500c84c15402c2287c200304c030300350040c10290b050412070152595070a04070304d030a985041c943c2c4c20400c00030b00780d800a40c01c0301031544151021809014803c0103514016182c4c40d01008003604030b40d0001280314800782d2035074001d5121400c142c084000070464407001030b0580066228084e03d40 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 204339046 1250 204337796 204337813
    0x1c230606010503130221030f180901050312221d010609150c08040509130c050a050109050d050f100e010515030a0b07050706091101180e01060311090405010f080d020111030a0b0d1202 80
    0xca0790710800884020ad455464561409001c40c0d04c4885002d1112042c2000180a0580c04a081810f102141c58845001000d688441c000c180c1e201080c1c000300c00c84895000001180c0c0c0c810055141039a43e260103100101d10701c0e0800f61114000424103d07454141400046100c1e1100242e4a205448080207038420b0091400e010b1000e40071078001724040c000c40c240c14090b0340d0300803500200b00d44007034480441c81c4034207040880c100484042040c00c64000c1d044a02d409159035000415001001d00080109032074282c1c2010921b10075091058140d0400c241240c045800381d2480fa500003100d05245240150640e281021602540822901c154002d8806500c0b540c1c041142c040103008855070741c0030b2034107041f051140c03144144907803001c00d501c40c0b1701028104410000d407004400050800e100d1355071a03080f05080b001440c0030744902c0d8411403981c0e010301d500c140242d5001c665215019451070302c500c2d9130800034242c000c2c0c80b69000b4a08001070b40004a0034503d01400140e02c0e4098455072 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 204340296 1250 204339046 204339067
    0x80d050306090f01050136030b091603021513030b040b1e1009020f0d0f09050c1005030103020409020d0203032b0e07051c230606010503130221030f 65
    0x1031005001c580185860f00010310603640c1101c10641c00d0608451165940005004050b24494058134404080d4080103000000c0000c0c0c100403600030300030403060325684007200c005001461518480694440340c5081c5101c2c07510001e100501051070006001020240c5940351210118002d580c104c40701102d200c00c0102c0111150a012000410200b0507103032410001000348403000a0302408040c9940002e100d6008924681110100000e08009000f0012481008001803803034900a48640c0160760040406180044800c2c1d00304020792038140c20b48c0d00b180c0174080181200d000413a0424260b104140150358100041d01c4000c600030b0540036441070740541001007005500d0345101c0103042a2158100b62804160754050315825100200b65100350000d0b290130b43c505503400b6005600d1882158140003250307000520090a0404a03101516203600440341448101c450040d07415030502c0f42c2c80180b070805200205585081d01c071500c0c02c156250302c0782c1103501075801084a07101c0011145402c = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 204341546 1250 204340296 204340309
    0x1b03070b0604060620011b120606020d0507150908070803180f03040e0a02042d05011d21011802030601080109080a080403090906120b060a060219020307080d050306 72
    0xc4101540c00f030000e01e01c1c002c1c01400c030503010840c060700c556040081a00394002540300443c070081160541d4a0b0003000c0b50302500145411050303082c0c280c01c141d0301150480c000111807481017141d0b82c0312481c1c800561201102c0c070b0912004080c810b52580c1007880451107085c05042c505000c0c0031815540d09204800c950703031105081c000c0901d0b07003040a1142041d0804025102215100c000c0c00388995608583d42009105681240c005038134041c42e401480304962005404202c1428a010407450301c0303600640345454244a4200c2c500c0c00c13900303107003000d0401c0820281d48030b01c01d02400400c0c90500074150b0948000707441607004420390160030002c0d440d04004d03503801080c54100800c4a020035440c0d0400d03a21942061005020454020034105841045803a00510061600b000b00790b484408101c00303289104c805980401030079000c00c0d000e1400d15071800c2110826002000940e070205044030050344445000d991501403014006403101c4280100322482c1c0742940c2c1e159880c85e0034000c0060 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 204342796 1250 204341546 204341551
    0x114040b01030605011d010c02030303040507060909050118020d0b040921050306030316080708070b0123030a030e0415080102030906161718011a03010b01031802040e031b03070b 78
    0x40500f0310500300081d9070807820b030416004035002075424502c01140165061a40103c0080d014407000080000340000450071800341da100d6070742ea01c1501d6490b8170f20015600c080c025102c810f136612010100c00c4019a0040150038400340c0e0100c1c038580b00c6000a000c68012440a0317640e41d0902c146c000061203500412030320880745080190841c10000003181d0349020f16411038000044203000041800f0070b81c0140c451041d0301020266503a0120716141c443d0050a01c641050f0070308041a00c0181c8001030b040c005600030280041c0b045001d01d440803680d8032010b09103280c005a9482e001c902c0d880c80d9101420150404500150756800c1180c031a81c54428000c02e001104141e403100750000603400024004411410185628aa00c0c2c0031840700e200280c82c02891f15662900c1c141e1107041d2000c202858640f50220002c1090b803103084015026200c0070f103c0152280d000d0b0000c0740c014503141c0c0c401c1e4041c0c0124800c490409091001d80102050f03030004221040c2d04c04205202084170040d01e041d0b = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 204344046 1250 204342796 204342799
    0x60303080604020f0304080306060412060917090102030304030324030803062707080702100c0f021501060203090d06060b03070c061b140309010e070609080f010513031d0402030114040b 81
    0x18640901305408078450300010b4001041d00b1000404aa081e6031244151006400162588944e0b40218a05100180301c85101181c45010f00a8030701d104400c1002981c00c130034010b8018516642c1d807a81e00714010404000032001050240300440100800f070f02000005e14425541c181e52410158100714241c00c4c0111010110b02c0a0003402c0040c00300c000d216500803041f4208481d01d0b450b030343e60507420308220540c4681414601903026102e50307800003005017105d03205c0d000d4400c40d4a80310f81d1307086056024064003015a10400086010b070410312850425180205d03000a011601c03000900c04c190310950300341c40062410000c61040c0031240c0714141d0190f02c581e034125045912010086c00900c110b041d14140302d0700c0800060001c000039000400c00906030001c0e0f0b09410f0f102c8030081d101c24030301c0c0641002c0b0322510042c003041e0403051161500a2624141c0300251040540e0201c8499a2001c00c010740007130368104200395601c803400030354040c00d55086560300d4000c080c0240002c5030901106507 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 204345296 1250 204344046 204344051
    0x2180405010b0421150f0509010506100c0507080303070e0102100e060a1805010f050703150311091f060306060f02161809020d1b0509010b0904151503060303080604 72
    0x100300100680044074202c07a0ba40250a0010100c031070300749949031106001614444250010141c0e52401d1b500800d241107400c1c0d010025a207030310340d610303088800460fa45034210b1022800c440c40726010b42c0000034420301c14000c450400b40c480d8206802e6400994082000c00c0d504514071402d90b070148011605008003407000c00450032a40d02e281d9540344050407003138a4075550030841c00c01420b00b0354100b12542e0008020312110034000c99900090804851150000e0326011807100140c900c003107441c0440e41c1007145c02d0f44c44990f280401c14070802c00340ca543c00607600c1c25554420080780b8002032001b885076450014080c0d28088001c0c09028441040a00315003152183c01d1104541c1c007000300650320031000c240d4040d88000d40b010001c210702d0070b0182d03014520000140411102d008030001800e102c401c403459a0380d582041c404150000c0c081c82408070401c0c030515034035003001c1d84000400c60000758030011403a6100b0101da54520032002810000391a41c4040c414560000540c61b000310040c2c508 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 204346546 1250 204345296 204345299
    0x1202070e090d0e01030e030a020606010806010c1106160b01030b06030730030e060f1305043617070c0b04151101020f0f04031b0e0f180f010218040501 66
    0x1440c0c0c40b102a0b0314501d0a20402401e20011644a41d1180080f00d9110040702d68500007220041e50b10030084940c0c6c4d0000701c2c1c0300c0c0001c1c0f05500c900f8100201c2503100304203003850f001c1c5200300555074000c0507143c000f0f50b01c51801100072403201c1d80300c98006c50041c00070324064101030040c9406c2c0041a04801d090300c01410441c002d14801a07050a041c9181c0600d0750750a01c2245000c5502c9202c0480c59603200714041480540c040c4900c00502401c499041e0b88045190354400344000d9400714110300d4280c007040417001c01048610082c40700d450b00d640002031a00c1d0000d40d1282008031840c1c2d410031180b88003003894800c11020248400141801c0600301c0c2c1454506101941c2c002c0b02c01c5c0805080201106002c0d013020801d4060f500da121024200e6034403640c1d000180f400940013480251030000312544204050074240c00c0c020140d41c5520043c904a4ae5402c0d5542103000300a082201d9805040744000d41140042c00b000244c203100600140e510b5201025600c100c1033280b19191007646800c00 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 204347796 1250 204346546 204346561
    0x309051507020405070903320d02070e19050708010509071d120a0812070909090201080f420103060e0612030c03031e0c030426161202070e 61
    0x40d80e4000d0b50444001c103455075070f00c40840306a20244e100929484030310311207960a40d000f00303071002c04000300450040f5040e02c00c8820707542e4061085003140580c108002c10f100f1500040601ca0b40000038496504016407242021821214112020b00003c0c03080e000503c003500e01048078036000740c01450040240c070501400400c81185005034036100d049241082543e8110500c100c00310b071600100c2c140e03121481580507810100e000c441d07420000e42c0101c0e01194142043c45040784d240e4041c1d4400d03125a86000c3c401c4000400540840e00c40a06e11030b11504260003203070341c08a1700710403844948800001d410840030400d032000845050600b0540b060144418403400d0799072141d4211000c895010220a1003411889201d070f6901c0540030003c100300414070001800c03400700100c540311001d04d40d112075022034107000948000306005645500c503100e042c1e020400180c0045e074528024036080001401b000f05403c0104200d503000c4510f00c01d811801e40522a0354010424005503014910740b121 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 204349046 1250 204347796 204347839
    0x120a050601210c14130602060106021204050d06020408030c0c040e01060503030d020d06120c0527160504050d0308040203010b01020309010c26030406050a0506030706020703110d08120103030905 85
    0x1200b450b800c581c0e9030410035100703100380f02542551040e44455035480650342141c01e1010568040d0310094841c0e00b00014426100145082ca182400b062040c1020b04050030400310046d420380c00d0750003030340030f0101080200c010300040c0b10320080b41008105039602da41c1484143d0380c220340d540340140d14051081269031004000c4a0340d2103405800140d0324000010345000404140c1c001c040c14800303003004d00c0c2c00c00070501000380581e44100d034024480900d04203003400c2004200c14080f1480b8600b0041104a400e9007070350121523003107041450406486402207080d5085404c0c0a0f0000b603c070000b84419030030b0078416641c3e00301d000e201545c03416a5403000039145201500008000303880b1341c040200003051181c0e440040c2030040011542c0e9003400d0602002514003502c9a02034146044042841843c00250b2102154825006070520514649a4400425440d4440b45d00501c00403001c2000894100080440134003240b46c86040d94103505000305040901d0b041940200791000300c00d00940c0c1d801e0b = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 204350296 1250 204349046 204349097
    0x110c03040302090a09060e07060219030c020d2303070c090b010822050a200108010614070507090203010609030311010606080f04061424010516031112120a050601 71
    0x6031500e41940c0c0307590b815134004203d004006481c03540b5007042d880d0300080c00b00312101140c205a0890360300d10340b45024420f941d500023070018045150700d92100b00508104103442000c034020036000c0301019001d095071480c40c28402c2520b40642001918604010320001400c0141c1300e0b00700c04015034840e22001821401000e09a0100c1c1d41d010304010614114001000c3e10081e8808241c54020b2810f1806110030304c500401d08046c6039122000c1c0c80c83c0e511503843c0703d04947e5981d81c6e141d1a5545840c1e1001c0c0799111101c140d4260003080030105980405000441c020a000d55514405502e1410024410150032810b0021641040c10801c2455409025075402565400514a00c0e441d240760a8009101d91240f40340120b8507401088002040e0001d00090200500f200d02d14608055004640c1403040382c54103003480d1303444004100423a11134203100b01820326010407580e024192000c0381c091500440c0d0300c142114440c4080004218580c011030303411010030301f407910128246c02c6c00c003014061072 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 204351546 1250 204350296 204350299
    0x20c030f030415200d05030402040f0506010816030e070b0406031407050301090c0507150617070602120c0c06070605040c050103020403120f05130e010518060102030a0c020105040e0108060604110c03040302 90
    0x50300c0c50950140c4c0d59001d003007062108007100c07641404090040e1098108440503403003545030410040c2540c25500403a031040605960315070165442ea1540300d02582d21058070320405985401d9020500720402003200500321840712583c40c1c5280c43c000a05850b03d90307913100e10140c8200148010f1035000741c1a0f82c1520b00401c1d0104240c103251404540c680140301c80a807035100754044071084440241c0c010000d540e4030b40a86900e00042c00c0f905951904075129040c01640303c81d07000552840301c0005050209000411b070b840d02c00c1d40c10001085a0480c01c0b040d1051641d580601c0108601000c0380c0c030080000b8201542818910384407440001c0702c0f034900605103c2e0031611000700c10f00c181c1c200c0ea520492610084da02c5a124840401007a030240a92030041441450481420400c00440d910034801640107605e0054000c008480798183c50318128141321050101282d000c0188a10074041c002c0d44008207414603000b01004283d451030701200c00000020402cad2103001501100700c84c15070380c0 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 204352796 1250 204351546 204351557
    0x503070b0c012c010b04060b09010e0402070f0524041e050705030609070305060609010f180608060f0a140702060c1303020a0902030403080f16120b040903020c030f030415 75
    0x32560306035805800640225914030a07042000d2240e035058030601101c03c10040020001035413034070244000c480c41401110001d002c01d102042e000d40c81103103203881b03c0c41c0c0940054102603580c4c0c5c0d4001001d60216041b50282c004c2c00000e80c5d14a880d203c0180304900000701380304c2d242401e071940c28091030f02005500007041d51850200501108004050051402038200c0318a0b1034610801515031145000899040c0100c8020421601e0300d03d44045c142da818020f03e00c1c04c030b13140c030042d201c0784900c807403040d00701c60344407000008c0c40001885240d00c40c0350070000c1000141f910800c66030407150280c0269050031005418092070b680e000420541c81301c0c41100c2c3c69503d0f01c58401c0d80f1307051b003d564030096118403180310110314221300da0051030081e442034580d02c0300c944a08149000e0b80b003048070403402070100381c1c492040e0380c1e1041110aa4036012441e0008448101c0030100e0203a400882080e4056440895410341078101082170790103070141107018504017400c0044020304044640c0d41d00e000c000303 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 204354046 1250 204352796 204352807
    0x405090a0903080105120f0f07051e100f120606030f0509030703080601050c01060f08010903020d050705030d050a1812020d0c03080105040e0c0a0e070e0414060103091b080c1003060503070b 83
    0x203c6c2000400003242001080350010f040301e0b900700342c1e03031580703401020300803d4144569680c544001c4c0d046a20b4100003408600441040e603c200d501c5130f915041c3c042042640700c1d0300c071050181441880041c040c280c2e408240d12055403c0e04c000d0b6100500f02216544c020058140400d51180c03420760000e101340307084c076603a001c50542140903100d02d0308411101c0100c1100010044015449102042e1080d0240c4140f124540c4090b1502c1c0210180500142c000b042007400c120015070110358072808c000400a49298103808682d54110034100480300000c0800e02540c45c3c41d01044003002a041614000703103540d103035640050003150103218460155407144c02000c0b104200344140419201e02030001041d0340d0382c1d6039900300c0301d0340b040d2401c0010442e9601c0300308050801c3d0240c40840c81071022162825110319004400a200b40b9200365000a14400c10041e003458001c124002040101e0081a400c06404104018001c01c2581c3d0b2044c180740c544200900d407800f00301d406c125001c1c80c00703854a61 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 204355296 1250 204354046 204354079
    0xa020d0e06130602030304060c020a030c080f0f0d020c060f0615090d050a0c1e030f3f0314010807050d050102091009060e030d051c06030b04080405090a0903080105 72
    0x81c05841c02a9112031040c082c007040e410350000185209a01482c014000f13801008416078890340010b9000d0005050600324001013440300000f800c80d00d800c41c0e441803400111103465509504620308005c1d1440c0c00240100300120100705058200f90100443c820304e080c4074001802906052250706a231100215a02c2c10315a201d00c47c0b624a01d400800781c0b6160003107450000420b03074282c000d41ca00c4081c0c07105440e101407050340504090300e40c09228101c000d00c0c1510361031091002c40b0311050080c010210a230101c0c4004400d0030700007500c40308180f245107002c0203018095856104440e0382c0380103078100400c880c407030000d56881200c00c01c0d6203032101c1c2101070420783e000e07208449000f40c0025000080304001644200040c0444d1101c1c0c0d03440d08100051403c254aa070804c20b040030004505000b80801010b480c01c0d10040c001d42e924001445a0381ca07583c21480b554101c90585204602140403c01410b00c2c4990b01ea120190307810400c4000e54958001e800c60006004660007113000710540e040d030 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 204356546 1250 204355296 204355309
    0x71206140d06090b0a0b150c0d0c0f120207090b120703020f06041d1801090c27050108100b060a140a111009060f0b0a0302090402010903170c120a020d0e 67
    0x143e9045080c110340c41c90100305000103020003038280750140560501e0b0f07058800204058071203da0041c40942001500e84104981007280c03040190340302c20081031030030005540d49200035000303490307a00a024000c0c54203051a0850b0144d0000e203019180d1500000103504001ca11001508d07811150f256621316414046039690107190058005402c107074080c0c4010381c510300300c1c09204000380c2401020000c0c03201d05030b600780e41c8032580003000c414500384140216031450282e03111584004500c0d440d0100b6450428040c4d41c02070b40100c13101e0304034100c8044c544083d80112482c10f0020766102d031504051340c400070702c40c01c0311070b0b46440202d0007c204040c0441c400c201600c061102d24084440300c0d4942d4007504000c01d240320040703881310710b0070001404e12030305400761814020005007a0742660340b540d0284010b8060042c81207040100300b4038040009040720382ca08081400b10038074107441d440030032140e614000102100e02d818201c2480700014190740040c4d000011702280c9441500c912101020440 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 204357796 1250 204356546 204356561
    0x40201030e0a020333091605010929090312091009030201020a080f1605030a170c1b010e03071208010803041404200f090112051006080907030c0608071206140d06 71
    0x145c03a142c5014030464020005141c0c40d003007200b0300060382d8103541e40019034450110b03219440c00d00c1d0a10920414800010080c0351000324410406031811810300002810400310000024002d000864000d4141c00d02c03800310384411541d810611805415a000030b9515002c180004021201c0002c0c407007900d206003000e80d156410000303aa41c1c2904d02030301c2e00903220f4000006002c002840d202c0c10a40081600302c85a002c5d010f155403d03484c0c403a08444420421901c0712112026640303c410a140c002000c1009089460117103e000070111840b904c020101101a40800400d610501081c0035080400120a2482c47c0855002802003c82c0d4543c07490040010841c17900c403013000c07841c031301000060801000b5008099032081c03201011440e1000c11280145c8000340c0300d61003e0010700201c0c1c0103100e0960008070b50401c65044681d21780d29103c40c58055003240340084c4840c0144207203641c2003180300002d50500ca400303200342d90070541c10314003c0d5211005640700c1e01102a0b00f50038060f6991010b02e = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 204359046 1250 204357796 204357883
    0x180b0a05090d141e01050f041101050a1809060f080606090109050601021903050c010b060715152106050c0711010810030c0902071b03030516020604090f05040201030e0a0203 76
    0x500c04001400450b5500c90200d030103403400d5003400300051302c00790340601c00c1c8e1050f0341c0400170072610034a2200440c0d65401034100c80342481040881d04845094050111008208107040030915504041d03400d00711150640c0001e10075030050083c010183e441d483c0d241c0c1500c59400c0b0001c4c46a55920041341ba003022010300710901e408405601003407661240040001000901c020305c80b400c50041808038621803408003034440511220032015400c02038002c1c9044000c1c1110181007551141082d2003103002d00a00c1380301004c0f80c0200101040118096107502801300c00c0c900d800c00003d034aa0703070000c07103500101e0790410860b82e00203440101c004218002654101221078103641d15508030b54002e40c071100c401e8815140701c1b4502802559105c000d075041da80d0695849060034828084405e100f045100102d92081d800d220208544041d40318100c0710300303000c15010580e81800d00024040703a103508003052454201d0705002004d600c001503250300a55400d50600040d14900c040ca034140c4034021000b0 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 204360296 1250 204359046 204359053
    0xd110402030405160b070215130b1201031709060304030e27150307081c030b040f05040201120e0307080d0636020901080a0b0406030c06180b0a05090d14 67
    0x1c01e000b00090300d8120000c01a403082c144917154200c144142c080d543c40250b100c07100c02001a034070403150018040320744581c00e207180c5081d121030f0101d10641040030100f81815050004105000b85018890412036414182c18507085c40600810a80d10000308041c0c1402080e007040000d07901c6020a0a60346100d0800e01d400b940c04940150010f24020760710118002c000c034600c1403552a0120b0800110386110004182c040e1580100c0a2103405103145c030010f05507140310038411511a8081e02c0c80b0b1040ba0400081e861074a48009001d003481c003000c00b0502031810300e00741501e11002040740c400680008600d5100c404528500c006400d06800400b5400012610b80d42000c60200700340f05c50440c00303c010380f028100816603204a000e44c903469400211400c1c08540b00c2da116502c01410400054404101183c03030352201c00d035403040c0764441d10005a20a00f501c80c0307009110015409045200e1560346410804400280180144200740307100347c03500c1826000300300c5000c61f500c800c4a07a030800c2c1d = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 204361546 1250 204360296 204360301
    0x6030c0506160b0a0b150c03070b1b0310080d020a030e041a03030d1e05090717010e071e080321090703050f010207020108010e0402011413090e07090606020d0e0d11040203 75
    0x1868082c0a440303003041d000f00702e00072110406c0c0c002881525011010300d0000c604005031611402400c483c041e08a10402c1401d80c0450480140f0800030361069026695000d007151815143e2072030302285108400840d00003414510020307078840c8003540742503070498000c1000303070f4090303200001c005880403050b6240c440094182005861900580c90821030300f00712000da9032004020b5410f0b103c044a40f80c0341038002490030300c04142d0b03410b0400d04410484000051210003030070418500100394002c0f18803c043c02c104890110301c00c113000d002070011000950b0616a41d000b07003600c01c2c810300e9132501c41100050000381e0b10141c10841400155004012548402c0e8071011083c002e41c41084241e000a46800001c11000c0301c142d5424092503040c0e4030420700c40300c09aa00d61072030700b104840103c040c900031800900c00d05603006900c10b28004001070801a403804005408035080e9911050a6400402c2c050201d00e801110400b4800d005403a50401701c03030303d86440c580302094180c100b0b038814808070a = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 204362796 1250 204361546 204361561
    0x403030c0201271a040803010b251103071205030d1a06031006080f04030206060d150e0606190e0703150b0d0b040b011e050702030c0904200406030c0506160b 69
    0x40307035407503e40200800c06407030400c4640140030601c1201d0140c1042410801004885007501c000c14075400603228104090000c00c03451001c003030316400103690f107107100c10141d2500c0c80d080c0507042c01000301d41420800c4203000e5070b81d0794880c054491a1004195202c0b51030725040e03d06000068084001030085503280b51110a00000d1120742c040d9900152102e40061516004491514000d5402d03400909580c1d940008110440721036142c1101e0320f034680c0ba5030f0f009824a1703024200c40c1d40a8180906000d20b03008041c4071122803800c056580b078048480003001400050241079411100510740820500200245104d00092640c00100c0e880f10000e20507100c211182d002e00840a011074007802400d000800440b450b9222082c1b178218101480c602045a5006070018000c0900c040d00f51039041000f840010503000c0d041300d0a40f50614103110b00b268401466020706030800046504000c0d140c11a166062241030b1400f8040c0905030000e2000d54150081307500c0300050354042500b00c0103260115 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 204364046 1250 204362796 204362861
    0x40c0c1b03240c090501080f13020306131415040206160c0b040302190503060a2a0c1514010303140d090503040f050d02060706180f03051803060603060403030c0201 72
    0x1c401e00b011440c010a00c100306114441035001c0320016518842d00e6150141c0d0044264400b9040f800c0390303010740c500302e001610305005443c07203401c4079080203c02d1980c03421f00340b03030309030800c080d1007095040303180216100130f441d98556030025015625292030381c03c0841d80840305a1020000360104850342c100264100c4050024000d4034401c0d6501b46002072003008520000d02d543c00f8281d815000800090411145079001840c407508144512540030301f8585004003859081c00d074100040d580c480442c05014210700000c40780f03c0703d01c0c2c042291400400441c2d07070740307003041c04000e0030850b9101030329020507203580580c1c400d68240b0314200840040d41c58900e0340e0380d00c240300c5c1d452440d01c1b8440014251504180212007290042c1100b8134202a580e10303503005003800107611b0044001450031001007040f01700c0314009030307200303407219030340c541d041c0d8901c141030351442007a14420340c010700800a180d140400c250340c0080e0b040c203010035050205401603014008698600c828415841c0d04004048043c0c3c = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 204365296 1250 204364046 204364103
    0xb0f060310151403011b031806090b071103040b0d02030c0c0615010810050a1707080709021305100f0305060a051008010f0b070302030a08060409080315030c040c0c1b03 74
    0x3e90b21003014001c901814203960310546110086c50b10b1140b80b42030340707020340c205600034041c01420300384640c2c0ca40d0303840040710303032103081a10001c202c201004401ca410080704c031110a0f546000794100703132800780c4810141c42984012135400d40c000c00441c1209801c9003c1e03130350485500c0255900c80c5850140031624413622140c0034001503580000c03d0841c241d80c1040390580e840038000d00b0300c250500038001850503481e29210744c07070304c104080091015814040c40e00501500400903030703502800503c0720920740c101e82026200e1a041010801070942001041031003442e142000306042d035a4000044031024194407a640203040b20004286c095448442c0c20b05842d07420708a1840d00b03898600305500c80c003400c0001009603000b0081801a030b070182051941c0110000c00204c0c1092250707943c84107581060300d4049035040d40c0c0002030042d1034103000420058200742c3d800c00c6060034070300700200314094198018000300b03581c2140d219040c40d42c0c0114000346420401c0f90082c844101940b001d100b100 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 204366546 1250 204365296 204365309
    0x3020c03010b0f0a03030e1f081b091c0c030507180f0507020a0b10180e192003030c0a030206060118030305190309050d020d090e01030b0f06031015 65
    0x3000c1c1d54074200d1504007520020040c01404c0c3e9039003941550340076918400444602c3e80c4c00300c2e00441004251680c200c061800a075565601c5440e030400c840319170a00303d8241700600502d08280019080c503181c0049803007202415110a00d044512420000c502800c550400341031409104000310700726032024200c03c0070850b405c10400601c014096400100c0748150390b841c0043e00680c0c0c14001158014562a8100c40c41c0100c0c1080141c0c2c4011002000450345403102445860396452040031005000244a95141c2414103d1a1a0f540c0e00c020022001d40300d01100e801c1046841c0241c0d4030b08005850050145404640d0304140500b400b80d503a800480d005400a1503424003083c00c1b05401506404483d41915540c4c1016402d581041c50118004030180400d03543daa85407011070400c00244041c010180c004d4803090402c1070004189500c15005030034800283c2c0c004200060b404017201d648002d0344d0159120944030100004e05001c08100c1c000111402d0654078400489011021812104c4 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 204367796 1250 204366546 204366551
    0xa0e041407170c180a2d0e101814100510091202010302030a111603120b01050f0a092718050604020405060609030d091a040302031c120903020c0301 65
    0x310702c804440c00e0008940c4462101404c0c07164140e104c0f03140d0104201440010445110309440d5000490491b03080814541c00c40c00001144102c0e0314615a1580600380c1c1100510a0745044d81c2d41c9030300b070701303c1d44210096000740d0002030782c0700d07980313540100b0b8000d9010029200e642001c04040d040c2145034000c0f544103181c80000342c6004c034060780540301144d54141340d4050140c40e58006600075000108650078860b22031241038034034590303500180010b603440032207a00d0000850500900b607407840f103d4001228508903421401c2c0e03030807100b661615040304005580c0c0300e00d0042c08560514081c0d100401403a00644d255810302c0c400d00740c03021110541d0030304101c44141e946640b1400e40d01007801074201d4100c00040b5015003482d0b00844d50000001d0715042c54050854003091a04a03550100720025060b010148500d40d03c4044990581d15480030444c14642075800098542c941c400c01031076084020008076907841c2c040e091000303803080b101d54200080400ea0a02035161518446c03018400d51 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 204369046 1250 204367796 204367817
    0xa020a02100314040f0507050a0603050403021e0a0b0a110a0504090b030c06030a0216140a020306060306040309061803171c0618020c010e03041d18060c0a0e041407 72
    0xa02c02d22904101d0122680c000304203440e1030f01c6004442035408400d43d074a0203811004100c90300c83c1c4030004020801564002207900d13003814000d003000e071108009110141c00e204070040c203040001c2d1580807141c0200f00c40c04591107140c0160014030100c40c1080480c075000c601c468080da00403001d001201e50041c800d000c144060000c054503060256a10340d4002003e10129401001a50281c82444046040040810019100c10300105a415642000c9900c610300707400440c2000d0080980003681a0002d0106061695029085000e207000f40360030440e8861100101e4050701c400c0c00300564000c10b841040344031074034a407035079a40141c00c0d01115844a8409140c06000c0c0d100e540c040740d060600d5203000d07a900e020f0070700280d8000c00e04108199200e010385100100184002c02c020600800007441d11080082c4030750720071900900c0746400710400154100340300310200d40141d21420b4015915622100d070241a102c403010403494613040b900d003140c0844c5200c5c01390b00107405084140c07074415805 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 204370296 1250 204369046 204369079
    0x911030f030c030708090d150f0608061902094b01020d080603070315020702090c13030b1b030901060509010b091c06020903060702150c070b19110a020a02 68
    0x240b00d440ea40c40b04992040102c5404071303003450040c2c591150000e15014003000300741c8800c0350b50100c001a8013109903540c40046643d81c414401c000052440b00c0181c2421315021b020440c01d084c0e00900202025000900d41c2e50b13a0b0b84200261050403420003d20100c01c10380c0345408851356044281080f501c80011317004414000c2280ba08000c0da030164001e00e8141d01c000400c659041010f840c240e014425544040000349007010080f02582d800980140c0340e07000d5004001080c03001070001031541100300004071074000011085030990350040c85015840d120007040300750034103006036030f20808203010040c04120031040d00304004482040742c02c030021341d0b03c409185060b03107e02c6550507405419840e501e603140c0204040c40c0c07821405410018204920500480d050500c112000001a00f00142c03000d116120028150b8108442007860741c1001803580c1c41c06030f11507024040000d010785072003c108840c09a90080945842c002842d1520707540203603406136075940003880892144401004500c00c1 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 204371546 1250 204370296 204370303
    0x3060109060e06030412030b030d020f0606010c170702011b0503030615040503100509030405150d051302090a0509010b13090b011508070f0c0519031d0102071502010209040911030f 79
    0xb044801000c0030700e90348540d55114402490700300f550043c5030312903100d083d41d954203100c800039621207034000e00fa15942040030241804402032109050124209860000c41d91200700c13100700d078001001c40c0e5921945800141c82d0301c0f001075903c41100300980090802c002003c130185010780b10540c1c5040b8041010540002030380241e0140ca40c2517440441d4441441c4401d0f040030781c0100d80b25054034901504c0c1c4001c07440f43c50440c0b1621000080c005102d80c1e51022900c0f8035580220f00800d20000441c0960000c1d000a601400901d41e0300c0d10741f0f01107800c4c0721080d80300010400009194075002d003030749440c01001d80550751050320f028040304000a007031824140203c1200c14940d55802c40395803041401d88020050000b280100301180740a0000903e082140720911031304c1c0c3e410000e500d40186001881c090800801900310000d0f4419000b8690700028140161421a4071100c0c40c80c1c0c52941c00c03402405001986c0b6405814400b5a6045c081c2d41700080008000560980d200a84c032012025035 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 204372796 1250 204371546 204371567
    0xf100302010c17040b04051c080a03020a0323160206090a1403160c05010e010c0507060c0507090203010303080a0b040b100e011101050f040302060f0412120207050d0210060f08060a02090d0f080306010906 89
    0x12450b4100000ae003200c1c03080c2d00611203190346044c00240503034401d1000c20081e500c2c1c901e00301004e030444144001d80c148042c02d0f2145500d944001c0c001703460510030a54640e065410010107003814500444421030041c001d440b01d003030422080109000e50703414881c0fa400740b50f100d0a40864440121018194480d01060410030f802900174200b03240741c198119242c02c032120091307489010f00c54001c00c441a50340001c500071406942e500a0904000c007004044920152000d03114600d0110a0030781d6496011004d41c17242a107040c1529141c142c440184c8560300500030302c020329440d05003040700001c8a0411603001e18061740c00c84a840e80c0d0307000251a4164142c4010300081500038250409612446000d101c01d44025805414945c01d43c2c1c480d46811050034a08000d41c010f1400c00c861340d5440d10882c4010402e2500300c1d50703440e00e0880003030b4032a00c010301411b402179000210018252542004000c482d83d210400c0072260041e8207284006800030344115001908580d000600184207031034100307 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 204374046 1250 204372796 204372803
    0x70314011104121403030408031501050c060a0f0e0706050d0c03020f03150102030906041410050f1804150f090e0a02010509120c270f100302010c17040b04051c 70
    0x2880d05083c2a03103202039a86004003120400009500042038090610146000c0c521600c1945c0d03ea08060642c0041c06c140c2c4004541088000e204018003158005407858111404500002e2240b880f000c01101404140c2d018005a104848001984540c08002003651200603c8200083c84480004a05920540c3c0c4c2c103410a41060001c684844080030100c002c4407070500442c4d14065105001c03983c603801c603501147c0d88005464104141e801c11044d1480c40d000c0604d042860314440842c203c10768000c007850349100c0a030510582841d51101d03030260040c0203c03078001c42008c565815900e0343e0101503000c0c0d1503025040801400600038001040c1e01c09660584559040c1010b07903080c842c134449080c0010071648164080400b494484090303c4030f4612422500380f07200360304804148140440074001c642c0d829142410403560a80180b8101c0a0300c3e42440c28641b604240c0c1417414100c8e000c21f02c02c0e00305001c0000d0004001d8008001001200c0d800d0780c08030050050318a00f0766000d6014140036 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 204375296 1250 204374046 204374081
    0x504050408070b0723030108190506130318091b020307020f0d111009060e0307030b0c030c070c0602060406110a2118050c0901080d23090603070207031401 68
    0x3100003540d03100f24240d000300d03a49080008209503030b901000140000e140101a001c0010040c00b4660f018000e0a40302070141640c1c0d100300322569542551f072036004200001e4004216041c0301058813a2a140303828031100080748005a440c1c6044200400740d62110740c1d00800c5080d07140301507030b0000c0151050590010141d25800c11014140800404980e500701d5422081c80d1549000790340b004c0401840f004035544220388a410500060714409000540314446d9001c00e404100252040c4102e47d4441400b80ca0a80c072501c0b0001019524016804001c20340b1106860126120f43e0000b0720307034455401000c051000c56039000c0400014800c4844444c0041d001202040c04144000054140c0074002e800c00a13241a89080f00e1400701d00001c0100c80c80c1e04412090342191400141e0300d0b000d000054090030304942c0500c40038180c0e16400c0d104014002416402000b10441c06064512038000078000960303c1c81c002c0c100a40310312050008841f1042840e04c9608074181c140300d0014900d4007480034 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 204376546 1250 204375296 204375307
    0x31f0609181a1002060114041107021c020a1403060a0e100c1b06060306050604060506030a0e070e0c030f010f0524041d19180b0a0905060705040e010504050408 70
    0x80c400b5010388920500051140e111140c0c49841c1c41030740b0315950900b0350162100b03505091484c4c205a0030207090501c61030905c03800110880c21038013290000b40c0c4c1207800340c1c1d1040d462000c2040b0001030401c01395025040c240e00203002da030700010b0302c03840000c02ca00342e441559492100d502112042000c5040c641e01800c003080c3c0c0d17049540e0110b102c000c1e81d0309011400e00804180424102c41002c4202c0e00301c2d8840c01c2c00c10400543c0c1c010039801072070894051028504000104055000042a1003002915001c1100e00703441d0901455001d00003941804205160009075007049a1046c3c85001024a1850000905130408075150050701c400409501c07031001940c0d02c04a9051101d042c452030042c0402001408940428403500789410703500d648a210b02e0401440310180716401c5a1480c068101801d5400c079000c134003036480b21f240e44459003e07029140c3e854868020402c1850046c501e1240b0380c11303c5109900400074108032101075001000584c2c070340007400165103064400400c140c405010 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 204377796 1250 204376546 204376589
    0x60504050c1801051c1505150a0201060504060e061005040810050403020607080f0c070503040b0309070315020405010f03090503090d051f0b0303030402011119030e0109050321090307050402031f0609 87
    0x20098001d008410081d0002c0d0310780001401c9101c0e02c000204823800c0005407120034a4080c014036009120841d401c00c28a442c24181c2c02d124080140000d100309a08060203501c28043d40503580580100000c0361941c081004000d00104026507059015210300c1001490321449440700034401c03281210111059210502d4140d22134002c4901107465020500003c242050400c015500c600580c03402040102d246080c900090324102d103450246a00420081c0640c0e600440326268410480c500018240b4032410b0043c01c50080e0180261301503041e03007500c405e014000912909002c03071920b064010302c44a014070412100940b4005030940c10902c006800756000d003a6001804c00500151110001c55007080100140011001c07004580d103095440e440396407044052010f4401030b001444c11080840300020318900c00b84032049283d00c0003d0b1040340f6282806046c6c010b15019009544070b0800024441c1e00902510b600184071129000004041e88154500d10032944980000181c1d020301e501d = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 204379046 1250 204377796 204377801
    0x20a090b0a0e062d10080123060c060a05010501110c090c1305030706020a0507270c050409110304060f02190f03141305060c0906091201060504050c1801051c 69
    0x9105542c040f003c4c902e5180115440980420541a91a01840491800b034208820100714401c11010402c1d90070050100311555920341400f500402801ca4006200b8400620340c1d20a2680c0301c0100d0040900782306002d0384581055058903426201d511200041c42c2c1a01d9480980b0915941d100354418003192031000c1c00e00c001d0200010107490400c0081d00ea00109183c20181c4e13200c440164016035800381441030600586002e00030071f13041e01560042f0640140c1f080c490518120036040c3d40d8414100b442030190080301c0c0140b4036420103001c8400030010780780e55908111380969145041c00c5614a1a803014400c44200381440b2900820f4409c42d1182160102d500d91107034000c0c150f80c0c1d03102500514001001500c1468101d1803091034503082d01d0902c2c280003000d8083c503690101489842c0c0d19a49040a403031f036841e815180301c981740300c2d960b11450141c90f03294405030f0058646000d00400300401d100408442c90301c10102c44008610200440705845400d2240d40507012541c11801c51900c240c = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 204380296 1250 204379046 204379051
    0x70501080c0c03030108060103140c1503071205070c021c030516061112070f02070f051207050a03050d020f03040609030b190c0807030b010c150e0f19020a090b0a0e 72
    0x41c0203040401d4903030420703e154400e030840d200b83d600450040080040100c81000d000d81d62001034036041842001003090f0020310544070441c00310200010703800c1d910030700e040b00070f03403141180612181c01d04410282802000701002d034003580100f410198030a5112014089099044d80c900b4905901d00c80c08860762444210b084401603101c041644280b1000b0011340b0211303580c60300ca600541003150001c1c02c5103112407070400a541192401b0400f00b8580841142241d106458400d203c6000d000c881d810818543c0000368084000c0030301009104000604202200164089a05403070740000c44958900a61061000107280d91000f440014100b12090f44c000d050031401c00456043c003581c1c4070a031024003070001c000920180c05c1101c183d606010b940c042050a0030b0000c0102c2c00c503150310101c40611669100401e4035080911603008042104098100540c0c0070348851002c51010481c004000300002d9102d10248800480c403524980300f0b000d0042c8000b00940c070110701c0c000d0700301e1002400 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 204381546 1250 204380296 204380311
    0x1c05060303070b0103121b030903110303040305010e0a170315010e060c010906090c1211191a0a0905091608040503090a0e010503010614061209030706020a0302030702010b040e07050108 81
    0x14030119000402c00e0261030301951107030b001002040607500b4010460400c0c90020068082c82c00984404207402c8089c16080c0c9801c003811500c1404110702103403662080f90f05c0240709620b840e0500d02c003000045030340108144644541c20f03c03080c40301a58070050000740ca41701551070301c20200845070744c00398142c0b0600040140c19682042c0c00010b00070708498440740140e4401d0348400c0034608011a80c0540c201070851800700300c88032803150700c0300c400010120383c20a02400d04200c0920140d000c0d40b00c1c51001b0301801c0300b1865088803840c0034040b1a0000c14108001c24105600410285404005503104a40214900710422001e8404448401000e841900c0c43c0c00f04210461007510b42e80c0c0c2c4000130384038809160b0803552509040c90308440150340100300e141c411198004031607072007400300da01c090740c4c1c150101a141ca40b818100c0c1103204280c0c00824491001030303031948954064018620548254008111b04030780389080c0300940d004103516000035004180305100d00d60150080c0d9800c040c4 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 204382796 1250 204381546 204381553
    0x60f060102070902190221070b1302060a170f0c03061e090705310b18030a030309020111070f180f060305011509060e01061409030601062001021c050603 67
    0x80d180c1c500412a4808440510760312008040171005940401110145541c904481035158244620161041c0a4200c0051810f0b0300280403801010414080c2d01c40707160002d05040ea2100c42e01800b900b0481c4500c2d40301d00444400001070703c0700c0c40b0300c100d562040c2030041400e0b15541c0c54400b04402110441e503001002c500520061015854404180c1c1c03046409484559884007080c2824403a801000d412003a611518038507103948000c4c5170384083c1164000c040c200d480b00070300484644201d20b00708000390580f08000400040c180d140d0021442c80e8000c2e254000384298214982d510b440f082d0103208941c15540d80b08005200d0800c82904217644200c00028008840d5000081904c0d482e80c4251110f80d181c0003903948809807400c0d0440281003108041052900e40400c09a502c41d05101300c40900891903090112141d042c402c9401c1c0702001401e581c00d540c0c40300e0010f000d0200013140301800c0d0b0f540091001c501481442112105013460030f548000781c00000d070034400f0b008014861a058007 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 204384046 1250 204382796 204382799
    0xa050702102c180108030a0e030f0105040b0a06050306400c03110306190203070e130e0d0309050307061508160603050a020a0509091012050106051908060f06010207 72
    0x445030707a04410241c142c0c14a59a14580600802070882e0b520a04440c01964090040003905c0000040791802900c1741807441e0100b010000280c00c103c8100342000d455400e140c20481080012681c0034841c00054404006030707070301c44051556400c0c2c1100e204102c0d2107840c0d00413036082c0860b2140c070110b04010401100261500303000e41d41c21641e6100032100078450745000d108002101464178529901540240103a2610311901d01c41c0c4160b104c00700c0240d40c3e000000c0303240303d48585a03081200601034040501c20322600c4211005001180c0e8082850046006201d8031a10a00404c05c00942040055041203903540311480286007001e5003034842280418002509042031042c034000d00d620803e20344000d881e00302d000e010f84000030a01843d20303104103c00a04181c10100b5111440c5003950f4030002070391508000342c40d80b030a030380041800741003081141c0c04228054115505980041d5035420203e168450141a084140c2c05042182d0300041c00140c01e034018094465030100c2c0520486144031b = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 204385296 1250 204384046 204384077
    0x1804170a02100606020a02060304200405010b090f0105030c22030b090303010303110c060301061805150a1b0506041e1e0308060a0e1305010212090618030a05070210 72
    0x240d024080e1400540c114400354004240d05101d908010400c0703001070000000650300003000786c4001080100503600d0710310301805141e500c1101d2050f031003010700100300950710703001d0b4000f86030403801c5440c0c4586183d00c1c1492b515403040c0f090b41c1c000c3c03c04180c5142081108840450b0980301c4240b0440e903295120300000105041c07044c1140a408488080d40c0e4950447c03c0003014081c0c00e6000c282181e00181c200078040d281c01d0200c071b044034441d01c0d00726010101a4180d114484840d441107601c8486054054a54000c0400804455005131503048a542640c40107000e007184004000d40359400200000e00800c0c1803828802c040c0f01c2010301c2050484450b40d8007450300d45841e440303955a00d141c6640d030040503048000280c02160440701810f92034070b0a641d0390f007000d000800c0410941075100c03510f01006000d4040e1001892000144a07081ca019070290b0790b1080e0031503510b0410fa08a2401d440301c80d5002c400c440c03186071607594035854001d01e50244500030740120001c4e410000b07130b0001041070 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 204386546 1250 204385296 204385343
    0x20d092d03060212090c010503040204020c1608070611060405070308030705220e0c09030c1207080604060e010617060c071e0f030806010203092209050303130201120501051804 77
    0x90352140c00c0044e111140300103c0704900400401500c91988049801c100680e04442a40ea100d0380c110350160f03032004040380d6242420500c1c022100c140d92a4580455181c5001c079503d000e403030495455040107404e8041641d5900c1050310058216080b082013400404d91280003541d0014071810143d00d80001481d0750a400241038180368920300c0003401c02c0c0204a071f80c00c3c041e41c200603081ea40f41d0420840c0390000b80c407001c03421606c501c00d1150041c10003000e8020300c40d0030010008074043d00c413a482e180c24002d02805101c003402159500e862004951800802c04180781199150014100c0307545640c902642c0d944001d805580740724145024580e072445903201509000d100342510f0952030014900078011000c00b070000e40c19504180828170040c2c640c0410f003800403103030781c44501c0c00115039810a0005c1c40d02c2c0c0c0001e080d5000000402480c02e031085010764030280700381d0f100c0140041c5a0194401c54000780078542d0f0041050b0110702099005900c0c55400c24002d110008040b80c102244141c1e = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 204387796 1250 204386546 204386549
    0x20408030703031a0607021305040321050a27060c030f020703020d031406030c09041a01080a0308060307061409010e040e070e060619050310080d0c02030d020d092d 72
    0x9441d8070f18410900190070a10380c040c4021750f03e81d410300314a64005404032440300c44a4002981d5400000c0a2501c00c0464100701180020003410136a10751b81c07500090141110031524060a280c0c2c9003076201e008a030b01e01c40c0c42c00c505400b040c0014071555035801400c48000c200007010344800b0541c40052403031009290080c03080c0c00500303425008585c0507003503440d41d81265803108280400c02401d81c0703022401d0440000200c8440b01e4940e15840d0031251100f04508005d030319011280080340003e0700041e03003481c0900940395032005a907404101035803109035001c2c0310b0000d082d20b5102c21020442e100640915001410040803841030b2202103000c0b160032241900c010b42c01a9000c106c0383d590300d2a034a42054054800da0318140a40f5851003206400314101c00c10000700000055181070413100c40c001400c4403200341d8000c101080c1d0010000000d440003a40701c1e001d110b41e600081400041d10702c4007803069031141210517280030114904600006052450320041010550303000988602c1c020 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 204389046 1250 204387796 204387803
    0x6030207030f020604020a06030f09080315090121020f01020c030f011b02070308030c070c090f0c1e09030b060409050303100915030f0215040801181104230a0204080307 74
    0x103884450a0600030009504105240b0a54118900344009610f40d15400010b955240c10046190030303c401c0345500910500300042d102400202c140700c040307484403801d00c03803410046a80c0411642c03228654903000e940e0340c0c200f849200072001f8400042c01d01e82525403600b141401601c42c41700c551404039007040c003564142e808603596450510340d001e022100d0300d0504070075880206801402c581d2005941c2c440501444840c100c0407d104d01000303400620302015004000051005400e200311303540c0a400c02083c0403011420f20041020f502506078070180c0e00c0549580c0f208031591558940c0c0d016050042d0180360442d44500c044408250700708000d502070140b00c640d5005072450040c01a040782c1703030103034441c2240100d40e1007000825640000d4400c9a03804484070030210b030014480080b14401c0e81e0122001d9420094828004020810907164203805440000ca003c078007038040104842d0f903440503500c882c02c04c5070f2001a20001582555010400e200d0040c505a121923043c0d1468100c1d06086 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 204390296 1250 204389046 204389051
    0x30918060806090c01081b09190302040f0b100e0103020c030c0604110a0602100e0c100206041a1006110102040306050f07090806010e0c0d0615030b03070b040503030910180603 77
    0x1c002140c000c001540d4403a003804040d03c000312074040000c1805102810316250300001c41c84c807140c01050203040300c03000d450042000341c0317029810001e070415040c2e511040c0c0c401c52900c01d2141c0c000303465003c0c03031a11240062400880d0001040143d0725805032103003503030405900f4003105c05145000c100406c0c040300060000c003140c0c5000c1c0b500394100341d0400700b103500a052006007013100320740000d007001050071184408101d0300c02828800d4544400950304c598814101c2c2c1c1202003c98010412a008034013a03205108580700f1108903910146003a1600640302c4480362040114038482c19442d03103c00001c1c000549815525244c401c1550030035100012400381020a1000d120b4200303601600078240d00001d040c80c0e6140c54105c1c400031000074604240d4400009030f880d1141219401280a071041e41202000301c01d400400800420481100d00e00905c190200031400e000580155012100000d00443c42c05c0540341c2480340703080406a0340b41c10310000344100c401c2080c0d03030181d00000d0700e1181e900 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 204391546 1250 204390296 204390299
    0x603090a0c1401020601060c0f1a190902090705070602040308030c0909070f1b0201031b0201060501020c060309060402060f0d110306010e0913170904110705122503091806 75
    0xe04081215030007074900e400282d000c0c0d1402d980125185046038641e060a136038400d090705000981081300000240802011140300505800519540d805101d40401e2519080c1d085040702080f174002a00c0030790302c80750341d0380044d907501c1c804d00080c91041e1280c0805400c00c1e980781d650024507003065070140302180c030100c4c2c15811821301d0b01c1c40b240d110f00c15140800018001b42005024031790782c070303c00141e0b803042150540700b0b69000f9000030f0300c00504400300814a10b007440000b80200664081c0d00d00600405a525000d842c0c001c060702d000c0e070302c40001340a03503480b03545c2000340d10740c4185040d1201002c2400580300406580c4a0404031020080314541e480c5003440005200c00490003c02e4814010181440406c1185c0882150a96400103029024a1000110700a28000d11180c0b80d40706080c0701c0003020111468001e800014490400c491415048200c844842e01803c10014200e00c012145811055003280041e245070f030180c1480707400f60381c6808840d0301e0700284001310440c145d00c9050 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 204392796 1250 204391546 204391553
    0xc0c121b011706040f09140f0c120c06180901060207090b040911090702070503071404060e07211e0905060702010203062227030f05040f0603020705010603020603090a 73
    0x10a00300352a0900c0c100701d549004030740050304010b0203003090f401242e9884e614043c10a095000c4445190015000380c0d81d800740c0d41007180d0350320307100c451215140600e0344101d2450400c4043e501d0140e01003005031804800030806d22400d9002424004400c019142c0c000540303443c1d20f0755980c041c1100b0380c080c1504d941010844425141030521480c0101d282401038004039004400d41710307000c00121251580f50301c80803012490003600380c1003168503014107040000d21140d010314030b0300c1d42142a42d06105150b6030b00c5213985502411603004000c10243d048003a40000c02c41c1500307048410030000082c1c502c50603c0c00080020740e801e003000b1480c0c1e0b84d0030b010302405410000c540e031050380c0b032000b03500e1441c0100200b00c81110300898462007040044c0c040718401c2e420341005040c04001220010010848908201c24031200b520641c042088500450f0800c2e00c2502214151440701d202145441c0c6000c00032002988981b20a0341da5551f10b02c4044016070300c600045005d000300a008003150750706402e = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 204394046 1250 204392796 204392833
    0x8060d0c1d0106021203010b0306010c0204051810020703080112060204030605271f0f14040305190201060602030f0c01021b0f0d030204030b0105090421020706171b0c0c12 75
    0xf04008107551140c0d40d24100c0c540e0050450741900d1801000640341d8680c0c01c01a5803c04d40d203500258800d0800c0200003a1001700e031141024220304d042101d8101d201040d440c412031186040142c0021403440c010b000c031315801030604014074890000149800c1da80c1c1c0b500b40c12290b068803551801d020001c811601c0700702c200c50b500f00c480c07012409400c1c410700e5a455461881c0b24292014102341e15401d0714140070442c1e506c0408080c5490400c160f0a142519005207158046900e404104e215100a42400d0340305200380c0d41920a1500110702d80b6445880009070380e0064038180c8550340d020000c40b95108011b000d18804011640c000349050620117680b2800d222050f035400080610501c010800304900c41c0f1280d044a0007969070350340603110360800e6201c031120090b034a140d50305101c200082095001815070b00701c840d90341c0e90110b159142214844103020562301c001c8200c04e0407180e4052614060000c00252a03200c0c1143c00c011011408291181c51501003001150000345154a03c0d40d03010 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 204395296 1250 204394046 204394049
    0x2180a050609010b030f01060305090f030705032d07081810020d030614030616050702030d0810060305090d030e0f0d0518100c0f061509020a0e03010b0a050108060d0c1d01 75
    0x205024154641054146d0860205200760b5080585410110300c034540103100b00c400081c4075009032659454541800d50b5243d104020181c40400880f04c890220b07400201c046409258001c007291030240b06880e50503054000b52000b480401050804410796956a141c0580718503080c0c000c1c00403030f007241c000a01281c000d94083d007660035100080000e1550f01003a4580d00c0402c400d0700c0082d00e83c020f60200d426009010000750140f0651036018451038105443e60300ca401c8030381403911013640742d11f0201c09a038000c3d0380e250110382c00302041e0304460780070350041d014040480e01141c401c02418145145060b01d10360b2000f0118100154030700d8041d04d5508070706030815040c1c0300b0103c51901d04030020b00c50400c60750040e1000d070341c0c6d2900b4420003209030040940943c66401c09000c090301c1d410300000a605c0203011101140401022841908060003074a00c200401070400c140240781c00010b44809200501999001c01c0d00f809260019049411080c050300da041400d000c07030a4444200c0c0c40c5e02506 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 204396546 1250 204395296 204395309
    0xe090f06010c0305031f0608040606050102150402091f230306150603070e0a0611060610121e0203100f0b040e010311030a02040609022a0703020d02180a05060901 71
    0x151080011503600040b04160540d0705140c03c0b69641d8603030042c05090103610101002422040702d001035602d52120003240900e000c4c1e107007000510b6690005a07950900308003a6032001914100047c0035141241107154010903000c4000c41420800080301c08085107a00802c3d00c4816003598081c50705452905094031110607002840241065a400001070400718200d03403107000004001541e092040b054608105400381000c1001512180d002e1b24450004848026a00c60040096594070304095061000015912001d00c450490080003028003c8050001194455401240709400081c80114840c1040507901c0b108141015201c0d004100540e11040901d00203003c10703c0000540007400b81160b600c0a0003550321840c400100f030801410b00c0010b584645050f100046180b42c030740050102d11500385c0040e00000080c50000c0c408008042919129405005d040c001400c0284880c481c1070b000804401420960a4010002250444560b01c4031a01d90b4180106828280100790142030b0 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 204397796 1250 204396546 204396571
    0x3011d030a14090a0e0c070f1505071d04020a0203070b042003070605030f0a0603080c012403080904050a0213240305041e08040b040902040515130603020a050f03070e09 74
    0x3070010005298140c41e000701709451004001095030400c0e0f02003125645540610400ca03048118140180300a840c0c41d080c0241a040800040341e1920456a85840300c003100e1113407441c42c6040701800001d400400800003503110404c8810049043d00f4030701c601c21803050021001014902201c1d10f01c41c50040f101c01d010383e1041806000c3c0c550000180c0b940402c506c0d55840403036030750001c80c01c041d00d090390020302803130170015070890781c854103420104103041c00800840318031002c4140b074010b2840a1001030310201062202144c186020742056422040b01107015007882c1004481400b402c14a9103d0400c1810300030300300542d0803150800da0702803011818200014645501d86a10054041e056a8602d01c00c40f990001080056002d0354081c0900c64030450b02c961720350600e078001758050b004c1c4500c951248a0a5582646510212082d544030702d069038000d64902041600a900544010810710200b40070195850b410354014602c1400d01d40e0b00c00c074500308004140145090040c0c825905101c = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 204399046 1250 204397796 204397807
    0xc0206010806010905040c0302060a050a030c021603230111130f06080109090c080d020a030806060307140a0905060f0d0c0c020303042d030b0601022b050903011d030a14 74
    0x3003010840d50f044501c03010020807503030799915041c0c80040803604000d500c52008925030940380e51120180c85480602d480c10440d450601000340d1740d0311610700e103013024698408014000030b0098164124004120f0000f40e0f449404060418255500c1e2181550300342c40200d40c0020384001c1c00200c1c0010b20a102c4006042410140014101801401003140ea0760b01d403003400082203d04290000209051016035043c100c03040700081d16440c1c0400d0550000d6071940c0403402c1ca14103c0120390042c00980c442c07440580e08074083d610750380c0091251005121600800040a1702d401c0300900381d044240d09920342e41d0850a03500412680c2055584042141821010005132000021a000d54440c0d441a501c014070340c0200300900c8540c24106104001244400020090740903075135801420240c09444c0c1004440b80405483c44c0c02009d20200300180b581514a401e00550003001802c60182c0040f81e5127209070b00780100101082d6040030b40c2d62002031680d103801d90002c50303110b0a00c0c40c4c901203444c04 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 204400296 1250 204399046 204399059
    0x7020d0b131b0806132105040f060302030124140c0a17070c0b0d0605060408061608070e091519051302090d02060307090810050f130f320609010c020601 67
    0x4100040c02d901d402550950140244200303000746c219000229061a03401500009008001d50024804c01032030b100301c4d102c0401c03043d0103402a01c1c16115800a000164468182020414440380500c1020b00150740741000518003940010064000c40c07200400c090322142ca0b2998800f25540440110004140601e0300001c400009560440d0059240b09442d82c0102c03002200400d11548681d43c03285002030001408000070035242d1040200b0b001401204003619010b403041d4404850340b0000030b203042c088401d0b5113065038503550401e603070405400a4002550100d60b40c0050381c82014545604a00100901c4ca403640201e03002a012150650a1203149400304002603460440284100c2c0301000040c0c581d03100700000740060103440d04951460019010b00002410b00351000003a59040c000050503108130b982000a4103a40010415407102260715002a02d200080c1508540407032800024080328002c138001c510f107107510028208505280c1d0380d03d401c68001d441d414083d90094001003001 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 204401546 1250 204400296 204400303
    0xd1505030709020903190b07030e01020d020403030e1302070f0f080f07032007060f1b0f0c0603050714090603041a01060e030601171c111009021306030803070507020d0b131b08 77
    0x812391a0401143d0320001c03144041c00fa015038800803a0301440428004280340c1d0000911b417403404103882c40d0055400300100d8205034072034044040e2000d5142e940c01e000085400b070004d9101401600b00c0d0381843c1c407146088050390b120401c20b40024010b44452100c403007907603918601d860903907001404041e01d050f001500c5e9000e45909141840700045460a82c0312402c1c1d020311086074445103004000132189084059000c10340152400a4940f81c00145014098801e0b990036011200e10541484c0f50141000312075440180304442f4280500201c40b8240c10b41c10800e80030303010355150591003003c030100f41413515030142e221624003c20541d1036441c444010034601070b040c0c443c8086442c800410101500e4180600f5908203076881440d1075509e5414480d440200000d100315812401d06407506424000d40381d8901014103111404c1021411040c004d10080200304e201400030090125692903080301280e04a1700c0456000d03402001008000150031502481081c02c02411803060502c20065503 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 204402796 1250 204401546 204401551
    0x70308030105130911013c020d0e0102100b010203121017011a04111207020106050132090a05030708060a1b0207060f030608010213030210140d1505030709020903190b 73
    0x1070000c0c20760f0f2030700614880302d130b187c00c40c4481e42c4410041c072610b0340541882201e811301c3c400c0140110f20505956902ca1262088901c505a00030151040003228080040400318481415031008000c451341020000200c0c5101d848202c8490082e40d14000c08401d40eaa020ba803d6000750745001c1e03401c000b201041b618800450b40544000030300242040000606200d40380040d40740c500041c08010300f896054009000b502c0b02a6a00c1082c0044e4808183c091a20031030f00190a40804040310740300809540a45480700c402407511011780d5130b0f0404242000c1c030703e802c41c0c14035070440000c1009072540d600a0309032809007180400a0a00c22550094890f411401200100221205d045490320300c13030340203100a008014021507690904010751080c5034403610003280605410140010403d0043e5050340e8010403a4038443e1410000720f800e03000a061126140e0382c44d0341c80c02d02c081580d88003040008040e05c20210010303540c0902c0c0003010301e4502e220f1a8000c003aa0004a044000b448100f81940c = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 204404046 1250 204402796 204402799
    0x812070b0601090512060105031902060714100905010f0c09080304060e04090b01080a14070f09200c0a031205070f0804051c09061d06160302010e070308030105130911 73
    0x81040d103036200103e03420701940e4011a4000b01e06541d40b1500480401c00a048550840444c2c9060007202c0301d038241000c1d402c402951200d030a001e00c001090010f20b0203003155440d001540c2e00c204450850908031414005c040d2030903955865242c04001e514801e04044c47c1050030880c84041c0382c000c5240e6288124040c0a08000c1b100711180f107903032100e030401d04109500030801002903840e4a9041c0d034076518040142e83c3e000030140c18920801002c5660f0f4250755000748008180c5040602a41c080c11a603050519040f02c1e0200341c1d0740604883d030142c108500d00c1000b03008400101e04000305618024007040310910302d070109210905400c000c550301c046010b410982610b9840d410442e0502015560000b04058800c0d01c0d419195070000070501994000d88505400a0310805503051803a41941040d4000c80100402c0310740c1c0a29140000c044e40c481e03c00401e9840d082c0c40e0142c1400c40b41c3d4801c4518110110042c00b6500e0841d40c2202e41010500702000248015200c9074040802010900d = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 204405296 1250 204404046 204404063
    0x1020903030a1103040b03010b0a080f090c150c0a0b0106080c210c130603050613090b060d05100c0c02120a02030c01080903040e010b03090712050303010b03100e1e01081207 76
    0x40f000740b4818802d0b10b005003102c81c4d020380c0703070340c4c0d10040e062290b0711103841480040c1aa03400128007002d4a000702d13000c1c1a1210007401c15082001c14000e95094131405000005014089402803400030000742d248a807060040d006103500d00b050140003968003030880d04e1413003010300c040911014034512080c941181c08142c4000c540301d600701d032031181c881d0070148044001d4192020400907016005a40201820b5070210105040d280191080f20f244610040541004001140c842d14010481d5501a4020815510703040003528905080ba50100c010f4008240070a80900652901c0f0300e5412011035584050320302d01800d5400251101c407021919810b004110300030a001590804c02d031005054084103500603561603001203c5c29800444a0840030b200300c18010802500800700500250340c80700040d42941d0030984586010f41005005246100e603014000800707048028409000b07111000c0c1c0da00000d0f500c05000c81c1c81030300c160402000f59118481d0f40c0820810081190090764012800 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 204406546 1250 204405296 204405317
    0x21e0421121b0203011a0108010909050303011a120f040c0b03040803161b03030204030b0c04050310050402040902041d07090e0316080415210903050a0f09030b0a060602070801020903030a 82
    0x103201c540d450b40d01c0701035059841e001c10404e91003195003206c0b1030a5001d0301d8850190f0390700d0b1020400d9034808400142907400c240010805c0d01c40541c074010aa554291380e05041c09650702c13942c00720309000c4801e051503035070a0050000707000d01c09072100040d1030b089140915529207600c0f116494480641003488100d401c10540c0074440c802c5904218409084554400c84805401c008010f9040360000361030030200c92004c24804030050088400711400500901200b0704c0c40100480200401002030344c2081c2c41c2c64030100140d880784038500c0000070704000c0c0407074224540640c07460882580c100d10b0110341380101d00305400d04000203541450b101d038085030303a03501110700c0c20800600407503010810081c10820010301c61070f00310450301081c440112281950145513003064058420002025001c60010015003125500c501203041d10342a80c1d0900004407542c0b99180902c0b00003c441d004000e0365520001d03c071150b4148200401807020b01d000358104801d2074006901c070710820700d03401c0910050080307 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 204407796 1250 204406546 204406577
    0x30b090a11040207030804120908070803250201090302060a0905090408071101030b09010b0c0109150c020d03020702010903020603060d050624011701050d03110708100c0507032001021e042112 84
    0x92740005800481d0503a986256190b030001e075250005117040c1d00706201800c2d0703400100469030b900540c954059681e040303250318540074031060f94450401c0341c04005040c000403903991900301c0e006001d40e1040304816a2002907081c51520355546010460405040c011001855680c00090a0544401c400880d958644a002a40c0108003041b40140b8910341000c030724040c11120760040e90900c01c1d94080d0b038402000d501c4124124400e501c0c001b80851109041440941015006560300c0200900012079225a50701c4451801404452170b40110b1b40030400203907486410405041c5601003800c00d4400400d01c9000c100240905004450080c0c1a12403c0d105142c46952460410100c0c9000d5504041c0c4844800e6207039520034101c02103103030a0500540840c0d00c0b9004644881d605a600d0a00d070502281c007d441d8449000c040344032541d002d101d84031301c00d800140c0c0110b1021103010400e0350341d441c10004414800b4015110079800d6050407040303011030641a1203902c410501e140c1607403500810003 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 204409046 1250 204407796 204407807
    0x13031b032919090204050406051503032d04050603150114180402090d120207082107030f02100f020415050a17040c0e0103080d0b0418020f030304030b090a1104020703080412 76
    0xb83c007075441030509041c0010700401da844180180305400a00c240840704c04140359481c0f08030400c0c0710740c140d031001d14002d841820b107003034103025101d00e203002c0c4c5055a25400a01c6582003a6110b42000340014203640d850341e040345c00440404c81c6034441c982805503000008043e82e24040d48035001d84e8001600300d0340d5603100d00c4114003076640301585240070707002540001e640301c803e1b021344400c610a0488035503030b004600007484401d89160082502d41401c980d4200d401800c4d8003108002e500c5031189034105080f042c0552004d50160510040e210780c50f0035894100300c04020b0340102880001c01503413945171342c440001040424511000d00c4151101d2400e03038100c3c05e05600c04443c10380d44400100030130103064020400d05640720400e00002c000034042100b02c50030350039104514810700c0840700060805140081d4031450040070b890401d5501d8030f40450181040316000b10a07004507000c4001c02141d00d407010f1101d64241c0c2e00318188203403a68054603402010300003a0441521003012101e20384200c = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 204410296 1250 204409046 204409061
    0x10b1504090f0609050f240d020d06090602040b0703030f0603080a0c11030712121404060c0c050907020d090e060a0509060d02100f090b0f0307030213031b032919 71
    0x290f0170003080c906410380d01151031050710b200030001d2481c2d01d85148041070000040d03460400510f090401c50a5508002d0301e00c503941070481e01103460f070100c00c001c80c4481c07000d48000d040442d040750340c1d0328203441c000f400c464543c0d10594a003440c04a02740302182030082695807407007190501c00360300007090400e02d179900761609580e41e0600c94403a0116055480c5c0910a2040b84518450b1a040c0804081070f03882c140320f140c468402e02000d0004001e164410601500b00e180613043c402d1140c1d403528003246500404441210140e0301142810300b8032640700c0c0700d00000302a1400a01c001e400d200b00040c40c0c403075007131040c241314403c49004100107030f0310505000001c540c01800541184c4900801400718152310320f052020070300c1034800092002100302141c0038116a10101c0b891507803240d009800035000340a001c0e401402e003210200024421080240e00072840c012400d400b580b031441d0001d80318030f49000c1c0b40c0660342010184e40400301100e0039160804c040e800080c0c6496031450156004140c407 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 204411546 1250 204410296 204410309
    0x1d0f0624180405010603060605121f29030d170703020d06122001030608030316200102031906050f0d020102160b03090c030f060a050705090a06050a02010b1504090f06 73
    0x84000b03110411205500c0302048900c0703510b00b44812551141003142c45c41c0010740310141038003c078242030b41d03504001d5003540b80014000000180c00580108025900d9046a01403420107151b150384120752070104445440e0700711300e1a00000070411040c0820262130060300c0042815000300d03031054102180c1e044480035143e0350300c0d00150062582484940d2060000c4010000c0358104400a1154420b01405043d0341e001c40046195841d0744000c3c0303e81d0902031112a0410143c111105c01e100700f450307403001a0440100016884e4208403112080d00754480f640e60007100d00e8000d00b04040d0715000e840c0c0301c070410221402542846103000503402e000000424190044082201003141a0154061400741201d01c080300c010090704408d240da980b1140d800038140c0d600207c0024040700aa4005907030003102807500d6410100041f0205010400c603810050201e01c2c0030070203108442d424070031400b5990341281d007440d03121100c10703000d40281b00d24040c2e64400c5480d100507210315006a0411401008c0 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 204412796 1250 204411546 204411589
    0x40b030f0d050a140309010b04060e06060f0309150c070309060c030c0f0c09150306050f0708040209040312090309090b090402130e0307020303131505040305030415121d0f0624 77
    0x40c4210851f00034651080320340e11681c90038101003145402c03c01510b1283c50080c02a03842c04001c0101e401203074100400d860741c2442103030343e909000010804120f0181c48003010b12070300c1d240d2615000d4440c490070340209040210403035402000c01d41c00710205d0961034004c480564080c0d01401c1204090b071042d0028002da5041c28181c00800405920001c1201d0240800300a20b072240c1c1c007048062482035910380002a1140c0101c0c0240c540740d02041e801620070304040c16a003003c0c0781c0a10540d5595201500425400c1c03000708440419030007900300080c030458540f80140f03003031380c002100820303281c0c50b010303000c3da4880003800345010800441c2c1c0416002011240c80b084544005541004a4001e0885e01409003000c40b4840e030258003610181e9500c50055414603091881298081190344056170820002d043e000c4014049031184920760305014502c4681421140705552908003584802c000e59071088080054202003480f0b1410207100000061441c6802840014a03164810303100c4408ca88 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 204414046 1250 204412796 204412801
    0x2071b0b400311180c030a0e0709140415020a021b0415090f0b03031306180b1b0613050a02040506030a02060a030f0605060408030702090601030e030f09040b030f0d050a1403 76
    0x1c980e803c5411100440f44c140010108503100070001100390b400e0340d43c540c030a20214a030103045400c031440d010100b6040301e1808c0e031740e1004a03090750720b082c2c902c8003000782100c180018007000b11040c11202c1d000c50410351030501400002942c1c0c50400880c1e42c100d11150345580c03600d0340c8a412000c1c6c00a00b4001c603180090b1104c1c1900010940395124101e01860602000ca80b03080100a0b5210042d5a44640005030315140341501d0000c8488a50780d46101101000304140c140c0ba4054841c07540c3da002c050700c00c084c0303000006261180c058050310100ea155100200010f00010b00c01e0500b980c195800324a0b0388500004c28039121400320000c1d480b00b00400c1118056905921280d09221881410b200842da00c1d001d005152145006018071034100700000c0000d030400003140c0d60080018540080d480f000080e110341580c200201622060400041606451800d40190f94542c00e00700c0140003051001081030341da90b0030300141c110a00c840803810901041c0603004008e2156502c0083c2662071 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 204415296 1250 204414046 204414053
    0x30b03071502030306031b3703050d0206010801061a0c030c0327010c1203020a09050402040b040e0a050907030308090c04090605014b050402071b0b4003 67
    0x20303001181c01394040c0c0b00b5690907900508060105040c3c12501030421030500a49040018238007010043d640d00f50030105408124400320301100500840c0260050100960042d030020b040080682c4481890384c10800240031070704910f400750030103046e11170784103a0ba45c80e44001107095000380c81a411960201207041c50403041900300072031402a1004139038500c0000100103440120411402601c040307807040c449009980694001c000c42c26050501078500741e65100010160b03405504411061140840e04001c0c0c0140851410f030440c2444a081c001440d000c4400c80c0e55841e1880040c0030044003801042c40c496061040081482c1d011b0402d024106660500e00c02070f000a21811751002030b0100d0000c03072481400c05114490809111021086241e4500c08000154040c1c02d550301218804002440350395501c02000600e02c42e10448051402103500b0003049600c0d40d011004814080010101c1030340b81607800004a10048010a10030444035004003005c494042e4045082820403004401e0 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 204416546 1250 204415296 204415303
    0x60c03091b090c0c072d08010e12070318030507181a060f040e0f1501030e072c0108100c0c050d0302030c090d0501090623010506070203030715050105040609021801030b03071502 78
    0x10b5000741b0382105240d03a401890f4221281c18081e107038a6080030384600741c00c00718400145840f500900d0400c880c21801d81002d540200680d0003201d151740911010002d100c00800c0d10031420382031150400040c1400803440440e515100b02191081d4000202d42c45101c411001391409440c2e5000e402c0054a4002c11680c204101903c036030503500c12200310141298805d00404142c4440c00f40500302c400d1030031100f20b00c051001c1c551900144a1408045031170f4490312850ba0081014a00500230134407103052a004032a4020b5044081000c02c0152201051001402201c56100c81c500181e81e5560038000352024001c10014688c003800b100341e003205105054004900b80c5005a808102c800445010303440303c81c075a080c01c801445005c0d07004004901c0c00390302800c07210340050309503850029503564039200c110300c0c551a03527107695490b030061129003084e203d00c4010385a011011441c12040440507045211144800da0400d900c6428586254505000e05001400c032540f1608080002d0300340a0746 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 204417796 1250 204416546 204416609
    0x1311220506040b0d0f020c1518060c0a05030a020702100c051513030c050111030103120807050a05030a0b010e0a0b070308060a030f12050408060c03091b090c0c07 71
    0x5502052510214161a04008440c02c448659440b1441c00101a44050181c00c0040f200e0b185103509004016600c00c0610000b8400e2002450303206407490b105c80000768264a4054440c010b5201c8c2d810040b0041058080b100d03201c41c203003091500d0f60f94a81d10040030307104080d80250405000306a0034000e17a00180d00f03044031845803040d103c46602c002041c0702e0700744040383d01900d080421008100802e001e4003040c1c18140c014000410492070b160800460780c2d0080e070044034258038269004d0b14455201e014240c0040c8940341c0f081c41c04030403040c02030190001501c02403050380d8940c5070b101c441e8029100842024030181c00e03000c545030350b114044140e4004200a8003c100e00400240d101d245c0441000152035000c1c50100004084d038840c0b1140058a51111081c044200000724540d90f04101d0a40b045802a000390386e02d240c5511100e0500042d1441501c460310102d0600200daa82c503601598400400348010f515010f034200058581100f5500070018041c0a903501102542d0b400300001 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 204419046 1250 204417796 204417847
    0x115031704031a09190c030b16050414010c0204060f170105040b010302010e13061401030f02120f0c0c01110307111501030326130c1706131103061e07020109050601051311 75
    0x4120340e91000382c00032140c0d04d0789c0300f040010001c0005220103070203c0403914207002c0c18580301e80f60240325408103044640c0354010300c01d1401454410400d40c0104164004901c000380f000f40107505156482c185042c0043c0002030500880b1896450151503070040614515600d000c18000180c2d0350078503001012032003403440e00107414100e11660441c00c1d0b00840e180b003440c852240f0f5495035507000641c0e00550140048019800401c00c602ca15a401d0182c40c0b40081c0c5004507036501d0510a03000340c040c0c40d48120301e5140c0d07000b02c11104400002e909441d81102d4060400000c1d003c20b60015510304114070a0803040103005105109020314010144a00c5504c94240090070340d4840c221586403a40d250891000ca1717201200050105001801a0f0807070303071140344400518058180040d04102c003c070b0710800390340386034900c454280c0160413030141c00c01c90500081018806070f44540707490700d105005a901400c014210308040100701ea021426000c0c1c800349468031880c1403138811800c0460382c40003e = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 204420296 1250 204419046 204419063
    0x70e0d0b090d090e1605040b071110030b060d050c091918090b1609050901060804061103070f0507110307030c09140f0411120115031704031a09190c03 66
    0x34410a40034500480c1030b00c3d13055026241c140e0b16001460410001d1000e60000c000045c400007400c40031400180941500c1060307410b900d40248400d02c00110200c1150300d04043c05d024054415444420403104401014500440e280c0e643c0d804400d80c0e840341c103800c507030000c0d45513482d001074640c074083c100103940785210740085810900c0c2d6000141d5402600183c400707e6104003050f404e0240041e5104c101c00075081078a03605075248006541104241d00c07607004108801c040200700807003885004025054041c0d16811401d00840043c81c1031901d01e039030f005210002400c0c50602c25174803404011050014100c8840c4c54591914070803100e01441801a19410115006210001c45040910845014009081e6642c590f280e500401d21850309294100c4803070560f032100d03000300303000b240710084904c18404d16551031480c0c210304031506900d4030b00d01550309010600c001410419240c0d500c0c41e60002c2d15200351191088103041c5145400c0c5270285001e5840d1400030048591040400c40740140307000c = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 204421546 1250 204420296 204420313
    0x90108030a02060a09080301060c0f0203030f0306030606030109030207050f06131716030b0f13050d02061006031103040f1e060f050f04020306061e03071806060c0317070e0d0b09 78
    0x2e13060300d0300b03080300400403a401e000602040e4404c2c402c5585140c007480044141d00002d402207400c5901a203d07a603d0000b0000820030b00e42020042c03d90444000c0d0300030420700c1000c0d00e0007901c0d0310090288520800d00350700719462960701e22042e5480503504003203031b81210780c0c0e83c4005481b010406000a9043c040c24000c0080079090048240490b07400c06151682c964401801208444004040c0100211007002200100394104604450003010350000d2200b03041c01c182c85039540800768011000c00d410a001c2c407211900c85415283c0007540f0500d04001d9200c0c61511036000740c800e40c03481959091403030204040c40520741048003030220259040146403100c17280200a401c0032200650198480c50101d225414482d240c1140d508048034414400511040007038104000303a88006581d40c1118142c91340c81e492841103070010301050420380455015550041c050854440324440ca07168094006800c0728020b8003003420321140141504610409440c01c00002d01045c1c94001c09440b80082 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 204422796 1250 204421546 204421561
    0x1805010e010f03060b011202070309080f010c0210180b04080403030e060a0e011404170f010e010209010c08090a0306090305032406090607050a020901080304030b0a0b01140d0902090108030a0206 85
    0x20401e060301c0321040d28200c1c81c0d0458680c20081e00c10f80300060304001084040c945455000d2000c3c0141d84c3c8240c0d03071140100c1c58010140c2c074191100707620102c241d1600864140e41d540010320300064900044011a466010030142018281d502c2d1000c0c0140110a0070003003040141c0b001407082d28030070f23211401190198010b000300c81c0511800c0c440843c000c030804c86a03d6019070015010700054101842c07030300303480e020451a452121404800030350721011014910071800e024190004004030000c5003801c20000000301101d80c1d000020304001000200e65500d9158180c0c50302c003441c2c004000b03101c071008900e8002d090742d1044030b1090b5035443c40c490401d03885450740340344042c4240040c5168104680030003000003d9100b14000c980d1803082c0300c1c0d040c0058032303042d000c03500a10041c0c0c06983c449180d401c0134048108000c14070079070140b9108a0004503a006084603521403d941402520b5010850040c00101074004001c0c2d03000c8040c2c0000074441e00000000e04042d10507a0a0300c209441d01311 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 204424046 1250 204422796 204422819
    0x90105010605070c060e041b1d091308071b12050d020d1d0d0209010305160e09030409051503010f02130504020301140909100e0c010305090a0b15040213180501 70
    0xc0000744400f0f81d03a101004217602c0350380b60150503200200001400a0304a031788180e0b1040d10080388011800d810b24100e00d0940f4801c0140130500d096400b501603140c0310044502a4200440041561402207200024404103460000c11350700304030801201e880e120012407100403142c1004407420301c500310210040c07a102050038082c1d16001c3e00c50151942003050802c100c41d41c9602c5054200000c0340001c40582c0d031308120b1600a500403009007181000403104014040003d0704040184d170000710511090b21400002c030780072a84046000191500c8119811818902c000d51182d0300d582069050f40040001c1d03070045c1a14006c1d030000ba042181d44906102c01c0e40000d114189078510001c4409442d400c0203001d5590002d0020152071281a00440a00803161103406c00c9400340d00440c1201d42950b0948241c43d004840000107100040003540d400c1c82500000700a07680b50303950b10345802040c0c0c42e5501500d00510041d8030201042e901c0c1d4419035640107403014003d00071410300c400000c2554616 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 204425296 1250 204424046 204424057
    0xb0606130e0c09030703080d05160206040b1302030114160e01020c04020f092e08040209070c0c050a080609061015030203060604030602373014090105010605 69
    0x10220802001d00d0100c0c12078880301e00401076120392204200700e01044e0f6080c40180095440b0341452600d5500040c180d0b800c6540003041103903440c20021345400010340018410350701c03a078003803c0e2000725502c0349000c80b0b500800781300007900356007801000d118070030300144018414040d0300c9544040c418101e4044800301c400c03d106a001da04184001105800c05d90010010081c0484840d40b8241c556400701e401c4160020798a5095050780c40c00651607021003546030825000c0385404001c60030306400181100c0c401401d06814482e540f1b414a00b0882180411070080c58020311600500d50395020031038a81710102e8900704180100707400512544002d000d00003c1c0d6140418484940034003003810343c000e600c007400940c3c0c452004d100002c0000c402e4002000c145556000608030b0022110a40008000401c00210706041c02129400c4103544507118211840c15039041004011800314180082c050004c540b00d442c0d410300c400e40d2600a00c03106018040c00144008000301e80c0d80f04021030321030151 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 204426546 1250 204425296 204425317
    0xf010206012907050d09180b011b0c090e0309030606030109082a1009120201050c0d020d0605040e01060806011406040e0901021c0c0e01090b0405120f01090b040b0606 73
    0x100d103807510100c2d08151510244028940ca058500307402510b440d8600103c0743c1394040084c5c2c110301c0600446241e00072071500f0021142c001c0c031110b00b45a001820300c0c0300c0c080c8001c14aca540100004188450200f0500c01030050300030410240e2407400c0540e40304e50054400f84d0192040d407000c10224101407240103109904034103010f080012000321068001c0800e40c18442e10801c641ca0748600d01002e00036400030f1401100001445500e41c030b407288041d01c41c0070864041d645000c0410121070b03540412541020100100181d1780d07000490214003d10072504000d41092074140c80c6985031105501178015038181313804840b0140c2c5e0751150b10b04418406c01e01d00303410032010300040101201d841c0b850b540041542c8000350810303140a0303070158034030320001c2003c54050719030200d0564a508070202c070303004800a20b82807200500789031340c0c02d0325445903214460040f00003a8101c00310940a0084074191002d85d4024001c4107101d041aa440544c00d4905550340c2607100702085040c6044021140d4020700b = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 204427796 1250 204426546 204426569
    0x501060512062403250f0e090c0f040204030b04080301032609011b050610030b071803080a021504050705090c03090c0f03030f070803010812090307031b0b070b04020f01020601 77
    0x242002140c003c00c40740306040e6010311800d020820001030b020004401207000e040ba072055507103030644085403840039902040411165406214000c600800d0351000e85105481c4000070341d0382e44022038002d200d00e034009880558017409220400c40d000004504803400f880c1d92901c003080d1447e540c5801403181c8034a01c080001042002000c2d40115101c10901d504680041c207000000d484041c24402c00319032550702e10407181024400c000b03024803213a800000030700d003143d001801200c0c0c080c5818600d001c054400b100100c0c0e8254864400c1020f08460702049000103d00e04243c60100d64802c254090329106424040014151090081c280d038800d0000500800d1491030480500c56685146d445064050108110403c240d80145004011103486840c01c40c0e83d9602d003141113818010400b98000f8000c100700048114ad98000460400340c0341c0146017522200c0a5010300b00d0300303c100390b100c00c40440c40881d0350020b00188103c0e480c855070095580c05807205032035004a8440e4824041c0781c1c030320030 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 204429046 1250 204427796 204427831
    0x10207030f0519080721020309211c110102090d0f02030f030c030903070512030712030603020406060503070e0111030f160804121b0612020a1b050106051206 69
    0x1041d080400803075034021015940c41400c103944000c43c01c40394071001d039405032000a50380c080141d00c5110303d0105120004c3c0d640c1240703e01c0c500030344030310807400000d200e8501000c18140c040310b2004003c1d03001400e88101e47d01c2f00d005280104440608540344008144802190604c00b0010b000316403c006000b061001030100700d9985809026814500303a07010f207e0000b010315480d40800c002c00e00940214021600d41c0c804604061421403d40c21050017a10018480c513111321001058441070340d44810007101091594200f00c1c010310142e40080c0d8010305100300080c403140c10100440c02440740ea0340f400f01c03c10102d0010340d10b103044080b4096540d442000f0161240301c0703a07070180c03403000105500c8420b6100c00742c5462583e82c1141d0080d901400d40c4100404c1040b0b250000350b001c2a00003199050343c0c0340340400c040c0802010b082c44102d050740004843c07808070310445950a0019481d117500b80344071007600b030580c004c00781c500640c3c1c01200c0034101206000c0b80050190711805220084000d4007 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 204430296 1250 204429046 204429053
    0x3070c140115061826010e060c0d0c0203090f0405040f0b04061d0a120806030a02060c010507030b18061c1217090c09010b07060b0a03050d1d0907140d020a0c02130b01020703 76
    0x5d0600d0b1910503007550b840e4020704039000c06000c81e41c0644912100140c880c01d020800b00c0481d0034036880002954804c1005040341d840d01c0c03107c4a00301004030380c001415662400e100c0c14102007210002c000c40c1107442000704000190340300d006c661294125240c40341a03800c0d10266109a00c1d0006800c0842c21440109240e104103802039000741c0c0a81680c1840d00180e010034000c0d00300c000c100b85265101c0d0200100554148166110801e00b122425680c014801141040c1c54010b0001401022005248900c000c9540c2103015256400030b201c002e41000310000900300d035a0362850b0403d40c94600c0210328020310018204601ea080101505c0700ca900e030643c484080d82c0188000c481c0c241d1540401040c03075030b60b01e54074402940034030098200c55641c3c100082c10f5003041102c10302d201104542c001c4003920f41c2c0d0381c03082d402107403070500c01c1c05d4601c454095040e03801025080f804140c000220581e01c80c0d0310000841e0390380e100f6182111018150088041559a401c1213140142d002003000c0011 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 204431546 1250 204430296 204430349
    0x708040503091e0d0602091e010504030f0f0b0a02030406051008030a0e120d08010602010606081003230304060207060e120d05030c040815010303110a02030303070c1401150618 77
    0x4040101e0318500389540f020010669041402c0070a075201940454035215a0a022404122441c1400c042506c1c808500001900f2800b990102074007401c0e043d02081d04110340c500782c001e213682e0040781800b098580020a88044e50046a04640e41800c150200d101c4103042594501074030325a201440c14110784200c1116049041c91010760f0000d030003218451600c005000380c42c220301071940c2e0030384158103200303000e0300b5507406a025001f044551420842520b40b40400c00d804d9030362008050000d00360710b8007030301080d1021202100302c3e0b010020b400250243c0004940e001c0b600240c0780d0441d02c01c016010041400400c0e2134190307107034224289980907a840392000315800b00e48907a081d82440d840d03c2c02c040c60002030280c5140001e5240006005250300a030304031041100301e000030300c04c030820390307001c039459020141060381440000d0803402c007040707800840e03008001c00603c000c115500300701c10505071440b030314441c0b0300100325440790b098664004042c940c81a22180301e00d00c0492a60344100309c02 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 204432796 1250 204431546 204431569
    0x160905030d03180f06020c0d021207030c020315090106080d0e030a020906061605010501061202270406030213090b0c0a140901050409020309010c030b010903110d05030705030a0c0605070804050309 86
    0x1150043d006280d00003014601c65650f01800b171000140c40303c0d202e6800300e142075030500c83d81c01550b00000c0410881e080010480d58850380c94a400d4251403000d00c08289405030442c200300881d28103200700003104105500103012107503024120350b40180000c0e001d445540003480c0d03c0340c140e0409408400542070410001e9080100a0030f0b05280c81c1107482d072a50f51a0884c0360403521030f51510010440c9030b034131080c6403060001d1483e086281c4020040052101e00c030b0300340140240340038131400300c117542d8075a40250000e68010f8031055001c2c00b1801c01c0001018012000c071143c011240200702d0b2121401c0940e00520b40c2a1101a0980603080003200d46401110409040260030080400c0d0401140045d50103400100c4c004150480c0f542c2d000740c03d60310340709251410005440c0003003003c00c141401b12500800c043e01c9591a082c66401c2090540c07040400181c00c2e803000013040f000301a4041e9540300d540c4d0089000704856102d0402c1107400714800e031005801c6038014000f00700382e0314007100c4812 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 204434046 1250 204432796 204432821
    0x3080f15060f030a0c09060f080a0605060c010203041709090c03090c0409030c05060105101b02030a06060303050715090b01030615080d020f01050a111c150b03160905030d03 76
    0x404401500041c419501665a00310700c0d0b00301000313000c45180c1d03e00400b00160802c0c1480c04405060880041c4003944c100301e44006c102404010408035619940010041c24024000c80d545104060b2203e011354020740701100c0b0b10040300e17010100d242c3c032a4180c42610030b0051400d0601e442e0b101c64040641c101a144103002c1c02481c014040b150354501c5440c5649200346c45e04004035410341060303820305005074451030003541001c175402c68142e480351070700650035046a403682c240ca6150002c00e00d01019540f0007010203140020103c241500640078100051040950043e20f5140302d9829040c6d505640006115407601001400003c4c004c0c0c0200900c02c600104840307095644405991410540241310405a082861052a810000c2c02103543c048180030b000c0c0140021100084210f00c02e01d04110006204420035240c8070308940c108891031200c0549111000351a4007001c01194400e9030040c10b001e10070f2891406442c085d034803540444500501800c0c1d040c400c00d40640140c0425a241c8 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 204435296 1250 204434046 204434071
    0xd0e1e1002070905040b062e0f140705060f0108010c0c062d020c12030112020f03150705040906080f070b2b240b19050405061b010b0d03080f 62
    0xc41d906485104e4a4452400f0f00545803071810180b00f07101130003c0740803601680c1102c50500c055412080301c01060283c440b8607101d082001585008c0b18007803615038018030a414001100310511800013a01c9005a081108410300c90760394009850803540d0154266000c01d1a01078480007007021603011511070740c40c0d0940e00d40a0481200090b02906501000d40d0400b80c0c081109049520f040000800224110318070b1450355042c85500306071000c00c180020300c40c151241c41040c0e80d03141800400c400c184444402c0303d040c20310b4407014241d504503018455005d4a031003400155410001401c0440214a1001d4017001d4180a070f946a260300c00c089102d4202c0c1401450000d0440f04008000c003940780c03840000307622048007000002034010341c5d004c03040c0fa41a15030a0250f40784103002c40d640e074002c0d5050007600c1e0440c45001c2c2c4032809913a20141d8000c01c08208c220743e01035034081200e5030781c11200080059441150401c1030914002d040900012118070025041403903000e007090f01b181400c03884 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 204436546 1250 204435296 204435299
    0x9060c0f0d0e0d0216050904060b180403211a09100503151005060306010f03020d06090507020c1813080c070e04030507050114040206070b1302060406020d0e1e100207 73
    0x700b034440007a000c26107070b4001d0081e051002d0341805030054951550703490800107443c00b40007600106001e803025041564407440e110656440c1c1c402d04200100000b45900286410300300900110102c10051a41000c000e991003103510281c41070b10b10304600e0400001584082906004000700020818480840b0102d00032840380d604210f003842c081a04044050035103080a030309000c009042e80314902420040c418084117a812035121042c1034668a0b0042e140d461002c01680a81001e501948007241b400d0180030a0990109035200c0324441610300030b000301c01c0c10314456201c0004851a9003907011280b84500041c1c908001499000310480403a41d80a03141ca402107210801582c0440c08140005210800c000c000e0268070311191520b24246140c1c989500407a05610604900404076180840010350b040d00094400c61b210b41c02825107900d0b580c4a15010303541d850202c81d103101044035060088000e240010a0030000c039180b1070106c02e46402c1e2004d002c1c6a100c5d210a0341c0950050180 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 204437796 1250 204436546 204436567
    0xd060509071815080109030801050603041109040303020c0d0f1e0302041703130807271d01020a0210271412040611060f06090c160807031709060c0f 65
    0x1040c2e03100d1241800042006205075800716003c40d5600c0120141d061040f086d011a8100e40654112402528007d41d6585c5502e010ac020180c070807406940a2005000d00040c15855805452000d154000b21110b10620000981e070201980500ba000640c01014030361120000c184004511545400e02508142e2a03841e021800301e80400031050b2a400854410142c035280c0140800602512000d0805d0314103040081d10510403c03c55041d680031540500404488554464269060500042409a040d504003e4041d600c03520890005104488001c201d2400724441d1540c1100900c1d2408104c5440ca010840001100b40c02038628800070341012142c04402e1000b020354103000c04510743d03558100394002d80500340004042210398024420009202101e060303243d0000381c12282418980c4c1c5502030551709200303070b001c8403014030040004041008000b4ac041d18140f1700c02d0316051410215045034500c8400c080f0b0765000c2541c03150002c00d5118044038000c100400800f05141c0c5004020351 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 204439046 1250 204437796 204437819
    0x18021e040228090501090b030105041a03010c0206060a0b0901020a060f0225060f051303110f070603200f070f03020c120f060f0c07030e04060504110d05010b090d06050907 75
    0x145089111800100003548603603000c01201c01904c002d0034030342800c0381808004a2580014000d1034003595075003590000508409820107400c2100500a004420040400035140e00c400d588a500030400000049071074107014082d1140ca8006a005000b83d050070380360980130f0440100045040c5078204040800020980d0310b00c210b0305185011411549101d140400072145d600800010380d13442c0009000c2400c2030800c8581010340c140c83d00300030031444600b1060030710301c101902101034811035030001011074141d08000d000c04c50040301306141e41d603002d4080c0e081303116111480102d05010444080054407000740b5444050091040380c0c000104000400d0040300c240040d5440e5070f0092207581e603016800c024150303002c0581f01680219080041032446180583e500007400d1141024401c2c07480d45860344202c008280041007030101c001050700c04000d44d407228182078091401c00303001140700c0b0186002c8031f80d0036001820222920425403181b41c018680503007c4851402400e04c000368030007505 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 204440296 1250 204439046 204439087
    0x2060708041e0303020d0c0b0408070203011b030f0e0109080703140c070e09061501140703020102130609030b01061b0807080d051501090e01050d0308060a03050a0f020418021e0402 79
    0x100e560016a055080c0a807503c0c0c0202e86000401604540707e000056220301c0c80c0d50000e03070040c055a110310691000a015243e04240c44005024078045070f2400341d415000002e00386502c4404002ca002c20305242401d80d06003183c0500098020004240001e00c656400b050b450f403030505181c01e01054001b00e1f414008036511200c510501a0141b00c6966803c0c001c1a400001211610000000003000a0143e2004c082c82c14444c4c3e20101e907010601d03000b90103d980c42c45040004648030380c0c940d10003403c2441240400d8070070420076800440c003180501520013002410025a20160600e6a1546e5090b4080c0c00100c0d0100001d014910240301c050092a001c6d10300c0c0b410900d00178120b00d00051a076612540160841c40c01d10004128a4883d440c4032f82d889a05440c08912031394400005c00c498003016030009100b07100c0d00d0484411303c002c4000a4030210320850341030103d141c00519076541030500b0391010354005510000c000301081c04c00030701d00410308054009814484480300c42481440907 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 204441546 1250 204440296 204440339
    0x3040816030e010905090f070f02030909010e16110303010506090414040c0302040b040225022e0810240216090605090f0f0708040f0204020a2d020a0206070804 70
    0x340b0881d00d056800c44480f0f005068103071220600c0d440e01c00d003580c0709a080a40a0410f10a032a804009298420304c202c0d082c0da04003030940961541e4505051001480850341c40180049210074941e281d840340e08011800c80b0408000c5045034200340401c85254400e141b4136600568407008500070b040340802d5548940e00445a0321103081ca90300601040d1148a10310604c45d0344100504c1460342c490084200ba9501d044480c1281051184045246418504210607035200c1c03000d82401c0c0b0340c0790894210035255071a900e0400a0f102d1000d60b07032490f002c0340a09550000d0404040038000f2090704901c8884503036204544940843d100c1c0c401004881da00a90000f50300e40c0001c0c44141001c424540c1c001c414240e4100c07042ca40200c540400401c040c110303508000f500710118040c001ea02400c03812040c0c00600440d920207010501801d845908031003012030000c06880d114688000c542c007204580341c0c5030003030150040954200300542e0700c442000c80e1091018003000c40c40000848084e05039018 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 204442796 1250 204441546 204441557
    0x2d0602010209151303060b0d0501060e190506010504060f180b0409060b03010605031b0c0318100e012a080d050106020709180b070e09040b060a050a14060304081603 72
    0x146080c000940580344020112010030400f001c0c84018207002181100d4000c8400107c400c0a0070014042c8980084042e001c1d60808001043e5400b2032041c00d0b0150380441d40c06200514070b881e15409503a8102c0f146400300d00140710401c420360081c44956080c014910b445080c181e0390030549001d081054008139410381c0b000c0740c203001800d8684103030341c0589802c3c800c150441d0b160680c010280d101c0140b41031500124200c0c80050914114242c411184208090f243c550a8148080d404e400b204c0450390700c01d64050b1340c144884e82c0141c101e143c1c2c40d18180c1d50480303441035003040940c12801803007250f6034981004000902207205c0700302500c00701c1305207440440c0c5940340040c001e2a21120350070596089181406250110031980d0801911540c0101011510b5617250401d544003410007a509030001840e4040104109010001a21481048492019094071002405000c0c0068010700044400e4141c100c5021703d00b150142d0b60041c0701e0713007566203814145032000c4a2042d400004502080 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 204444046 1250 204442796 204442807
    0x302092206170c01030b030a240b01050703120e0a0206120403020129040510030605090105010f080114040f02150f03010509071706041d01060b090306090a03092d06020102 75
    0x14500030200100401c05414007149440c100d010344035010404480d041c980c0e03410340544a510103110b00b000380d90b04101910300318203001194272815038401c02d083d1049403601a2040c10b030740c010000d8411880c0c15517100540c441c882c40800707005015035038a2048a100780c071802c0d8010b80d280b9000380407400c01c1119001c046d0038649070190944003400c000307520000300d4148142c81da01c11802c00300b40340c0c2c03c11200070600740c80d03600b1400c1d055070654001a0610742000204902d02405400c81e90496003441c505042e059a110a11070803998000441c0920400600c007150103e29900d121089541c001455030b0128106030b200381401e64083c0e42d5401e814a404401081036161845c0c015074495240c0c00c150702e10754034419180e00d000c9801040c1501c5076581d510201070501c8010b01d8000d80c00c1b0701c013000b000100d07110b1444a1642e00914840345c401e118810024800b210041550080682c0c59100c90400504048034500282a030425955202c543d0581c01d01d0f60402241c481c00003001e03035400042c0c3c0ca6 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 204445296 1250 204444046 204444109
    0xe010e151b06070e0d0b10120f03080a0506010c06051509070207030303050601081b0c0a02130207020f0a050d0f110a06110607081510030b120c011205010e0402060703030209 76
    0xb440101550144540c2180b0410b00392140300041540345d60000d40310ba5242c0d07400c1007140200d40705400220b14403001600700400c21100d200c601403458000d84031441306503241d1000030240c40f4100c561038001081c90b1030401c00914030788c101d1a0080841c4c00314a00745140f000c0032402c408812a5081e006a2041e5402c00501d9090301c81d80760401c4081c82c0001161401340e44030700f42c03c2015040300326600030014417a104000d0900c02090050380c001d0502c01c0b13480e180b0364040060b40010a040c0d00c281000794000c1210b140440d5070300b088890141c114044410030b902d951582035641032090302d64500b030380140034803942c4804042c0d0141c1481e882d8042c1c6100c8044d030080c41c0190007401c09040c00500c906209041411030002801284221006c003108044c2c400c0c22005040e14202130781d0031810304070380101c8504e0041480e44900c10282e0340d04005c0d040310303040641036030401e1040300e00000301c43c0c0224025042000090802034000d050143c681400318002c41e02c6148040c080d41480c406030007198100 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 204446546 1250 204445296 204445303
    0x3011404031e080601020a030e03190b07110a17090105040e01090204031203050402010822020303030412030c0203040308180d081611010c021c0f0c06030510060903030e010e151b 78
    0x4081003032803c51401e1510b003001079070300d9040d00c10203000d210b6000e0304c8050664003006041c034091002c915803440a811460402c640180c26a601c00109440305d944855500e40003079801d0200d41c10076140000001343d40a03040c0b207640620744050400a00b0403010540d4061303040c00030300034412a44016030720b41c40c5080c032940742d2400340303c2d003020141000b09020250380e002241d15004440885a0070704004006000511154001002501030002000308020302080084409500f1002d84081c0300703039060020101d840348903170b0000601104092018180300d0080744600034201c0e1000c1c11042c40760308291215a00f0b904000c5400380c1403031186509004000d5980c040804c104000c1c24000c210b10b41c02e03030005175100100740030040e02803042d001120500001c10719030092550400300017046151179400003405800104e03640d095481010720300049007403060350604100c80c2c05542d41e454407409100110b4842c50f004070708540c0208181070401e0700c60400401004801300305c1502c440144801b0045a09 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 204447796 1250 204446546 204446597
    0x62112031b0906020c09131211150912040b0a05130302040e030c01110f0a080417160c0501050403031202030603070b04060c0209010524070821091e0c06090301140403 73
    0xc0b0f0044080c00310541c07e90b81c2040c06690f109071031001d1000c12480c00c44000903040c06c0d0001034840c00483c815001c400040c030a008800007801c1d5114800104180080c0e84110f10403050003007010040c0112070b5110f403000d00241034000c03002d09942a900c4c2c0004060328600d0303480c4002a0130000d00300c01390001c02d205a00607d84424649410444188030742c503200d0081004c2c19041c03010640000d42002800030401c580c415031583c14a44921106d02485038500e609801101c221120180c0400c2d5580502c090700c0840390b05a4402c01c80e01d07001e800da9400307500040c000c180c040c8503103031010070340d0404500940060f200595440001c5441c5004110310305c078040c0d020500801d140b244001e0b100c0f2006114072411008941c0300c40c0d5484943c80d0406181c4a920300b0840d07041742800c28075120046218006018007051002c48440600403447c0c00000481103203407125550088124071024101180031308100c040040002a003100000d00a0304054811075003140080c500050a2910b511a02e038680c8 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 204449046 1250 204447796 204447799
    0xa2f01020705011d0d0f05070e0901091e030c051b01020c04110d05040c17010606170f0f0702030708030c0409060b03090309090414030a020f01062112031b0906020c 72
    0x5207003807500300040c10031044045180c168000c072606501154903800460000f199022a103065150200e003402034451845003d001c0300190a20082005048140a04c1000c01d822845a0142c06650005007650301240c00084007840505918180402d0043c4a600308043c0c040c00c0f09200d0001034000207081c56840b58031207201390b10f80f4141c4108a800c003001d0f90907804c081000041d882d1610300740b952114003568403c4c400761003035109a407621003042d0400320844e0080e443d2129070715205580304070104d07400c0300c229444018100021701d101910484058224802d4010b503840c289070340e01c0d1440c03c0c0d0320841d0203200312100080c2c00c01070100540300325001018110380503811801c040a43c1071b205d02c6240c2c0701c0c5100e00038541c00b24051010000440180e001e2200449a0b9108203039006500e4440d601203c0c0d01c154030b4200000b500e08500b0034440c0c0500c40100c00541020030a80e070700c2c410f400103d842d160800d80d49100d980d4402d00d0088180c88200038a45608140610704880280f41218058409 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 204450296 1250 204449046 204449053
    0x501061a0a020a11041803030209040606080405190201180e1905040519060609050a0902040b060405030d050304080d06030503220b0a050d0b1302070b0105090402030a0201050c0a2f0102 81
    0x50301c895000c00d040c154654024070302501c660440001030050250750090300d060302445880102015056401018210016202805034582d03d503820744c3c10b50350441e4080c0039500b2107804c0528500701d01000c8115148141000307610342444002c02c01c41420603812600c00748003240c0c107000006580100350a891890a24240040c0c0b03890396401d134030349000c038000b081501c07a04180749040044c15001403002d0499008100b006141c180101c0c40a0300181c4d0303007039005926044e0801076904081c021903003a0744000c0d0082810f0b46444004403a194001070080d581098184006801082c041c00f80138002d50240c4010750300c5402c05040c6200d41b400c40611881154034a000410175034400700240e41c00d02c0b465040c440c0d203c0b80c40c0500000a4150803031800c2d48520308421400c0c810045a010307221180c0107003201c60ba280c2e2100244084001c003600c1c0030794142e0200c005a401588207100500489070094255410b044a42d41c640071481c01a01061001c142c4800c1114581c80613039100c020303c00b01c2480103 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 204451546 1250 204450296 204450307
    0xb030a27031707020a05060f0a0f0605010e2101090303050702120a0207050114070c24020604050303280218040b0d0201080610090803030115020f0a0b0109051902070501061a 76
    0x7510a00c844000d0300b041c0e280c01000604054000d015a501c40c3d9005800d49946161542800b4002d02c0c048485001e024940342d0b24441c4440d00380300e0b81c0309540c1c040c0c5810103e00000400c10600003080e40c04d60144001c8500d401301400801c9c02240c0c0424882d032404205801c5c80c40010741000300003480705101110600904000a40c002440e000b01e46003802c4c041c80c1e03a140f8120504030341c4103071400a840382c600b0707103000502006060401c1c0e51300e41422660740c241884081c0200d84509054402500d0b0340e20500100d62050814140c450340707100e038030909480801000c11030344141e070400c4040801d90a0000321541807418035008000d8030300401c90381d04201d00f91950002c0d0003d4009480075021311310400e0042001400355601c2400740c0b07140c2c0c048945941c0e50346200c41c40c181c2040240b01c0140180f040755050f50100082c90001d1075886000301d052a8200050312008000c000e210814000c0103030140040c1415510003000b02d0780c0a5000440c0090a0420345501c03280350036a9003510f203008218 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 204452796 1250 204451546 204451553
    0x60e150105180c16230c0d080d0c0309140d180b0a0f18081c0503090304031103030f031305070501020d210603050610030303050a050c070f020a0b030a27 67
    0x1d407143c0c050046a0100d40780c08030f45441e8030800103001d03002401201001c0c0d60b04240200ea10384142d80451410860358650206020700070454007815004208030018015074001103401d0300040b04807501880c0000f0021001c0e2250f903100700c480742c2c0b00038040c2c11820b00600e48681c0021880b452105c03000340b502c0d02c20714000e160074040c0700304542d0728208207112402854587c1b00d100000c0030f040d454801102241d403180440342d1200d9000040d800351041d5140042e4445000d01c0941c2c3c0304001e04000b4505103891911055030220f004074030709030b050000700854414001403001460055020071007683c0a13140c1464000c0c42e082640d0449030540d4080c07064081d400340e1000f1000b05030345900d07540d40d0b4180c40800040001e00a96000100380d07024800802030800440c0c210101128040e0fa0300340110b40724400d0640440724281ca070325100355420001d540c081042c6405840300b0920140100d060550307100c08503201500141c45000200f174a41c1d010f520044000046030310b0031a500f4084150850b41e540e03 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 204454046 1250 204452796 204452839
    0x105010e0a0302060901143108060610091a09010f0c050303010b0c010e010906141b09060a050d05070306050102070503060609010909050a0503031608010b030f04060e0109060e150105 80
    0x200092044e80000b52104259100d408441a9a08001185601d5004080300488288030b0100c02018898071030000310740d451001c00c4a1412180400c0c0070304040d8880c10284640804c40e124100f003807240070301e0700040f140070703035100c0d5508820068803058030f413501c10000600d110200a640700c00c1201c640d419902255011040380c2c115400d2522403075841e03000c40501409001b002c64003032111751030481d200c000d201040d0007200e0145000a00e0395590740d20040c1d01c2c1102c200701082100d0a407000e1141e00703820b00b8000c00914418910303091103400c2501214503001910030444554000a840da0020840c0c0c0d40c0420400c8042d00007100682800d140c00c8000c9480000b052207214002d03501d914000081c060705105880ca0140c000081c1c960ba0702e0503101d04000c00f00c004054000144401000151004882064a00400c1c660103e0300280d200d64407004080d001c028045c040d95565030b401000010003a1040d004c5000c00c0c40c014010708120a80c030340030500e0f0140d100c18000c007607500c00075011a003801c = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 204455296 1250 204454046 204454049
    0x30c06031a0108060310020d02070606050909070612020d050412120c0e0f011b0c05030c0a080607030b0a050a030b0a0e0303010602030a0503100e0f061302161103100504030908060105010e0a 83
    0x3e00e0034004566440c800245050300f00b800d40d0700791901c0007c251040605640050054034041c480c01e0040079070350414400c0030751080703841c0c103000d8001c00414002c0600c205c45005800080110150825803130526020840c9da0964041350104070040380c524000703401503052070000341524803c001984640101800300064500e42074404d034803130034050061360301441c03087d80807052002000e0496409460001c1030315916002d040c3c441e1142050f02201c900e00b290410043e650704001900403900c2c1c1c1881a4085c2c52100302d46075005403810000700703c90715410300210056005100710030090801c3c0300c01c403049945440740120140c0040005010040c0c0010440d584101240b8025640e541e07448202c110950b6203411010a050b5000c043c0300ca00b6456100981c00b44104035a240300c0300200e100e00138201c0c4600c00c03301030f5100b1300ba03103070001280c04401021060000501a03910301d60b45c0c404400c0895030121012808144c01690a000440b01080715502410307081c2440304541030204002500940203 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 204456546 1250 204455296 204455299
    0x1030501050f0121060f090609110d0f0f020f0a1b05070e040819030f1a0a1e0902070501140c12041103010e0f1c1806140f030709030c06031a 62
    0x100d840f50004548050300d90441c0d1300c0c0780303003082104989070051104424080e10030404483e0a000002c92907120038802d44880e56500c0d4482d514010103501844040e14210300c0d00210207680d000b0291292015000034040c41c010005c150380d1310b80c0c1e5407a000e8542d2a0500801e28149070383d070030803400550300103241401c0d644c80d600d80004a59a51400d0440ca224940c80c03400c1070030219214586e42900354114500380c801c1c0c04d4003401126125110202403032000d84074154020742d80070b4100b001034046d06072426910090410b0000b00c5884600301c00c26a40904000c44546e0356a80c91030401e83e040030b417510b030016900e03041c80b890f00740d1a00113072a88140150024000c0d400e904402c8040355401d61203030b86884c0d0200140c1e441842d000100c6510383c490103c003003034665070036980c4a503483d1240300010b52005210820b48506400e0a000b100e0201215600400c0401c0c10840d10056406800c0a5440f802c16581c07031149450951a10036150155984007400b418181048201740c24050144000c0f190300 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 204457796 1250 204456546 204456557
    0xf041407031107051b12010608060402120d09140112050f0a0c1407120c1b0608010902070203032d030c07020a0905060d020d0206130305030d0c020c1f09030b070e03060601030501050f01 81
    0x801c0d40000303c2c146e8125070341c408550f1070142c0c00560040c000c550144654000c860300c4030900d0481440c80e80b0b40480412a2000a0080400340030b0105040013003030b0140b0040c90800e9483e5030151400044070302c00c0d544000c003001d400c0200b0004480c94041c020302643d042c6451040c000c21000c01602900411134000e20507405001e003d8021480750f04019201500490b083d1440440c124500210244a000701000200c0d04000407902100c01c0c02111480c6601400842c41d012100100109184681410403845070401c80c1c0f0704407a54000c405180a000008041507076822103104200051069038031241015041c0b4081004503541c00d0384070007555805580042da0603030107100040d07851186007a48802502d802c00040705200b8004098001d0110304102000610000c440c160380d00c4502201c0d265024901c3d42f0313690140c112400d016240381c942c80c01d080880340c1d202d87d25044800b000b1100500040d4658500200628080007a1608681d013800c00b000f05504003004528807001c1d10200505020 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 204459046 1250 204457796 204457843
    0x10b03040206190f0206010609080705040e0705030f030a0206060109050a090c032405030f060f0403050a050f07080304021305010e0a0902060d0f090b07030c0e010c020f04140703110705 81
    0x1102e520403681070b41c444480320503401880d0b0102403c60440760b4120001407048000205419008840d4402612402c00c01030814500d09000c2002400d08040d8040300343c05600742c00101030700d04000b4409081040340c051a107a01504a00070b240085c010003460405c4402c01c07041060782c880f82d80c8072080d41e80701b0341c001c12480d070181c1c41940030785107808842e9000e0780f41c603403e030520300010a64501910421026120840d003240e54070b598550007514402d109041440100d00000d0198004013a80d003040d007401410814400e000b030b040d0303400c64242170311403200010801c0b00b1454440c0043c0711f003000200b0108a2941403000100c8000401002d92940ca69100c0d681d00540d0389003000d0f00da000041c4001400040210300040014100078203040f01d51442c000041143d660090050001641c000e55400000106d908011554001c00d5030b41640c02003010700c807a1070307a6185e5024040b80c0403400d2000241c5403c20b103800600b1520564400820200244850400103502050403841036010f44114050722 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 204460296 1250 204459046 204459049
    0x1080615190908010e061b071e08030f070315150c0813030b060105032e0e090f0f0309030c040b01090b0c0703150507020d0c0c1e0305010b0117010b030402 68
    0x388610702464403099500503001640d290711a014000340c4402400a0104c0300081a0303081c0c0c0d4810684084441d81100c6d0301030385d80140c4840c05001d21a0007400c03d01100a100075816100c58800042520201c50000420100800040d800c41e0054050307e0200040641c107140c015517210035000d00040d04480c1d10f111070140c1e1107400040c0841d07802801c9550340710f1050718070100c540303814401200c007420620006510b0303602031f1065901c03642403421442d0240c510b4881952041e81e038400ca8001c10f1303541d410f001c58100184203072240710f91402001403101c5800040390a20300440c00320b6030101d9a00c2004540450307180030841c01d122050070ba0b404074950b5066001030328060010b405c0400340520202c1c1512515400296610880340104580d40c91814186950340c10b40c6c004460100c0560701c82900142280e200348005008280244400b41415480d5030810b06094040d100c02c0003469001841802803010070722a14001c031400b400c14200c10014202d0407404180140701f40840d08002000050a5 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 204461546 1250 204460296 204460339
    0x1205040606090c021b03010606050d02090103110c1b090601090e15030f1b0409080418110406020d1101020a0f08090705030a030807081302030303010b090402041a030103140c010806 79
    0x107020b425000348000b15950b00d00071766420701c8254003000945020080e40107070406119501c103540041d55034604d4040ca00146d400694480c07113029041554920401c8804ca0884014042c0502c3c0e41c00686840c0d000311001011518100c900580710307007041414002c15a03000601201200c1c002c005902c40c030b03a05d00c404014002d21401c5403507054014110004d00c210000700e022031414444c04001d0012015150900c82112007e96009184404c00c020600c000d100b04801c0c80341e04600c00760b001c120503005c0400c031442070700141d0000c005a80102d002080d943e80000d80c5207001062a8000c42c00c0003e60b800040c10101c1102600c406c0c03110140100d11b801800340400c60180c20040c003140c0e55004145001482c00c101212100700081c4004045010000320111124040d90020300131411642045d40e1101d45500880132a079019500304000a06180c1500d5081085040000b005840b585142029081500903010301c0c2e9180c1c0001007003a8050307070011049908550103940600140c81e20840e0800c2 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 204462796 1250 204461546 204461549
    0x3180406080304171507090302040504020d020a0311100311070311071a03061c0b010501050f0904060801091e0b010303080402041d0106030302070f060e0f061209030c0d0f1205040606 80
    0x480d4040020b000c220030305001e4070491200d66400c21541c05d40c50520807060641001c0e5160340010f11000400c00c090b2400303030081d0380c10074002800a2440c125941c0000c000003056170040301c002150802341030319454440001c1d41c00502d241820301650138003460302251441030040c014240b0102100c1e00034414810031124000e0480201c01281406a400344404c2d503810496056109250300c2002c0500f40480b1a000406550b0010100002b6400c003401502c10380c000325512160000e00703001b00007d079078135402401e004100321000007401c0c0344a41003200b0f080385c414080d84080103150400c100041c40c90004d22741101d03010b162060003600c403803001030f01070402e802c40080b60003406401c80f84030000c10351090302100d210782c0840d081c2e5960341404105068041c13040e440030a0171038014803501e0510354554094048020070b980d1400d400540c41441118058480c41d00991010036220a078030405c102020702140c03d0305201c0002d17199894020003540b103004855204544413804a4100f0440750403100 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 204464046 1250 204462796 204462809
    0x114040b0d0209060c0f01110901050a030e0102090402120103020f120a03030e030f19171902090a0918030e0301020405130b030703140f1002030f070f05070c06050403110108010803180406 82
    0x20703600d100c82e40215030b503208160004035087d4680169080c01c41490000c4801111043c0c64660400c3c40b0241c3c250014503011034402c0195400b00402c49559840744018804580710b0142c4403255411801403041d0303140c001c41200c0c0a901c00740c848050300580016011541641840d01140c400d0980d4003650650050301001c51040c1e0300800c180d00280340c0c100d02005c00c1050760ba541103000240c504e141016410640f1406030b0303208048580f0103400415001020a03403000351000d080281e68030740000407a580b96200f06410700101e0707080c004056105000700322400d000c400a40c03d2500f440009103009101200d9503001594079403102501d071b181400b500009580100c0310308031040c00ca1f000c0c241c6505240c59048128007039801640d00990230781c401d90380100c0360152408001c6e0765003403050f180b04100d03442d542d050060600045001503410603803c0041c0c07886035543d50700c452852604601400350030ac0224103015241d001401420310000540300580d0b43c0c4100c00701c2401d6000d0103c2c0083c022a08100b = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 204465296 1250 204464046 204464059
    0x25020a0c0b040303020d020606061b0a0b15130c2a0b15010f0c1106030702150c04050a05040b030607030b1503090610080a0f022b110405060114040b0d0209 68
    0x9040701c05040584103d078002d800790344141c191048120b032600300446500c2c0e1b000a082c0b0494551120034001140000c4800f001c45140040c20f8541f44403840c82101e44500304400700303413020001d0401399214030f007501c1c00342030601264402c1100039245100015030003803811240b030701c400045518504e00c0b20b10aa0040c0000c4000c0c10100d0032f80e14141b074191545404200c503441d02e042480c1c0319642c03040c80341c0d4214800680d107d114508110043e031000e442602107204a10164000296200c20706000701c0d40c1000303540d51035207000c013401115112a4420f40c825813500950f6002600e0104149600080744d18001403281240000100c1a940c1d40100607243c440210400c039003c200043d03458016000030880c0d40525650b01061a0351f034121130b60003081044503900d450010704224040c0e08408d0504505040c4071180c018104000d50a003401c20703540080d04041c9442c0c181014862280c018800703207803810449141035120703140340c0f00e1072007600b0b80a00002410214101d80d33505896103144000c1c0235 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 204466546 1250 204465296 204465299
    0x5060a0306060905010e210312010608071704050309010e0303040b07030e04060e16120f0908030a0e030a0e1201111b01050603030403022b0524010503010525020a0c 72
    0x40c01080c25001e440c0c00320700c08402c0410158000c4421902c844801443c2440390113150115116441c4030a003078150f244001d0212049140803860102d01a240740d9640c080c0510784500000c140300360802c403a1104a1852080c0004078102100b00d980f040c0c802c1c01c204a005440b500070a00c0d5204d00d40c0098007000000c0380c010308160b400b804c3c401c42010100d5040c81107988400b8114040718090f9090114000713040c0c03420003194098401c2d84159200080c00185242691030440c06840e406101107484240c00010041041c03200d100d030034407600241c0015814030310f403001d0140040d00b400c91500e1051482c000c0198125400b500201d070442160080140c4804901e04104201e004518076503406500b802c0c0050703402d0500109440c21a03400a103170780316400759544194100d0603402c04c0c0640030414680064042082007081c44188940102c1500c2003042d407010b144c1c0301c0c1c0c40607007110740310785d0400d8107100c402950038550905401d13401050b4421928520310a03031034040c07090340080182208490 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 204467796 1250 204466546 204466567
    0x16021e09010620070806011203050403020907080124141c0204080c01020d0f020d081302041407030b0103050108061b0d0509031b0309130e0c0303120a15080a1b0506 72
    0x1070300c002c1142c0c103c1000c1500f81d241215922a02c19010790380103a4040c00042013941280c407179440b055400303814a0361416440342c012854409044030001e01107890480108941c0030300d1064813844480320036444140c1680c10b00018110001c000c0d04008800300400c0d200110041c0741c0c500c460910061008550b195600c0c14000e03141d10b18804024054024200b101a034940204842d840d6500707154083d00c96010600415190048040e003052070780402d103440840140c49510801c40e1782e1400360301c102c40501d802580103050341c0110508504040c01c1800400102000107000303a000109811102242410034007006840d0040c401001c074040d003407000f0f214080304040000c0824591808001c1c03a01c020b00c180490381c0b80b164150785600006400d0746042429101d80c01025101e644509a03082c812000c3c000138910b030050550711454030058070600c101228548650001d2215240c00400620702d440440c64072a101524040c1880d403541d5100e07100c500da480d41d4140a03090081c0700944540300e408 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 204469046 1250 204467796 204467807
    0x2041a0d1202070608040305120c071514060d02090604020c0a021e01030c0e130b040e030406030b030f011404030e0a12030804110a0803071104060504111e16021e090106 74
    0x104074050701600c500030580da07103c1e200c01d610450300342c2c6130145061f940010650321600e00501703840216009214501c0000c0c4060001d4507914044940414429104165601d416030003800c441d105552070075000d0010b0711048005540900125001030b264030080c20014204610f0040007944034850625004800810020054160f0030a0b40c0410080005960586001c12282c41c8182d011010503250000640700c1c3e04900441030002d44080f80d2859220a480c0c035540090700100086902c1d0507038411141420051050a038503c10000c0c0305486020b950504558000b81010341000814600c016403901d482481400030080000e0054a2400608000300044001c1d60222120b00900b1394241131860010750340d1b0155100701001c0c500d0103021340c3c1c41034103482003140361f070360400d444001c001010380d1244580c90f504000e88141640d0391090715441c1d0300074404464004581041030041c03000e500503681c0c00c0400345034162509444800942e40d442804405400d100b40d02c48020000801e6140d80b28 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 204470296 1250 204469046 204469073
    0x605270304080609150606130b13090e0607081f0b030a0504031101090201080109090c0b041202010210020a090b0c01021603110106060e130513080d05040314031302041a0d 75
    0x810503243d041c0c0304c800c0300503180c2150a000104030300c0170794041461454003500610382200523085081581d40c0c0d66120a01a03085200c04002080c00108100800300b42d0780103005d4039880c90340c0986103520b000030014006003030142655000c08210310b102c3c2d504101001d103a402074a85e400c0c41a40301d1804201c3e48000d80307001c9a0440000e207100e4651003440c04140119a01c80b6816140e0b02c855a0034480102c0052004c020f0582e0494880c0000190303a030501030050010744503200749a81410614000607240c407549500d100c83e843c1c0704007e442400c940c0407280c80e040d00e6203254030710350701d0807414035a130302a0068a4480c07c0720041e1000c0c0d07008040c3c0000540050315070380c40c001c2c0300442e039901c415145200c4045415400c442405400c8081c80c41c2030340030a603c00c804d201c036400d80040c50f80728003072260031600920206940ea02d05003c04d25810150750444416102000f900c0c62500020a0405040b410002805191101040c210840700700c50349200003a0701a08000d0b03011035134140702e081401071 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 204471546 1250 204470296 204470309
    0x31e0d0c0201020a08131d04032709050412020f03030108060103020d06110d0f0b0a051302030717100801050c0c1b0303091306090f0902090114060415030507030b060c07030605270304 80
    0x12591f6445c02a155001c0c52203180c05d600c95604851507024194090300030601003610b0280c0202010803400040d110f024000d40c055140c40d03292610303207a0040d20b401480010103040d94410300041110310b130005413840c15242d040c0e0b648240301c480ca16058014000c1202c540000640c045111741e2440d03044d0b40486810300c001d003000d0190384180c400348100800c0500506420070340c1a14000d0010466400441c4c0010951922030b0944048010b140180c900995408401103000030040080038401d026098000d207050300c2d51460140d005900954a400481a0407040c020400f15000b107607a080c42540d181030405040d01f070400a80380400380013407010340105101c5626010040440304118428080c1650307002d007000410b40d082242c0000e20841443c080e070b078072072410031000c00c110b41c41030702c407150000503a1404200d90810030030140503560108600c500640c8180103503c030324100042c1086c2280d0b04544002100d440310f00314200150762840c0424000340d00011880319440f03001004000729100d = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 204472796 1250 204471546 204471569
    0x10f02030c210709030201030504140a15060614070b04110909010e150105060304082b0b10020a080406051b12030118110a0e0303070b0108010b031e0d0c0201020a0813 73
    0x502451001c182c000d0b2041400038131082d03c02e00055005c1e610040d00305005603d020b01c2001c0c1300345072501c0d007900080d085403024040c00c9d100c0c001074018000e12002c0c08a81c1080ea103100a0550b81d6440c1d0700450300c010307080c0f440200228041c00a280301c03075015020081c0590480b45000803030207010f88500034007910f0754451400303080c2014000e0a211410798100410b85880c649840d110a107864208410762040040d4290352880300300d94040d04481c84140302400450010280000c00c0000300c440c0301b400702950410940c07440000d112400701c03400d544140c00c04075110030141500c13004142c070052078207180744600300700c0780c0c4080c85034005141202c002785120450350019100d0316050b24181c00c11043c2c81d910500002c40c240c4d000300c407001c14020014045a00f011165203414004010a905c43c01059554034540c80c0141424000d1141400e0b03480d074110f000007041c1500380e55612000000901700000b01d8880c801b11780c424010b080c25241c01100b42501c40c500050b0010000d215445401014107 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 204474046 1250 204472796 204472837
    0x80901260717131101090b18100203070b0604050a0b0603010b070c080304063516030b060708070b040311070906080d21050408090301060603090b0f04020d14010f02030c 74
    0x20104584921912150103c80741900055a0307421a0240040c2424184101c50001050621000c000350131328a1381c200340405084c01d64030600207884144803246c01190820030500c0c020902405080c1e4014405460000c0c26555400460004010201c000380d40003100000018103000d815000d071042c140203a085c0340040d5030302c1e2582941c038810fa214001c04100c0902402003e85150b4100e42c044003c00d80c46d944124444803510a00c445040706c0d5040c21426a5403104141d0b941882a807400b803a003500d02c60b00e40300c8992141c1100e07008031000141540d51800c00070f41018441c0c03804e1080080e64008a5070403c2d2210701c408081c000501802c400c91094090000f01548503415441c544c4d402c0c48408a51650b50403e00d1010703020090082e2172183c0f04001099650324244102c0000308510303500019850300600d03003081004805001c0d214156140c400748009a91851404030310325503c020104485400c026015014050f00c1301000c000f1440441004591b0901d07800a0240249a403032030f00d60340 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 204475296 1250 204474046 204474077
    0x30506040b0a12080c01060b1c060905010b070b130b07081803160b060a0308131d040b06061c050f18010504030f111002070503090a090605030303040809012607 70
    0x1030403e00c0795520076400c6242c0c1d1400b09991100034609240070200100d441912801090303820f0b441950a03840301290300d107400e001e15665102e01c0e0007511a21030300744041e5140a042400d2401b401c040500500c00c81000301d01c2e481c54100c9041803032640003507400254540414050080e031021101c004c40c1d458810500841c8038808230407140c8900010200084140131034407485643c083c010803041d00a1894180800420320701d0024006850350316070141019414480e005410408400d8410803080b840411f000000700e8038079030a68090780940f2800d4030f84101100d006005d101d0b0400880c09035141009100713030000d99080c104c2c481d921006002c4048141d44000b41d080356011580a00052100001c0003d0a40309462000981d00c03644201c031102c0c8000740800c002c0764084101242c8030750002603111181e0520360002e5006103011001003241d146403001080d220703c4000d000400c0c2e00d00028041c40b1300e0f030150755048400104d803071240c0706181403281101c00c820030a07502070020840d10071039001c03c1c = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 204476546 1250 204475296 204475309
    0x3040c0b07150911030f0601080106080106031110090906030c0303090509071e020c040501170610030c09050c0f0a11011a03071401020319050304120c2003031306030506040b 76
    0x569010300321900b400d500203007510007801000d0044551040d2020001d415079400c01284150003002000703020741b135141641c081e00b100e5280e84451001d034103003d01000070031400007003402d40002c00d640b00320001800e08011901002c00390440312202d0b1810741c022080c040a10801c0d01a41e02c04d80320300103100d0b00c95040203034800c004c580040000e444503c5a080e440c0d82c4c011504940c3d88280112422078902d000082c0a0315026000740040c4115402444d070219410024990001c201d000304105031815911101c024229600450f845507803114003042f011140358045907841c400ca4050300344c44e00543c0340c00522400010a0344122582004e0820203202c001c2d8540b00501880200105051460715690345000c0b17503c4817409040d030109001001c5417043e603179a80c0301100344d00d03620190f483c60140b42841107004485442000c2000000511000803414070443c0b45844004445120442a071301c0045c0c60340c0b2070560300e0360800d0342e000c1c0c0000d00940c041c2c00c224000c100403101032040104040c140000e = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 204477796 1250 204476546 204476557
    0x1060302041211011103120406180b161b030807020106060e18040501110a02150a1104121110030b0924010f110105010308120906010b09041104050a060503040c0b 71
    0x40c03000c01955140025039104003500500c00c060520070210845d034480c20381140c20240d030104c541149001004100710840c0314006408403d41820385080f151900c5001119030024280407407406600407013008a0300400710340112421502c940881c3c6d441500d40180a01c0c801c0d600d510246d03081420205403e40100e010605126018214920a850346072141940303510150054405540c0c4080020710780000500400c46150250020660f08036041e642c45920f0714000e02c900841c0303280810300e00401e0510000c403012640c811456000300c628500344280380400980103103603c80881d494038080b0907050781002000300c204844c103044c0b540e1080d8804071001c1044124407540060701c442e1400b590f01a00040d410400f6078030381700401e10101c00f00c1d41d085501c2038006075012100804c007031110021009419500c484500050142549030151800140c0601e91465208036168010304031355043c40c10036030b0001d10b0004c011070b08590317036003001a203030758030994064410104400380400c109510508856 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 204479046 1250 204477796 204477809
    0x140c0d05030a030915020408030c3901110d11010e0a02030d050a0903050109030e0405090c1e130204140109051e043801021c3e01020706050106030204 66
    0x41c40d046864900710014030131034500300c440d200040c850719425031a80c0f004d0000303441c6120085554800e42c0c1800351514000d0b988548020400d440490303002401c04110710043c250b40315424040304a41c80040c0c51400e00c40c46002c80c01d1050078064a48194403044944803002850001c000c2c401c01d1418650b2540c09030030300650190b00c69081d00003118443c4000308040009807410440b00b0b516075a803d425116080e4040c7c4c0003440c4642d40526510b000d100e00c0350806881801040c44981c140c01103039242d401da80d03558807181c2d141e02038070032031b81c595140c1d0b030400c1c070745071036046507120780b034400091a615121841030300150300c05d040801c1c00c2c24544109050860700000b60301c0c0584407102000060700742d181d10f03e81e1030101c0244142c014408181e103803100d0102c0c04000c514808120000902e0000c00703664518200100b00342000107070307400031041c641c1c0e01e111844003c4810080007003940007102d1181c0680380ca04a100035011011811f40c042c0903070394071a001c14007a070b90341d41c5e808805901442c014034 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 204480296 1250 204479046 204479053
    0x10905030a20060406050702030601050a2102040e0a0507031403041a03070509040e0109061104060509060918040309061e27150504050f030d05190903080304140c0d05 73
    0x3001042d001044811525055001400c2420940000c9030164100f980000c020a0780031900304114034043c0902c502510060303803420101458101024000020740c20700d610603c11b136040f44819503c640c0c110304900300c1d441c021100e40c46c01074a8541e695080c94802a00c0e15034003140307502d01c09400841201e0840b600707071940f560803521051260125901c007802c0c01c0d00b4840108540b040c45d4490740a01d043d000c00d5803000154200f29814a80142e4041000c08140384804010500525810009844140b0015200603807591a41d8000c5200b84020b006840308440403c006c100401d17920144420940e001565050080c110056000040e600810b04038404110689080044113044d20305181d00c04d110044211503140d500c0012441c4801803940c00800a00d00180900c218208500900310103403003038004220007050408014104d02035001e02c003520440508404102c948030b62080300240d40c01001040e540e00b0285020083e020010951503211700801c0c0849607545400700002080c40e401c18084c = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 204481546 1250 204480296 204480313
    0xa0b070807050d09080901030b011422080f06090f0703020a06080613050a0213061412040203150901090303060905070c03140c0610090e160e0408090414060a0501090503 74
    0x65a14490081c80d801c01c000c400d01ca450400303000c41c010400f00c1c50203180d11a82c1d0345074a100040694150718a0711381401410454100b20100c01340886005111881c0800c2d86035001c1900240701006592142d180f81c0b09441c51900c140c000403d196000301440001c80741d03194800c80e07965444101c18030010b540004100003c00201d400352102a030300c100e000302400701c1e45d01100d41e518121401503a581c103030907501040c54045421040c610308044c10305801c050328488100000125588640b02500c2e280702225004581151002c005021082240d40f101d4034082c0b6003548407a008244a00040d000a820b019001030303d900544500f40c01015269100c000304403032503c00340d400d80701c0b031516001812030800c58415140d80c28004140560030740c06401e41014503000e165010b9a401d03001d40500d903000b640c0c60b1480000032080b000f08568080799001410398841c1014601e074012001d031650000e050455042c4038804c600392880c4919000c80b2482c1029885100440303c10cc124050345030590711030f909 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 204482796 1250 204481546 204481561
    0xa1b030f0c08011d07030209070c080a090f05010c05060604200301062106031a070207080d0504051806013f020c010c08070c0b060f150a02010c0521130605130c05030a0b 74
    0x80c08c0e03904c8041410b14414501c190359a214042c0d10501e603080000701000b0041c807201c0108115400103010900c5d0280b00203107640c41e180d0316420301511051003280c0c4c0e912800c581104410401561001182c40b841c1c0325030350341d9806085281482142801d20500390700e1001900c0580c032900080c0ca030841c00011110303184094070311800b0300c090050001e500c180b03080001c0c141e82c10002160f03440c4869840030385a52400084c032803400305040007180d242c1c007401c1c2041080d991001d06401012a0741c001c1015008130103040c048054440b141000358003031000d0602046c000c958004114881d40c00000b00310124242c5401c448165003542d0801c0000c503000240c0000c90809040c203604458002c202450100f411000106400d8001202c0e214030100820034004c403540a00c1801301c0c0760005c1c10040d1524074820742c200307400c04509901c051049180004a600302d281518626149544054200110b04080c60a1216078418410131516424040400700e1039040c0480c1202c07489a1010304400326894108 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 204484046 1250 204482796 204482809
    0x2070b060d0201030603050118020f03030c1507210905190c120510060e100806040305030a02030a0e010e010b0406091103010938040c050c0a1b030f0c08011d070302 72
    0x78050703040607250607011010900a21031120b818841c5003460344160701510601221002a22020307201c0d407c10700007021302d1074002c038415910011441451601d55554a03017035845400e04124001c080780e299001c40c0e83c3e54020350100c543d45005508680341109502c0358840c400380c1000000789481003c00c070070016003200c000505009441031003521407186180c5070a10403544c41da40150484000441401004000d10222101800794840030340060315041d100580244005480d0034285a0b0000c000383c203001541d84007200c008952002030041901040d9503c1c041c040d00e0512501c51031601000040540c0b0900c0303503450000743c028409007561300c2d00c4400d03402041482c140c00e042020308014201001208141b01c003064200d0500c1901e034600050a0001300c4145004080901504101800c00c80f100007580c4c008440d404940e88542e0302c02d2070310240c4c00c90310035030000705240b000307140c0c15040200c201c10700408d90b1086802002110303000c0c442c1c25100e802022602000d5088003806102504191 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 204485296 1250 204484046 204484069
    0x151503061b030a0221010f0e0106020303150a080f210901120e0a3302030106020a02040903031806090510020910050a020a1e02120c032a0a08060f06010302070b06 71
    0x8803001420305e4071014064440e00112140c3c8100501008018025035181c4900c54000e40071a1025100640c1000c070041d590f40f00c05005c40400d0500d0015102e119514041244040d048c40b0060301d615440180c016540c175031a841160045070446541e049041841405503552240142d403070000e03070f14105100784010014002075040782d000302c26100c004510712a0030905840e2406565070100380c48003260f041380c1001403c842e600d060042004001003580000d0380013a2640440d0b0004461481c0e2801341c0c020140480039609404a00e5180380038008940d010703203141030044050b514413480d1840280103e201d00c4030792a600070301060041c480b480c8508003514449030701d401142d0b10010f2030b0320345205400b5502c3d00d0704110240079001c40114188040710f4600042035200408a9070200310000780c880d80e00400c0800402001421952080940182280c4815002d0715410603151a4400e142d00c1c1d03001260044007401d100c20218803294801e00c01c4810b1550042c0d4000b4941d141c4100b0000e080c0c44a = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 204486546 1250 204485296 204485311
    0x70203010912050c07050402091818060702010c110a170d0204080106030f1e0b061c120503070813050a030e1908031e1c020f0c151503061b03 62
    0x807122504000356061051140c610142d44a03d40c841c9040901180740048a4000728080ca005005003407268a90a8030101c06103598801da103816940e100c1d07043c80e004080b0010b4500c622441e4240078450b038042d030184c81043e559030b4462005681a036003a81d52a065038100800304820080b00a04c0b0390741a03405010389804032030004d417519a0f280070090944160303400c1039951020500d0b03d0420041c842000c03151107841140650b001403816210040c0c110401005107002e15032101020410000d2001042a82c03a4014010760f100c9560540080250300101d4010000c01c40b0200031071000c1c0300c14004080328a42c4030b001091280790503a0b0848481189460386a001405d402c14440b003840b101d02d034103019001c0140150340742c0c0b0301c0c140485101a9690180d20742c0c404204900000c1d0080002081440c41c02294090fa603401c1e605032041d03180c03117a070102d90180e000740b81c1000d14199501c4c01c0d6a003e180100d150407130030410302d0109521240c01751a4240400507028500030000707003480c05181d01807138 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 204487796 1250 204486546 204486551
    0x6020a020f0a03021507020c030a03051303020301050112050f0f0c040c030b060304060c030605061303290406020306030709050601080402010309170c030c06010803121f05040905030c010b030606010c02010507020301 94
    0xa42490740c076040700034000b20056000310030320f2500b80942c0c1d0f840746d0303112440d8401003040d4908080420b495a0401c4800342c200704001441c1e00602c400404840021a030240081180c3d6030740303030701e455045040c120044070580580703051028106800507580c0011641c0b200540030450b100005c100003400950f04000a164441c800210183d580c0c101444c400c0307001d08000324a201c405413000f8101c511580046100b181d041c40b6002000c0544010101030b00c2e807201851480004d40007440c00c1d128005c08080e00520136400802081080d1078000d076014520a908444d8855165450303903040d03a00864400703000a4041c0f00042c0590711a4222070000c501400e0b10455113407034400d080c00c8039400404a1107c0390300004044140c8401004080d004100600145081080b1110744503c5184041d1074481505540060b107103d80044184480051500810411541e4800c0c41e0644d1680c10900c4083c0c519481c00140c40c0e80c904000c5501031045a0581d40c60704d880c54140d0040d41d994200110982e015903 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 204489046 1250 204487796 204487813
    0x90b0a03020411180312160501020c03040b07030908030301050121270212150c0f040b0a082d160c060509010902030708070806070f05071704140604050d06020a02 71
    0xc550f841200b01e040e0850106607070b60844491866140441540032900a80c0504c20986d43d40683c80269242046c004002c41c2c0c0a03172150802c14064010000b503001580000240010110342c14001408400c0c031a8403030300b0b5269510038a0503100e0000744641800308111802d00e04100140b204080c520503035041d00002d08014803100f041a04402554481c017a031402c0c50094158070f000030000b403104c28042c0c024070300c04101c1c1030703000100e9070090000005e450000c2400f010250414090b80c001d4000d00b1011521899828001850b141003914141c20750b0300c648094000c144a10309139502c050707a0a61001e14180c03074030351884070a80d042d124500d0400030f401c02440005101401018002c604560010815010310b004050816686601581059100c06e070200008a004500258800054280550090a240010742d8a40700701e400c0104189507400f0203446004414025001780d070404034540c40740109040900200b4070660051652044c00c0340411400555241c00401041019105480d0030300e = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 204490296 1250 204489046 204489049
    0x20c06131b0608090c0a14062107030507030501080d09181d010c02150403090603050606040b030a0e07050a0303080a0c2d03050a1a130e1209030f03040609090b0a0302 73
    0x320142d401020006450f007003400101c00381000480b4070702c00c0c200c8180700443d14002c800b00380303a8090540c0034080e09000c28403486640001910002840340d50301c19010350b29007000000c00070035086076444042854600046985d074030001d500b6140348031a807101c4c90600d050018034072a0141c81d0207030800c41a00d5a003214045a01c841c0e00620024211001085e01600c17080c2c040d08005031245440c2c11001034404001c08681d03c01c0900c0215542c41c14001140d0311000081202480345400208a50341c0c008144a500c80041d8403800c801c0c45603100340c131440b0f5190800c0100821032484090300203026400441d030120807661141c00000741508080300101220190803084c1c00c4588000740e580402e1180080c05240c06001d40b0ba40a61a045c081008091a003a10b400b035482a10105000707042c000c040c1e0f8900c101c82c0d84040d4200b24030070201c40007030070a5207107100e980d84038055203070007070095100034021000c00000b540c054410a40300c2c0c1c881c00c0e080107000b0005000908006901c00801080040035 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 204491546 1250 204490296 204490343
    0x50405101e060605070b0f061f03060b1c1406010f03270c080105010605130b031e101a03010f120602070804030309090506090103120507020105041d010612020c0613 72
    0x245034513102c4985804c51400c0004034031500038030942206052500300006551942d0500a8028212030305002e41d1690302d1040300101104d80001a01382d000084001c9980340c06103640b03200041140c814001d101a02d1200301080720140c8565002c02d5400e040c44100a0080d0440968a034070020008003a11744a1400200e136816114195010b12403035030140a10a82802000e01604490905501d4680d2410201065081c580300300c00a8050200100d8600391041511001c51640585032280c0c500304001804061300c6039105500b066030071a0044925030501d081036034100e80341e1118a14085142031103c06c1d0210301c40c0c0048405590820502000415040140003c0c50007942d403d5025030914013100708543c1e0140416103e00c0b181c200400003c3c0b41e00000f501c000ca01e80ca0041d864581ea0f02c0140c85a000d56002b26003400185542e240b4080601c00105040701e1450359018101994964140100e1141c00e0811026802c0b5a00160704960402c1d19099054421090241002c0300851003000 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 204492796 1250 204491546 204491549
    0x2150103030c1e080409090618050102040801060504050903090d030c1703010510170601030c1b200d0c1203110f0601080d020706020a15020c030a03140a050405101e06 73
    0x114024850002c1440301001030910b01900038003000c4030f62030480c3c641d210030380910312a00500a444410310020803005410a070b8407100b5042c85100c0c864941e09e8914040d4110380254a13030740d071804d04001440d1400c1d010f074500504018001d0351501040c0350034450320b104a0307007098040c044100041d000041003100070184103603d100d4010b4882d4107090420914100710840c0204104404040400c8051211202c5800c1030090030000f99211f400c0c1c4003034803040c0f000b90f02d030358506444841000c10300100100800840340c40c1c03208209003e40b4541049004660607501800c1600103901c144450f41400d5464860140071b801d0591180100c2021246089403061242c1c07010b400010041100b0501000780da98040e0550000c2c044030b80c10100025550250074030058440c3e01d480304142565180c82c1e048408840300141a80d503140810760028001d48580107640b614048880000341d0002e0b0288200340c0150350102c090104044065440c40281c484030b880c5240415240024442000141c4513940 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 204494046 1250 204492796 204492803
    0x40b030f0d0507022115100812120a11040306050606090d20150f0d021905070309091103010501080915070e03100b0d0311010209030109111e010e010e0102150103 71
    0x5586019a1052100b80e0030440d0b070031100c85da04080180e040000c08101c1c101610b14201080825685100c0001c003062030540c040c00303141c0a9401a60070705114040186409001c80000c0a4640c0340c1640710005c4416461005190140a220920000e130940d00900d801101c01840e60b82482d0520001a441030600b4804603000c1c901c4607209000c2d1550200503081002089800d0b440c0c0c400840d0310f84083d48119400d0130080c0d20005009000030282e903040c1d504280200101c144841300152001c0d040e41d102d0041900815000311000400525500802801e03c100001050850b40b0306070040d5540079000c1d010400b1070081002030b00840190580561245650380d0314000a13801420a240c10302e03014030304107041203050007250a1030351500300340c6540c115803600d00981310082c005005070090284900312503155082a6004040c032064044040c1c2000084801880010303a900d1a440750100c40140e0902140c0d4844040c0015801985a03400b044018010b883c0520420f01c02d09545010903003044 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 204495296 1250 204494046 204494057
    0x203071506030203010c1404270e011515140a050705060f160206040c030b100b040f1701051006030e120301030807030215040b04061e02030907051914040b030f0d 71
    0x10010f5203401d0241c04c07840180303070a12044442076040310310110301c10350191060204040d01c107207400700420b902c1020048040401000a0200c010300103018140c0031040808000c0803002c0494000c6008110804403115600e544102012000001e05c1540094200c14140b000500c80c50010035000d014562051101d156510000d02d0301e5a0044a1261104886001c560120b0100070000300c0c2ca040d05010340350080303100781780c40e03417800c0d010242c00a07550007440710b40401060015000c0c00b0340c202c00c400d841c2254a422014100c1001e000e080754400c031a81499268504401c10000f40070768040340c0800c181809071400b001c0c1c03640c00c2e03030841d50081e0310465a0301c034001002c01c149981844a190603101030030f080400c070f00345901c4804d640c0318040e00c090300141d40c48140c41210240351040741d080003260002951240f8101303c207141c4502c000c1c4601e50040300d820a40f03001c01040b40d071a24042d10007010303c4001d8021854180030040a201810301c1d018810000000340e050001c0140040c0e804265862 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 204496402 1106 204495296 204495299
    0xf060e04021c02030f011413030e0405060406050604061218030906080a06050901030503030a0606050a140c0a020d0b0114030d0e040c0201060b04080708010506120309100203071506 79
    0xb1340c144a01690424002810340010512a4043d03010000a55501c840c44400010b4558010001288261141201d10301030f4030546e01301074094400a007654a450201d01c0c0c7d58003d4010380c01088210030400c1c0b032018280513040c14058900301515140185580180c40040340b030160006005141c40000d14003030381e070341c04103005140041000010796568100310742c581d8819203e00c04c107182840004920076018000311068400c01d83d0303400750340010725840c140c015045262810240d000c0c40d80800050707030700c0b664086500d500544c03c0a406501d45403151802440900c44140a508186900b4480c1508541150480c00c4151001704080c460340c44101d004001c0f542029455500210307020a0501000544d0000d0340c0d001c5008100b1525500d00b0080c2c1e0420071143c042883d4800c101c1c18a5505208142d40000066401240e050526580d2012440d80607958208803140d5500e20 = true := by decide +kernel

theorem cover : BRFrame.Cov 204316546 204496402 := by
  have h0 := BRFrame.cov_init 204316546
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204316546 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204316546 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204316546 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204316546 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204316546 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204316546 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204316546 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204316546 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204316546 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204316546 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204316546 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204316546 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204316546 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204316546 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204316546 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204316546 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204316546 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204316546 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204316546 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204316546 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204316546 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204316546 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204316546 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204316546 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204316546 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204316546 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204316546 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204316546 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204316546 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204316546 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204316546 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204316546 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204316546 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204316546 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204316546 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204316546 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204316546 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204316546 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204316546 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204316546 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204316546 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204316546 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204316546 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204316546 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204316546 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204316546 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204316546 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204316546 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204316546 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204316546 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204316546 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204316546 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204316546 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204316546 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204316546 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204316546 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204316546 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204316546 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204316546 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204316546 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204316546 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204316546 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204316546 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204316546 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204316546 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204316546 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204316546 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204316546 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204316546 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204316546 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204316546 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204316546 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204316546 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204316546 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204316546 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204316546 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204316546 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204316546 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204316546 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204316546 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204316546 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204316546 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204316546 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204316546 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204316546 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204316546 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204316546 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204316546 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204316546 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204316546 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204316546 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204316546 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204316546 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204316546 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204316546 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204316546 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204316546 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204316546 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204316546 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204316546 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204316546 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204316546 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204316546 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204316546 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204316546 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204316546 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204316546 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204316546 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204316546 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204316546 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204316546 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204316546 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204316546 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204316546 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204316546 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204316546 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204316546 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204316546 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204316546 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204316546 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204316546 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204316546 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204316546 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204316546 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204316546 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204316546 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204316546 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204316546 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204316546 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204316546 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204316546 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204316546 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204316546 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204316546 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204316546 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204316546 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204316546 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204316546 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204316546 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204316546 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204316546 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204316546 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204316546 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204316546 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 204316546 ≤ n) (h2 : n < 204496402) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
