-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3124
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T08:43:47.404169+00:00
-- url     : https://prove2.me/submissions/89ea0a28-e00c-4605-be36-e0c2c5f11f64

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 561690647 ≤ n < 561870503 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 561691897 1250 561690647 561690677
    0x3050702010c1a0403080109060605030112050a0b0c0405090604021620031218030f0d08060a030b01030f170f071403040b040f06181401050a030b0303030907140609030a0f03 76
    0x2c83c400410380c00082c0c081d00104810940e00810b62801881000b909200c058103025010701b03503010500a84000c001c8050000c81404400c00c08070019a8005070803100d6800d040104100716031060059500900102c40820381c070382840d00c2100c00c50413045c000b0310706403015076841d0601d11200443c010350041c1d60350078080c0550b60070300510070440c11480d01941e443c07001544101303591211016081c80b9030403086152000480c003080c0c51170008103501d0b086203141d40b100d0000d4000c14a40d01302030024450480040304100c540c02403180c90318088c0c86054908400c000c00028030b481032800f0000101400d011a000294101d031030903e0207404402038034145911445810740c1078006030b022070b45003c44100200070709501f00d001209003402180041c2c0e8840e040030003010800083c2003c07241000707400161a0900c1d1f01c203034001c1460000040589a8070f0801000042c0d49140601030f5503804607150b0700160103458150308844840174007801405c081c0701a42c441c82c0788607070010400d40502c1303626107012400c = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 561693147 1250 561691897 561691913
    0x11070f062727060306060b0d0b0a0e0606030702010f060b0d1b1b0203010906050a091406041a130203100509121c0e15160905030d02120d090606031115040605040303050702010c 77
    0x21f40f1454603090349942d2206042020b131424001c3c418050107803001306122002da51168681c0c490000d5505a580303856071107040380100301c04248110f1241c82d00c00d000c6940c00326580280048803900c075081c00940c26450200c2c2854003c85a0076000c9040c2c110350040c0001d1035009044840d00044c0001000d130425160324098038000c640b03440b0141e41e40c0f6056402c0081917020a144030560b94010451803400d075442044454a80c8113a07210100440006048044074084c00b403012503014042c1d84000075001a000c0290100396905421801400404124202c0040070f0715424582c842446181860361071040f00107042102d8010064021100c3e01088588264401c034007074682007607407400400c4421801869210300da000f652180c1c1007416984c500c2035002035844d460b05480c4800b00e035030302c0c00604008010440414010401c0b03042c03010000c10300c44840d4000d49a410280c03080c0341c2047c0a10079002a5100d20b020300d00114800340828808a4030030b9020b004000e206041c442d0710104d841e20742c406 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 561694397 1250 561693147 561693149
    0x324030106050a0905060901272c0604050601050d0f0b040c05060f1206041a0f03031603030f0f1104091806021204020118050d0311070f06272706030606 67
    0x2202e145c40708203001e5542420b0f0749550051211001440d00074222049643c90b040c0f002c2100c4a8050321803090415000003d5950380e00800060056109008200c51094032480100c4003580c09010343c030000103480c10000103d4090b0340c0c3c40012285c40728034964480107a00c074050300c00c2e00e5011103180081030b251101c0008024524940c7e030101c0e21382680d50081007240c1c90050074039000303904201ca110380c8051544014034042d4800c03180c142d07820003000d0120b45103004102140304001891302c0c44509154260340038400042c4540d5051140c9a9038412850036a00041c100c240b4940007000200071017849980702214004500101c800980728030784650099811000d6405041c00c281000d100031036800180c0e171000d01145410221074945000c0008100d110302080143c00d01c02071051040321142d090001401418805400520054541c0401400410000c8c861441c00300e02440b016104d5400d41c0208046808141da01202064964940102890302d5101911420340700c0d0070210001d0a2030113154 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 561695647 1250 561694397 561694409
    0x1915081207060b030102040f0b0702130c0504330815031203060108061818100903090302031501080d0507030e3102070503041517040804090e01020324030106050a 71
    0x5481d114141004003c803492003203c54400d80c8100420819502403040c00c2007180c480900254a0f000540040340541c94140c88480c2d61520f08401c08004540080c007500035610b8001200e10400c801200542000183c810042c9240e00e80d08403401859100300a0543d000350030202c0707400c4d4a800705020034980200900760300b4141034080200001c0303581c04849164040780c100c448204030100a07100134541c01000e0250703800c521501118415440c82080007000100380f4038410092071a0604005160310002c0c00104d220f40a04070001c0200000d032100175040e1950803000c4c2c140c010380f9640c1a00c1c2079102030b504400340032001c6082003241c0d071801d0740d90f01b2030f0680400089144810342e001c010f45a1072001a401d1540c8141b044201150000081c0c5003907800144442040f00180d11044e600f4074110040c131030103030900c0401c00c030400800e4ec0c090811252000c105100201200055600340d000c01c450301205080c1c10243e520042100750307900e403512440034000040d42900c40011070000c0c01c0c160410 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 561696897 1250 561695647 561695683
    0x203102301030506191b0e0102150a0614010f020705041508030705061603021206060304020a0503030406020a03140a0e09060a09060f080709151806050607140d08191508 74
    0x60708481c840415540b00c10850800002d0689958521b03d02c83c200894001c0000c25001c0c0a1541d00810410381e5640030021081d0061905010008c080d19090081003a4480842034110155011351021b110720407480d005840d400d81404244401030400180703804903000c03110300c0019800c60603c020811203014401802d40d9151045000e0030341030b50584d00760304161042160311074900d142e03860550407072400c0300c1142d5079413124000250903c90503046203034140030000e400540980c0010b04641003e11039110315a00c2d204c41c8400401e0390151455140105681103603251080c581800029403100004058100564071042240221403070394001030311070414031500740071094040002c03100400c000242807001059005606015a14501c9031455061100d9562000b4500f01d4002da80503080140c070107910b074840740c289000600710041059005000350f154004140340f01c0c131240b0b4800c140010407082c0d00c8a100704140c008000100b503040080b41e040d20082407407070781404007600c2c01441c0c82c59 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 561698147 1250 561696897 561696901
    0x6020306042a0509060415080708010f0f06121d010b0109080714091306020d1a10020601051203070b0f07110f070302011407020a09150f030203102301030506 69
    0x18401290b503910000b00004005000c0c02c0d841c00d020b420841c2c1c104440c1d2074800e032540402d0b808541c4070b000302c1c4c00a0390918490f49403207000c0d6030b024450b18800d089039a91000140d0742c682c554030a0340f140780100ca04001951009103c01c03401228001b141c4180300000041001081c49494011032001984e041165180d60350001a0344e07103c0d0001c0c3c003524120b005881c0d4903281610364414071844039100c44c06402d41e1000034229000c0704030310b03d030b90b1034102c10295034070b05080407240c00600c050001305c4200c0d02e4000040c1000d043c00b050300d582400301d940081840ba401c0104210142c000201b12a0f283d1104002c9500013803a040b11250141507541c501c1c001d1030810030406003120000400400e02c5078002c0714684408440042c0c103404070381c0c083c2004140908418070100f60b601c40c1c200080e402c030f00540d0b40028442600e900440310090124140004541c44a04d00c6d40b061555101c082d5040c0d214105030702c1050603551082c4904414805840b00404170b109801d541440b09038825101a008081 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 561699397 1250 561698147 561698149
    0xb0309190506011d090d08100801140708070c0506010303030b0a0812030403080c120438060120030301030602090a05030706110714061c0e1e01111309020313020d06020306 75
    0x11207128200e540c50404d240c40c80c2c0b54010305ea54000038030b02c0c0010803810001040c40d88040308900c402500300c210081c040481d0040030035402c0d41e02560160006240500010101071181d81690165a440000b8000c0c0742d1031618214040c06d9010075403a80000940800152542c040111540d49221040481c0c0c6910b0642000b804001380146070070b0a4101c10002089602c80e07440b40c0c280d006500450099a82542c046141203409401c078180344e5400302420b1002d401c5500c00100d41c4a80c03400d0380d840c08640003054082d22a09010203000010f0f074400d00060000400c03640203000c40340400b0b850740c1d00603940c440000b80340c0010360380400c01142444281d40d10700b58040c8508800350902581c2c805069880ca404606584a80540304402c0b0003810404010b014981d0002c100010001040300c18060f4980c41420078003080740c100799065860140231002c103180407002d880c0000201e5251a03007803841e03c0817010181d48018038003202001d003049030740c1c011b0380c2d91021041018000d11b00180c0300d1402c00 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 561700647 1250 561699397 561699419
    0x30010f1a0a060c0f03080a0f060602010e0d020f1f0f020a051e04030807080703030603060e030a110c010e1c0b0c0c0c0111060a150b1605120a090b030919050601 70
    0x500802c040000840720000803501088801e1040c640c18034004443e55105461080104007140034000524200080000e1680c0d054000b02d400400d108162010640c0190041e60303074550400e9800308a411200800c8080d0200c0030180c0c00707400c1401d0b0040782d1802c00c0c0b107a800c100e90100324078801156003c0741e00b440840240f4052901c80450355030380751910f401e5884020150040b00d80050181e00005055403c00d8400c0d08841e00840d8082400e015690b0803010942e140e400141d485800200b0741c80091346518000030305140440f4040c0c451000c10014a414011400030118603c12002c2a50800070000380109034007a11072020608281d449084e82c1082509080007655498104070307c07443d10103014203000c1103690308841c0c0c1980c00510002400f100c0e8001c0d600560000c0b00c4060042003180f0990041d501c0f905407036108105658a01808a00460300b500505003c1000542c041ba018441e0947c050300441e00401413504840307041c0200c000e00b460340114040102c0f015002807004100803041c0b6 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 561701897 1250 561700647 561700649
    0x903270e0a020a0507060f0209090c1e0304020d0b0912121506090f360f0f0c030c0a1e0908010c02011806020702061e03060f30010f1a0a 60
    0x2203203095240060591000b1301d98000c0301d1000c0c00399942d0301e0303070074840c031410b03504599480e0805441c40e080d0b0314045402040301d4002e4181e01c901c074003410854102c4801079030f08481c0304a42c000e04891080c000350f182c0d0aa07000004189880074840c07405094a100c03000c1c0007400800304500c02621741841e02484100c165284005d00c540908414020b0703414568980506520341102a50810003011400c0c1d036402a02208040110303c0300c15058819007044051194148540500540095035480d62602036028207811900e600c5409400d10109a0b200130b80001040d0100d034901d4550300c1c0000003502e220000e603c002c5c182c03000c07540980c1d0402200c4c4081c000e141c0700300618002003040303620f00d11310141101c5034401d00070245030380020510219600d080c00c0e01c810141c1d018007480241918800b41200d503009880d014816001030701c2610580c0b502000201e110329007504400c88444000300c0610660408680c881e010b1354030741803010014020b510a840b2070205600b000702503080b038a03040c0705030301d141 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 561703147 1250 561701897 561701911
    0x19080903060f090c1f03090c150909060e090303070c0218280c090b09040e01110c1204031104050403030b1207060e0303090a05090a06262506030903270e 67
    0x4041c4040a203120072100302000c0c031201c0d00780840c5001d9113140c40b00d01c0723914942100207801c6e0450501942c0c00c0e8032a45000545014110030060251280a041d480e0310086826003402c0c2c0c002c00009130260f10034201e12880303a1010f00303004042e01b03810f11284002c0004692803121002c80204000030140a251040d0303000c00803131010017210082c07990041206440740151101201c0000d003036180e5031125031105074050b49400003040343c00103044888000e64001c1c505240700d849070280c4200408c40d1413049030103e0341c1c41009607140440180c14400580030091094080c190342ea02040e507a80c540f28592a0280144000f801c003aa0070310303001070440165458400e02030340c010700498070183c840000030b02c00c0d50b408560b45410b60796401c1c4110043d00703894000622817040908003c1083c1c510b00655641d84241c4400e54000303615403a8a20285c00e201c1014640504034040100000b50003644410301d03003800307854550116104000a07582d5805506862040a00d00c15010450070301d10030a80340e08009 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 561704397 1250 561703147 561703159
    0x60e03060601031418070315020a020f030901020a020f0301090f08030910060b0304030c170a0c0209060d0201140c120c0d0219051b040b10031a0409020319080903060f090c 75
    0x1420224004c01040000c00340c611001250802e4100007000b04070f83d2008561000510300c1c0e0f01800c0503020042c3d080381060401502c581008000703049c6000c0161240d041c0107030700810700c155443d002c00c07640940e4080700c55019580d50341031002260302d003801401d1450244000b6503480c180b00117030700c1c980628141e110b9105490b040c3c040c0318070601d1104984e00240c061034420f001102d1410301c66100c91704901b0541c84041e00250b215031030b64100310b407000e500d07008441520150b60f0b0707203080c000158000c6000a0020307045142c2e0083c44980540541050100ca00c2210b40b510500070a07070780e4176401400580e138a030344124007580d09150b0402403e1141c00300306080072100f8500360b550a54945102c400700895000154511820751102d070301c0700d0043d040060441c0d041260104028000341034400c4036005200d03101510a0b041c0c242802004c0b41039034068001c147c510021440711500d0b500c801002c61301c1c0d0070100030f02c500340e82d41040100c0c06602d0700340d2940041c1c02c10f5140c01e0b140042c560980f500882c = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 561705647 1250 561704397 561704411
    0x60809010b03061302011806230f090114040515030103050105071407061a1003023411060702040509030c01140f01030308040c08030a050d0609060f03020613030c060e0306060103 78
    0x780740491080e42051a131031611141d2009440181d80208212407a240c00c03031640c60000440690200c0391a90080c0c904803101c3d280d12205100c401607110340302100a0184081140d003070b02d54801c0d0050080491b41401d138504094490740040c684000d41124055141008001402441403c0c45229002891400c0445c0c1c5100b0500591043c1c0c0100600034111a0303941c004851001c0b1511480000454002c02000f03d2804024002d0700a4000d07030b080d019064004051081218844c3c450883c07241810701c0343c1440048980e9401524171404108990401c2c010310144c070068885008160060031080065615000c08008041c03c40e40d0b04400003c65246e078200b8401c00e523a0f640d01341410b407905858100040d0783d55060403c0801c143c0e5000303d42d184000246540e58a41c0b003000f030700341d0510a050a0080c02d0b41d54800d5000d482460082124000081204000514040b00100001003d004007281007030f580352079121a01c1c1882e4003c0700800c400300b440c101503140500044d503020b1400d0a0800c046 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 561706897 1250 561705647 561705649
    0xf0204030b0408180406061218020102250e160f0212091e1216080703121b05010c12050c070b040b06040207051e0c0a0e07030b04020d0e07060809010b 66
    0x1400020300050204800021444c04c0c030025104030804a41c0050720038070117a0b5507000001e10a00310000b00580c21490240b41e6495150b042c0011528540c05a0040010301500b03814170428140c0345090050058028900280117044406454420260001690002c0fa03000c031002e0703e0680c406802c1000c6404c240441c8103e100014160b0385940001e8810700e10740d8440c0c00e000f0070101401600d4a074403c174480d402c0ca1010100181820802c40c1e5211100c0da05641d60611558403190f0f40401000030b403642043d0566140b080b100d10380000e000728103810141d000c41d01c0e450308541c030b2590b202001030031001ca0722541080900602ea0847c0180406510717060f500d03192545010000b810003000d544016010603260b03a1650151614543c2010544c2c0b240c00844100004100f0980c06501d01070084c61040342103454190609002c130f90782161482e03981d5862400840082c044280da4540c415401d000000490405200c1d4030590340c00791009081d042d04014000e0302c1c50000034444810760b81484908011 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 561708147 1250 561706897 561706913
    0x1203010b0414011b0b04050d0302041d0411090408040602010510081005070203130806040507120203032b09051005010b0a17130503210a021908040c080706030903030f020403 76
    0x1120b98401e03103030000c0640d0400403121002607625221420045a01c52010711a002d1121030280b0300c50011202d408403c8a0b06805a0085100c0d1400d525041d1995200308a820341c4004d40c440e200b0210040303c0d4035074000041d00701c281501d00344c860401c04a014044140c091142c0740d00b04013141240230340710317150000041c0d464203044100f00c503450301c51011459031402041541c1210103030f40c900e400784a4641d40104c1e5586c00455003529184a85500010f0200c0061032000d60690042c01552034000c100710090100840c03855240b81543c1c000d54400b14152036445420a0184950090022124032280440a661040e009503050350710402100c400f00d40c103c45100b1088094508241c1e1656074040845500040311401404074003002400040c0b035502e512440640110440c00d52081b5280ea030340100c100d00032002c81c4040520003040e9020814043c40460303130700c14820810401d009880f10665402d10ba02940700b000441d84031000102055014041e1000b00c056807002182810300e15251160 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 561709397 1250 561708147 561708149
    0x70c060b04091112210a02061e010314070305030a080402090f07200c040204060f0906031a090a1d0f1504390f03020f0303030f040201080601031805030c1203010b04 72
    0x4413440e13032030721400800e6105001102c407500c40441c07064204070f801d03007191615a0100c15401c0040c09408005944d00749100c0c600c00c038841c0c1d152410b20a80e03085a9a4a6200340400d2406442d8851180c000002a8080004010106d156900c2d0281d90030300d807050244080d00604280d1800d0990410000f110b031740b110150403d001031000c3d2201840c0308480040c107054500d15515085030000031b0101d0401c0d00301003040e0450100350740c0c0c0c800b0141c2d100d004404940012541c0349401100c5405010586064142c030703904414106800510143d290202c86200784298506c00455000701e03000c65166001032080000d24460081101078603c0c05030ba90070309081404c901c0394103500a8070740d407404101540280224141440080044850f04c500f500c28011070103110403440f40c0d40c080c0e9849407500707010003501d002d4204c58200c00e00ca9115a030042d900d144000300041e041541e80c00a241d500b0b159001c2c4456001d010703401441c2d4442d40203e4040c200f400303054008403280c00c104010041c4810302d00c1120 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 561710647 1250 561709397 561709399
    0x70308150a0e0406020c15150409060212040506010501030e0307020a0e092a0a06090e040210030b060706020414040204050d0f060f020c16060207050a06032003070c060b040911 77
    0x30016003848006000101a03401149415a0700020007080002c03e500410a1400500844410348202e400150b02c1c07100894a040360201034800d10601410140c010b0302d03013a0720481e00075080540c41082c0c0c03100c2d6101101d0603504d5912101c0100001c4d6014418021103041e4100594070b00398060b000714010618510400405145400000f80b143c1014849900c240360f203507a50070042e0700381c0740621801d1080003884030b210340ca07184800110302d0f0055807020300325036100c5449003450351580c0070014802d506016003401c2c03540702d907400f036050356500d002040c0c0c543c03140800684441c2414181c015100e500c115981c0038030b00c10403091045035104440e000c4000d43c404003040175011705141001c041d2418010081c00240041160319041a000c92449050458001554003940c3e6440741244d6a009510400d0780003159003505002036842600403115210072404d10400c0e001c0d482040740c606a01c102c80000008d4000da407440100040343c0a410000242102c2c2070085202c6a115118141d2883c81d440d = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 561711897 1250 561710647 561710671
    0xe0a05010c0807020a120b010e0105060a0f0807090f080a1104140f0c0d0c09050f03150106050901140d0203040c080c13050702150103030504181404061d12130b070308 73
    0x901156202d240c0080039021b0540094042da08a2030034541ca46400c0c0940400c5080074400451641818400d0b640000281d50b1000544002c0200c143c0c0c900e200903281c1005c0114201000c9015010a26084000c00454005110740200d5080c0b00204808103481c040c0302c2c80c244880c1d6000070b15800740c0603421a02d00000001c161301d6486422269114400c115a006800c1000c0a11190b030440500c0307007154015a45015a400f2030810151100c1d64030310141a544003160051018a1080b4094801500107040211418209285045d22504290035040c0b0880d00002004200064a54103000400ca214001d000c03446203140001c8110b001590440600c903596400100e6541c4200414261460205011a42075841c0d0034001c007a03a2150107000c1002070b035600407000240180c0726200c010b05610701c07681c20b241c07925505d0001500c0c1c0e4211416600311841691140b0303131824071514402d50078204940d0394405030300030148408015940801e524201c10300c6441c2c0482e0300711080c01d60040070f007240 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 561713147 1250 561711897 561711907
    0x240e0307050d11100e010f0b03061317130f1a1201060e041b030b03010b01260618010e04030e10021e011d01050f06030f0d0503071407060c0e0a05010c08 67
    0xc83c40c42d04c11035030083d0300e0160400c452401c5004d0103501c6100310b05007541d0709200b0f12000b1424903a40e04401d4031207100d0000103005410200d948000046007010707180002520b440c1c640f030342e9a03030320980f2504064400b4a50040c00c01014a0144400c40d2200c01c4482e0641000311080e910b8941500500c07410061091505115240d980d0740d03805020a9101d0448110405100c00001002813581d0302d545402907180c0102150558000da01040c08034106031001e50300d2180d0400145000f44020300000e40201c41c0302d0450180402e001c9902d80604040e101c1400146424140145010b84000c0c40d40d0041051820f80001c1d650302246e0120903851400038070440a0160301018010051030f902a10300a0090950801c0e41506410143c007484030114244d40f561101c0c0101a01c83c018410045415032040a0007075455020b5406994820320900b4580b10012046000100f641d1101104444803595a94403110541d003006082003050300503038000151506003800a04000e01d543d50241c1070240c0810 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 561714397 1250 561713147 561713177
    0x6040905090c04020f09010206070302090604300b070210020403150b0a0b0406032309070e0c0904090c080d03050105010203093a300309030c240e0307050d 68
    0x46070b14260304001e00210350382c6604807071003480c0383c0080700003038014024000400c460324405d00a441c04560018100d0385003a14265400d0070a070f50810b00c291100d001803240b601a55184d103645120140113064a18840c509000c0080c106100d04e200a412140b041c40300303101050303101003280207080048800095050941c0001102c110980d0b100e0030402000040205046502d5008802c10300342e181c21040308407441c1b01189444140840d03034020107502084081192865044c19030381c000b4500c11019260490360004503060b03421180c400d64507441203a00c2040b07c4d02c0204140f1100304245d01d4100007a506060000b5203911074040710901c501710a002140748421034002a8508101d400e03100144003240c01001031500c00103000a445900f801c0d030480e11040c02000006601020b103509a101e42c21300b42405600070401d1030010340800ca840392507080064000504904078180c418145420320400604070815034520741042403031504180540d03c00688001441a181040b03814401041000c2030 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 561715647 1250 561714397 561714403
    0x801120302190228081902061e07050f0304170a050601063603170403080409110f030a0509010b0d0201120f02120403090303020615090a09080f0703080105040c0801050604090509 78
    0x2c000c04112414000c080820313a0326207100300d0464290a0a84099807160181d49490342074030b00019400503802c0002c4125900c00c0d000d02001030094441140c00c022003030715041e180402019001c5041d85c070000d014016545a86010300d00400c000c4004e10b0900499031307496031615010704c1400207001000001a13034002621805105050342544801350200b8006680301c041e40140c072040e03030203241140702600584c0f00da000301c40907a50001c03200c41c545840c00b841e1380014801c100c0852114481400882410017084008600400c1e40f0903020405040c01c05201c1d084501e00c0003034034450350349202d0400050740c11088070116070010314800108422280c035528003901c1340ca2180444120300b0300c200001c1503080526103094078000d50855045075141441c2c005125200203901c0e601190100c00500c107840c40e500213507000c501c0360074940d04181c00b400d10b034881502f01d0b15007100810540c0006020505140c4151403406005107021422549403401081d098411800707140b190f5600c0e0300004078401010 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 561716897 1250 561715647 561715669
    0x106081b0703030c0e062a030a0203031501033c020408070611011b0f0206070203280c0b070c060b0d080712021906020a0e030609070b360108011203021902 68
    0x160001d5a81d005007003640c1d010351050001f0391903012104007071a103150400030584d800501c45400451035a01c7e80510600c500e08450004d0703040503202c8070410544191036041c0896401c00480e5189038076a8015610004c20030000c0c03e00e2068410b01041214601c00119881190311a051201c101444000f50a016001c8803402c4d080c00159601400b41d040c0e40319140c24500382d495070039518162248001240c881c032401101281d01c20703240e00c2c5113030703001e10940003100308003c01e040c03180c000603640e80d60502c1000100c2b0004081505011038409010440c000c4255140e42201d0b601000b12746652910141c2c003c08602600c182c201c10590318a1900803c8007151200e04403031868581c940919000003c1e6100d2840c2c00c002440c0c030300140300b039820001440d40c0950400c20107009000c1c10400c80100b10b801c01c42c4480900c03450004040102e000e80210009145d0f0a07080e0356046a54000002d0015101a80003060950202000c440801e9000c180000c0d10300305800c80c1808002c06000150280c044 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 561718147 1250 561716897 561716899
    0x3020309010c020406081b1318080d090606090b0a060503040503030c09030a0606150f211a0d060b0a0f140d0809060a080402150f0f0c070305150106081b0703030c0e 72
    0x84104c0d8000194407d0100380c031a8508692954140c041121188250390300c40b84400c2d03e14602d00310540000e84150090a600388520300d0000d24070381d183c1c030b520041d02c0055101e0504280d80e101804070341d007400304804010704020300381580380d814149e481554a21008200b0200c940f4041050003031564141320a83e030315a0042c3c4144030164a84006d41c2c0d00081210805011940218800420900500c0070151a940540a000380003c5041c41c1c000501444240c0c45815482c2d036882044942d0303103071044494180650b1001480703240b1300c0b050007080c04450704025191101c1600c200402ea000b03100b148041c0b9030507a200c0d40c00124a26107a01c0900403401e61590003000400c200f03113001d40c0001140c0c8214001c882458034a50310640d007140368800c00400c80560b5a040003031100070211f54001f4094045a00d08442c3c0030369894454034102042035200c11020000a0300400c1140d0384050069048150341c01c50a1700c0c406004024217580c41a082c0c001d0905480e00760324242d550140200222600d0 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 561719397 1250 561718147 561718153
    0x3020c070e15101205091614040e010204150c0f08040b130b031b0c07150207060f0305130b06041e0e0613030203030f09070320030d02010903020309010c02040608 71
    0x3440c1d1480030a0a4001c41d500a034281c1507403090245460140d4800f0700d0400c440d204c543d004015040311102400c8003c064810740e00c0380040f40e150b8500c049400c000101058009842c5040c00b00f000c002c241e40d04136001c15940e81c01400305100440004414203d40348903401e064994480c2860801810a5041da000d40b10140200b40080c2044903140180001402c1ca50940d50980d1101c099150500060f075008100d14070081074409404500401090f01c0c065080413141076680d101028540c0c18901c1890800507002210100030007a0031007120082e21950f401c00344128603200c0d020400c200c1007528042c1091078001c0115041c1c2d240e650051441c000e18032038a0380c2e85c400c0a0002c101406403000223962602c100c4000408255500780b0004a480c1e140e40070b14950344480103450a401c001601c448401d00482c070b4000000342c1080d10303158040c200b484102040f803101b20b00301803c002e02d44005005690400354141c000a80c04001c450745100f003400c200c81450b03242e001050013801950082c1c44284 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 561720647 1250 561719397 561719399
    0xd0f14030c1b0d09090e030f03090d120b06070f0602090904120219080906030414010f0903030b01020d120e0c031006090b19150311120103112e03020c07 67
    0x144141d401401c4000498040d01d12252a02c4041a034418403003412030000340301100107000c83d0784160807001120103c0e030b0840b410044003241d44880f40e442514402c0d056401500078403400b54000c2d080700000c1c461040100540c2202c034020031040e2090030300050221000b049440304011065050340c14050010340510780902c0c0910b0190090802403022401500c11007211488444520001c2d404080e8080302045c00c000305141880b429800c05001201c01010141e03103071001920074400d101c940055850045440512800c0c05400c54551111860454004402c8601220f40181e400031851202c903200082d91070a1003800c50801c44403040d401ea06004506100311808485d0304154181c2d00a04810007002c5000c0c810402c034441203441207421111541410810f01c403c000a4403030202c11800e0100703440c180c080e100d109660000d0540e4904045000062041c00034030901080c0780079003529a82d00d410900c1300010380c003254044403040100c0e9001080551584690140d40708030080d001107030115 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 561721897 1250 561720647 561720661
    0x3031518052517180c0d060e100227030604032a230102040303140a03090b04050d02072102040b0d060c080a151a0a1e0507110d050d0f1403 61
    0x181441600d603070301d0280000007040144840513000110250950b000b00855003a9406225135904200c40a5940c0d66403207134080580441130000c1868407401001c016591004811000c40049036284191100a068056051030b6280050002e8220b509805c7c988010004204280302c07501640750260070280e8088504000c0101d2512607002d18201d50005490386800d0000c03186c202c0c081d51002a000031340c0c0c1e4604a04510007013004144c0c0e4004d80c5804a9001c0300c6440701040b00c442510308032210b0303020803070100b202641403200f44083c001d2255040018480b45040f01d1944004c00000b0784155030312242d080980c3d5910a45000280e0b100505108034103001902905c040021144c1c3d40c01a800c09a243d0206c3d20008080016100c0b100c0350041c0d10340ca90941d60200b074008070016814003028030040c20254440d0902900c5a2503030742e9904e0341d192110329000c490b00c05d03401140c03405030b200c00030180d00098010502600030902860611910010340d0005c4900e0208082c40c007001c0e00c0700005100103 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 561723147 1250 561721897 561721907
    0x1b01090905090c062115032505030102040b0a08130b0105061b0a03030b09150604090506130e01020415050f040b09060706060f150c0515091608010504030315180525 72
    0x3017600b15140b1092160b84010284003a0010f045041d6815000b401891480a0301c145000c0316884e0800c40300d440c21900e43c0003080c04c980c41a044001c901c03d003c200b8180503507001d02d400b0f5001220b00318031400301d880b23035607100542030041c050f05101e10000710b00103019074120581c1851214030320341111210902824003400410100c1039003030090194000007040380f482c04001640d0b240001d40500d140c10324200014004060150890743d220321481d00d1082c615065000c0e020740c1e0850503000507556480c0010861803030210080c04402d1060602c5a1110b22260800741e404030b030000d0340c060340d55904000004001d813042400040c6014901040442e0454402e000c032010307201103901c803104245140206413404c0c40003000c000d080758401c0403280140c2c9200c081e140d800203c00c42c101c442c00010505261036200858000b1480d60390741c1c030100014954036014881090170245010609107040050001c0b0200b010240c9422180e152004100740d5000d5441c61544480441040d003407103804450020300c = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 561724397 1250 561723147 561723187
    0x19050c10020315040e0708060f04061e270c03060e0a330b09040311190308090d030b0303030f040c174c06080715021b01090905090c06 59
    0x40036174a400c401d404c80d094005021004c1d61180c800034580356880401d00045000b0042c000ca40180d12070646151020160421015104240300003007104550024044007182a081c01c5940300d42c0710181760400300f80400c81720341c29070b5003092001c54a0b0310a0b9030303076a142c1000300c0702c000d0100491920207011130f420705040f1103181010008820006c4090b01000003a1601440210351048005001c0740006c1d016002000008000c4002d4400c25004070502c09041c0e0000e8105602050b2040e08008183d003041c0044618500141000c1202c085182c0200782e0301c0c000200802c40c03280403203010506200e00c80c40e500e0024200520101a034003003001c42c558451404115420340e001801e0207401191026401d0f0f41c503c68a1403001c0c00c0c1d0411080c842440c61180c0001c02401555180d0001c40d88280c184882c60140c003d0301c50f01d803166100070740000c0c03601907465154100d6030905890f02e050341c0e80c00100c0c0b000b112908034002c2400c2d182e4220345410481802d401c07030750201e400104003500264201c0d02d00 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 561725647 1250 561724397 561724399
    0x5091c1101060b04060801090507020a05010c051803070b0a180503070603270b0a0c1418190303050f0901021c02010506040b090f060910030b07050714010219050c10020315 75
    0x100c42c00d5502c1e20948158082e81c021500072032103100040c8480b40c066070080364400010320480308003514689a043c210b6900b0403200c00000c0c000140c01d020620b001c00c119045030001e17402080103a1920802c501e01c1d0080110f804100b0038044c018a031520040014040a084003c003074070f080700d68444010f0002d003034400c0c6000c0c1d034200d1503101d18048107020380b0f951826500315101380c0c40c5989155040004020180380102403060b910443e00c864001c030000760084003291801801118100420000d1100d88c110300d078481c603250710302c0900c0040e502c84285c4440f040c1001c0d03900e403211184c00050781416040300b80301c4d00210b40c0b101d0340b205059054110341e000e250701307807410044a1100c8050011031082180c0c44c0200c500721070301044840c1404c0424541c003400842d024a0003a1b100c0e9550790604a0946207000010000f00c0c07204180085070b0510492032146c10021840d00c00311100c0f1182d800c14075034200050100118108a031034500307105031541408129811540da10300310703c3d07020204002040711 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 561726897 1250 561725647 561725651
    0x90d1211010e030c122110060809190206090103110d050403020c060c0a03201b15040509150f0306040605010602160509194107050706090804050a23040b100305091c1101 74
    0x2c903001070004911081c6445415652f83c5c07440700c00b9006c0c014940c3c40b2080c1030781050303540c1510900c0c8007208800780815031084c4030081641e042c1030070000c0c90440d20309011442100d0402c091b6124140000300800503c1c4d060901d844051451000c1c2c03180503001030103040450003280300081610b9070100458462410466118580100c060190111802140110381d0082c0e074036408500342043c003091200e1495001806c400c0d42040c1c0d11301003030601400f07403400c4a50b16254001072200c9601403012004507440f900340da9034403038a84070000d514100d0162800040a0200340c0c9400c10306000c5d00140380e0700340907124144400c12803105840c3ea2840c401e4000c0c003030741150701c141d1103004445d09000f801101903a80e19800c003011915038000420404200700c850820801c00061140c680150581c010144101e0440d45008428804902c0c800c46e150494030552802036030307405a40d610b400041d03442905207400640785d90b510065a15206600c1c00048194803e00103030003010358004003441e0703c44440002 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 561728147 1250 561726897 561726901
    0x6150703050a09080304151b060608070f06050f030a2003090a020a0504020703020c2205070807030b0306010324090501090c0510030e060a02090d1211010e030c1221100608 75
    0x2184c0d48034011400381c412040c0b00a80d202004501c1030412080f00302c88800c08944405042d9500700440d0480e40c4641d0f00e9804c03406c420801301200c030030314800410503420b065150011800c0820b086120044c41074030340d01e9903035103519103842c0086100d9602c440d804070309031740c0c0307040494119607070768403041c0100d101e84c483c400c005c20f5505040c000d032003c261303164004109901c8410304004062503c0005070042440c2c0e0446a4040050360043c5805205c2c00d440d020b10320700b0300003001402c0e0348841d0425800303075004400400010f40e001c0c0701800401c00e003099034803070101141041400f03012000742c0640030b50300b0030021409201d1580c1d004000c0318411540d84003401180d400590650304440100000780d0031120008085a132550000c2080c002e0040810180d100c060350f90300c00070032000340c030300c80003d00c1d41b02d022081020900c14140841c52040c01141412202d540d102d40d240c00c0090860801040401c005080d08004400c1c4243c40c104141c080004c1c0c0781c100c0070301e0914901e0348501000a0b6940d00 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 561729397 1250 561728147 561728159
    0x605240411030103031112030a0b0f06091005031807140111060103051f06090509010e25050d05070812090306070903020f01210c111c051206150703050a09 68
    0x7241220100401c0c80c40e03402c50b8610b0304c0c10354161607040841a207501954505850840603d00114801d07071352010300058110680341440030b038001d1054504c1c06090200800c90960703071441c81a200242840c1f41440d56a5900d007400c0d08182c5800841411600c102c07000820800c040c010508845e13403082c0d0761030503120035000c0803665899081c400a40f03107800030f1026400912441d005011802d03221040410390f19034807000e04007190001c8652140cd650344000c0c81801c036409000e07003100341d01c00c0c001c1000c01040707498042401548500c1928030424080494404011051000307200030450760050b81c1c540060802450401c2e802418180d100e40200c00020300e02a0041c00c02c481070340c0e0094402e02501076030000644800140000040034826000c1c9c880d801e0444500903526141d64664606002011501c0d2143c5018000c0c405901e952104404d1420040ea00409540d5811190100140b8079221100810215901d00f040190880c5d030001d40c40f0141500280101060410340e40c800c045156140 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 561730647 1250 561729397 561729401
    0xa11090f160e0d1b0801051005130603020306040c030c091b0806010e03011d070807150c15230a050c16050c060c0a0c060309050304091806052404 64
    0x100c04186441845000c601031008007440e0801d000d0607401c00c034801c1c0b1420000504210758941048130510103840c00b110040c540d2124400080482a00038849400c0c12a0b40000c404140c0c0a154000c10403400d441c580c084140d003103030004680190a0fa003c608050030080c003030300f00074042030713510190152000801624600c16031400100b20406030303180301c001c82d00890320203401900142c100003003107180d0310180d5000c0c0f1810b950b505491a4001e007003800441400e0810305194404889500100b0703040014018610410b0001180c902d42040e08450f41d2400d01a20341410419840491a00d2214007010015104104920802448100e443c1e0340342d04051082e18021640c0c8103100b0018030815200e94001e407229110507119400b40d80c211880c000101c2c0d0960041d10b0300f03c0d801c0c7c1c40460700609000320885c20b08081c0540345414030060709951102d6a07a44114402c841040303a880c00c000c01810407078601c40440e03030b5000006008a0808404680a401d0400f000d1340035000101a0002c05103098 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 561731897 1250 561730647 561730651
    0x11011d0901120f05101a062d07050102040b040302150a0c11030a05011a090106080f07050703210c020d03060303081b0c0f070602070f030f200d050a1109 67
    0xa01200007607082100030820080c0075501195030981c14035640c00000d0b41485520b051400103603002400c03000390200c501c0d418200428140c02103200b085500d002100c0c5e030b642c03980707642c00c8684613200848945500c096141b10f0b181d0b000c0c0c81544003050119000346554001c3c01140d0080704d4503070300044808107401c0d0328451211500003050007a5402c0c0c0c00200a90351302008000010b061743c050810035103d09094440003940c05240588074940401d040c900984100d015100d1443c0500301407404c8000305800740741c0a0706102c03e21202003035100030148a016200311030f1030411865000c40155480543c05848bd400100b80540240145901c40a03c24440c45d02242d800d81e840c40196126182100c0054140140005503c0010842c40c01d90380d03400c01046805a1401006044c2c1605e4140f000b810409590022440c03203146000400100e0000071a1821305c540040d1107048032001903403c8280e400f0040200d0b030b00301114164100501c4001f080f0b0303548060044001d54608450300c4c2c10403003e0401 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 561733147 1250 561731897 561731899
    0xf050103050c0d1a12031b0a02011b060207020a060203090108180d1b0615180501060f030c0c050f0a05060f091e03130e07030c1d0d050c0a0311011d 65
    0x280002041e0743c42d01d40000315500b40e00c4400384880d52110000c01e034030a07030f8040000d1555000082500c0d103140340d4080000749442c1c000203000389411a0380000c00000c2c10215950526409409a50a00540750704075000d00798000c0559404513a04c80340a91640c014006c0d443c003141c0c0c2640092400c80c0031400440c40070207240d020b480001c8000c401550702c01541c510316990600c010882c200010342c1481000000c980701803e06101030f191a0b50600750408103204030200c03d007044010016560844540306920340e041c1030204406d04207200442c1c02407400030b406030092248110000175004c020410542c024000c80035102d4507600c40401c060000001e0b03075682e09aa1152080c08000c000060301d81d00b0715194075058910748002c0e01c40e00000340804c0c0c1c00c00c0c00041d65041c1880720749501441200441c910300c1c04d14086000b204601003800c2f002401c2024080c400303414050040240500c041c0c40030540042c481c2c0c049070349074240b610752264050903807030200d0700c007200f0300440300740c076003999410420 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 561734397 1250 561733147 561733171
    0x9021309110d060e070f030c080c0915030102090d1407050910052b0c0e13030c1104020405041107141f0c0309060c020606040b060702061914040303090f05010305 71
    0x144005125411986100c01c3d681d86565070403011045000b400f0040c000c052042c16a00c60760b05509003903d001e461644890b400c0d50111040d450306490302d5651941c85911035504010340751000c4040390291007018180ea40c0000b0300030109080143c0d9240c1d030408513510804581c034071074540003071007820703402903c0030648035250303800800aa02d8030b64020800311000c558845e4604a01d0014031040c5084800211500300c0050341c18050780d030b82440c110368030100b608400b102c90011610301410080d4030b6030001e03001e03034a003501c05500e60700c8540444004000c058010090288181004040d54110b14400c49034522030442060300c0300c1300050840181c5d40600e000103540504d941d22100148800c518110515442d0031010000c01c10300c0c0310300d030301816940c1c001e04410b161020400040b20f600d0180c191241c403081c400a005602c988007074503401901e501203001c0e011400001507031480c4103115400c545400c00600071041640c810180c6007110640c3c603002e40e02030345900041d02500c6049510440103c = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 561735647 1250 561734397 561734423
    0x20105040e06300d09211110090807050d0203060c070302070b0301030b04050709020f250803131104141f050307060f020c120a0312020412030309021309 67
    0x505907034007003508a440100b080844a00e031800358200000715007900841001c841c1c0381c5070010325044c44005040b06061030542c00407401c24501d41c046800c00100242152885044041001488900c028085000a001403a01c02001c40c1c02404218140940d01090044007800140360624001660b10190f0003405090960340d0100c0131076994108100540440c8122000003507140c940f2130095010350b00070440b5014518003800e2461034400c40e0361007074071111720400c4415050385101007a68088000025001180401002c070340494188020000c0c004540020510099a03040b005d9283c42078400c000b40d01c1e04801585c100021a030200c4a041e2001d80003600290201c01d04c2c0c400c60540c3c03524110f5240f003a58031840464a031034299000b000104441000305015207404011003440b00f0b80c21114183c40180500c41c8640720004100c0003414011903c20896035540e103a010f8802500c160704400208460904008015003c4941c1c207a00811070420016a14100c5010b0310140c10b801074245c2101c6 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 561736897 1250 561735647 561735659
    0x23d05010b0702090a021c050711060405120c0c10030617010b0604030b220b01051504080307060506010504031e1208090601030b07020c040213030c05010503161206120c2102010504 79
    0x40b61000709545113055080015103010307c0301c50344070210149045800511890691005840c801c101d1075111842e0313005004100c002240001d9601c05001c64000c220f45560300d00211510700515403842e15401014507000b908002c0c0d069010000719203842840135030b00740442411508a074558411940c112204100520210307071841c640719002810542c0582030300b242021640b8440440c80c0003190070059101c010050f0f0700e40048a00380281c0d148115038981440c0c01041030b41ca1151103402811036480e400001c505a0142095034003c682019010b070f51045840c0038034280841400e03044600207912180503e8492180071081c1c070036020000108401d900b561501c0c015031500804180452080d03022010040d2942d002a142c4d500c01c64181701d54150461400b521100003d422583c1004414810000181c811128411412000b41070280350360000d02d0800d005000305810481c00715802c0e0404504000000910208403205040080044e0b41c24502054407000021806400194280414018 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 561738147 1250 561736897 561736909
    0x605040f12110310050a0b010e090a090302010902090702030c0706091206090206040512150a0c051207181401030f020a0c08030c13080d02190b0f0403023d05010b0702 73
    0x40c90700511182c0012061080020f00d01108820400400e64440051240e1042980104807040c1000d08004201c003000c0800300301c080e580207054603482c6840f0300c0c00341c2c2814000c1d40502c44041e005000a20070345415040039540b58010b002d804641e101784040011000d11804204003501e082c03142424a40540e42c8a90001d01031991060703902c241708100010306070f0f507504051615100403002400070409015407003140c24030000c00c040346181c00c0043d4041c5041d40901100e404140c20901038009480340001180c42c0c98200e40e002032920403c0e00081000c1d0750015444070068000d80e03040c05040760806015069006405200012540c0703100c0040c009110b035400f8541c00703510318031100c2c149058400c01d19000049940502c0f01504030481d50100168107000360005260801011000401e050303491040c001c00082002400300c00c510702081c01c1501c00d005401380040e0303001c400f4a070b203c0c0040344c0e00c0c0703008500040006960f900700142e0301c000032580641ca0403070780b10f10f901d00d04001c1c02e07409000d0 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 561739397 1250 561738147 561738179
    0x40504080f0d060b0417070803030106080402060a02070e0c09040c020705031c0c020307090c17010e1602010b040e0d0e0d08030f06060408030409020409140f06010f020c150703090605040f 82
    0x21440343c640e0808500400004041c0c0010130303451422406c0c42001c2d8003082c2c1007080c00d070000c9035250020001070080c0782d00080d6041c0c02ca503059a040d6507410054000302e08028964000c1c801d44d6101c4400d1200d120881d0010b4120f41c503044904004000c8241016030340d23a5120300c600354240d0010301c0a0040100015080303085c42e0000d00f4122007508041d0300003428401c09400514650740e452506101c1380340c0c0f000c510342620520003c0c0012a504125090702051402044140c98251400b00f1a2206100b900030f80f03032403200030b001480702d591001c00460726010f02200c41c00c0018819a00316102d4680000142d064507000800149581c407560311201440c0e100502080c0c00c42e07010400003071300f11403c01c0104020900c8020060f29035082c40c140ea0103960702d0141c0c50300c1d51200c00043c00703a44a1696410342d040754090030a03030504081c4200607424005502945a1b00400c81c0d18141c0d9400454001801058845d681d0010380301e865244c02e40e8140218001c0c241c64545c3e6000600030307200a0b88400c0 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 561740647 1250 561739397 561739417
    0x27010804031709010b0604170f240a0207080c0601030605161709030403020a0f0e0c0a050d0b041107030e040c051204032f01092d0204270503070b06040504080f 70
    0x41005c1c2038400c0458050383c8994400240004d00100406c0518018031100541d1140740e4080d2150101c8000c0c0000b241d40001003012180d0604004191002d8066048400310360f4800000f40d00d0381502507e1f146c0303a401c24031064886908000001d240415242101041818075480761001c8400150b02c418081c0c0e4010019030803444100000300140c2d446120250051020400f80303110300303080060b0320349001c0016042c8071101c0020b22140c0d50341a08941943d114103600c0301300080120740341d400503002d0300d80038a2664420b00001403a03000c1c158803003001c0307070b460806880521001c1803886007118144113070000301a00a14500118000a00c104460707000342a107051320800e03c0400720110801c140c50042c4c0074040341e40d102550700c00c202046007142141900e90f41e1003540c0082007414041c0118441c8402840348d55201281c50011100e0362201c4980c2a0340d11b8810004200c038039046940317034801c40d4252003a9542000041642c0340031700803140700c0c1da80b02c203d45041c0029141c8100c0700307400180000c = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 561741897 1250 561740647 561740651
    0xf1104170102071e030212090901031b1809030306050a15200304091b020d0212220306150801020304020f040209180705190219030c0312022701080403170901 69
    0x10101040c1450114007446030031030b0204ca100c443c00c0c50081d180c001e10400240310068144640421580c80a00c4641103d030010b407544806802d91744003072030b0207810341c200144403281001940c030542c1440c0d0011404520a440803c04c0548400030007100084510640714110700c98103403103581c103218888407604860703107450103d034102c264003000e411174005030007140c0c0d0f00303684045078010b805140d03c03040503d030401d0018000c1f400710940025104c0104a000b004103400000703e0b1404400c8002d107034441050010032451040b522407900402500c80c1000c40100380812b41c6001c2044c0d603041c03007101e008681c020422409159000d041c0b001a40044a50607800020400e6400540c60041c64140c455202561410741d1054502c107000544a60420300f0b60455001880d1440304540030b10048900c0e5170035007082228241c4a1900300d03651415100b084c1c00780c9002258003503081b03c0e2a501250b05122015410783c01d88244401147c1c41c1070102c9016000850070702480344c00120071002d55401204440c00 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 561743147 1250 561741897 561741907
    0x170c0f031b0a09090b0a0606080f04120c05010908031b04241707111002180603131406010801061505030a09060b0319060c0201060317031024030f1104170102 69
    0x301100700c0e0702c030780303030583d14a0f000d01c0420071906d2003440781d04050304c4141088080b60420289034040003100501c0140765005000c3d020500f207015020305803400d03a006000b800f03408650710b40283c540c0c0065500f0200c0842c0b1155020f0088a12810748040d28160521b04034241c0e41e0b07c07407009204e000c04e07110000340000e800c8100d40780100f078260180b0031ba240ea16888a1144140c24241c40d10740030500083d80e803881132003602c12490b054240304e40c0d0741e10b04640650300c0e030710b40e2503c4040089078040020010400e0000c5e080703140d0004519281200d501000030424655159001e04041c0ca86100d984000342d420000148041386c142d00050b000c0707000d9074000484016110209241480c079510a0004843d60600082080350500601e4403140c0b0b1032000f402120b10f1581c50990701c80344000b49000c450800701c00212050410a00c2c0e0300140320002c84d002c224486001e104400138510950310000a00b0490561000c04060203208401100c0d51005842d041c44c1c002820b44a0219114140255400304a = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 561744397 1250 561743147 561743159
    0x112020a050412030309050d05040807050d02030f0d0c110303031b0304030306090f0b12030a020d0503131b29040b07050a0c06080910060b19020a0c170c0f031b0a 71
    0x110306003c54480e8078005044004d038188141380c60b01801c80320042000410044c0401034020844a0450b0419a481c003600540c03440000d00b041100c170603041180c450325000140c403661003003005580a006484081c104100042415101c1c80119000546405000c13400231070140e4500c000c541c010b01074540011019100ca0802d0240c401c0074008c10a100d40b1600000a81d03e0305088403410b81c103845004502d00903441d070340130751160a101c0e0100180b1001100240706c0c1c030001480b6900c0c542c0c0c425000d1f00f00d900300c0e6440c112074494500440303a0400e4001000084001d60309241c00401f054010b91900307192804010144607803117014100c4060040b0009440014000003041d40901600d881c1d00005203400b240709442c10044c4208602c903503007030002c1008079149403002c0b242c0e4122101d12651404e840c40303d06038907046010b88014402028504001307450448000c04551109070041694a0b100107401005206000090900d40c590007140705814503e2030202d4118640034060031094602ea9072341c0c = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 561745647 1250 561744397 561744419
    0xa0b040c090b0d0506133305071701150201020408150103111806040b060705030a0c021e012001140403110c01052506061e050a080c0112020a0504 64
    0x61411a28030342140001c0c821507440d0b01035000009001d46036020401500c0c1c4074940e031040041c0ca00304c006004040c1041c1800365810904500c011100003411108500100759800e0340021001c0140036440c1c040851441445220300303040584101080b401c4690030500406003412103091800155907081100091a013806c0c4840340a1260b9007910380040c2d032440c24844656581d41c10050f200320b07081415039490311f1380030642c00d821140540340003d202403110080754151182600180035448081280032600b41d01c44007105080384203580c400c420010026880070380d081040c0c070b0f681c00306811500c44a80c5080c121910061550071400209054001e505007101e2220142c50944c00110145103045c0c07a42000c0142c50103801e0286051740c41d00e0501003517030242012441d140c407140240b401c000130a105140e0850340c050030340c030060800013008640034183d1118051041c42d000c1e003001100000c0ca030001041d88106030340c040c1c54001c980c00402041000a40c4540c04010078044144804224804a5 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 561746897 1250 561745647 561745651
    0x70905041107060e1e061e100b18132f09190510020304090501150c0f1103030d091509020f06030703090c0b07030e0f060412030c0b0f310b04050a0b 65
    0x10102608880c144407008203070102c087c030b206007045e80440701403161a4004a264500700c4484180d11500c4410040c131034005500b1034052594800e0b404001d4040300d1b0000e40c80000c404510b00c041c07114a083c1280c0c2e1600300807203030b240b20000325010f1010003a54200700c403151000c10050152a4195074444001419075142c13064030b400143e0000c1020304c20b000b1584211809000120f840c0144074560620090040d240d02200030240c000c0454400c0400262030003503503002600030140d984480150b00c5440003403c0c0c01e001074400000c4d001c01302440010310320039a882503402420f1b1800c0048800280442076002030800030406613180300100105001e00044805080e540c494250b4520540c14010000031110024030320803da046808200f541e03d0700700300c6089800c080c9084101600c1d50405540c40c0e00b502c4400780055900000300a244004032035580c1c0324a80c4d0100c8240d40ca0030b2416070706a048017100c030b1105810141c0c6a140045440481c00035032080c0700e0740840d5500c60a55031810180241 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 561748147 1250 561746897 561746953
    0x10f031b03050108060f0402030d140d0c0509030d0503060d03050721020606011e120c03020c0102070f050f0a0b0c030408190818031218030708070b070905041107060e 73
    0x15890061104d5481449910b8100207540060380c501d0800e6000251140c004044803000c0c4010101f40074420340052007591b1120510120800461542c4a000b908030383c0202d003414841d00031800609101c1f400f03002034a00410021340103084c2d04a80d6602990a540f105000796150030764a40403d00240b0a60040a160b05070317a03000d0300080c2400c1001411070314140b001d6640c01c6411034240e100032a841544416070440c0a040842e801c004090160000d100d1000425019400055142c00b4445a411690303809441203084495220440907040d031a642010001441590780b040840d00d20500390005e950018007508103607141c00c4580300d401800c051922449c1000c250a4401c002d4420b003c164440303019104800590300c0c10610762800c660888004006910303c00b522525641d10200410544080e1540031001c0b40c2c1d83e60b1030703040c140351410044520b000040c80710340c2e000c0313403604160103000ca404800008140c20320310b00b83c0c0c1c1d0201420058002e16043d1061450081e184000140c008041400c = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 561749397 1250 561748147 561748151
    0xb060307020c090a0908090d08041d010e07080903030403180e07170906091e120c030c0f032812020d0b0a090c020a030809030708191b02030c010f031b03 67
    0x1041c030103102400d0f00051601646900d04800740c8045000c0800715012601c084450702c0e0300c170304145040c0700c540c000d41e00420400d000428a40740e00ca40b0031036449050b6a2032110000440da100702084030500f008031140500fa410500100300001e00a14000e62400040c1201007039250f118040e6880010088905200003810b066000d8284042c42c0b403a80e800484880140c151b070714040900c1d0f07503101c1109440c2c804111404c51160b071510800d00042400c0600c00103075a43d50b19040507901d642c0c1d00030142d2411640549298442280700000445801034901d5010300006011481c4a09044030540030000a110300c1c003102d9402c684281c030080c148ac03464480c0000c1d48240082c1480500348450300701250f403038944124440360307030780004000b030850380d2600d0f040105d55118900f160460103070410080c07903114041041007559418034100030030203425035100c1c030410301060314142c2403004940002c1e4040e04079480c5048a940700c3c03468840b1181c8103050210b8030001e0800f03240542c011751081c0c100066 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 561750647 1250 561749397 561749413
    0x1110050a1e0b0303090f13020409051611070e18120c010b190e10150f03180201090e060f0a09091a1b031b0a0c0215180d0302010b06030702 61
    0x416001004403003104040e204001c101001c1e80880d5481c4111100c2134071884102c2029406da0340c4000043d03601039100d0105544541e03132010500042e180c1a04c0326040d0404102d26819001d11600c1c002c85d6640c014801460061302d410540351606001130440200d40040c4d0720b8481c0300c09400c001c5e81f04048803481c65103641e52040c650305800c43e030a246289214010070440d500742040004c0701c0c0820390342000c409485540b544685018036540c43e900c5204c140903000740780a00c030b540003c0504040b9940c2d40f014803085204200240c10202d01d40e20080c081040d4030800d00c2004040741d00b460740440d01420701c4000e03010920006007160300750ba10002c1090740350440c2c58108002010540849500c020402115040030041c0015041060030740100304d15000c800201c105a0b044056481070410714040c83da22854030790300401e16100f40300e080e401024000d08200c10b038908038003100d598001c01c600014401b10f11800b04102400d1100b429800c5640b0b500c0b46504582c0d64000442c007400c0c2d150020400c0b0 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 561751897 1250 561750647 561750671
    0x150c03110d02060a02090a0806040c1a090102100507110a080408010606020a051513020607080a0206012309191e0e0d17100f060518100f1110050a 64
    0x40c00392004048640c0208400740070854000500341c0e000b481e0301034050b0315840d030b98000c10081130b000c0e17103c01e07454402ca809000c01e1101600c0404140c3e0900d1440d2801204400310685482c031445401900603880f00d04401d20940c01d039446160040a00e00c0c201082d14101c40100d49026820700c03096030700100000701040a010309204000c01441c40e4009008200d500d5281c8a4440701c07020409141612140001410100d043c407040904030f5008200c16140c0901e400c2107842c640004d9440e42c00b600c144000850303804454407504e80502c40e00c1403000c614180391000d200c8015006407100c03080581e106004c0d00100080d025071b1680000d050303030094001341c041c2000415590032002c07202e02d5422001c84500c9841c0c1c0001c4100d8040d84100320714115071204400d08204500c140d10013000c15a160801148590348000108001540b082c03420016030920020800c104000c00140004146c43c41c038089002c5004050001d0345010704c5c419596404807404c5100d0594600b101d01485055030f1352014000 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 561753147 1250 561751897 561751907
    0x609030a0207080c0a05190b0a0f030b0a0b09040b04090b0a1506080108033106021f050c0d0b060d090605010501080a090c090213030639050a030902040204150c03 71
    0x41025000403c5019084c81c00f2803400c04141c05280c0c0a082c940462103801c0100b4803100000b86484200160307a00c5400340001d1400d03240c0da0045002a0518520021600c6c00000320070035502d010383e040b45012018420840108001c00010350020f4446400c040030030102e40c600c600c10301d0505004600107090401e6417607134a00d0307908000b090150820050200901c004295420098224940103049180340f080348a10b06819401c00219840c812010840340c0c1c0c0403900c4c00032941c51043c14016030420b040103405071074040340c00c1c482e680c0341440401005142504442c0a401d00a41654548600e80580c7c0041e12411001500ca103a250710040100356400103038180e20690343e1004110b038419a41e51041461014812011141e8022a01050001c03000d00800001c41d80100204410540748207005c00b8503c212044d1849258010701c281c5d01844940316074051788071a9690a880c290441409030300804400d1010b0341c001c1d900344408200b1719242415074941090310348424123050018540141 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 561754397 1250 561753147 561753149
    0x40c0905070815010e150d0e100b0321120a230c030609070e030106060e0306010501090302060a031806050114090a060f03030c0f052d1621050609030a0207 68
    0x1000105810032404501841c0c0b03204a040e82480e2048550100345c000030500c0b501040422840140002c54a11040040d44604864500ca4003600c800c92006800442107074440750038680c00d41c21100c448140702c1c030311144156100300e82c2e05001d4100144221a500700581c1110300e001119903c2802016101d0304010840d18800f0714401002c1d00d1801c0851a00c99000280c00c02c0c4c007400701c4402080641d406500d03540008400603000b04205541c841b0000d2003c0c0c06810f140d0b01a00950700041225481550204103480d0003501c16840c0c0b082607c002c400400b1904a0f40022400644003000000c0c1117020700c60081c6443c030042c04900c0e03c00d03010003100c01400380058400500d003080070001c2101410002d405c40b90982404281c001081c2002c0143e01c00340d0074024154041c102da101038407150421075142c0d12041e85a00c0118440e510702065903605000b200015105410074100141c114207481c9902118081845410032901c80d0740d180c3c50400c050700c0d0a5000c2d0008110b500f001c86c1e04200e440 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 561755647 1250 561754397 561754411
    0x90f0709020f0706020d1d100605060f1c180b010e06040b030709020901050d141e1b0c0a0c06080a0f06032001110d090302040606050a0e0f18040c0905 66
    0x52419891880982d030600c900b02008201c2d80c3c0210f00b001410115034041c1c001c1072138502c00280c15250844070a0f840e60090142801c165181040c04103a60030f01c4401d490b000c0c0541d580c114030b000248a404c103014440c0703691410100f40c403402002043e2080c0e8410b41c051501c265841c562030f5051100000324200b0051074140070794a004541c014654000450070120b8140d00001a81c840120340120380910902151900146c1020b007502091110201c440e8440c04500240c040c0e01050034820080c1d445043d02c90401c50f14189022185d8001c202000300304100c220703000c50300140450380c0e940005208540c85034010840e50f80401011032440d005410040e1841d81040081034150b6446060f04440c4120034064020198103281c0385134040c60010509481c0403040b030b085048030300d1000340040c0c2c01d40400ca014500b041c10015039a401282641d21480e050748030000e508051105000c0c0c00400c80002941c42800b003c400c90f2040ca075a401c1a0040f4041c0d4580140e003401d052102c001d1b254040d08403 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 561756897 1250 561755647 561755651
    0xa0806010c15050a020d1508011b05030619120312060501030605010c17132d0e070c02031006080303240303030a05060d080a03050612010e15041a090f0709 68
    0x260000a11142e0070280da0405820005025200c4c503801000034058200c1000401e442c04034466907100c0812040412100f0b098004e1101c05034512039031405000c62140103021490510100f46039107002c04903036800c1c0d08090815041d541c0d44582c2076585032480e00090700172800c01c0700c022038910400c0c02000081c240078217040c44100c0c075000000b000b401c0c103034a0287c8045000f8101032450000c1c9402c481c0c2c494666800091038907143e2441800c103c503060441d90590090941d141800207440c601a03040304c01088030031501d036948100a84100740d00d039200701e0307050191800106181c60300f48102005001101c0080d41c9900d404076800380610310505419090102c0c5070210340c070580c1c2c0041120b500c83d2146202050544560300404c1a0100302080208180e0300824110403640e4154006489010704840784000030190302e034018200c0b900342180020315044000035401007142c1702c03140c9800521401c448050340003d5200b0b00b41105058a80d4030694001c2550040000e80400022002c2d105210b42 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 561758147 1250 561756897 561756917
    0x1806050403030e4303050303090123070c02030a14070824010512010f0504030f230a11030c0f1f050106120c0203090904080309011406030303040f050f030409020a080601 74
    0x10081500e11800c2130001000340e0114210b000c9041500034044880074a02111003242c0c59241403030326a002100e070020998a000f0802c43d0500344410038200c03480400c441842e007a00c407000125007907140c250b420390305403140103182000110340c0201000c07040108805405250309001c1914104012807040005d1403006110280480c801004c0190440754110f42050114402a0300d0902405032405502c41d035515000811080c180c2164140c094504d06688070382c9090b0303c40d01103401c03100500d013204500304000d21000c020f00e030241120310b1070034010004803400d149a80000500d4501e01222100e0a43c00c141e82c12a828462070300040441c0a80110038815581400e200500045000b00c2c0c3c00111a15841c031568020f000780129429464090401c640900e080e00300140698001e6038100b403290b1070006503128800050500902800d0020003452443d10b40c0c0c0c80b1400640209041a40c00303001e42001260641003c0004100070480c000c00581c86825032035001e846000c008085605000010f48 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 561759397 1250 561758147 561758173
    0x501110f06061909020a0315051f0e12030412111c030c02011110050117070302060405040207080c03070f02010801060e030606010804083c0a080c07061806050403030e 73
    0x1450070350014083c1d480b4504040b2120780114590882d61000031114400950716081035855000080804111034200b20082d42e10010302400110a002419032500c06003940c542c114801c034600e80010400816021054840200d52800c40d805a403004604076002601c0108001203181a00c1d00300b0422124500d041c0e9048802c0340b042041c1c48070060400003111040f20440e0f0040000d810341c0580c0c402242c43c1004400d985c200140000e01030300020540311000d299140000003030303c0003a05d41c050002c6090a00c3c00c410712004c0d42248400719004a03080c0b140b04110300080000d0941c0d03d000740f400c045401001d00002d441a60181c01200400680d071040328080c0e20300003000d60b000356081c41c1070055076645051080b401c0c05003031006001e04a4202e07101048021888a602408880402405090031502e1222985224001d45070f00030903020310004003042c45000151411b14041d4201161125040c842243d46a061030030849289903a0014001410761611a1103c8001103500608200300340b10 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 561760647 1250 561759397 561759403
    0x504080d080420130e010b2103040e06040222091416080711010608030a140a0c02060f0d05010b270f06090103142505070f020d020612100501110f 64
    0x3401c1c0c140d03e50350504030254152206a11280d201500010805c8180403a29455028040d20a101e5200e0510801d055130022501c0d8039900e0115004401145007d140c911032426211004100030342c00303507090060300040300e03840166a003055000c0210071b60741400c00c0485000c8813408070f008842141131904000e102c04249107141120b14090810480d130b41c1c0d5040e0116014042640c903032045508180d000210f41e103001002e00f030192226214010000108402100140280400380d000601e42c541d07140054101a001801404002c20606207444050442c58080e60805c0e0b101c01d005460011707034905030401036088a204040c1101110850b40c07000d9002030005044a0400d80c8510030010b040e0050703a000f81e1042e5000360f5146581019481c1a1000310854007000c281e01040d5020540020b9800c1d01c5142255642584038203641102c50094003030245100f03001d60308070382001c810008140c0d10012186007d08c5500c5041c042c03042c3c039080000051900e0344820f03400c1529440a00380e03001020001c = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 561761897 1250 561760647 561760673
    0xf010617060903250f02150417011b1412010b0702040c050a090306050a18060b010305010501140304030807050c0303040f0c1a040905070e090c0c0d0c030f11010605100504080d0804 79
    0x1a108210403104c2d43c20100200c0704103410007076000c03003030410000005017210054000c81e002c1703c03008482d400540d019242610485c00d0342000142c1ca501500d00c4490003079015030100d010f10925207042480680e14080302013400c0c5c00410030b10002156810440c90940a222190601031030200e003040c06c001400343c00100980001409591150009070540700d00f03910080110761111440c0040c080c00d410208018113401020b41c3c0000d04102c00400c0c2c0754050906110303442044c02200d459a41c803502d013280c1500d40500b1b9030041040404c0416801c0e00e042001d14026805075919072181031442c44d12125581d130035804a40126082e42c0741203040710044040e20f0468031400d00126490391044070844030300600402d4290b003c41d251040c422140100c5019010110741c181c102c4820301d4020070282d41c40041031500400241c0002e122260241c07043c200250360b03100341e05c0040b660f42d4a4800013000d0904100703c0000040d40413408215011040021b80d103035131100c1c2011041400c094580052003c00 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 561763147 1250 561761897 561761947
    0xf06120c02120a0315050a050612040c0f1401030f05091905010e160311010203090d0f0204060503120a0201060b0906040b180402070c080607020c0a0510020f010617060903 75
    0xa40d5036a000a64000e1202c0800b19a40d03554040c0d488440d2000078006060104161042c119031020218040c1821102038085d10802028141003040c054040603c442000740203c40701400d04c280001c00e02800300d417800c068001256407090400315075000408841d0700020180b444d03802c101c18003030f1211020501584084200f081c070241c0400500b0014050402d002c2c10f1340c03031881005507031601410300030f078528103a030712802d00072804103205401280e8038042c2a4900d81d102c20450120030000b01d40600d4940b101e44060000300e2480d6030b0760002800d0001903040c2e60081440002e00340c88603a42841071501515401003a00e003000d01c40e1020070428000ca0040060101d400102d035440d000e0380822448120388000d00c00d550311051450002d080c1440340c801c0301c11500ca200e01007101e40b4008a8002182c08001d016000203e2500040011543d11030f46a4015402540603000403004207000d844003030000e200460404490901495251202c002c0800c1c60301e400601888080150314200c0300c0c0a040 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 561764397 1250 561763147 561763151
    0x906140a020f030d1e0e0304050607060902030a030f0f0819021c050c040302040b0915040c111e06010f12063201030209010902120a0f020c15010806010f0612 69
    0x2601040e450b1404400100c115484085040340c403485050b007000d820b50105501040070a0001540c001c1950204490078461741c000384801d10950a00d60b01408100380161008181641107401080c1802e6500a0540004450000805a446d0414500452202c66103000c841c07034600756092590081108258014841c0c000401500103035401d07295200d0316080310000c02c0b01d0308004070450090341c441e120480c06a810014110a94a4a004028880c5500c1401400d0603101001040010b09030030680000b44064419102020070301004280501c801074800041400008035802e450058140d10001204001c4841445a08508540c00e50703d141c0c01070002c103a6081c90405280321400740388004c054881c03940d44d80403826240d40100c1d4101c070b0081d03450040603604c420042060b0b21808200d604003201d200041414520568052480015651001400c11288509071401c295080594207d0104000010b00801205228950040c684005507a10700c61420744094460045118490301c0c00e9 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 561765647 1250 561764397 561764407
    0x11508040b06060c16060305150d0f02031606050310210303020703021e03030411040b0f0105030901021b0714011e032408011505041a060d090b0703061401090614 71
    0xf44960302a40c003020314030410385840b04520150307144091040d03c682d2000a0600021503105000f6854080c01042c0c003801c58098220781e9207921601e40350664040360107102c0d103500e00c41c90300080e020f400043c0040d80d0f86e280ea00d00302003802148004854024046082c141080802d15070308001c140780000c0d0b4141005130b2542c103942420ba041c090514081182d484820f2030b00500b4000120085115511800c21400c800340700c1c0052200f11140803e1480d046002c1480019680d8051400307990b11241480002d4981000d44485100c01c1c1582203803e01d299001d00380070f1124161181c8814001e40d820301c0d0188000c004003003007020a036180700e050700600d0b5440c0e59030400c0056102c0c404062918442e01d0301100740d50341c11158001c040e800380c494800503202d07001082d2440d160142e031b50608000c00c082a0303148803040402031103034891502c052240b540da08000340001e02507109981704a03190744000440e0f034030b01a4040e4103c500e01a159042000510040c054960420401c000c0c2003100c0140903150 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 561766897 1250 561765647 561765649
    0x5030604030c0f0209180f0105070206070c1106071a010801152309040302030415080108060f0903041d07260c180301091b0605040303050f0d02040b0c060609011508040b06 75
    0x80e50714443c010b50000240c004010a0452100b514082050345004491800100310304090032030703101f602d02c0710040c3c015402054405104100c13a01469010f010100300d8440c6600018120b0350041404490046c0140915000c07000514071302e0340100882002800a00d1400034410524102c40c041d41404500c100c1001c44c214285e00700c041d00103038000e8010840340c106800d020756203801c14030811450a0340048608107203449250601d04039084c410041c401501d500d000501031401c010410007e51109100014110b0988509031180e07030074250306002a4105100c0040c89842100d01403084114014042c0c464a20720102440d882203851503c00e417103c03a9000703440c44a02c04e140c4030590541c00c0920301801d104110002690790005000c01c0702000d80e0f40c04080d2054000c511001c3c001c20418401212204541001007004850082005107801e4441110205d2500a031921601c594804020032005040501a040c003415030143c0007007080b00681c5005080050003003004151803030780e401060f06 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 561768147 1250 561766897 561766913
    0x7020d0c081207180605160602070615092901020c1002010b150904060501080402060d0b0a030b070f11280c03061103070806100f0509120105100f0f05030604030c 71
    0x108440c019007220742c1d04260078000e040005a03449200b0509840b0740010751980954102d030101250b003e5103500d042c9450b11400000e410402c000c1e61083d488500008980c83c1c03044142e8050042100d000483d00d840d031308015103515000103034103540c0c4607500c8554003030780c5c000406e07100854088408803a1140d044408a014207605e460164201e1003003001020216410005000c1d0b42b20182d500300155a42e0300c0c01114184c0d41981c02035004001007003c8244030a1580113140c5d5644040c0c40486115526500c40b400c06030304035070b0a0001440b849030321840590110100700c46c08030b4000202980815400c10001d1a43e010001c40b01030700101c0303045002c200490103444d004580000041099181c2104101c1940d402117640b080040c03040341c0040c05500d007980540540512517940c003044c82030203e0080d079550340000c1170380740d02000c44d80402c110304009004052040d4a51080212403904d081c01582140c0c0c400c0d004100036106907a27080c00185c0300040d6156005401d0b2802c002e03001014180380721 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 561769397 1250 561768147 561768157
    0x1050d0f0b0924063912030106111c0f11010213051306080a02040c120515010e06040e06010e0d060c090302120309010c11013c0807020d0c08 62
    0x42c1000c0740c80308008101c0303440350841040c0310031400e65404607229407007004100d00c221140303480e000101c544c020001500880200e41c0b00c541c1d150000429400d41c00d261842d000402c3c41407400c0c003c0000060081d10b902190240031000c0550003002054002581c0302c0462426080b010100441001c44012203803142807003100019004000715526203480c60320420003449801034034010020700d4426509181588921030484007200040e16108105034204030203000c07940b009404200300e00a4a02d8424a14480d6900605041041c82800078001c000900b120b181c0e0480c451145105000400a080b11903407811750110092800c1c2a1004c0090001081c5082c00790010f0040c9240c0003064034500c0c1c105200074150b0b4004c99008414070380e00c07072171155203105821081d0300141d944a40a0300060b0024001c400061050408140c242c491a00c1d0402203d804c091840950f0904207414400420086a69000721021700d400d091034a0080c0e8060756034042340b03904030100152010f0f41400d00090b002030724 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 561770647 1250 561769397 561769399
    0x703150b04150905031b01050d0609051603060603090309050f240a02070f051e0a21020405070f0816050415110c01020c13050603032a0d030b01050d0f0b 67
    0x19222500c42c00300c008003100782c288a00c0454500c190208003481c00103000008002070109402c0f038a40964011641504010070085c001512180c1c0446c0d907201034007916100e9030004080c00125140a60024143c5040c4d502403401d05250034402000b00e6400164134043c0c40054400250401490001c1100c900b004410041e00460039180c4802d84c6000c9402810190720f243c0c00c0f140455110690700351b09a40c1b61048a50091111002e40d4045445480c0e0701c040304001000e101007075585070700551205080040c141e61410a502c810421450113118254109415181c034100d241036540026180d41400380c0400c40c049a440f06030326115110700c0403034002d8848040c058000e00784c6281c0c05001541182d0004c46240240e00d1140300f694400514010046c200501b00d05a0f58480c0800f90001d000203808550580410400ca454a000c2820a03a40c0b070300d070343c0b100c040180e0346800700e80342045c41d0480a80101414000006e029031f0340501922802402c8080015451840f0741100d0f004051221101b = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 561771897 1250 561770647 561770669
    0x20609150a051815030103033603060f1104030b04080c03120708092d0f0703030512090f0714040e010c0f0906030b0a09020a0c1703180a0b070315 64
    0x20420a0754442c02421083c8001ca0714118410305001c01c10509240a843c1c40b03103008020700041002c43e1090b045680300e9543d24900d600740d644192260311a18809980052220948030400c0040203028070070950f00d10304001c020000c0040015003200326102d244405800842e650000c00d082c003450008440882c40043c0880f596000111000e40c03801400702ca981e800304400f41c000407006840032070b61202045003c03124210031682c50003010508041804a51321a101d220710022400400300890406036000c1d8032a581c550040e1020094144002400c0d451150000400c1141003040000c5070000c0c0d40c0c01c4901100c3d1400e50350003040052150359080340c0c00398244681c114140f0703040200b04110441c80c0d81c0b81190a600c078001501a1a450f80303096030064804a0104166103041d03000d0309402d4558a00501c489078591903c03c0d0001d00d40a085030420800410301065981d40b40d444a001070004000e440c00381201e4035410402040180704400389910f49100302c0b5401210b150740340180c0310740510 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 561773147 1250 561771897 561771907
    0x16120c03030f021f0b0a050301231e0a0501050f030723042a03050c070b01031103030f27041e1d010c080603161a1c0f0c0e0f010c02060915 61
    0x2c00117001d1a820362402070320112004501800c040c06180c0031302c070040300001480e640d14842c44003107490003007080320403856854004062602c0030310124003a40603128042070a5040500304490452a1308450344030b540700000c200300036102c44d85c40a4551341005012810780c2040c030082006005202e0311074405483c00261400c03801c0c0070082c601c114014596040042d542e0705100008544074961002d084080075500410000c0c1d864102d04080c858080c4c1034130300f0100300070a02081a00003562a010740c502c83c81d00d03c0ca0303180d0100140e100c08201150103114400704041040210a607800010b4281a111921309200e800207101980044034088020044400e4408009004603019943c081c03080c001c054090301c00340841d040c4281951241c1050320301140072082100511b900c62080310402460240607911040c1092042d00d041e500f00800200f012400c4140051510040441503441081c2008180402d80d902046551030300394180d50751642c4401c1741000800003d00c00c0344114511400080f = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 561774397 1250 561773147 561773203
    0x18020a0605070605012c130f0f0b0a140105061b06240f0a15111b03160f1707030605010306060509010b0406120b010c05070816120c03030f02 62
    0xb03115080c00b5510420290741c960644002e21194500d5581d0442e0b41464244c6080c1c4840740c03402d0700301c070000d010030480c2c8445540301d8010740e2003104255000005810f91606000e4140106c90f40b028100c2e4080205c01c001c00d04088200f0f6040c001e50740200004900000b0120007000300707440c01034014003250303c689080d9030351030b104581101000c0b04940c500c110849107400d1185083d031014600500940e170075421302c2201d00c0e20610140195080000e0300c3c0c209001c2841c103010b030044201d12158555010642032040c1803030044010440410000c03d840308002a51008800405031169416800842542d02d101103203002c1e220740001d4000c600e818000001c00c50f1992140045810944030815035a03600c21b61246280220320a000c042803090100e851301b00a190b020000804c01414060540001074a039140380c40d40036004144594003110145d45030b00c0c4d070903010b50010b02042100803200341003544d94841102c01440020240a42c01140680c1d060007402528044141101c0d85404511403403 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 561775647 1250 561774397 561774407
    0x13050f010807091406010305061903050304050913050c090a02040308041e0501080403090519030503070b0601030f0908040312090b0f09090a05010b07020d020604080307030305040501060b031918020a06 88
    0x312510700380b0b01caa00702c0041d6403d00e5015848039800004021075055903041c00540103080000d00300c6500c52401c1035000c111003860030020029601400c0155100c074244024000058030150014010044212140700018000581400313964015140600f081e00d84080c0500a40100d420080c00d01801240200b81c4c0e030340038008861000400c1c0b58000c006c80d030315801511884002e0300d01a00041d8100030503c0a81054000b05003100300c00d00c081c1030526640c0d01c03441c0c2142c010384000c5401c003d01c2000e100c110345c4e144c090707040200c42c0084104800b0b4000d948406003442248002800c1c164150300b040d003902c1c010301100c0b00a140c80390b11507568048808115809a1040403140d2040080102240c04045188600b42c1030310a80b03101d403840c00c15990208460316140c5202240c0c000000c03c004145454240080d00c1e105100381c40100b00c500340341c501542580c0854004254100003031041040c1e080311200c100d1a0507141a0340020900c5210701c00784c14aa28005001c3d4010020b03810000d2015880 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 561776897 1250 561775647 561775649
    0x9030e12060412080702030a0c1104021603030e0319120e010e030c06010b13140d0618020301050603010c14180607030804120903150c18030b010314060c1813050f01 72
    0x50000480b403c0c8a00106807004982510100c005030b105025608405004101410049004040c0304883c6109480010140da10400200c150141c2c5100400105034042c09804a1402c2030780141d81407840741c0c0d0340003c8100c10105c5620410000d190406400321032640000c608491820090100c980903042503039490340000d1002d40c00744261400004c44110040c146c583c0ea148103c840c8005a00e40580c0c0c070400c0c600e407407505501c03a90720788501d00010b0722032089400e411011580003003c00038500405084820003002140a6410304800f0001d05501548603188420840d80303207521003c8801e243d0000c0b1550100c0703613400c1880015800249600045118800c92103558030352188070030081708407101e802328400182440f05401e00054000781c6500121704103001031a1004420008501c0614100c0e4260310076a0b034203502000610a0000f030051400348072800100174081401d00c111248224800c0b03c0654103003646901103a5003a94502c1020000d15026400c24000750500002200c4103240c2 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 561778147 1250 561776897 561776903
    0xc050615011808060f07110d0206090d0203031308030910021204020a0815010b1e03010b0415020d05090405190516030c090f0905090c030a0f0b180a0609030e120604 72
    0x4194804402e801d02d40d0180401c0d5450100544819250b65400000d0345001422403414422001c0803544c90307840810501c0c400c04410760003400103017484460030707042141401030001150401c0040040100c40e460084081725480311001390380780d8400c04020700b0500c10401c944449800000c0c007031060320804010601503402118100d02050f0b13500c80303103a918060b8488585c40b241d00c501c01003010032020000740916031960705010724011a2000e511105600981021015a401160911005407020020590710401c0d00082603481d074503032405040d500401c50458402c03a29540098100b03c00c000620009880700348081c085424401302400d40c17255001d01c5280064039001803040c04904c60001307001140c140c0490660400e0404141c04c0103072600814064052181d1040c8000da078604210500d0558010782801e01d04075118908014a140083d00c0c0c0c00500140020821110402141c580d652503401350002078204d40300d18043e1024804100c2c460b5100c0381c0340c002220400008034215102c3e501c = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 561779397 1250 561778147 561778157
    0x30402040f02090d060f150602031b03131721180a06050d020306150a08011404200a09180b01020609030c0a0321060306020d0c030605030316030c05061501 68
    0x316808400d0100d01811075000c0d0b10081c09140f90010900750340c03100911119017100810400910f0743c2d5440e000d0810388c40700d4016400007903601d9035030070002240c884a07071415010314076010243c2c6a030351340041d681c00b03404c1a117043c1c501408480380d0200002c600e50078404004500300c0980d06900b9006401642da40b00384103020540411680c034084103500f050340c03c42e0300e415080c071610b44082c1009420003081c0e50f40054020294028944502015210100305070f5101007596040101c500790b8500d034040300307174002d038100b503902050b886079407100c0004070301c0c034269091310341d1400c400403900c00104d82c1c480160320245025442c0a03518682081740d04840031303002c03548280c440e02c00032070350b911904218819941082e544c41c00085d00c036003d030119002c043c1d20643e503c0d41d00890000c04813030060b030044a8059000641c20f1380d103000790107200e214107260305041080e0f510742004292284a203420301548040d80026580802d40120b0008070303c590454103d03050f40c5000d52401048000c4101c1c80c6011034 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 561780647 1250 561779397 561779411
    0x122b060302010201140c0301170a02031009140a020303040605222301050412080c0304080105130b090f07060e1201060b04080c1c0f0213181e030905060306061201080303040204 77
    0x5c0400c08541d0140043c07a103c1d0385160b1800208080b0b02a954a1b01c402c039018088a0502580c0e040101035440366041d50009000607442c41d003da00d944404c0204581901300c1601d80d0701503500030003543c0480301d407810020b649600c041c01c0c0100c03940e00516100004e900c2c503080410b0340d2800c02500c4a40d140319054040401c50f4400041d41c05d4046c030300c00c014400301c07024a800000b030050000340c8141c0710104200d80c10180c5a41e400c0d825600104c890752214230b0241004000e00c0291030341c554000300c00f00b014240c0e8041200d0b080b078a40b0b149010b1041440f44400340110b9035290082090074000c800c40080100544641003e031725a03111340f08250710b6100c1c00c002240c0134a0242140324040303005d051528040449651f80030000b5614a4080ea401402034240940500c06400389420305401c58410030b99400141c5890040c91202c2c00301c03004281e0141c4101c600080d000140700c0240d41e8103d40980c0c881d90740400199040c41401c000d403e0030008000000380b200300c000099070140e4400c403030070300c411 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 561781897 1250 561780647 561780671
    0xf0702060108070f140103021201030f050c040b0907081b04080304031112031b100e030901090614091e1908010f1506030b12031305030c090405122b060302010201 71
    0xd924140510a201c1500c000f0030460940080e0507400b17121818100982032807070305200e81d00600b10990050f00c901100d081100c0c100b000902c650f01c081401181c0800c15800e0000205d850000010903a205010700040801c0044400c0c076403004c0304484d04407607195110784403900a83c41c2d40144c44100c484112417a04010140751500070b80300260a101c1c002c44c1441c00c0740030810600d2049032003019880c002c0214640d0010007501911a400c105540210307598841000014400100d5502403c104a158080b40c40c044607500100c41074131a04a900f002c0b00a06121100711110003d0300d0594860b0a80740f12400700a10600140120742501008005143c14a144c1c20161081804104428641700c001805483c2c0281e0100b0407044e006801d01c015a103080c10ba1511f190b01c441d801d600d44844004d010021442d0801030301e0788510080e80d82c050b80e404d066841e29074610384400106a030240216820000103180e80a003400104450050f0001518841d2048010301144c04140d0055003014129144 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 561783147 1250 561781897 561781903
    0x50a090f1212090e0a0605090708010e0c1e07030306030c12030906110f07031b061706010f1101022b0903080c0901020a0602030415051803032d0f0702060108 69
    0x4032000c0c0c44500304840350aa8840318007440d0040b1040601903500004980d100340da03540944244051940014040d060a0400c001d407a80180301504000100c401032150004a00c109a04900300c000c2d11902c401a1305d4900d43e40411841c1d600401c207070041100e005041e41a00b0500807a4003507105c43c1490341d1104c8845003c0201144043c0110b001d80c0c1082010301d10810000146032002820b403003000e04035442d07003800c00d030042d44165140602191004580f00607012030100030080e50030648920701483e504140031103001442c650500032040b41c82488540160b102503042010b000c0215501e080350800c10301110184040045c25895008448030404464400c2611198140c0c1740d0f181c440d0794090190015510103600b0764118010807071440002182030001d18029441001d1400d04d4090315000070302101d900502c4081019022090000421000301c101ea40102d020300f58803964a0340104841d00f01c1060881682e88014200204500e0101b0f41a000d4000e210f66400e44660383d0b032707424000c0c3c0d0f = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 561784397 1250 561783147 561783149
    0x50a08030c0c1c080d1406040c091a070218010f061403280c030203090d0302160807060615030b030c0f011713051507020c060f040302130912050a090f 66
    0x1a8000072819181d45000fa55503082c048400c1100d0440c00d0301a50b480340b964001092049015482e04030401017060040d6009031b0201054808028a1001c1c0c20014804a080c0c401c0b401e0500d81704221041d10200042160350780d0b41c000c2e006815050441170349034040d070002d206003120b1b0b08040c2c1c000300e4158840c5541c1d164030100151901d0035519000750500c6481d0364107003402c01038a0007824000c0f100c14540182151400030f80c40050322490400d140505040a02c9100c81c00c143c03040020b110322420a03c5102400707a00b001007135480f4003081ca0140018012600500174164003010b00c800e400d0340c50741181800f00c00643c1540d480545a1081c010680139110120380861320454040520f40954109158402c031001409020328400d80c44090508502c0546040107000440c10009242d030104203030001e910090356898074000b00c954020300396008a010003403050203200060b4504000707541243c41c3d8240c112070003c1e40750419400203807065200d040f01501240400f140054100c0445903000 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 561785647 1250 561784397 561784417
    0x1050606091c120521040209010e07180f090b18070309080f0a0e1005070b0a020c0a050f0106090f09021513030c08030d05181e0f0313050a0803 63
    0x900380150300081120006031040c09442d104080421038000c182410f0f0a9030640d1090b80b6040d43e01c910800071500c3c5040d00c004008010382064003800016220034003c0ea046801c0742812003010744a4a5003143e001b03000079180c040a0f100000041031092806580304201d4403024410400c07a000002400b4071100f400c0040b0311001080800540c1c4c1f24040d40190043c2823041409514041d10607600345140d41043c1c1d01d180020365143c00c04070b81802c0c19650031a4046140c01e02038240f206d503a88800c40c0300c8004200e400035a80204440003080020807401c01440da00c034042e00c018034240003080f0b00a00c082e1080d01255402d00d800400a000c0b144601d80c12980c001d081d8828002c524802c42d2116842400a042d00f220003034030000208150418460141098801031540c80450b44001070a0b07a20103022000b030b15240749203030a001040000c804121440c0c8110341260507202c00070f0241404041c4181e400035000006800c82115010031a00d0156101103c1c00108562100c1d401c0342d60b405000152 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 561786897 1250 561785647 561785659
    0xb0d0201090b030702030403060609050703060b07050a0210200c0907050903060c0f1b03040806071e0f0302040f091506020a120302030a02070f05030c0127021207050d080a0908010506 80
    0x140b015080c498011a80201d00d030048918003a9a80c3d0740740101c542c56440369030311698030300034003c00603410f000342c600520711109000c0c184082511202d0b242c0c2c41d1420001d105004081158070440d020f0040c070040042000b20f0100b010b800010380300c1d01c80d48941700076071140c40c4d2100010601400f441c00e4480a103009001030900756901030f000407403640030072105012124203100c405494844e1301c4401c41007070722801c041c40d26a441c1c01045494140041d01410501040c0380c43c4400c506c9110080a0024241f8506514100d0b010720701a4020f2081d604110070003501c0039000304070701801e40c0041403079002d000860b50300540e581d401203842e02c1e405200108540c500c2124801140d01c00c0d000f85411824025006190808030b84d0796814101c40c44100302c070240c0010804500902d001e109040002d90074071807608040c5002d0720024154048103c00a10802903d503559002c00c4041002101404024210065801c50342c1440c004035001003140b000000c2e10718101141d4501c06002d0356001f901d0141003 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 561788147 1250 561786897 561786899
    0xb09010c02040c1d0a06021b0d050109050307060522031d040e01091b0b1b01061206330611010204150804020a090b010509131509050a140103050a030507050f070b04090b0d020109 78
    0x2303e44000c0b0305145090340d10001004540001c5802882100c0c0070034458801141e645005141501c15280c00134203d105c00079001d81d07505140a03102c0a8588201e91610b001c40c02040110108100c2990200c021a0010319110050411034015408056070f00d0160080501e16481111114045d036140c0c020514201300a0000043e03105c50301403850b0307031841c0020000c070742070f41c40b5180d900601c2142201070fa045038842611803000c0c1081800b95182e075036402d0a0040c031401942e88032040310314074030a90042007040c01404894403001e606407805081d004801d07900e4021426401499000c09035400c0e84a201114800141e0240340c0c42030028800741030316118105118001009206090204107201203502c61001c544100600e01d840d04c081c0c40b9903c400107081c200f03030307480310119040711070b141c0c550028050050000c19030000306110041e900d0b1816039035691042c41c007103082c8020130801110320310480308040b46842080340607109503404e03480204a68400d5504220000e1880040a1b010440c2d0700c138 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 561789397 1250 561788147 561788173
    0x9030114100920071e0f05010b120c0d0308100b040308072306041b0b030708161d0622120204200304030f021207050705090105040c090b09010c02040c1d0a0602 70
    0x30443c0840c540b6203d40105004141c41d00202c0c060302d094129031a942d03a2010009e142381588141000303001520050404074200000308034001c0d001c41018081c401c913039000440300700594900748007808010a403d91510ba071380c60004210f4001c00005c40e41503803410940306205541d030f2018020003110300d00030041c588540d21602c3c05d4504407220b001d07a07003640c0200495034210400055000301a5a9a01040e42c1740481031013480840000c6c06004201680d40c3d00d9400c00040301400300308400450b80c81e60355500b401140c40c4a010605081c03024413804400000340c140300183c0303001003203000b900d041c41811007101c40000c1c1811800030f03039544000c042c00403c1c0400d01c03a140d03005499206004440840f070400300d0201581e00110402c80b440e40c80040c003030140d400d0900c5d00710300402043ea424040c100c0d801744060f01d101142c1c0190500580045144c00b25a8811611000304e0340d0060020044e00307618143c02003800031821403c44021509a2009040f0700b8105400d2049810643c080c0c184038040c42 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 561790647 1250 561789397 561789413
    0x70c090c0212180102071a0a0503060d05070303020a06050108210a02070302041d160503030a2d0302070b130320070806070c0b090712080903011410092007 68
    0x65048011032040d20400002e9082500040001d81e07103100b41c0180c3d481207078000914002580c3c000d05440105000c064098007180025141e1403d92820055120303034070701d03003c940c0391411140007900710301c90720600000340740d008074110701058082c42c0c3c240030903a20760080d5540c0d61100c0308080b00c000310109400c000101c80001a2540b0003c600c1603620066503500014140e0340c0d03411003080001c03007080b10550308100820901c08810380305614507984901c1c00c07000035103e0081c0140e1205100d0b80940f03000c011400c0c880245d030921000001c920310b83d608003400500a401010040300c4c11590742c000300f42d030791491880b42c0c541c041d0301d07030b5a401c11204158142c400104241d9070302d04c242e108800d80820500018050588540c52070f039201000d400403410010111503000e44a118550024071050103021070b1000750b085c60542001040d40e44a0a41000c40c5c01009025103100d05603003100c3c1070103003e9482c509141c0840301e400000740080600c030500038950184501045071102400c01803c4000303030640c = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 561791897 1250 561790647 561790661
    0x50904090246061d0f03070e070201150503070e13080a030c1403060a03140703060e15061203040308030c16061b0e09010302100c050d0f080f061e13090303020c06010b070c09 76
    0x181c01705026651080102e03240098139003000540461503010418156424171a070803a80c05001200b2403150724190100b030b15298a13002d01441c00c4a56800506860501d0f040d03103120540c441d800603510024800c00800503e5000040c0001604a070440c9000d2001c1901760307802203500900f40c0304206e14540e01e080142100d1500b00b0b00e03a008216000000c107078648034810f45000854060701004103007504082c05980010a2248a840109101401c80200100b0303039003603c3d4484003c83e583e854400c0b8201e8a4003440d840845402e01d942e00350002c1180b00d8000d1100c0c1c1070031030312424180b4001030f41614007210408266800c07881e4140104003518251a5401c0c2240d01c500744041c041c40d0903180c940c00e0070088042c410118043c01e1401c482e0b2540714064580c85912520030070720500b00740001034161010300302c64922030030f03070450400b5484d902c0c54004100340255140c01c10104406142c00b40c065080600c0007686401000700020b16510118102d50905600040c10400c07141080140402000c032 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 561793147 1250 561791897 561791899
    0x30203090909120c0303040b0a14040b060f040608030c070602010605060a120902060406110d02030301060e0d020f06031807080604080a05030c0403021806040507030b01050904090246061d 82
    0x43c0e160760ba01252000002000b201044801a5a0b03034540b1b405c0c110414000a044650803514107641c5410078924003121682259028080e81425214035000880d005c4103c40226800303813400c80000360000d00000200785042a04080e42c1400c3e545500982c200d034046c0c03250701e400ca2400c002e4505002d2007040f101c03403004005a000181d5400703d8003c20f1113500550003110202e14035100c25130040d035041001d0720320340c1040c1c40114510f6040c0340005240b01d4406040070301500040a0390811035603030305485000100080c240540300e2801ca10701d08055004480780340c0450203203a00c0070500350b03000700d1001d128642107001103103400081c1c0b4003203450398001090205074480c00d000200060303480c10b40351000c1051402241045041800030001100c03806032074030003031614004c00b02141d83d030010160b500c10700b0304030b8001860310100c1c001305e10048584119400c07144140c401100900d00c0c1180c00403140245180070b0310b18035980407040e440603a954007402f00400c81c102c8101d91400425100b05802800c = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 561794397 1250 561793147 561793153
    0x705010e0402042d2909060c01141504151a04080f0a02090a0c08040b060303090409050604030e06030106051e0d0e0c03101119020a0f060603020108010e04030203090909 74
    0x41e640c0e9003050145a41c0f101d0149020440c2491003100300c04089000180c01c01d12001c20b080030804100314001640d0102c005c0610502091414039a03850b8030540d1546a28200284000790a40c80c1d0b140003404200c50000c45c003415111548401d040074443d0000c403486415542c82140d041c15046038804d0f5200e0801e80b034500c02040081044501448884401c00c1c07030a0090071171509a104000d2840c00007070085142d680303811550400203a11020158000390000c0b10410152215008030307095101e81a405904541000414420424001181e074130490290b51b40c106410030300c90030000180b200303100b041d00040c01800401d08c40e454407001201082c149026080c50041211794650a5981c01480c001454101146072001c5040600c90030b804580c6d9400c0802c003100911300b100c02a030080c9003400d010310b807402e0503039010507000300648152300350000301d22120002d0601e0804080c001601003240064000b84c000102d404000901902850707154014605200c9440244040200000c01c0d52280e84 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 561795647 1250 561794397 561794399
    0x120209090c1b0f070302180721151e0602060105011205091c021e010501080a030c08070b100305010e0309090703090c0b1305090c07080712030b03010510050108070309050705010e040204 81
    0x7a90030048943c04502d803101900040b413560041002d8140421600c0c4502d4034003e0810132041e0340160318440501c40c00d0070101d25001c4003441100100384603a020f5069410001c0041105401c4480c00c04038640c880300c41c903070710549407402261030f010300384102c41c0842c90003803100c90000441d07080039074408080c40c00c44400000b074403503001103200c0303030300c1c0074401368101900c0c0e1031f0048984480344919442180090201e545060314071507403101c1c982d40280801810102c94000c00c06860100d510043d0440c0078036110f4145213200003010109448100c075150f191020300802c844001c81901c000001c0285071031450394440300d040e400b801407090100c0b031a0120500c04901d2070344001c084c2c040100c40c015154001400c00091000ca05000b030402d842d182e00c14007e00300001c070020b0880304041d0b80700c91402101d502904050b8003400d1030f1080c42c1d9065081c1820881c41c14141d00384141126000d90f40c001054031550f03000e030115400021701821741c1d0402c002c140887d5000b01400c1861490182005140c1 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 561796897 1250 561795647 561795697
    0x1a0709051c0203060739051e060a0903030b09010b04050901120314030a0b15090a0b04080334061a0d020d1707021903050c01020607080a0f020d140601120209090c 71
    0x1c2000721b00441400100d2080181c1801000c00c0303401010200e01445001420087c1034103503403004024104401141c07a40146000c0611030b8010400004d80646004c089503110101d01d9041d41003401040c0c041c40b0000000118a4100c0450744242900f503104d40d805550030784042c0041d64002071140b103c2079141e0f00d141c0582e4581c1d1043d91001d46080b01401e0f161400c140410140c0400d591203a905150180402d000541001c0215100d00d07045200c102d001c80404180c040e0808048058800440107400034036041c803480d50480660442e50554a0111589035000c124400d0740351013010307400c101d803203040c1c400080d42e111004400d030300c83c0d000c0c00d41000800d0307000030f11a5803000346155864984801c04c00401c5000c04c070001f481c60003400508418609a0b01c0102880c03001080002c1094030380d5160302921103180e0498044503080d40d4203011002c6a45149046070b0350a44800c3e0001d541c40100c003035071400c94425140e251b50020841c403155100c501c40b0142031740120481e0000d14599110017100 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 561798147 1250 561796897 561796967
    0xf04052103010b1602130b130b0f04021315020102030901140112060504060209060403060b0306010e0f130807120201140705190e120a150c03060302010f0c1a0709051c02030607 77
    0x103940c880000440c003005010103012400e0344002030352380c803107051804605036655901c1030000c01e11000c0c1d40c010b0310f80e248079100f050b0213005a40490202c8183e284c040c5002ea6040d0000e62180d11001c2c028450540310500200318500b00340300d91420801c20b5807001c00080e50940186030032074042e960150501e841400001c0140d40302c2d500407225a80d84050060542c1024070500d401444454030182551910416291840200400811285603015041410020b140d42030b501d44503081481030300d40c2d04000b41c019000704420701c1460551013000317000640c203900c0760382150359813400c101400600c1304a40d60244c42250080310102da100359041c01e64400c40700d0401600c410103014100c50415030940240340d42c00c0361814030800c4201400c2c183e003800982d03000710742617072104071078600355225140d5810003c014810000002003820030803401d00990701e902c80030100903180205d40c1e105070300d1540c150500e441c1c030030110025007603042540002c001d00d010707240803640c01a8030a10030030300280b0a200801 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 561799397 1250 561798147 561798169
    0x3030f050903070201080f060108040f03020709090c050405090601081b0d06110307090605133006050105030f0f1902030709020705031806120406020307030608060f04052103010b1602 80
    0x1d168800708941c8190360307000c500c06404c86a215030030303689800c01d400002d0040e075000300040c1c1900000303203852003054400c001c010700403e100d6400300010301042c0740080c0c86010074486c042c0308600f0000800d85190000c11000d041b213000400a24510021440c1c0c59600e1907074104855026404806030000309006008602c4000c403203040a41d03883c41c040c2c8010300021181d8110b1001c104061140c0c0b1803c1588070185000e9a0f000d0205000104466803008a082d0002c002c0c4045038841500103001c0040d190000350503100120282c0f49114500030050f07030780d10200203004c000d03075101a503480f80c410b110344144000140003070207841d0f0b403e4841121000741d0b400080f0484e0740d03601c00102d480003550012000d09011500710f03030603803822403001c2c1c20024080025101400c100ea0010110b0780f482d0281d403107000244042c0c0141c1d40c8500e4541d49a021402044400b51154010300f0024980c1601002c40101060403d0404600310703400c0c0442c11041d07800468000441c0000b40300003a01503521a03015407 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 561800647 1250 561799397 561799411
    0xb0f041517100e07060903020f043305040b0604140f0a0305062a0d1e060803040801050c090102062d0c0d060509090703021c0b07020322180903030f05 66
    0x440c80548200c42c940031507080c20038420940d00012401d115566028040c50100ca07011503180302400c08840028000748143c0b10720241aa1040b4241018102d00184020900740c00b201240541c5998000f4403040c2c1d440c018070540c0c004400c101c24403890034801d60032800c280000e0403030400418154082022107a01d0f8200391141c3d4000b41c1040420580c4040c030041c44400c0c5084650b414030000c0d00b20003140100f441d0f5499654907080150b5894060303080159084004075801d00010369145203060301e0740d01902a0800550074600001c00d0580daa208a60f8070242c180c4c000d01e02aa61060301c1084048603502d51010102040c0e045031007130640030b04140c054004031454641c3d030310f155000201124010f9120034002d020b4003040100120f0042101001c0720b4040c0c1c3c03003c1c0c071100040101202c0115401c0020402010304083c07041c840c0d8004080c0c841c68012040c8052010110140c1491a034403510031b03180c0341081c072050210303034843c1038101140c000c0c464103000c0b820b55440c170051003c2d1034040b03880c1 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 561801897 1250 561800647 561800653
    0x50d150e1f05030c010503070e19060302040302090a05150d060209300f1f110301080105040308090304150309061b0509010224070302090111060a060302130b0f041517 73
    0x7000e00780e010099110300a10089000b05204607198001911a00005100a00340000d62032180c68545610841400d05121041d40da402592a40000780094103d40000c0e0300500d100340019450300c41c070744980d600918068510000c2e0b600c08808010401d42c0f100421500d0a4007848010110340711309440740c2d0104e10000000c0042c50b2005c400041c020b0034503070b200c9441d07885040150f0605101045c4038802000c903040c81d01c450400d00f859000540b00d90b21092030300060000000030002019032200e802644656100002c1e500d4900700d02d03990340242c1c01001003a82110f07401c919142c0c0654000c1c1c031294481e04c404103440300071081c0051810701c120044004202c0c0054074640c2d540c3e041c00042400024880c4190b03880d866016000b21901000303041406042e800140d551035a0301403c00225a17003c1d03079084594504d001a00c00000d85000e2000300d01503070000018240011030341c02801e80c85200a080140b0707082540b001c0002a0409401d11528110703007441c0400c1584c20b151001d615410b02d8401 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 561803147 1250 561801897 561801931
    0x70204020901180312170f06010f020309150a08010f03080d0203130609050c01110706020616090f060f020c060f0313020418030e0901140603040b1506030a0e060610050d150e 76
    0x101a1040b921104e0308a0890400030400607d02e565805507504200c0030310b880c20001e0120141649035100344181c855008036011258521506208000c081c0f40c2590f0303441a256986c1d510417042d10004070b0200600e00e90041c000c01402e04099800707580d00c05c0f8002d003d01c41201003500d640c000c640c2d41d00d509552070742045e01e803000f080d60030010005803144010002c0c102d491805200948825019090840c0e64078921040c0c0c1d07080740f1424624020b8045080401c1c460b40d610700014010f1020801194054040d01c11000340ea803400400380ca07a605a0702035502c0c41e40c0d0316202c0c4688005d01c3c42d801281d0060349c5d940522841609180e004941d240700e91141d1400d004410304204141c00e0591022100100d514106c04042d100c1e1401e881e081980040d01001a031103518115102d5110f140c0c4807a0004404000c001030b000403904907600303883d589801e40d4020b840c1d00091103041c80e010400e10021400c108011040100e05611000c841341c4009200d200194035011501810003003500c50058001051070 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 561804397 1250 561803147 561803183
    0x708070203040929010503010f03031d0a151103040e010513060f090212010e060102120d180b0103150b0915030a06050a060812040311010c03230a1103030c0702040209011803 76
    0xb08010b61380509007442401e562400950300401c4896000c0281000ba890000542c0e40b0303e4035a5108100500518100145440e0303a180848294504d000f40c00046000c0c00c4207581c0000030084509032003d00503004600d80c02c2c40c0512004080c0506251400c0e03640d0303500003580301c0a04140e10041d20b00c000002d039135030140700b544003031015042c0c100d000d005030040240203141e07030005105a0300180c00104181c80d01c400310500b500412251600391075a1401b5072100041050100d2501c1c1078900c6515400c0440e12480c5c08101296a46000380d904a860480400c2500350207801603500c52100500b1201c03410300965a84013561000d17900000c4240e1505014412a10180a000c8100c10030a07a01410503146440711403040000b14503441c180035403010010281842050221100362041810441182216182580c01d6000c140014001480c1055240201d4008070480303000c1c0803090f4a2034101032154003004000d5002101d054140440e580d0302d81c0c414103403001038a0045025100400a04500e14 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 561805647 1250 561804397 561804461
    0x1050f1309080418110d050402060f040914090a03090608060415120c08030c0304120c081b2b060509010b0a08010f0501050d0f06051005120102030402031207080307080702030409 78
    0x144c034102045090007255249400300c0c106881c0040b039078a001041d80c0c3c50780c5c0042100c910416606111031000028049650b00042d0864034144410742d0303120308254bc0d290030303154403482d0081c0014001405140100b005502c01c64449030098002040081c50001d1106950912003241d44100480c1105001079000c1c030404038402001080080b01071894801a0101503403240708600899440b002c05030f0211060100f01c85040c1e010702004000c4800030020001c0318280d00050340005803040c01d850030002c640c40b840900c140c604c4c0d00c2c40341481e00b202c0003958905010381001090140707199030700e04484e40c6569550f0f0305140140300400c000140d1950403122401910b00c143c2046005505406100b0006035840340402c1031079802c00340008580c0c80304030342019440c210380c0c84551310942414000c1c0740c0d148198011070055108034101c80c4030290b40d4144180f5405281c001500c242c2c030901c0001d03085030250188039400481c6105491420340c842540e041141d000e11a22050340c1021003107501d4010181d = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 561806897 1250 561805647 561805679
    0x3030b0319050601150516150b060a230903011d0105220312090b0c0d0e060403140a0c05070b0415020a260403061d1b060301050f13090804 61
    0x102405040d281c680c0c0c03145951202c040c030420320050369458400545500c5402941e65002c9964500c900401241c00d02002d40545040c0009445240959080c1c01d46068011214002469122410b002c0f505c002c003001c80c1150400c280c8103200c420090301c56590b4080c40303032110100100318100802c55540c00c84a00f115801441c1c20817840d0b650340303000790410020203800e0140e5030600e05110700b0003a80132124060485d515000f001c6040c2e41040c40913526229029041c8045080c40800c400944454007d598880c10b60b40900401c1c07400da40b1080b48103811008081c0c50071281018107402c0b166a5400d483c02880e5400818030500c0400e041c02104805c90202544213840e200500c40080581c94101c4049400c119039100c91810401710905042c040040e10025034009500b005454501030f086c84200d201d81d00007240c02d0044040c903880565000003002c3c40060040c0645003903a08101c01c0c4582c00b400ca003105030340200e103e54007002c5220306008030161f240c4079110460300c452610314080c40fa5401 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 561808147 1250 561806897 561806923
    0x90c020f0105090a080a0203070b0a05011e0b030103060b0a030b0103120e01020f0706390515010f05191e03110f060d24140112050123150703030b03 65
    0x105400d02100f40000520001826000443e080c1e40d41281c0b50240d00e148103181c00180a0300703070351080154800395507010314104d03490340030039030b0395800150300202c800704183c0104190100240300503c04901c05030300142d8031000203010144607548a0f2204032000000743d1040f140c0024070340604441d036500c411009c011300000c3c0020a501d180c0c1460603503c801c9580101c1040100c80b0b20300402d0700c0c12030f25424060b10301001d841c00f800c400911071404c030396080030801d071458410040d203480c0d0b40c42c0440049048800711040d5064541c18841000341c038645801c6d011112940070714000c02c0f2400400d8010951407090156101294a90f01c0c10960000c0d078001030511401e2010680b180f19220003044850200a4400c00107000c0a10800c914003418003102d220b048402e03034000882c941d00760050402c0600c01c241c07541d40291680000c2203050382d000340207003c1009a642100c4a840040c00050101c6d50b500030320f00c880c132004051150b20310b0741080380b082d00000d455280282450900744042002518 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 561809397 1250 561808147 561808151
    0x151522080a0308040302030910020c15090d0f0302010207080a1e0302031b0c0f03031f05030c060a0e030c04050915090d0f080c0706020304110f040b0f040b0613090c020f01 75
    0x119050000751a03012519002e010702032032034001020140b0a00840c3d800f050024803696400c0340505000b036460b03503000a018041d0030004c1c030220b030020441c010b0703889580e030007000aa542811660343d1142d005010b403046081d0740d001e01c42c039000126074101400ba01c108641d2510304107000c0c00d800e4079007080222611001d0510420a0004074440d0242c80b1000e542400c071129560030313054480910b04801d03420541002c3c0008414849020800c001015001421220030802c079600c0b4400c050300c8665100209034410000c20603200c1c001d00442031903007041d00c001c050b52001409003010a007540c200700c5266815800401540032105041c680f140d40108440c0001d14802d6a0300f8030207080580903204050a100c600400202c01d6007070712086417822540000c0542d1a41880e15111020482d550001849000300c0900c0c07180304d0401d8440c401041200411090300244a0424880208401032100790010402c1010fa41040e1341d41103070b400185011301000078942c0d08134200070300b850500004236026134 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 561810647 1250 561809397 561809399
    0x204090231050f031f0504050d02010b0a090504031815090b040b0f07050a050a0506040606081c0f03020705070810241521060f0b0703050d05151522 65
    0x401c0501d16a056450582d40111101c001a001900d4104520024111215810701d0000c4422041c0c0209000790f1042e01140c0704500c0c07402d000c0c3d00b030b21030002c43d45411049525081144091b80c2d04015080780c040c0c185070591110084800401c0c2c2170640205224094801c510f0040c00c0c1e100301b50348004d00781c4180c00e9081a06100c400351080c4a5504000c1203500040342040030311601748180c400d450743c40300031110504985e18000d62664422181968030514100d0009108000402c081c1032100b03a08888810080e0450003d41d078405024203011308040d401d004540010740c0400040c0e0146c24500300400031001060030210a60358203c01460756035544006128086001220240a40340c108004500b400c2d01100202e175404010083c102e0405c0d0a2090f942c03406031264001410380d50740c601c0c080149500c5942600c414030605000500080d01007048091001c02544841c0d003008a600f90981f085102c00001280c0d80038244c940c29255400040c440d1112802003030749040f160040340d00b00711003 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 561811897 1250 561810647 561810727
    0x120a03021605010e0f0102071809021302180415081006031b0b071119031a010503010b060904150308040e0711010606120506010c02130209090c03040507260102040902 73
    0xc6810311301042c000c210324808010107a0081c0072041c050202d241050340d40d1115200820301505030741c80141d0142c550740e1400040e000041c0222810784960089020705a07180f20144001800448498401113420709030100310807106001803030746004400008100d05045081010900019003454201415003090030072150101005503805550400b1045080400e5240403c1c4105461054112003801e8040c0102c1007021540ca041d2800480000d5110142e80b41c40a040c03c880ca01c0400701e912441c00c1c02402818601900000c050144180402600580c0c1e580c60a6098100d03801954441c2c042e101000403050b800142e080d0007040300002401003d2600c135000d012007070040f52444407143c44500040b003a902842458000c541d002c0d0080682500b40d00741d11f0001d402064030244240040004140010f1000e0241d074017482e00702015001030307407904000f00402c07a44014518a14a12403141002441007072001c0d2009010b0b2070009641e80744100c0e18400f1135544515004501410540d0180107 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 561813147 1250 561811897 561811907
    0x80a020901120305041503060801050702060408090d0201050910020102072108040305030901092406050d0503040b1c0203040b040c060f0f0f0905090a060303031803020c0103020a0e120a0302160501 86
    0x450b003000360781c1d400c085194101103a0342d100c3c5030450b83c000e00c290000040c4080c4c0c5540a041261000002000942c40d5058100c2c2c4980c41510007a002c00300c240324105151400c0c042d0f0042c8140b05062440c40c2481050208500c04249902c0780301507540404e5030303402e100032040341000f20804070000c00000c000d40c1d080a045039030058006010840e02000251001300c0951050001d0f9405c2410106482d6410780316803045a072041e1007440c500d061003400545400c014103d007440320b42c402c000d503003098244503242c082500900035412800040c081d4910602c2c0a910003140200e003e100fa11044d49400e051040010802d0342c0321004001d00d00c0c009550380c0d5803003441c0740000c40340791034013041620706d0303240c100c800005e41e403c4250300c0100d020912442c054a544440b048074800c0d2000e02c00038280b14569030a16002cac6002502681140c51800001e40c1303e58000c02100700641170294000500b480421b101070401040281142d2004a0010034142c04001c010119034000d83c10720036450030000000c0ca = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 561814397 1250 561813147 561813149
    0xa051305060a0207030e18090d03020f090d02010c08031509182a130f0b0402090105040b07061401060c0201020f061308161b061205041112010b060408030d0501080a020901 75
    0x440ba58049103601c1050720030742d500b10381040010407000c0b0b00d0410144c0311100c0300d800d0b03d8000141c890a154240124001e00950b1000c2a031001c03c1400e10790104188040c2e40031104040341004103c0d822000050b844001560041c01e02c00d150b5654510342206200004002a040075050081441d1040003074900040d030006049400c25810741c0401c100b00b04d411091207911410340d0045940c0359a441440c000c1c2d0060340b07400183d00052001c840c400c6c003404100c1c450b020a00313001400c1000280200040c060082c00424402c1c90000f900b102c01d82c6401301506400c0c0c00c1500040e038421800015903034100025071200c4004030150490b42409145105d01c025040401400b10f0408114490342c40c0310400c919859540021078484200721160612090003e02d00800000c2142c00580740c078460110b10840d481994030440f0115031503140820018a40f012003054500c543d00c0f14009045c54503150090002090700030010f50700c41c241d4014000a862050f0807900c0b080d482a81e40300003581e10048424 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 561815647 1250 561814397 561814411
    0x21051c0207050c03030f0c0c0a0302060703210c08060102370f0606030c0617010807090504061b0503100b0c060a020c030706140402130b1003020a0314040602030a05130506 75
    0x594400c42403900e80d080608a803000f03503250102288103410b440c04000201000001c00060701c2040d840442081a102024000a504072400307003da42c3c0060f028084820440449821000010685140700b01c151044842400c0c0024040300520825507010410348082880101040f02c118048500840300e49410310068507010041007540e10900420f25a10440d01ea04040180492912810f281d001d001c2584211000101003091b802030320181703010024183c49036807002c1c05500e49000001070107040d020b001518116660020700100700d00e413010744000383c0d0301034807116220301d0034440f95900502e01e0381c03001170000b01c10030980f102c450010034070702d5024404c0440141c49000a01c8400d01d94019080b00804040c600031904c0440306400c1c190701d20a61003240c21840e0729a00b407003041c09844200b650f143c0c00c00d424650004e14980203401505441a1603e00052480242503001141000540c1d048e11265400400e10982c059103000d55580f00003007582c132119050060352200d42e04d101c014505 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 561816897 1250 561815647 561815651
    0x60b0313110d0b010b0c19030804112107090509120301051314040507031209051f021c030504021f1d04140a020d200a03020304060e030721051c 63
    0x45403680d070b20311200701e5481d500141410095a100c0e1450060f60b8002c461042191050b141c0440205101d01000b80a050789079441c4065525543d0303614961030031001c851980100c20700194120050000c002c41c0c8603240480040c11682c0c80c0040403403c880d0050030f1020070b46c120b0300608503a41001e004481c111001075444800310002141003800501e4280035800e15020864140002d2000003c0c822098a00944007150420390740078094880310b4045c40390a401000750740c6040d04001d03115441d0000038034a80180d808005a064003640c0c0c91603107070000c0c0c010a6959081c4015802d00482c102c005034503051911420103030049002d00410300c4038005540f4030f502c82400c0c01e1b00761510b4100703203581d240f41c03440b103901418503104201c00ba40160101010b21441c0c01c60a0101201c2c03401d00950164001d0990f43c54a50340c040118040d5000410a582807501c60396206d0030070380c08000901040d0f00480c001c1420b5180740f45c0c01c10920302d141c40103804120080c00716000300b5002c0580951000c010f4480 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 561818147 1250 561816897 561816923
    0x30602071a1605121009091a06041a04091112160e0c040e1503011a18070806040f02040e09030405031209030303011226040f080601121b030b010b0a03060b0313 70
    0x110402d011725580040c8002800c1c40603890400804c620304500c0e0b0328a040c0340c80b20960b107400a0104903160018041ca81c8209583e400f41e0760b0426603c2403041c5801050f450340c040320000042038403414401c0703d0745429401a010b0000f41d800c10075100c03001d840c0d032400c00c107490b040c41c1103007040d1400380307004a10340c864075003021809608002e1105a441d0401078000c0c4600e0000ca900c091280c04001c2d011030181c1854662444484008403004c0e00c03c40b8a6120001710f0744581c3d0501c001400210b080484880d03080202203812590340c15214460b800c0c500c001c540e201c0c10103060508040d4941e00c100010b44090040980d680d6010058a055403101040130b11003600c241000214180017003056414001100e041c52403202c0400000c0c000c0d10101304448003860f03960300c2c80303550312402442010442c2c05140d509000140110074035041d0a070340c400380b035614142c40e83c41d60400700d0801e0b441403650000000f1401156505801454028002c8031881401c2d868001c2c07545e841c00d044104000d00c5c60742090b003 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 561819397 1250 561818147 561818161
    0x91704060e0d0812180d0203040e0603030901120209010c0c090f1b0905010c080403120801061b030206180c100e040b10020c011116030302070e0c160b0c04030602071a160512 76
    0x2085d01403000000e01252100101104040d45030350142c019000b4007203500300040d6817820000b0845102003010303914192140c07a01242c400003500011500f1f410050b10f0220280401d014a644201424400d08006022818070914000b01c8469044803c440a09070903a908a00d8000000ca0203d403400e08080e900f4004924003084244603d0b00000c000444085920000607803200c1c9a41c181c071140c0d00c50842080007c80821241c1000e1100100103034070540014407041a003d0a500c0c8002c5400700301d50301c801d070220020744005840480304000130803070604040580b41a00500c2c1c0c4518003a50300020850820b1402501c0d0200c0003d014140600c0e40a01c0c00110810042500d2444071013012070411078072480c00039141e0310188904580080000088ac40c0da00510044580c0314a00144804070801981d030340011590340242000c240030f900707100c00001305000f4002869001d1141501e5400b000b02c0781001908000080c1854040c1070301c01040c94125900002203d1200d03400c4907200c52103a6420ba = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 561820647 1250 561819397 561819421
    0x93311031e03061c33060305010903090f14010507052118100e0f2d090a1401030f080702060f07060c080919050c030a03020a1a0705090402030703091704060e0d0812 72
    0x104405419140c0726000088c00419407240c040c00e4440c0e5208451580e950030040310041c140d018031760ba01c080340190700c071081d0b00076002041c41902c644c09403000300c80d5980c0400f00b001c07000c41c40604100c00000702020000c1c681b40717080e00b240700100c6880f81d1090041200400148030b0080190080000108242041d81d4140703150142003070401e144e401c4e10a80904054010000700c3c4a640140c8010012400340b5420340141101c058810540c54841c1e869510340000190000c0f00a84e14548208200c001684510008204030440c9100490740ca0b1240d01e040d10498480b09100b0040040702000d2096020f008074083c3c040c0204000079421007180b605055050080b1000d41315414440c0c8028141016008207031314031014040d09a200310141240d5039045c00e00800c03110000060000c1001100c0d51400390302468100015250003d4486440d58800e00600d207090380d20582080d0118042012980c0300f070842550038019500f00c6941030a81d03440304098051a050b08075880080b10000b141b00c140d0b1 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 561821897 1250 561820647 561820733
    0x60e040212090d0f080f06010c0804080607091d040f03140c0604061b02060f04030c03030f02031e09070e060d0311030a093311031e03061c 61
    0x7410440307507942080c84403195a56003401c03080e0041250b001c0c80d070001c40c1c05860158424a011b1100090f596150401103400b1103211104540e43c1c6030a21022034800707010480c061069030151207030310000d802c040b1044811440040350400c0c091145041000092580b8105c3c0c10743c65040c14422180c05480300e1401d800d01900b81500810f01c2203200b04414001c45030009102c18550446807920701d001c1800490f00d80404540d2b0155003400d25010500203481080103003442c5020b89800200344da0f10110120503a0b1040e1082c00d030031010303c1800039545071130402058019244030000c2507180d00e0144440380690004055912440fa180c8a500c00c1c1030084600c40d691851403404d60340c3d110000d100c0034010f040140201403401c500c2041080701c3e02032003500048100e1500c4c0e40c2011003000203100710f07580714400380f41500300d000901921021400c400740122100300560852516460700c442401800305141d1a611707600e034401690707070010510742c071007107100164040045510207205500c96002030343c203 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 561823147 1250 561821897 561821917
    0x30c100e040c21240f0b0c24040c060216091e060b220612020919090e100207030516030c15020306090f0606030619030b09060f0117030301060e0402 65
    0xc0751180340200c101d658440c0700003844c0526008505034160200c511442d140e8000d81784507100d100d0b001c1c04050545005485022210400c03030b8401c2c0081d4612511448000d10309100b03500051090008200c1c0c0b170314141026000d18070080190110414815032000441d00c1a0700c41e890b6507441492041d803204c2f01824041301003540030f2240c19902e0404001d25804203030f035104004124524001503500e6050480210303945603403021406030030500c0b268029403082101550140810380401c0380700103c460148020088000009404251090520709254613816170590140c410001e40001907041025119141c403242e019030380101d05e601d802c0e508815608805400601c025410401d021500c2d0000c0d0311920080e41c9a40142e11440f800315521401079500f5076111100388001103131820148004111040310003c0300c5170715552b0344c45541e00e4683c143d41001060b0050810000ca9003400b8000740d004001038500703050203003200032003103480e07000c1030040c0810001142d1b003d0440c3c0da07031901505c1c3c00c140 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 561824397 1250 561823147 561823187
    0x1f020d020307020a1b0803070201141b010b010e010e09130311010e070f0608061f030207020603100611070b040303051e13060807090807090b030f0714030c100e040c 72
    0x3000782d00079686458150044a12000074400035004040208041c000c6840c080002d604052242e4015680388034103400c29903040400b07014400d1805d0300e403820000d550000b0f200008201c0a1140010807000c1d81000a81c1071080040c40c160403512001c00060344001a4800740307120b5811447c00700c480d418012641800740d800d00030050b98008000c2a602c0c116400130702031741c0700c0d55a02e4401b41d80c0d0b03410485003d43e00881d0031114210081342c26880d907125115620b001460f101d03855002650a81003070707520082d45684840c0c18082c2c15003090301000d1040b035640040c144280344c044614102c0c4200d0000404101d80852100d02c61004030907100000035200c40d805440c1c8005d00c00d82d080041c1c00d44251030000310306c40080798172140903560a070242d40d805006041087d00309285600640304090440b5003602c175a1140c220359242c04d00014000d00809400307520000d035503030308040c03603c4c140b980518821070f030710840a0030940c1c00c4441c200d40d014040d00d0104503103e100505649802054220700000b02c = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 561825647 1250 561824397 561824401
    0x901021204030512070e012f0d0c0b0105090121052e060b0c0705012304030b070f1e0e010c0501060b0901030f0926090409030f1b03021f020d0203 64
    0x43d005805415601e10000410381c02e0b1341c070868112115031840000e0f9011030503c411400520760207482d540d40540c0e41c40c0e0010421442c40c2110303450441c141c600c58002400e8006d258042180c00c298050040c902201c03a0740e4a541444002e4040c20b038401ca80c1039451009941050400c030044c4100300810111007418100b219000025602d0708040b00c0200744010710700400854a90380080a07a50324018020050000d41e04180042d0340d09500444030009c600d02c100c1c03011406035901ca0061000e0742c8500180e08517824400405003001d0b00c079410540030302110318031104600d92459500340642d4094034000010185400058a003105001c501911a5080c40c0d0301107420a044030007080c2d103071020b1f40c081080305450150b0380704aa1201d80c00500440845646c180b089018140181d84d049000b0401c40c604030013500060111499004214003182e10030b418040c5283e0803101d0030310005a015064071003207981d07039002900da21906510050a8004019881035405154103a400051041c8001c40da28 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 561826897 1250 561825647 561825653
    0x8010b0c0c0612151503011703040803070309080f031c1d010c030506100e151c0e0c01090b031306050a0b04060f15050c0309010503060f1804060f060303170901021204 73
    0x6080220b07030001808100b8071002c99281481141d00c1003141c015405d01e0b045034240510207034200488003d2031414482031002150721001030000b0050584030361550143c1a140c049110300780b100001a8038000c1c0c00c1480701003074181100841060840c601140080e40c03906c8001d04200c003001001c1c0d145002e42c83c0040d550850f0f03070160f210078010241118420303200701c21b00f101103851007940d400700d507008040d00340c0c4262080468406807030b00d10318020980b0b41000c07038049134000300d0764003a001184c0c50740a10780c10b00301942c10141000107030800305203903440c0d0703c3d0260381c2e450345814010000701690b80d20320001d280b0510702d61003004032400003403090000699407070f01c004254144e4081c131240084805141c40115014004031a080351024000e54204400e01005466513000100503541100c15400c1015096070b421350f00f4660007100002102150400d07041c000201c0350241007480645203170000031f0001c40d400c480780c00c10000014808044590724420f41c5230290003445130b54082c3c0c6008006100070 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 561828147 1250 561826897 561826927
    0xf0d27060b1201060602250305060c03010603060e13021e04020f0d0b040e0d0c020f060a03050a0609021815040e04030512060f0906060703090b0d021c05060108010b0c0c06 75
    0x2401e0895120b06444182e01d0350303034204d50042c030541d00942d00100e550600c420044640d42603040024a0340c00c01c0d60365070340380c440c145403007110612401c240000040c0040782e010720a00c00a8a00320f000f000031854041030b9901040031407072019105540401c0f06102501480003440600c9034082d1055480d6542212410f000780c000d901503c000d6070420240040740e040c148901c46254015500030400451207440079142141001b03c09d136000601155912410345850009000700581e5960014040c078004226008035025500103042c0d080c0104030103001c0c404042c100d8030544078100c80b4111440c00203800394000b44141d40c442100d1750360300d500700028150440044d08466100c040002c00c5680d0f1441001207030000c4a403c03503440a0303c07070003060542c14208081e03c0c0c1244030b410405440e50715001c040584e07801c5100040b00c07070354002400e44aa5110280c14040c00c6600010a00550030305a00182c030104050080c0010004081004440201d042082c1450450041c04c8155220421700b01895 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 561829397 1250 561828147 561828161
    0x606030204031e1a040f120c02040c020a0203060c0f04030507080708070e0903040b22090b030d03050103080306040228120e030c060c090a080601140907050f0d2706 72
    0x2440401420164080c80e0f008880401c02c0c0d0351100e44030f00250400f640d807040200d00a80180e4041602d10380c9540001c1003125900e10712080d6407500020b4060b60702c108400d4a034a03c074030300c0454201c49400310060f113001420940180b0740001031900c90b2000840c8100900403a40044c010340b140420001d04000082081c00960b040201610407064036100c20010220003034810114550042104100050210001c0c02e910146140800202c010302e1704951080f000e079400c10486241e40c0d554280c40d5281c108100d015416850074140b005614544480c0d003240401002d150146400084400e01382110103c500d1100d4000600d02901c90000400180344c49402140124424036040d545042010000181c1d100384c9000d80c0201420364cd5103e4244903500f161181540000403a030000c80d500c201400600c2c00303440c0030202c0845520f80d040400c10700c1c010103090308042c00000c021310b90304102948100d80c914100d41d0b80c046000c0c01c1400a007050031901903250791300990f0702d880030f4080042d0340d00110 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 561830647 1250 561829397 561829403
    0x120305070e030313060206060603251b05010b0a05030a11091806150a09060302030a021516050f0c010e09070c230c03010f0c0f030f02090a03030206040308070f0f030e070801060603020403 82
    0x80c0781e0303580780b41c14270083d0310082e101119591801000380d0503030101841150600c01880c030303242c1c13880740b85501140305c418032280089649946030030448490f4205009010b00a100440050444400a850ba44d140d0001104002c2c007a038801d00004015500d00940a5103082080c13080714618a05140c6920640d00c8011416210b82842c81c000183c480090260500385c0303400a02400ca21040d503402c2103240c0c440340031500c000403014420440c140710001d942d03005031405500030700484641031410505150501e4645418004c00e2804810f403a00c8180002d680b100040c2080d180302c014904050312044003200d6160070448407041c041d44003a02c04607050718010303006d030002e20181c00e5400320082940d403204185000103d0380c90401e1400b81c07003038100d04a200610140107240c17010740c1001c1051482507030026409a40300d0004d100c1010740c06041710754031a41d1031900390b0710000314050040004901c1c1c07484504154803400e6003a03036160184100e0004006000007040000c1c0d662802030060f4125210036 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 561831897 1250 561830647 561830653
    0xa0c05220e13050d14040e060d120504030215030c04050616061805060a09030f050a0309060e0604200102060109021c0c0207090e070e06010f020304090c09050906010c120305070e0303130602 83
    0xc0c088070f500030412000e500c290f007a1106c1c01d042c00c00c4910092120001c3c40b0340d41c001090591034000c1030102086258030b001603501c0c9a40c4905600601204c18240a08044204803c00400c60320580030b5043c0c40c103445c01181c11580d1005182c60b20940d0365100071000c0c0056140140d032160945244820b203da542c410425602d0aaa401c1307060000c9400220016000c500b14030154040240700f48000c4c046071202c0d0600082a800c161034110450f54110110b1001e6403041c1c00380801e00400e002000b1040002c00c3c10f1b11890f0b0107600c0002d442c0d80c0c040c840c00a09540101e290901140001c00030141c0c0d400d03440040003c2a6582d20095907400a0f11031200b000d850300c50481102c2002003000001d4800d01960052a03441d503900445a081d5500d40c2c2d5000c6000030b01010070043c000340070b10103045010b0f40d1800707a0b81d400d083c00c0000a01029120303034103003d26031080c84001920a485a5a20300003424001440c0e640c2500680300032045400840d0f03d8000040c02040f15507100c455002918020360807 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 561833147 1250 561831897 561831913
    0x80a0b06060a0804060e031b061b0c070b07080702040c030b0108150102060c1e0a0504050a06110a0b04080408100f050f19020309030415170a0c05220e1305 68
    0x20310219118a0b00c00303100182d05000007401203080341c1c20441a00704090b086a24118050100360401d00c0b141140d00c0180d0440310a01100b8002d034101c4001444648130042d180120018540341d8442d100d1080202c0d4502c0403075100705000d445c2c004d580b2183d4000e402881807031744101c4001c0c002c04120300001e000c00d03002004038413511030410518074003c0e0180c00511003a215104000c00c1c84d0000900c1c05210f0301220f0180c0c0d400203c010141001c561030351200c5131114181410080c11390519082407042004010542102000c0000c1840ca83c94200200a52580301c50030050454070a98000041070301c940030b0f40000342415944404408114040104103d40b20340c2e0614803443d0059038881c0388090800d0300c081c0c0b450060350086822860070360071246040d5032089034079500c000e0140210003250b800343d040003240040d00400e40d48058100c4082280303404c03414016086028021142c21100b00e18151200d200581c012080d010b0480c02c00d106680d49041c0780f800ea0154a0403100325514024820 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 561834397 1250 561833147 561833149
    0x70806010509040627030f200c04020706111b060a0203160f02010603050f1b04020909010b0d02041a03090d09051f021f2306030c0d05011b030f0b0a1202090718080a0b06 74
    0x1058030700e010312310048c09106501c0020013000c2d400403002a240c05589480300e01e840030400c40182115040380c0d40280e4000200a4094240301c030041c8501803c030b004108108000c80c400203044000e418506100a0f00c0d190410103e00602140e000145540708070022807404020007e698566441540b01517040007030110107002c141e0003000607184c0c000c0303610320040c009da2001c5000b80c41082c5401e44010304056598007844201c000f04500021483c0c0c00100380f022005003031021068a48507030604024451030302e00841d40710f00c010800d180080d801c0d4a56032181c20710900000094030b084800c0e55034903000302a0104000c085212034070705036414503841da80080302d07910500ca10172000100a8000343d1940000c2c0585000414400c0740c0c19503031071003400e2141c0600c015071500907525980c00a68174003c00c800b10200e800c1c403014a40f06120507481040340c41c2150b110141c20a41c1558070300c466032588003080e96002c070703844000c0109000499010a5401d000150704154a016028280042d25554 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 561835647 1250 561834397 561834437
    0x60f0b03010302010e0d060c0f080a05040215030613020f190206040b01050d081b0c040c230714061e0609010b03150102030d0e0708070806010509040627030f 69
    0x11080944220040c00100003640c040c00c21400212806001ca4042c04603a94407041103c82a4103d800400c105203400c058084c1c1c0301049036800a141001007103641001d0700024a141c81c0300e0403541c00d40400000048264442c0000c2c580c42c20001c01055448082d2002d00c6403494102c20b960701d60804516a40040c0700b4070000d04c0e0f0340283c7e000080d20381d00364203003400c0c040c51200e80301058810183c10000c26050074417201d0010f00b901801400760040c1304524042105490341c1900070030412003540c0408140c203180402d10712400e651580040e60300d5020f4906039159030b055a01c0d00c09a409102c04102086103040d00c4090404a0104042c4e0655560307010807018200a0141b205100c0003030000815450380254140004101401104e041000c16107042056680020300c2c080039400c012410040350780c040107070340003074050f0f50060030b46581000086048201d004002529894448054040c2c0044203808e1504410224400744440314080c01e018014250403102500058085070310f03c82d0860b440 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 561836897 1250 561835647 561835649
    0x70c1802030c1c02070c09051509010602121312080a03050f0f071805090a0906060803070336030c1401030603020f0d021503090708061302060d05041a0c030a060f 71
    0x10b0403119041211002c40c400e248040b0300d1507030762282e80c00c00007000400e40b080030303c00040200c0b11010440c0d20700000140016100241c0440c0a81d0f42d980040c8245600800c24000c40300d045081f40d91903041d919031025044d16075a02c42d07030702907442030805000e12040400400c05420141c400384610707200c3e0f0502c1a844a0102d901011010aa2000c134203643e101d601141481c100b52061503503140d80b200002602607205a92100c46559607012800c200314642c003940300140100e0010f9800c007161520040d00c000820450720001c1e0070065041e400b503105115202080060413004051102e4903031800f8500d4504078092404112544920b21119611a00804040d80d9000e00b50310f82c01c258440074040c102c0c41a00040b83c0c00036041c1049030001d8510710107103108201400050450520746143d50317080c25009410490021000492400540c84510440b410802130b40c3c0002825980c504120301b031113003101d82c4550354070341a02c1804510801c2c1400345014145240c400c10165940700041c3c002c030201 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 561838147 1250 561836897 561836911
    0x5040f1d0d0c0f0303090506090105061e1008101502101b121d060a09030809030f121003050105070c05010605030c01200c03120a1d030c0d0611070c180203 68
    0x6451100b000072101e4540c035007802c0c400c2c140455180b81e203540c0d190a01c0000c442c600c2c496035481040113824640541030070907107002c00c0c42c081d600401c242c020540780034400c14110b0900c1030032004248246204a6660024101910015405c450300c140094458444a4000401c982002e0200c000d03040c0d0488901f0500303480d9180c0a1410300c80c44000c0d8050006104008020041a420150a500c040c00054031a0841800004681c021407401401d059009010f000d03465005100b180783c1d940c27070a000c0f41ea041d480300340701020035942e04d000c0c40040c89254200034115400c3c502440b5050b5004010650017030704c00c00080c409a51500e003810b649500811080b80002c0000b2145248840300085101d92101c202041c1c4240c0307044000428600035140c0051100400006040039555170302c45022801620b1000d032202ca2550704400280d503074114204101d00c200703c0f00c81810f00704240c5034440300401d14800d000c151150b5071401c3c002103da4043c81000c91308111090701c4084402540b08a80c42268 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 561839397 1250 561838147 561838157
    0x91e0a1a060f0703080a180b0108010e0c22060b040605090306010501030c120506040b0d1b0b0942070c0b0309030313150203040c180b030c0d02010905040f1d0d 70
    0x3c915142201c0d042d00141042e1812640c1d0300d02407041e0100440b14407030040c0582011106035160a07001802c4880c02c288005c01c9420002d07003102c071907403031003914010000c4100070389400004441d80000108031503404a98614000200040c100b50000e02602628074100c084d40c1e10b40e0398231030040d025222503030500c100081001c0c40900e030404050b030002c0c0e0080c42c0074000051103c08031010075a1401d1142d01a55083c020500e500e103400c01e803001c0c03d0094a00b07030160b03504001000c000b24004025020400d880384ca1416504022104d01105030600310b84032072460500580c80d04440e0046920180064500c461354408c0400e50440d440c2c02c91303000c1c0d00b08400a510715070b604103501c0215580f00c00c08441d4400f065184000f01000e90001e1030066000300a50042d42c3d1921230390400b007214100c0e840c00b401c3e0502601102568001c03039003c920b00d100b90381c10701d49000b45100480c0c500c0041d810141d401407030102c44004609443d8072018a500956861703201c403503182c1c4401540c445242c092403002034 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 561840647 1250 561839397 561839407
    0xe040e071a0c1e151303051c0f0f0e190804030803190903022812140f0c060a0b0d0c0504020a0516060504111806091e0a1a060f 56
    0x3001c4000188800c1c504541607503901a000c200016245a40000711101640311240a1403141041c2c6440e035000304207640d00002a48290ba4054110700442c1c07120000b01040c130301840c014003060b0700b0009030030511403020400a445215070200601003052403a00b14410862181d6040c1000381921a00c580c21900c1c0134109403031030f0341c0d07114143d000501c0c0082014504807e1200301c1d075240148500b040c821b401520350f07080069003000058140800007043c0c10040010040840c40d0f9800f007001c6000a80b500e0b032025840300c03100703031018410b0800c03040300c0f01c8002404220903100070400354041c0303445082c01e01c064080c00781001b075810321a0a02418410765000100580d1400c0e900510004225040c40c0e070500709082d11000304150320501c11703511261100100006c0150b82003000440c2241101c6802041c074440d002d0f2050700c5801800301e4080c49402c00454003010549442c242412205010200185000c0c041e407005404800da40751380706000305c01151014900131095454402503014914101 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 561841897 1250 561840647 561840689
    0x130e0619150e19060503060f040506070c12180b0f1b0106051507020418060209010e102c220e01110a08040606031e14010209100503090f07060e040e07 66
    0x3901c00e016800540b0356130480020507460510400d40304d007d00301c1040206141a040c114140880102801d007000041e08004d00007896100c4a45100740040c0383c002c450a002204815080000390080c40215070301040840740e03115100700404c2110707035040c210b13241c520031400c03034509940441c080d05510a0707040c061242a03040000240c00c146000500100c1c900f21000b02c828908820b202d016100103800082001c55542c01008900e11143d0170f5400106a8110400040071031705000f0203902c041c041c0807440e4200708010030341c0d81c5030020000d11071043c600e109a80400e034800380012070005c540c148103e503d841c01061080b41902000c160141d4941408880e0441e08403000500c129182603544c0b40100214641088560030480054920620344c10641400c440542294a20600e540e00401c2498565200c0d20700348983d41c07445003002901c0c3e0310341000040c1841100008141d041c441d02c00c00050344d55114142000c1c0f000290b41c00c11000c3d501c203016a0712400540608144040c0b400862118 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 561843147 1250 561841897 561841921
    0x120c080105060a0e09120703050c1b0109140102030715020309120a0503150102100c030e10060320151204030e06130513090501060e0717040b06130e0619150e 69
    0x80581a038051b07414404000352420201c1d08040c00540000c3c1000c20400003501c401c200040d041e9089034074005440c04683c0008000420074000c03031078043d00c10400c040c61a402002a15180396016807800180c10215509000a400c12142c0185910541b001d9070b00200c81c80b403c84800c042c2c6580c0e820f245643d03c42d40303038050b040d5442800f8110701c244098244845454850070f8a020150b9a0118038120314402807850a441c2c035040c450120710b44002080020030f000480c0c44030a070a288100c60740030229001a410074095003020f401c0304800506407180d00d4210000c0d6100740d21a454001e46803c0d04420700080c0d00441000403200e03001d102043c013091030700c0c4825140c4844007443c00300b08900c0c26503400b400d41d4242c0d400035400342c10010600c450075070000042001440021100d0500d4600b68444441d0540081c0106004044056209503641200c0e08121211031000080b00c01da8209914090800e41c21150480700e1140ba044407880c3c1e400c580c4030024101d070104802a202500c2c0c80c6e1309805 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 561844397 1250 561843147 561843151
    0x406090b100b0f180603090709051602210f03010906180b180606040f0320010c0302190f120f0e03030a020706051c05090304060f05121915120c080105060a0e 69
    0x501d20b44c0c11181c1d40070315a01c80b802140f10f00b03010300103881500c2ca80b08104e07043d240013400e858410101c10415440f1682c0c001256138800706581141030500000e500d108501d40300390340400b04080c000000105080c100c60300400c2c225609076004c448a03480c50a000400c881c030398030b05607a0007003400000390280300100100540140d80140070303600d8265107050904a540340c0350700444103540c089403042103001b42e4051f09460a2800c0c20000c01140042d41c00075192034405055041c059034482e000000e01c4001654103481690284400f024100c41c807002400603115130101c1d0000829012a1a02d40c0c1404400c0e01c5880e0302d103800510159042c500155540d070071042000c7d0140c5540d40c903100c3c41000602540780240508c0c0041c0d45c0d62414800000c0604d05100240d00c14058204500d44190390003c0406030300c40382c1d0703091036010b07042d14401341c0000c1c200c01080001803411201010a48140e012160401148540d440748c50303103a43d0340c200701d0980d542120b94a60005031182c04000300440403207455 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 561845647 1250 561844397 561844417
    0xc031b020406090216230307031107050a0609180e0c040c030207150b1519051b06101701110a03090203070f0f03121d0f04090b0406090b100b0f 63
    0x201e421a26040118100d030058550806005071250100c030a000104046c254482d04114008000000c0120120740d603100389038000b401c004200b05411004201441114060711000f050181e000da91110010b21580b1a80070314901d00001415594a0901901c6400203104003100507114004041c0c0070003005080715004001416000c102000003d000c0c07002111140341c0c00786000414a600710180010440004007008450130100400391645c07244c510540c40c2c8048501d001039070b41241c03860023104074000300341e101d0651065030b044c400702d1070844000d00241d600b0710801442040001100d80c2c03d039110404034100c2e200d002c00001c030b0590700c2900000320309070005c0c0031a03515a6803040100b00c2c4403910b40c011127410813140018800c00c80240c1d80c103800c000c20b40c600302404412000544450400031002c86100780d46404d0020503031b40702c07034204a982a0b0802184a802d1809003048005420741d888122640304031540020a0001607140359400d94200c2c0d00d10038100b070024090040e41d580110284 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 561846897 1250 561845647 561845651
    0x70f0311030f070f0c12030903060b1210050603010b1813030302091009180203090615130608060604150609030611160f02190605270a03051b010c031b0204 68
    0x10002d0600c400403e0101d10039801031402518a05002020900640040d060129604441c00100ea88401d240382602c0c0c001e400056418100000030b19003800b00c1c101d42906014121004100c000f0540c009441510158005d1200106110403c010f0076008064812400e201001003500032038245c40311051103110b410010328000b524000210340c40601e0041000180484800b802aa01c4210a40c900c8609601d4150b00354140340b0607258460000a02d06414a030035022003810554a42c10701441500d858803042100325112070010b919210225015030040c0d040c640f101600c040100003800c200c41031036849210b242d0a540e01c8402810b4405e00208205100b84900390b0400b105400720b580085c441c44c20030310010428418080c0440415029075000091440c081000ca504007085610004404942c40c486c00c003c0004200d00c02c1e00205000d0304920b07115408001c2041c0020515400402030051104002c20b0720011030b88003603074500040024800e800d5412854500c0380703902018900c02840 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 561848147 1250 561846897 561846907
    0x90a050301060f091503021f180602072c06060a05070c0e011805061516050d0207030201022802060703021507080624030f060d080c0303070e06070f031103 68
    0x307003510030310b03080003415181e001810020b820321846114840c40e030301468041c0346880c50300098a940d083c91100a541d1580d00d00341c210140c8110742c501c55140b00810f511241d96210030001f51340e01164000c0d40c2000340c2d00f580c0354071028440942c0031590816540d440f001950351000788000c54000400038418490188622000641c010203180c0c007800700003080c0d41c165858014128510000721610203081880c28040c00313081c0d01c5851182540114002c90705a9801012840c080c004140c9203029180b4000d154129142c0b560114a60085071b000b642118070160b070800e42c510741d8900d030360ac90490788a0328569900c01801c0c004090506c0a00031b005070f6034001c01d070019030807a122085920100242c0710f0000c21840c2d251440000c217483d46a0040c058941c0c0013401003620314403001d40750708414500c010008000e9139171080401c440d41d5022502588404800e50b00b00c0e560340050f81c546000c1291000b400d411410700c00d0680d00100c1d0052505807418030241c41c15158060030790000903582c0003c01c8 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 561849397 1250 561848147 561848149
    0xc0f221503060905150a09030c12050d020f032706070c03030212100807060309052a18070215060906010c030207150504080f0d05030420120c090105031f02090a05 71
    0x302c1c03159100d00800107001c009680d083c04602611009009006e0039141008800110b640850112446940305003040a6070300c8051041c0d90a01a22606002c0c8900001d00c400c4492070080c00380d405124a900c100080c40b12410406508600c000b4000f4000d902c6100001d441a06c1001c035181a82d00070301300149800c4c0c01807000c0c1404041294010380704586038000b0001c400c03007000582e00500c4545003c000b034401c5030756069122005101e5001001c4440c9050032034021000704226940e4000402210f00c4424510f00004445021100e0343e000d40100700b10384556806840f11988208001095104035540386801580d0482d0014800c1c0c0c11440b480300080760620700301142c0051a80d540c1c44047d203c2e13140c23612861030f00150040c2003000b40c01c601d201480254100c0c00b544d80155208031700c0c00d440819241005101941c0c2c1c2da0003075002c079100780c000c09c0c2044003051079001c814083e90f0750b40c05680c0740c40c00d0690364a82d00c9450320319580703822600300d43c0c3c1003282c0c0504902e000c0108400c5e445030f41c84c0 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 561850647 1250 561849397 561849401
    0xc03040f081219020f220e040b070e0f131a0411091e010203030402060a0e090a06170705100c1a04080316030515062104050c0f22150306 60
    0x20003a42c8400703009000f407140b6102000f8a15080b500080000c0d464060008030304061401644200603051452818402d034402e0040312035000740400186102643c40c050501041d08103060318028003094466800f0442414480640848814007820244001c0b041e0301e0b20390020495201052499090758117207202c1c0780c1c0c0303501030141c0d41895000c400b621400c1007410480d000089410b45030b00c14005040404a42c1d8012003541d80c8030360100c41c6551115070000d820746030741009068556100e12030400304500d60070143d0080003502d1002c10420b80301d4031184180c80e80ca00da07501a65a004440c3c48260152501c9042e08000c0c0c3d61060040c2d00007840380e40d0f5621107100d4152000c56081d08040100081c05080c03100c80c2c00c0e1000245424441350910642a40810a602c1c1d40c40c0d014941c00600b2510718071265048005009a03907411004602e0036043c01c0380c803010400d4005201da0300c8180140181d1a20760b11424500311000f1182c0190300560911000400f440c0400d40c003038044030131001001c6142d40c = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 561851897 1250 561850647 561850657
    0xb07030e090a05090d020307110607030c060606030501140603090a080d0609050c090102250302090c120702100506060a0e09060d051c18060816050c0a0f02090705040305060c03040f08 80
    0x80000410f140c103100c8185420302c400c02c858102158424856034001c01c240c019a046001c10640b00700d41d03a0341c08d40c10308890344070b01b800014044c1402d0103c0011100e80c16400b01d070403251070b40b0303000c1005a614420848540320a45168a85a00400418011400c0d1000602490602841c009101d550f11460142542d41c100e0300210201008141c510040d40c051041b400e075040d0141d82c20003100d0000525001c40308aa01002c0c1c064000c010000c0e0311007106204035500c04038049034040d040c3c0703012a8000d554a980741c07648281030f81010045034840c103003407042c1c441c00b0000b84ca0b80716021a10b0800d10403800302c010302080d031100f0706108400c0072541c00e110300c10b4401802100511350180340740c4080d04450300b82c06a1010203031103d07005c00a1645c8082425000780d082c4e94504114003000c00c04031707a00d000d21200c0e05464008d91909404022418058030303640c81c403e984140859440c6072003030320280164070010b01580c20140004000d005040000c65007d4030590880034191240e842d950320903040 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 561853147 1250 561851897 561851911
    0x30a0b041d0a1a04022b0b0c070210050408030912150c030a06060c200f060a030e0c0901120f030504091e050a0e070521032b1103010b07030e09 63
    0x12840c400d0081c44200035607403602541c40c1c80c0d81c05444c102580454202c0ea0040e581ca00b600e00400501d4a5207842c42d11001e01c82504010b40c0c0401d030800c554540c10341d5000d404201d10030044203159039881d82c0584142d0341200c0001c0c000e5428440b1810501208850715002401c00d8004e42204282ca050b64012031805115900c00c01e640741e241050450040380d00c5600040c0c144841c8440c2040020398040e03c865880e06400d4481109080450128000740401c4074002da000c400480c3d00401c2d5a410781c031024030305030070704200c440c030131203500a006050401380104920180341c240c01c280400c1090110300e100a02c82e02e0311a240540d50b074880004c0751751500c0303034000850001d114110004002e00610b5001118208200150704401200564808440c803425004000c0170712240000013000c400324084502ca00d05680e50340541411600c000074a0034181244080504c00242115400340305850a441e40140010301c0d5908044603034105421800b000c808010903142d00a180d600c07140d401601aa60b = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 561854397 1250 561853147 561853153
    0xc021212030412210b06070614060118030804050402031f080318040b1f0c0609080c01060b13060315172a03120d1107050a0b011505030a0b041d 63
    0x702480d00c3c411a0700200c401404000300341013101c0ca940031410395900602c1141c00000740900b82100400c2e0607001d43d1001904075403400d85160380462041c0f0f803a5100d010240d0792413858110055094142481d04c2c000a0a0004144014069403c0c06d03401103800000020140c6d01d0b04c801224401c10603600d0741c210b0314003a080403542045607180e0f00c007010a54401164240100c0b80c0744008241510b0305103030b80f031920304001c4070400401802082510141608000306200f041180d04205c01c10368440590140e056282010010b030681012003500c0240c0000d000e000307000c900d03101046001c1c124506076a5084641140e000407440103000030706100c90b5082d005001c06c1040104a0100c442d0003200020100e80d40d40310a00c4955004980c00b50300602580e2500d40359080f600d94040105501c50420056000c001518001c0c8a0005069400725114003190200c0d41c2c0c0700da1114452042020070080425014808684014dc450300940400c110203000000c004004100d65130b9a2600d601c18030405030 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 561855647 1250 561854397 561854401
    0x7080f092404091409030d09020a121b090905060c0d11030103120f05130533040e0105011d0108070e04050c0a18060f0813021306050316030507060c02121203 69
    0x240f204e02034005000c4032889610315525080c1e004640302c0c4198110351001c1c903910341a040440d0768203076010016204210401c509407405d440c18030780318011158007811a004152000491b030480b401928a40755008000c0c1119807512894803441c0d4000b0300c5001d03141c6890380c00d1031441c0d201e901c010758000c5018502d1240081c440c104041d200d62502809002044400c10400340020ba802d00c510048170b00544030b0600d031103031520210400001490010454110150141205048600103802603e402e00d401e40403c1e41ea40c0019260311190051022100d8000b08000e8010f41c01181ea0710f5010307100c2c0c1001140c1c03e0300e6000003002c40340b044401504504000c03894250703284e0304c1025a5038203415101c98030f00c001d0400d20b0180503502104030180c104804500090086114032010b40340c04e50f4050090741440c1c80c540c0e0810007800542c01035070301034442d0201d07102e012143c8202c098100d80e000f10187c00e406042c054100d404130410380041e030300700d0f1240c4a01c0710b0401003040841c040c03400e0f19041070784074 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 561856897 1250 561855647 561855659
    0xd0e0a03022505220e011419110a0302040302030d02070e0a110912100b1203120709030f0c0509420307081e0d1b0c1203020a1707080f092404 62
    0xa514603040d45c0816850700b180740102c0002c880c0e41a4225250a11784101d80e10100b40c81d101504c854030700100800c802152948035130780c1540140c02542d1003102550840702d04070f0402ca80d01d020610074140c1303001414001c101c050f00c0503480016054030b03042c0014684a91540821080e600c9045071440540c090020292104c98a100340900030700200e60704c440b60b4905100c0c2c20f98a00406102201c0501c040000c50314050141a60000965009045401c0106103081104003000c4038031aa500480c200000901041125a40041491900701610560ba0300c05e00d000c6000c1ca102c00c980726580d1200b60f94081150340e080160400034842c0400421140b4016520642e00751400504c1c003082e5800707400840300d82c0d45c0000a485150f00003440f071090307148080c185651b083e407003540402401d0804114171014550b020884014044c024128001e00d514454980d242e1071054500140c0300c40d2051207034942c00700c107440007000c800e034004042d81c00d10030448a218840041c010114482d41e44002401c00c26 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 561858147 1250 561856897 561856901
    0x5190c08030406020309041a03070806010810020a0f080408041205060420060429030103300203070204110d05090312130c18090606060201020d0e0a0302250522 70
    0x40c000d0315016506191500102a640e03000700e0703103e144150784505240016421400d000380351084000d00701c0300c8a07540c681d502d903200d01c401c1c0034080050255a140b00140c101c54001c071664030389a40d64114003000c1007041158526005003045070300b40005c2100040c290943e02c501801a801070700a058907040c0340c6003284801d4040c041810209001650341d200c2652480b041d00e040b2040440700d60b035000c5028000e205810311015801801c600044008014000f0680d52600d811015400300d2a0701a1805050010901d100c8025401039004010207001800e113500301c01a0b00510320b034524148400d040c0c088050344c0b02122000348640c000710388003600c2140c0258a80e0130036182031003040780c0201c80e142c0405182160240080403d004041d054100d0744a0348850180c5800040070002d01d81c890400034040e6010807205040682803000c12507075071401054081600350b040d0010b240a0090f0303142460400f040724100c1d1181a00460b00007000c3d01c503002d00351410001d6150400e6a0035100d201941 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 561859397 1250 561858147 561858149
    0xc050c190f0e130f14011803020c121b0303070210031b03092105070b010303091a0301081b01050c030c010f1a01020d030f0b0a03110a0b03130609020d05190c 69
    0x1034145a074400d0108410f0351120b1840500d070007952a034041120303030500300414544012600c18a40c03030700b030f41150a00140c82d14103e28a10070b609565694185904210520715010100e0802c0d82210b0310004210641d0981d070001010040c00780ea04041c065000180780c40800104403000c03a803680390b004000c2908481c0c0e244140198242008040002c4e01e405501902600204066070707100038003a2105030150003a0f40d540f41c0c0c8280b0240c0c4940c1c6900e4010000d00b42c80c4988112039940720011014948a401624144c0703004800078100c011080490340c502d00500b40328981400300402584c200403074203000030010b0b00035503000400c469542030450340444284060b05c480c0200703d00303216490380ea03002c01e040f0401c4c019850045203940e04250383d0801031060008141d8042441807000007001503140800755074000441d021401e01d0781c2c0d6844880700303100c12502c5e0b110b003400141501d00050b0443e44104c04030b0780040c1c0880c5001455942e0a45000c51035409070f890428249020410031641d142000 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 561860647 1250 561859397 561859409
    0x16080309030a2a120c021320070b061e030a0629100f030b0406081b060a080711010f020d0203150102072105100203180d09050d02010c050c190f 63
    0x400d0b0b43c8041101449403a402891541100201620740d44694114080303250020301850101500101000c01030032828a0040c1120407034001d140740001400590700243d42041c03a0a0795a42d0300c1080200880d140d644c1d15a8603404d00004402d03c0d10100000b031078092040d03200051018805d104000094240409510f90420544644125450b00d041c0700654003c00d040c4021800c21070403095014104180c1c400c2d070882c1c9015400507102d407000846000b20710855810213032030011321041c001a4810306040c1d10206401034003098a1500c03408540310741541c110000214411052500000c2e039201405021403d80c020003480321420201d120912030030000d00003070601c40c0c9003500800e10704c139601c0c014441c0c2041842254080c0102484000150030130000110f550349400c240445003800d54a11101c07252040074440301e071030781c040c07030841d404e6030030042000d0115142a801194a552a43d204031414019910340c6022911000031120141100440910845042031482e002e0007106910007 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 561861897 1250 561860647 561860687
    0x30304030c0e09071a0a1b1e030c050d1e02071401030b030705040e0307150b010519051902071d01050901090c0c0f03050304020906090f060616080309030a 68
    0x1003000980407a4418202c504010981d40c9599503610501d08080040d449240380303005440c0729110b0002c40d20000c1c030072455681c89059207540d4098080081c40200c080003000c07034850f45103208040008120f0000c1d16842454180c2c0000c025588050030000c68040910100e5869a400c00020583c178a06010038407061009280716850841840b4695003070107040e82c18103682e244070102907201808103401909000d030050160302031000b00150340341d00041090703400808a01d07511a06003520b025004040350143d440310300340b501e4284280e030480000c078048000c4c403000304443e400d490031403046100c482c64a6005000321602d049050030003c1c0702501c3c02145030004900600550741c40101443c107450001000052120510300252000195004060441c0c4007514000307040550000065100350320036151800c2e652600c909001400b8020354641e40152145000a4400e0601401520b8030746102282c8407944030468803603000c03d070b1054a00342000d400006071049843e030400c0c222019525140c0b49 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 561863147 1250 561861897 561861899
    0x40e210409050f092a21070611071505072306070314010e040302030c100606030f0b01020a020d05030d0c03020c0106080a08041203090b0406030b0406230d02063105030304 75
    0x10040c2c0303c0d117003800d088501e11100c1d201000100c2e10f941c00706882a00291495802c1d10011245289010800920075400e2040c07440c00703c0ca41e481181e01c00410302ca41ca0017802010305001160b65055544a030140800c101484810046200044400f8107140300842044071071008510050070000010f010805140c00e00c0450914080c0c0800f076141102c02600725444aa100c91508038103503c201c41c0b003c0894800d590512030100780300d030300240491741592000c00078110441a0310060728902d04406000d41c2110202001504108c07100d02009881a0107407840c01c0620310f2440c003155018114000003e5001c114250748502c00d1003003401504100005052840d8955203807650b81c17280e402040c1c00c4144001701001010b018000340c1014003d80c3e1621034855880e120010000d140b5440c41c1c3d4452410440c0c0052a10b1030000c800241940c940f8044d0302c0c0c6d940403000c0c00500441e645040f42c0112081050400c4003060390100c3c55071030040312030034800500c41c080001c01d03001581c1100388641c1007008 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 561864397 1250 561863147 561863161
    0x90c060301080d0e0303070615240f08090a0b0a091502040b040b0d180b070f0806090606160c060804020a060306050904060b01030e060405100c0518040e210409050f 72
    0x1030034140c3c03107499207080f02c465900c0c000868118003810900812507400c00103036001e00000c0242120075941c0740402504038480b084195500d1144000c070310303404242c0c05070140d14954403c00c481da500500c503030300b21800308615545102e0841c00485403402e0182e5140000e00c00c01400f90f61001590038455400d604080c00d11329503001d203104030301c0f482039a070800250241d4405c290381c1003508141c07080d10100c0d60a6006040005041d102140e0410000d11080100b08181e40192022401614064804000360741c81c141482402d6022403e0803a04a82889040c00041c035511b20500150049640c1c64640e420300e03105111003452690095003e01d070910805008039103581c0d81040e403041d084240403881d007034104010380051403405600300081c00b6240410091080005e59002d201040d540c08208880c000c200440d414000d15001070120121220803641e0b0745481d4220b84800030720f200580303008100490310842d40090321090301041d084041000c12812445219159100d4001c110b41580303490005 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 561865647 1250 561864397 561864403
    0x15030d051c180c0803090913030903140f0f0f0c0a030807170c060702150a0902060405060304050319030e06070309080702040507030e01020d060806010f050907050915070308090c06030108 82
    0x807141406956907210940d4890320100411002580240400c1049600d41c01e1040e1030f5030010785018000c1801d4004076855003061400715a280342c00d50f0300c0100c1c1c6421276403100750080c0000c101100c2d0348203c0b8a4040759a0080c0507a04599810400524a0340000d0700003131b090405011402e0300ca132810940410206140d0000c6038643c1e90b00100455003074401d4103602010f030142d00d81c540030601c1307054104040c540e000520035101605031048456150744d00d040d02d009540040d84000c1d00010144003c0045041c800040c40e003081c401c03402d82c0c0c28601d0000084402580002011000a0700e441881c070304a00240611904011076180500080c005030311180310038031418a0080c0a19500e80000c2d95403486940314940b50188040255551a14010560b01814080c0203405190040d5000040e00b0740000e09604101c550103017030103945541d402d000f80c400d50840b401c26508060707607000d4900103034004401021320606c41d4503801007508064860781e140000c050b5805006400400044c85040800 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 561866897 1250 561865647 561865687
    0xd020c010b0a080a330203010b07060501081603030c051c080709091a0d1505010f081002030601020a2a0303120f1509020702130f0203190c0905041a030615030d05 71
    0x1d01c0425490b8503500711642201000f04031500442407001c0008627800c1540001011714a009040511882c0d07250701c005a12003a1206481000d8110f8540800000b030080f1002c041550158040d5801401075100452994151590040008264401f00031485400c2003018004d0203241e002088240000714041000050082401e4402c0c0c00e02c600c0041041801c3c0901181c101030b80d00700748030a5030742c0d0300d900a031100140a59503043c024603107045019050351080c0d0b841800143e0003050040d480d03407100c2400621040101851529980968480e0403030340c085d07100118400d41d00e40c12602522075014023101c42c010300b0408501d04001d100214203182e6400c0c0b07810b507002e002005039261100d10000301003007a00e0010240312402c24540d41c0b0904074075030146109004421004460140382c0880100f115107a030f0280d40030458192043c00381e0b04081d48407034150713001c1c0d1a0790080e01054100207490640200d0b08040060090b9859505030b040601503002c0300710032401d10303609247d0104a0f801c0b02d0904 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 561868147 1250 561866897 561866933
    0xd090b0d020d0c02240f010b030405030d050106120501080a05070302010513080f0c0f060406121805011b09060f050f161a01080705010c020d0213020d020c010b0a080a 73
    0x1003516a4456a10390440da503411402d00308206480c101c040280d00d80d05402142e10900f020b80000c0c1d6402110060300511540404440d00e005a09000301540316400182003a12284820302c400052000a44a0540605030544410900000d542001000e40780f0503049410a40c0158141c80c00240740040c500e82540c0d42400e050fa00d07600281081807581100380d00407100da1042621189071b4410114805040d580f0176141030b050b0541001c00e00c081803107036104040020701c400c030500a01e540e56500060301c03800614203440043d1a181c4400742514505d180395045072100744600001c681d040b04800006060070705150075002030316007001e0800d00459840151140001641c8070326601008204d11a41d43d0082449842ca0440c00103207503100070900840605102e044d0000c24598024100b2040341c5030700a20706614687c041c0e0a100240c88a4103500c984e0507000d02c1118050b0000340003a01d00c0740c615000006210707502c50104002e05207954401c0e00541c105820450115803032140c55500348103 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 561869397 1250 561868147 561868169
    0x1f0f06171909080d150602100b0d0b01092418050919080309010b0a0b040504090f060608030a1209030e0909150c0307030b011701060f031107080403140d09 68
    0x1482012048482240500d01036400d45429103030000c0103d42c101400c030100d502d0400f000900d40e09403484907000c0742d500400300035a100c110a0707609404c40b908142c4ca008805400491818403ea0b5042c201d450280c1200d9507a640f2103040d12010a90030020440c904003a4600c038090340d103000400d40401c00103160514000b920740300003c08007142001804c0e000e14500120046085180c1410809034100b81d030b85d0fa90355402d01540c90301500c1d10400b0346043d01e000b1042245003d10340340800004000d90501251810140030424012803824428900200000d0010b141d0700c08400c10002c010a082140c07030400c09140c00c03042400300f548050200c0d028881601c0c861300689401e440d00d441c2c0031120040c804041500010081030080c0380014500400d001d803014050020000015584807400c100450042198840104000ea00c0b8035a01c1001007060b0400049072809032030386a80e203030f03c0002d050f515000c00060030000c00c02071402e412510100900500001070b81a0030007400d401140c45119600c00c = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 561870503 1106 561869397 561869401
    0x80403060c111209062803020a02010e1b040b010507050f0a021203120c03060a170f070f0f060c0809031005090616120e12031f0f0617 59
    0x11060610942032101c01810711035560805400006d8000740c1c8842c291080c01e0032009034078080b0703c56070096036030941c3c2c2c440642500c5c5100d540340105d50110011441e40e2280131454030040b50110b0300440c44280103c0101c8480c040e08902400500807683e01c0c40c8001c0000490400c00c03071003550140030b40350070300801946901920690750003580003403001500191111000b59880100201007640e000d03100c4030005400304190f00510603d41c41440c0c880030003c41080180001c0c06464440303013242c0c1c21b211442450111034824030052040703c04001e030410075901d0590300c03180300180850b14266031760141030f0054442a50500d8003070280801082c0c0400c420030150341c0b10714094580d08980302e03080034441e00a11202e0403940d102d000d10f841e440d9025071038900650180d280c81003010f80b10072020301c4c3c4059150042d071190241c46c003001c1c4104886900000c0303e0b1010740c03607140519169 = true := by decide +kernel

theorem cover : BRFrame.Cov 561690647 561870503 := by
  have h0 := BRFrame.cov_init 561690647
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561690647 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561690647 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561690647 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561690647 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561690647 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561690647 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561690647 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561690647 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561690647 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561690647 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561690647 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561690647 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561690647 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561690647 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561690647 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561690647 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561690647 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561690647 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561690647 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561690647 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561690647 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561690647 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561690647 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561690647 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561690647 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561690647 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561690647 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561690647 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561690647 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561690647 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561690647 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561690647 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561690647 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561690647 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561690647 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561690647 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561690647 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561690647 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561690647 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561690647 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561690647 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561690647 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561690647 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561690647 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561690647 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561690647 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561690647 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561690647 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561690647 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561690647 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561690647 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561690647 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561690647 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561690647 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561690647 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561690647 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561690647 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561690647 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561690647 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561690647 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561690647 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561690647 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561690647 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561690647 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561690647 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561690647 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561690647 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561690647 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561690647 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561690647 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561690647 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561690647 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561690647 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561690647 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561690647 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561690647 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561690647 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561690647 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561690647 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561690647 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561690647 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561690647 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561690647 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561690647 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561690647 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561690647 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561690647 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561690647 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561690647 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561690647 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561690647 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561690647 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561690647 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561690647 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561690647 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561690647 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561690647 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561690647 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561690647 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561690647 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561690647 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561690647 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561690647 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561690647 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561690647 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561690647 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561690647 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561690647 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561690647 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561690647 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561690647 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561690647 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561690647 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561690647 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561690647 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561690647 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561690647 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561690647 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561690647 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561690647 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561690647 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561690647 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561690647 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561690647 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561690647 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561690647 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561690647 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561690647 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561690647 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561690647 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561690647 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561690647 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561690647 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561690647 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561690647 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561690647 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561690647 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561690647 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561690647 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561690647 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561690647 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561690647 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561690647 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561690647 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 561690647 ≤ n) (h2 : n < 561870503) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
