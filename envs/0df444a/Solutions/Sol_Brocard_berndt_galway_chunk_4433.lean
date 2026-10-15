-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4433
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T12:36:03.525107+00:00
-- url     : https://prove2.me/submissions/904c2e2a-72e9-4d7d-ae58-19a802eb0cc4

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 797122302 ≤ n < 797302158 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 797123552 1250 797122302 797122321
    0xc07330c050304060509130b060d0914030406262511062502192a1203030b030a0b01051509032b0c0809130902040c0906020c030703050303040605 64
    0x590385540290540f901c0396580c40c00a070055200d0004140301d46450704900e44072070840d200d042000f4402500181c10030210803003800040000325001e543c25800030b10440d1030170a00704002c002034403241ea604503003031686a900002410f00c1d500c003400005005010000061040382540440808031203048192026100b01516400c080b94140b40346402800d003003002180c41c01c500104022040c00d110390b118455030904076182c40c03c5030187e04401d6100700c0c0010105680700450300031080c01c1250310074009841c082401c1300300b00c0c40d400450480300c3c0407007150505405200718808174500b030f400782040b66090368401c0105681406000c0c49001300310001c00c803e20034201901d410810140499614840310a141c0550f0603020b440440ea00301c4000c5e42d07290700780c81408100c502680c0204103604259202c0d04102d0356061803200365185940d90501c0c00301681d50f5004242c41d045850715410645418844005d04040d628080d080c040e90114404200040d0b0000c101d940c000c1d0803440008003500c5207040e0 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 797124802 1250 797123552 797123567
    0x507080d0c0201060303020c03012901090f08060618040f0212190506010905070f020d0e010318030e0310053c1e1003030507151e020c0733 61
    0x510036a4503010128108a80551220341980e0194088030494000c800404d8280c0b01c4440181c50f80303801182c1c1d185505140916034511602050400b04034290b100c9880303245094095109140f80d6103c0402d01220f81044101c0000c14181242810f06515003522002607080306050001e004980d05151902e00d241d0621803042e81d9020310603074030b4800d902400d000d03644440a00503042d81a15180c086411140140d4001048403003a801030701d80c60b9040d480c02d44024080c0080d0505250310345c0c80744000120b200b8001412507200307480f0100214141c0d0141481c01d080410300000441c540f00030303c0081d050600d00c00d512403001e809039400242100206d0742d44080700b1070410081049640034416071280c8250200e52601184d60084641da542200500c80388005200c09004500202322681c08261101285208613100c0200400c0780c0c800328403015206036148500344055940420700d20800705082c08540000e000309048a00071940103c080c8010460884803c403e4100981030070740c0300c5015060 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 797126052 1250 797124802 797124817
    0x3020f041d01060302150903120a17240406291306021c0806010e04020703020c0a0f06020d0203071e021201050a06051f0903030f140c0c0411040b030403050708 70
    0x44090358004041c52150180c030160000301e215078882290000081c46010540d41c0c0114000c004010b28949445001c005903c00c01b2014100181603006d610f000e003000368072900a041c034201c01c83d00601441203100c100b01c0400c0c20144070754113100080254a084002704004e09000107011144550760840360066407046c6003001402000e08000022202d4022450042403041e00c42005200981c056044481131002c80c2c0c180c1c00308194001c3c101d070f0341c105540a000e40911078011112000d4107031000130140c40d42503000032f0100030701c050240070300d0394144805070b280ca000340000c1d4185812030342c072035000f649007034400007140ac0b110012406555900c4108007594040800030411420201c00d040b002e04414007c05003e01d1b2200310000f6803580401507001c4103403041d580c40040301d003160784c11118a03502c0e403040001c108260104190352206407006041d061044d000400f0303000f0558041c441035032613440c0c05480c880030a020800c03018401c0c41c11079a005030716191050340e80c2804d14048402d03004002 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 797127302 1250 797126052 797126081
    0x6180302030708330106050d0609240602070b0d02070f0b07032708094006080609120a0909050f0a0f0209010906030e030f0c030a0801150903020f04 65
    0x4000143c4500115000400c44031200000c120035140081010300456861901032182003140010442c142c480e4000c0c141e01d00d0348490101d0810740d40c82d0b40c0310039900c00348510b4020b204003c0e02c054004031101240402071000d400901002032600c0702e0300020b401481110b07120f00790002541e208114106000c40d0107150311444464541c100b40e43c00800070700c3c5410001d80c1d002144107020803080c0010401a040d1540310901d1841d000c00038041c0b040c03529041c0e0144003007030f1030194001103180c258540900b02120010340640c941c1e20300034400d410b641c861345c09000d0b2604214180400200d000c01c2d140e46001c2c1c0c000e0980d6403078012074011a14143c4541c1b00d03161081c50541880501a111a00e040c0180006030007030013844035000e194822840b51820b1180031681c24103040280d18060b0704040b81c80c280c04020b8900300081940d481d02a60700c440100f1507650000610328000c01d0300400403e014010700c66001c2440c4a0000b0042d10b400402d0002a1003141003200c0704942ea40c681e04403031460f01400 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 797128552 1250 797127302 797127313
    0x1e0d0f150204081e060402060d0b0a0801021602130c02030306011d030106061d0102061909080d09030201140108070b032e0f06021504080a081f06020606280618030203 73
    0x83c42215143e00040d0849007140401d51080c41112000080590180741c00070852881c2041c1415550024001c0c1e1418079048040000f0004a072802840508030140794510a02d94000c81c0f44100b103902c4900c0c401c10070400346080d141c0c00e000781d8000143c0342c2c081c1080c02d00241400020826441e40c1c9009401141c1c10b60a2080c04a20b540d4420320600e44030540e030003003078034409040e4010b903200c10085a42c03021a4114181c1a102c0118580018030034501440c40307985452480c52000c01901c401500650140c2c0d101e0b01807007a40300406400314014034030400076004c030078201f5030725031030a100150245159080994070707444c9540d14502c0c3c02050060b409030300200d0b640e503031700c1078400c601240c41481c000d4090340c08172003103c1e54008805031089600c504180d2506511070000e840080c00a00031000380c92550280700a10080740309840042c2c0042e80041005180c1241041045416801c1000300d2804108940420239804030448069032100c3c00c0468118202c410300c40003191031684040c2d03051041 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 797129802 1250 797128552 797128559
    0x1116030e030a1202030403120806010806010e0409050102070c031202060c12100b0c1b0a061e030b09010e04151b0804050f0a06050a06080106050604090c030617010b1e0d0f150204 78
    0x9001320b82c42360302510b08500f850401554241c0d4201c49035400b1800c01d100042241d0f02c20030f4000004080104000381b0b420079a11507908903040312000b241e40400045c0e05000740f001c1e84180503030408080c40206050f20b4000c0703001032507000340114001c0e00c5ea46040882c008502000701f400250803031004007a118402111016550031601211804064a6110743ca000d070030095240410f8500795200c1c8280d01c83d1868000c40780703103500c4640c507040555074141001d030307a507901d4400790003015030108241180c142400e1000d0020102003c8400261601c41c0c04543e10a5845c41c410b6601c0c3c0a04141d1881c1d511401c0542c01c0c0003881d000c0d110705004540055081203d6039009502403030700510701f0081b01d912030b06a0b0303080300c0c41400340660001b814001008114403a03080402c440207072340b8001c03604541d0b5001064400c10740d05016103d1340d4461000c85c9160074818072506013400c00b5410303c0f414004031404100c0300e0030404406086c01d140048500e051285100342c00c0070705034121000710340d110f64 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 797131052 1250 797129802 797129807
    0x2c030904050a18021512100905010902130e06121212010e040c23060a0e1c11061614060103050d0504081f090b0c0d1116030e030a12 58
    0x11a4400e106928000124507041098850440d42d40d1412a540c543c082d02d5808000160900b0507580000210401189140030b42400c4400e01604541c00c5016030719080c00b05001c10b9580c16000108547d00c107101c00079204005501490407181c03004511036003a1900c101003901125082100003042c840e030a401c08800102d00018054090f07a02c2c1c00500e0b0f42d1700c400301c1e064140000d6401038814400808103104650b802c509650080050210030b99004048002141580e00310011010200340c040c001c01d116410f0103407400d400c41040b03482001c15407c4da55034015069500740b080d0360203a400401e0040e10500e0702181881281e81202400141060b0405c0d00c940d154000d02007120940240c503141c20149014000b0b1340d040c0d1340200083d01c07694680b50490325482042c100045059500e5400701d0001c2142c2210f00d5000d500e107148015922090b4041800c16541c072540420611202041007107003070300b64030744800d0800c1d90500c4c02c10614010180080d150100841020b4040002138421840264 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 797132302 1250 797131052 797131057
    0x30b09010b030907081c08060120060403030605040b010c240603060605010905060c150c040e0a0605010f14071713091a0d050a0b07090b0c0c2407062c03 67
    0x1120041204e0790551a000c0541d1202460605a4003500c22280d00300d668901841c3e100c1e900150603d003403e03245003041c5c0c0c04118407000b040d0450194000b40c1c280028148c0c5802440090300d42910305100c0803811600090080e02c1400c00502032080d0b00d880601d030018441c8145130f40c441c0c0e07030000307100d4144c903420302e88003c011520405000c0360080d81d001035541000c1050b0f0b40b0b51f807254000f0704044000c864100c940c0c000e0060041f2004a0108400304580c40c0d051082800381c4014000010000c0c180390003d0a101418105401400301240000a12000c100111243d4030b510800c02c2000000d4003410400700e02514a260010320102180450300d42001e512064110703014403000341c20440c0c080c060000320390012074003900c5c50b04105004000300e480f480940303410440a01e03000704450f0703441c0c0c2c42c07200d503400100e644000e03070f044941480054604000c50003445801005010301140c00000b500c5502e1084140080c6401c4e00e6242c0f1031b50110303203d040201c20074094048103d000c0c0085075050b49a5 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 797133552 1250 797132302 797132311
    0x3060409080f04180b030703020a0b0a090314030d0501050105090d03110a080a05180a150f02100e0705031c0221210717060603010504020714120309060a0203061c03030b09010b03 78
    0x214905170780d002003450f00260b003070226a0086c0003c14414200b075030010044d13112100500034031942c200300200165044c2071908234101b100c00510f07100c0f09207081c000306440c01a40414108141440314100b81d03503d45c400d0090107585424081c00003920708400070f00300034120b20040e2966802081c0692925080710082c0f426041d0039001c0310380d0100315010070168181c10b0142c200d5220081206003c00d5024221121100181d8011110441c01400114094580c5450500086e0b042282d0800c203905081000040301d440d281804042443c0c0300320000d60300d81d95070050701800e0300131161402448003200c08940890a00c101801c5092070300715002000700c1d0b425540035002449411104041000c0f0429440c02024000c102c0ba1459191178100006500042c40555506909401171242c02d5000c000d140800c020780502c0c13984071300d00414510f09044006003a500e0701801041046103658490070301860030050307480c07032000e0928a818120010001c040d00300f50451050400031881c201981d0185219 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 797134802 1250 797133552 797133599
    0x5010305071505161b0801021e03090d140f0d1e090b04080a0e0a2310020c060a03110310090b01020d080c0711030a0308151503060409080f04 62
    0x36650724212900300c80d0500280c000050420b04c08203013000c0900365055910340c01250412a1031612070b04120010503107a1182c200d5030f600040c42c0d640c0c003403071607004103c00c0e46840c0303d01c1c20341c98481c18050b02c410f91034a0590400c050403000b14109207000040c4c0b0802c41ea21040c0640700c40714158000020000281151031911500d00e02074100b9a0714080d0b001244c0d840a000b171410b0b101d41d9152071aa400070034081e000d01207001200607841d211345011000074940300140b03410020300c0c0280d21813a118070000343c80c0550340208056010039000240a041414150344040d914946002c1c00c4000381540b1002d0084101d0000a0010701e206580d0418103aa5202004001607640400160398581d0959000404141c00c840000c2159003c0300c09041283d000301d044010410340b0340d00080c2484203407001100440c042d4001e0085e10703105040c0020260400351810305641010442d00318040c00014801031040c0c0e16001010100024402a516043d07029004c0c10b498075200d060900c40400c2c0030821129 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 797136052 1250 797134802 797134813
    0x509040501020c10230610080a060915031a0108061305030906041203082d060319030512360a1709090c040f05060706060b0a030902090a09170d110d05010305 69
    0xd560303403e04000340262001408101600d4081d807040c0d0f00c10200070000070042e0380e00c12000410012034012003d20750380307133010844002e055203404c090b49403c83c100c00d0754040e8854010b001080d000114030307400c0b491403440c00441d0120381c034055145120305011a900b205020500042a0b0b9580c05180e00c118800c1c0c88660983d640d01030b40300b4a0140050320411942d01402c80103c07225174240003903402c4100a8240c0d00060798014500c10902503a42d421400280001103030a0308215913411940c015848101c030040305a14041d500c0c40c0281182c00c0e00d040c0074045030036806a004108214103002d54420300503502c541d52403103641d030180c1100a01c580665560301c002801808040101c400f03035491010744001060511040c480b05030450b00003220456a00c05002c22416007e5025190b80314880c1c0d400301d4009024030521101d550050022654070307060020903000907030034501400054500520980d2142040c0340e10b1405030480c80030010701c04a0028040b0440c542c6504501e050301c1c00350048a8 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 797137302 1250 797136052 797136101
    0x21503160e0102101a030303013b04110d0506090303010812030906070e01020f0f0d1214060103020d09020d050102070501061e09110f0c0c03250509040501020c10 71
    0x490404038070390081d0040e081251012142d220f180d0080410a0401c104454481101c50210746582d100380c00144d03480c881e0506106180881710b100f02d200010307810440c203040f059101035041010300544003d103440804401000d42d42c0b51407003d140010341081c100c5040e4100207a50075100ea0081c0035007036030390144c041c56040703001c0c02e4402c60780902e002000034985c5948800c0101c440c000c42c40a502d0450062180c40c4090030010000803244800c024050701e451090200b018140b8103410400003400b50402145082c0d0b40c00400825902100c2824056543c100d400d4004004009050b0b00030760144a8004a10501405501410605109800030029117448840380c0d4180400c00719000c080390718a080901c0030f0180364200d40c00500c01c160348d8078142151a034034140306401504508803103034899803803031015140401180001d01e240d07440082280c408042e200016031058020640190f21203000314082140c254121002914003078265850888840c0800c070243c0014140301291420140118 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 797138552 1250 797137302 797137307
    0x130e0105010e0f1005190206071211190216060c0b060a050d080c070306050726102112050304150c0503130303060e09071a03040305090d06060302150316 67
    0x2200c99100103140ea2038521004081005440d00c2d07410f501e04000c01801540c10355078031344203031400031b900d42d030060701c1030b46000030b402805a0380380703008039100354140261146241c200c1c03411260040c82220455030107a18a0b0f01c16407404010b0070500c0d00c5c00c4d2011400048403641301c040e12140d02d10500d0034001710380381e4a04110a1544c58010668040c00c0410207100050310b01d00144440581031040c0c070400c80e542d0b11103004079181128600041142c2c0940b112103180400034606800068900c0400c20341400360103602e071909103000341d00814107909000003030240c403426101c0400368070003000c4002409028000302079070000d0360111034480405a01c5900440e40d0b00a1045142c050798030141996152140310813100d8105c903054007815950300001c19a43e40c4205030b04c6c4682c148400800001e89020803040214810450442100c0b40030b2040c080000d901c1400c99201d418100c4c1d40340514540c50030800f0080c550340e84000c1d805800700d034203040c2105008000d148202c07420500c5000d41c0b200705005 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 797139802 1250 797138552 797138567
    0x905030102090315180102030106050d18200102031e04061d01080408030a09050d02030a120504020a030204050718090b0907020604031e02030702040f050103050105100b2508130e010501 81
    0x740c59054010110004d418500301c1100340d48041281c20b10085040c00c0a40142240d2003a00601c00061002420320000c0209000302e03450801d1200c41c00c030721842d840d1209060110a81c070801c94034101e0031100801a1310030010b0300e2000c0e4030815201603100c20400503071003680c880d1140002141c00800381e40c840603048014100c520704117031540a1550703180d50310011b071544014055038000c0d544103c11408600d0810240317600b00e500350011076540b0301300c0c41301600e000e0210a64070551420802007000613181c0110640489138103a80c08a5541c0720010141c400007492185428100c1da4440001010440350700030702e03142981910003042580325450100c5c0c0729042114080c4c003290320240207044030144011b20010b9100107206480c28605141c0c001810b036911001d000c031040740c035100103005006003881100e80080704400c051903030b14907104806031107024642c140122288041d10f9a00d46007101c54200000039804003201d951004000a88145940e16020340303400c005022001059650081e0750 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 797141052 1250 797139802 797139817
    0xe060d0c141c021e0703200a02010c1209120f0c0b1219020f1c0c05030106021b0120060a0501081204210b2403030310150c0506090d0905030102 63
    0x2000203014594000460195104c10003c64138282072040000101072004003401c01e580c402c0e9649400c4406180800240012440e40101160011810b03040140e0b00b02203500d0105034410031458070600000e0f400d039900d005950000040c0403100054200304064142000b034440d10400f0303404506c1c2c0c4c554507644010302a812404c6510b140030008a07a000c20382c6008200c500c1140301000d481e1180580b203904058000c840f104010b11261703080000c44403100e000d500e030040b1144ca0594210340c0345c07a40c0207540c0c00c10344c2c0c3c0410700d01034040d440c108164854410340c0100424024240807058900c1c0c900c59440300122160b0307120910308800810b82c42004a0104010040b10720f10070700307150505603849000c16941110081c41c4401c403060000058981c02c0c40d80c403402200c20100d0340c1544041412144402070350116119030410010001e40440202d041c0080e0341c1010303c004429141c9000c1543c40281071000689148950410042c44600c00a4201226121a61400113056035a82814241e025441 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 797142302 1250 797141052 797141077
    0xc07030c0201081009110a1d0a06140d09031d0306061011071505091509090a05040201030e15010611030301121b09060e06040c0c0506040b070e060d0c14 67
    0x544090341c85401c3d61608558149a040400395840e00c0c84030071200d56980643d6009404a0752241003600441d8181d400c207003941c00c162840c0c401100040d200d007614090001482001c603403243c20f4081801c01c0e82c140c2d001410040101880c0c908015007041c0c07030314108051a414196051031907050205005003d00030242010f0210070110342c00b17884191114501405a1180940001784144581c0c02241a143c0d01d0300e606980e420102d081c0032154140c0c4050381000203040011440e0398545007203060303000c1c00c001e8000625031501e2004801409010302c102d03140d40301701d0070b00c001c8541d58118805d0480350103840360449003042d40b203030320b40368002481460780180c4440140c1d4089824055902d036a883c80c0180c05e0407454560180c0012645260024102c0c1d01842003001014200f0340303d111134409550420110114003076683d10b5030366000400040c9409080c83c08241103034000c14034138409000082416444180d441d00c14001000c050401d800003a20b03080d4425003040340b40301140c0d41075003441d = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 797143552 1250 797142302 797142317
    0x1a04020c070e131e0b1f06050a0306080d030506090603072111030d0c050c1f0f02010209121f020f16020109090e0c1f02070504050c12040b0901050c0703 67
    0x7080342c0510300000c00701464103500d03c0c030642c0000e8000c001e11001c2200405007024045550510869880c0010141c901212101c45009000000c01d0f401404403034452800c90344e900300304082100584041c2d070051010f84210403240078169010780020f4841c240c15980e5042582c2d1380020035640f0982c0b4800c6500d00e64440341d2080d0400c1940c00100d82c0c06000da000100100311035004207117000043c8c0c4410b00003808110100381040002e001041405400301c0c0c1c0c5140013480024007034840f070704004015091000308160080340c54000c0d01940c01e2158010000c40c5490b0440e05400c2e15581d0b038461480d0080844510040030b80000c8c401c0d40c440c00700c581e80e000c1c01c0141185214194090103a8240c1c140309a010002800484074003034014000841d2001d0b110030011542400303050154400341c4124625009a0805126400141c1c1c4080358402c03a000f00c3c035070702c840c4081c0c001e5100e80d100b080f81c0c4500d00350400c000c2c404c100d4401405040c10341e0080081e603030b40c040320100e1030284605c01000150030 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 797144802 1250 797143552 797143559
    0x50114040f060b030708090c0102010b09060d060f0203090a14031e0a0c0f080a0f0905060a0513080d030c1b020603060409030519080613050910020c150403031a04020c07 74
    0x168040c0758088020140020030a44035600041550000c86405002032081030810000c400180b10300e505813076080c0028449903003510001075190344000c059a006030056050f0b4020b01071903400040c002030001d070b011513607030a00c45015611040d1900d4103850741d20448214000c001070000859019110808003004201c8144603807242c1580120301c1d960800802c800e880012442404100c445a031158100b2603548601040203011900403608003818015450810802c6443e81d004403810040c45290490b520f040014462100d0042508450750520a100c0390116075a010360100c4d8007110552203d80654519540e81d2160345aa090002d4000e41d0600c003184203810150001c4490a100c4d081c603504080ca2001d0b50f041c01c40940840304001644c04007440500d0400800307580d01c5428030403040c0401d00d4022004c40d0f0b1400600485d00085900040c0c003064110144400340240f804804880810305050400502403e690940c19041c0b1601649440c498501442118822540500500a800c1c034 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 797146052 1250 797144802 797144809
    0xc122012040324060e0114030316030806180915011205101107060e1c030c050316140a02010b0406050105040608040204051906180e0106080a11010909060603020306010210050114 78
    0x30250740c8100c3c5201d80400120100700b441c0a101d01a080100b22001507600d08203000511641464416009400c108603103080100b40b140034155003074050909200980722000400d1140340103280741040e005c40c06080c8180d070710011505100052007500448441d9817a070043c8004402440c200030071552000c400e210010b415900140b00300031200341000d050a00b0703a01c0d10425101c12062144082e007000c80381404100b124100405d40c210f2500d0100030ba8080800003401c54803003d00103211004229800541c90b078030130342d0040e403a0301c03005044a440f030301c80185c060301034101c45241c18031440c14500003094039441a026542143c2c4959600203a94555409000017003c02406249604605205c01182c80c1c0c103a019031300042c00804008401164500046d07401c42c0c510052020059040c10410407a0364000244d22007060380107a0001b9000c09280b005a1380b803141a44190800703403d001d000034540d03030940c0c0035600c03981d000e80070307141e2030107500c08044c04440d02400780505403030313003c1c100c00303560309 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 797147302 1250 797146052 797146073
    0xb0a0e04050114010306140705030105150708071209060201271e170904270b0a020d050a050105100207150f0309020301020c0105041b050a030204020a0c1220120403 72
    0xe0181d4000521070807503061a12080c2004d8100780c90103030b00d8080b80d00c05500454070713099101d605441e00d00c2c07c55042c80d000807030345901124464002c0380049500d6051204070811200e00b0341e1310265412040301071200c00b41410b84248189405546449480507051184011700c031403e5408192064100c030300e41ea208141c03d07030241c0d074058140c080d0120050009101c03c00c41c051140c0038440454503500030104100a803488a140b040c1045286580c036845100d1603c24400c0807580b00b1104071655503160b00c254020301449408040719030415042c802c0c221040d9101c2810780340c081da103840d10450005002e07641da00e014070ad103480c0c085080c082d14069910030060443c22100f14078002c1800300003600001d09a0b00013030481c0416035035450a00c01000250085c038140c0741c00d040505851a450000020381a803140e100c0039005680008031504428881ca058427017441d0302c1400001c15510824002340051051144001401001c0d031164440c0000000d0450000151000e40c40c5064116910440b101 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 797148552 1250 797147302 797147311
    0xa0b04030c0c0b1909120816080f0316020f150903070512090a081504030807030209030609071809050c120724020c010509060d09020f0301090b100602010b0a0e 70
    0x40241c0d031601c00070766002c0000004003100402c96440d808000300245410484014079000d100582500300081204264005c01b9a504801d1442d00d03605640498854801c140b10300402010700004d0182e043d02c0c95001450140d2585928031a0048012030160383c0d516031440128100e07404101004552400e4102d150740c4840504d0563742040c001c0c0c0d4a00e072400c140c14810301002613004c5040192400c22012100c020403103540102207644500c800ca00c883c600140002d010050550300082c9118000e4044030000c180190481d9100e1511030481070726030340240180407117650302100c03140f02030505000340c10341a504040501a0700c58028200411400251600b4100340500500040e2518400c540048044d0012145034a10100d08038028103211030104000d05000d014481c00d9070341e480301003d4500c2501612030000b41d00200740006084da80030042c00c0741d855800c190700d54003004540c4c010304e8002c80802440e81d00d1a0340310030303041c0d0136100b046c81300d03d4101e0070413081040302150203003489811 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 797149802 1250 797148552 797148557
    0xb042309010b06070b01080d0c0312051f0602030a082a030604180302060106110a0b0a150902130e010504051b0f0c0a03050c101505040b010e040c03200c0a0b0403 71
    0x350000101103216034100792001c1d05e41440c48001006180c809100c1d00107501818074000c58601515500a040b1610040c4100015a034071340c001610500c010703450200400380481c1070004960345d20300003540c0750f001113100800603a06e000865072601c00d9665250142c861740e2007079500c5000320b00c0700a820b900028100d940c841d889450012103000707680103240200303020798060125981003800c081c100080e0104200070941c0904044404a20300460f0141c20103c0c41e440406c4541040580d03100354040342e0024540c1d2031000a580010400c05c1e00e084040303421101c1c851003d680e8071001c1004603401110101d088020b00d1403401e4650303903450001c2511000200259041000d03040400c0d14005901e00c0880102e2400900000114400c01c801c214a400c90130041c0701200d45680c008854003418070031580521384940841c241c9030700811800c1103511025000b04429407070124020003030402d060480301d00da801c0c0302c07a00360300c013507488219010600040002e04030800c6e03c0d5500e2030780320b0004206904 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 797151052 1250 797149802 797149811
    0xb0a0b091e091008061b03070c051c0e01020d050c070b072f130903092115050a110708070f08090402030f04050105010501020706082e0303020a05010b04230901 70
    0xd1660ba5409041c0207000c4030010144050030034805514202010b0f050007281c14019090201c000d540000b00c070340c86103a914080c4040d00040c503116240c4480000c2d40c4070841c074070041e40c8100640c4100140c001600903401c403002014550b0301541d8a200d8000c84600c6030304040002d00500e40c52000074054640f0422001c190708021342d081d034851400e654040100c61148904450755454250016084040801e5082203d94a541e501070311601c102e128109410026580c29010100c3c00d074134440e0640d800c13100440307040080c188000003c14044400c03000246c50803c1c80f049a40340c80080e1001183e2004035546400c04980714924400a1420b007111101c5040004d0700080e21280055070007400050416100d03421b151800368251441604842e046500007d01042a83d034003000d1a5003007010b0115034201152001c0c2d0740b420715400c0320000380048800300300010400d0f50003d401003016000318006c2014000010812054400307a06092041d004030394402c10788500010382d0243c021406100008 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 797152302 1250 797151052 797151109
    0xa05070f050309030115080d0e040e0d080f0112080d0f1104090b010905060a09060302070f1b06030e060c07031b02091302040b060c1f060503100f0b0a0b09 68
    0x4910403840101207400d40c20100c1c0c00610303810240203003c0680b030300c40349109810341840003540d80c841c00c9a4584d0700700195002c02150548076940302c10f104210345000d40c1e03542c901003040541800c105036480c1c21568203020001500c1100394001c00403071540000c2075440c0013403100070f4001500643c011040d00700d0752815500c00c07412002000380010403d1000128140e100329002512610441e0b10031400b40204003e6005103d41c030405640c1a204d250400580b14511030030840d40da1710070707444002e0083c43c0840816840e0343c0e10407a50383c00c07580036039000d00824540807501034032a4015103840800032418461040000e0252a10081170070b001701142642c03060507000125049410b0321548503049000c1e403503006504141c003802d0300b0f460055a04c0303441c00d03454019095480c02d500241400c200d070000c0c1d0703000030500316800c08002450000c00b1503000c1c802c800c0c2d03804010035490152411182c07510b517082c6440c1c142007000344226200d23034803880d0410352a0810700080d140e5402002b00d014840c410f962 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 797153552 1250 797152302 797152313
    0x60a03022115070315030b0c0d1506090513020c1902031c0503010503120418020304021305190b12070504020f0c100911010206040c051c021002100c0f0203040b0a0507 73
    0x40c1482c10004104240506040700054100c41c00e10510040a60205000f440402d070000304190f005000020001d944200d85880903004100001b4a60340c01c10720071a00060040e80000340b101541d6084898600342d100010215040303110341d081e0803d041e004444044a0006c03000c2d03e6203509400174061300c0701c400c0c034104030040003501e442000b0045000400140241d040400104000340301444c8034a03c2c190910500b20240100c40c1d449002454000000508548680e00206803081944100b404203041504641c040500c05520000c54140741010b120414038103809015541c1c031600c0302429140f404c0400340406584a18040f00007440304108802e245981000740d040024108032001800000500e0604031201182005904642c00801400041983c01861104032001200c00b09510305d0f0301c41c60651040480d43c406544040c4001c1b044a20326004600d40c94001000c8030100810020712000345d640b00482e03145000103900c10302041c8111031060000309050402ca0a1090501d1074643d910b = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 797154802 1250 797153552 797153563
    0x31101210209040b13061802070b06131107050a06050c04050d12050c0d020f0f0607051b121611060a0c0b130203070b0c0f010501050d03030f270218060a030221 70
    0xc0d451717180d9480307108100180c686110b00381d0010310301d20207514009250b1940b0061400c054110f0341708014030b058801d5103007490752018135401040403a50780c03550307404e00700f103510f814110505891290510000a40700c4614804990540700005c225240d802c02980707510046001442c14981442400c01c44800082d400300300c54000582c46500511a40c66141e40150a00b4100c484624151380050140030f10366800500307482082d0b114101044444010160281c5030051080c5154402038002498191200c8070465509010740134403d800040d01e0034600b0b01031280300e030500380d40c005882c191505000407002540250020200324000000b0002c64000070305008440e84401c01024000030595120342092103100c0740da442400003004990f16003008070b005543c011400604147e6642d641911000103980003054041018000041c002c81c3e103150011070251003c1c040e842003181c90742540101e80019a02da115500c054041c2240500d1642440440e0b040e0002c940f4030326404100716220500f08101 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 797156052 1250 797154802 797154829
    0x207032003071a07091e0b04060e1207030c050f04140702010b09220f140601030516050301060f0905090a08210609041a0705090a0f031101210209040b 66
    0x156903980707038501e0410f4103010b58078105060700c140d5604100110341c0014281e000c0704ca90b034400c045460301d0380d4070303803245140250088000161302140103d00d07194850142450306405035004018246160101943c52038a440020032409402c00b041c802e60402115800310710310043d0002c1144206a8180ca00400084400f5001030b952501c00c00000c0c0750030320f8600c1d0400a02400c860446107a0503d00c00f0310b80b80c1d2032018044074040d0308118104592400c0c01a01004500150365507075860346402da4480315840051501d205135042e01240c2890180700d03032402c41d1400000040d501e464001c1031405460000d00030740560140f542d5400c0801c000704028540d02841110300c802c0d5600781b098030101ca04c000b40646009001d110104400070b00707440c030009090107560122003130380d660790041180c080c0708d0380c09181d810040a0600188107006001c80905892003005032060b00321460b401180c2840310515600c2c0c00d040020310408440e20640c2c02001d10046c081c0c0082641c1415034007180c0d807801c4940 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 797157302 1250 797156052 797156117
    0x18060f08160e01030309060f1b0311010515090115090b0708031b0f030402012a05010e0d03021c09110402030906090105011505090906030708070e0f0601031509020703 73
    0x40c01040141d08580084025210002040301c155046460040c0021820b000300800c0c0306403440503000c514000c40c00c15010134030320300301000b10900754a002000c001184c0c3d88003c1960815012072118102d0002c0b90700c1c0008050100040c50307203040c884030074000c1d410100006101001c0e102169810359031b8010f1200500480095a903800c05100f0401201c101d80300501d00520b0a000781240b26082a0031250415024078184241050040c0f441c4520080149034054008103c500c0c0010841c040d0460140c40385000282c4500300c83c070400a800340d115040d00807038000c0c50241d0b02801000154025103045009002e803200c01c884000202d012a0303c16102a20940d01182c100546c95200f40507032405040211113048000305400d10141050207500c031810311401d0314000003241c94034100a140c000307040c00011200b480d5a14560450340440c00e80300381070b40c5580c5000044165009020b48000759241100c05c0300303441d18001c0504001e40100004904004039013001c1d498203441d0501200602e04900c = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 797158552 1250 797157302 797157313
    0xc0408120f1b1c03020a090303391a0106050a0f170703062904090b0d0b15010215090a0830011814060907120903080402011101090c18060f08 62
    0xd11101c1124003c8890030400c160041009420155111385002e04613581410a24406140442d020f0108c200014241c2c00c4400c0080c10f000c40d0301d010070352400000340509014103280391000b0700d0400008007400341d03d021900410031180c2c40c038410720003a8090b8541e841e080e002045140300030b001c81e4a0542e0030f00300007a10340f2005d11440c3c0e43c0002c4250380c0d04d400b00c051800600c3c071125010541c0114854211407030307540c0d01d4170350316034032403806900b1060b502c1780460340e031454030500c03448481c1c604028444c0180701e081c00d134940300040840081d000ea04290b0061200c0362041e43d400c0b4242d40607604a01840c11108200c4601e020750740d13060003c0710312008050f10310b5818001521444900d49002d9503206d4204180f0990380c24000d8035494002505446000907036940031011394041042025034441e05185c50f40c85414990311890990040e8401d903248a03042650318146402c0e504001c4014045c0d1082c00c40801500800d0040460800d286c0d00001c150503569451310744050400c2c1e030003000d040c4c208 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 797159802 1250 797158552 797158573
    0x10e03030f150f0105160b040c030b07080f0f06180406061502030f1209070f090c0306060c0203060f10150306210506070503250c0b0c0408120f1b 64
    0x155801990300040c0801d0034000c03005100e0024480c0744800d00f501d8140007001074140a0341c07081100828400717070490b516545a040c00c0c944007040462503c01680c45420302c902240d501d51140290b18040c8005002c41c10741511003040a0b00d40c5040501034aa1284101860409245100c0d02852240340150300001e04c552802062410042040f200c000440d0420440a200801c080b0280c80b03150114070000307c03607591030b1051646005815003001c1092038140d44002200b0007a600011580a402e60b810320603203036170f401c041e94030a29040e0000d5048c0c00c030200107aa00003650380399940c0b11050419500e4525622500b1240c480c0c02c140c0c00ba03002903115032003400341e642c8410040b444e41d0700180300c4014602c1c1507120030341c07660005030140041201c000040791006044901c0c0c50f481c0e560410840407000e07080c840c0a00b5420030024111b44505031000084d6070300c00e401e01914121044d25001e040151250189c0105035402090b55120300c3c0300c1407003408240620300b0304044080c0000001007500c405e0 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 797161052 1250 797159802 797159821
    0x1e10051503160e010203040909050f030c07060e0603060a030210021e0a02090609070c0b130510020c01150b09040e0a0b040b04021207061d031c020115050d0209011a0705010e0303 78
    0x342c00c1081014495002e505a050742d07070000444048941441c0f001420f14401c5c502542440c0700c01c00704161620020800d0b500742e680c0800d5202c01c0720070035103903009900c03140400d1005500080ba50346511461b24281003000d0708140061103120826403050300c482440c0c44c2480b41e06180f0b000040000d80d80f05140b41411401c2001c41e6540001c011601d560b0589045e40e03008114981002004008140e004007190b00300700c0b0300040b0742c0c0c6550b000e020740304503d220302d590307000a4004480b07000403036007000e0b113422010000c0102c04003070380c040008891800e04a00144805420115861556449000d0a0310702107443d4907240c030301491040700c00d03540509141c01001006100800f580038181c1155004002803a004413101010404024003208501d0914000905244d299010000c841403049890403c65a065100f411904900095468102d4981052020101d201c01000750400301c0304005000402143d103940c50580b2180361890b20b401d90a6031146d00703440e115002014550302c0030060005042 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 797162302 1250 797161052 797161081
    0x2304140603010c030204050d021207030503030a0504120816141209030d0e030c0307020d030e090405070509070e0607020603130507030503070314030721020c1e070e1e10051503 77
    0x507052405504090918002810302d0400c140b002b0b2003000032440704c243d11001480040300558102059030780700e25049441c4000b40c07500f218202c80c410340e00c03420b8550440c01140e120340160b81900c0c507030301c01d903503070080030390b080780c05101e020500240a2140700c03c1448102d101c0c82c03042d10907002841d1503141500100c410354460075100100c1c0e801c2485500840c020001c26681102e404132400750801100e82400d9411802c00300495411030700030001c01050050004005c012114103a8007010107588031041110320400a50107203500020400005000d481c05401560300309050988100c1c060841e56151490f0004550007102c0035000454050281a08070b0302400f55907070002d403010b2451a1160b001412000342d68000984000c108803a1a00d911140e4140c61400010100322860703a401000c1007264440d1104214503548960480490a0b2800d1860b07280500c01c9140d036000079088603440310942010060003410f420b0161000020a03a4490054405a2040f031310341581e0f90034901e0003510002c = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 797163552 1250 797162302 797162321
    0xc01020715020a080a0c033801020d0215102607060512042003030a030e1c08160309020604060e0f120c19170c031005070207230414060301 61
    0x10780c030520910800b903030011200c40c1d0102c20074a0015000132030701800d4006201080ca2664010900310001e401010482601d040f11200501a818070714081c8004907030701c0600741d1242d801600500014450080c840d9141c58001c42d900c9107450407291202c607410000d03545847c0555080b04a00300c032036180c1505200b010082c1400d854500d1600c8800300c3d46c015040009800100440c04c9008501d2028a040c1c4000f80d480c0c9004040d81daa0f8020010001c01508442009600501680d410f0885104c90101c0340142384002d0303140c0c8100e170740e5840c1803c90005000c0201c041803545400100c00140e0300e410003031014010945030b1110009408081c880f103c1c020900c05405003c3d14160403030040400100d001608100300c454000c0007000b8140019a205164020341c00c0d220100c00b0f403000c00c280401d05603010302e0190100d894503070100c0700b000251007090b00d181c005030700204424494441d403184006459101c1940e01030010505d070703021408079621140340c0309d06210300c0024002c15160a00444010 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 797164802 1250 797163552 797163593
    0xd1b08010912141c05060f09100623030103150c0203070209060418020a0306020d05160e01080403050408100b0109120c090504050c0a060201020a0806180613110c010207 74
    0x140706956541d0001d020560412405109440e10741e801d02096110803161860202110610511101ca540340301503c2c003a25094882e140c803809280b5141844ca0b1180d00c55188640c01075866482c2030000d842d203210030a44103142020b40d200e60031000480400843c02980300e40d800c0c0c010a040c4141c50012140880701000c11900100034000142c2d0b81c8840c0250420001c890000354141d03000030101b02003001c1c3c00025001000040c000044c000140c0c0500148014003100b409903582d00200d00001c04c1c0850400400300e03c1c4540400c155510903113900d0342c0103201c1c0c1002490503480704025440e0020601448941644a00d50900d555a0140d880d400507e10301d11100404003035030b07490302843c03d510701550301642d42c0c580004051080800030900c8821000d0070360032590351103000080c043d521200743e12000c28001c0010800b41c2c241484a034180e00700c14110703411192591301c1007103949c0d0a862261000d56494139100110030f840c0d040101a00d04100d4001a61101e56141002ca21a042c2101864 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 797166052 1250 797164802 797164811
    0x1206060c02030312070509100c120302091302070f20011806050f07051e280c12020102100c0e010801080708060115212f0a0e010e0d1b0801 61
    0x603100002544e050301c040d030030500f02558800308101c41c0c5000c1d940c90310b0741c4540e09441250086810150f050560742c010f5041140d11442c441080c0d00342d01c200b1007860f801880c071001340c040300c2c110359001e4804184115004007403440180c070b4590100c19401001015020641c2560301d0b65a080644000680100c404201c550762800d030300648203026141103480d4502c0002038400803c40180004500d011540303400310411081e40010395a501921124031034420520480c2f0b102815294404a012035070151000703111505100002c9403500ea545001c9042d07210300140b101150540b8020544c14400380d03074681c0c0b8441c1e4450001800b03020f060740031030b0454000650500c113054020902a042d107084040c1c0803000c8900f49011603003482810801c42d407044250728000107003a0a9040846041205c3c44040d40c07079070107042420081c505250b603640c0e9040003008000865405142c2100c3d04803414108808400350000100b44c0b803250000c0c0481d0508220703c3c40042c000c6910000300f0150001100811 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 797167302 1250 797166052 797166077
    0x60601050901140f040608011502010b0f2107230406080d050a0507060501080a1a071d0d0f150612050705210f0f0c0d020105070809041803120606 64
    0x8200c0d1180502450401481c4025929101400c0e8200c4041c2d1000d40225070341d40d0340c0e40f480201000000e0098844200c0606c0380050914414081e8214051307008041e1089071882c0c0040005840d20140c40008440c0c00d01e4600c400c0281c10302082e0014003009401280c1440d1680400c4204000708054901c55880c00030288424440020ba041c24040b503400c0c0959262aaa6010389441c0220440201814146000891800d6003c03a10102e01e1f03208a540310320400c10300d00444100c40c0d003294007900040d403840b600e101904c90000200c6072114007504507600f8599136160350480220b50481a208604604440e421580f000c0c802c100040001003490032145605982d40fa071a0010361282520036114002d400c264810228025201c0800c0c44080b2004401146951512002114035048041c05001c0d002c080504150303c00c220f1285e03050b5500c0c0c0ca1704181e652040c90f180c10414085030801d560b0b1600300b00b0141d6a1404010060207038032142025a50107200307405640c403581110041014405d002d4 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 797168552 1250 797167302 797167307
    0x606050c100c1413030302070b0c030313060204080a110f0a0f090203060f0a080604020316060c0602160503070b1909110418021504060809070b0a111006030c090e060601 74
    0x91051149001c07000c240c2c141c0998003201c010018004403084440d0024040c00c3c4242e10725440411648a038003030340d550035591140321410f4010003e140426400820006600740c01302840850400d01c41d2000500341358449020510b8042070103021523080144512098503443d100d103200c468800d080f03485818036400e1048004042131540f0480e01c4854020011503101c3c0c0e5013011109881c80080e000c600802d0350351240740d95850064500368064040c121540c1045a6590118021703102562a405003410064cc0c07200000c2d0b000744190042c81181c15424800550184001e0004c2406000444c02e2800c02140d0310006034140c081c4603420038a0318800c640010200c03200a9110082141c000404e44610b106951150f560510000c1d030182d54030f100105400380c49405082612516502c4200950f03e00c10007555a5070f65002e0303100400020301003070200340d100f481034400d00c1c80300d80c0c00e94000e0360328030200d030040c1e4000da04121400007007404184112403403071003442c0c000302070b11008010340c1c10300c031001 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 797169802 1250 797168552 797168563
    0x9040b0f0307051e04050a020307031508120f0d020417160302011b0615090218190512120d02040303030c03021c1107021c030305010b0f0d0b0112020a020a060606050c 73
    0x1004e0190750041c4842d0316804a4002288418601070400d120134600846114020b42c403c69043c4003191515042d10f0120054100c236034140c1d28030701c00400040403846100101c0c1d0f0450664003d07424803c20810140ad561070002d48004d01c1c079000d00100c800010001c660070280c4800c84485d44a10020041002d41c0c1c1c09040342c1e00c5480c40b074460303260105203410120080c046440500e8100d0032400340004040710f46a0061980c4402d4086900722480402d0400000004d032521984a83e01c10718410b101900d1315200b242c001d1001c40e001c55052002110050026030800d05440c07200c1c590104040080c950140541c44520b8003610f003c5280000d040e0064401c191601200e142c850740c1e030302ea140218003440301204d24407a0024289620000403000071840c90320700c5001100080e062800005440191405485013407a410f4051814624210002801842090401810401440709030010050b1a10007040303998180c1c1d0203007030000705a003005010354600364400c400f04141001a0110342501140 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 797171052 1250 797169802 797169809
    0x91202150705030402010c060513022704142503030f0519120e1204030c0f080d12090b0406091a0709050409020f22060b03040f0320030a0509040b0f0307 67
    0x10b05980b80d80b81c40c00121003180020100514062401e4180460001c400b4402510701e8400c40309a81400c444900e6030700701e00700048c20400607500d86030105000586004001c840a40100100d80d0f100c0b5080030002034002c0841041c62940300d1085040c0b0078158021007014075841282041c41c5400b04c5480280e1800741c695084104100d001c003c5104600101e400628000d214041202c400c610501c900e120554818442160102c5041c00d00013a8034054101c9601241c4441e0050000082d213040c0581e19118901c078413803a4603550b442580c0015880e5003006024030300548000581c04081e02c1c000350800c0c4103010200d01502c1560804c0400781d0322080e404207545082d9004100756150388041910a03007811122a03100281890b0501150ba8541d6141c030364002c08841030100560350000c0900e1803009650103880882003004d0034010900500ca1070b180c0110840d9224001d0300c00000d4a42507402030fa198030009440050b0b1000e40e840e1600411906034030440d072800c0c50110440000c1d545803a82d10 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 797172302 1250 797171052 797171057
    0xf010809010e010213060905030f030313060605030a0b0609060312190306090603060905191502092103040618050a0303030b030a06021c050f13061d030d0912021507 72
    0x4001640c0200290030140305944468000d42d100c00c1e001c0500d00048189016032000100034400c000355074a800a01001d0200c0348201451541c0c13100050342c800e0740024213050300c19548544c40011a42c4041210101581c0603003643c400306c0c01c01104020403079401178002c41c401c2c0c1c08822000005240380c001c445410744a5070361000c0440c10702d1001e5010f4031030b941c440100146482000400d02c41240c00a0101c3c910a0040e541d42411029004440e40f00c45000540081c50410b05003000050341d5005013102d00c1c0003069517004920580c001d441c40c0c032404200c0070b803642001c1001c001d20754000e070510701c6650402507048425030804011942c0003071503100140426456031001c10882d14280303e0f816a850304070109540e43e440402e070340b00740c04d40b001c41039100041ca400b0000304000e44020105001d00207103000300c0394030a403940314076000e0456108560606007442110150034802000103102e50202010702245860603410202c40d06041615a01c0541d08041c00715068403031100c80c011390281450 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 797173552 1250 797172302 797172317
    0xf0809010e01140609100e0c0f0403062a05120a02070c0e01030804030b0708130b10050d151a0603012306030a0f05061005042913030308090106050f01 66
    0x88108a014181d030340c0c110701c469481c00d01c00020000b08416110710901c030594102c4c0c03d80d10307810004000103002d413051488070078402002c1411140507100504101e220443c4045c21306031a520b4010481e5014000c070354000c1100304021869031500b072000740ca04102c90900a061000b8a030508600b000000d040003007050b4002190010042c2410218014020030720004c1c0701d07507031a17281044d180c1d07005000540310100c030003002610040c45014840c0c03003580d0000300201603810350350b01e5a082c3c0301d024008140d2400304a202041c41d8942c1014069040e0060004842817200a1091404c45030101c4040210400450806282d600c4007401c6904488642603c40c0c40c51040540d601c038a00d500e080d800354840c00c0042440a92107450b00480c10924050608100c50b1320384200f000b14080007500d138800400e8080c0802c00070007039403006001c0c0151840710210000800e151030004a0703030041040040c94090b04a040c8207043d40440016804a0020002c20035141040c0016607684d5605101034100000c1 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 797174802 1250 797173552 797173561
    0xb010e0411150a0810090e100b090c0702010807270e0604050402060708031003080d06080d170c0a09080a0c060807180b090112050114030c1504120c0b0703020705040f0c0f08 76
    0x4004d2028020400e202c6c0800800c1d00701c081807501d480242400603c21400d00540301601d1420740c442c40e001d1100141c50314903000183e801503030b6400c40102044240f10f032002e1340240c41c00002d0030302c242c2c0b50508455560341600709030f01144e40c1d03c00a40a140543d291000300001a1900000c840560f900020000c0c0ca81c2d40740e4481a010f84a103410003040c101d004107640b0600442c030f400107816541c1c00f07400d40d0701c1928010000c5643e80c00703080740300c0b150500040c045000c01c08014010881e140c1c40c1d140030300265440c0d107000c900d800800901100c0e214114101000140d9111070764603080182c0349010055480300c00004081070341180501d80e90b10500040028150380190720044419045140c02d110a6a607582e100c02e0b01a154000907000b03010741d60400c9100d181108100300300c60030743e001c2c60341001d05110600c50310384000035003141c9482c4181c40100b00c24804e00041e00c0024445e40c020204203040c00b040c0000c0d00d021400910f602c0c0d0a010a0709509a04500d02e0203400c0b41c2841c0103015985c9 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 797176052 1250 797174802 797174821
    0x9090903031f1818050a110406140f010f112d060c040303080c0412050c0312070803040f020105160b0601090b0405060706200a0e030607020c030a0b130b010e0411150a08 74
    0x13408440102140b01d5240d19800700800048150601e2070f08450421150b6941e8160441d041d045200142d840303030715520707020100e41c00703102240d040342c201c0c0c503180c5162060a8042031501c030312031018207480d0110441c0c0c1c444440b00802558914140f80003e0300c206c2c181190803a48901503408001c041c000c140000460600420f01507400070650707094400000b1016050554503020a005150702900a06038010740301410102103424056000c140b99207140d581da01e0300b002e03000d9554030032410041d007000190190204050102d5880d07004900680c2c0741d0920704c00140c848000390f0b01240740500c090204000030ba0f0303603405540d043c0c1e400020218260f9402d8041c00100400d0500108006201040d10341c0b805a00c0f0100c890405803d9044130126114901d050b6660800320181950640c003c1c100e5a00140499644a4100203403441c2600e190442e0350300c0300000b01c000d03048514000200c00400081c889041c1d4950703400c010540f10200b030049510320107540c038403d01000005000700c08011600451 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 797177302 1250 797176052 797176091
    0x1b0d061e020f09090c130e060f10050d0b0307030c090b0a0f0605040812030c03071d0916020c010f1b08040816030b091207120509090903031f18 63
    0x4440c004219a00c20741124a2400d03074100d01c030031a001d200304a00264217440c14130115041030a4660441e11101e00c2c1440055810074000c140310340010500001c8811354880d460001c8080d03d454440760b4550764045424001c90f0080c03200b0300d110341e105507020404240204020001c0c1c40142e400401c5000b200c501141d07034030700340e940001d022000303503070780010102e92100240055a000005032010b0303020580301d00d4800d02054500b41a0f04a0410100c0d9816000d400d849080f42c4071888008100540e400001d1907540701101d010045020180003002c032582c1c184441803c5001c02d003030601d04865a680c00400081c100c00c086094401c1d0741c0818014444680207460081000e07601311007a202284828400360507291000700d600301707541404142086c80200b41c1d00c1c2c05008003076a060402506403110f41c080c0c0798041c007020a0005c03c1011210a4550249503441000840c0046a5a09242072950307034026180c9003ea92031039146105210b0200382e03509500d2541c10f4100045100c070945142d164404 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 797178552 1250 797177302 797177351
    0xf070806030f0a05011d060103110108060a0b04080c01030e0607020d0807020a050f2506080a09020a03080309010b1f090302060307171302101403041401062102031b0d06 74
    0x902c03d14103488100581500100e00c82048403074403400c1c2c06098182c840e40c0e43c0d02030000038000307500b01400c500f030755105541190380000001e01c409101d07075580c07042c12403a9005400c002c01940004901d8410740d42c040c000c051007005201e00402007450310300c1000351580140010007081060b404049900c20340b08024400300243c100382030b66068a880d020345996101103405e9000d1700d0180340c01500c1512141040d003001c4407110b4450312040d40d030b007a01d42402410400000c80e80400c85070340100216150b04050342c49410310000000701c0007402c00811040e89a40303010300c46443e43d0702024207007240c1e00060740401c596042d5802502c1741c442c2d440603102030f6140111416038040c0541080301c80301418800c911824001d888480060710b0300070040b21042007031034044441030010004203001907140854a0200041c200002424036144c04500000d03103211103031074080310030001c010400c1d450203200040e91000d81e401d02c10509200130020075202e100341c000c042c00e85503440e01084001e082d2942641000c = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 797179802 1250 797178552 797178583
    0x9090708041124270303030708010614070f062301051c0203010902040c09181416140d06090506040207051915060b0a08100506180609100c0b0f0f07080603 68
    0x150140700104000848100d241c4512030180c1c0d440813000c5060120459014021035690200d407a070030806d0a603100c10058107000342040e420844280030406060b91241094402c000224114070b80c600c50703004091030020602410348120004010030f64600440c20b54401c0410301d018414260750000034010023140c2c0019402904051003802034560015800c400c0e114018001280c01005031640c070115149102c010501c000d643c004900c00b13841c0c2075403040030600c1c1880e0901e4202260383c9124003035002202c020724016110a800d002440150060720b6000c1d1040d201141808001e854450342d421346c84240048018054654000348024450035000c049580e4105100c116a00d0800c1c50742907205030040000104590042034002c0541510001140d00c010b1461b030405d4150700382c2c0501022000c840d80c1e070000040021b5102900c4d416413030000f8487c0758a0b0080284814101600c1e0b0010050081a004a20781c0800485180340b403185600202d09207090491555070f04046440c04420740e010020 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 797181052 1250 797179802 797179807
    0x6020f1f0e1f051b0a360608010f080c060403111f080601030c021516030608060a060f0602070b0a05130b12040618080f0d06170309090708041124 64
    0x8824020f03420441c010081142c00c5002d00d42d02c504882c2e4140252000310001404c6804a07841104030071000c4010b0b0080840001981b203109100000d030031806501c010041070711035004001c03041c2d03000641802440d0390740250101d0f40740000000c040303119034000104401240310800465403a5500341e805031410b400c040503d0424580400341c40c10301c04641075070020f4104028400030910100c2c2c031801188804102d40c08546507030030411071090380d846440302011307601d080c0054030326020402d65000b0507a4400018440c0d04000a50340154542d40182e030075903114280402c8014001003c6440310112460303d99251201c44504a25407a41c80d4001281042c0118900301094070641186010b9440ba410410030308004105030035001131172910151001e070041c807001d61102c1e04000104000807a803500028010348414417040c8500300b952070101103078800319043c0041c0c2000014550480e0007401c0051082c503056451400100204ca850360181a0500c41c52292030145c0406043c8210442d01058 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 797182302 1250 797181052 797181103
    0x17090a0909050111070218060f030703261e0a0c02040f1a04201b010905061b0f0301030305090414070c051009051e07030c0b0406020f1f0e 61
    0xc090842984103440d5546440b003034081c4030070341320100c0b189594040d2070040007202d11803168080305030007030038141c00003c0c2e07c1141501c1d59043c04804050341c40740e00c583c441e10344182c91154802c1c0c1040520341200b4410401d07003d01c1748200c03000e2081540842c1e0020b60303546200b03804450480041c2c2000390081c0c104601000c108038250404041c0080015140103d059030008000640d01a0103540401c103a08041588031080a4001006550700e41101042d0800c0c44501243c00c6400003c0213a401d0740001c0c0a000108210303e41c00791506402c022401c2c1050821541840341c1e120600c002414018005240d804036100c5c1c0d0005004603030780d0807212285240061000d880d0f001030b80021a40c50040401c00c4951198a01c03450502c281c001008104000b00c0e90a19268000d03110b600d40b40500c54280b0000c0003990b00d00d0004082c1160761201a1a24a4004040d2600200c45034180840d00494601c11030712000c480d49580d0304884010205aaa04020880d4105080d411011002500202e01c10 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 797183552 1250 797182302 797182319
    0x280305030f120907050603130f0b2508100509071e05042d03020f0604091113080f0a060f11030103120801060f090e0622060509010f08070317090a 64
    0x100310442d818511040143d81c3c0b0421152540f40901610b5071044092001c6420305242e00101c06000703100305052410b032281074450716074001d42100c116140c0080c95a6076440c081d0840043c1c81540f02d641000312150812a402006200c8503010755401084400c000401643c0300d410904100c002840081c2071a801800300107000383c0c0180a41900d4071200c079003d0307000c003140080c100c0c1184640e90346448c0c201d0550742000107a41d003000755258024414000803544030301c1885644103101603494940e41ea0425100d42001900b6544d005500310341201441e064100b8020660f0072820782c0c04400000c1f4080340700440d50040083d03450310342e0222004030010003005060b450000514540b84c4405020317030380c6d0344012680710040f400351000044164000708044107200f030705290864401050450a0710303c80741040303604c605c0d80348031010058940d2810000d0342420008140076190710440c80c420182443c442d40c0c0c0da600130b40b200608182c40703610b060303a85004e090300380c03406e90030024842401c0c04d41c0c501c0c20 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 797184802 1250 797183552 797183557
    0x5161217040b090c0d080d0b0303131206050c090603040f0305041208041d07050712090317180f060906090a0e040503130b04030213020715020c1509010b280305030f 72
    0x603a142403040c250551440d140103100d01c04206d500140702480c0204100c0d00e00003405000c0c99440c2c1510090201e0704840040c02c013200050444410035003c03c880c0c0c2c2c02e096003a900c000e400d60b2120801000080260b403112800c490b401a04091080948545890121400d00c00c3d40e01c06040005c7c02140c0808100b200c0000b071044913221034842948500311008520910400e99009002c10000c014280010720141c4c02c507580c50b030301403c0c41c0030f003d6540c1c2c9400d5a00341c4070080400b1100c10000b400210f090400e03816007050103095070b01c21100482d540120f10741e4400d00c02294860440450b01c12400c1d40d4120b1000d028080c000310741e0405041900d0100d6a82d04a80480d01d18079050000200e0048d0221054904032a0001c04020b103503071560004c40004c1d40b1101003528031140e06040400c600d0048c0c0024919104003200410f100069894650280480500002d2559042510400c12903a0790596100640030010340c503010110440460b0681644590008100e8000401e040302d000710440d01 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 797186052 1250 797184802 797184811
    0x20a0609061701120b040317010608061f021e0a0203030c0114011215020c0f010606050c010b18060f030f12190503040203060a11071b06020c0105161217040b 69
    0x64031000106030203040d41c1141004d00800340159140c081d0b503004640f0700381085400a009040c101400641d0b48503004850740242c00c01ca02040c5400e06200150601f842c4c801c1c076402400c4494405070309100c1d0000c1d100c0044e40381d080f41500d400c0031501c50844d000c2c8041c00010b1360060440b0769a00341000d00030701919080c4541e1525032000000000c0d40c014140c0009400c03a0700469205141101882d220700035000340209004070710560142913010359003446201c001e0040f50300c91689640c4804012401d540a000d0440d000740040300414114107502c900003504090704843d04424600f50002017842c00c625800d10b88164890704c03405021240b980001424009280c5214510140c40190184c541e888140c40c02900360303001e0000a0041103055000510592001c0d0000d4500b0280380c4400116003409034103401e00401030803040004c1501081203062100c001c1c2031103030400303041404144000752401c0002e440c0700100d4007a05130152184400301c046410118075909507003401d00305480010030849 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 797187302 1250 797186052 797186057
    0xd02070f0209011205060f0408041d0f090106050d120309150608012009040b0a05060f0408010b0904051507020102040f03140105070203030c0d151706190902100305070c020a060906 79
    0x40c00402c01351144000c0e006607940000c01002c094075099071524101c8001030083d15500070601007c10802d05070b02c040b0003030070050b010540441c284040445042d100c050003c0340c090b85043c03020442034a40400c5600042d4102a200c115490030600680103400700b41c80013812040c014a0410304d14005da80000c051b100f000d0003c200003d507042c120042c204c803030034015000140c244500e034200d15094002040f40007000d00480c0d41995030b280400d0081d0003c01880d0745d40301c00403405000c1e8031700034450000020001c0391001c4080c105611501e89507400d80881042c52940b510000d882507000350100d034000c3c00300040d18841c13296241024400741c41940759445041d42841d02180010748000701f581c0c011a501e0001c189005403000c0b02e400204072420f62002d1144401c04001010b00b4841c02c07003020701d40114064446480c1c804e0007035042005205054034064502259100580c07142980c00881e400181400202500c40340001d0300c00300310b0020000c1d8404051400071074056400b009010845400e43c = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 797188552 1250 797187302 797187319
    0x6060906060513060e06041e0e0c09011b17030a11070606080606010f0801050f011115061008010b030708091603200a0302030c060304020d060203090120030f1801020d02070f02 77
    0x340400c454040400303549903030091b0140424000002c2a6411a14819042e0103107100140d882544c04107010088803070105244021030050a696004060701c3d011007403ca010302c0062200707540c0d072101c00105181e03e2040080100009200d0b82c0c10785d101c0c0c1d036001e210b00003041d1100c006290220243c0750601a40685004a20114402d54040c0b5102d0f29441044d49882c0507980c06d0805000c490128130621a0400164450048140d002441410040c81c95061410740c14609841444044500b40c241c0e0000c2201020040220903810029241c02110034507000c051030f25003d906906d84840b071020a0180780303117108000100403403111069641c2d03508040408601d1b40010400c4031141d180e100280d0150000440d481051030900002d680c0710384020724168500745946c50b1001240c1003291b06010f96950341001900180c0d80a220302481d00e11409618a18502581c103550303050409040300c0e042c2c0440326032240b020842074064407070742ea400d010708540721b80b0541480300c070341da5034080180d000d030720720 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 797189802 1250 797188552 797188559
    0x3030f0203030609150102120f09100503090d0e040e060702100b0a06140915070b1b18040b060423040b04020c07030b04020105090d050109030e040b0a03030c06060906060513 76
    0x3000781d034882c0b10f0081411440f6659090541e10540000090301d04500441070390a8961650102034006c0c1c801e903205080d192481d58060048a400c0044003a080c0a03050003045841080000c00b150b00395411710300008900b9000300454040c041404120302c0902968040040c02540043d215800c2d0440c80818806451408180300c0174403098010f0074000741048000d40c20f0701407028000c000d450030140000005215494030402c16420100c41154820500d0051044507401e036807030b101c0240d8140c5045031038131083d00c2014400c0301040d0a00d5009070b40f15070707201009913169020754004020001c800b10801c1914482696031034900754000384224509036112001d81000c1c03081c0c96031190070000034a520303425138680c0001e00100800490401c0800c01410320035403213030000f1004c3c641c420340000c01e4928540c0707405483d1508803c1c8141c0a1440c03c1c503406102d50714100300500312601810010b04070407180c10f000018005c6071300a4402c55007003050005060750702400510702c0b40090006042c01d20b84 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 797191052 1250 797189802 797189807
    0x10b0a090e01050a060c05070f06091403061509100b181c08030c0d0b0406060305190b032a0405040c060f03140c0c0c0307380304030507050712050703030f 68
    0x1403e01501c2d07044550850180030890080c8003440d800340c0038034126040c00c5e41c2c60700340d01c4e1550a503130004400602554810800e28098803800c141103003040340540310701c0c94443c01c45280201d034003010300c0c850101741000c03422000900480c8405080a0800e081c2d03600788040c41300300a20342074020709000302400c41038000d5001150580700c0c1082e07800b801f41451520b85102a201c2030f08100311f9641180e41e201700e410540d984500c26100148015100482c0760b00d080d480060524040d54640b02c810360034080003508641e000b040c4040101803038251403008421031261000f0b090214502f00c1c2c3c004c0e14020607c81804070041c11030046400039903458490004648085084e201d10540b1aa024103020020402100e0094080c1c0012003198041700c0d400080c1400092030950264801116030701c2c0c2050340d030106040190000b0078890496400000303000003a102d650207220060010b4200400846c203078007000402d1107040000c24420054045643c5c65003012038440085101c102c1c04200120140c80701e090 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 797192302 1250 797191052 797191079
    0x6120102070f0303052e03140c031f02130801051021030e0d0813150906080109090804030f1101120506010804030e190806040c050105030f130c0e010b0a09 68
    0x180d100e24a11990002c0e940d066000d0000030307001c0e0506e20b050b50180750949841044401008582e0311398a809189503060841c61380c4840b486204c42900102e00001c55a18002042d05030030060400c0d409028844048030070080c001da40020411340f8582a00017201c0f81d0540209016207040e44160030302e40c0ea60b000002c454054001100c03544088020b0f80c601103030060782601e150107405401c5400c820f100fa6185d10f0503501c480d6022a03031050b0301405002c510890958008c0b5407d60341040c055042c10318401405021f030510400c806903495081600400070340d001964002d56124042468020303242c07610b046182d00415140340040c20364680d04001d0112030040034003683d0180c5420100d43c0380d94400300d800f456018003c42c1c0040062600b0040700c5101980200100f40f41c0c800f40020341000e1820300c030342c80c44951042c0d04000b400e0007800440c2244000194000200c83c61807401300c441460240444803890703021608500910000140c0b00c50448020103811600b40c0e128080300782c49210150303080 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 797193552 1250 797192302 797192317
    0x4050a0617010b0a050f0703080412021f020309010908070317070306050f211c1403040c0e09120706020304140a030801050f03011805030a02100e1207020d15020306120102 75
    0x190041d4010805150044003e00300700340a031400c0e900e4101100e0213011550300440c0214001040a0104404d0156209401da031031185031002d0080110101085600c1642c0011100d06995000011444009095000304900c41d4046e13004e644450050030b02403c2c5101e001d052103c0180504002084075209218071380541d440101208a803c03603d20501400080410850701184020516040c0d07005c003c01038180d50760300014001c500d04144403801003500040001c5d081c005001441448002252499a2009e072004c0d03414029099840f500f40c6440d014010124518400c80001d20000f40201c64005510072801202c4902e14091045c041d5681c80040c450054002040310f0010700c814a4048144070003a01c00500200c0c000d4416509031440c0079a1107012610740d400040c00b504081c1d014080e0891004401c0401c0194040030030380c86071240c910a600c0701d101c440010720750003159500403110500c0e80d0405c039955084160441d0502c029441560380390b2040c601c0f5003d115061005000311040c0 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 797194802 1250 797193552 797193587
    0x90b0a09051009240e07120b2a0a0512010b0a12050c090402040e010e06120721080d061a040b040311061209011b1d090405010b100504050a06 62
    0x31800300040b1000306001c210454000d4080943d44120030540703c4200080d030814440001c10064000400e4501280d95015080c2500202c09900100d0781c0e0080c683da0001d1991003e420480c0c11030403c02861819011501070740d40c0201342d501440d60b01c4009062420b1545003020820703600d40070070101714091902100c0014005090600d0402280c0d0009a0000c1104103803504000401e000a016038115030422850041e41500400c18121400d1800390000416200705030100e000d04d10003511080701d030046440e07407410840324110696107440c085903165040030b902074481e0f82401d10b41000e048244684585210030124603042070002404450884010740142884d05240d603031211103900c06103503c3c0d6800b103814481d021780014462402031040da04c80000043e0908903203030881380ca8240489200c20001c42c0c46002d821034032403a260307030ba546400b02c17071010701c40d9140d1a0041c0036221070700b510f0f40c10100707044a0802d2140c1260190080c0d8400f25801c00080e80c440c130301143e40180b081c030059034 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 797196052 1250 797194802 797194813
    0x6050f0307210f241503091514180d05040e090a0501060b0a08010e0606040303080a0b0415051f020c0d05070e0709050907022a0d120201090b0a0905 65
    0x1402401014001e055070807900c102c100c2e80421182c12100a6044059800d4603028420002240340b0001032603d204101050b4080f400c000d440c52041803903c105406040d50303900b0318400d004550000c0c0f0f400108800741844144800884107205040c140c6100031600c24030300808a50320070105090784100456034406050614140e22840900c40c0540700c85a6401540f4010020403000e00403080071304102109130b0380d140169100241400c805901500d410f180c500c050100c580d9550044404403505443c3c145c607a500c036440d001b0010814800c2803940180b42603020700030302001c144070b2001c0343c10444100d0b14507124840848141c50301041043d00581143c40803000030300e4140c0c0b4031003409014a04640020b6154990301e03852420544d020400301d074041c1020480d501e841d410242c0c0c050100d2001d040c1241100320750415400e110142c480c06406209840c1c9281d4a40c09005200644c100004040d01c080b0a0742c040c0c021f201e0f4030403d032003c0c07070608000350040315180113008640303922400900 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 797197302 1250 797196052 797196061
    0x62306011d0f010e03010e030c06010f0e0408180a0303120b0105120c0f040b0d0204051f0f03021e03040b070801170a030f030f02030a0605120111190c0f050d0906050f03 74
    0xc6507005001c50ba07414800719296071400d5032004d01c14103400125107401103584104004c1808c2c940803050340701e04107074030981c09c0c22b0064000380c45106801c180e000c601161100500540e2441411844081035000902c1c03050000c28540d10008101c0002d52102e405c101d07124640c2c004681f584501440320b00c1d0251400003190386020708500078a1256505908942041e4a410b0b050046a1051120b10700c981c1c3c02103411300062600d4108010401c40b4880484298491508082c01c543ca030500c00340d05142d800f103000c2d4644100d0088aa0480c400c000c20a9036038601850401d1060209861540c002000c150010404000c0c7c2c1c14552440681c4200411550b05159400c0b22854050042001055110810030014856500195005510004011901c0c1e4140018003010744a000c040c1c00c0719a0400400b9005608004205d031152219440d8241c07001c102c446003502c4405078544000c080d40340804004043c0440411500491170035981c580c0032035642c403042103503107002d0111444c400031403c00204 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 797198552 1250 797197302 797197309
    0xc031d03030f061824061c0507030e03490c05120405102915070b040f0c051e19150201151203020316080403062306011d 53
    0x640c010f50082c441c0b002803101c4c2d03a20040000050b503128041254020b039810aa01c0c2c1010a0040c40b20300f5501c00d41481140310305da4101c032015a522034600c2e9900c0c2c0119540d00d100b900310310b4900c80d101e01180d90342d42e50159064000003003400d40b20515520081188081001c5010461103c00550140b0005c0d1050f040c42e01c009100800c401800e00c03c0400070141003a00340240c0a10550045002e080b400d50080555002e42c1c2e012229003100319800f01417184102d40210318a107072008250f48205100c0c01407403607102188a2040d002d480c0d5040002088100b04d2540a6031540510840c200c0030304070380d1001400450344015010700180c10782c1d03144440031818132a041aa042d62040e44812442d40d543c0c05241608604008203801030b510340034001000070700948190700a2500043d070160600490314001d4136030049822000141d01c2900c4ca880030300030030005650146400c4801080743d6001c41c8041a0900c0c0c03008100b0481340802030002d6000d60040c1d5178405410500c0040300848207500080 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 797199802 1250 797198552 797198581
    0x2040e0610030204050406060507030f03140c072f010f0302030403050702010305130c09020a180e060603090708030406021e010b09011a0c0105100504050121080901091502010c031d0303 81
    0x50700d042640c2400002a140d50340d004000050482d42c49160381c40740f1030b040050075601c2c000514414142090165290303090903401c0d140c2d009440b04151a280c1c0444e04d0414403504410070655070f0000b03040f0007001000c0d00c515184040050036201c6a00c00b0100d0b1609400b41e0000715409008600180040300240d400394101c40e600a408914001d905402555403511400140d00021040340d40031814002450700302183c585229038940403007085d0703403800311060840b07400202014010100440403d0000d08204200c3c00500701d01000d60f62241e40b90403000359108000e11850504030030400e6420440403061044920040d000761692a05a0034103140a40408105483c03540c800d104106c00f600394102031181501841500100a20992500c07080206868040e001000d0318080249000300da1010b09001141175507211800780d8880c200a070041c3c5aa192552000706080e03603d07185100c42c80d0741984000d0400d41680c4007000600004004c061560004403450f107880d900c01c101040745507104c07185 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 797201052 1250 797199802 797199829
    0x6080706261506071209050307030b0417070209011401030542100305010503010b0f01080a2a0f081503030409050a06120f1e02100c0515090f060a02040e06 68
    0xc11480c0c600c2500c0101c2c0b00f950000c64144d501011100ca11038140d50300c0380840b0002c21003180200310031801c2d9161408050400741008002d400c0d007150021705104c5a005440105800410200d10b40d03950f6104150710461070343c0b410b40000d20b810009141c0074001200200c0c40c2c2e2014100480c4038008850440050503601c5110640e83d800c44080002c136540c02c1c0f40c0d076003d115a90342c0440c043d45080c00307044c00d481c100100076101d03200d181184603160341d1111419034420080e0b1000305072403802c0c080c4690700904003c0c0c40516000100146013140350421040070100c4204e560303002c050b0795000300426240c40502c41c0250706410402c000c00c290001d542103950400030402d000140c01e69128543d401619052200b00c034500e840f0f988001c00d100c8040c100e24040ca00030948424080d04903070000d80708900c0c00710300b82c09201c000f40c281410b0000030803c0148201c0905a11012824440032082d0794000c04284401c0c0e41c416000016100343d031900a81d400c032141036040c0070075034881c40c04001281c2641c4a = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 797202302 1250 797201052 797201071
    0x1150806060d030905121f061e3204061203021b01021207060204051002010b0a0801060b0f03150301090c09062403052d10050616021309150608070626 66
    0x40c3d60514126101f00360656019100b44001170741880c2c0180e242152528130a440049046490100061408003100c900c104090010341700e0301c0700035a424070402d90600310245410034038011002c01c1d03181d50811840120b0b8002c0e001c0303d50300182c24407142808a601c000c01401030300591409054046000054141907200c1c40c40582000e45840205062100d1146c0810050f911203505070f44c20700b060800c10009d070250308000d0241074101740352880c99100c1d803020052841c030008001400c2030b40040c03006441080080080c800101079081110102d01d85015101a06290000009102e64205a0403121998000c0c00004054042c0c030140d000307000080225012030000904000142c2d856240440750b000308007103090150810781249642d2580540105000d00800c01c8040300041d8110321004803564100c403103c80c140c041c5420b6001030b000a400051500e50031104120101005400c01b20540e0108001c4521560303884904450447c0d180c5543c0b80154030680040f00d81c0e442c110746a551004400b07 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 797203552 1250 797202302 797202313
    0x6070207050f0d1b05010315060f0c140a0f0b0106030606121a0909030406020c0f0f041a04020c0309100c200a030b2401030c02191401150806060d03090512 68
    0x41d110030102000440b078203621400788000a01640da00351148840840c8c40380001c15400b81001d03c0680402202041710040c040090030003810410b010704041030080c0517034117903801039010b454200066200741f14120f50301e171a43c00000c55110b20070320407001100c40e5030b503a402c0c041501075409001801d81003400001082c00740d403209480d0f1990000b1a0141d880a0300469980d0318000e002414000400314140c03203207a0000702c01200380e840d440e0034840d4100446000a06803d41d64030883d08031110a81e050304680041076140c0c1803c0c0100152101749000d440c0c042c4c59070503c607002c0301c40c00c6201000a1100386010319000980c108591020303900074000e03190620342d540781e8803810001c8904680101d140b84141ca129001224800300f1034110381030030309050019000350400a52904600d40e4031101e12031a02030f04200340035844040a020f062001c000f044000c1c0b480244480c8020301d801a010341e8403500000c01c078581407040c041c00300c0c0b84c0c1559604a4050401040105c1c4014503400c50000d880b90 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 797204802 1250 797203552 797203579
    0x21e13030503040b1201050a060f12061512050a0207080f0d020f031320100302181206010e010b1c090203010902180709090932060405030a090806070207050f 69
    0x400041004d08900564513440304c00359105041040c4050300598050812540100030080c0c008446001e410b00500700600d491100045260007055194020740030301a02000801d80780b50800d004005c0c040d41044c003808a55164006241603100766a002055140c04000c1c20520483e40d102400000180b550701618000d002c1120b0880c40d0000c0d5412440616021401d0041044d040c200150442b0340c8601180680480e00004802c0c035031895805040c1a00040c558003030328a070042402600798001e00c0300c8012000318100720751322603003402012100b00010b00040f070002803030415105403e5040d503900d4410000000224003a1902070b0049070150340301c0c00c80c01d0050b0b5031822141d08208030004209d5640c42d09038001481c2c81d4250344420881440d0081d014045052526901d2451050100d1041e00003010079004240f01400c04522180d4002c0c1d00900080160101c010141426542c0d14000c01c59200c100b8541c861006540710405a80148010402030414030b00300401e460000f4802c1c105c40340c8 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 797206052 1250 797204802 797204813
    0x307030b060d06062c01140c1e0f0114010f05062b0509070506090d0609031103070503090a0518130819020f0d0206010e070e0310022209021e1303 64
    0x1660041c1d00440c011041d0300c3c0840030a802e9445d00d00f10600944000e240f10400060b1091085086404400c040054548005502048141100003091801e01d10b0b081e4903240c0940c840c144240031081c1e950a000c3d80c1480c960a4849140c161000c0000c81040c3c0c910746403c0003007a41c84410220a04045541d5480d011102600078052044080d5404105413030001c0a16090400c580c00075841410280121a200e45501c0b104102650b84170100060110150400342c8800700440b003070440500c00020404104034010000d0015140180c5038251f00d15101c004020f1042c0e140c40c2c441c2000c030200360014201e01803c880c4911020300407981c1500e4016400b04175895444079900800c0580e204107540c41e940c440c1040f291820012501c041c0440c1d5041464600381c019010301104200a240c0600a135290303014010344c402900d002608540c0e40211100c10b850740403801208280503a0510030004220b00d041c004c440c4ca81c101b00740891086000f40044401c143c204001b00160401000000b000144 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 797207302 1250 797206052 797206061
    0xd030c0e09070f030c1b0206031e0c0c060906040b070318060c03091505221a0f06010e090705160501091a01050913150b0102032206020d020708030307030b060d 70
    0x2a501d5030b4200000d03010b1040a0180c55403000d1030300030090000c040b145001d640401d0385556a1f8100c80780c41e52034980c041e02030181801c0b01c000c203041113010b005001118103100700400944d00a4001d541070740c0c0d1081c24031a21110100c40c05040010201c1c00201b550348640d000500303800d50701604801c003c115454a1048131801003150005ca1394450301d09090004249a0150380c02c0140720600c00391511964018048194a0366443c522280803080d10800200605c000c14220300550705142e18580203804440c440000d48080d804250a503404030082c0c20b15610b880c1c03083c1d4403038a80b24a0643c1d001008c0b4008917000c0c10594a0b95a216031100000340e40444a24a0005a0a446155504003802c1148010000e04540580501a0700100008064600c603900b143c03401d81e00003588507840c00050b410340c460032000c0c0e410b484a030708004968056005d962810b48201da821100200001e00d0182d82e20764050040c000310303030320910000340307864420b420101c031414001d03064505040c40410140141c5 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 797208552 1250 797207302 797207311
    0xc05070312240f0b0315010e0604031505040b0106020610060e180c090906010c0c051306080a0f030201112107031104060201091205030c0702040518030f07230d030c0e09 74
    0x24002c207002041800818030780da40c05810900040c038550b00b009500030558165807a0345070305000403501400d0080c3d6a91040d01c0046070409410f40b00d0102415596000740320482c0e00301c8441c9840d40c0081021440040c41c02e104000020004803050704140e0140c4004040b81e0140d0381c04a0440c44a07442d24801015460050040c030208648030082c11080140019000341258100406800c100004c0b5451400500850340309455881c00d072588400c0c90b5001d00b00b641c100134880c0c23040184510400c80d002002000341400790f4001c0103580142883e000552060b10200985400d4201010950b03040b4403103250f400a016050000c1ea03445101c00505580d00b0540c00213026035910020030701070054001d0324281400c0c03289441443c44c0703490b9040804e00e0040c0d0b58060700840d0340e030b000280c15007000449645a501218205c90322944010200b600741d900c400c504070398427152040c1140d00500d0400c0803145248081010303080e0281204402c40041000120050400030250390500007900c3d45442c05004 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 797209802 1250 797208552 797208611
    0x3070606080708120703050a0323090114100605031312020607140403240b03120d061203140a0c060c110d0809120703021203011e090c05070312 63
    0x100c1d01d8881010b081c2826540800195003107051001c0c06180c41004568086070b042c10a036072107540b031840440003014031580d5215803d025007180400244003031003592087e460742009100400c0e070001100641d0000350f40c15030480b150360206020441c010744c00f440e4400220f032408260301c101e644810207456070135240761026070080c03410f100030b036640185840306c40380004815602c2c01340755035940c0921004140302e20455122040e40004001e039541c1003107043d18002030449e06003140740c0d01315880a42c403a00c1c948a1315440c1c41000110740301c0980c4d0700c0410341d0301a1034801a08101122000c116444401081704000c05840c0300380000340c445c4111915145e603a59414280000c00d290319240c8400d16000c04140121201005141c22001038201e80c0e103490100d600d070f1210642e107400ea1910741048200401d444000c0b00106400c4500c0021100010400b2909841555074812400494000c120a035001510400084010a0007480f60b0207021107540b02c0000c0c07911500000015946980414481 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 797211052 1250 797209802 797209811
    0xe0a090b09071103071416090f0e0c0904020103090807060c02011a1c110406031505041e0c0519080a0f2612090313030609050106060903081b0f030706 66
    0x9907810003214481e88941c06081546902101c1542150341c1d014400005000692011141d26411001d00c05400c20b91484220340c103d050f04c40440ca0040c003043d000b213404461420040340d000320800568600b40c028040c203a0107482e140c5400450161010b01c80642d04048100400000180c0c684640210050154000600920080d820701400d41c030140d011445811141025902140652601c128455004903e0a6007005400124003e000c1c258005010003000d0032300301c0c0c00c0300071513001180301e2803007400c8000060302c01c845602481841a00042c0440004003000d20483c10440d000c2c0d83c1008080b8403060016542c0c0321102c3c03810108803000c442c0e5502000141e001c00c840388441072100318504840d03400b0400c200c4280b000c0c4e0b000d500c1110031503402140105046205c14001c6903000b030403100919225907140d0a00b20003410040f41c0c100d4066180c1280018664400c1503684243d95000701c071030380740c5280f4000c1101404400c0d0320302c00c02801400740d03c0210040030130060507460f104440205 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 797212302 1250 797211052 797211071
    0x20d05030715090803060d050f07080c0901060c050601060f03021c140604022521020a150b0f060c010f0518010b030309030d0c050a0803340e100e0a09 66
    0x100407280070076107000941c10701c010200064071130000d60f64000000d0700c0c95003070030304542840f40c40c10501011915a40c02482004a2524800f0585c14140401691116640d0742d0311442240c6040004101802c2900204014000d480c8501c100071500005440c0c090b00340716140ea42c1200d85101c182d280c000c040e42e00d0b6102044004402e80b00c07640490104e50031800d11448404207544041007075040c0000d501454480810090440d61505203001e0720104c11040700751400000e03503520444842034440c1000d403034080159080300d0160741855600a842a0300c003030210000d011194001601c010b4055484410964409446108a511450441b02401c2c2004100703805c1e58211141e10b40001c1c0039420070071180d072240c0c600103280306041c14249404001c61825082c11400c00010080c010541c400000601036803081100d00c1e00e80f020010030040c0007041c2c4640585142002103103107400454400340643c0e07998549401114039020943c10700d8016102001c0000707450403015006440200d55521625 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 797213552 1250 797212302 797212313
    0xc050d0507230904060b0307021509060709051309051b0a06030b030705010c0f20100201140f150a03050102120f070c0609020406080a03030e0c0f010921020d050307 72
    0x81c0c00809506103910b61400000000684662003a04180c01e8000000c1c2d001e2180c031141e020200a124201d605900c1e4140307803030b000b134446508100703215000019501244118001081c030a00440076601c1e080c0540749404d0078010b2410a0005400070180d440c1e000902241c0140008084100540e80010008281c2800c00041c4180c035041201050b1515040d1001d6032000a1a241a54001d091001d94960185425010540da11400038500e180040602029000184400c005040120b483d14103182d41070034228200e448400e94034005141c0740000c100c240c4014600300b41c02c18510701500075041003039400708884042681c070407905a94009800c074001d810400490780c000214010521a50a03c45c0c40240040c0d007410024001c65507445848045507295840300f801401300a007501c50340262420040c0042043c185218070900030383c00c0d00d1010340340551004080c41c005071940c400b01c904065182103150083d035040100003020781902005a61441c5407110114841c100850f80d40b40380c0c0c68034 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 797214802 1250 797213552 797213561
    0xf0a0b1003050612010e1005040c0f061805090c0702012106140406060806011d03150703091103070501120906060b0f03220c0909020a050913200d02011b02040c050d 72
    0x131a01141d15120141811410104201c08000222000401c0d991200e0410001c02103490b4080d0390b06007506480000c0450704229096a42204030044001007a17540d020720907110012a0841100c110410050b001903005035204081411422060340103042140008001c0350100c1d04040d840e5100c8150450b0a80341c00d00171100071b003005190020150901000280011440285400c0d000010a50080d0a62820480c00010b02c85680007030b101400e01000140003088441e0b000e903000390708000c3c0e55005050006c1e8000407a00103960390800c5204004400000740318508084810f41c0d01e0743d20006022803c840a0400040d54440035540c2e070800c02800455a11201c8001ca595040340c803007540482c424407110342c1250340510340440d1001d41b500c0000c4654076a904884d600444540601000115200c19020301b00d200e100c1700c80c2204500000c400203030f0228500a50700100c980c0f42200103521844001000e058001d4486032207555660007e000c0d122801116800198049246141c26400c2c3c020b = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 797216052 1250 797214802 797214829
    0x13091506060806090406090c260c210109060509031b0a03211409071404020f09040c02031c020a0e06030f0711030403050a0c140a08060f0a0b10030506 66
    0x1040501e1412202516014000b00083e00c944901c1340020140a59500041c0130700b54001075210000c1c2d1517881c00c420800d6542e04060380034403007000560b030340350002841881e1464003d0201280b120000b00071000c8049130b1038a04801c0d52a400100f0000725507003e11801404400c1c040d40d01c400441c50110480720703007034901907001d41c40000e03e80046508002d10160955050401a60b00306031440c1a101070510545c00b15013552202003004690680071603100b007510081c04032505641140000c100680c003840750352140128040042000364a410b52001c0880c038110f0042e40e042c040c08502940000c13401c1c5008030181a000030341700d00035680c4a0b43c20304000500b201c502d41142440a4802030b010001440300d400e003c0e8000c80c1e441603000800980340110361040486400704210711700340760400464454000d5590749212150168580708103442e040c4d403114401404150340b02c0541c44110800a0a03201840380d4414102c1d03491f480d90780c000c080005941d00d0102d5942841c2043c02641c0c0c02504 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 797217302 1250 797216052 797216093
    0xc07020f06120606090a38120c090a030803070c1115072006040306020d050a09050a0303020a09090204031209080606031510080304080607080108151f03021309 70
    0x15680c03a080c916804650002d0040e181c0a4070b81017500302080071a0070f1a00300402d808030000101100c00021040881c1e140302c00d82c40025084445031f080c042a0240d03121070a0004290030000c0c2420740140060010440e00400040285540c2e8882e242c1c2c070b600039030702c01001410545405050159444103030807104004d403072140a05041c00c5104485000e01e03800181088800b841c0d03900b00e5040d920b000300162400420141d0386550f43c0c0303012002075100b610700d46a50b90070580001d2208004c0d20a64603480c0d007001c060f03ca03001c030381c0c1d6017200290311404410b400d00007103071320102d109061840075001031840307002020404003a13400041c00c004d0450744104600d60001c0c007009100d480211f03240ca008007054915000d02c2d101c1e0b00e2141141003160304510550700c8049000107608000140c0b0718080c8440791a820038690f02c80344800c3d264031001280b002030341c40705404035840004024240b10340d82c1d60a0840412540caa45c006001a88400d00310a030068032407031050107024008044000000068 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 797218552 1250 797217302 797217307
    0x207051008040803090f06090f07091b1206150e01080912090f0103021603020604031106061012020702040c05040915050915030a05010c0c0308060103290112050c07020f06 75
    0xc0100415511004100070030140020000c03030b409000401c52044600304241c01e880c400d281c0300b11607a07910701d000b098951143c411a03000003001100341c8105804503040000b9160002915841683c1030606050f50100090351800d00003210038481c0514481e003801580c40c4e14400c0143e034001880004054a00354040e00003801018004442108a9081c040240e80c40070007403d02600680c0280a62240210100180221641019030114400c0c1c86140300e030700c40141c040c04845103103507581800c407030b95a0401043c2900b030103803034000d10701c100b1050b5181c2005841c05410f41d010405840311501400c021420101d0240318000f540d016114000c901c40401c603041c0741c50a000242d820801a04410040c0303030440480a41c0e460900440035001c0c0c100e03000384481c2500d060018885403100d40c0c00d40001c1e00c1078010480c10b40c400d0080020011510307a07494000441c4080910208080305049414804551a000c1c0b011006005031442100c041d070b409511030645005008059283c00d030380d14400d980c06c = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 797219802 1250 797218552 797218579
    0x20a060e0d02190801020d091704030b07031a060c1b010c020303120402041d0a0201080c0f1b1f0e010b0415061404241205010510050c011515020705 65
    0x600300355444460b0122402c200140b5244222061519181c000702220750002500c201041c00c681c10a910032885810342c110000306150440080e4010340c00002d20241c0701d0350210b02164401d07041003411000804105004200d0980010b140c1d50000301c0400407500900f06005071240740e0410100303110000e00b011421100b00e580044e440303108d84003080c02400d00400110707055440702e071300c80740303204032154200700038200042402c070b64070001408100d002408030000140c03425141d10a80701107080604050741002c0c210000b0500c4c1e060342c101d2882c80f0740300300703011103101d0040c80c0c0c04140708601d0792800107452020700c01541c2c2134030200030441d40200d052800440c00d42c03ea400404007140c005107850300070b4000030b4124242c1e501c1039038410511250f82c400c0120340416005500b11001041d501c4840b030344500e0030205d0080d0b8609204031940114074010480181d806400200b00380f0f00440c00016403c101841405804000c80e0000c0c60000c0c19108902c1c5a07030380420040002d0001210305c070b078a070180c = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 797221052 1250 797219802 797219809
    0x307050a1e05240304081204080706050702070f141f1812020a060f05040b1821070909111e0907090b4f0b0403050601050906030f0106080307020a060e 66
    0x3658662425010f40000c0011306200c0c1070b4040e50b001301c42190301c444c8070f400d1900b00708a007500058010303142c491802d00420501800000c4034802c40e070306000d907408810329003240750403541c0e00d115140b6000300c0a030180810404403010004441000ca44a05181a13082420040d10168540011092003520741c8510096a10118100102c541e68039002520070412101140c02d401150f0141090220106240702d17004880d883c1d001e8003070015204050105501c01591800000903d45001660442002446042c1e02034104003016070107010f0416028101c88046200c80e44511100e44601c040c50b54001500d2502d824a00c0c0c0004592914540700c42c18002042c03064403913421020b9000f0188074504100c5a41da1080c100880c0b0a0302074859105968101040a641004440003c01c02c2c00a004105044890103880649400c0402003e0903030800c1c05001c81c0b148080c1c091a414821080014007002d02400b5800250482e04090b645401081c4144605810f0941000c1d00703005e00b400083e80700c0d49 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 797222302 1250 797221052 797221099
    0x4230105060d080c0a1202010f0b0102161a16060509010c050705030307230720060406020a0b0a0b100c030e0f01020a0201120219051308010b0a0902090307050a1e05 72
    0x98001c0c5030343d5a9001d5136a4807615203a01d0000c0100a070281e10004003113650107600400c41594040c03001e020001030540126101e941001c25012440815a030a02410308003010030102d040e281c480040c5008640036000d403820f1402e20040f540d50303032240100010f0b55401e008502143e40c1c0c2e801c1441c20081c2e50b50b1503d07240e010003058207007041505100c141044000c05400d244907010310055958070321142c00e00c80000030100380085200b00072201c91000c0380c01c1c070a0455085405950113018407003440d6803018500000030b001b64095540720000c00500b42d455a099440c0702d01c130354640940468452401400702d0103583c28003071251400c105100000d917000b281c0d440ba13090b030928251111490788401c0000034003581e5004001400c0520050707460940180c01030182c48184d07081c5140d602e80c1c8801040c00d84006a00c0f56070402c01482d810480d601441d000ba104040c0010207841e441030b10f034ad010410302c000550100a01c6031a6104c005000c08440c060740000d0102a280c0040700d071804420b055820 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 797223552 1250 797222302 797222329
    0x1207050d080d0b060a031a090c120c0c070f03030f08010324094115040c0503060c070303050603070819020409020907081f0e0112050a0b0423010506 65
    0x314000802c9403000005a020900c07a80e00104466225200040c0050040400da1480c2000080ba03650f000240d1421011a5228102a0b228986408000405040a6007010b4140d941c4c0781c500340210410b144040c400140500004200400083d1546c10b0040881e41d0350100081800580001070021500c42024011030b0200c0031421742d1608103805072030008221540e00501000c3d4070766011840c1980d41c0901002000c0c1010701d200c845c0020014500190210301308903046a071003000507600c0d1200c50000a607029000750704004901d507a42e40131a042c070740c0454071613042c20b000040c1c1d141015003511560f0740085040d401031000700d082481a541da901100c00b0b100d030003810140840c085650ba60481d6003d640e0113425544031b42004100600980000d8035070826560006079070304a030641c0101c0082c03c07500400c7c5201082c0c0d00e4014001080a41814203031507034095000700b9004907282515040c0a98842c501002418005205101900e50618881d00559040c1400c0c490340f9581c4d0700040d03480 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 797224802 1250 797223552 797223563
    0xd03030915090f060b19031103010608120316050c0a03020601060f03180201030b0a0f0e040b070215150d0605101e03020310180b0106110c0a05060a141e091207050d 72
    0x165407000046d0440140c59181d00f02006101c0c408001c200d42d4802c03d102c0130380190001c1c0840d03615120301541380c407054100c4480e0358509000085e159003c9600f86414040c0c14208145441901010141041c0c250001500503034000c07401004500c5d84603800084154951034204035100e14840912102c000013840641050b440d00b50080195507500300c050014404104907000c4107980d10303140d410000c412241030364502011400241d01500100720b060540e045140d00c101c6990340c01555032449009030380c00036000f4548a0448002403018414203008450070080301501c2c6150024080c41c956030404041c89418180c40204010b84000800030007100c0c0c0410042243c0d0a1034000b000702c242800d0010308811030038400012000d4000382c07003c1d00031301003406481c200401c07003042c4903200810344205500b00070104010001c407840780074111500c00c6c12090503440d0040c410710700d81064516000004003e60006044441c509d004002d0000c00d61408001c0c291103490724000408043c980c980c082c02 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 797226052 1250 797224802 797224811
    0x1c06060f090e0a0b040f02070b09060606030c0307030c05071e02120d02030d020d1407091a210405010905061513050702121b0a06020301140d020f040b0f0d03030915090f06 75
    0x8140e605e641100340d0741e00710300c14215207510f15810700528103281034810540a00902004c18540c1c1800c008492042d8a191a024590348480d00d049008090f807060030300400400740300000001e00400341c00400224040285500050107004001002846c40340040c0315a20100c82c0c50f0100c1d0f008070944003480520800103881c0d41100010401606c1480d281c01c0d5076400f40c400300090907400080c414180c0d84502200e0701010827404511600d80b04150401c0b10001c4000000c4611240f0044a00d522a20a8001103404489543c07224a05901a0780850303e03502044100180307410100e4118014414601c01800741d800c12800c0a0344401d08032080042d1004001941031141c00350f42030010801843c00d0844115815600740b0780029042801084d95034020041c07855403e28220b1894000c05800800c100800c200c1c043c00c0000510031254441c0c0c0010f10403030f90094070358801031443d045600035200494064030526001440c0c1c40c5040c0c081d1503c501d0055a1804100c0d80c000b10421540d101c02e0015 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 797227302 1250 797226052 797226071
    0x1b03090507060e01020f06040602041703071a072303160528051308030301181a130f0218040c0801080c19080f010b0a06020109020f060901051c06060f090e0a 69
    0x7803d040560b4aa400a03107c0c0900f8441080f51a500400440d85038403a00101e4040780f281050700ea10403000041c00940040d10b102c08640714940b200f580120b000d0a10b4000a80c5003140607000c0b03030306004800842c1d40044100f04030f01d19039410141002810b890214585a502c0940c0002040141030624034150f40d0415202c1050260089505842080d050f8602c40b0707a641c203410790740b44c2c02401001301c00100105001c0c612401070140d1210f680d0030b03d86801c01d50b031107842070003015520000042c100075282d0490304c6000310301c4d1004240065440b05642c81c4d1480303000500c002e40c2c8032480c40008103c18100100100400481d02d1408104101c6800800c100b00018803862900c0940100c01c65010b000c0c1c20440a803015400201c6850050720f00300b001607540c541c160b00f01c9208403c007039013004040d903245a49182030001040d00e031905050103420264000c0030400c892003d81c0c15892020b90740c42051015075007054441c01020707014030b0558102400e0400e45640582c002d80719500f90354481c01e026 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 797228552 1250 797227302 797227307
    0x70b0901020f0610051f0e13020405040c032c070603020c07030b011202150901020304051210060611070807030f060b03070305030a091d060d020909030d02030a1b03090507060e01 78
    0x200102c00881c0d040740e102e410030342100c001c0340036148111803050400441302c400d05011110952100e9406031100f05444103210107009088680342c4001754425406c102c00b041c82c0e42c8620614202e05a42e50700011251a003110410981d82807440301e0103880f031009503105c03c41e4400105003059804c2480e025882d101400f00b060b160070786a82004002e8500c1c08008140a444070403043c0c02c90303000b00c4114025140c0c82c10342c614103105016a950050300100014004c0381071a0380c2c1c0144005550044811401000000710300311141d039000301d00040c502d17210003900c8031002c2040101410340400038104461030356a884084d2100074000810640c0c549082e90100ea074240132110003140c000c020340e0ba44400340300d001000030010b1700840c0010b4800c0c5480312814005000c44500c03c1101414100d064012902005400b20000301b2210042c8810061102240441d0003e10b02a5070101c0c4046075180b00c40c0c1c107110503411a114014100341c90181100c0118100240040c2161160b0030480042c00d03e10004 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 797229802 1250 797228552 797228563
    0xa2405040509160201150e1315050c031e01050609040504020607061a0112050c041a04120312050a0203060901090509030706090804030311030309070b0a0905030d0801061b0203070b090102 82
    0x34580c4881440304011103d00d00b010342c01c82e81d9289900800002d40740d42c1802c00c19044034080c5a01640e41107000030690400003c12003005801a040c80d40d040c41c843e4a02e8050ba0300803210310907060004000d010703d004d01814240c100c801c0f280280c030000e604000c04520940103440405120701d48800100d82552a8402210811608280103020303115040c61500d40e8840b4a00301c07540060076504800d040e0714480c0c86032a0040040403284da190626019111a03007204402e698144602c0410000488907903140d0200030b250702c25100c0000b0030f8049026102118001018903004030f00400400000d56501c5080a043d9504201c000945491f8010014074500450400a0030103161082032001c0c0010f01c07001d00122071007592020f8844100e07000540d10381c04103961840c05a030000005004d41825640a840c0217901c1e4a03240022968030000680740c8074200c81044045010070006000c246c3e03100301040c00d47d0700502d00c1c68004001036400b0135030700c138203030300c28000c030800b000c5803030304071a03209025 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 797231052 1250 797229802 797229809
    0xc0a0e071e0e03160e0a150306050a06050907090f061d10020c040c11190506191b031a01050406020c1e04024905072106140a240504 58
    0x11641c13039010440820207000124090049407841c00b0001030300c820b055001d45010800c00d9004000c80900e15520b48014210181020340040d86911005c00c00f51074081700548264003596644040c41d01d000400035a405203a0000340401142d0303143e00d1400003030400d911014501c1070360f246c9121002600c04900b4103d5a5a40303a520604041e00c60341c0d600d03440800301d020484001c06076502c808181030a0b000008010400a000c0e030000800288200d4180600e6240c2c400d043c0408103201000c1c0b01c09069454040040c2400300b5070312046680c194465404c40c4800203000e003003003480c00741020400f9660302c0c22420614403d07102e01c00e0707000941d805440f4200c1003500c00f50082d501c550140764040280004490200340c0c10b000344030405121060010540e00300003207102e40d400101190b500150140100500e803600740710030411121b251580381d140003c11000d0040300080c0392802d00710215a420b0703000b901c2070b01c2000c0e41c40b000d00c00c8410020300115042d0418400318050f11140000b924980615403 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 797232302 1250 797231052 797231059
    0xb042403200a030b250905030f0a0203070b0313021f0315060909020f0c07030503070b13170304030e100e030c010c0b07051614010b0411130608090102070609050c0a0e071e0e 76
    0x5103c0c81c16180c00c806d5170019500200c06480780f0030b080d103020503078461081d40080d50681c030001c010030516030a4001140c000113440031844142400e5004104d01003144d102c1d200045c440400c4140d4110340c144107003148103000e014222011442d01c080144811018055140300035130024000e14400c4000c001c842442c460481500d403900e60340d0608980700c5d0040d450540705030f440803000481000541000400f83c0f039000200c405103103101c604007241a08010011030500a800425490550754480c0e19240b80c8000d66440460180580074107041524004040781801005510301d8001181c0144003076002500307150194036415544000c0c0d202908440001d010b00282c4443c030001d03010103420030340031a001a20b092042031030640c0c0b901c0c014450b0107440d8070038000080c014030940f44216006508004050300150800c00305803500021111104e40454041d480103614060381d041403101c15004059807540640d0910307004c4006010200b400c030600040070345681c1500a80e138004c909a58038130601a = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 797233552 1250 797232302 797232361
    0x2e0503071112030106170c03041502040815150a06120c1b0c08121c20040b090315060108040f0201021906050708150d0201030b042403200a030b 63
    0x501d0040b4056000380034840000382c0c4101031941c80d03100d401a4a0290040480e50b601d1991355840341d5444240c40000d4400540d000c1000007507030041082107081c00c1d000035500c0c143d80d0800d520f590b260300d10b004102d14040c105c40b0104102c4103801c401160090320440c000811000c1480030121616200382c0c0d001c0c01107800408001013400a2028464103440d0140c040317070700e125424150380100d030040681e1000403224856074a0783c0c10b1016007000b2030441006071a14020f110340d5041c0b8900e130701300ea0402c940d80c1034081107800803840c08200d88041c400c0e4110401405040090001b0130058000300041c214501c000500e0045910800107865007000c403071404034110720140b4000025090075a04880014032040c04542c0c0500c001507403e244890003440c6003003c0401d5070055010b42000f242c020b9000355680850a00304500204004603984464400d010b0541945060120289070880000c001c20742191405d1b09500c907001a0320607030760844840c050316a64540600b400ca00f45800d40300c440210f070f = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 797234802 1250 797233552 797233573
    0xb030f01020f07030906080408031801110f09181512100534050414011101090317070c0807020f04020c0f01150602060f0f1b030103050c2e05030711 65
    0x160740075083c1244243e0380d014a16903501070403240028295009407003000d0402c0407a541d0300e210ba0a541c484000d0b2000404c920204848806440c0c014100e000034a4400059a480c5440c1001780181c401d0141107141110b0304008207082240c3c440783d41901e0141003034003142c0c030210800300076079941c04031035110600141c50000645078070040360380150100d0900b80303460042040c103e0400c0203000b2450f543c1d90381c10513117448444541c2c00024800c0034180050415902010034007801504201c0b8041c4d03c40c200d189040425078500003400618603010844081901d03000104910122014140c049400289141c0781400090003840b030031091450502c5410741c152403520040d041241000c603641c040c01030440d911a001c0c0e0b1944000c682000140d280540000c100e550300300e40c4103400078280c1101e01c100107001310584849030704c2030300700381c942d648041900c0e2158646a0404100701541c0799030704040000544582003500f194501c640140900440010764540c420000000048924002c6031140c482 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 797236052 1250 797234802 797234827
    0x50607080c0111130501051c020a090e0a05070207081f0b2d010908010908035506081b0111010618050a0506030a08070c031202010e010b041503060b030f0102 69
    0x40202d984d10314140c2d0310030006180d8000c00548813807644101000346400c000014403402940b18a1008049c428001d001103120600d280c000c0f803181504000010380b9041c0090041d2410178140d200728020362021403001d0341b0b512580c11103540418000c0e00811099514000601e05000c01c00500d8514803014440e003240c0704000000c040355030307000c0c0c0391008202d445900403030981e2034011002e884c110040000c40c214140c1068482108850594484e1090b80045141e44941c000514151a81105c1c040341241031400e02099015908003d1420072403246007001e11520f0300c0e50031105040025007c10307840701d81c0e4020300001d606000d10100030810b464443c450103035102c015a010740900c516200002d8100b8201e80300c0d0306c3c000c0b00300070001c0080c1e85190380c072281541d20031036080b20009004240080051101c0404108c01281074002240e0605900c01150840b500c01440354407035400c00c0035808124070203107501010349801107c04140c5e4890103000c240340c8855034280c0101d40d84009603a440c01d05 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 797237302 1250 797236052 797236057
    0x50c090405090705010c17070f0c0f050d030c080a020a050d1d150403120e040f0603030e04150902071b420f0c140708010e16050607080c0111 62
    0x10422035040005864a81820395141298060301d4007280b04128101c002c14070405442c203448032481003403894640c561f6661140848480001ca40400c1882000d01c01d041d01440114060b203415141306581c1001c42e1002469040303510400b800003400014001e5160f1b109104a41410781c000003107909035400c00c1e00040c5400c3c04100c500090300310000c01c0380e005183c640143e50849404040c15804c1c50700310b4661346440d1000c52402c03024001d03507a80030052601da40c0030750030f040550003000062003899400c0141c0400ba101074064465803400c4034409000390fa0000040035070384002401601d6484610f00201085520b42c003180044c0c43c0e060001810406201e071400e20151910341108800c51b581c010b144009007403440712a4081c205000340d540882c4109004620141a4903090043e25082d49800c0c800384407804003c41c054202004c02d02c8010024051131406886807801070600010a00740d00004080c0c1d070052a2040000080304e0341030251400c280c4068042050007005508506990141c859 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 797238552 1250 797237302 797237317
    0x4140c0a020c04060f0b0c070f0b12160215070c050f010509010c0f1209021503040302060f090304030b040b060109030816030e040c02031c0e010903022d1e0709050c 72
    0x18440c03445002e0079810507000300c0c422190507682500c15281071100300060794001e41c4502c2c05074428590300040c64042300440740000c002003c00c40d0759594001e4611004010010300c01c1c040d41603041004909680e0001d00c0b80d0351a103d0034000031a689400341c040f50882c1c0d0602d0007400074800c0c150f40011007076040d4000350003251850000c00c10703a0300c0064255a102d900341309000100d80303882103840d2042c101d0303007009106910051103961541100090803400342c00c240d42c140d006034800010481c14010107200a504594000011030401b46180e6030101c000000410003030080c81a400444c4c401d9000e0241400516807000f0f880b80c030790300d03001d5100d01e1003a600881640000c43c0b221031000c041c1000c0c0700e010410021743e4003a40c90080b9005440360000224881c00031110794650480d03240c02c07001e118550826200c0d50142c03410031140f01100c1c0201000e10301086601042c907140b0003003c44000b464411f10100344610700000210781030103d040c10180e510050055040c1820407614042030801425138 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 797239802 1250 797238552 797238557
    0x90e182a04141003060c1e03020a0f1b060209060904051f060c030815030a050111040e06060f09100201020702030a0f0201111606030e030c121902191104140c0a 70
    0x24140c04030b12210341c920151020401400d040704280b001c2805604110462501401c00101c4000c1102c0401050b10204840ca00001d82c04284045d120742c0c003002e07a503c0b0055920782100c203e1542d64403081000e0301c0700401031405034009080f15140d02c07158151001003800400c20000352510790000950718582c1818402e090b4025000411010b0040481000039601551544402d55520510403050340e40c0304500c65240c032940000c0070008400340203102e18030401640b030944562500c80704038054030000d80800d10907034003807010700d8108180030162000e64a00310b440c1c1401c0744502c0c1c0160700912441d080690540038042d0b0060500105c1300c1101c3c4107504c00c1e03031200a551180a0010344070400310a01408002107070608004140c488d402c136540701d0b80340d80b0a8038500103070040090300d00360303810840a503101c0012550400c0e2070303402d403000110080031313002411170a84940e28030f04040c8564a4010a0300710742c0907105203541c40c1c41d070007010100659406070b045800c01607030340c4031645c0091103034900 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 797241052 1250 797239802 797239811
    0x50402190f081e0c0d0c0f120b090411010507050303010b040303110a0b060f060c06190b0d0816062c07170a0f110d11010f090e182a04 59
    0xa01803165160602c0f540c1a0300c9030b15090505009200c003641c4020b412150f18580c01e0181542c840c0c0c00c1c1c45140c0321106036031200c5880c0030301e03035001a01c0c5604070580000d600746800000b03d1581c40b10040e02d5441940032204058245000c40140d0740da001d503070781c0684144404800440d408000b030004205880c06038440c41c0400380004607840d60b90198050060000c83e082d4081140c9007400545015140d00003040d1904200a440f6250303d481d100310b03a14094485042400b403030300d44092040f000d0641050301c00600d0040c07540c0b6041030030f00c6034011340e4800d1043d1b0502401404816404100c0c01038000216010f0310031180007010348600c400c02c19000700d005114002407086000350416030081100400b030086402107450b4441e070140700740030644d00c204106d0341350300702a56200c1c02d10840600c51606500300500d02c1c1c00051032429003000c202d0520041c0311092003810b44a03103400340d00c2030300a40ea080b11081d441e65202d040c07040300c100f40c101150b140c0f42c4405542c2c1d400211114050002c0d5810803 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 797242302 1250 797241052 797241077
    0x605030c120309150f0d091407060203030106081902030702031b0c0f0d020a03020d0b160801050d0f05070504020f0c060a0504020607020d0c35010c1b02040605040219 73
    0xe10000440261020b620030000c8100380c1c100301400000307070380c010002c2e40e044c0841030501c11403e80c8850011111320340e80e1078541081094120710760000350750100c000d000721030070244040d580f84818029141030205180001c0d0b00800c3c10700440c15080110780e800e548034200210040e41ea50401801c0034107000c00c0c01d031200000400028075440c2400700030440c2c100745032003006102141a10000c01d981020a09501201603169140e102c040c0f00c0c40f540e0481c0003450079003207080b0f00060003206101081803010041183d82d0314640040c041d00d0f006049a40416800d1401c0340c0ba0000c19880660449e0012440000c3c806401e0058114219075030160303041395030f9100d8140110762088030003d500135000d10121002d1705100380c181035100d203c1e1000c000e00c4c03501c036440501042c0c13a80381c10304440c03000104c46241303400d000604440c60800081c02408022100c54015090003100088040009900c080d020203568480c0c00c008020301d80a4021540c802e1a00502d000c8104210844004248101c2000 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 797243552 1250 797242302 797242309
    0x30712050a081b0a030b120706020a0b070203120720010c080109060806041a100e0f07030b090f010e07051b0102090102070e070c0803040c090e010507020d0f050316210605030c 77
    0x190f0703048928200d03e901d00802007030107500400f1101e6200350000d035484200c0742e406508010200241c801a0001c0c50059914500b5191148005103241c0031504103011001000c503040810680040c203504210401c1d50200c84070404040f202c2056644960908100d400350036040801c10341a00d180200a03c10b00f5180e1007410703654401518000e02100a448962a00752000c0003c41e401c8183c4000914102d039484120f0006400165640c00c400c4200905001d15150944901c4044031800e403280202840c0c2000403200003003051213141d00c015108000501c499205da41142d0101c0d025403400e6150259840c1385034001c3d0440d142d5517026100310000464444102504030b0300c100c5255030340e502c04131003590726142c140d08064803c46000e1518800401c00a60f00c0c0526409071200d5000003903a0718040000a1a0001e000307004004c0c400501148026243c0c010304030384e44660f8800d02c002c03040c100f00c3c43c21502551450514031702041c4d281e41e071084d5119990856002c0340d108400700d070154078208041 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 797244802 1250 797243552 797243581
    0x60d14011e090506150408012405090601030c05041e0305010606110307150f020706051e090d030e0c2d0103290f15210423030712050a08 60
    0x291503208071040010044030381940c22855015402402010b40072480c0e4054079034030b0700503400611140e51540709004032411085c65414849001e00204002a0710b41000309a100788058481c5041588ec0d80941c08840c5c01042100c00070049007010050ac0034241c5900c2c00e046e80140021107141d404d04000191300c034400c05052120040950181d0716014050740d4003020320030041e20310340c02143c5404114400d20224805000840e0203590302003000e19020b0016080210080d00a510300030320501485480e1600003a1508600c155080014481d4040e41c160762610b00003481040e448440d5402a42c480480e50542c03000d00a18000c0c40e205012803280198250b070141c10109410348409403e600d81c403401c1c800b82070402230028000d10074009000380800c50800900220384190900040d2400c094480e2144103541c00b13000507401c2450741425625500b0960003000c01004c025242d03410510b00300018001c41d0702d404c0e800a2444501d69241201601d1604110813150200d40c541e8002181c41208064 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 797246052 1250 797244802 797244839
    0x121e0302060c1b06010b0c01150b031902160305071b060e0402031806070e0a05010e0d0204020309100c020a020f010507050601031203060f03050f240f0411060d1401 72
    0x41e25075a5a0400700c0e98031504aa10200101d66102e404078007285014013a0602070001c038050319546892002c43c3e41d0a54805900d0152401c00041c0c042094404540c262600324581040000300d00050030205c4019002d034011103030702c1c1440b2503006001c044d0020001d10303145200f012028003800c0d038403e0203c0072400c14410702001c07800d4050781140c1460309900071540200000c50440385183c03d041c01d1442c01c401180c2803000b24413040045051407400d04241401820240fa0101154030800042001000300540090096401001160002c13104ac06003180b41c1d02044400c01003030000c501c00135660303010789000703a000760002c00540f003039075220b6400c861142e81c2140061000c0e0b4030315910180c0c0044142c089008240d954080407901d0005151200015401030b40204038000c58901c00c90308000e040d6000703001090b094030565580e80d80440e01e9035400201044452070b0faa40314141050500d6212440b01e40c40f08001986090302c10465000030b03010154009040313a1030780c0340d05106002219211 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 797247302 1250 797246052 797246057
    0x51008030304060b1804051515010525020d06090c09090503181f03020310090605100503100e0103050a050c01081e0910050f01090e0d09090b010e0a121e03 68
    0xc0103d111a08000000c1c440500114640316001449220110007540d040356107801050b500b16080004000e03080e00310705c001c8050303007100032035100282452088a500429203481c1402401005984224108031307141c0281003000c9104091030724400400c2040d00407582c1780201500030440d4005881005100e582c42401145896080c00100403504041401e884d03005490700c5a01d000d040d00103107810b17001c0000d9140982c40781480101c580004c642d5802c00d60500380340100402c03903951064500e9161140070300f03000740e4a841da40b1106500444607001100324100003000002003040004a42c48250300410039900b00c0c0c9060401180c4442c000d0341e04807241ca420440004039114100c00a41c1c20140880840d00482d94101104064a0013159078914030341e4030000400c1030082c00c0c00741da40103503070a074007070700b08003079000c002500c951401e004402d061540e90000f1880369006643e0b111720407800520700800f01e40d81d04a40013100d50750860488850365018045a0040c100034a030001c040d5141c0c = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 797248552 1250 797247302 797247307
    0x2a1005060d080c010615050a11010e0705101107140429300c01090b0427020d11130605070b041e0803101d10050909010204031403070605100803 63
    0x60b16440501d80000c084403916540e0303094001400800e8408450801015446103900c030304a4140c0500041c1081002c00c1c5182d041c0785a8a0f0707004e0000c42c156082e91012184500c07010800030b4200c2e81070080180302c02c102d10452201081c130720311108800c0c0980208441c103002440700013442c0c1a01204d02020340014614480454950b4980705208581c0140841d604520f440409000f120b21603043c00403020490b00700c2040c401455034480e41c030002800c1c0c241581403401d8501000607840782d0441405e507070118000303099081c00359200d80454060440d129010b2005c142c0046610320710703038400b10b1a103000710b01d1070000040060140b4181d4042c035801c013060803581c0d41e5a4507100103601c01c201110441c80e841e00038150009020b034024501895401c1404001107082c44401f2800e4941e45100c09040700d0135000308034003085201142c03001d03508252413503240c0341c542d0300800340640102d0b04014401c00400854640c028000000f424000c0d0040100b80400c0d140c1811401d8200d60500500403d038008 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 797249802 1250 797248552 797248579
    0x60a110a080103110f03122101080d03050411030d0305090d0e06040306180b0c0c190f1b1203020f160602060c160215180913030e062a100506 62
    0x40404000e030040001d044000e1146001c030006c0d00b0101d98041003003503103601092803000c091070080c4108440e03a2080514046504000c0b2080d6180450b40c0c0c2c0700708050702e86000a0400480300004c02c140e0501400b207130704000c1489005406440e04440e1106544568040d10440f9031041c5005c070031041029110342c2ca4941541c030b87d040600041d4545c40035408209030007400207004c070721074207100b54101c00d00b4a0300c1c1c1d44042086810800444054014800c0744940030300410103201d440340031741d644100240d20503081c004250414140d10790006a40c50342c0303807445600703058000c1200034187d0301d4682921f000703155400840701001494001c1e440160f100300c0000d0400c404420040481c50504002c00e01c120000d81d000a014070941414070401c11008114070408a220500e1404161400c4500072242d00c0e01c403501c0800d98440c02d8000d02040f034402c00400061b2504030448022071040070184030340c1c800c18801031030100c000c0c032a00315007889000d43e1481c0010702072041500a10f070007400d0a04205e507 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 797251052 1250 797249802 797249813
    0x71a071e14061603150e090706030f0618020a020708010f0e06010e010e0f100b041d0f0c03070f0e10110d02060115110309040e060a0e150604020a050705060702060a110a080103 77
    0x20701105c040d8202e00403801181c00104040064130074603150b40148407160408ca002401d54000000c000360407400e000d424461140c020001a03021840800016202c03201620202d1411580c2d500086040d4604070b08400d0094543d000280c01001610440785166640c02110031540024172500c4130350542c6034040f483c14420007820a4120205100c072002090f2181c0e0500182d500c568480112490b40803100000c5401500d902d951002102c00c0c40c02c1140f906050300010b610004000714108080d0100d1040c0450054900c1c01e541c00c1c0280c540003503034940c1c05024000b002501c00407a00340c03040303600e551a21840040c00714142d84210700b40000d24051110140c501040c04411061140801d00500c1429203e80c881c00002d055040001e10741070406203501012288100c0d0100300c0383d0031109038610780814001030150030510950b0700583e0749154a40031030385801601001040c6004007018841e21640c00601d1074014201c12608200e14030305006030050601c61b41801602040046004101040 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 797252302 1250 797251052 797251061
    0xb040c050f1614060906011a18060904060321030b101205060105090409150f0b0f10091509051008280f020d060311030a020102071a071e14061603 64
    0x40c4241400700c1c03d0409aa900e50502d401202e01289030ba0200004000088000d030142c4080584c1800b16843c0c880c841104030380106900b4101d42c000c00c4005030500c030341c0d207603a0305c41c200443d0003107147c540140243c024228806041105040001e0030b00302c2c0700d9a240b622420078501250a40c0b81e0365980b210b4002040050803008100380d040c41002d00210b1140c6d00d8174098000694440c0d51300c04d8000c06041c5042c0308503800303010501c000624240d010491910381280340a020070041764000c1c280d0550013011503000381c8039040341034004c05180352089115004400e44081e54012280d101200100c104201d50004003110f40105202c142c0403400c40c0919144540001c82900d0480880c60a07a4948020103980c0a9110201c400742c1c0c83d4000c00510100c40c850401c1d0b450110042c005002107600000d41c1c1720741d80c1c0980d8003040800c0b000c0c440ea2a442c0345c11285100c1d444004500e203800440041c03100c21004540680e50b042d03e00e54900030201011130220300c5414180f601c0030aa00d210b180807802007 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 797253552 1250 797252302 797252347
    0xc0510051908060a03240e0a06060f0b04031104060801060e0a0b060310121b0f081501030c0612021201030b01030308090c0307060e121603051c0504060e0f130b040c050f 74
    0x800c801b04020095900c1c00360043e48035040006060503034540c50000f0454507a54000484a003d200302440410010030440d01180c0d008200490000740041c001030050016a1144c0820b601e04a000030f180f003030070409148140840d91040141c0d02045080c400c2c1480f0490703000345080b8114805110809140140212a5010b080d40040e960040b045000340101c40b80c00c070800d00141c4001c01c11100e00e082000701c00520591101c00d0440d451036903020300b10012405440240141c1160108540c022541941c02e00c000d03c1c4c0c04030071030b03503500d0620441c690405e010540004201c480010420715000406154002e0702500619125107412012038a0b603174401c00155000d034600c10144e690320b10030000c50380381d08107108488100d140703103150891070001d1410301d0a030403681300e02c80e016050750041306490031140d440c141140740d010990b00142c10303820984140703544086450681420300b282a4010301d080031082d14200322026107031000b40c48a00510211082d440d0080000d4224041e01c14001c4401 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 797254802 1250 797253552 797253593
    0x30216030507030c1b1502120702010e01051c05070e03030c06010b0a1704080405040c1803110406080f0a120e0307050d050f07031b0f0315090c0510051908060a03 71
    0x1100390985d13600325100548800b4000704240a2000e002c070f401c01c8045886910311600007814002c2c1d10b65810200c0c0c1c019414080e051182900520000c2d90082003210107125440b401043c01c14240420340004110a850010002c0c0c1d400740350380d016050000450b041c016036030004080d20382c680402c20840ea48403183d00400c00c551400340e0342e1181414503c0728007c1d4032a9200e035407160b00341010301c0b04a030030342400182007000700a00312154003400c031304680a40303403c12000544030100d240420080d1800fa8400c448030305c200170401110143c045412451a8443c0500740c16012032008121100001400050780c1600b006008012500d03100b40450042c521a90503039800c0800002018140061030b442541c2c40054480c1c2c01c03060780030309110030b0050051944a825110300715114001d440c200304403640891ba83c1e0790101d02c10321208958200081500038505210a18449070080064015280c01c0c2500c600400013212028000d4111510544c80501000e082902e1a113503c0c20300c580929107800b0 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 797256052 1250 797254802 797254817
    0x721050603030405030115030210140313020d0f03020c01023003060a050d050a0c08010c05090603040c0314070501031b021f02070c2c0708060d0c0e0f041203021603050703 75
    0x4c003a02c0078080c0b4254183c0580340150304610314014407518500f2000b0000c00c105251082c0c071403e56211040c3ca412070244a0a00f654481c00e00c0420845100e04001410740b002402c1148100341d40003032880c4020000303030f00f561212805070741031040d5040307001031003003080b050100e24142c004d41c540d0141d81e224100802280c455907640d8042484050200025540317504100c80c842e0900000e00540d2004180c0000200045c10303000c440105180144030403e03120f40000408107080c4400b94440401031074100c0460744400020b103d00554608840c403540c1e0100b0b05118400c4079100c911030044040b216260003800407035400050701060f036008001c2107800350358203000d00303804a150801e0f40005000346c41c616110548401d014a00700340303003881008000703c0910040000c1581d00c01c50745600003005941071030722040e15182c4050342c1e04440d0054096152a1410044202c0c810301c03269000d58020000b402d804620602c0440613881494030b4542200c410700000000240301e1001000064000e180010 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 797257302 1250 797256052 797256059
    0xd090507090501060509030615090f07030906060801020318030301030f02150c030a23190810090908030703202d0d0b01090506120c030a02041a040e07210506030304 72
    0x700325803083c1c20050001d01e000c518a0143d040801000e6048809081c40c40000446800010040d040050040e085041035502007203c49000c1d070040040301d9406103083c010745480310ba0440c000c0d00112000a007502e04140c0700740200e440881160305981e00001c400f03a0108031034003403010386600080c024440c100d040003203643c608028005031200e0b02841c5d65405c1d80d0300300f805900030071903d060390380d909851041014915200b03901c00e205003608010704017411207070350b11f01900d010104158405040582032010031410441c4110084d440786400d41c070704001c00d500703500c1c1070b100f0283c1d5588060001c400c100300f00b4864015989011880110b10f42610340050503401e200030954129074952150661a000305504960f08448508003070081654040e0804044010b4141030680c050b11503840b031480000403c402c0e440b240c04407005803880484901404030000003103411580644035000c1541054404162460700c1083c07542d140b00e58203c0045001e059500c01040209030262138190325200420002 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 797258552 1250 797257302 797257319
    0x1a090f0c0f0706060e1b0a1805190e250315050d050f01050c03090a1b0b030c1902030405060a0503150a090f06090b030d05030403021011190c0203030d090507 69
    0x2e188451041c2d4021880902c2c1c0b01c00070f035075102d024001510071055401d1303d0301c000c0c1c0700409803a00001507140114803841c1ca08030b1003d500740c050304100e40100c0003840f010041101082c0940850b20507651094039987c5005014a20203038003010441041002252155103600c6a0445242c080302c01156000840d9290006400c030b241e641001c69160300300c0181204540b40a01c00c2c181e0042c40e110070140f0b1442d0400030503460b44001c0300d0050003d80701c0c2c901d0f111071422141c092809052680c0b185541e0b41008621090b4940006249040c007101403c094003120b440070090fa011280064585410070b408160103544540000700f82001d4008101a4510790741c1d5000b01e0040103005141c800114034511502c1d00c0d00380d48060b000503101d00c0c1840f14248094500090b14103140c0070501e402ca840c0e443d1450100c0c02c0c2003404104020340c504200b01c03c4080140d102c014002030403c184090b00642c0c400c1001d585803000800b010390b040e0400c0c03180d4100344585800912402d40703d0003d9412403a02c90a00 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 797259802 1250 797258552 797258557
    0x1718240f190c05060f0402011407060905120705071703030f280f14010305030403140f010e011a010f0c0215070b040b0426041a0c0316061a090f0c0f 65
    0x9600042c03400101c0c4082c81070502c210364000d0281210b003030091900d600060618030550302251503000c4000380f8002400b2071503004450702c0e6405415204401c4d095000000c15400c40001998240503c0c0300010301211740c91204480c0742c42040141d429540c0301d030404105490010b04070740c803006040d00d020540c104c9020148002c182a00400208001c00c0003400044a40e0741c21000c038a00d040b20010300c04210004140c43c00caa034400d0342c0e802c81d547c0000a103030400042da44078420795030901c0e07a0041c910741c041d04481030b032010000e00c21020402400044070640445043ca201007001c1d81071500c054101054000d4550101f075007514a0001155a45041194112000e0300c0ba20074201c284000c2128030101415075010340401d00080c061241443d074075910541c840c80d84071196816000c0110b20301102680c070301031441829a51560401138605642c135060243c112003180c0360484040c0340345484c501144e040c01016000340c0702d558842c02c0069800d00d001d4024147c140c001d02543c030343c0b0400c4000 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 797261052 1250 797259802 797259847
    0x50d020d20210601050918060942060703050c3d06050607030302030a0506041104060c0c090e0f101e090f1718240f 51
    0x203000501c1003501012a880c0e951103480c000302081c04018500034144640302c00400d14210501806030390301c801005a1704c0380320742c40310f540c0c0250440c01c94200c40c0000c0c040c0c0314454001a90081510b0307484100004484030702112803001803004501940c0342c882002c0c0c2c080080c6041030702030b00c950702c003450000702d0030303081903134110002600010a042d0706042402415489c02c440c104900d003881c2100c103015601034840d5140360100724004809150082240c00200003802e0140071b4507600c07051818000c001e9442220310581c3d642c10400031a90710304051203403410310300070890040c0c00c19080420844008880c9a030554030305105200100d5849035621481a07180700c003c005000c0518102051400c121805a5982800b03142058480d508008041d4684045c0c4d6601800038083c1c5180ca0000c21048003114054102d810701280340518401c89001441d45140201907040340125203c00c024201104c00c2c1036810b06c117032800040d945081140c0142c68001c8520b20100d04200c41200c0301400326850a0 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 797262302 1250 797261052 797261077
    0x5070302100e070306151d090a020a0e0a2009100203091306150503070503010504050c0c0114091b060703050a1b080702010905040b0d080d1103040c0812120c0a050d02 73
    0x500c04c008014035482022151954103001580041c5070080d0460083d059041d00c603102e81c8000002848070300248845003800342d0003041c01d009981c0f51a00480206411105891040d150100054951003410050b880c055010030201e03250030100420712103c03c00f5107040806501c0140015221642c0d03910312072140704817218001541614010145e80240420175808003802001c0090040081c1d0001c100c2e410b469056070041079640790a2203041d00ba00c11141c2084855192202c58100414050b070900e0081c040c2008950206031000001c1c5034004d96019407a510003410085030b8002130003480649003401349418002c0ca01e811500020348040c04c2c611049a825100083c55800c6681116070400130301026036040240200300000308081c1d003042980039081c0013021600927000f0354280c001c1004030006000b40c5803641401e00d006c00410546018550460064226808518030701d5800c2d945103040107007900249031681c4034a0341040d402403103400d00700902000102e59286a42c0000c141c100e2450 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 797263552 1250 797262302 797262313
    0x30a0b011203090611071413050403110601140904060b03010905060a02040f1203020c0411040b070b0f0702010b030304151206140f010207053609060a0c0804030f05070302100e 77
    0x1803030018844502904201c084c0024090036117100080080e802c0d0580301801141e080000302c8000240c0600842401c03000850b0404003000105644941c40c882e52070017481c100c40c41641c0324025840807490401007603403c50b40401c00680801c1180d0401032980da400390000400303107180c2e01d0351400c1040403100b4420640d000202000b075410780c4c0c3c0c1ca40c0020310703450f00180740200d0705940094440303101205491149803101c001102e1030500d00d044a005001411620380c2e1440d05242120140d4401c4500100c0c11544c1030005081c01d0040c081c2074940710004014515141c18134009019041118000200f0012025082049500c00e8401c4002030a50350100300c0d40b191000f41001051080c04580134110740040004200d103440300340f42d0400c2a5010070301c00d50340103a1b85a80706403200c1e80055140201000c0c00500510080c041401401980c0d0900240038840320400290307001c40302510000d000507000001c80306254810400741510310710a205030b03941041440031040903100c95200d901304a4101 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 797264802 1250 797263552 797263589
    0x608100b040216210c080301090218060a1107050d020105040b0714160e090c1e04020c0d0f0212180405040f141b01170a0507180801050a1a09070e030a0b01 68
    0x10410305105070703031345c600082c07403299035039540503140010303c180c02d401900801c1da0f40c40d6042d00c440c500f01040c1c003d85440e858010018006002030500c40e4034842034012144003156a040c4101c008020a4060712500e180901d040980102588501c80589240201850b5594402800d008080d85840c45095801c05c840c00e19070460b0034020064400d40d0b0540c00074140400c3e6031220440e000c60000345035107402d9681099004a000303840344540c502c4441c0281881401d410781c1244180c8140c85d038907070072a850a03c40c151f8441c0b4604c914454204018880661071240c0e141540015510070320030004540680b1255039500c00d1001107100501041e001050401b01c10003111044104850007440e2a8010002d054103510b66444050b0140c40d4068032200011145400340b100e208c2c00401d2026640780071984d941d11a0300030f140070b0303902d00c00302c906004185003004000f0202c06040340004104440d1030b19001c40035502c480d0011207403a010701400072030801240b00f00004d00d000b04056049074504104 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 797266052 1250 797264802 797264843
    0x403080411010503070806010f0215130501110a022e050a0501060f030b0a170705090c0c0610030819120c020303060f01090e0c0304020411190e01030608100b040216 72
    0x50030107503030420005204020fa210341c82005903810100030300340607454600010f4200e0402002d1100c1c41c4d04017802c01e090104000090b0000003250f8002d0000b08068840030448a0403032240500c42c0300140d018100c140031b03680c1e03400041c3c01556082c603408020314201811400c10b4540844190781400d9072000100b0100d50005180c0c0c080310443c2c034003003042e0801d0074002010140c0700d0054140326660501c020103c200c042051002424008010b4038003894074015103803540d400900e40c22440d005400c041600d404a01384c50300d060f00d500544907818030703160ba80000f643da002101e0701d0013001612004210124040d1040758072201c01ca502550b520f00c1e00b4018080305008418981c0e04000403030400304503d0507045040c1c3e130484119584143d0700d0700c540c00050080c09054420003189400000c001c0c003110b0500d10b00401c041120749075211100030100040d0100c1300e142c41441c1c05508511000401500f4a80c400d03100c04000800040c2000650f0b0b11070b2856032810f600407101a414007021005140c17 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 797267302 1250 797266052 797266073
    0x2071e051e0102010e0105130b2707031110051b0111040602010605091008070506070503091e091803033c06090a05130209091c0203030a15080a080f0f0304030804 71
    0x400c0f40000d005c80e0030030942c5d00c123200d581e601015144501e2040400c44080801112010310710801901c9104400104501501c0305a80d100c102c1d00c0e00160056030081d0b04018a104c8000c4009031100d60a0450800d00d00408584c031b92803000c081d550341c05a44030710301000d074041d04c090425540001811420042030100c020405440c0c0c800340e42092800308210b06002900b0b00036074005460440c0c41e8111450180e1441c016494030b140e000c20b01c410072140140441010065007841214542e086d80c031007511840d00b0003b82c0b50000340720342040000a030000040c1e5104030345034a54103020340b10541d298422803491009400f100a11030401c00900096141480a1682040010a08102d94107100c0c00000d40402a404020b00500c1101d0001304898000e0145259050f03200407024a4523070740384002034070b81c1d1085840d8200305103003a1550402221440c40c0b1300c10b542549008005c100c2c0a40c0300c80d081900a43c3d1610101d00b4104091010382000c01c001e14003480c800e4940f80e081d0f04140c42d0021811 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 797268552 1250 797267302 797267321
    0x1c1817210d0c140309061e130b19060e09120a090e04031407060b03060711060c070212070e0a14040807020411040506070302061f0602071e051e010201 66
    0x203440940c1080250240440340c0c00c4040490000d061401c6000503288450420408140301c0383c04420001c800d4004241c842c800c07103110206084600100758068892030064840d048465405034114001840825599400c40c46040101c001c42e03144038445d00540320030760030082c4d100039000180250707084100202c0c0302a080908019007051032068000b070420780301d485059405a80301020600f4507014500c0300c480818000301d110b641e2005410150098482810028081e1054100040b90b070740c810542d0103801003561000c2d1071544c448488041d182d400c501d40c21383e40041c01504404119204206210007441c10405807507141ca0544075804c12034440e12802d0b20003030480d804000002e41d039642142c1d45640d04440000390303e802581800c040340600c0e0401a0007610000f510014035800007040ca10a81c06050714031900c201260003005481101d2294501580c0441400d10580c90700030702d40540540c034030403030b01d00581e9554002000110141a0030741100030071132200205590a005d0f14242 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 797269802 1250 797268552 797268583
    0xc070803030708040b130c0b0c0c01140901030f0b090916050103060e06040c0c0605090309190605040312050904061701050a0b0f1c170c0601080a051c1817 68
    0x3507190504000d41500c0f002003000b010b50461070006040c64040c1d2004282641c0c01149680816445034102410b42e40040680f401d54403c20441001e00d610030065400740308402c801050030034101e680150050200c501e11444400d40f103115580103619962100c911801c8a00001e1070000c0400300b51070000d180c01c1d08801d04240c1010400d200000c0c0c000816504610261400604640400c00840c0c4440707085000810641c1800b050050701071000000d828000002c448142000d080c9000d41c0000410718811342c404544144410804980c02d100507001000c4a41007035854140e407a07001404407a00d43e0450b166101e90000008460002441501c2c2d1007006000104000b810390000159445099a08a8482c50455803401c000714052100c0314002e41d4004181d0066880528100d031413a0001210100c2610810000081e5001d0010700c00755880c1c1c01c10054005404042c0302d000424991a00303480600c810290505800c100c010703000e00013041080001c040e52800c29500d41c0c00e144400e24407050313 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 797271052 1250 797269802 797269807
    0x40c0509060c010c17100e04080909010306050105010f03060f05011404030803240f240d0e03030727060e040b0603090a0501050a090201090902180607050f0d051615060801110c070803 80
    0x42c0c100d00b5160400a4604500e5014616234991405404c940f04686096400c80071081c000030070892942c1001c1d06072102600c0d000b0043d0310612003102151300c940b044000e443c01d2600100701650042e41d004641d04103860b0341c5031919407170f502c44840b10303802034a05590383e007a5540c01811008100030f000080510450302c0b80090b440300f03c0040c21240c2c607000c01481e0812511345042c060410b0070101c5103000d811503802d00040300f00c801900d490790821201a4041a442d50b00384448042c0740b600765851080c440c2d01140b0540c02c141e4200c8114130407401c0e0f541c119a07540d81c1004d80d50750340806180b2605030180100340c0041d00303103006420b48d240a00a001c0301401c044034900142c1e00715200809440c0d100100689070202e2400c681e40b40c00d691001207030006000902002808008201420503074250381c1201c3c0c541e1100c210880d42845984620540d00219030403090024603082c1d40e50720a4000f01ca004158103840b000e02d1800c50759011340100500000003010310f5051410f10084006104004c0510b0 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 797272302 1250 797271052 797271061
    0x1c02060a0612150506132a0201050108070608280504061b0e0607020d0605070507030306061b2004020d0b0f0604060f200307080a1b0809040c0509060c010c17 69
    0x4512140b01c140e1a103a491300300050f156200d44070219039014040d2410300a03060200080001c1c0d55162210107403901518010144440c01405464102d130741c2c040c02011041d140c0746049414420103003005040c200540070324001c1c04901d0100240b40012120000341300e00340b900d003a808940d0442c2d1200c0070403829070b5004802036005280026a14400d0301c03010b586544620000380405143c40000f4040c0c2d14290910107800d83c0310b8058000a03109403000c02540b602c4d0342003544d11000c0301101100881551404000145941c0200b01302d5a94000000050062120005040e80c000b1130a001c041c0ba5038100e5040b462030900d0075042d140307409549280c980360809400800b10701824002c20140403d00b500d15082102c030401800008a040d82940d0b11000c55240402c1c00313a00c04203090b0000b0304400c103031008903410941c06c4a1065401440c0e14502108642030002915a281d9002c080c4601440f11002a40710003004060503030030717000001503003503010304054a42d4040400c10600c40312844d00300b0 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 797273552 1250 797272302 797272313
    0x6130e03031311030609031e09031f09051c020705040e060f090a050a031e0e0d0210021203040f021203030c04330c030e12031b1c02060a0612 62
    0x60750400c60104180b610040346042c01c2e40a400921201601031080400301300000c000032001c2d0071600b4062804e0b04050712034901241581c051503044507403580107035540001000842c081900c46030103421003c1120604c1c1e031541d6040200c01052500306a07041588000025418050300f0003418040b40c04201c0989900b076041d07952900102101002610030022901d006000c201001096038410100c0d0721180300d500d03004051513001079601551344001c000000915000305200804003401500b88000c8081c103808201e03100412418100540c061140c1c070800070601c0d500150310583c06104120f44112443c8140200300d1400042400c42ea0018821b00c05449002012a82118071160000000c9200b520f5400d0300c0142c0e0b0b01112003c041e0b40d000821002c6c2c1c00000254115000b81c45010713051006100348038203030300243c511405a4004110f1706c024507110800d103003540e0311940d00701c921840b04000d00160002025a844016134800d00802061201601810014266441d20300d0007510455486 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 797274802 1250 797273552 797273557
    0xa060b0301050907021e070e01050d0f02041113031a0705032205071d06330d14131b030804030602030403270e0f09071211130506130e03 60
    0x9151082c10307814041404c05100b0000a00808448055006510508600141e6810301c907c03a0750401e032215400000c072450441d5520940a0f008941c80d0481110f43d4200001484003c4500312070304070600600000d0808002c02001851040309551b20310408560f840c0c429200003070900c01003000070002c10007121900d01a08801120b444000c2c600502645046810884c46401600031078402c9003843c0603000d001402280180016140c800750010404000511380701c8940d00d404000289a1803031085c2d13001d410040520340e0001a00003103c1c0341d8507a031561031610070b4407034600c0c08408105800c01d0000c10f44007203030070242c0d0f203044140c140d10f1a45c074a0f01600581c40040c1c40c06601100141c140340c001d0035070b040b44141c16803007020208010a0610110141e0707016a0301e011030900000f840d40c400c519600c0d070213041002d0051100c1482c08800017140740000c3c0c0219640924030f0307415a019103540c450b03154207044521001c00e051401c002803029180b1050101082036007041c1107285600d802004 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 797276052 1250 797274802 797274809
    0x50a031107030b0c0d0e0c06090105070f1509122a05010209030a03032924041a07140c2103160506040201140301030b130326040b0a060b0301 62
    0x620036060103100d10128240022036001030301c208001d40c100884509140028000e81604030420040f888040107519510000481c049800100801080305c0a60048001d05100384c8a50349280b00b80b2050b0b030b11041400140c1e08042003440e220a2001c0400134120070300d0704003202c80c3c500341030708402540c29004081280c4040200541c8103007040f2003804000e404840b000748018048803a2030b059482c0060003070810407000040a402114820400000017480c0d401e0218000d0400c181000c801e110960044400f0002c280d40c0c030b00403c00011201410480242e65581441185071500b1072800d08070000c900e401c9852989810001c04440e04d0341d1204500301c1e008152011f0042c50a481e080803a144d440742c2540307501e40c4142125240104000001c00d035204910070ba80728031280c0b04a81109004e80001e000050030035045c80005003d0f5540070f2441503009009280505004c000f0040d841c0c40c5032039945840040d031703090400700414444080c51003900200010030410040e46003070b0261a540c0010302 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 797277302 1250 797276052 797276057
    0x30304031206080d08010905240f04151e062c040e0a0c03050706020102070c0603110412080a0801051f0e0a050301110d0c05070b0403030213030c06090e13050a03 71
    0x340500c101c11540110302810708401180e851030384064002d44201002d100b403d08041c2442c001a0f081e2143d1400c21046c3e448001c1104401c00c0510308216810505190780f5400c241d07183d0388031075501000e802810040000008094100b007501c113041c0410329054000400744154030345520030610b012200c03c400e500b05107400d42410304200700081c0150120801d41c1c28540304d8840d5010501980c00c00c01c40c00c40c0d2040741100c1490f641d40d00c080e401e074080c01138081d101c0d40c0070038030410801d8000d40101d180c0f907041072041480e1548402c0b002c1d02c01907030301c0002d850403000428001d484680080519001d8801124074007100424001c084444014408c0706008100c40c2007100a455105d10240c2005050000c0c000d10000c0b2010764801e80582148600b065810b04046407420018000c0d007c440c01d054105881c0000c82d556500c0035030280d445203c3c00e0807031420001001001c181030001d014040c04040d030341e000d0003901e400040c2c0b00c1c41e000030300112500301d10881031100007a8002540b0002e6035050 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 797278552 1250 797277302 797277317
    0x40807081c0302090f040e0f0709060326040503010c05040e06090411060a0215040308061e0102070b0c0307060c020304091d0d0809100207060b01121a01110a200f0904030203030403 79
    0x5004502d9260b092410a038001d4103140146441f08070100d07410040c28098000c540050f07581c0c81035501a210303140301c0034118140c480160100c100030000c14003040000c001445250503a00c3c0c011030300310f5441c21004000140c0c08a824080b03204403200d04d03508190125140401c0d420103458003000c80d000c0d6001c0328072506001500407640750007400b41c110402c0381c031000c0c45400d10305070402829a42d4101c5084d4491401d0381040991004000388401000034103030700820445080c0b566030681a41308403024a503602c800e11031300300010843d014440d45645141c1c09180c965180030380d80c7d4141c951901ca28603a01001c9000c50400b05c00000f4510f01140701841d090095480c2d90103440c0c104080e5a5010130100d0001610109128041e08102985603086c3e8a60321203420155000e000c881000d8980340da08020380f41008070310341c4240c2c00e441840c01490155400c0f0030390381d51200038107110510000e05810716403a07480c500340f40803445a4103540c1c1c290354101507071405a90003522440010130050502128 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 797279802 1250 797278552 797278567
    0xf03020a030608060a0e1516030504020103060e1f080304030f020904170d1a06090102060708061c0b01090605010311030118020f040e040215090f060d11030c040807081c0302 76
    0x182e00110001c00d101c3c0141d61040c01c0c0103003900301a10107100010030034400c1c076510860449120540521604000d02c10440d0a09540e400f00c0140c00b014000380d0405da00d507240442d0845100d50420b0080f03803091101c0d0f030118000c0495280100080e0310440081d0802d100400103e072039144110b002960440700e40b080c41d0350b01c0c68070450008504c11040c1c03c4020129105041042c2d81e4040b10000c0d2802000034020500c0100700000d80c82800d540c6801a04007402290310705004a03403282c0c108100030044003071440100402d04150414038000d9407015448030042201c5126445090b003d08030a103403d0040c9803100001c0c502030b10041c8202401e0f000b010504520700c00711641a104024070f80340d00c1c56940c0b80c0c1c0e022079407402501910141c0c800c0c241c10185003041c500c0b1000f211000c40015192841c01d80100d020410260405082c0520194940300304001f4560361100031403241c0114052180c4440c2425825450030f400c0e0741064001d40d00200380e59029540c4120005100950b619000d030380c6620 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 797281052 1250 797279802 797279807
    0x9050607050106360c09030b06030f010516260121020409320712021315062304090f0b03070f1d010e0c0702030708071203090602030a0f03020a 63
    0x116030304c45a030340740000d40401c0220004060588450b1561030000c80d0040b0492940340440d5150f001000118250020030070001e9031900005900240080a8a0446140c41c20460075624112956506260f500640c001c515400c0300003c41c0b407901c0e007800448865139400500b9603007001809840d05524940c1c06214a00c5500b50802d0241980a80144011070b15440c0881e00c0e00d9180700b19024010480300328100c2c1d422100741c113810920303c07600200061858071218004c105c00c0c2880a03a00710360000400301e500c1125000f01030308180000c000c4070302c1524010303004011101001c00c81c0b078000c1031400d2010f00c1c000c0c100252030985024100016084013021903010040540c9442d1a805001701c1e00d0010301042c5201548048441d40c80d21100c3c105028540815204800d000f50300c100c1109001107504040ca550180030703450b1018084840c000d40301d5241c90315043d2107500140440c1f01d5103002000b0035911542c1b15009121034002181840c05441016041d02c909070040e07403c040c2d022a45c2c050452 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 797282302 1250 797281052 797281061
    0x2190509150c0a0c05240a0c06140106110a030804110109090f050106030605010906091e080a081c0b0d02010c0c090e03071b0509011a0f0301170f06010501090506070501 74
    0x28558210b0707a80c000c00a0090300c403a200b21050b1040150803c00040310300b008a1000000b14054441e80303481c0820381c4040400360010150b02080003605102c0c41c1c001103007072042c04a414a11000300040c2c2d1314044e0001c1c2107440c8007130f81c0000c64002221010000c5d03001080303d500540d01000c0c8407070804030900126074002c00390384505507240c1000c00080c4505c1240d40143d042e10103076a418084142c50b440195083c9072180300706400642d13003070303000c2181e2a44284c558140002650030407407065921840d852404820490a589404000640480740350301c18000207888280404203100780e881c43e000082c0c4001000002906000c805907010042100440d4071801400c91000c04000007041180320b113540e6040b602044501c040d52001c4000c07a810510401030458000401d550b203168241100c808a410300a119000110f8060004550514644000d18007a020013200e1125010010f801140307032440805950340c040d00030078018005070761300c2041142904d000340c1c1c18559540302c601d0f0060041 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 797283552 1250 797282302 797282329
    0xc0a0807050d053f13120e030d11011d16060903110108061302030a23040c060f0e060a050d1406150a02330a1a04090501021303030e100302190509 64
    0x40e2404000c1201d800004c0f05c0b114107960080c5500c51186581c100103581d040349940f411545a070100c40a003003004e2107200003030348d5017507080e00120710080c2c102c140e40707404020080003140316004421070000805141455000414691505d080c1e01803842d01e0354100c01d501d5028250400074a80000740c80d94444000000820290180842d5285803101d0420020a044110b00340c840e611700d203a205111403d80c40c101e0089800402c190b07041458000203443c2c6501d1426010103215900c1d80f500101d5a41030f02816000005840301c036681c4070602c00d075100b00d80c034000c00c4141c1014044180001034890b20f4810346003000c059081591070300c05a01c141d183c1000b902581610340b1079a100000480080103441420042d00c00c50717005941c42d55403214042d5400c0c0d4212801900f0100820070891034160000e4111034014030006181680070b007030100300f03d4260340058000c19054540d50722507061229007820014503d00e000c50030010303c10803004000070468030700341c104500030645007003d035102d03030000101 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 797284802 1250 797283552 797283667
    0x1406090a111302160b1806040203030a0c020a09020a0201050609060d0c030602090103020c030c030a020d020f064c081605090c130806060102010614090f040303020c0a0807050d05 78
    0x200549280c40201a4406c40e5042c9851404c1300da43d140c20790001548a02641d4020702960910345602c5046403480c460810583c1d11020807a40000c0d0200940300400d4405226400852540b60040a125603020084d01d164000c0d00740f1103c18002c6500c3c0844101642e034021400b50f070312008100120003030b006006040242e8000014000c4070710070700100900b803460064087c0c44041a51940590b1580ba03021408006604610000303106008450603000030010b40908007500d003100001c807020301d541d041c905004d801100109011500e038030b0303c4400c80107080e400b00604040c0d921416850b682d00852207090302443c401004540c0c051a04819a0036130821140200221544d4104031503481005a6a032030165190180106442c080501e01e11000103014114800c1511500e00704290480000c0050303040590038011401c035001c1c00d00c0400340740d50242c040251203030524240b1900b0a003d400b00c1000344401001030000c17003100c03d240103844003000300c44442c0c580300c0e1003240c1d0848804085c00415 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 797286052 1250 797284802 797284837
    0xb0d021f02030405030d080105030d0519050319020d090507080f0d0c0204090503130f0801140f07030b1f022b390605060a0e060616020a031406090a111302 68
    0x48040d800f03a1f40c1c60494a0480451710200c5054100381e1ba180316081c41da440000d42000c00b040640d028078000d64000b4002500400d200100707890507800ca800202c03001007495202c250240500034100b190f10040d0000030050410071940d80595551814110341c640e051026003a20300040d907070b403a8420110550420252a550200c0d0396030700c0400c1c1400e0041c81446a41140301007045801407190610303c650310580d10801c0e44030f02418074281da5004114104150700c44800ca422a180d80c0070014007104c02021660558424800c040d080400407121698414070700b2164000f078407108a90068050346a007048401840c00e0301191143d4441204044615840401011000c18404084010f03440c0280010001c035182c140130000f03409214800d07150548141c001044c02c074a0902c005101080341100200b002001550103d141d03119540c1c8242c1d201494000801c000740f50500c0000c0e44035400ca0702500040b802a5a1300c8074900941c8a55030254960700520700307406e10f05a04840003203030410020b10 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 797287302 1250 797286052 797286073
    0x70f08030a08070201091e0f061e0e063c010f06032304020f03030c010e010b10080903030c030c0f030a0605040f0606081501030b09090a060b0d021f0203040503 70
    0x55490303004529020000b544a0005240e40c0e1040c8540c07400b281d8000c0d01100039024107281c89200b24201182503c90700e00903484100010520301c500d081100040c200d51901c1080303c126941200c5c0d1140b0804c1ca550028010070502e54100d1250188401c807000c91070001c2540f10380d01c034003a10700966603000006148400852100040c02c490340844415550a105044500350b4200d0781c56040e1180c81c03000e00c0d0742c3d0042130061400010240e0088006001c990404d01305d00e5425096899808581c00c03203955680140070035040c001e8544058040318184484207040c4000030316501d110040080301c80750b50120200b45c030100310a00719a45100d00040e00340c6c407410702b40c89804c000c007c644200c602c10352810f2200c1010301003c1c05140f08447d500e85448045542e0003500100c5004081011810541e075a140181207580f0b42c031b00c590042d001d40d0010302101c807a51410008590004424500c40d000d170310b0ba440700507610507580300802c00c0b149040c580b220400041c20381c9940900d41040d5418010b550540 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 797288552 1250 797287302 797287319
    0x72a0516030b0f010f06050a0324030c030c0e0f07080601030902040507020616032903010e01092a14010e0a08190309091a0607080f0d05010302010210050c0406030905070f 75
    0x2da00445140024043d5a40e0303a18100461900341e02c6a030700400c0040c080300703103d580207604c0180790070214070441e20004240800c01c0d00142c0c07540c100b189c444e1341c090317020b000b4002608440f030040c00e1071041102c044e05100140311031000300284888108034189001520030b902c240c21102c101075024009104a0603c0c44000c0d4507480700b102c060312044005070158104511074002c202c1c07180182003010b50440700d1a030212012650100406406640342c41d640c0c000c407082481000b81d10750040c51446caa404000e0310703100d03003c00d14a403000704c079010031a014000c0462012801e12550024207200c140c03002c001001c02d42e0000180d0029a0302d0145030700e5a209031581100710f0210b140310b9a85c0c904140d40310b00c40203040b61004040842200810300c0790300d0603420300c3e400410041d40240301e8107081403002c8440028540c03000d9440e9903845d807214010000c40d6010014810b00e245024410300c840c1c070705003459042a004510a0004040d21260b840040c02001c1c407001000c1d000b0186e115141c40d0700c0e202d02 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 797289802 1250 797288552 797288573
    0xa060b03160807020606010e060a0302040f120312150909060b030d050d0b1c030804150c0e040509061b0d0603211413030813080115030b072a051603 65
    0xc0074040b0340c0000014101c03034070210780d1501c540b00503142c5059a00418040c030003a60881044a000e0544c20800402c1d145001c1034840f004105550b8140044580c0741b45c01003034040c11010030445107040000c5e4440501140c154403043c0c0b407480f03500040010301424400b000e0316441c00241d0301800340030040100c1c1640f01004000c100740da00410300c80f05000c00240328100c03407c01c6008240c3d08036850068002485900f4181d0841d0081020703c522403418441041151028009000426002101c0300ba070ba09060040c02e074041c0800c1d000e820700349030070440d01b43c03103032030035020301d0851400020004044a215031215014682140c9071114800d03d807101c03c0500e00c003420400c00800d103c09400811400180e089070400709403445421490740c590342d284c41c00d03608000c260310b4004001c0c84003c241d1070000d202d0a08444240002c54014514500b490000c02d04040c03e25810412420b1101910844004080c0b000004030855042c200c401414154201800d04682c00c001d81008240003052141d030060 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 797291052 1250 797289802 797289841
    0x83901061406040509060907020102190507031d0325090f0b120109080a05162405010e160e1c08041802070c051c140106060311041d0a060b03 62
    0x41c11001040700d810010140628801d1641c4034a20b400001e180d42040030b06035803c059513000140c240075400340d5940c09110200348000005038041480030034958408420440703881a00014141e0300c2003240460380380d0414a1051032041e80c50700e006074820300b103501011700030503550808120010203021144041d10100707426278410350b13080444000d2104c040c400c19820340da00c84c40407403802c0380041c8280d0b02500151070401420b83c1e007000030800f081120301000e02c130b000300740c485200d10404603590030126441078003d107840560351001c0041e10300c0c1c2e40003071080790b0040782800b20404440e200011a0502c1710001041000d0300d4828800030040c1c444082c01c241c603a480350002ca220750060201c0120302071940003030641b0110280810060400b1024043d445000c1c600716020310b0300c140c88070b550031064400003882980d50741c20304103e4250306125545440c5e100d4000c8902e4580f03081c001c000301c0085210001440196200803400d40800da5101500500321054095200e00e041000d400b01c1501015 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 797292302 1250 797291052 797291069
    0x30f011205211c15030b13230d0c02010504090f1808120a111c0e011410060503191812053c09130e0c010f050708390106 53
    0x101c000c3e8010400303004800440d07502d02d401c000b0b02841c2d512030310310014000d8059a412046041201e010400030f1184860340e59242080680b64643d8607245850910414a120b003006500c0c5500d40043c1c0c0d1040882d0122250200c0218032501020020801016041a5154a90b04034401d04041184890103040701c01ca01d02080c00341651002d40c00000d07200d544803040d102900030081180f204064101003046160189800180301c8040b070707050350031104160300c04000342a002c0200524100a5030a01c0d010308280d19102d0f086090028200260010381c101c00404992142d41014800084030719072071166801101080000b6402080505150b02c000e048004005409032040d6038000a0b0003921059522100c850482c0311143c00c1540154000900341540481844000e8a103000a8061060400c05c904060302304061038000242902507040f00301d4091003420f101610210705490305440303522000d107807054116009690a103080f001c4001c0d0b585041040d00e16081c00070358055101d54107071100ca2 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 797293552 1250 797292302 797292337
    0x20d05090c120613060c03140411040516080c0306030a08070804060207090c05090f0103150b090907170412120617010506150a1d040c021f02030f01120521 68
    0x2019050f443d0035007101d071020781d410204d04441c0000c03110f900504801e9094580000d2000b03401d581c51101000584080d1015004002040c0517441d180c841c05400030400103003201c0344038500e000035080a02c0208500d0b1503510100006031591814003c00003c29400303280c080d6070380d80f036140c0640d00c0d4001c3d000d1000180706d14800860215401d1062440c0c98038a51101403c0085540800105860020482d41099141c20000b4295400c3d140600301610f5040c040c19195006081848500b5030001c0400040011881d03080300140301080c0c078190002e0f08002c142039852036240301600c01c6422640080c000a00c0c02c079000905045512030001c2101585009101c29104c040030484144900c108881c0b95030070400655042c180501250943c07200c1e05d83c0c8007000f130124803000404882588218030003680101030400d42025400945e00440400f1071411400c1d820801080c0904480500542408541f02d1511805100c0200582104105620000031307054854601404040d00040d00c0e10680c000c11 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 797294802 1250 797293552 797293579
    0x1320a08070206040b0412030f02040f050103141b030a021603201c110106050604030503091804080a0f0e100906020c22050709080f0312130b04060b04020d05090c 71
    0x3040113030080d0b030014043c18042e103c03900c4002071224100241d4050541c0d807044150680c3c80e0b800504002c01e541c01d06030a4003458107002505a4107002c100c0400900c104041003000c40d042c0750820550740c4001c81c21a00c90307a4030f00b20324000303100c0c424024019080802040303042603800010710303000d42404510148070303081b03984889a40b06c107080410468814200000b4040301c0c450170343e40d4264030800001048017960741000c01d80e175521a8100ba210354000140396036250400c032140420302c45030807010b509a45040d881c1d0045500484462004001c50390350b040c4a0140300c4d00307410140140060004081031040c41018044038214800c441c05800340e50611000c2d4030301a10132a40c402c07040d106541c05603894403911401018010200424080007040101d43c901080000000344a90603000316520f002d604082007010340d00604001c0303000e814541400018280303000c2282c010750700a10100325440207034005406401142a400c00b05403410003081400c1d180000d404403e000240c1d40320001c03001 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 797296052 1250 797294802 797294807
    0x1801142b020c0d050a0c0c0e01080c0607080a0503040602091309020307050d02060d11070807050102131a0d1137030203010e01170307140c010f0203090f01320a0807 72
    0xb4018480b030540d04090b81030090076001300f0050441d41018a024442c03100941e0302c9403102c2c5038580004148240310001480300260400c0401c03a00003003202ca06040000a564840e924402e00303600004101e0040041420842c40e074050701c9200c88000c084468103c40c0e0360302d038002444080c0040e4424400c0010000e00b0341420140046181c0d0046c0c4101d14000541c41c4060207091502403011881004101c4c0324003051101e4003410021b4410b0f0b002682e20117400600d0803a4020356008402c40a0030000b040111000c00011504200402800410302c040307801d9414205024480b12207000c0ba141c58000c0c090481ca0908040e4842c10300002105020405081203080780800d0084114864010005110307403c1000410000b000c02c03007080b41c2c905140c9950318a1245a14005c8241c1584000c210220a681203107035442c182490344000c50070102e0140c0059a032000ca01007690610150108184402c4070350b0f81c08590003184031140024044194007010388a074414030010002541c280040f503282813 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 797297302 1250 797296052 797296057
    0x6020c0a0303123819030b060616050709060b030c0d0c0c0213060f21030c0f02060403141c020d0309050f0d081f030c090e150103140106090209061801142b02 69
    0xb41031503005e582d01811036588001540000d48102e50003d001d0015011100800c0d5400040340e2180780544981490020843d058a07102c0c1c01c01e18022209004000c0b40d005014140c5d0781c68804501c1c0410301c1152944103a8004035100e6001e134000d2505003001c0398600181d0030a5003241c003081250f80701240d80d140c090340c04842c8540c00d0b14094002e184820003183c414811040360500580418101d0740e02540090180d03442680112481c0f6502e640c606064001440f0600c400014842004034018140a00a4460300307030040c5542815a40c548600074021304201c4510040088811503501300f080c440060b1040030200d541e841d6640c420310f002d0b0f101400c201807030421658084003030050301c0e06201902c0040c101141d00e007810b500c18003402c201e010090001f0a402540150343c25114040400711681c01d45500d0b03040460018010050721042c1d0703c0e0441201e072684e40320502164450403c00040b1482100038000c5000c99001141600c000141c59003045d40d00200c02ca02c242003200080030340400d90 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 797298552 1250 797297302 797297329
    0x10e010f080a021806130615080603010525050d0f0b0f0d03050d02030a020721120b0915030a2a06080403120906060503030c0f010606020c0a03031238 66
    0xd0768035010004a00400d001750088001004071311907100501e05001141c8440d40128540300b10a50402c401c80c0d082401ca540043d000e50080c03000d46000d0740c1e82c182c4042074031080d403014440b440c41d030550184908155021030b205801c0c00d03c0060b19800760794000d090850784462244408407500c201600d40300c414458480e515450b0315050081041104000350002800500015000c2102d04001030040d2055290120752481c5241c4003403958030020328087c001d44017602200d14081030301440c0d0f42c440080682c043c00041d403114100d89840d01080c00c203508902d00510540100e10b45140c25203440050300150200e03413001525566a0309012248270400f42e40250115100c085180d650400f0354001e026054041c000204121396240d000c48d00d140e110381c1d1a0002500807803031101140c40c00b8003941004107254801041e80c82407110010302e4a40c3c1c0d500c401414460f207100a5074041c0101d400c6505001b5860b4001d041701c80c1c6520781c035802e07120045040800d6041400d01a141803410392002c001c034 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 797299802 1250 797298552 797298559
    0xd0908070b09150f100909080d050a27050c091e060303040e1306090210050703081e0106080a0e01150312090b030c07030903050307080408060a02041d1e010e010f080a02 74
    0x75502c51100755800b002010340200a200d0140c000071401031007900038103444038414003000703070340e40900c009c040202d403c0039209030149410036104003091201d041c1c070143c3d62007851078041500900c510b0004d191900c91003030796411420010801c4041c503031030440e018003030320340d0244801180d85100805461748214040e2044014087e0702280a0450700b02401040c03d214881c0041e0710305054002a1540c00040d1940c8001440007a0900c1050b030300c001d06a0308805444030071020b4085a95401c0030880050040b6010804030000045426403150440019020702c1802044010f500010b84120010035000c2a80c40003840000748200a00c1000c000d01100c41082d0807900f540c540100044280c0e11440d0240c0401c54020408004280c090000300f40d9240700d0740c4070658551130b02c1c103c2030424070014980701c0300610602c001c1000245600c4601100703014040140c2603a41c0b4000914507815141d6000c00c2c03040400c40000c0b8401c44400041c0303059880108003c4072640d0b549108542d10040c140c002900b = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 797301052 1250 797299802 797299843
    0x10303090b07030203180111010f0501090f02040e01030f0c0e102408040803100e100f0b1206040b1c060b010e030c0d021509030d03090b0c0a230d0908070b09 69
    0x890160151030403906c1d0705145c4203140588849005096403032400c903001d40700c0da482004000c00502d610440c6134400400c0e20960400c3d1901c0e0a281103108140f20260400a0403032000e02003020841e6914003400c02014508032030308041e10811413140c400c0c00341c92400301c0321518980c1000741c0440d02907038100d0250751fa40c10681e6140d96400b0309805c0079140c07452500d460000417074800111103c59205114100810700024600382c020100301c2c0303d2b82d0021031900010030000c4a02e81b056602158030941c00c1e1804141c1009940c0030a610b80352a03c08040c0e8070140720b03211420090290007480200109036030b4004040150010551555040c00c2d000b6030104009170981c00605001e620040c41d64601407442d03042c0340b04a03010034103100300b20010300700080c1c0d41d581e040200100062403035004604110b10a00b000c2e0031440151009524103902e0300c1ea07146a088130f607042d101c0d403400c603440c80034030103018050115a85414403090300002c2c801c58130441030f140041c04400001030526101c21036200410b0 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 797302158 1106 797301052 797301067
    0x81512010f06080c090f0c04140d08040303210b01020c150c0f030706200a0c14031602040e0102030c03060d0f0b0f0f070306050102120d02040e0c03010303090b07030203 74
    0x8580305e40e19001c1c0140c4600c10700523902900d01e000901807035141d8800001d01d2040102000400001000170048101688456a642081802c06040d0b884840030444c1c001034481a01c403c50040c6c1c440580e00280b0700d0108401c804d801e02c06411140340c030340c02e80206401d100c0c185c802229607520004558041000c2c500c900803c9542c802d5a454140e504101041128031a4001d02c2d4100001d012049092013068022100842955000c590740e51150303907020394100002c020107034401c9140604810801606000300c9101e02e140100709071842e60348408001c00a9031404040e9401081c402008000550320103400d030140300036401c04250f601d8464008a40d025004201c2c008060412504000503600080d554001d217181c620b520391203800b43c1c0d000500901898bc003000c6a01d1014007413004401710600154142c074040d96030201129203c425441e100d00c540400100180e00410081 = true := by decide +kernel

theorem cover : BRFrame.Cov 797122302 797302158 := by
  have h0 := BRFrame.cov_init 797122302
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797122302 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797122302 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797122302 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797122302 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797122302 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797122302 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797122302 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797122302 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797122302 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797122302 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797122302 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797122302 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797122302 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797122302 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797122302 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797122302 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797122302 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797122302 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797122302 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797122302 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797122302 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797122302 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797122302 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797122302 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797122302 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797122302 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797122302 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797122302 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797122302 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797122302 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797122302 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797122302 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797122302 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797122302 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797122302 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797122302 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797122302 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797122302 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797122302 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797122302 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797122302 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797122302 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797122302 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797122302 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797122302 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797122302 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797122302 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797122302 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797122302 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797122302 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797122302 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797122302 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797122302 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797122302 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797122302 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797122302 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797122302 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797122302 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797122302 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797122302 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797122302 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797122302 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797122302 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797122302 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797122302 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797122302 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797122302 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797122302 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797122302 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797122302 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797122302 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797122302 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797122302 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797122302 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797122302 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797122302 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797122302 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797122302 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797122302 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797122302 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797122302 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797122302 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797122302 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797122302 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797122302 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797122302 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797122302 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797122302 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797122302 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797122302 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797122302 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797122302 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797122302 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797122302 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797122302 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797122302 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797122302 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797122302 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797122302 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797122302 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797122302 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797122302 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797122302 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797122302 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797122302 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797122302 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797122302 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797122302 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797122302 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797122302 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797122302 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797122302 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797122302 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797122302 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797122302 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797122302 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797122302 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797122302 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797122302 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797122302 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797122302 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797122302 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797122302 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797122302 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797122302 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797122302 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797122302 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797122302 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797122302 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797122302 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797122302 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797122302 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797122302 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797122302 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797122302 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797122302 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797122302 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797122302 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797122302 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797122302 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797122302 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797122302 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797122302 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797122302 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 797122302 ≤ n) (h2 : n < 797302158) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
