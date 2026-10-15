-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_5505
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T16:05:21.604107+00:00
-- url     : https://prove2.me/submissions/9b434fd0-bbaf-45b7-8d87-0f7ee6d5e2d9

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 989928057 ≤ n < 990107913 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 989929307 1250 989928057 989928077
    0x19080106061e02070e090a0507090c1e091e080d0201090b010902040b0f07030912030f1404052d040e0c030c09060a120602070f0b04170406170901090506010303 70
    0x401029031002c0400400d01021292440705081e80100d41030742514036404820b8019911a519249006160580904075018080010807840165006114143c0d40758a801c0d40340c649038851440110900c080040004203045030a00008040320000441c50b00078100c190107150b11030291500300507c0b41c1c141c4c00942c5d5103c1e4068100700b0040c4440b8010034105004609061500407460080d10404412902864002542008041c01000320b01c0c05002601c01c00301d03080e405d40c42c000d0701e803e40c0c0045000c041502c0203158180348000c1011101030b2040a001c1145d02900b0040d03015001d04203040c0c48030700700b4181c58604601d840314410080d00002000081c10440030b03a0742418201403103245242e020f0124032003000410349411900380103d85142d000020142103a04040c0c0003405a080000c040400290440043c050900c020f140100d0280480705581c0c03808425003d1207109506c18003000c80c070300440c1c0004410341f820140340e0091210001145035000d50b641d450803c51300360406c801045280700 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 989930557 1250 989929307 989929319
    0x60b1e0a06110703080d1431110906040e030c0d09140307030f08090915010e04090b07030c09030c080708060c0c0a061a0307060e031216030e19080106 66
    0x81800300070041e6080c404840a003400081d91a030300c6502000d4a080000034503540601103940c044030611408258010b00c030301b883c0d90b20001c0c1840340144050004030801c1d00b80c00c034810700000620082d601402000600f07a11009001060200601044d0700c160754405060351250180000d00c103007600704004d4000c00c070850780c000d401d142181c0c12084070208602040300c403d031400075940065981106850200407810b2804100701d00c20005100c2d000340700b020134000050a0382d048803114101c01d0b290f03c80954800000d100c00c803004400c01a1020301082c0100344018040c0d401000e940b6607500c1d140490540f0303031f1074100b0500c0559002502941c843c00007006a18400d120350b0b5007207040c103104a4900888442c100303680d40102280a404503658a150004e1800c007140c00150004001c0d041d51007007640c41001504030822030716002d0082c0900c0e1a1803082100300012100c41480c0d0b241040c4021000792022211003507042e031415041024840d01c0080c5169880400b402882c210002080322410b1003 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 989931807 1250 989930557 989930569
    0x120904230a111608070b06030604031e0e0411130501021606030c1e03060e070e0603041e0b0a06080c0603010308031b0d0c02071409010b070f060b1e 65
    0x940340c4051168082050484010900446900325404600c049200099410856000c2c800c034800c000030341102c40c0c000303002c20a0704006080614007620104540365140c1083c0750700c0e50b0003224024005005511002046105000e181524904502e0140101d0504801003400c444400840d820b102070089401c1112546035032201000c2d24080c40039043c47d00c1014844a90106580510410306455254503900176100e01e80f102d500c0d0200c01c00f44282c0459110010b0001c1c04a80150480d5440745000261464020980c1c0c21074941c02030643c030b1440d80c031078070b03106500310b030003e12a8909030b03051915001280f100e5130060301459410700006234a51400e80c00c07030300e400725050005000c1d180900c010070114850300141d035445021107507488014081c3c2c0410311032911591004940151134404001c0c0c90f540e0005444064580001003080c03180c080f00d041007640c031003d1144a1210000b040140c00003209800004c502c2c0d4444c060104442c284440010f94104824204088442c82c82c000103039a86005 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 989933057 1250 989931807 989931821
    0x120f0b030f150a0b0418060f0e1c0e0d061d060601140412050705040203090c0a120803011203140a0f030f090308160c140a0323090f040e120904 63
    0x340001c00da001c00d4250354014150b0020580c5420350b54800038004280c9858103c0c6042c140d130f42c080c9000110292401c240103240084080c81c855282904840500d1000200106038200100741143d40002200c8100c07450618104800d40144c52030000c13100144290003490804052a082040d410440e43c00151038500002d213040d041040c02581803238042005411103040d9030456004c01800c820a0414902c1d0040c17035800740f07030058800020040c1580005c14101d60003a0211030b9102d0081ea0344090704d5039011844001781c6242d00c10801040029801100954024403c0c01c0240000d092501c0d0b620742034000c1c0c00d006000c2900420b40c4056258948140300704a44042c0341017203515071a8070700030f1800c2d000401b00f5036000e40d85410b402d00c076401880c108407481c3d0b0000da0300e08801c20030345d8443c1d142c0d81c2d503078421404541c0c4070314005400c01c10104c00c07078804500303011114100040380d0100b10380c44104030f03452134005980b0202c0030b9250700d0901054405d214188001d40da02d0047c941444112860 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 989934307 1250 989933057 989933083
    0xf1503020909040f29070e01020c0a140a080106090b0a050613260102030a09050601150210090602090d030206010e01320103060f12050d0503070507060c120f0b03 71
    0x410403220070140d0301c1c030444a810070b40081110550901918245245510101825040b10007080c448243c0a845442c4680314481e240d50301c0b514018001c0c01a6070302e0700082c46640e400888501d051101d00803c1c01d514072240790040c0741c940d10507036034500326003140c410b0b400c4103503095191041890b8500301401030200400080c1d500520b00005144000141680c3d80144c1020515200a0324600c00390002e0880b610030404008541d81d041c181c1c51140101405803040711a4042d40c03000190040304a049258140b0494015080b00c9810020703104c0100350314101126026400c2c0300c141215180c0700c40014655200360000c002e154146220640d4100b0141d0020f51100c0050402d0115400943e80ba5203900e500008543c0103050900d00580c0944069004031034039460030140040c1a040302034403469028020030a45020601e0b0380011035a42c4800c88119001c99010401c0030000f41055005000e41c20301c500c1c1c9020b56981c40380c030f400140d402240d4108610390312035040e806a07103000e00c0303140030344030f4 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 989935557 1250 989934307 989934311
    0x50c0a0c0b06010504050414040203010e0102030c0d1806050411010806030705130f0603081c0c0503010f061b120f02101a1309050d080a0507030b0303041505040b040f1503 75
    0x1400401441200c44000c000c22800440e400304407164001c1c4250360113808020030602001150014500c1140d00803502644070350700700700c140081c848041c401c032030081103e2400c25161060081c03210011f488005004484070381e1a100400210b20240300700c5020300d2040e000380480051500005150a00140c48984660000c20040009603500011034034002a0228085078000301c001d1104c00402c0b09602c06400c0ca400064450814031242d0510002c000c0204c004001e8800c1224080361140030034092001d4001016601340205401b5400d00c0300e0000034603e0018210803903994442d2224043d03124840030540f202580365805405215100c0e0000301407804010a44d1000c0d43c14a0011303259400034081c2d02800807032071030b441d4dc0d40c000c154000c2c0c2000c00c5440d41a0141c01c000d0201904130780c0080c0d50791424021030103441c4240500900d45500400560030141081d4104485406282009d014030204100005900c107051300904018040b01107030511262400709182e100c5802041c080007014 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 989936807 1250 989935557 989935567
    0x30305090105090d050a030b06090a0303170705030906010303050322050705100c08090103050c3901051e1f031406010f08030313060e031b0f0703020d021e09130501050c 74
    0x203034403100340d8041b00705914002c2444060040450880c1c41800070b41600869000da0100a250700902d443d43d100b1a000c6070260280e562510488007400700ba109802c00750011401007000c06d124401551b048488840d5004242400084440703180071315940460700c9410030714007004945040312202d212140c3e5400e080e100c01e00669650002403088041c2c0707505060b6a02d01143e80c0045110a884a000f0f070a8410590f140614240018810010f0030100b040c8140580280c41044103024203801440041d45c9101d02c88a44442650031100003400744081034524034080385000d04141e1b29000550142c200a26040f0341c40d1281030801405030040f41c110154480200616440007003181e40c04410303503480040d02026441c0c8035000d04088034280d0040c1c0701c013203a00707031952800113100fa807010042001c42c2d030070b044042e1841d6203c000f0340c80b000c0e5120305503540e910090308160302d0401c0c419076001c8069821034540700c0050442c4005480c0c08030041140740e58070041150921513150003005035000e0a040c1 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 989938057 1250 989936807 989936833
    0x230a1a031e0c0d080c0d0e011704020f0a060305040215070f030f03140a0b03010c0e0117040809030a030c141c0c1104230a0911062503030509010509 65
    0xc1e6000d03400341040054203071440680340a090040d081c1d4050000d010003c0d180039402c0928075a040000b0850440c06912140500240182d0500940c004103031504072114850a54020002c0d90003481a60001e4000c050041079a88803100d41d0f000e0605900c00140c0c90909005000c54125110901d40c903202c1e040007447c01207170000d60390b5900513500d0300e03045041c7e080904003280585000d41135094880d0a0409220704010160001052200c041e00204180e280c01e14041b10f080c40340c21f10741d0317000c9554a010200b002c400e00145076030090140c0c0501b80760401d00004a0b151162105082d800510b0b00750440e010007020140c00c105416540c0d00400c41c0414440200380864907400c03403003047c4141007000d8410403440300c40b4801c0c50301c00203104005a004a03110b07420a424500c0e82d2100c16088034002032803818881c4a121100c5400c0003003450b807142e000c400e0000366400320b1140d1105031840030410071604091002501524840e03030f004260350801220310307801d5690141c00e011203500006182045 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 989939307 1250 989938057 989938063
    0x130503041d010e0903041715070f080603060118090c2d0806040210320309071d07260411040c0503060d06150f0b040311090108030409050a230a1a03 65
    0x6903104041605050030018101f1481d01a20181c0325488103649410012020740207102c3c000d0410b015252540d85950709410162100d800340241100e4540f101041c516006c01ca51002070240d03c81c01c003040c000754540400c0c11455442d0a5500e0074600c1c4940c0b4404c003095580708083c01481c25400404d0f860400740e00180c044020400f00b4410840b131150070100d841303644c41a0108404070b0742e40b1841390b550f1050342c01a460340b0403501444188103030007000130350b84644001000755042181c00048c80d9100c00d0011138281442d8040030003c01071aa04504c81a4044086076004502c1400c00c280700991203410300041c0c03401400d00300180300b010700c2002100c0c1c803050f4004410940c00382001802d5a500904410190010703080300c212841143c1d0045034000c90540280190390094418403103030f245800403c040340409000307040b95500188420400c101e0070350012900b016120700c0c0411410740211018030041180e150020603a102ca2043c01090f04d5244613903554040c100c003064a141401e10b002c03940e = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 989940557 1250 989939307 989939309
    0xa0e0c180601121803021e0d0207050d02180c0d0c05030705160501110408100e16061101021c023606090d170403060b06130e130503041d010e090304 65
    0x2043c02480c1145034480d059540c041c8071008858844269101c02904000b95500c0250310340c400020240f010102d0b0700711000444001d503030312070f50050951600f0705052043d02c68103088100d03003083c81303071213200f46d62150b85043c548a96140c12500e071720f13048442125419140e4040109041c86010004e200c13056921404990503900c400c2c268810004940c03800f240181122030750303403112030004a4003003000c00000c00d000e450300c5400e007424499882401c0005440c1d507090042030b100d0115401d41040041c3c02110449002460000010300340801c0a0b00e0f4950825030aa0700110513074001403c2d40311105940d001828034500d40140c99500411810441d00103122100c80c5215402c0403540d00d407240c0e20380a441d044194460b03003e0080d119020402202500b207404101c076000d040151441c0141000001d860522200700100e121407442c0a8050214000191031160203e860303100d001c0100340100300800041001441c1d2001c0d15601410049440c1c2040e040800c0150092003031184030320000041e40c3c = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 989941807 1250 989940557 989940559
    0x1080f3d0608090d0924020f011a090a0e060402010f05040915150206061302091215090f03211f0312110309030c0108100e0c0a030b0d26120a0e0c1806 66
    0x186c07600104005070b203031030040e04e03000c40d00798203048801c0519030a42490481e94181500d600345030b62588420141500c60300c40c011107080c2e008400080c0550300c41e540e00ca4580d1010b0901c5031915840742ca900040e90980441301c40c1040103000100030005070504811028080c0d4400760032a81005000100c0700c8410004805030942c0110b03a9440658510000340ca0000c443ea08035031910b0403164500319080c004032070b2075401e4055030300e4100c16088003204a9543d00038940d008090841d009200940048024100212820094404103000e0f0780c54001a4003643c083c1c9052102c407951580c1c0104900c5007450030b407980d07800a220001c0c89403000148141099001d090044199a03030050100041d00030340c0c000190940803406010341203610b070008009a036031594040c00240024020721880c0c0a00e070301d008081c000c10403101c0c1c00a0307a058800b08040200100c01c140790403a9409070005005058411041140d51022100c02001d02082104514581541c052007200840c09080c0a2100010426 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 989943057 1250 989941807 989941859
    0x4020a031214030a05250207030f0c0801020a08100504060e1311030d0f030b0103050402011b0510021809060924062701080f3d0608090d09 61
    0x4200054007402c0c600c01a010500c5a0689a1900c043d44030081c0c80165145864181c8001d011069000308903001d0002014640003002100e156036074445041c01421070640b40411044000b00d400c3c0028001803c8100055943c0c0c0d00600304030850400401c001e40c4810311607450b081080001080001146600c100d40c1c820501009405080c907005071004e07050312541c1405107000b110300060f0010414000701680340e41c2000f080241c0d4005404665003a200640882c22095851024044c41403805000074410070a1f81c150680340d0058909036005040d400d02c030401100b0385480c140c14220500d41d8003190848560101c3e0416000d0681b00d14606900c00183c0b056030048141c140c2c9520b8100c42d00351002c04074040c0030326100740008030f01f50780800d28540040c0e010340c003044e9541a0021740310301a070300500140000141114000c01401c2001c000c060300b0a40502000804898103101c0710010032154803807070801e250203600c1ca810404002154820311088000c140890102c8a0100401007226201 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 989944307 1250 989943057 989943083
    0x30105010c06052203180806010506030c13051c0501110708070803090c13020c061305030d0b0a030209010806071b08030126060c0405030f120f0a35070804020a03 71
    0x400428030402c24440c40c40001300358014010598046610055410000182003080d5252035100c0d071290360038425039901c4113007417010507103602d0340400070300e200e60050720031036455661000030401601c8a0780074819450b85500c029000d00000303005040c5146000c15810303150103003503540e894140c051114068461a004800101c5242080180d00265078000340604502d0254484130700c0a0b6204d0f50400e182801841e01103064440c0741c40460300500d5000000c0c50500c040d146241004125003140540d10081c2030400002503154000c41134003070b06008018008030300d001e85010300300400b00d0341c1d8410f61180b02c10006000c9000310043d00d064903280551740f100710300304d4a01051103640f000c1700c05403240100400c0c0403032102c0034002401201c034150155140c0d05070598200e40c80c0e600b210b0f203282d1200402c0000c0000146d81c0c40040003a00c18906090540c81e10386c040001c40002884601821580946002d0441002a108450340400c00380707010090740c500b540c04504038100521006145000300d5003 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 989945557 1250 989944307 989944321
    0x8070603020708040f0b0a090510080601081b03090a031701030803060409032c0a050a0602031905071e0b01090506181b070b0f01080f1b220c0e0303030105010c0605 72
    0x8440040c5454014540006d8841c0014099a8000c064410124510030000111810491501c08401a164803400e500c1e0b640d480042d254070700018040035880d4803110380811030618410140d801015107000400c03031214036280203401881300c00717540444da00f02d1400400002e81818212580620141d4010401e4442d5107825524031840700c403c12440c144001380582182c0103251918441c3e4011620003140a56880c1440103005d242d000b800c0041e0810806031302c1e807200c00d1040500050003494090315010090700c40b07940030601041103441e134516000c800014000b80681c00e03400350820120812507800c00e20002041e00320074002c0044541540800204000304511282e0280b071200d02c4130554581c01441d110f980b4000460301100440418800031800c8400025600448400c080c0100708c400d03d1450441400d1203e05c5540380c0c803a2038404031110841e816804040c6002c0355480c04911040503d07000303800c409465180d28003030390050004004680c1e02c0004000b01581014000a103500d03141 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 989946807 1250 989945557 989945573
    0x23031002070c050612100608070228050a080d0621020d020a0911131d130804030507030c21150908120f160905030604080307180b03060415080706030207 67
    0x2c3c1c0080d5006901080046015021048461141c40f18184641030345460780340039642248152000c0300140d001010740701c004d07055500b040207440308a03909041500300c9a035483d0702d4a410480d0844107264045040c1c250350308540150301c00b801e0b8070580d11a40340c0c1a010400f40600380490043c1c0705d01050040002551101d410302800780c01322680c144103031900c00040d01940c3d0b2109000c014040c008200c001500c10062041034694081c0380d2881c0140d44814010200c000707450343c800d95081800f0800003000880070030010b0000c601c1402d11900307542c507141002d44003030200c84844651000030680e05000810b81c0d0750210400c0306107000024800b00c82d0600103044c0c0180b10041400c44070341c0c41401008401032120a2040c40c207265005008544c588089a00c442c80e0b2060039010b900050101c5e00040c0e104000d50703888161882d2000f00c40c1ca080002882c000c0c0c01c1d500a150422000091007800d003850b0082004083d403044c507621505d440c003510b0a80d110003900c80c40e020542d020404404001d010 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 989948057 1250 989946807 989946809
    0xe011202011214040c050f0123030402220c03180f031107050607050f1608120a1214060306060a030309090e12120a05161e050c150123031002070c 64
    0x202e00403902c03480d080ca40302052030f205c1e0107224800c501300e64010100d90f01c95660a800c10f400f031a200c03070503443d820100c1e581c5504060012030b1310103845150445502c41034412540d00321030054022820b10202034000d82242d03103400e0302e0308000710520f50f40f40201e240b1a00d800d100c20782c146407002000d00385814481c00c1c07900355008a030b4446000101b6000b030190002d2505012600202601e640030b0000208141c000b65034494a0441c0e0401c81c041560010300c00041c14800405040444903d070b88100100110380e422411550384a54080c01d200d2541410416030350b100009032101d002c55403c684028040c03820313601c52041c03141c0d110500000c80769420300c2640c401e0398010301e01540740c9100d210740c043c100008981041045140c180000e81400d1520304001d00300c0b01503241d00079504041c828074042018121846c03014000c04000f00c01340c003001049188170082c4051021091941010400345000e0002076403005420341541004289a601180c84c000900550a006903500401c0c9041566003071a = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 989949307 1250 989948057 989948081
    0xb091c020118030f060528090c1703031504020a020727141b19050703170c090f03030c1e1204090b03010f1a0d05010915020703090e0112020112 63
    0x5800000f0810a044c1e5001003910071441845950740e003204400400c00251a9003480b080000400e030548032650344610300b00340c05002e0495100d0740f62100c054007420911420081e80d4400001c00c020000307410108040030f04119020b500d00300f4a00e4000b5500c1006015001c0c1300300003200540a2064078008414000d415030381d05100c00c1d0266080045881001c5501407094003142c0711000081c423208084600540540c0d07542181340c01003c2e0300b00c0317040e0046c0500700c0901c10f008861004600400e50410304c03440040b074540d9900e0760403600f40240c5000c0b1051040c041d60061080c40c5080c0340204402a502e4190503014505400c945141d610b88520b21001400703030600058081002143c40c1c20200f01210181c0c024064407009407000300c201c03a81035800e940700221000ea1074040d03141070b0a10600050144001041003d001c0d29208500403e00c004141842d0b40000c10908041d00100094002c102c5c4646402c003030741c54440c0840448100001c001e0400c0107400c40700c481c0c01c00980c27048003c240 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 989950557 1250 989949307 989949347
    0x3020f0724170702070807150c0303020d0213080304080c1207030204180c06091a0a021b040b042c120706020f07050f0a02040608010209062a0619060b091c0201 70
    0x5003c10302948420341405029543c0c051640082803000e009a06040101d07e696682040040103450883c001d40000842001c566000c21101d2990030344041d0003000380c0944000385a41e185400c254502d400440800b0714002c42c15800c0034020000e01280460451381c0640d800301d0381c0b02d090302d0030140800c003450004141840c0c80001107012544032180400783c9a00300344c5d00b10482005032400103d8080c40e240003006a21880e040302d5061500c51b40e068104001400c08100c01d815440014207540904c000d5034010900b00d51242d2010b014428484401030a0b2030107043d400d04440c08810052140301800b90019800203803146801ca400d004580780300b41c00805a07008850389040f52529034400c10400e0744250704204000c11110010700c21503140c40c10081c1174a20f030a0341d10300c19000d480850b030300c950048401c0480382c1ca0002c03403c6c07041070b10620806005981280030031700d40000b103038011340026070038a101788120401c41c3c840c440340507101d0844a041c00c6000607140300480d0302500c94000c58071540 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 989951807 1250 989950557 989950561
    0xd020d1101231b1605010b010c0f062c0102030907060c0f120c1709030105150f0f0a171e06040b0105040e0a060c020102070302060f1e04050c090c0703020f072417 71
    0x1010300c004d8105601d20480003030040824030030045a03504c5220401a0201018180880024115501c818215208940c01d0140d511440404041181460300b581550703035000800c00c03070401c90511003039002d003c140c140780d280140580c940c560a141d02c4100102016402c60321039013000d00583c08040c0e5181d01c0490340d4250b0072000c0d41c1d03400c0ca80002c142e140c003949c03c10300403c104643d24642d0300c120301009440c40d01c14880520401c01221000b144440c0c00a80750880480d400c0c0c05103058800ca1108031000344100b041c00e1500900800c40a044006160040400c0c0000142094061411100d0481e00450030084c2540e02e6400d0804202c80141200d1801d0402050719030190090210f05019400741d880c1d0340e84060b00310703092003030850705d0140032182c110050400c1418410382ca81c100e4010801c44017112000400302e00c01c0002036a42095100b00494900e00700b66040251701c04a0a0000c041c1240341e14007554284d06142c5c688c001512010340607500d02c4480d01c42e240007400c030349401144081034 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 989953057 1250 989951807 989951827
    0x31b24020a1e030206100b340b040b1006050a030f0b10030c180509040204050c071e060c0e10030b0402090603130b090f0307081303050d020d1101231b 66
    0x3040340e080c0860243c000d14002680c0803980c080c0d034600f207c0300c0e00c00c0217103041c00600000d45881c0007040c202074801150003003c040c0c00001c3d061012a14401d95000c0a5414641030031890454010300f48001e0400d260b50a100d0a580501590000001c078280410701e151a01c06420107840e10a080e03c3d0002804910300c0704195140e013240c40b41c04229203c0c090406811080414040058040e550304044002d0104005041650142da0301c280c42041c041d04141ea15642c001c043c1514410079489030985180d080c0a120462003010340c03044050805d814140d1418012902c24900c481c0303007105155454131001c40a4503036030111001214011310b12507480c60704055405400386c42ca8002d683d41c01e110320000344c1d42840006d81c1035618007c88021801c00500c2e64496a00360f10288003580f00307206403080000002c80401c2900740e480b0042e00a0302c002541a40004c1c955162000450031503030607d111051208920f03000030308049000d64a41d0320f0303585e45030928801e03204030241e11005003000048048030 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 989954307 1250 989953057 989953103
    0xc070b0408042c100302220204031203020408060a09020d020d05120d051006110601030f050705060309030a1815110705030703080a08060301020a05030f1915031b24020a 74
    0x242044102440f000d484814092050107418000290403205143c4020744202000100d035040702d00340480907290079200d54604902072040009000401c4d0042003d2006010500610340d100a04003410040e0782801e80015901000c03884004c0d0260318122113510902205004180300600d40c0398419030b07146540e503d8600103000480d00410401075004020542900c601000a200c146080c01425644d0841d102c0044480ec0f0100032140b83c85203900c00103603602c421021314072512110000d16202c0030021409000c804c08000c0700640107410010501c0450410005800080311500d0305c0c1c9010580081c1d96407070890b00c1d400041d414403e00200008000c0828020015400c10b65107002c1175840d04d000b410b00340c0c080e811114021540034000200401d030404500c0f58400000c045c0384a40d030b4040d00d04c8004032508201c0c40c58104c00407070018400d001c8a5480500d0302840300c034226046034600259200b00c4144610414010440070000b152550710800c2030b070540b69008003400c40c0100c2c3e440a0145 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 989955557 1250 989954307 989954369
    0xc06090302090604050708070f03060806071d0405010503100209010e1905030f070e0403120b13021b03180607030c17130503060709090e1f050103030201140c070b040804 74
    0x88a4034070b40d00041c1c200d0910b401800d00800340c80d03d403640540c546803001d80d01c821108018204141d510100040e4081b8104405402604d0355110800e181c4510610116101c40c0c4452890090f030034500100000d8400080c2090f80e402c26040040c0c40700507410040301d80c1840110040e500003840c00080c00c58981401c040d10446400320103c40401d001d02010710b8603181030388201a02c40001000103001b00f401500d06000c01d2544440004600e0051070020744089027030b03030001c922240d000c22180501e142c1030b20310311f5498070b00d18015410100344d140e02100d16404002094095440030501e40700b014000c10101e08000d03401041203c44550b00760700652103411510000705452480720001401d420003168142c0101305554510f2821400c080108014161009440580780f0480302c5485003081e0007510340c0695400c800d00401c103540740d410300900b035135040000940e00e03d52400c1842501422201103c290690210080e04142e840f0b04147c01e41e0b001d00ea001c00d07890504c840c0620703039003600b4a201c40 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 989956807 1250 989955557 989955559
    0xd060b09120706081f24090b04050f0d05010612080904060501030e0309040e0f010c0306090c05031e0405030702060c0618061009150b1611011416030c0c06090302 71
    0x3001030001d010882da6949a485100003040344a008114005e581c40c5c41c2d0b64403c9401d8840c1144642d440310741250355001000003181c445810320080b411640c1c04026580240010821a800c06062070001054a03c03100d601903c1001e1100e561030401034290014001840600a84000c080580c24122013a5000d8803000c0d01c918078011002c42c6543c042c1c41801c02c5000e12100460422020005000044c8a4071a24100621030000d8242d60428240a0345504400b907580100d039440c545940342c000c0d6a00000b100c410701005004001c49200d040e0b90565030410308039640c0740b1a84540c00c2c84c504502c641d41000e0741100c40001e002520f400001083c0d40120407100e48584d10604040c0c005840d00c000b034442c1410290b00e18810000c50420b90401d030f860315010024020320a59800061032580c0c03001c202c03411800042d418140502c480c1c12102000e2003000c0c01c00720020399194401c0040c52054640103a032003038059080c42d091600c1101461043d5a00c03043c80e0050325243e100251072010144000c07 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 989958057 1250 989956807 989956819
    0x160803030a181a090703211e02061b0d11031f030b0a1a09040b10140d030c0312060305010506100201020f0412171210080a030e060f0d060b09 62
    0x200944034448a5030760f400158242d00d901104002c000342c02006001c4402c0d078400c015003c4089400b201541c540d00a01e03500030410200701d40340191074001c00c0c800f200d80701c510704c1c1110b207442c03500883c58580c0000413010b8080d00114000d581c0030302c1d0280840146c8040c1c5441c0a40301d440380c44200840c01003a00031868604000e1000001e4100409404014103280c02c14011400254030303070700005c0c1c032101c0d14541c3d1302c00f091124000c111001000c6405458031505101404028420554100040d05244000512061040740410b170000c0071410000d0030001c1d0600c0100905100e01219800e04508907014881642d80c1d041035400b0f402c040e80d045109905405801c3c420500510884450000480311681000d16042604501c07089519050fa000756440e805050040c0440b8002c04010540071041503d50070b1042540940500d40d40008042d6805500c024011030b82001041068020845406641d060341d0000248140104000c400c111401c00358040f82070303414403001d040100419595 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 989959307 1250 989958057 989958071
    0x3040f0b0a0f11031e150d0b15010f090e070302040b160b06030c1807090515040f0608240310021206030114010302150307021e0d020c01030510090905160803030a 71
    0x40000144825222082c5d0042c204030300c1e107400491070b140c060740a03084141d481007560f1180e0101d44c0e005106c1030101d46004901040050614040c0390403612100c0a1030319020b89139040300080c000944074020b108411100d240010401c81c802c0c1c044070084c1c48080c290340d45810342c803030028004d041c1d108412140e0528640002c1c486003030000701d0f400c003070600900034080c119442d56480d02d0300300003034840d0080101b4031034046000c0c2c554a003c640344280d0208103960321490310800c06140030f2181c0105c0100549036060200c10184101146840d4581740f0464990041c00c0e07000a04e09100001c01100c0b407070000c610342501c107044c0b502261180c0c000740c000307000f001d4a030641c0c80c040303040c00d0000035800030013038951541d4050b41c40065075110a2a0045648400350140c03028101e1606a07503621050348020300200d00c269041c45940d140341d60a081c1800030b07003000b11140c00b01d1803039400f855004590341c80c9100b01b03028042240c0030752101441c0d82e010740e05403140341c00b5171240d208446c4680001d080083e = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 989960557 1250 989959307 989959331
    0x30d360219030311150903250807140d05070b0f070c0b10230d0b041704030609021311160201051e040618080c1509100819061a03040f0b0a0f 62
    0xc501c5c0c1c460b20204000d1403400da9600d4002c4140168217440251015109420000060000c4024064940580c80c42040c041e108100ea91a0111410401040001c01e0101400003484503036001e802141c0070f40080c501c0d9503803890440c0c00140f0b04038058129030644040c003c0d020480d2640405030346111045203250540252446851001c503400c82d40c210700c030740c106100464001640150444d20580440402e0f941c224100d89090300700d5001518a0340d0741e0981c00c03086140002c256502d0701c071110b600344041d0704016498403150080500e4115400d0b60030070142c045a100f50b0444035125204282101803014417503100c502500316024201c08100c00022111482540c0380702d00f4100d403038070300c0244460240306c0140807080b50220001c1c1c0ca07140b414800c3d00c0c226652070310080c000206540d28203285c3d18000c0c09586d0803012882c5140d1040b480d1140601080b00c0c80b02d01e1022004400d079103a0365a49403460b0540e00da0341100c1001e000c2c0d9402d501801030044180c0c00880109440b003000f0300040340500 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 989961807 1250 989960557 989960593
    0x702032a0a08102301030507060314042406090f02070b010605070b0415060909030e01080a0e210f03041416230f040e030d360219030311 60
    0x80210221644588072040c3c40c603602c0d4200c0d0428221100109a00d40342c0a8804109040203070002c44d0b00380c000340c0c0c1c284001c0f40e03d44900c42002c025031781490541c1c10113840e00c0007100b10b05640031000b035030744e031060344244d2150750040f00c000c22840034204424018103440320000d4000b0102280d1404203240002401803088050b5030042d07800c42c0c0040c800361107540c0c42d1400031034868880a101c1d92075800c00140c4000314807800340032601035103030402c281229000060003028010075101c185440c00300321995038030001a18225540a10002c269485081d030380c005c019000f103891040c14480c0c00010001004442c402d01108205108101c4610b0500362420b000c08621394020030071800000c00502401584541030280e411a0241c81c0c405002c13245000300d4150760044030700828a5000060044a4581a1162840c030f03c0300c08084125480e040d040710003d40402111202c10b8010f00700c0f1540c15950b80e010f03404400045103510011856907407402601c015414130b03224000c1d020304920003a500c485c4c2 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 989963057 1250 989961807 989961809
    0x50f010507080a180f1707061e0315270b0603130b1312090806060409020a1206060b120105100206071b0f050318030f0712170702032a0a 60
    0x40301d034180c10140c00d60f00444180c6442d0549207401000c1c80000034011507001e441c0c00c06480c000c2445400c9a8542c00460710f06000d5030302c501c00700701000d81039604500403068034040303901d550710f80454070b820103000881340010345401401c07140300c079111005968290840e6205000f00106428040c807120901006014002100e1110010040303040c00e00000310743c108039591010b44810ba40f406031030746031908140710048010407030108403840824400320404021207580f00b0f50441e01409001c0301c0e980401c40784109481444a101080000e0508110325070b040240986185903c1c02e445410441243d4943c0c2028840c09000e84643d2107421040c81c404a500b0f03105100540b22050a0410b5840c00181d0036220402900c60a44400e034103400260103000810030717030300014622700742050f00c001090b0805181c0340f148000d907406042d0401c005011a0f003512816a003003505190600c00894540d8601d11481c04000c1d418041d40180c00c188194245480e06103070307034424003d18411505c2051041d60211 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 989964307 1250 989963057 989963063
    0x10207080c01090311040f1b111f02131e03031b02090f0a0e0105010e100510140d1d010501090e070605031305010e07080f0625180b1201050f010507 65
    0x1102c003d0020405c918500700007240c0c060000150846802c2424040760f04400c1c40f5400c44884040300fa00381035110181c01c0000340710101628031030f4003030071015030904503004544880a401150202034484172442c018000c200503501594001c640c8201d11119041c14007040740403581c404081070680d040c91007088442980034201035a81c0e01c0d0082160130980c0002c0c04910300c980c550b855100c1498087c010b850017000020403420060030b103401c0340302e0094a00d4028a010f02100d01c40a64040d501140c9552500d0300442c08591b0385081042c69809840900c8424200b0507498100d50502d642c1580818100c0c0c03034201d41009075080383d62682e03403940e95034411000000c0382400402c1070301881002d4070310000d00c03602c00040c140302d6464001e420314115510820940d0085a0340b00d40e10038090140710781c04800c0300810703142c0c44c8035089180d00c0c51b2a0001050304124503014032481e080b000262840191119084883d246d185100312003d100209003d031900450564130294070035400b032401d441d29598 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 989965557 1250 989964307 989964317
    0x10c05120403031404053f0a060605120703060b130e1c140d11160b01030615050a06050c0f06090c1206060604050607050703020904060902032a040908040503030408030405010207080c01 81
    0x5294440c0d550010311040348440000c50703418030f11019410543d00241f0100003d030103031131000390904054084400541c0164000c50368680920f02400d008982041601d900410018071201510302250704034105031814110341c1d29280414640080001e0303001c88011141e003c1d48400400381104496022220104402c100400c1c0f20403007540170360341c200701600c0c15044846802c0c8110001003c1640707001001c00c0d07841c1c0080d40014002c5c84840d020349030080110302414181c8070b103490b000c5081240c04d44542d0040001c04207039294440780c02e004000072003852904994207400c08400e02c5881d00003a41820784100d044240100b450100810b40500c50900100118202440c0005024840d40015021581805070280c0400141e07140d000740c4c0e0255002e80340000d40104a4414189001084030119200b40d0040082c0020322202140c40e510420040c2c4011545070600e00c2d012096000d6500407e42c5808042400301c0e03140c400102910403140709038220362005503142c01d19901d42c000c1c502c0c0170340055 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 989966807 1250 989965557 989965579
    0x10c0207030b18120d1b0801080703080702220c0f091d1305030a02160503030306031f020405030a12022b180e040303050105031e1b010c0512040303140405 68
    0xc040383e031100e014603101c3d005a5040021184102030641c0c00441c0c4040304d142d59440400291015040c4100b60b600719041082d0385506000050359202d0480c40020706040c00040c00c02c0442d01d9031915521202c856580c007118107299403801501501c220040003001818280c2c980d0141c0c2d00c90b5031035008442c3d0350a08245601600d1650300095000141320b000f40300c4030000f004002940400007080c0120300d56000d44030241c41b080c02d00c1200c40780c2c0e6002c03900c668014001d0080c6a42e010450344140f010081d621030b03807026100d40c414068092540041d070f1501444090304280f22030040c603070664801c0d580c2500c0007402c400c0c00710000700e6280544403a80d108c4e0071484000b41e0707003d2801c01084686005140001c10759070381c070b00542d80e20100c804400180d00c3c2c0004000509041004100e4070488860862804c8840c501c0c1035030b40c5480110324400c071650612400c44a0340109102411550080150f5161389000e000b0460a90301a21040b130006d04c100d052802181030980503502a684010042c6a0b11 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 989968057 1250 989966807 989966821
    0x13091502160b0709031203050a050a020903030324040e25030b04150f060602011a0103020c0d080a110a210b01171005031c030e010203040209010b0c0307061409010c0207030b 76
    0x1044004141c141400340070400800400c902e1072030301d0920300117950040f03401d1a140c1b01300000d480003c1c02004d80d9a006010150337a81d900801603d41c001e00c00e8004680c0c020504207405103030f000d01d0385250b03003062401d90351800190011a4440c46095501c1030042da07030074040502d0600151a1001603c4e1202c0c0b540850001091001c1c010080c041c00e403000701d40203484034050000c5800592049000d81e5503812055034124040143c0c0802c510300342011410103681e4182ca03901d0300b15a0944500300213401d00041c3d0308040c1c0c1c5e880300c41103141c0403407060b84401c140c20010b040520884002c03107500c20380015540c007280c036030b0190b00f0340300c20113954070200c601860404180d0100040d140700f281300d81402001c141528100142c01110303002015503241c03c0a1000c003d400c6924116181c600f031f074010070401001da01c480098904551010144c10f03a00c41004200c6400c60003003031002803c0d142841e0003901c400c3d45010b811070044038070b07c008121700400381000366a609202e100c01884101c00c0f03070010b00a = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 989969307 1250 989968057 989968073
    0xc04060e090a120c0804060e030f010c1209030908011401060909021e0306031e03030612120a0c0c030606030b01051c0209220804080a0525180b1309150216 68
    0x64403e0750822541c0184c9030780c0e070040b8581054015000249465200034400d280411544210550341c0c402001001c130310100c002d05e4409200d03418040b9544420110082500c24803034440201400b5008001c0c00d0241c444a09483c9428400c0800040322408081010010343c400ca0750383d500441c800e00308200e41c40000c44015007004160700c1c4c0c50300603c041216880d4018a43c100350842c41e00c040c664902d015000c00c00e425646c00d0310b0080c41d034490804e072482c90526600304c950401640c00c00181c3c030281407800780c0c0025181e4000400c82d42c01c1c400c001040212280849050701e400b107078130710146694060414120b800b2014042d601070000c201080c0c0071001e2440311050002c25030a003e200002c20740703a0707036000e90103036112800c0c42c0d20146041050007400c1c0a100464001d540306220411100c011040c600d10903801852440b00007007040380c0c5002c030746a200c0d01044030098410480f071040020078070000c064101c0306481401d00c609110341d08540505c211811141500036a43c1c00760401d44031184 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 989970557 1250 989969307 989969333
    0x30f04120c0914010e130b04140703080c0303070912050c040b040b03010c02100501050f0904080f1c0f0c0212070b180a080a0e06030705390c04060e090a 67
    0x115604038400109035990b07a8001d98400da15000310002041d40341c440400c2085000904503803581c0c414030813100004e00082032054200c0d40003408040070450600200e810500d0981c4002d202c0d6500290142105001001862162040307032110a0b205664005c1400d40e44440440280950841b0f140740c482803405920030000e2500203040090b428180101090849000c1540c4a0159001041c03600000505008050143c0000e40f01c0d00c4840040c180800c9000c04003800c014141d0b440410b51151300703480113003903410f50035400c4a10740c402d98100c000c00d402801100042c5c80313500d00741300c810308281d400003460f540b800020001c010710301409903c0c0c82074080c101602c1500d50003903201316040b40381008c010070000079004011190f5503400000780a00250001c48826000c0d46080c001c00500941120684035007400403410150401d80340c503210541d0100044070143c41c90703604540040510400101d1001d5050141e0301000150b849048149840d0421104026568070288880c000101b091038003072 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 989971807 1250 989970557 989970563
    0x8011505040914100603020a1d190f15060201200301050f030a020406031113090203030904050a1404060606030c0c11060a0212071b2c0c0408030c03030a0608030f0412 73
    0x110520403034000d061024000a131071803141c840105006610340303812498001c000e0b0b03007841c416500540003a101d02c4036005140c0600e04007a0422554151800d412850351020700b80c0301080420f03040030703c501d008030ba140641c800541c0f8049503070031151184e0141c826030208840040d800c5031b03c1c0c44100701e03400d480d900d91039416010700b04040c40140c94030300400c0c000d144a00d00181c5203e000030140650704000e81c45003d502d40c2404440d40143c0c078040115075238204183e0380812283c0c1c8524440e4040c0080b0312025400514100401041c4032a41d40000240c0b4441d030790a10034411007143c01c40320150075440c00350003001e2b1700c45481c0d0241b4200004000358078103401520b01300c9502128806041e04141001e4940d07080c002080e000c0c7d105441e1450340039040300d881c0007032003c1081d001803007600c94030180c400000c0740c604081401e5a82c41400d0744c0051403011f084940c6c070503d60500d0b42e03d9030015a4015442403c0080c049500c90010042e914900b81e10810070b800c0a1424104114949014100b5 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 989973057 1250 989971807 989971823
    0xa0201170a0f050a0e0d05130b09180708150a0f0b2526041202040e0f100212090a05100f021e070209061e0105030a020c0a140601080115050409 63
    0x44110b181c10f402014800c0040000c0000c104c2001840d80d400d00b9401035282e81042020860103034081e100d80980c5040d140341140c0135403078003003000204425001e4040310004541044c03041000b599842001c0600c552004c1c3c4900001340da500c2c041c031040980e40d01400b540003000c03036014013a0101b4140944411058202004c80103007800920b0003201210910945846440c8110100361108092030441c04090400c4060b150070310300f02c40000c0708072921800074455a21000004c2208030208502c1c01d0141882081d1110000746100d0b44000350701c581c180d1003403040320f5000105418404100407403025000000b5151459500c0101d1000f00306940030b0f03001c0c840c1e0a12180c10840b08800b24021070818401718155515864010092800c0c4001c0426105000c0307142c10086400a80c0c2c2c10641c203040a0030550b0300e03610743c481c21001a0207142c602c0141072180ea1412410310034803900c2c00d0342c10000700c401da41c4281d88640c04903081c1e402481280000c008406000c12140c00e10f03074011003000d401075a43c = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 989974307 1250 989973057 989973071
    0x7020f0a030b090601031412030105120a05010f0e010f050402030a0f14032b0501030816050a0f0c06120c2309031c110f07030303050c040b04030b07110a0201170a 71
    0x640004058180c0b03c1403041c0d44450014000c11000800d00b40301e0303d0b200b400515800a803901d54003a40d2005016980c000d41240840ca58030302e008107d0a20540ea118000b4418099001c1c20640241a0104084060742c2044486002c210551050600039900600607114100c400e441c1c00045098440c070403203110307010500b0320708900810b1001d4000040c509403203046080b43c81c0c0c20540c44071000c2010030002c500d00801040012841c1e42260f899450707103424484803010a00b0450b050040c01d07040580b101918018840c20070501d0708040044d6412516030841e845800c00c903c0703007101c0300000340c5c4005c1000503050340450307180040c440d641080f800a405140c440d540d40401d05150614291074009030140c81036044058000c400041c154a41d0300081281103046020030707076108074610000e028165250081500809a54210303000b5103031516150350707601c3d5a0f182041c4400700442c4d40e000026100c2c2510f58280c0c4010821080d003a4050b51000081e01181d5240c1207142d801401e14506036a60704c20b = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 989975557 1250 989974307 989974313
    0x250311032e09140a1a121005090a12050301060e13180c15110a12020f0f060703060609080c0f040e0106060e030d020105010b0d0c020c120303041703060607020f0a03 72
    0x40e00078040c080b003a0000c01c3c107051034007154010701005007030400690f04200da48402d0b90401c1003100c0000c0f0044848880311040803180780e0070000010aa40905414541040008940000c580d1115445455444a2100340d25002c0300c80d80400c1c00356200140d4101c40400d142c0c03910003880d0b4101076101d0800501d02404840000c00841c0d10301086400031003e000402c00410070642d03542170441c0c10305105400e1f8018040680e210f41845000030403041118002c20582c51003040300e4640d91413104102c0398442100524281c0d103844c00c580b480c002a05000020071042d01c1050100c08441100d40201a8298078000b0030280c01240250143c0244c2c1c2da825800180909006141c0100002c3c6c03035050705007070318006060614804103400d4017960b0502c0010060100070404a40304001009000100c00c1e981030780890030000441e040d180e0040d1440c5080404484c003000860084d4170448030749441098003042c90b05039000840b4003c1d4003050502c05800540cd01c0e1410643d0104003d2002049a459039 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 989976807 1250 989975557 989975641
    0x90a110301170c0a03200405010b09271f060e0d02060915030a0207020310090c12050a06060e061f2304050a030803160e03120f070b25031103 62
    0x58000d5508000c0080d900e400d25480186d12030103284281d40900c00d40d03051415802103032040852590040143c41d52030140c034a000300d420901e800300300b1481071281c20303c580c81c1d492001e182080020304202c108000540030380510501c41c02110090070003001c1618503020801c0383d401c034110054110b0100444403076003060000055106445507140140c0f0b40000e40140352401c0010b2046c0d0642c10f03c1c021980c0085003030401024102c4411606495101d60245081c5043c0209220010902818081b001c036030304401c3c0d402603109001c00da55160107001d42150381c100951600074900089002c40c0300350154080003d1422041400002080d442e060356a400304058100544c02030341e041601009003d050316410b080700318110750620b0f0450303480740d070301c400070380c507089925076401c843c0d500014001814a10300d0309441e01301d60450381c6880b0500e000b49540024400c0c0c030780e03001400b001c5420003001c410f000c0d1041000c0a202c0303c0d03400e4115514104810001903000c2d1440780040c4d0b600504d440111914 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 989978057 1250 989976807 989976809
    0x309080708210c0d0f09090209090402040b06161101030e0d0c11030a05120723030a0c02010e0301020a02010507201b0a03020303040807180b09240a14090a110301170c0a 74
    0x83e503106041780750310703010051142c1801c1d009010b4081c0104041c2d40590703100c260203500035130111000501c40303040d40d00040c82c0744070b0440b000c0350641200d140790051054151440f000b285080c0c809000340e540407000e10362100c5e01c205208000c50081d1800c2c0d808101c6107a2540c0501074080c080340d00e004910f4803000d02d030158002070314018800004045040008080306030004c7d4120f0740c0d844001e19540c00d2416183e008850403001000583c4080105583c8601221002650003800031540d45a04040090180001300d4552011034012481d24034110440e2408034903002082e0041c0865200c91031121a1003526079800b203074400042d850210241c4d60900082008045803002880c05074540789407609078507800348030001e0092a0041348001c584a5111456001c200c0716140489914034080c00c1d00c3c40c0c485109441d070417206550340031915820382214019800e40844041040d030760b6107021601600c0800316075030003168043c03004201c1303901c0c4240c024144000110076503010ba83d51101041400500e = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 989979307 1250 989978057 989978083
    0x110d08162307090608010c02030d0b040204030b240f0307060e03070302180108070617070806011e02032101081207150f09110d050309130f050c070309080708210c 71
    0x3010004010a500c01c4c820540144070000003800a5191980d000c0c4d1240650305040f04420b459503403560302d5685a03811140a1135008a0341c0c3c0e081d090401c130100511902c2d44c01c0710100403038901c2111035882c1034003545403060b60040c001c4c040c107810494121900c1c4860a00550940301c3c80f41302000590360105511508650480c0560b00c940c90035240c540707040301c0f17980a101403000e0308800f40d502d50b00c801a040e0f1b0001140c2408000c603118100101c0703000000e01d58184210391456030030f072142607021000785035042c1d0107100e031480c3e040017000140300c54030207119000d920350050500040d2a111080503249541c002c901503c02c0032409001041940e0002c3e45158490750303510100010028a5407414540d514181c0307074a01c0076403003603507113959911070040d004d48a03004a55060301c1d82c25081e00314034110b4040c0b013400d1000c0c0c20000c400b130881c1e4100d140200c0102d211210041070a1600283c1001141d10f444000c04d0051984400348100e0100c9400c03080002104106403112604200440d401c00c00b1 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 989980557 1250 989979307 989979313
    0x160204110a0221120103060203060303161103010b0108090a03141201150906050a02070e090a1b03060e03070c050603060619090906270b1c0c03110d081623 68
    0x1040d240800d40c00c00c0d5030104140014042c805144013011800d0500c0c1501ea20260046c0d894a640000030315601841c1101e6000ca407592003000c4c100001d152400c00b0000068009022800d12400151110041266002c03442d510425515000c070344500100c440c2c16124450301460007141c0b4040d100c40c04800d03007222081250415a08070070310b91042c6050010002072806d03030700303180061074001d403185550b115541c0c0710f50081020a20150050007030040241e4003030784a58100400c1c20090105c4002403105031101c0d031400311445030340200030088804669015402288041c100000c00005070400b41c80340c4d40003281403004403210600030090312448001600e500b01c185191141441c2641e0141c1c1102e001d401d10080071074650313141c10792080d80101c9070b07802c04241d100f90a004200302d0352100800008241e99010140144030010f0541002d480c001d40814001180440078800c3d0b042e1f117990028003400080006000c440e131000f4803075000c0340c40b4240510140450410a118050400e040e41a06030 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 989981807 1250 989980557 989980573
    0xf0f061606150504050712050c0405190e0907060503130317010b12091605010e0d0501050c071202010908180301200d0510140603101a0910020c06160204110a02 70
    0x80401a0000091070111005d000c1881d040000400d00400490404040b5441c0d001059914259400303407006003034050803503288220001e10480f50717800ca0f0b2044020841451001c0f40c280381000c0303015001c0da503441d15a6461521542e1740c1c5a0318441c1c44c14150100440d079812590701c2d40f002c090050007004064002620b0720035940481d490124094008036942e0b2207841103414030394003101c84404440003401c01d04100d40385000805c224441c00c1c0380007411540b0303110810011903807500203007070001e004e00d10b4846e1036941c05500780c0c01c039018204080c00c1204280207030007240560b021603070f0060788050008903500b0f100c1c2c03130700500c0301c0140c50b540c600c0c2500119201187d0382251140d1030b4811032600113458280c1c131f00804240c4919800025074054a800000941204005040701000340000c1e0780e1848a0b0a00c06a291001d4110450302d500c11031100741d03c0490240b00040040001f0001000300e4a8520304a24140c0a60a80502260050f407a1403043c20410364103000b13424509042c0e000703071440c1 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 989983057 1250 989981807 989981831
    0xc03020405070816050706180f1b030503090906040e010e0705131503080703110a0c05040c0807120f0f02130504061203170601090b0c010e0601140f0f061606 69
    0x9204001d22080c10080880b08101640400788030043c0030302d44c036007170841c0d07103040034100313031000c0c0481c003144000780600c40300580c0400c80080c0c4904070681c0a0011b520748500700c4201d000324148144009403ca038000c1c88200c01d07178500101007076009240103100064050903401d4940c2510540050301806400c80e5800b0083c0c0e0501d0140540c010035689410442104a84401082d115642c0006490601c021505400b0103000310b10902003480d1604c200c40c4d03804420b103018213001d103c5000d2180211f040050301140d050040030080d0141d030481d22a4032100d0601e190400040c1b00c0d041c641c9603400d484440814a01143c0d02c000d003060700300704041915a03030801050109607801035011148211a40c0c0a007000701340d00650380300059402082c00c1d100c0d0b44070440100d40302030141d04580b00080c00003e249480003015840880070005030010340b4166aa50310300c5d50040080c80511301c0c0c00021180e14507a040c900381074030f00d5100c00f00502440c1000740501564489865560302241d0342d0ba5100445243c3c = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 989984307 1250 989983057 989983061
    0xb1804030e120c03060f06041104031127040b0c220306150b0412081308010b010215060f0904080f030117062d090c03030f07210906050f090d0c030204 66
    0x100b80d681e40140780c40300300c0700003090780c60300c0c0180350100d682c038581c1c0407030b00c1591103030080b0380c48040a03002c5589aa4403400c02040140890203203034414000e0b4544542564039541202d2400c14060001c0c2520b581c817a01d5081c0003400c01030903000300c42002c010780d280a20b01c0102c0c4240705440110000411400c5141107030444060362842c001e009114001000f07071b8920902118140c850300303001851521018940615a030060100b00c0309490740510020881400c15401809003507400d0f82103606901100001d0002c0d4601603400c107400a142001424032810f200d107070320350001d200d01c411a02d01000b030740342c082882e042a0421040c0203517403007038680030400c100140d5802041c0010b8100020485800c591189015011568a261328000000348948003e0141c0300300340101400b941d0381c458079103a16414503840500102c0b07805041541c0c448070483c03d8210b203420410036848890441c0d040160503101da412800b1003250408041250602c3ca4460641c2c034044544900c0e12503440754158810001 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 989985557 1250 989984307 989984329
    0x120d0221030405061b040503060c09010e0f01120903051e040510091503110d060e061c020603060105070c0f090c080906060d1514040b07090b030c0d0b1804030e 70
    0x1003480014002e00001c00c2d004034910f500410740c0d03054440540e00d03204015220303014039030080342c0c180030340c40400880b456440c004110310a000d90b15580041003250400c00d00c10002003c4500148a12410240e0b105140d48059220784c0039040c064107000500070001d124030030112030003000c108040341c00c1009044c1181e000d41c0d442400d00742007120500300391820718040c03001000201010b8036210035280d00d021a40442c1c1d4016440341c81400300350b07120181c0c019036400c02c1d40d14a000c1d4584070b1180c80702c840d84903410518654002c08541c5182c6410004452603080100700740c3c0e00c0c40051100103684207869840600601e0f0340c0801141006410502a02c0b1010090210303034590003000402c417455540e100081c01c0f8644c04002c140d07451501041220081135014003488101c84408240011b01c03444013a100c0c8500c44942d100003000e621401c030200680002d45800110f40c2080c0100c82d581c0d12075030403a0f07110071806801c1410040b0b44008203141da0000361825030104814195800d06400c011003051 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 989986807 1250 989985557 989985613
    0x80702060403080c09010c1a01080f070e181509101518050901060f0803070203070f03020a030602030406020d020f090f1207170c1908070e01031e02120d02 68
    0x100d03140c50348010f442800000d0070701d481c203000002c0300c03a03250b802041c11140080e008003100c0c0d130b00c4006001ca230014510a0080325480d10400d01c1d403c0e103120000603098245c3d110280352589075100c2c1c0c0e0054100000069505185010b03c050852090b100c02b0a91071140300c02c04d000741b030340314907032040c103022504092030182c1250381c491001e0080e8180c2448180d04070745140c900141a6403621016801070005800c801d003c90050341000603410000000351807040c0c0210b0030350b42d40c41c2d0795841801c01c00c410b510000303400c01480c22080002ca80c1e02d0317014551050180c000545031207018202a004c0740d210b15250642904003040c00c10143c100b5071076071040c154060310300044060719100d0036682c81c81c071446080d41501da0500c1d6500740c44010301c90300c1c6080c0300183c00702c1c8942080d0404400d1025840c003070000c45124140c0c0024500704040b0202c1c0c100d0313402242c07000680d9203402e8443c40f5040356042c142d80003102c49079040c4000b4010802d0068019060780903000c42507241340072018141d0004061 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 989988057 1250 989986807 989986813
    0x305030a0f060b1b01060f1805091c0f0201140f01080d020d02062202060a03020417030f0715180809150304231005010609060e0301020a1e03020c160303080702 70
    0x60100040703000407680044000741e0b00040410300403131034601400c459088400082101d001c00250501c2848a80d0141142800203100740d43c0c494000a0341c400206100b41c0030340c8110400d400d8111302038803407000502903030300c000701d602030124003018030303400c4244c844405c2e01003500010455490103001c01c403e410001c0c40604a6604c14a2001303503540030281c0381c0d0714085c4048800c40c41d03201301c1a451001e102d81c060f10903070302c4148010020b80250420f10402c100c199001995252a0901000b12400710050702100b80c02c2840c00d46800d540302d5a03219490180c165240e40d01d018402804a49035240340c80f581c0d819a940c0b1000041c0010a624880e9420010406100303200004002c084182906025100040700c07015001d116549080507c010010720240f4203800131441c1c80e40074440106a4506407a01ca1540c0d1400f410300d401c034441c2d60420340000f0108003940800c0301c450710106c0d48114081c90007501309020780c9800c1d8240002c0b44240440950b400034108105034201c00280c0c0c0c0130780c460020f = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 989989307 1250 989988057 989988059
    0x306080d020601060513051201050610080103080418021b0705040c260a02040512150601080610030c05040b0f0702180f070c080d050106170a050c04091112040305030a0f06 75
    0x1a503030300d80c1802202e050140100e106d5040a01c0700c9440b0008050050075040c0301c80707600e09158000c203c00d9800c1401400c1c580002d010407030043c07686a04070f9522190305d6190610342650048901964170845892a0302041110395910302c06038a030202c0340403540074103c800d2030001080100c405003074807102448542e080402c1e03e480d045040110303c4840030801390700c0381c0e500d15004c1d0003403156400c01e640c400c500e091645403403500000d00e10440100d9801e581c0450711064015243c10070304a585a5012001d40032281c5103d03c29000070b003102030241489030425440b5929103289030444030300d40c88104800311b4941c2c154640f8140d0b02040502460181c5400d0912003c01030a400c0010040000e101c4012543d0b800c02100c941141c04020f550242002256101d00004060720101001001108008408101072420703074402c1c10f000c2c01d40384490038500f03450008404060104120810003000003400489080065031100ca40f0481c401c1d56182d50340c0c0b400150b00c00c01c9500e101000c054072031800d50 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 989990557 1250 989989307 989989333
    0x3150c070204090c080d08040c0f1401030b03070f1205011a060906031b3709090b0102210c25060302090609030d0306090b04050912090a0b0301060f030608 68
    0x3140d000c00e80650b0081180b40260504504451155110103200d00c0b4410500303034403070360203680d59004038031500f040300f034107070b51003111b040361854600441c81d00b1150700300d200c54658001d5009007403001001d0182c8111a80d10842a40030348541e6200107181400d60039203404110702882046292881150452102c1000f100400d01901400c01c2650048000001040d003150f00340c000740c9a907200e40e800d01030b51198403007007158000301a41c201510000e400703104101940d50384103000001c07589a50741c100300c0501d09001d2501030002d440c1d00070f0541c010809103035042c801c90365041daa07000c0784e605038a90b03815800c1e070342600e40f1540d039403881a540811480c00700c1144401c800d4408440b01443c0150300e1340705800003e55640300d1085c50580c1440782d0043c009089030550041011540d400c0f00030800d46035104140800d1301c07001c0b1080541c03600300b041007080e1000c1410143c0035020b0080e143c12002c0d9200c038002d0f440741d03200381c0110010503500e070301d0300192076814003a8001034051034000d04000c11240c3c0c = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 989991807 1250 989990557 989990581
    0x20f0703080d1d16050406050301140c0307030f020c0d110304080a08030a022710051606021602030303071e0f1b052e0b120a08030c070614060315 64
    0x512115052529554000c0704072003550403542e0720f000074405032200040450740b80040208940b00b054003031400c4c09800507080ca4188540f2a200d040c1500c00703059a0368250310144950b02c001e080c40103069843d0201e2541c0c0c452403010b0300b00028100000d00d18440d922101500c10092900950000c2c1c1c020081885807110204046160300e501c800d07099100d032682c0040d20045c0c0a040009016100729501c02641d4440381c2e81c5102100b40195a081d8070801c21550403144d502c14004201e400e0301c0003500803000a80198024144a1050f4103040c6c0b074030311030f40d0020741940c2c403e561400000704081c9080b8090181c1070700400151006040c00764200410300c0c40a060320800070704500032520030341584002c0c406c0c00d0101d030b11070449000e050780e054413001d0310494005030008080442c062030254801c1c2c003804d145403000b2032106030100824420b4810ba4908140b07510040894511420034400305c000203919015405911003040392190452501200380361a0104114400142ca440075040c400e00c3c036982 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 989993057 1250 989991807 989991817
    0x405010b0a021c02071a190201021e070609020a0308070302060708130b040c0506030a1505040c0822021017060f1f03110f1b03072d02130c020f070308 66
    0x2036843c1d00740e0511801c2a030401180781c0c001c2070400c400c07100700742454851b800103010300080c500900703842e802407410072401c030b014540e60740528450111110340410482c0700684070587c030420000c03c6404595001c2001c20302c00b60b000702c1c0c0c10301c0f0102da070074201a0180701d21984000b880c60720352594a04501c0520b0b250340400030260100380c0c0d25011506005014008002401c2d010346003c0e0b5904080c11074000a000514108030700c040001c20210700e13890940a0407405801c607a5940c2041d8036644245004540c0b4013442c048034074a944c0c00d440c016200d1210184220340030303403100c800c0462009028022540000c140b20f00c40c070a0503030501110750700d001d89648103203c02d41d0b100d042004601003d030000d1028011000040101041700c541804c0c2d20130040110a181044109141c0c0854409a40da0701514200900780074000441c0746070724541d420540000c0003001da003138a0a6a1070f0300480e1010701c41180c0354809a40791a155540b16070100300c00308489450344001d0407e64a103803254441d502070 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 989994307 1250 989993057 989993083
    0x3020117060a1a0c0d091d0402060706180f06020406260a02030c12250f08130f1203060302120a0f060e2407080f06091302010315140405010b0a02 64
    0x30700ca0507000800101c40c181c2e40c8540440003201c1e82da8516643c05040e414092091420b81851f2000508010724044013481c0155409000141401103a035101c034007034259414a070300071004200d207040100d2410310341c00108600072100161756a081c080d00403d1805907140d0140038114503221802c00b00c1c2454020381c0e12903007520300140c5940707800b445110a44220006c03d01085400d00030301420308aa45502c04510407a401140140180ba203000e030360008071b060002c0c1c003258640c000035646000d03584400c5038880c4950f451104c542403a550b000d00440011b512640041e030380b10414421801e0030328204460740c80c1d510060030b54031266a216400c0c210b0007540284000c1d2182601c80700100204000d1a078540e149200c139015039486011050996000c1343e022000a4910001c0f030107860400041c0c900038003002c2c104c200c0c640c0e43d0316403041c40ca40842e07508074105a6600341500000080807141c0015210b031900e00c0707203540320941c2004191503040e00100700500741008110b041c517800044496007258 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 989995557 1250 989994307 989994329
    0xe0a0e0307030e0105091518030a0b070f0e0621060f0d030e1302030106360b0901020a05030c0709060b09010e010c110a03080715150501030e120f0403020117060a 71
    0x158520048031709024800900c0c1e0025080402c03c011620b01c44060220244041401e44a400d081020907959849188019100c20386920225a955124015010742926542083d403458103807000410801c4d4440b0400c01d8401c4404040341c582c2c1c0103182d0700150812412586060342400c41c100068140700c0e4090014144098005401c80c0b603281e9800072010310850207811074580d030751400007508141906585d02000101c00d9070100110442d01d0000030340c11911020001d000d030a0804c4504180d000c5c046441c154840c0e56010310014a0800041401d501c1c400003900b03489141031904015612550044d01d0b0030082401900d01d143d030b01c0240103581d070b4024a021403001240b41042c1c008040a5210950406c942d1200441484900401070070503a01c00c0c001041c1090180380d842040b41d40c1d81d68084030b4040e444a00308255031007138001c042e042e030481c4145c400b000040e00c548400c580c01940c4002c004080850f00700103541e000380014101d0b03240340c190100246098800901c91604600038046840 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 989996807 1250 989995557 989995577
    0x6080f0f06180106050a08061e01032004020d0614100201020c0613150606170115091a0909130c0b0a052d0a1d04061a18090a02040e0a0e030703 63
    0x42004d400c800c00400000d021129001d495403000358907100205e5100c0003500340418210004a007811480d0704032500500c010011f0b002111803518101d0000850551081d024402500b4800a5116420090041404d524007a25002042c010b41d0480b04100758250b900c148001000104046001c07640a40f5600d510078107202c2038a09074041034904014602800d25203c00401e10580000341269101c4062401d441660b0303a80da4101c0c0120f6000140c3c2d4001107441e0401c01c2404511150314410080751200386080030b202c18045810b104003140d1980d819400c44040d072003442810300c124009001c081200503e4407a4605002d851485407242c0c071451006403010098400c2140b20480400e10307056540e00b9500c0e4583d2800406540780340362103502c0c141c602440d204030707885e19100e5041250324032481c01e1510142103082002d04d0300201a1010014401e2203d01c0140c1c0d540707a021849550350301c40c0141c0f501e080c0300c2c0b8417a00400051144560b20f14012500711501000801e4a40140e490701e0602500 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 989998057 1250 989996807 989996851
    0x21060c02030417010509160303020d140f0a030b090903190f0909020c160f060c030c050c040509030c010b01020615062a010b01140403020607140102070b0a06080f0f06 73
    0x5205a60200c49424000040d03c0155041074009a0054030306100f280c00c0c0c0b00d03a40d11080d040c40914400100507034400c203030b410602c6004422400120341142e020ad400c1004484420b422035100d601103d00082c1d9841d4000542d01e01168020703000346042000f1410722408211020116a02c25400010b00c00c0500355007008600c19103d5001a04481a05545404500c01015640d00a440c2210480049584046002d1510010301401c4032541e550700c14140a6036141900d6800d00680e040c0c80a00525000307010644840c003655001c0d07076004008659070140c090409085500c032920f40c40c11500000103000888448544c00001280c1c1140d80c20703610501281d8540d0200010b8206e408800c600c0c1c030400005040640c40b6011200c0c003a01d502490400e40603c800312841140002503001b4030030b0240390046915007803205a0b83da055000185424610f0f01c0e107d640c03200880d4040300c4c041e00c1c5c030001e0100034400d00943d1018030141000f444a121100d14640c1c03280c3d0028030594031542806444450 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 989999307 1250 989998057 989998063
    0x91217071103031810030c09090b030f03120f090d050405210105090f0d020c060f0705100f020403062a0e0102121207030c1407060216200a21060c02 65
    0x31444000c040340d07500c100f14041040740d0f00b04079181e248030321103001645c01250300a020741e00300713040565109441d440c02c10a00c00c008043d8030307200941620550f0340030507400e0410070044c4001e80c4440520b01c010302e80003401a800761070003020a8500e42000120303081a40c0c000e0155425241c0071682c2c4035242d041c5255440c3c1240c2c045043c08015030070134080c00003a4402060381c900482400080e40c4448000c14001c0e41e03103551a40701c2d039411510400c85004a04000805000303070521500944a800030642c3c401f0042d105150025010742758002130030410050240f182c00009840902c40310b25000c11020f2040241e810507884100380244104000d01d107038400d014800407001c0002c0496101c00c0700c540d940d2020319080f20f800010034a8460002c9400d80110b907903030080c00415540c90f2510109690300c0740650001e521240320100c54181e00c0c00042c1240880703541c0a20714103c0e0088600d0701000b04920320400b0b0b802803900124004403800381c03145e680b181d281c602c2e07000880403d41c000e480720200c0c5 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 990000557 1250 989999307 989999333
    0x1009030201140f1612090302010813080f03010621111b010f1e0510030f120311040b12070801120209040c090c09140907270b0c03040609121707 63
    0x840c0c0c21002811101c1da95103081c036010142d010764800c540e04140704409030f038011104c7c007001c0d021507411800107580b045e8901d0b8602ca0148281c14003420406209002c08840d002078004c1c1c0d003c0780180508084801c44030034074000c140c000100031303c00c860502c01819454400c400130f000405104100503060003109410140715001d100710100044681010801500520803402e51400c0e400c000210b1300752900c50760850152a040010380744140d40580d82c2e10202403d2109910602d91524505400c5c45c10440280006049000d500d590b22041120040c0842c0340092501040c49000d038010300513204150150202d032079040c2c4d1100d24644030340c10501243c1c1080c0e07115003101420500400040c41d072000a400844182325406841d0052142c2086000b80702260410001521540c421482c034100002c44002e4140e12030038072091030f8540107081c0e41ca0380030000190f807039400003c00f002819400f031294801805016000b1310f2105aa0703488480115048400d03d510540200d905070034010300200b2a0 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 990001807 1250 990000557 990000577
    0x1505061c050603010b060f070c050306010308070218150d05030f0f040e0a05040b0c180d120f0519112b08070c050717030d0905011505100903020114 65
    0x40d44810000d00002004a00d28024400c5903041001044035400c05001e4404c4801d0001e10040c00c0c00b40b50300403a13455030060b840a0300d5041012400007001d45062003418080c600a00b001e036562812401030000d10f5100a071004005212002000180319a00c1521030f420141200e140780d03090528103000d441d43c00303440584e80c0c04820004425102850040040007103a07000102030096a603015280f42c2181c804031030191011507018001000c3c0c8050764000e010f00003031401510351050041d8082014222400021200d5402482124444680280c1c040c2c60603207940c50101d15112010b00c42c030210455400030001400003030440a65401414040c2c0030104446404803001c20548281d26000221903809800100d8040408a8211071040340c40e8817003981c04c14010aa06450441d034208401098000410540401c0c06141c41720611402200340ea140500008505403000c08a002d0500003258841c40c0b00313560030060f2860240e00300c00d6400440c1e40900381b403500c01c4d1400ca503092079841812512 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 990003057 1250 990001807 990001819
    0x1101050c2505010e01021203060d0f06090f0c08070305030d0e031b030a03060f06210e0d0e03060c19110a060c0c0c060e15030a021b0d0e04050f0a1505 66
    0x44180074440d000300c00b1103000341d0314a002e060242005980340d40c04950b801441800410000b060342c03d24072250904188214111501032070151504000c5403407441088844404c100714070401e0103060482c420107410454043c1045900d140e40f0251740b07125425289070503680300e4100d20300c2a0014001d40e24010b5004004d00c1c20807441c019515101d034001c04103038000c40d2a09a01294242a0741a41c0007a13807050b480310543c55196018088210300400d880d02070303180e12551400c03103e200c244254036609000c0d407036500b82c1503103039010135051540003081c0081c142828007074400340d00c4070240340d407840304002d04000c00c00641d03c81c260b87c240400504081c0000d17041c41612103c0990040b40040703024040c144090469031142d9040b00c00003903100d24603038000720700d4a8140e4046a98001150007101c035040051500398580706400c05500005c548401039000814a201c0c1030317400a10840c40070b07504480410840c6130a10b4044c00304603001d044410510350340c0200000d54007900d0706a0001d05801001 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 990004307 1250 990003057 990003103
    0xc050109141006140604140d0c140f03010515100c0c1d18030406050a120e0303090d080405060f043f0302040f15120f0501051203071101050c 62
    0x8041c1e90b078080e02079942c0d034641c42d001000444504050107101c103080d00415451419180c8181140c200f00c0350440240e0081810700340e4000246180380d04d2004248044600c0e218208010400c400c12640010442c00307641090308000c070606040100c850005011030701100304a0b100e210865490421417001407080382d00d00b5010a20481e5a4450b00004001c0c01c52504160340c0e4500c6075518502d4803403000b446520920003448000c2c003550140407100410310344003a00c1144041d0503400d03500d13400c0d40ca500c3d64000000784072840710140b062410350072890806404508003561070581e541001000c2c000320200c0400428200181d69540000a07065411000c00310802103403020320910308409460851205100107000e00c40c040e002341c80c1100c69040060701428600600f5410420381c00800508201613080c1c101010041417069007900c42403e0b0340043e40c2d605000a102e0f06440d51240d100c4982d2040c4414030000e4007041c00440100802e191843d200c200441c1040e04c1c0ca200000c220800c0189802 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 990005557 1250 990004307 990004343
    0x8150c2a010f1b08060411130306020915030c16060f020d0f060602070515180303070813052b0813030b0907060f05180105091003020702120d02030702010c050109 71
    0x101581d6801c4000c2c0400c00800300c034404a031100803984003000450340f80000a1014070300b56001400000c09440b510349400480300e403168030300d41c542d001120005d601141d111558100384580c4043c2410881c0c0740c51550505c00340c504064000c500c281601021301c20104001c000182e0010811100203c2c0c056441e050110304640c040c19400d44143e003650700e000c100045041c80021452308403440600040b02d410b040a0ba0680d407503020880030545100415002000c07900d04000800500e4043c111240d15a080c0b56071481c4460340c2644540d20a15142c02d400085603888032000d040c1c604030520524000c2428074101c0014001c0c180011140b100c0b00d4000001d1100651000b84561005803d031880c49407201c006507008401103442c80000b031000d129882050020b04c0700c075480013405040003428140c1c4940050381002e0400312200010341c0110707082d401c5013030003e030f501343c1c404e64840600100000784030025500c1c01520380203810400600c0c92101802401e41c040180a500070030701940d091500c0d0 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 990006807 1250 990005557 990005561
    0xf08070c03032006060f010503041103070e010801200d0504031434050d0f11120c0115080309130605030f06010602060702160303081f090605010908150c2a01 69
    0x3010f80c00c01e005034004246081402044c075501c40c80000300050702e48104400112803d8000902c1195512000e4402411641d81040a00700804207000c04164542c10000001c3c20f41d0414800d00883c844d80c000ca5112a24000040c0d0f01400113807480050035030744604088070360004040c100c4100b5240002e1102c140100b07401303030301241c0441c10101c0c1e8401344606518585414a0320020b4607581000074003410480c070980d901c6018001500e040d00c80301402d0b050086c28481624480c8003c10000103010784e65480a002d10081ea2401114030900c0504e4001d4640c1c0f2031007880c41340c912031407030120202c00c41c210603403205016010113400c44d403101c5048041c455441100380507003001342c82500c002034245840003901e1f0001d10710400310b0f007429030300e9550b0039118014041d080401c0207c0d060b4a500700061030f515003100901041c00b012841c0d0b482c200014140180c00e030815601c9030440640841545008005160003103180030b00c0e03c0c4d550700c91021070005201d0507407160003054210000d13212014415 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 990008057 1250 990006807 990006827
    0x2e0e0706031a060706020724050a1a0a09020a090812071a040807030c02062214010908030405060304060e0f0c0a0e010302010e01080a0e01091a1b070f08070c0303 71
    0x1074404104040010103803981211801d560294021030801c9048001043d0790007030000c443c425450584840f601c890410840804038100c24621039032181081302550090040102c1c1c0928011034a00383e2507014042000c807007403030044003403071034000815044c200d2141400e00f00070700e20801074441c45880482082d01c290b0007002c00359030030703c0408560f026035a0000303216030042e0740c0090060320b00941c0c0c0d0341c00e480e4504102d00030380e448003080c0821340400d4201201c04160148100034102a2410003007c03080910759440c83e00d04100f40101c0601455000008940980b10110f4060ba101c0ea510310b0711402400e0324920320302d0a0f0280c0500301205880025071034880302001c80e07404500c10b445102400f031070502440045e00148138001281c0980d40603140d80d5420602c0e03520b000c600b000c080b402440c20f440c000c04049503001400a581d04007080c0030980b02350854162810383e1269907100c2020403840c040c007036000c0e081d400c2b006842d8007081710030b07021151007652210300030307a41907a2400c002d0844025 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 990009307 1250 990008057 990008069
    0x7050d0510091127011e06121e05040308010801020306100c14120d060602160605031005030f0d1418060a0c0b0c1c0c0801061407080706090201110a03022e0e07 70
    0x4c00800030989010359000d035503450b040d4107140300b00507203480d4003100d080121860391983d5a94484442106a4407043c420075403000c4080042041d04140c5801416a98141d100f00d81992050050180d0ba64039003850015801d02441d150048024600f0507d00c550034000070082d1511a0261403200301d068040a0807000c02c3c0e22000b001000e0b03941c20241d07281c1000003803109000805203024032007107001d0005150001d5603407000711222511040420324041100134040c5132944204c55803224294840305001070544001c480c03034202600c0281c407000c0041445102c505c00c07007000c155507290a1244c3c21042005410034801c0a090030804a80005588100b114a110620320130385410350b102c440c000c1a05160699440c10501da00c3e185041341c01100c00341060508003400c0150f41e000c281801d01030710005010300000a00d280c540d01c0054031141094060038400d4006000200c0400c0c0c011489500301004d0001000c81403400e915108910f00c000a002501c903883d0210109000b900000e00200342d0f05 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 990010557 1250 990009307 990009379
    0xe010903020d0504052d120102040807240f051920010c020c090601030f0212011403160312120c091a0c030304120905090f0907050d05100911 62
    0x2210b000886840c8101e0181c2900443c0341c039200c00c1030b5004040d056506404094148009142d0b000004501221142141d00c4aa402050500444909010207001407030710042d240104085202200f0403981d4a000c1e0740f05105071094605111030107202121000301c3c2c04100a03002d91002a0080c00c012500004803c2003294503d6842c0145014400c0c2e1a0444264000707010035140d9208000c09100000c00c0305040540303400504e013444401d400500951f540002c1040340079814401c2080341441c0e0411080c1c420383c440c0c60f0100700c07c1140449102960b0300000803042981007040281c4507207205c006d4041b0700d245402d94000d03210b94003250403415102410f090510b11a410b0840c00c01c1801140c000740c400c1d402c100f000c80d000410880320b80303481520a0038184a8140e540c00040d410300000c444110200044804000e01404284001030241c641140d402801c43c00c4c1ea142c0c2a030f1820383c5c40721039101543d03960b040c0c02800041b050620044800908031082c0340040d8150007204508000c0e9410801 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 990011807 1250 990010557 990010573
    0x2109120f0b060d321e060703110d270818060c0c090612070b071104060b04030201030f0e03030a0b03190201020307080a09050301050109020421030815010e040e01090302 74
    0x11501900c030360b8079250000c1c080700391804e121070b00450002024010300034080000d801c0c1220b011080c8024030300010f88880c04c0052034a41c07128141414802001c4130209403600840840c0050f4100640305a8441c011f00091003149103400a250f1108617400401101c40d0102e00380200725291000323000c281e0303070300b091a180f148a50b002c1c0004c134001d40700d543d02c941c0c000e90060102810111443c40d0720001c0244200400e000e18510503042c05403540102000040008409040c044164084206a401034900b0821186002c0c03000c1501d00840c00004c0c101a00d80e40440307000701040e00100c5240c464501034a9403404c2816205004202d44000c0074000d000303914401c0707090031040b000340303007010b0301a006189094000d54801e1030740d9000d0b00e00f98080c000b1a00d40440c60351800d10032036002e06a0f1303500051343e1700d00b40902d0b80303411008100b1101010385140c4201c000603602c4083c90b60071911030905400760120240c01a1483c28248614603000b924202d40c005039200150000c9a1050103502070b1400c00e = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 990013057 1250 990011807 990011809
    0x180105031009081603051303050a031404080d030c1e231903090305040e041211010b010e011101020903031305150c0606100e0d03080703060b072109120f0b06 69
    0x2658402c0009401c030320003400082c101d225030841c00b6100610a2a1051030000d291040ea01c860791382c1d810640c0c1d80e40c0810f01280402d0703003244803181c0c15a8450303041d0341807502e00f2407002c3e6164021030802c8209030311030b03402c1e484160055091800e5440340402c1d104413041154002070104490144082c041c0441c1d04c1301d1034a001c6c2c581d00700c07800c02050b00074108400314a00b02c184c0160441180440401c0410071000548061440440780224800c0003510f03082c1c60b000d0402006000640d000703010f00e9140810804140e0f07000742c00202602e9080c24401c11f0b0984501c10580203001e00895190940000140040d95256251030041604c1040b528a0040d140c00d61461000d8081c0c4c2e24003000a6000c0d0020172014900340c2014010641645095140f0749441400f0680f90511540110042180c3c5818040d1558141c043c1d4070160408030740c0f40d807d04a064072411901400b9070450528580410014102c861003034030f00c2005040f040740c1002e101c6c403c0e49407412a807109004140c44c14055100400d0322 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 990014307 1250 990013057 990013061
    0x1012020d0b090c040501090b090120060403120c1b03090801020a020601090e0703030210110f04140907020c10030203150306011d0a09171c0c0c0303051501170c07021801050310 77
    0x40e107070181d41f138440140c02d10008662550203035a6850600c4005c80424050700d140d800f0012580180c0381c060125800c0500c0c016041d00c00c051a203003034440c2005010011300d039000d455550300d555005404071101801c1d09054800d400180c102c0c041c2940001400002260001141070490740490700403c944a0381c0d01c0101e03190382241c00700800580002c980310101808a821469071400300400303942c94064440000e40240d40720340d000f040610b910b0410502145003e40000d41d12030070600151180d203101000240e010358280034060181680400440d055111344204454108005811a030455850380d00f44100e022154004404804c050000500107403500d0040001440e0710228411003c1c150f03032080400e030b030040120f1107645036800d41c1c41d40402ca140d0080d0303100418644c6078116201d0181c100142a600020f04c41450809144c1c90f4044e6079034496584819003290000f6085141c40d001000740b858418004081d500412280342c00c003c14049200c0c00b4100c83c4100c0c2180d84082d02d407805102 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 990015557 1250 990014307 990014309
    0x150e070807030b06120c0d032604080307111006080604050d09050d03140712031e0614040203090f06093d0e01090c140328021012020d0b090c04 63
    0x48008241c2c04111103082c0071151298005e0a101501c1c0410015408900c1d00e40003032130190001040407d660781c100700c800d0021400d1545524085505242070b031254203240c440502002c04001281c940c0da40b04040601003500f40700c0d0300e15014030040e07030f4492016075102000d0302c060f1140d00419004020060003040c1030411140c000d041c240c80e81005480c00e56548001c5405080780843c00c203c4040020030307a03c0004202040c40e00e002070fa0036540b2102c41c0702440101420b048003840c094042c011000001803070041a0021100965030384d0b07500b00e40c40d06140c0d1421943c1d0381032044070140803025001090b440301103580c82d00e6800304000100100c0c440b15448030440800041185044d40368900c1d2600300c200452072070070020a4030f4400f60707200c0203c4d4501e0751007181804092103100342c1a1a081c0300000c8540780d9946d6243d003030020031030b85140020740ca04000303120300300c450184041c607801b6a04e51a41e190010100f1911032981e000e0003009411288007461242503008001010f0700c0c4407100b40c034 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 990016807 1250 990015557 990015563
    0xd0501091b0f0e011214070e03070b0306060702040e060403030b01020606010813030309051c0207170a02130b011b3203070b0a0e0706112803030216150e07080703 71
    0x3000c0a002c1500681e600e42c0e146201d41d0403c0b003201110b44444c0740c540105080c040542030090110301c3d00b0040204540c0044600a20a0308030349400c00102d446401620b030040c9041f0346041d50b6562520008004003040100d41c2400d00401c0f007048203158243c0d1101384849020380075a03600341d480c08011034071208104d494900c02d07a0390001502c04280300b94440c0001500c03810455081079040b075140b40e05503004107028801640408424844480c00082d418048440d28006001007030302580064107110080403488405580c0380d84000c03281e80719030040208112030b10080008038800d070512460301d811100c101c517505072100f48401b9102460550310001418108040c40c108022aa40c0300b0070a80003900b400d00341c03915020720131075030442400100018409a12030b01d01da00d01e208503603414900c0b002e0340656144080000c8c50b800c8113074010395a210603814130300165a003c03940d0048428105188020b071001d1f07001c0203d411081910350041c0084043c11080361202556148881d42d074100500000b = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 990018057 1250 990016807 990016817
    0xb0114040506130504030905041d12040e1906050405040614130519110a120302070b0f04090c03151403010f180308040c0b030412110d09140f03030d0501091b 69
    0x80400030980c2c4c811504903101c1e06c2d00390000c50f61200018181c071030076401250403800410a45490316070400000000d80d04460b02030f070410346071007503901c1e050100808210302c81d840003a20050800c1140d20007400303008014400c00c82410300d030800070020030054141d4a0350003c203001048001c081c106000d102154004000d00e14101501d40b80d24080c11445003c88a170461070400c0b004955633080407130040d00b1234818071422030070b50b820000d203000c031700d5401902c0c01e02040003d02c00c0d80c0315580c1110241c400c1d51202080708080e1020490080c861041404520300f00c469001ca40c1c144030074002030403070b00c04400912801d4101d850640c1246c0341c0000c00d080003030a42c929500040d0041000c3e130303442401440340c842c0c220780e140e442c0d441652041b10f084a0528200c0b40030318403d070304180d1003000040340030010325403003036040b10207090714001d400764401d4011180c140c01c1207980c40c0c184000d5000000b500341ca031612045c81d00c41010300000c0c01349204560030308031994080c4c1c880e9204680444440d0f950 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 990019307 1250 990018057 990018079
    0x1406101e050c031e0306040b0d0c091a030109140c03010c0c0b04021c050d0f09050102060a05101a03091b031203190e0f0709061a03090a0c030b0114040506 68
    0x1070351142c1c050b22800d01c890101348030f4241e600282400784a84908040030840e03072890b22804200840d141110424030035013160f903070a00032a0101304400c0c10f44000b4130001070000d14a0400b0a04c445041104590640c20002e1100420a6041d6401141c102038000c50300d01660b98000c060a1700d072003036645c90000d0021a40e0b1004625410b0b901e6810500241031440386d0700c0b84241e901c0d4208004542500c0d6030b0710681d0400b2400b235002d0300001d800101441c250717500d6400c0c1030000351607441c00750040c9519511800400c00da0151041100e00030120300d190941d21000f0803200c010541c0044500608030301501d02402e82c5016903292545442c2c0f8002c0c098118580060782c8103440742c0001d000303100c01e075103e00c26100030035040e0705c05c200b9031400321401031600a1b25412918a0b0240580001001500f8100100410121411103620300302642c501d254891351408011032902070840c00142c8903002d181c200200388400c00040d07a058441800724154043c290200b0301c02501c80650b0883c0e088068075030 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 990020557 1250 990019307 990019367
    0xb0d02010309080c070b03100e04081602280e06030105010b041502030706180b090f100e0c1e100e09010605031e070f17010311150d140610 61
    0x808040003d204038a800d04180b0126074480c507080458010190500000040c056259509600d10004042c00a103881080c90300742d030781c0100350090081c142c000b10006d00003001156140007401440c10b00c031050a4a0f1240c100348007007600981403280c03445174016200071560908060003454161082048500d10309498030402640343c002140c1090300714001402804006000d600403524050802414403070110b009062001d03803030310044c0480c541588040740041f1407900102e0b000310035164031400098a100242d0420b070400303010402c071b241d10043e03610407400041d00f10500900d180505440c4140a005402e90139a00b10950000d403560200042004216191103100119484840144c1103a8000381d08004005039902c1550041d01003504d412072401800e60100440346544107000420b803042d49180c80b080c14000c0d9020916000b840304101100c41e41c0d0301403041b201e03030520503003003000321004500c09010098001d440030351143c0c80c01044061300c06d219508203101d5407000c4401c00d400c21402a = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 990021807 1250 990020557 990020561
    0x90b040b040c080102070f06060b160816050a1a09030a0816030b041b1209082502031903090902070308181009051005010803120a0b01120e030a0807030b0d020103 71
    0x18001c4551490b04000824180310a00160084c0c81c070524103c66800c0d618501003056400641200040036800c0c0520715840003036010980d401e40e0410b0b201a6030f107110902901c04641d02e888007800d81e11552000c0004c2246828a01c040d00c103e52000d411141c541d8403030302d600c902c03400044e1070001d1842808142d055503a03d40843c510401d6080c00901c2440380808101034600141308402070313151512444034690b4101c541942d81d818842c404000d505620f0f95000d6a0780a00c460302c440ea0031941900c202c1858100b000980381e950020122024040c021603402e83c007507070030001140010744984000035840c7c2c49009586602d689601e42c4541540d4554800079a1000d44203a0040c80c424040600c5a490040c070808000714050702c00ba100c0030b803401540310261001a844143c0c55842007049501c240c0e4200782039500f0403400703070010a4400721100105d450ba5810b05080c2c1c1b01501c2d07c02d441d044030400200030001c2040355102c03e0304660f0345800944c11503a5040381d0315000301e420362652006610035 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 990023057 1250 990021807 990021811
    0x402130509011b0309050105090f10021e040e010303030b1c060b0112020d020a02160e1f081906052a0708070b0708070225030b09010e0a08090a09090b040b 68
    0x24000006080c1e660b152004881041c082d0f000b80420b60b0b038803a00341882400c0c0a541e5202c90058014003040c0e040e000c20550f500d802d00d54100d8001c0d40424074081c1c00d400180c4000702d80c1d40e082e41035a202da844008284441c0030a1000703d0100b450548141d1960400d00075448803500c100b01095000341e0103456603030180a440d03900074100907a0320140003400200c0d1001d000c0c030160f50707440140c0f11508680082d280c4584104c8241440742c200b0b10070010401c0d0f41209550002e00c07130495000c101401000900040762507040380c80719000d5500742d65100d400c1d804a4904250250006106984440740080e0b00c07801c041ea01460f801d00b644203480385001d000781c01411218441d1420358030b00007170b649861074948020790382d5400003500c0c502803085656040000010700e0405002031200c8800c04000c8038520a81840b00a125140942c00565004001e5001010300034446c070540b412080c903407038141503552001c2005407240701802c03808070b2298960700c40c0305212a0b200b01000000c3d103564880101031000 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 990024307 1250 990023057 990023071
    0x1314060f030402040e0610050f0114030126030c0102070309050d151a0613080609030427060503030a090f09060513051005180603012a11070b0f180102030304021305 72
    0x11072007454402c800c10001b0901c42c002003140d02000c1810541005000248103861070304100406003c1050507111008490440f115007215442910505000c0d5031502e00b16403440080b4000030480010f0310720190001d20300d183c030a0341c0f64403055890307a0800030280203c540c044c04801300320145640e4054164040400004001d0300001c0140307030740000880a40c404103400030707403111982c001c01030004104106900410404095424203060240f00d2114840000555a08210344803159880750025484071000d400040e003030f81e96407099040c0c09000c0c0c0740e0314822008400180b05000540d00c0e260702c00c40090715001003142c0045800c21240c400600310240103002c1001e100400000d60f9501e0722603601c2818400d0316410000d01d0a0700c1050b084804000402807250300c11500540c4007213406d040c00300c0440e064101200d1082c3c2c1140094501031980c0c0051380a200000781003200d4200c003074090200c081da03c2c0d21103024403500340300480c1c403400190b90094100c9101d60108541500750f030011544458 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 990025557 1250 990024307 990024311
    0xa060308121902040801140603060c0a140906030a0b090114010e01050d06090203090f16030c030308090709061710060602030913020d2a1d060d1404081314060f03040204 74
    0x40c824000c90100e81c8640e00401e81760395144070150070410b4a01c142640060201c000c1c28144c076140716001100d00c92624403504004001c898084405040c034240c030f060040180c081910791902c82260001000601c0d0340b1032181c00041c0000682d039111001c680e41c1000180d440342e00e8041828010b50742c070781101103a102820740380c00021a81050302c0c805103200e020090010100000710f6400c08d4100100c652210325013820041082c00410b030000c0d072081c11603030b241c905072804c3c4d52141411810f1010310f41141c081305042500000303182c1c010200c2100481d01c038200b941c0c030b510000007080c3d088540a1007204091b0304140f16804c41445c20358a040d003842030444002d03207049404181007084404180503210211031080380f003004003824840ca9500d400890403d8400a110540524000750074014414440e00e00060011981c01070b50300500b031052234ac0c5140044030b08080c03a2001c1d043d0005800414801050480001d0400455481d94045000a071000d4505403050508807503690000b402030383c0240d = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 990026807 1250 990025557 990025591
    0x12030e0d120c0302192613140c030d081e0108060109020c0f0a0305130b18040b010210062606010f050d0822081006260a12030f050a06030812 62
    0x80380e400420704051700d103560383c1e0201c00c810140016400c25440d400c80749018108042040c0c4043e28091444000d4200e1300e0ba008444d0a260a1450980100e04450b0580514100100c1c1d8541000c0c22a0140c0c030b1400700c8480155400c0c09240a4038001d104001a84d0711400c0100450340300c80e40180704182001c4240e410461085034041c4c540903080074101d00050002170180380b05c111a000540c081d00300580020b00c1d010310300011114103140021407510842e9640800000e51f80200512501001100c0061121a64405011800c4c6103c034245600091401c5085482820041151410f03515590100104c4508110178000d12030040c400441d0b000c5410840492400752040c0740520b40b00b01038022a0016080c400a6420203d112201140840c00c1030014828183c1d0341d070000a80075041c0040001030180060414602800110040d01c054451104d2008a660540140340c1d41202c51005101035120903070208101d40245c803020741204020710206c0321801c070600c20190440b1070511301034105 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 990028057 1250 990026807 990026827
    0x8010e070c0c0e010e0709060c0210051e0403060f050603060115031d060a0c090602030a08040c0e0c07052404150b060f09031b06190212030412030e0d120c0302 70
    0xb107085401c07440700300078031034010019aa41c034605c4070341c01000f034a08040c80d1031a00001800000c00b01030f0092041e40729400f04980d0521941c151911503c03842950b41c820445000c603020700c0d40c09404141c40c0b550034212007000c207440d580103850154a0190041c92140c0c46c1c40702040380217542c641141c0405031525450303180004107581071801c8038507001c00f0340100d00b00b49805408a4521102d03071414020301120030000c1903008400d580081c0b58908001140350348529011500d003400c1d8010f80c09200200060180c0443c8070070152111600c0b504c11114490000f000600703003400c88600c0015400c0d20407000800040e400d0f85c1c4007081e43d07401440850009070b11000109140c00601800840140114490580b4601040035150888545214801c4040300e10045001d6114918502800c464084101031a043c0300300502441c1040c144505a140e0826140150512807007810f008000790820202d1580c902000c034240ca40c3c1c1c10241c450b00545810f8500f0000a02403020307444050580c00d1000e02c1e13070 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 990029307 1250 990028057 990028073
    0x5010f02130509180d0509040204030b04050303010f1e0b0a180b0c071d01052223010617060108090f0f01020a020607180e04020604050616020102011b08010e070c 71
    0x150888010758500c50402e0180710102c1c0d0000c1c164141d0380b000c0c41c030303d07080e091001c152158540c1d40c40c54002e9843c001100030030302a2240303500040200013103508110500001001942c142d07600414000340702513507084030460b8611047c20151903804c00e101c0c200034180c0c01c0c2005014a00b494240100300240c84144a1600d038610340c4044a10702c00091040c03440101404200040c010300640640444944004c5907603251050140d90302545072005103880030b05600c250070f034031244144018000b003c001b03014800188108103510300611236050012036a10f0090a4404040313503c04080c00b03d580d01c11004542c050406820542c6c64004c103000d40d0003400c030501256548a050f10000f6a40d002c20500007444c00030000c00703203402c2100f010710703200c0c05070343ea8031004040b9854541d1200846c1c455000281c1540b14591120b6480301001074100754400b40c2e1b00e104001c048c000d07002045460340071000294051340c04104000042c0715400103015011944001c117422241615080c0c0d02d0f1861541d507266 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 990030557 1250 990029307 990029317
    0x230d1e030914010b0102120c06130f120306080c060910120213032001020d080103260d0f05010e01060e060705030c1501150512041e050106230406080304030f05010f02 73
    0xb41c1039440750b209440c0c0e940c04009403070000010000b024642010b0020741911107030090940e03c14460090a050184100d0088005219400c0304214200c2080580050014003444c40b8402140c00381c8180d00340640782c941d0680741c0004001e000110b41401d19a000c45589550300031031024a9801d200c44460254203112400c05140b24404100c1140b07000480c40382c0c0a8040015541150701880040319610381c85048681143d07030010309400c40b2000f5200c02d00c4895180e1000c01c3c5048c07070124880198041d0f603000002001c015450801c5180d80300e1400c41b003525024054100410160100ca051078100100101a0b040c0030710252402d046000451504040c40440c00d9241440d40d0001445040c801da06580e03490722160420307074a09040010040340b83c1c44000d0000d0060410321040c40c2402c80b1402d5549001544103000f00503194450760402110340402d51f1840e091100e001d0055114241440b8a405075074082e4001c500303041c9156104114a01240d20441d000e5480b0640c0003401101c03800a89 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 990031807 1250 990030557 990030593
    0xa0e061017100501030f020c1905032205130e0c011209020603010e0105090702150c09031609021804020403050a1e0b150f010813060e03070f230d1e0309 67
    0x4201c2c1440c040004050701d19980488142601c100425411201c0000b5140030300d0b00c1c1010007071041d803000d00f0994118014440d26070310081c013640040060500080e0392600350b44085480c01d14448032a80c6100c100c0d03454694017101540072007908140ea40c0100c00c02140140200b2010030f080b5082d501180d940d410a070701c00005da1945034014001c40c50701c2c0f50302c00d0f0710074090f00c001d04c010b4804890440f10034a018109014034000040e41c600d01d501d06000d048030f817000700089002c1d2580d840f481e000003503100005040c91b900c108070031860f851526000f21411070303070002d00030031041401d0744a00c0a00328614070924844c0304540c24150000c2c01419003144a20140106038118a9107101400300d10031340c0e03c4841c2c0c10407502c0820411221210034540d075240ba0014000100d00c17100f07408591444c443d00d034001d00340f50030212000080081d488018441810100f6540d201d6001c015400d5a80d44900c07824003020940741400c00d1041c031100c0400c04948901c0e8503010410710b415427070309030402c0741c243d40701 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 990033057 1250 990031807 990031831
    0xc1113060803092106150a120b0703051303020c2106150f0d0b040605190e210909010308030a0f06090219080903070f060e060112110a0e061017 63
    0x20f00c0146015501c0c0715000301c24809001101c40a6802244c0b40c403002007425809503241c85101d0b1668448a0307242d0054681801c102c0c2410304181881046904101c0311000000d04240009190740008a5201422603142c0c005180d0340c0425010805440c641400d070720382d0307108081c501d001d030320f1000c105d540d0050380300646d0f0040c00c02c0b071034061105c01980300300c0c654040c0140303000c840e0000f01020303d40da50054000b800011251103233020f030b04000301403881140b5120709044000700b21940100d004400c259450b800c240310600c1056056690b8010b221403151310080300750040000c180079200840c1e104003419400107101c000a01d14038202c52042e0801415070b0750110f55045000764503061504196002e00382100c031407a100350b11030340d644222000140301d80110041b000c100031036900070309118143c400c141c0e1165030b111241507000141e2032406032040341d0108441c681c182400801c0e80c00f5900314aa021400369100700138006040074000b04001081200d07044c2d06150740381000c895020340b8041c946 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 990034307 1250 990033057 990033067
    0x9170706050f10090b04090804140f04050c0f0a02010608030a050c0d0305060307060309020406050a030b0906010b070317060f0a06030605010306081f0c230913020a0c1113060803 78
    0x20050031078000a0076440800c9a03142881003141810068000b1a142c3d030001181c000e107910003240203080e040a001348007010104003c20a08403420303840940010545964588840380760800c82658010380e0002c041200c20404501c60210440003070240e002e05000105520b42d50b030390340368a075501822511001a4010844131201d55003403000c02e64414461405100314244000000d031502c95522403035041c599244000707411500da0350800002002d00910801c07800f0f0356401c211080c08000c03942c603046805030400201e0071404d50401d031000717140c040c0e0305e48003401501c2250a0303d061020b025160301c600b01070410300881daa80c0c00814040c162640d13001c070f280c41c40e050014007034070b04580001c0442c0e00168124008541c04040c00a042c03000158040345490320039000351040c601903000012400c4441c0b0511500c4020000140386014044c3c800f10010710a01d040d4a040b4029240c1c21030000c0d101b0885200480c5031030707404039a880340041c114407001110035000001c844135070b400b0036072a1b080411 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 990035557 1250 990034307 990034313
    0x201081f0e1e07020624040e0a050c0109060e100e0402070f06050106050408100b060c160e060a030b040f153b3c0c0a080c060703050706091707 63
    0x129a1540103040b101c01c0c60a00300310181d03c0311001480c0f40b100c0401c440004a2030040428030162010b009070080056400c60307050a521424100000d407881c7c4a801204040b6520a043d040b0454681e9130f10180d0501001c2d0410244007050042c2c001040811080d0100c641e95071300c014033205100e50101039a8100d5840c2c0407050b54016800441884400d1104014a01d00032a0a5004000303000d000940701001d1400550300b8020600f4600c607600c42d44c902c000e80c13001080310711415151164443c040c0d030703580c2c02d00b0025031300d2450000600081c0142c000c2000103d9080c1d0246819100d885100c0c1021883d031086c4086900d40d0f0380d20301c1c0007e051988100b441c121303403040300d41c0c0d100403019181c8990b031072010156032450904250007110016440c06113030207001c0d42050300c1c10600d4000c6180e10321740e4188402e60310320404502510074003030000b000804a0700040d248c5540d60000c1d0000d4104078560700d0540c0c40780c00034482a50302a440380c1e80d1000190840300d03942d145c501c00000c00c58503043c03141 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 990036807 1250 990035557 990035581
    0x50a0b0714010e0d110f1518030702130e070314070303110a081e07050d030e0c1e0411120c12221202010e07060207170a020a030201081f0e 61
    0x400000d920b900d0b200c1d20200d9008045182c03c0e50154900740300030094074860142e4a0628000c03910342e4903014094078000340500040f0201d0040180d000007044211164040301e40780e2085280003980403c09041e6582000007903003115030583c017124291510760f550303038541094043c03040325440341d10740051300c06108040c3c1141148110300d10308801401c0c1e40d46030759103e1504e407141d1158400040000349680c10b000070320a045070440d907840400d40e5000b40003040081d000e4081c00a1458450044046001725424036114680000114a81404000820009010007024005440d400000042002510384042c5c038610324064059580003035900c04203054a40110b42028000c403980c00840c07040110500d82d0040080703071242e08810014050518010168014104180d404001d8010404000b845a401181100441d00c1404040c220f805d08a0001c54690200200080d4403c4044000380055440350324016440194070074001a01240c0301c82111040249a01c01038244181008210360703480e000d = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 990038057 1250 990036807 990036833
    0x5010c0204380a08120301031e080c0106050a0501050a090b16021906030501060809030a030b13051e09031c0c020c120a0303060e13200a080c0a0b040b0d0e0106050a0b07 74
    0x903001134541c2c0003070180d001d00e40d0310040c840540540f1000401c0040e04014000e032700d0440b42d105810740e98901285e80340d5406003480c1d1260622803548007500040550180044400110041e9501045a41400304030300c0603803c103100012071544103279000303801602c1d861103004070940f100c40407100307462600340c3c020140c49058000608000c0c0b14424040315150000607120b007480c01c1e0030007040b210114404a030400c0500081d040c040f500342400d00250f00f180e280f075042d03080540c21201101c1c1c0d89c1c0c540d101d6501d100c1c080681c6207561203a00c000d5134103840c0b0317441000d00c030780e0601c15110801020f000083c0c011071006500d40c161b81107200014201a010301c0303080010301c1480504095031420b105098500740e42c2c00c0e40901800880c1098400440400b042ca80341c85d6401001c0d00707a03a40d00e401080d5562800c40c1d10300e03402418400404100b09800c20192000c035a45c06134030b1031800528100102c050501000005400d41d01c615011940d65103000001001e883e4402410340c6440c487e090110030241d031 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 990039307 1250 990038057 990038069
    0x605060c0115080f030a23041d01051002150612030403030807110114160c050610060206060909061b071709040f0605030c010c21050c060a0605010c0204380a 69
    0x504c03600e46440034084140c036401140c80c140444070000c004807101c03101342c040746070450300200050003083c9000d43d551481d0202d00c00b08400c4066a072101d0074071010224407007507440587e108203019441080c081000d103a2141e009040846508001074901d0b246800c242c2007100400c031004100101c50741c1c821010140c40702454000d10900b58020188050400080d00006008550350f00c1c119400340504104100d55074080100d030910f18042010030000d65942c090304005000d4074021803003500d41a190345004095120240c130981c1c41d850400617071000c0c400013425000009000100c086452803295004a0702c41030141503441c10001d0400046403524420824450300d480000d000070b03100021910701c02c210030700345807c1111050410495500c070b200030540042c04a00e810400c10f9038007001400c07000c1101d000f03e40365502c904d401c1c441902d50740e0040074005001095001d0151500c2e07080110035030040b151552031041c80304500d9005100111003900c0d820642c0803031903124104071445d5001884 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 990040557 1250 990039307 990039313
    0x10050703020702240706180c08030309070f03080d2315090703021314210705010e0d03050f0f1b060601020d030b03070b1e1201030605010e0105030a02040e010605060c011508 76
    0x813100b01e000324a0180c1c2201920304c0e03581c3c1030f5603103000c10180d4903020041e400041c01c0c440d040c0e40b1705a45549030f20898840c04c03036005070600060180b84031071078030f0b0a49500c910624108801414520014002100302d803c100c00207203020310065034000740d46406440c4158160402540318000d005030303680094501c07002c152041101000b881101340a9800f55907110030000c0c2070100c500001007092142c0c03048200311800c064440c0100080009110040300c0c020780303411010240328000c1220b88288144d015000c600e04101035226501482c004013586480480c0c400d0030103c3d00408a10240213407500c400e4198014000e001c080e68041000e403444024503d010b11192a03101d000c00e07100c402c2840790001007a000704401030408216036149845054030002107403907510000c002200c00200f844107580091528001107441c6290240e1181a514041c0092001c0034440d0b0074030004040184c085141c2d0755a0b01c4004c0358507901e101c001c00086849a00108600f09242181c2513801c80b10f62210583d03034 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 990041807 1250 990040557 990040609
    0x6010c0209040201110708030a05040e0604090c09200d0c0e100207030f080f0c1f0207080909100906140102060a0614010503091002160605131e02010210050703020702 73
    0xe81d504840d10703405a428a80744a00b500100c071040d140100c80d80020406000100e1407404460f4408082d1044170b4034034004140b65161081408100d483c030400c0504807484004c1c050140c000e00f90000d504003969070402e1a071441c83c1c01c6949945810050907000340740c2d00d1383c24800806a000100c03441c4a1011200d60150794400c41c800703035680c51203200051075084102d10703030310a02510100382d520001c5007141c2203680d445021240303034407122046016405580c40340507160101c0c1d594400c3d202500c5d4814002850075200800300a5030040040021551039502c2c0e030080384096450256100405d2090090080c10004078006400e0420007000080a1881c000c0e04100c2c0440901700840019001c1c00c18580c0d82d182c5042d99400e002148a2a080c01d90002841c0d01c50013800b14900490070b03005c1d102c01c005689136110313084030b0803202d5880a07240804070070756858062611541401598414012600c68400d80130b11001900c1d412544607000c0303980414a20b056042c01c0b05c0e4010310043e041c1071681c1c80 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 990043057 1250 990041807 990041809
    0x3031e0305101a0c010c0f1107060504180e01090803100b090913020d06050403081602010b01080604180b040b100f060c15140f040c0f0807050f01090f090c020606010c02 74
    0x72111440f4404900d041d00d446421000751090459403041d6a07031000b4095006400805060002a080e011000a01e0003c8210703810002190742c0027540c0c1c5658905242a10f0f1560419030000044c60322042c3c59900c0c400c1c500f13500b40c24400c450089104400094603890034141d80f180c070644a07441807501d91000c100c004440c0c1e03a42d020307883e401051840003034841d019900105100448090004010382d01d840300340f00c241500700e0f00052003503030381001c807041c5165210003c074245c1d1a803200701404204001c0c003049191505030445c00c0c88221144c0c0c0032104019586031007580035415141642c1c0002c2000600504600b0102c88a020748100103284030140d1411000038061066200040e100c40d60901105c40700c0320868110b00c89100031008624034030708011404a804242c01d9500301c4d00302402c000b00148103c0c82d08120342c201c94880c00078100680c985030500022100340e08502e81081403964001c50940d88000404004c6c1282d40000100004c030500003a151500207450141844a084144401 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 990044307 1250 990043057 990043081
    0xe0604031106030c0913020d052d0c0c12030406180f06090f020d050105060108060306010503190501060906060f020601081b1917030a08010e0103050a1b03060603031e0305 75
    0x550340030755071269a91303145600c800b440d0150100d610790101041d100c5011628258014012092032150104402d8445800684045502c0380c0b0402c0302d612500034945446003c4044550700400117503030207282030782d201840c80c1010019108103001c41ca01100340011301c1210301c40c04440b031200054004840c01d254442041410103030000a0182d52070b40e03610310400ca40c901c40c03c1d1905901810124110703403d490a02e002c0c00c821a012070000e0110750006000c0e00d00010014102d690180142c10140d1f1400e0004000c1408a01c0958166407a000001078004907480b0324070080c41d00f50756052900c01c280b03074000d040c031302c044c1c0c051001648080c401c0034543e0401222000e130800100e840c2c0d4100c456000c82030b10f01007100c2c0e00c11100c0882100307050814130000b000070903540340316595010351603032218130030b40030b100c070070b000240c0079031302100c1701000194000d448145040c40c040c40c1002c81035600c0c1c0d10101511565001103000401c05140d64021b26120307891500f0b480b01c41d0605110910b09800380c0c850b = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 990045557 1250 990044307 990044333
    0x27030f041505090312070b150108070c03050405032506030209360109020c010f021606053c010602030a020c15130b0c0c030d051207050906030a05070e060403 69
    0x4240c1c0c894141c000c040740104210740c10582d010303040e2140c3d2000302e01d103051036030080c0c00241d814440d403d000403540030000e452a4003e00050310342c49240c1c0c580e440201c43c0340100030000c41c1448130070000401c0c0c540d010000081d00c82000c1104050004840e1015160881c90364082014940141300340b03c495035514400b40c0d46510480001008241402c100c22142c510717148a05889116580022607c0002074008000d2850038000a12200b003400030680c00301e00c84c102d0002c0000c0c01e441d03030100c001140790300002d40140900072059400103803104c6902a0741000100d1000c081000614800c2005c0781a4030180104030900107036060801e444006034503070952003038451040058141da4404250710000380d5608549a08496130b02c0c40d101d9002c000d165002e6440c540f501c0c4601d82d05400c89203400500e04183e582c1660b0f07080d0400e18511200b4500c47d10207049003061180030b0010300920b844100256104404227540800d03542000c44000e8040c0741c031101c03051b0241c801000180f01003018560484 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 990046807 1250 990045557 990045569
    0x5271801060207050105030402280812070b0103060902062a100c3009080909150607060b0a12230d021509030d090309060306090203011203050304020d080327030f04 72
    0xc0d40d20385c2d4610002d141c1c98005010640f02b00032071782414030000300307202065060720710707000c110f80079440b4000c2c40018034091104028410200c440050000a04039008a4011031000d0086800c1c503c00141103950400e0f0000540001310855281d044d038034604220300c3c140060b0642041100d50720b0264010401001d8041c1e00d070103807407800c6207030b484054100d440b240304d00e403215010003003e200d078030b03040304160301c084100c0d4400c02c29070780440e5541030003100c9100301c07007001800c55281a0300e40d652200030f40141e61010385d0000140100140402c40d0b00740c10b50141d0310950b032402c001c545100c050202c1600c800e40c09030303507540114003000034143c00240b03540e008039900d20f20703416640d5404191480c611400601b0071045003040121810142c0000b004015900151001c1c0070b41a01d50719108124042486120034400c151410f00b8013007401180110340150005c2c0c5008506100780c1c07610180c60f40180c0f442c440d00300d034000300c180d444d060325482101c894250300d01451070000e498480304101d0240780220 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 990048057 1250 990046807 990046817
    0x41203050403020f010513140303091e010e030f04090f09021507140f07080f1c030b01050d1a0f04090b06190306060f05040515150a052718010602070501 67
    0x11800b458000c000001004046100900c41e80c549034510500340030f40490101d4400081c81c41c100413280c00801628402d80310304009203080307903500c1c280c030044280b6150001055540d4015982d400e1500740014650400c800c0328055640e8074043c1210100c40058404103811882c04240100690b0b84c17020110103071414422013603d0b070a5508001039201680d08481c42c0a00c01c216a541d13401101040d0501240c03050402e8682507a030404100740ca178030035103c3d41c0300030442e20301814800a00a91040c20b01c0c0d039041c949141804240c6100c4802c44990204009151f042000490083c0c540941008201d02c81a1002d00c03041038183e031041c0005201a210034464510400b0240100e5002421180150b03088181402141d039100703017086564209018560103a4102000100302d81d0400b0703d1742d0200940a0029001401c0c0c10780c05182e25000804080d0030800c0400039025200d800a00c0440d111103400301040742241c1e040100180a9030f503402c05110007510b0790041100580109500f0215182030810b = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 990049307 1250 990048057 990048061
    0x9033406020c010e01060e161409040c20070305060108070e010504050606120f0a05063c0a03030e0306010504140a23040302300901050903030706091a0a0504120305 72
    0x90b1405402ca0110071a00366103090350000d441502416058003440381541a0500290031603000c80d801b083c040c41320321040104002c0e2217002e040a611044440d1041d181c0b401d00003408030030514141740c00c44200070391540250000d100780320060020720b0041030700d20010301006140004a04003150705110315071142c1e0355000050f0607a114032088603c00f100b000d84003107080ca0101c2141d14100010348100700d00c0c6181c4070004100e0300785000c60701c0f080c01d6440240400390346044466100070407440c040ea1188903480628510649400c3c506901541c4a81ca401c90480110320a0601d00316050780704500c96400c000c021a002c3c3e10a03001144c003d51030000108003a100e0804031120420b1100100c500000c01c0c10411050590200340b0b1000d50450511460218000c4210206003444000c2000009603042210040d6907005000a0107816406415a4108840c030b0b101c03031040b5500e10809580341d00745050100c1511041520745580509058000c2000c1c1c02c050310360441d182e861169100c2456a9080 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 990050557 1250 990049307 990049327
    0x3070b3709170c190b040b0c0f070605070209060a03050d02030d050a0504030c080d15030819080402031e0f010e0606011b1a0c0d0c0504080f03071e14060903340602 72
    0x5108094217840440b15900c542e11030316410503912200800c0c009004199080c281000042080c0d4200c540c01d695443c2044a180c007040040c2d40085c0c840d95200c06c0e5240300000150040c002c1c0c40e00701a80380c0140d6120303411071030700c4030a581c0e006041c882c50500d480e04100000b60810601c4404641103003e60780c0703e124145a4200a0480c103050183c2485007110001c1004041c000034422903054207000c1907034a454000c2a245188280c400a5160300309410190503460b80c100c156440e007800d00116004d0040c0c1100c110300319040001c0b06800c43c0c201200300700b000e507005200a801d400c400700401c20180307010340310002c0304003070300300c2c0303070780c004c03010b00c0c042210111b1100540b1003d0b0044d000030401b007a2101e0020300340d58410b118400450052410280d050740c404015901c050307820600d010040c46141044048035001100100c0382c406400c0031040310307148104003540c8035454140013907030768240c1d090080d10340380421491545d0055081742e0102180a110100d2030095a100c1c1d00036848040d180 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 990051807 1250 990050557 990050599
    0x60c03072615120610030b15090a0c02062802090121090c1d13020120010603050712080a080712091a0f01030203070b3709170c 56
    0x41c81a0350898201040c04001140e0282c2c070741003040100c03109141c005004018640f20303081111031040900512a0400201d14002429039020b6030048450f90001074000018014003000d4800c00c0780e442e90342c6001c0030196010490350303030042c9070308810717199405004040d031040d001450309199250742c0118250403641d000d03640d04903280300c0501d00110301d02c2c030013010440104180d10055a414200400000762081d940d400000e0160141c4e460410656403c2c1808400e143d8201b004c90402401401182410481d11080001d00300c81000208696195003046441e1103042d4205603000426400d402c40050b0081c01100c3c500d000c10f0400c8021980e500c8419503101300840382601000b030030031403000100101810344a007400d524001145140d1500e04d000c9010303a109010094055001c1c5800740265040800034103181b800c404e00040030605007030710089920900c84030f0704203d008500b12800c401e980003480c800242902c4000040d40b21500d0100d0343e42e4100c0030400900038482d40041c107182e50410 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 990053057 1250 990051807 990051857
    0x6130f110304052d2a0a0b04032906040b1f1101180f0f0c23090a0b0a1a0c0105100305070902030702030703140714060711060c0307 58
    0x24005035034582c541810b00c5511a00c0401c401591400c0d9a805a44011124101c0900500350b050090081000c01441c0c1c85180c040060420700c0f02500340c07000040c5603501c6161101400561800c01e0710f8520f90b1400e01c0040c14545516550940806c484400c04402e8144031640060201c0300071502442c00400f2440d41487d1100e8013010b0002428100e003803a0304204c06404220250300208442e00140c0c05140421000100041015440880394000319070400c5101121078042d014000f07519035200740f00b214185140014000c680704c0700103c03d40914042c61000da20020014040c000d81183e18002050030794a400b4a1010070101c0802c02c0c400440032055581410b5140e000b0400c908010002d1101c0407030314442210f440c03141000c0410007070218000d586c061ba50580065042004954041e103804411055040d11000240b10303403008104048012480c1407040000352601d400e05510080c1103003525100708603d907102e0f20911109041810442c3da020b0198030300143c4030b80c41c02841e10314234011 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 990054307 1250 990053057 990053081
    0x4020d060b0d080316090f030809060f0c06040b0a0509060109020d0b190e0618070c031704060c20030316020f07060e0405160203031b090612010f0e06130f 68
    0x240034507070302c10011079000441c021921020f6006205000300c5e011126008540103900c1002c50b440710030000103c51201401120b40010001c4d07042074001661280c150700640c984401c994001030601043c000b40743e0000f50000290207080c41185480503074079548041c1881071401e00d950001c1c0681d001800703580214641c00e002412071801070780003002e40300c14030950301503c411041040e0210f980c9103420198581589104001da2010790b5480d20f09031000811001c05500740070041280070340c0011070092451060b40300d40c2c070007e00140e8085008000c012821004c00c801c00003c80300b00004140002a070b54003c0001144607004030340140100c1c1001c100b8101a20107101d4210081201034020003249148a407d030ba0400c801d0742c444030319000580350100c0035005a042040400c4d40d142d6050001c2100300900205549011864400301b10710394000b0755018010540d0200510000c8036082095004145180700f038601d40c00d00c540029180d1100c0c03120003100d5a920741e04428003803010707040f20484841c = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 990055557 1250 990054307 990054319
    0x1b0c06020912060405010507020114041205040302060703110717070e1902070503040311030606150c011113090f0b100c150219020c09091c020705030a05031e0a0804020d060b 76
    0x1c0c0c80c1443e40d6414140e40440d450750030900001d800620502c5501c1c16260300404090051b159a141d665603070f082071103000c00b040313000c20010000d03844540091160511a59076140e1880301d1016060402d500764011003000041c072412040b000c080000c4401c2030720780c451408030183d00c800c00304c0300ca40b1010313040409545001107808014000e000c030103002141e000c0c0e0000b0000018040c1007548a42040760b103507030b10406894481c03220440f01000f42030350a006071700028001c2e03842400c550b05900404c0600080400c403071b00c2845212900e00070300354480c031090b8092000341000310020700c8a19041c1d80a00400c002c1038040f20074048410300104112540380c800710350310004284101c03861005d040b1064094440c001820f07099040c510412441200c615000d00b1b84c01708201c43c01c55030724a02ca202c0c07c0c21407003005404105990184010400c4601c288000c69480c00b401c100031014498041103140305900a001e1440040d41059031241d00c81d80c111a03001131050a0b1424a00800003161400d40280d = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 990056807 1250 990055557 990055579
    0x2109090e03031006090b0a030908070507030b160201330b0310240207091112090a06050c0a0f0309021f030b0913112103030403050406030c031b0c060209 67
    0x180012000b503000e80c0902086480c142e8a41d201903d80031014481c0d042681010090313803400510030380c000340070103104020300e605e404600c0d1103030f5240225a4206664203030082c01803001000c8a1990164669510b000034001824010b090b0540419074420703c002c400c0d2942a41c40e0880450005c100c0508982c0c00b1464480c10003480b160340859160040800c03000005000c41081602d0100368072140c02642d0040c403105042c980044080d00140982c0b40ca40607050004069400d1200380003486900000c008007894244ea0400506a51028200c4001a1010000c00407844d51240750307001004c3d01401d01040d4400240702096003a100c126000080000851000101c0f59041e0440030740200105d0390300788107032900d1500081d1080da44500801c2c02820352500c01681c103050348100614014250890000202021090308560040342c0440c001040020705018181d011b00c90307951503040620b400c0040681504513200400c0000310080c040c001d80840700c20401005404842c07903201c0140900c0051 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 990058057 1250 990056807 990056831
    0x509070203070b0907180b030a020f061e12071704030f0c080301060302030601021e03041a040323190213020d0f0e010e0601080a08070b041103010c050a1803210909 72
    0x45c2100b40104d02d038401300080c0c420240301181c000c002c1d2031200200034004030410f950800018148017401c2c643c2004040c000310562079042140c2520740746170200c0c4699111840340c03c3c00141c0798018410300a0207500109620b8081b00f01d184543c1c4564181016881b484120006480709040c0306402440741c1000000825400e40c10f401450240c1d0081c0c0840da164051562807900445042160441d564018001040312049960302081c03003000319500e540c6003a461f6115155007000252034440c8014054210040c8110100700c580b20303504440030300040e841c01070340c00240105c482414000400d50003103000300c0b2040956014010450ba5003404000242c155400c042c040c1400215055490051500008a209012404144c1c055010320030501d00b200030fa554070140031b000340081e0f4414248000c101c03000e407424031400010744050384856444045c42a001040c40d40c03c101402c030009941502040040d00344041d802460315244040c4d20300d6940000b04035070484441d84804c3c0e140e400c0813a070f4418 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 990059307 1250 990058057 990058063
    0x5010e01080307030819180b0a1103070509010302090603010923041a3412021603031515170603150c1e0403080c010e030f04092d2c03040509070203070b09 68
    0x1608c600303a525015602c0500c13041c00c880b00003800d0b40c80c03c4010400541001c2c1310b01d00600580605040041c00d00040001040d601d4009030824001c40b035030344003120b43c11012002115403038802500e07039400510302956500001c1010303030034110485100e440842c1d401c02c02c2200a005c140c030100d0260503420a01c0c9400c0603a140b4a01181c00421450441c3c0d07a0800c0d0f4600848003041da080c5000000f05100d640c0440040107001000e801007050341d1008561800b81c0c03035800b03525200301d40e034060448005c2d1103403401e8540c0c0030340418400e60160410981c2100a04019540100300d4000c0c00d0300d403e2104080c10b20403a40040c0c0c4181840005800b2040260881c045e01280d021a002008540394400f5200d41e24800c60b54866148a0288410050155a03130042e104040400410a88071002c252200024080c450504001e007915107181c070301e01c036540095028101c4418207416214030307400b440082e280c0c8244d000300b500407882080081c4016000300300f00c540641c1d01052800c01c0c1c1c5040107035280c03 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 990060557 1250 990059307 990059351
    0x30902131b0203210a060b0f0c070b07052e020f0c0607030603031707140c0a06291e09240a0b0a0318021203090405010e01080307030819 60
    0x560030041c200410644000180c0d80d0002c010111050204507460820707110b8440140800c80c016258100420a004031300702800240242c0502641c5a0340c0440340d46082625a40010910400520445020820004002c6c5209507000103801d0520366407010741c81e5500119000143c86400060080a081040c5005011200d0820103444441e202c005c400c5080c0c0d4018400580004c04e07400b0340c0c00380c2c420104466508402c15003880030170040444e54040e0140c104298010480c0c00001d17055051082c01d004088510f948400100080075040c4d039150040b0540c5501c1c0b50062007000d0011070b12107403401886406000003001019603142003d1010103072900c50008510002034600250b81904003c103110003500d48a201b200c1c2032000d140320441c02460200c0007400c0c2c141c04051660096100d904144c0c400c1071000000d150754245003401d2000795001a8407061482e0415001001400008001d84000d1a8545000b0000345c03102d800701030362805910342c400307030040c980070380c4c0681401861541d034 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 990061807 1250 990060557 990060581
    0x10c1403070c060218041b200a0204090b01050111060708011707030822090b0303090111011404053004030201050319050a0b0405010605030426040b0705032508091003090213 76
    0x10045085a050250780e0000d0001c041f804201044005410301c4810700380700500300e8024003150645956a00050184c81042c10241d9001e03040c280184034550344050507082086040c002400304d400c0010000700550814031420704203d40100e007030701e2854028440c0f03200454221005e5034640f611080000300004a03456070b00c00312040d00200152262103805021040040100510b0a01c5000001541c0d000c01c1c04e520040382d95038030080c480720344c0c10340d188141c0a00c0c002c030020092600000301c0108246034160a440c42901c0010418110100110031201500d0f4207103450754681c1c4030105280340d40c6038481808401541403d04000c040e025903402040100d1040317605001903681c815055519110075500036145079068500c10386108140440c203034511424102c070500d841d907604010005508000d804498503040024603482d0140b005040e030840c01c4c695038a54916081c1656841c12510901c2c3c20b00303008850489a400700742e030081d4802030809030054100402715050482c5140141002c11500c = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 990063057 1250 990061807 990061811
    0x512070b1c0b0109180213090f0f1a0619110717011b0e041a03030f03010302041b0f030c02010b060d0f110903100509030706090f030908010c1403070c06021804 70
    0x9042c0315807080f005141241e044000d071000c4d80c03c400089a010b94003203c0c01603184903500000142c080c2e4035100d026504c04001d4400140b40c1c40003004102a503007100703240a24401e81d440141c8403591140202d801c10344046075200301341844000107461900700400312150600035024002011108070340c011b40b0819080d002000b0b10240303003003107124041707000d550240051b608007242081c500740350384003032403004140380440720820f0040c000030300d554084006400c1c40e0802200410440c2803d018814480110540d85140c0c1d8040910041100d0242c041c61070400d07840784038550805000790f104580b140c4000e00860b42c2d402d6880003030b80181076441c4a80d031489140c40c607000070311442c42d4250749884900802a10021401c8412100a000b0191a5070081c0c0803c00100000402601c2580700e0140725003603c001c16403030380c14040e05604081c0c1c410900c3d641800380c46019141d118000c1c020396004900703503584940700d12004855222107040014406031001460342c540107940302500d05c0c20441100d003 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 990064307 1250 990063057 990063071
    0x706090b03070c020609040b0402030109140a060503060609041b060926030405010309110a030b04050f1203061002100f1d150c22090501060305090a0c0512070b1c 71
    0x410302092004540000c0016840d030380c0342d00189007180080080a400420210308420218001801c9070300c2a446002c100f0760301c030207400f01e11107089003040d404a00c402c0308002003450000482d44843c4000c002c1c0e841024118006010080090610480002d07034021200c070082d2107103005050141580a40c1400444100d9001180d030f0110508600581000010f035050528100055010b0080e003082151007820a10790b03190180c41e03500010005501841c030741d0722141480d041c05410800d14100c0d1000c10740100900f5100a0302c101c0449400950641d4075500542c81104120700b40301c25001d426000d80e09010580c200c03031782c41d80c2000c4030101043e030036055144044a14240e8030040060011902059440006c0e0320b500020081c0000c0700110314079415a090320206010019030b00d80020041c5542c9500501c0b0040e4148903142c0d100d4403510040030344001a03250440314625138440c15210b88842d44402020000074861400207040c490f07441922117920303200030b44050090104011a075443c4c021 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 990065557 1250 990064307 990064319
    0x302012d030203100e10090c020c120304140312070807020612150114070c030b1f06020a0b0c07081819301a1012081c020310140a080f070609 62
    0x9503150241400306d124030b461500d02003012001d007100003264800d501508203200f9a640b00c0030b8500c50000d001001031a03036117081803004c52082d0164142e0030f0203580420394414407a60740404482300310b0303000f044103501d030103043c03002400701c7c0f0884001807554100d50092260200308801d050b44001d81c01d03211700008103480d0703004207414045d10001501c6072070740103001c10201c0d403c00841500030410180c03040080c0d400540d49441c02200d42d00400042e804204041d041c0514082d125030070136512000c0e54545900c0342c5880e0381c05c4c045c416150202020000c0b20035040e640d01d500d004900078290001c101c4159403514200300e1005c002c042c01403403880c03840310440d1180301d1034070740720015a000d1242c040383d40d01007003000006403005284c064003800c4001e000c10100002c26034190b010f88691007007070b07407000d5a0701e114884e6a0280d0311102c115006000344002002c070b59100c02d0a40e24000300300c1900d81c13529000280c401c00c907940101c3e4035014032144101c108001040d40c0040e5641521084071056803a6 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 990066807 1250 990065557 990065579
    0x60603031801030e0109120203071b030c060810030b010b0405040e030306010206040b070e03152d071206120b0609070504030203070e04023001060e09070302012d03020310 75
    0x70024252a920030038071285941c0294400d034014400c2a00000c0c0c880215901c03030f0891403424034000090b84c0045002e00c01c008645e03184981100c100049280082d28603a6070440c880030394010b0005001034900000c0c40c66030205100310056801c103150a0241d40e5800300000158000c0c051a40541c2c01c05010b85c0302080000122802000181c1c000d0030340c0d0381c6940303545da41d480c005028031080080c001c0ba0a101079604001c203e02c0d184040c842c5070305900b0252013440c51032031007a07840c0e116a001c1010f0302140d0760840d0522076108600c2d0404507070480b402d000300d4006140c280c012013800c001d812001c50a02071803400451042500b907544031110f4079540e5056401e400759201c020750503440704030300b801000007000607030303400030310181c140400864030500f00c000761000c028845030b02810200050410003000d005410003001c0c031842c00100c2d41410480076071038105600003e0b050221480303010344a04600c034020101c20081c00c03c0d0340b83d48107000c50020003a51007601d03203401e2202414030104620010f0 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 990068057 1250 990066807 990066817
    0xe1009030809040b0310020a0203090a12030f12060b1204020f0a081c110114091603031b0f0206030408031b030108150703020903070305150109060b0706020d020f1b06060303 76
    0x1004886041c000100b04000c00b80202416158050141d4040c00100841d280003070410488603801945c3c580700f87e0303070600101c54901d85c007940c1048a221b42c08008680c002050b01c03d00d8100d494401c0d4455480b16904014181ca5481500350000002c0c1c0001c3c4540340c10031190045200f1a0400c0540118030700b0064210850f0041c400242c02c19080d6000e00e09511502200340030440c2020321001c0b0011020070300310b5184a40030900b4014036410400c0a030414410308582250702e01d90611850308585000b400000d40000b107c030b18107201c80d2604180807100c6100c400c03080d80209010b65a150615142210350000d8901c0030761800081940d0300c14101c02da081c0ca06030340b503550007000b0345410624051117003500034100da002d0550030058425141c40034003400c40a076000740005c08036196203810151541c18140c0c0f00c614070a20b404010b1110850040441c1c082c44d801207070141e01d40810500c1c502c001d00c03901c440c010310001c0026201400200c4034400b0071070806d1050564500356100740c18540c8910503 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 990069307 1250 990068057 990068063
    0x6090604051209010e04060b130905100324061502070801110712090302030618100204031a1f12150b01050d02130b07050c0a09060b070b04060f06060e100903 69
    0x410821110103000000f81016030014540310340c80c503c4140100302110465040740608110010b13000411030542001d03800140000c850030051842c01c680d060400c13051a0000a043d0b10030801006170020041e40302c0414104804010000c1c9903560403030140861070b070914000903000c0c800d40024885010312441842a0100010078507004803070303841a14540f4203030b030307840188440c81601101584040101520948441c804100d105282c02c900914144000d41040203a5004000030f000203a0034010050450a148500454540320340042407008121000200c880c001c3c40b102c00103000048885000e4024012040f10124049440e00d12081c0d03102140c1680c00309400f003281a0085846500a2070000092454a46101d0704c414000069520008080e2101c2d408002c12078014a4413090800007001a80010411945819080c1e01a402040360181c03414580d00001000e0200ba90801c100c0c0010411041152544444028107650401c0c0d1440b80500f40ea210720b9584140a004a0015660 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 990070557 1250 990069307 990069313
    0x61806020a060b01110f0601060311031005120f0d0306030b07110c06092431030b040606031a090d0302090d020f010314040b090c060712080405070f060206090609060405 74
    0x4560300c9903800f508144802904110501084416690007840385c0c0f111a85104060003c0c0c1d45003541c0202030300c11032880e41c2c0468400700188a40d66441803c1d0008440c00ae40b0503890218000003854240007004030b14500718010300f2500d2141540c1036004400790703842001c98982c05c1c0c8940100700c59914031107a111450794030900c80f41036546080f03000703021002802480686083c501c819509004c0701405070031a0181c03000b00309143c0300007500303243d0070b01288000310701812821705000e541c45d06d0070350b440007070300010061010805019054002c00c01440e00300280a08803510060a02445407046514040c6c81c0510780801105911a0007240c094100c0107194183d6880c0c01d400b00500c0506e44d841c40d9050540e14040400181561030f161441540142240d641c4c529002c40302a050150b0400c20600c506030402501d80012140c4402c0c0d00c003856036141041642e9500d103065880c140c104c0d0440b2000412090002405650000d01c81d407103040c5078020344d40b541e2a51401190b4607102940e0040403a0 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 990071807 1250 990070557 990070573
    0x12020102030904112115040207120c0809210618122d13090c0804080d0b09010902071a040c0b0307090e0711010506030607120c030b1906180602 63
    0x21600303070040b01c145102c0d0042c15180484da0105150350344c08068040614102c48004c00215200c1601005903810080d10150b00c1c103041541c2b1425040010120308061002030030701c00003404101c42c00d803542207402800c1c6058020075680030b81130341680ea00421040e88506000101c0c01e422107140344052004400041070008079032400440660005064030740403079222902000c21000b80c8000c04003444126603010f42d0348411120402c0c040905801401105040c18088106907510100955120f40c2100c91103848400740301541021303065211000c1da02001e400e0000c03940c90100c0e07004002d024802d043c050080100b01c10241035900741154040c0071301d02608400c00403a003544000319800583d034500020100d0f00c800300703a0b0300b00c401036a1080000c4c45134031041c200c2c5002403141136003014049009004074030700700c0801007101c4901c8011020700d82d111004220701c42d000307420008056000a001d02a80d065a4040314003400b021720422000030b00e49082d1346850440a1040400d4940a60190440e0 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 990073057 1250 990071807 990071809
    0xf0312090414041109071d090604090c032a030c1202030307050109080706050f191a090c0c0d0f080705031b070302010f061401020a0b060414090601030b01120201020309 74
    0x40e4105500950304a5241e02c0061500d0080c0b00050340314502c03c030740c000c50405101c028041a1100140b50605101c01012103486240e030700005456406012110390703d19a8403400440c000d01043c02d070041014030011004001c11616001501084e0b4000e0345640e005581201d010300d0141c00380c4005480303014000403d003d0744074400e07031030800c050020341240c2c0b40c44016503481d802c40c3d641c1502690000320201c0c0c0c02d410010715028882c0c100048840d908070364102000d0105070001000e5464030301994861001202144410203148a16001000318040349403000018200794030a420100560003889082c54005008242407440070255564400d042d42c1d940b0425100c95201803c003d00501007904501d4440003204001c1818a120f43d0003c6400780100c10310344141c0d9040e42020341910066640d09030180d0340003036489038494001c051240c1e55250003011400400307102c04442c0c0c14848150400203031500c00a1001d04a0384103170034281840e030703035000b0f0040220380004000340140c10400200000e = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 990074307 1250 990073057 990073093
    0x7021c050a1209170304080415030605010e0f0a170f07081501170c10180504180305030c0c0d180e070503010b1b10060f05030a0201022d070303090e060f03 68
    0x2491240000c00e8288040c400c00c034540d45c00803901100d4600000a09020a0003020113858104106040501c41c0604000000c0d000031200000b883c0150080c1c2d25101c516510703524200000c100402440d10340a8010500d0342d00c81076840c2c0ea10342e0707500c102000065182d600091a00314815124405101c590074940e50040e00390149000312814460a000041c55136503140f40c00e582d00301c840c0c4030000e40a81801b0901c481401990005e03228a00c4c20410f01c83d000b4584c1c0c8003240540d450314056949030b851440c11005806401c07000c01141c812410814030b81c9821884080400401000d0300c1c10a50703075071300107055031a004c4405800045e021b10040002d2460100500b0300326105050194100d2a0500320038138004000c800c0c0c1407025100c0408101183c0d07940111001f50409030068403c1010700d40001c0e50310031a803d101c1e505409110701c0c000705841c0441d449110221290f054401103966414028109507982c00382e803502d00000c0021485a00c4e11280622500d1005030142030032200031502d007c5 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 990075557 1250 990074307 990074321
    0x114091e1b1002030f0406050a08060d0308060409050715080103020a09060b09100c050607090f0b040506072d060914060702070b0a050d060305030301170a0309051009030b07021c050a12 81
    0x3e5100c10b1103521491400d4001030000781a45a4a050311400580d9009000500242c01c40e40158480004600840e038040074403913002c10247c40c0400c502e091407401525054481d808120318840003030860a610707030f1110030755048a0007120307030090003034480b001001110210301c00d10a103010200100c880908049485e00441642810505c00f040c1d060b849807410448200c400704002100120140010039070407042802500c1d580803000e00306414140402c0c01d610590502818500c40e040550074030103004510045517850070401e840300c041003032615001810400c0011902a2098002140311100000300180320b880260700a010311440d048280b0b0712076214141040070404104444403180380503000e400000c43c8210002c66880d072404004070200010b1218082c200d4104101e5840880d51001502c01a40c10445041000c0c2d00b601400795005100b59000420001c8207200302720780b46402060780009140f00e03150800e016003000b0002c172a1442594080004035500c0c07070a81c0c00040c0305501441d = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 990076807 1250 990075557 990075589
    0x1e0105090f061b0706140106021e030f0705031e0304050705091302120c0301090c0315020403020603040b1024110712170c19150501030c030303020304050114091e1b 72
    0xc4c41c062031a291981130b5458411400018043d140040008035410400c10000401c1c0002580401000e40549a141d00c590317101c00040040220b04002840700500441d21001031a1421030034030324400c07400819a0300b0468050350a4080d403003001a25040c00e0924500c20301c0c4041c05070a400c9601e49c02c01080c400d00320940d49441c402d4603801c5a880e142441800c040c80e015580b0031403c80c0c41c500d481c8400100018441412354010310003000142c8a0205880d0000d610154404990b5274501d01100502c100b031703100b0017202d8180c1d100300030060b64158074009410707201d64074090002c010084042c0c0ea6501403240d1004072040c491003102280c00b00804c03500c000e0140c41c0742403a00c418590000d1626525071106040c00b06003074001020464584484005c002211000b44850742c0f41d5100d018fc050f507a031101074289500000060104202907000e065120380e10740711019542030840030113036a0303000c400304c41e0074250700301098001001002421090141e0102c00e680c03451151003040c032481404100300a = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 990078057 1250 990076807 990076861
    0xb010905190e0c09100602033a05060414010810020c1f020406080115050a0c1e061a030606030a020103150906060512180a170403051e0105090f06 64
    0x1612100680e402202c1d262451803000b0021500240308201c00701c1d00c05401c0c221248985641080740d150003200742c0c0c0302c0d418121031022680402c3c19503e00c0d4001da0743d400c01c800d01000540c1940042050b030205000b0401035800f00230141e100c60030048150800e00a2854580c08009100140400c1d50000d00000000e038064502c1c2c44086c00d04840b800206500c07003030209402040500c01c1541c4043c041d07005041d19070503000e4000c01000050410710510380b200c410400c4050300c030002c0c44111821500008210445610500e440d820507800034034821039848031307260140860320100d260001e00b180c02604003c0c042d001e1001a60300540040c40110140000e282c2d90202c0007d5445c00b6200d8100100039039144c459a40700070f18509400b1080c0280040312500b17040d00c880e0603548001900b0711520703070f000f1603100e629101c1e0210300b401c5014940c4020040c0c800d12a46140440b128030210f0074a02c10b400083c0140d840e0040401e8982c1c0940001424542c80500083c100030002040504074004c10002 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 990079307 1250 990078057 990078091
    0x210b0613060b070b070315061e03020f070309031103010638030906011d041515050303071a0c0304380703050403090e070203220503190303180b010905 66
    0x11078000f03800c000d0081c0c0d01084268208a0740c150140280c031007202040c05814005c9041c68405001d401ca10136846000105000c4101c520b240681d04942c0c050541c00a602e48500461600905100c841c0c0011501900203800c0f04c00c1900f070501408050710081e6a0250780d41640d07480b84592a09403141d8a4011002c4d400c0c00b41da103051980045024880c080050004340d810500c41486401c80600103040e18501c0c40200004600000c0500c1020071103010086615454100810040f50b403035007040303505002c0000c0c0501004019202c044840128882c07000455444c6915850781c1e010448010745081241c0d038160f82d40e005011581306150580d45415184090300f07030388004200c1c104039246000f0a586a0500041c507802a040d04010303d11091035071030303903e04010000c1d01c0e0302500c0d2200c040704100e043c10a13548001101141c010302009000c94903500a140401510601003440580c0070034542920301144170303024413210041d01e40081d411b024607440c11101d00010300005140f04908101d60130 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 990080557 1250 990079307 990079319
    0x2071a0712050606070b0c09040b0a0603272301020d02030c0a08060f030705040902030a0b0406060509160903020607030315270203040c03020f190807210b061306 71
    0x105402068540e844a040500c0421107108584020703205921407101480f09100241064800715402840900e0036a10382003003a010030040e0070485041a80801002000300305244d0582c8140600d11143c80b002e49840c25401c2040103100a11001410200d01401d5140348110f0041c039200c1c0c605d40b50000140f500c1c0510654000301c1c1c0050340e0110200d00001246880c1c0343d40000055007108044961300b203160540c000081e5a07100e03911903c0d001d2078886035104250f6500f07006c44613070240c2040071110a0310b071070702e8950000c0c240c50043c0c600c5640840046000007074812503100c10340d05a030b2282c440003429130b020444140c0124004030300b0076848041c009246150607483c580208240000c1d1400003c0030420340c1d8000728000200c1c1d00503403062081102240c0704056500840c0c2d01500c502041c00343d0107005c0f070301d100b4201d00751101d0608030010008078210001800004c5611851000015947c501c803180010340c00d045003d42000d003d10007084a07445c000441c50300c49200c00300c00242c0641d86003 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 990081807 1250 990080557 990080603
    0x20a0909060303030f06050103020a0e09090a0516090606020303011203081306140601080105060c0742020c01050a02030306010806010905030a030207170c06180612041209060f020d030207 82
    0xc2c0003200020307150074505e90302c10860300407030b80038007000d00303003541040780d0004010f182e104441000c511419400011410005040c4800352005820805035006088200208031081c650f500c10481c3c075034901480060901d10201c180d0b0b0684400200000355141580c4044030368410150588600e0341c0501109800985244100e2186007103019059840349001c20000d031940c10140c4c07106018030420411100c1c04500030030500c0c19602100c00800d600e03a4400f0000d1100d2104004030300000c5d540100e01202010b009800e0b070145002507080f83c1700068104011103090081da001e52016a00a0020032000c0d80071310341c0300f6406141890110111642c41c8006850f2081c0ca030410307005078011030305c10701c08951224184510704080900410581580c0750200d605480b60106400404901c8100c10801d662107004850003140700d6503800d651030800d41894aa44407130b00c1d5034140800d40024000410034018400060716a00f9500501411302007894150080d5014907c01c4038070003030080b42e04030004030781 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 990083057 1250 990081807 990081809
    0xa0803072d120e0d0f1d19090b0103090c030330020a0e0d02090408070c05211c021b04110a090f0b03010e0105011b0c08030d0606090b0904020a090906 66
    0x607650440c1500d0304001c1103040720002e01043ca801d4015110289020342c02c01076035111100c9510344022000b0320361070500c401e440c8820200758425116240d24102010745e420003425a030344490104260700c0d544005504403004200c0041c4100030229040020078010413061020503003500e00c00503e200d101c00d100c07214840610140400f286c0c04034180384481c0c1c0c0000019400d1005031201030303040c151600010260513008100804031200010410304000440e210304005243c00b40c004410700481c1c1b11112007a10b400039a10341c0501c0340c00201d0500d00c0b081744080050f100e00341c015010403400541000c00510310443d80390b400036101c10310034007c40200700081802e54100d643d1524424180f1000300c9114900f40d0004c40074402c00e20040c4900448c030b0503220304548090800b818a41c44a20640081d0304a49402410707403126404002a008004030003071084d555901c0040015649507002a0b03454915030060341007100041c0210b0740141825070007010003170558200004001c1e034468544003600c0c3c403 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 990084307 1250 990083057 990083147
    0x90d03030c090608090a2a12030f0507150c020a0813030c05030a0c09020a0e030d03090209130b01170f1209010306090507050306100912030903050d020a080307 70
    0x5030300701d22692541c1c003070700c028041c0c00d071403401408030309261100681d5402d101c40f003d02002c0c0d400c0c0200c42440180c60381051045116036074012115035031a500b0780b0954000000754003046561041440c0f8511490413200340d240c6c00100b0384d900458101c025801405007402500640c849d607907e00022820010290400e498903081080f0701c18210301e40707100e4640c030b10740c00700b4040d900c10000f04000414107030014003030303d824220068458803819412158144d18110494043c0200c81e902e41200394540c00c41c640080c004d9541e000f00392203070480071054000010300a0070410300c80005000909010582c9081c482804007125400d183c0b41480e40d0410562508003d00303100001001242d550305400350500810340c0503010001c40c5001c400203082440018562841801c103a80e2407000039024400301805403112030148007100525280c040d25061160109654500c0f8001031501c45600c0010b2807030030b00360701202e504d095842e403900c15501000b0140c2600d1810309800280d000000403005001c599500d = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 990085557 1250 990084307 990084311
    0x60504110d06050904150c050904050403050c0714060901120204050a0602030d0e030703210e010e030717030411011209051504030f03090209070c0606081e0f010203060a030602030c090d0303 83
    0x8103420002194041d43c440760165841004000128010a2090644000c3c940c00030804142201044980f0300c1a201d40d02e0340300380ba000a0109050f4490054a020715030f420841e40d81d00c1c2c8030711419400d411021240c1e83d10000030440d0342810b510843c2048499244007a002d828207031a280003e8840e4950b40201c0016800881c503101d0341e500c01d0040c1000000a900558545030090700c5c0100700c1003d01003a8614000540c900141100e800d90146640b00f001074001c0103450340001045484e0740c01301c00161010b81c0b4800d25541004110170403607000c0d5500c200406412400e007401960b100035502291407a032030b568040310020030001e001c81002c020210000c0c0505260038540036000210b40941142018a480c0301c05c0016100c5118103500561a420316007070712001407600401401554001c908140110382c504c0040d07840c14110040c0c450004800c5c0c0b02543c0102e04100d080303000c1121010f034003240601d002c2020519650045030050300c215811460a4001000700e40390220b04641103001907 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 990086807 1250 990085557 990085567
    0xa050a0f050d08041205030621071418070e15040308090a23040f0f0e0601050102370c0b130812090904060c0905190614070f0b070306050411 62
    0x440240600b2024801c60304210000341044d4480e15140d41c0e940c000441803100c0000410290b594045005406881130404600c400300345003025912011181304804501d070100c44413101c0e80c07074240f012100580b48880410100e545800d412902d03d0460811683c100754240c80e008280d0441000a2000d1406441056611120042804190519548103810000003141207800034220701d498020300c614116804181e010725041d4a00080c545030b002560000e10380031030130707a403500003144880c12a81c09800340d441118101100c16280a061007804513203940d018155105010590300d80c10180b4012211713602c4081d00c456204826030700030500b482280a900078100f001150400244e0301140d40d802c1824100600c101c00301d8001c0c1c002a100400b090b0300d40ea40f410195204d0706041f8010301c001440341103002d030591a010403485107400f40070001541207000c0d11081d0f008004842080ea4000030524841d4801e44610340003101c09007510040580ba1003001031559030302c1c0a8180c1981030101c11540d12 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 990088057 1250 990086807 990086813
    0x60d1a10030c200604020d06020d0603052b0206010e09070b03070309050c0402090319020d0b1e15010e0d03120507020706090f14091b030a02090f0d230a050a0f 70
    0x40400300c3e490b2031004422015070402c000105400c1d0b0441c1d41564509801c0c5154034185019008202d0303089a0783c0d10b0540d000060000000d14001d41410307010b8103110b43d5400d1040752090400384140c5c2c002507848040100080042c404c80c0550250200060307a606984980c3d1380030080c1d206807210030000c1e8841c1d00003020b109080c00100200c4008503021031424002201098592041c0e03c1030001c1c1d961500c07010f60075501e45003034400c89903a0024006003030b03213843c44003078031028188680c1001000c000c2000400103204000241030b00801611a60380c1011404204211806500c0d8202e040007041404201d40c8404c40c050389000c0c07442da4010300382450810b00000d100c0c00702236201c0303488100840300801485d5501060500c0b0007009482054440c0e48160b880100b03c40031700c0400d25608400010032030210b030913901800c00c0220840c1c0c5044c42c20200410020225800480681a0030140c030410180e5220303407440f107a4200c0480146c44907086039441c1c0900304200f0110a5031000c202004403820 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 990089307 1250 990088057 990088067
    0xf03050d1401081507141b0303040516120503030a022d0309010c020102120106050c07080a1b14011707020c0d1b06020a2004020403140106150509060d1a10030c 70
    0x43d98056154125903840c1c2190002c000082e5150070042e03a01b4000740340c4000d43d40c4541c0300d8408018881c1101d5680c142490f00c4c9a50b140700050400413040c5912000c0b030902103c0c8004544c2580003001103055803124440c800c000e42c44020420001c1d08122142e2038982c41d11240c040c8070860b01c40300c142d22880c0c0701041d13500f500c6e0301801890440e4410401407611004a4082c079055a080340f030451340b50203400e2240e500e4419150803101d0607108054182d400c2000316100c40c0d481a213041c085a420b150b41300681161181c1200e041408103514000702c4178884000d0000381c1e0311060030310454102c143c14a000c60500602500300762444070140d14114500040740c0c0c0218010912440101100001c0c1d0b1907c4040700052541141d03080b03041520080c0039900c0d50141c50146800040c0d0240e184401c2125a00070042886206e11410f03c1041c24200d10303008000b0b071025004090500c91a107054403c4850051100c1c010156441040d0f030703d040f40584a20020303880c60042620000b50348825080e010702 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 990090557 1250 990089307 990089323
    0xc03290a06060809191502040315020408014710110c0a0b07030c08040e090f0d0906120b030f15090f1c030506042706060b09030303040f03050d140108 66
    0x1050f0f407240c9624000e20003200d030f100d01381941086d50b100e42545480310304000b910403540094155184902a00c06d80c0e6200d90040007221100d07030080090034035200c2c4105295001414007503000112440561011b0340203060790326240c509448104280c4124030000b2401302100000030009825204402a042810490074000880c101e03420309038946403032800c0109101e6088000e082260225022040007403003020384000e002e4005920300c0610300103079000da0320b281c401c18202c064802c0314080c840030346c040d0324200140c441039900e08400d014001040005000750812142c0c06101d45905101003180c288010300c5075010703403c030021003410803024a6151855440000321a40c106899462440003001c1032891090b003581008100c6075110000900144074250b0307e244600c0061511441c0f94040700c840178011481084104402130319070200600754000d0440d0550075a10420202e004940340c0b044c0e60010780e20a1a04510700540d1513014001e44ec12032103ca0761007081c5100600401000f404081 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 990091807 1250 990090557 990090571
    0x309020d02100c1115030615040806070c05160e010911190e12010c0c1118010f061205240a0317040e090c0a15050c0a0c05010216030c03290a060608 65
    0x80a921502e8000f01701c41c1c0703c094600c034858100e601d804889220903c040d103009041c00c0054a000d481e044202030442000030b003080302d69008560003080303000d411450710816034605a82100c010307070030a19400014000c04000c0c0007120414010814585005054a4a40ca14030364400c0d42e140c10342d209020204070040300400840c1d040000d640300482d440303c000c00b021a0800c030040d08014003900801c111415425030144880035181c00442c08005945007001202e80c180d0740c2903a07000c0783c0201d000c126202a228174004129420340001000300811a5041c80180204281d250503aa82c0d124211242c411034443d0b0003000100381001164183c8000705c0e40709603c20060480d010a40c0005510720310240180e003241802c0000d11501188518240c602c101031102c11225240200e0030b008813400c51501c2031074010312500b008a10850040450003003140d0707011180e00c02a5085640340102501d201800d807003202ca03180000d00c4000c4030700100c5070044000c9400001c0c01410a6001003c3d100020008 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 990093057 1250 990091807 990091819
    0x50c0414010f0e0616060e0c0102100c08010b07140304080c0103060f0b030604090c080a150b0d0206030c030a090818090708062409040207120e010206070f0309020d02100c11 76
    0x408050b03a0092083c00041c4401c403146561a01814024070241035030340c0c17001d85424a0001401001000081c420b401e10800341c00300c1e06140c01d2040e500090341c1180c20341d0800a12500010814402c113940a0300030a8400c0da0440681e4181d540c1d030038610f4209611242490740141c000039440e51b05441280c0141100b5a00b241c800c80c00c21103480710780c3c40302600c1180269901c140603814030101c0030b0074902030f2402c0c6d4191a00100300d07061604c0300c268136030640b4500d43e190802e010114600402a40c10165001c0c0c5140c0c00c69450344080e245c07540005107594040740d180d00603080001c0400009050340280c99103140804204a010f0242151004001c442841004402d201580d0340741e40c828141d152249850030078841502d860150580103902c01c072174100740041800e904002180c034254034000a140c0e1340580b880c80e01001241d0382e21080d0340160110f0300000201000d2442600071300c0e12a4005400d460303442d403e55001c5848070b0582d0303c85d8000191078901050402000305042c0340c4040702100c0b4 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 990094307 1250 990093057 990093077
    0x603030915071a0f01030f0501110d060806011202011e0306030515090c0a06021e2103010503252d09020c191515080a03020606012714060c01050c041401 67
    0x41c1300c140401808054a4500420028000c000b025080020310040024000d034640c0c243c03c0e11302000d0403160189407010300a0000205510b0340f2090010340c1c16030140d4800d940c0316140c1035503000c00f4860b0001e02d8101501d407a070220106504000c04900540c50050035081490080750985c01d0403200ca2680b0b10490350b00302c042001032390020741c5014200703d424004040310145000c581c0b5100880440520f03012580c41a8441c5596075800340d41214000c0e003d48070441c231038104608100012020050343c014a80e00c050140b00e401e00b101501e52501a5110300d845080800340b18960398445d03003c215215000180485d1440e000d1102c500107408400c0c0615401031300d503a4081030b441005c11800045c1380e9a05841040c1c0d142081442e00071320702c080c1074601114032401c0080d1603101c00c0741c0c0b0301d0114032041220181000a040740344444a00503540d81e5041c6d041c0220702c03066480d070082113980040e080c41840a169402c0c400c40327000301c40c803501c6640e6030ba2400d4541d410004c04044681c1c144031079140 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 990095557 1250 990094307 990094321
    0x8090313030503072f1009080f01020a080105030d170a0902040207200d081b0307081308010b0111030a0836100207030203180a1805040605010807050a0501080603030915071a 76
    0x34008905c0482d0060712000401ca012105000340380d010110074030846c80648450300301035005150361207082d52440501ea80b913805050365000305400300400149402c11129220f88940000e17a004075805c1710104d42e01c00c541e00040c4c1683c01c0140151040e0300d02600401803105282d1008440c0d03503041e200d03111203180e16100c00d2513500603160001200c4001d030306903a40503141407044580f01030748a00600e0301c1d420024898032203450b003400703106450341c0b91940c0700405602910102007225a81e000551400061450444000d00007034a0014005461007100003004910080890120034080f44007510b01d00a070102c1c2e02e40001039103001d0030184100f10400220b035011084404e400c41c0c401481c10031113203503004100100c840c0c3d48800e04600c0120200464100e980e000b903400756000c1c00061090f03036203c110813903c820349882425480403036134200b0031140d40100381302940800c0c02420303681000d4005001c17601c6007001e02c1c09100b55440c001000e00810040b10203940c40c00c100b1540c80301c0a850860 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 990096807 1250 990095557 990095633
    0x2b1b0305061806040b0d05060f070c11191a0a091409010512070e160e03150a09110301020313120206010e01260106180c0806100809031303050307 64
    0xa800080c03203101000010fa1a88650f001001a040054286903c01e085424040d445840545101309800c440c0300200d042c02d80318511016805800c09888a03881a8040801c49950b14801504080c0e1010920004001d0945a42203d400d00c00404442d0341d582e0740d2100408002241d0480380e0103500c51280f00c40640c48903208103055a42c20740b44441d00c01084495070b40f4007011540550002030300941040a29110100c04001010711602c40b01c280c000d040701050b40382c0e41c0180105440c241031000190020a590b00b000411a00074408419180d151202103800c1ea84225005410f40c0c4044904208202180d4903000e81442c0910203820194107040c3c1070005004c0c180300380c00d03503010342140d0740761462070350440c1c1c4070306074030300c40081084550307a011a003207014a100000413803074a412a1418080d0180706880d100d40c10050045c0300181441c04155211b100240c4802d00303512041c0210300400342020040405180290000c507101c040a2603c0c03a8080b07880c00d208030040c5090b03c596000c81c030700c078 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 990098057 1250 990096807 990096829
    0x209031002072a09020a020d030b0d05100f0f02300114040b060c030a0e01110f250812280c142109031002130b2b1b030506 54
    0x101c070f141d140407044408180ea4810b4000181c1180b0005139803060540016252504601c0f80c0ca0601c02e04028204120030501c00044c00f400c00d4010300f5040345420030316408400e46081d54040003a0703100b00c03520725030126081600500b11902106410340021000d0381d09041070180c104075200e07581d41c10124000c205c1881002003e010b25107881c102c145d1503443c0c405656050022104480d11148001001881c03208081400ca01003901880c0c20700c4c001c2c0f0041101c40a001d5410000d014103015601b00c03594020500349800e000d00715212001c110040240000fa40b1040391143c8152290000740031440328051090300750062030908400c1c503040c01d03080402d8aa4158000f006220381540102d400e03411f1050641d030300380040d003c4100b0005508001400341070b80b0003080c1c0c221441c1110701000e100413445200c0009010039400f100c01c0000200d031400034900341d19111041d408424215a007040c15290782d1240304112a114124000503815010300c121480e245031406000d00d09000000c55840744c20 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 990099307 1250 990098057 990098093
    0x19150602030c3a0509060705100c0201020f2203050f030c010501140f01360e0c090a051c0c09060305010b030d12090203010b06030114010f030c121a090a020903100207 73
    0x70902a40340300751300520a0303602e800b402030030255440416241154a90078018a0b50f81803078500f440c880c4860344144240e07104440a1000c0034030b82403841c81c010b1141c5184440100840303c84110200c00180c092000c03c081d204070100441d1200c40710000c42d400d507501600010702c05440d108a24034950344000804c0c0528500f800c102594a480020328040c418807515a003142503090000002ca04059201410480d2002c1c08a4030594803070117807254a80c410f0707241c482ea0000828400740a00e24048181c204104900c1c202100040115507030004045170580c81030301269921802001840002c0c000e00c000c3c3c6400310302808a11000c07102c050008001c140441c00d985c0d0362964403008544095100124411000340119100d40c3d480c03000146841c1a03151442c00158142001c0c44901c2c0a8040c04140b0441510703000743e00c0d96039503803000003880408280010009102990100d0782c90304114240a09280640980d8494191041c945402501008007407214410080c04010801e080400021f80c00c0c = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 990100557 1250 990099307 990099403
    0x7080f0a120903080601021510090221041109070c030807050c030c011a040e0d02190f020d05060a06060f0c08070c0305150103110409080319150602030c 67
    0x4115003088a000442260035444540750104582c01d054000040d03500c291000d07070803248442c035062001403600c2c00903a0007100340d99000006100c0c0c140c15802520102100c804a01094480702c014035402c68415142520801e04801c008070450500d4668076500122500300300240404581e0b00620160005051508008000c00c09020100e024411140c168080d40000c1c014101c4068000c020350320340d624010302c150300c2c02c2040750542a021a04095022541d0082e111940c2c407041c04c040c100b80142c0c8100c421050f101e8011005980380c54090484034000c00c0180403500e00648440c0407183c0700e0308241d00740010b158181e44540e40c400c0044400c00d922170030541c4c941c4400c0c68840200d00c15608000d10300c1c0140d52003c0034003150506880d048034040c081c50901215080c050004030340301c0d0741c00940050001c0000502c8410002c03011401d13036a481c00001481c8100000c581240c8006410010042e04001035000307864108104803580fa00035100851001074468084289030400d120405003034203 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 990101807 1250 990100557 990100567
    0x20a0605061c060213151d131b03150503072106020406020d02010b0a1a070c050a1d090d0f200109030c052103011a09130b01080c07080f 60
    0x2455507a001d8481c44241003007942100d00b98502180030790015000d0855100c41c800c03000900385403088110380440040d440d16444c1c0800c8808002100156268803504190444c05640b0350350450300c030300c03014443d0820109480060510f4024151641002e00e010b81010200091005507000301d03004007100d4201e2100010800c00420410481d02030520150095101203000102240c011a00300043d4815a0003040301503411420420075501d03d0086580c001d0240409218201941004120751030090000110b1540d0300c400142c44444550088000c44280c010038840003044816045e411030018800381c000007100210003040c0310740b00e0303004108010482071644201d0072a19020112030a0900080c0000c40c0341d803c01814070070300024200c41070721604107a081c0900b002c003600050314040f4102c3e20314503481c1424002041c0c1d400c8840e000ca1000400030003034203648580c205c01443c20921310124804002c880094902c0320010481c1c500704008000a500081c1e1000480700d158100050392a212 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 990103057 1250 990101807 990101809
    0x703090f030309030219210e0301020c07050907230901030e0a05011d0705030a03050f0c070f1511070312020f1e1203150108040309121b060906020304030b06041103010e010303080106030b01020a060506 88
    0x660342c001c40c0c0740c24ad440050805600030003c01c0941c140d420039180b850f116150444221140c0c0200014443c1a804900601c0b0701144450b004103401c1c0300524021130510340c2e5501441c1020309024040f00e20760356640030042c4004c1e0540b80c0206a604000c0903001e030341d00d081d010a88400311220020204040068012007000010040c0d54420b0394003411a8280d5480380401140100385000da078000441608019030020301c10b0801050105c1403801510b58a031444c1e43d00302c1c0804a00c0301550542c007848080080ca0707841048a804a65503ca41c2c804030201d41d03d800e40d050144420034404120401c02c10080e02100d030083da551000020b180c00d00c610b95803414215150500d0384c0002484070b544074070340420720410040409a0104511002240c1603449400b0340d03030000c50f4890f85016810a110800c00306400340e60f8154412005032000c1520304481e00802c0782da90098000000200c02e08005000341540482c0c060f0240c2880d0508000348582c844c0041d6544900600007066903403240002546 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 990104307 1250 990103057 990103067
    0x10c080a0f1404030c02031606020a021203190518010c020108070c060902060c010219081b0c0c03030310090e07031e0201090b0a0e01030b0906090f0703090f03030903021921 76
    0x2048954410182e128103040c90001c110f03d004420580c070034800c555504084091010800049900c0c40c0c00900380754000f80c0c01e1002d049118894800180014400805024801030340d0600b0b07180780d44d4039981d40c0c4200b94160710184000f01c40c0e080c100a402094940182d0300a01110b42202c01c904045190311094a0300d0805400900070003504032002040c2800c3c1004150060035000000105034012403e505008460244044039040300e1012203540001c194080756000b0004610b0034000e9510021406012034510391042d61913003c0040404810400001548100d00d11000f41c10050014a461038407200c03d907021440440700015200200c140840e80202038034001001d1102d00e060320398030100340152030744001d9080c042c0441d00f8090150060326001030150303c1800020144500c540310301c0c001381c0707244174010441c0b4141513869080300b0104024440c5c40185900ca07540100f0541c43c0392400078200828150a894480ea5044200c000180c0c011900b4411404e0250944200e2080b443c01b151 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 990105557 1250 990104307 990104321
    0x3071d1608011205281401110a0509010c0c0e0624180f0406090b040b030f0d03091704080a140105060a18060b04030807020307081209040b010905030f0d11010c080a0f 73
    0x1c0b14840407206090117150340d040d42a001c0780105146070001010b44c10107400e9a501090007020041e042201e051500e00610152208031018909504c7c0a00d0f15528450220643e8109444102260040008501c0d10001030403034502c80010f001100410303d01419028010a110100008407403221000d50362160891a02c000000030801d10140c0d580d043d440d070040a80c08000c900a506100703107014181000205800c40300e074504002c0440382c941c4441100140303880d050840d509440f01040002034810400680007819070b076000740116059a1a043c00200700501c4640e41030b905100400541c0c0d6541c0d04070b502283c8601254070401074072103054000500c25508951120b05002ca0003105100c0320038042c1c03051500c00d400701d640c016207603600199034200303442d0302825212081205100c1400d003508800c400c1c44060401d071107015265400a030501d03103010304d007c2d0b8650060201c102c1103544440d0b0507203820140700c000c0145011b8050020020a03000340344042c1144c40c4d0901c0c480140c0d035a48654 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 990106807 1250 990105557 990105583
    0x6210721050d090512010c02060c03100b0f0c0123360307060f0b061801030f0c020a0507050f060a140d0c0c060f0b090112050c03071d1608011205 64
    0x3441d5a0042c400501400907900500d405071100c1080000140310500c6001c03d10100c50700240310f6a5134000b140d9105a00061464a0700031403500005450280d6402170071024845843e140e032910458003121b070843d8001a0245050f15030503c09884d000084582141c00081c0f205c40e4443c90f00104c3d043d0304540c42c449040007441c160340105508441404006050f040f489a50107010540345d201140c42134410410b4402e41c4854100040c00c00c150f03607840c84004040c0103050100c0e60300b10f2401d80c40100c40b0150000c2c4003680240c6d8410081280611140010f014100c403418900001c002c0840d6182c064a1640c2040c0302c21903c0d00380400455005072000160311600c18484c09004c52401410b00e45a540d080f00c041d4100200090384405900604d09110710107810007915a2030610040d07030f003070349400040c3d0303890041110003080e41d282400490050580b0440f90180c02c00303262080404d8440c020401c6007548000c1c0481001294030001060454540c00e00005e20300c101030909a0500460017408 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 990107913 1106 990106807 990106813
    0x70614090d210c090920030705130e010305030a120b060d1a1203090f090610030b0102160801320606030a0e01090503030621072105 58
    0x5040c07a81c0300d5400b14101414812490040350300603605000014082d510502005e40d080c0140e03085c283c04000001c403014401510741080340400703803c000403c0b8000900341c010b582590b035000301520780049890346a50392840c0c401d0707a82d070181c45c0300000314100700d008403040340840c1300d2028802c3d80507103414a40b8031103040c2100145401e52481502d456403100080035910790b18103054a200201d0001c5565284d200c0401031382101d146400c0c2e01c241c0f44101044450380724022280b900e18000c0c00e01007400251200144d0400c40604980321010031903900004883d441500465011114082c9444001c84002000c0301310901404002d0a5109090040750481c20800c0003554803030a8a500000d0101c2e420750903609550303500b038050f5a580d1021040c804103180121907060807030090000000c0c44078413084903d40b00d40191144035072400d560070b00f91821a07181c0d90b800d511a5030010507 = true := by decide +kernel

theorem cover : BRFrame.Cov 989928057 990107913 := by
  have h0 := BRFrame.cov_init 989928057
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989928057 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989928057 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989928057 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989928057 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989928057 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989928057 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989928057 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989928057 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989928057 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989928057 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989928057 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989928057 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989928057 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989928057 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989928057 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989928057 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989928057 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989928057 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989928057 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989928057 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989928057 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989928057 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989928057 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989928057 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989928057 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989928057 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989928057 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989928057 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989928057 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989928057 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989928057 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989928057 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989928057 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989928057 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989928057 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989928057 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989928057 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989928057 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989928057 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989928057 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989928057 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989928057 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989928057 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989928057 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989928057 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989928057 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989928057 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989928057 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989928057 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989928057 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989928057 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989928057 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989928057 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989928057 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989928057 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989928057 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989928057 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989928057 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989928057 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989928057 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989928057 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989928057 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989928057 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989928057 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989928057 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989928057 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989928057 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989928057 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989928057 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989928057 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989928057 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989928057 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989928057 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989928057 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989928057 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989928057 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989928057 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989928057 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989928057 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989928057 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989928057 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989928057 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989928057 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989928057 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989928057 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989928057 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989928057 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989928057 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989928057 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989928057 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989928057 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989928057 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989928057 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989928057 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989928057 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989928057 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989928057 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989928057 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989928057 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989928057 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989928057 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989928057 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989928057 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989928057 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989928057 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989928057 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989928057 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989928057 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989928057 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989928057 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989928057 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989928057 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989928057 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989928057 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989928057 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989928057 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989928057 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989928057 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989928057 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989928057 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989928057 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989928057 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989928057 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989928057 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989928057 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989928057 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989928057 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989928057 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989928057 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989928057 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989928057 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989928057 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989928057 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989928057 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989928057 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989928057 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989928057 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989928057 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989928057 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989928057 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989928057 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989928057 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989928057 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 989928057 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 989928057 ≤ n) (h2 : n < 990107913) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
