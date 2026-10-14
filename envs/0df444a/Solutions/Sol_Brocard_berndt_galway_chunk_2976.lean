-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2976
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T08:18:15.545202+00:00
-- url     : https://prove2.me/submissions/92b0860a-3ef0-4299-9ae4-2a233d22dbec

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 535071942 ≤ n < 535251798 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 535073192 1250 535071942 535071947
    0x20f0607080c12010e0709061409061b010e06040b070e150c0c030106140f03011104211709010215040804060e120a060212071d1215040309050f0114030601 68
    0x354000038084206040031035075a585100c110f0241c0142c80700c2c111500a1000700b60f00240c04070300802d01443c02c1700c0d5082c40314060306d055009e01030320f150003a80c000c5681171400e107211540c0c51001002030300801004042a0b01c080c1d03501d0b4192070580e210180b0304003050004d0b100b031044900d0310034040c1440704400303407401442c00e03980d001c0c12102c03081d40605694680e4503602800340c00010201090780c02e40501190b000c00c50407001c01c2507001e20a038900348190030070352280410f6900722498010300c1041d031048451000313010f0707104420041151b0103400702001401001e60180403012000c0e070840714030196010310707400000400e84025224181c103100400a01d407080e402150b145e500600b0406c3d00c041d550070f80d185440800720003151019000300707441c1c40c0f0703245000719941d1040e418501030650600d001c0250403540c440c0d4034210301900e007014041c0d1048404100c01c0c011100c0040010303085240504000700810218012a841440c102403045d580d03602ca01f1b4220755810821000501d15159000107 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 535074442 1250 535073192 535073207
    0x30103080f07050f0a030905130e0604060c1b1b090506031c030b06040f030501050603060115031512150501080109150b0307271b080f070905030304060903060c020f0607 74
    0x2c460341e21540200c0c5a0640d000c1c003170b2050f030034400c0d180c3c04411410001000780001003c0d941c110040c0c600200c516040500081681d007040e0000000110072207880d50807184d035040700e00c11409507101e00c83c84034100904070242058604998016541d05070700d41142ca8162401542c05581c198050344a103001c021181d500110050302c2420300155500510000c10000d0b005584880c00391661100d013001405000c0c041c443d4400c2c1c2c00c601a210941c1490810610015000611020903541c0e40c014140c15001d50915000f03000c40d044109a084200d1500c1090100b900ca03031540100d0030240001900141401a484074640c0300310904804910f15440c08020490880c0c9250706102d03220700000c07444104006044600c8241887d0608010100c5c1d20500381c50440e0703a00421078180841c10002e0139440402d0355081000188001541e071505001142c2c0406e454102c15814000064001800c41c2c01001602c00c4130b1080c03070b09000c11082404140d8944194100c451500c2d08400300080400b4400c2c40c0b0b = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 535075692 1250 535074442 535074457
    0x809031b030912010e0c01021606050d0f020f19020c010c02090a02091c12050301060504090c02010902031c03061202060304080a140315031e120714012f030103080f 72
    0x200d0b420004a000003844014507030512603030a0355101220444c06400313116001c80304d0400e0004021040341c4d00282c09000e005807003040304004002c951441400025009040002c1d0aa00250f40722200c07038180300c180381d00042d000032002d0284641121a1800032410035003001c816150405802c407540c0900440c07100080c5482078851382003010158030755178811290b540e101c000744042c6420340c040c90f00d0710b44888492880310034000d050004002855100080b1402e89240340030204080d2883e0509a000d49030001009615000c0c042c0680f28024511009034030b00c010039a0144680c583d280444401081482e102a4224030104001004210484018040c00249142814141107440c0c1c4200441e00281e588a028120944034441185402c00103a404945810910f1500700c80d24100190340302c418440d50307104100e000c1468010b000c4e90000864020000030003d111202d06a0000361a080d8640c400e1107144c52001e8000015545400590741a81e0b440f0034031900d0031341150703101c4185420800 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 535076942 1250 535075692 535075747
    0x70302070503161b1a03060d05010e0601031b050405190e10020403050c0405070e011d011809200f03011802210405010b010203070f11120601060c02030d080903 70
    0x1468105003021184040f49030040d20501c200c20380990382805400516806148071404003140d0f00c05402e06641103c0d0014022654140c0420141c40c18a01400c008204402203000d000c0c00042801217410002c80c0344080420361100585d229820001280c03015240c003110500910502040301100e9030040b140180b00f0030881c0c00c2c042a41c01b0341007d03a0f200d41c0044505810280000380750782030a001d03040c1c0126243c11302c42c580c0c2c881c0c0c0000034400d014075003c2803500300c6602d280b50526401b82c120f0303000829840c1d401d00082c0707071209010800350502d05100001c18240c2da4003c2d0380c110f40da00135500d942110508061a5900e00620b400540641c0c8044810042d0b08004914030b00c182d50f02c0c0a0f05c0542c1000d1004c04600d800d04001d400c40e605068044d0641d002040010000f0380070f000c0300601c45a1103a041c00d110340c1d0203008214030030504409500c4078455480013064203034100c240d5044440c402c4045076050343d80320a0444103444107541c070704e05079403092041c046d158005842039108001c424 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 535078192 1250 535076942 535076947
    0x512060f0a0b0d1104060902090121021603050c0c0d120e030705040f0b01090e0610050c1203071e1e030b0d15020703200303040b0a0b030718050915070302070503 71
    0x180c00034981c4a00d80c40104d6071100c2c0070324503031414149401039000804400004500785120800040c200520310503a090300c910141d41c41148003e21941620080403896102200001461802411030f03800004003543e14412905000d17218600004184443e41c1d0180c0113449180300341105440c2d004040507500c2c4c1c10700509001140caa1aa4071807804a000012008070300c0e41c1c00e03400058140d0500c0d0b0003200c0000c410500308100c40d20381c4c05d0704000503441071134025514249001844c0c10503c0213401001c00074170000511003d6a0b0202001401501c1814000750041e0a450203650300309404614a01407240708810080e824002c1d8000c022100c406060580d1a0030183d071384100081444c10132100304c41d070100720174082c1341c3c0c810480122421282c030380c0c0121010301d100d40303541c078000140018006c0c2c40d400c002501d1003030182c00081c190350b0b016080320361550f1104922580c0040300d03442402014500030018030104000180a0368401c2c2492041810f40c032503140c11030103544050b0041e0f034030744001c = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 535079442 1250 535078192 535078211
    0x20306010b1905210a0f0f090201020c013c1e0c140a0c060306081e0601090504080409021c1a0a0605092403100609080303012108070302060601090512060f0a 69
    0x13510f0801e200f50109080055100e50f5000d41008540b17a1104c001015840c055407540141d80010304002c03405004d0812510401c0d41c000a2011100c0d041014810200310317040340c82c0b070400d030615031303a0107007441da125446140c0b645010b140a41c2d0b02c1c880710100040040c08030030081140707003032003425800d00d000c00d55018101d039864000008041d58042c00001c3c1c0e540004000804060002c105c030071580640e4902030352000c2070060756412040c0220128996500d01160401403588119030040181003006e40d101c3ca007d03500c80101c4031801c100541c100b03080918204100b412045240900031005041d8466142088404c907081d4001d418419008030070760054a00c0b4903080703000c0b002c1e514080001c1641d00d1408030200200d240240d4807032818064401002c1c010400080305917410354040c4d64a89500707507004564881e400318808006007220400141c0c0c0000e240e80032455620a00702a250400056600c03030612000c0d4900074500c0d0420740006c8007144c941c0790a0b21318540c00010711000442c12850 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 535080692 1250 535079442 535079497
    0xb0403090902130e0105030d120f0e0a0f020a0603051e0601030f0f05041713060c030e0a06050307030b0a050a17030705060c131a07030e01021c0c020306010b1905 71
    0x8504403d5503014200003040201070200750485014090a4011b03050717001d00083c0c05050071000c800603c071441d071241c0446c940c80500713610848820050350708980800d5003a08096814040c001010b07800740c0500392022030018024001c50b40540d042c4d1201c0046007d1210710701c080c15078090402070405032600795080340d030b00490203185044421410001080c0c241441c119001241c1d5031108400c0000c1400354075440e440c200140012102c0d6414044c80c0a50107290446818100c204c0d030340c0c5d01005802010841940c0800954031440803600c08001ca50210700420030721140358407440d0b9101150ba501841560301c1004d0b0017154141d0300c000c49040c51070555886003030070b00850b002c1000388000328543d4083c111400c1d1480080c0f21404007070101061070b101c4130069214601000d0706100415a003603040c0d0744200a4202503156000c0c413801c0d0724903031260040c08814042d000380e10034402d010000c01d440f2034980450341c0300c0c880050707044a040024481030700d5136000200c09902c2042091421700300000c = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 535081942 1250 535080692 535080697
    0xa0605070620090a080a082212030302030121050309060723030307200606010507080c0708210928081009060f0b0108010501140c0f010f0605030303040f0b0403090902 73
    0x40c54070b16035444640300d10a001d80703850151720643c2c0b071354403890060011822040465a0481a0174014155404640d11440310b0340c410b948038428034083d401403c4203140c1d06d5800380d0b050700d12210f041301000c4d960f0303020228809040c1501a106801c100309402c20340c9048401032010b14803e25004141c90090540c086030041085507020454100000300b2034016882420350000c030210761070080103a0321401d5001c0d6a0a0011302103818804000351000c00e0298807001e40d01780a4018003250482c50b1152032130b81d2624444000390000700c0110001889648120f4241e45070740300c0140501c180501210341c465078240303111050400c070f10325040000c101644184009204044d40903008652004585040300c1101e140c0480700045030302d080c03c01040390707030300c140c960741129002d20782143c65450300000c05406104030100314590707128840d00d02c2c002c46810341007121202404201000b00310342c2c850a00d03440b44021900104900001ca20b00000030b140c882010307070064040d01e820919952141e15640807139 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 535083192 1250 535081942 535081991
    0xa1401121404051203010803030609131202012703080f0a1103070f0e0a0e04060b131505130c02030304081c020708070506010902040b0d0506032d010e010504020a06050706 75
    0x6541c6400b000148242005800009030401c0342e22499913140521554980c007001d08001e2051689030041040040001c1c5440d4150390020300a134000118080060f0003414114501c07108441c005c40c41403c00286c554904050303c0e0942c42e150300d02d40d100592e0101c081002080c12405a5441d802d2000a402e0000514850040398a6a0302c03045115100038100c505000151889800360b40402d1052021003061160130035408000460404014400950301d036507601c0c0303c08481c514205585807054050901e803c215a0165807a480410103012210140c03900c94100301c000d41e1040011400091000d80100408610b0007800c400a0083c2c241e1141a6800700d0800e80e41e444000c036400040c80001e115643c010601502c0451801e0b282c10350405480c015818407a542640d05c1d03000502c41d4230f041c041842e4441e400fa40c500c8100e513200e040d09010b21458510b00c0241d42c68100443d10000d014855680901d400a05a008151a2460440d01c1c0ea026100031100035880e50511600d2000d01c1e0310402c004c = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 535084442 1250 535083192 535083221
    0xb0a02030409180c121a090106170c0901180615080108010b010c150b06040506030f071812020d0812010305070614030411090417070323090a140112 65
    0x1a03518100804043e25000da1210910400145400000403d030443c1082118040c0445008404590608038071580041400021200ca18400c1148200040d40520300780c0f03407a030481c1a074580070555513070f6840351a03442140e0000c0200c00107001d43c40e0043c0103807406041d000000f0446d281c5a1542101e049201480400402c03104001404611800e006014004000b0700c0d00304422003094031281c4c4004029a0004121035944000c0c01c0280c4510007201d000e0071006d0481540c1e8101240d10481c141421211350001030450220000452400c2035804213750030982910b10000c425001c008101321003000482d00f200080004403e00707100c04079082d0003940180042e11080c3d1074440c0140c600142d400300b200200a040080100152010848204220040d15401d03c59500d900e0010440d08180106901484001c40d030841015072044105810b12420035111f04895000450171210740a0080040e50207100841c043c481220824070b991700d402e005140076241c0a100000b0307101102c0e0300c02200c1e083c = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 535085692 1250 535084442 535084447
    0x5030405030c15060a08150601050904060905090d030e16090c0c06090b0402033013030c030b0105030c10050a08061909090611040302130f020f0324011d010c0c0b0a0203 74
    0x1c1e905e0302d0110302d401030218601501c0c00350180a0b20b15107404001f02020f06020021942101c80d4803658851400b400c482c100070410f40c20a1b060107607844941c11044000030381488d0601464180101d00c48008000c804440b818039030070550540041d0440c0f94054082041c50369075a804140e06014000013070b40240e11010286c10b107401414200507406012403150b201002d54121882c25040980100025202c40c40b42c66490b0740301c1020f9591450b51010b401c61a51600c08410f01a0301740095040758021021545003a00d003005110f03610483c0c08411000c58410f00601140600941d409540510028041d80e01000c0d20804d01000c2e041076040410300b00d5a400c0d00600b0001944070782c00c0c00c00350340800c442c101807840d0f0000e245a490610346103010b81e01c410300b041c600e000300c1c3c06984500d0021805a038036403030701c40031030000c00310222603541fa130715a02403d484480d401809082c1088804c034042e02c3e10111150010364490242880131150f0540b06100055803280a0700a003007941c9959004e140d = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 535086942 1250 535085692 535085701
    0x2102060706050403020c091e0c0c030a11010606090f030209040c15031e0501031101050d060e071d010c02060405061e0f12010e090d030e0a0204061e0b130605030405030c15 75
    0x385401c5034821586d009656000a2104c0c40740da0461f4030300c2040b0401e804207000da403006c201a89e40d00413561190303030620001c10f94490341a007040300c0f108403c1825008104490391000200c54081e036034860008050882030003031002d4240308680d5503005004803280000c40b540e8003407120111048851010010750b4640a07410584081010b2880b48041d51a0074400d550450325008024018003201ea0305001d00050000c02c03000240d00301e0001895030381c12141c2c880c5450b44010f00001c18691080d2404080519030040383d6025003003607900c3c20b030054949400c260520301030111592164155940040c0041c00591001d90400020146008a07140d590384480c0204020300000c901a00009881500c6601700040648006420540c2c00c90614012400910283d405402c16040000180d003090a050300840c0c4482d0742c0000c014580640c155480a180c0da960340c89105008003c4040b502d21302c07000b4204841c0d8410703c00746800c18004d00c2560300d00318501d130101c0e141c001c50305c4808600811030710030132 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 535088192 1250 535086942 535086947
    0x10e0316180612050309191e03060c08100603150513150510021005070c02101d03010c020304030f03180906090f0209013e06060f0102030c072102060706050403 70
    0x140020708002e0340700140030035180c4e1410f45a00412164030f000c0c3d00c000340940c5c00c1c51001c50314100117000704551f440c1110b540e084810025074050209503041c505190810035801e104a1550b8412034180b640d00c65980c2c202003003100135111003152450b0401d001140070595640d4100040342042d0340d5400080c0003807805c1d07159010343d40c2c298800d910550f6003031841c10089401142c180e80b40d400c013000c005010340c1c800d00d0688201580c0c89000e904010042ca0101040382c104991450b03110b000300c079003c1c044224200b01170980700018141401a04241701c104000f44030000c14840292103424100302c038100c9140f44c018040a1a8091700140342c40308004c0102181d5032041c00200141e1080940c40c1481c014006030903840c0340c4150070420549640074010036041e9030307000091015215101c0d20310100d1101499074907581620780610964030011140d41a40c000012941819800703009041c1103803500c5c5aa502d47c09100c841c50051a02c603114800040e0745000040001c14410400020b0030308103402e00 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 535089442 1250 535088192 535088201
    0xf090b01080415050a06031202030903010f05092d0303040f0c12020105040e0612060924010608070f03020c1204080d0309080f1b01090606150504060509010e031618 72
    0xd0601000030244000300c0c1140c2050701d1003000c10240410241c44e8405090003c0003a60b20103088000035507004a9480c1c1d01000030840030034210020300485400c450040b007182c10136180d14100d80d1000300d0246800c4041801c0e60301d40200101141071203491f00061307606541c8210307000c0714001040c2141c2e001f0010385028160207003c0b440c9407440110003590020b000d900c1940540c482030109003000601580d5031403480c0c5c244114050980b001030510f182e655070358013642400c0d110480080c800c02340c0c2e0640d032003540c18100c0e002782e5a172600c0b580383c42c0c80988010721f202e40700c802010740802c084220210100488011204085000355031203140040f01418641d492007038804040c1044141da01003000039055810022892441d40c0ea14418003c0d0840f0380b06a11480510a5082c9101e540500816600c4401140d0080280030404a600b0504503040c2c4124010000402c0c000d0043e4140c41d4032404c51186800c1002e01258001b04d980c03d8001d400b2091a480039480d01c0c2040f0282c42c80310400e009 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 535090692 1250 535089442 535089461
    0x203071a0307200604140a0f03030b0a0b0f07030c02030a050307050706140307091a210708090609071e030b04060c020d0306080a1101140f120f0f0412020102130f09 72
    0x114102c00e681c0260f0490300d8180c00741c800fa116a000000003001504240302d0406415400908460720305850720703019015101c80540c140c42000400d030300040c2e000b031560465030310141144c446d07440e040c01035800759045016508140d8261180f44004400140c04000400120340114014601280b401e00020f0035070030409500000340d401031085c0012035401020041c00d550314103080301c5224000d01c00ca1149401118043c0504d180300001c2d6820300348009030f0081c01864950303074040381c0f60b4415030915500c3d401030301ca40782c481d4081c140c100308103544c411105212814820b010b040195490312420682841a2400d454642d510030b42d1030b00c8180c0400568411ba607050905201a603d803031851a1036080b045006000d1003000e58803501181c0c03180c6074a0007240554540c450b241c40310342c60125a680c1012291001000c00503011864900d421070b1a00d10611582c02c1600395039603142c1e0b502031844200d03651002999020312882103003503012800000941450124051564500b02200040e1407130700c80c = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 535091942 1250 535090692 535090727
    0x902091302240a11030c010c0302070b0601030b090f06270a0b150a0503090a230d050324041401060c05060c1201051005040801050f04060b0a0b0a0c0203071a0307 71
    0x4090003030040e4040d003600e102d5030030303818040855240b00340f5480c111b129403c5a0112035103030545c8481d04035015809861601d0064040f0450b070780e038a0700154200d8402000066014401600103100c164030312004590141000c2d003c64114684a035200c000e40d4009441c032140182001c08120402d02c051103a0084c0d08401c95084140350b0a4001582c2c00e44a50503000e03041000020009480000400054101030b5014030400d010320a60004090882000e540c1c4d864a4010490103007806442070042d203005005a070401080080119081208850300301c801030f820540f20710ba5004201c0480c0d0040340240001d449004550384903152050504600401a1044a10a110a42c40f0540c0941c046055500550781c1c000800344100050b207040c000c40c1e00175002c0750300b003208002d105099012864000c82c401e039401d1010303910400c00c1102e4172841e0b000f1481c1c1c05109002041c034451064008010003030000d0147d90a05072180038000c00055059082d220489002040c072210640c080100d0300d041c210390 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 535093192 1250 535091942 535091989
    0x23120a0206030a0c0903080d020403053706090c0306051b070b1302030a080324010c05150a0609090c0611030a08061512092104180e010902091302 64
    0x540c0080c80310b00000e40308840707060307a4400c00c03112940105013400255820040c1207480b2041c0c0103101c0080d5000d8001110316003d105c02410490904125501d1000405224007440c0303804801140140310742c5030800d6a940340c449140c0004200c2d80006a40918080e040c0440c40d850106c025071a201d4944052609041042100303070041041014441d030010720034000d0020b01e0b091400040e182441130040500010000001e00040b0300e5108111104021103070304020071075030380b04d0040d1060b0207115009425074129148290703c01900c450003d50080d546400005d03900d4030703401a0000c803044200104d841c241c0501041c845c0c075420107455030044603003a0046180080540005100d0203025100a0040d20352441403481c10002e5420380c0c40c1340c5d001500914030382c6000b0114903566902c0b01c2501c0344c400540300c40c40b8040e8054078110740c142d40921805078016568540c0700c0c0b0050030f14225030082075585194600050b0b45c0ca4000038000c00c8020241407070410580104010403491884031505500741 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 535094442 1250 535093192 535093213
    0x1050901090e0702071d060118030f1101030f0c11011107020a0e1b07060b090f31020a08100b0301020315300708060a0c02070515042312 60
    0x100d00304159410101d4260141d100d0705001c4c0d2900c451034100521000c0ba404240fa400b01c28072403524841c240c00d81e10000a42c4a801c1c080951100ca0700000d80044030103481785c1c011070500440742440c17450600d800a52810034107010421209008002d44c00500042d01080364a031090250142d082144010345251459550000b0403801c00c91142d1441c0c146c2c5040084e42e140042c0300d030100e01e140554099a6141b0302413401900409403405810700c1205044080b03000310000c821980c0c801c03105000080c01c28070b4900d115416007141070a4604c1034808880f044c00040e11071003c60b070003d140303d1000b003046664001307201741541c115014181c06070388180304220385803441c0340716400482d0041c2c03813600782100c0380d0341690320100d0b14070310104444405141521400314002012001c940603c4141e480700c0d11082c0c0400c042e16640b040020040e070015600b030000d8580b003c0d034500c0150b400c0044a103440e0307484c840c0e41e0b030a10150500b83d4150503d0741d000c041d6414550914401c141d20100541051402c = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 535095692 1250 535094442 535094447
    0xa0b01020312040606030b1e0f0906071d3a02030d0e0f0306040b011d0103021e1906090611160e0606120103050c0a15050301030f030e06070f0209010501050901 70
    0x2e1014150b50304902400410f090105540c0a01c01450f0800c44401d000d00c0c1c4030308400e0356141580b101c81d811140550000d2600156590404d001e03489501c041d201c540c484650844001c1a0380d130300b2a03103010305c0304c41070002652004545070442c8100c41250900a14505603c0007000441000c5200003c12001400040c2e03408aa42c03200c1210070706049804250038804101082031030340440350181304020034001402aa036a000d0304a9070a900048001c0e04100a00c0220120078400250014040c14103c070305017200e03441003c155540074046180400c103a00b200000d041c0154440b0001c00e5040b081801f0040d07210815440c4038400200629081c80c0080300807251010520802000b803480e0301c0411426a149000c03140b00050b500003445841d40c50f420980d4445801d504050721514034910005290302d2038a8400f929610141c9480d82141c3c0396440f01d006049034200100c081184240340f0124039a5110083c084082c05040c0044648143d8814001545e206800c020306122040c050a01140c5c0d = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 535096942 1250 535095692 535095697
    0xc09060604030c060311160605090601060e13051b03010f030b010b03010b090d02060928090e0304150e0a0e0601030c020303090c0d0804080307030513060c021804050c0303040f030b0a0b010203 84
    0x2002803800294881b5120106100f0b4000d0f503000c820b400790040075000c00e101107504418041c04000c0c05544050740c2e43c2d41c0a6540c02031300c09101e50092000201c80c2d150303080607480b0540c02040c80706040c07140c8061200100e0b455009800c10300c1c0c440b201c890117100b480101c0c43c07802d000d402011081d9145504100c120700d41c41c020181c01a100313205d0114400c0454440d242038034041940131300203a0102540c0d0b805a0070940c240030511011403494100010241c0b0755020340008900c090002e90718003402d1440c41d80d20b08007450b0360320303040c0b013090b40580c04940c5460100d00020000035441c0720107424260300040584500301861000c6500506c01c1c09003000d004200e402032000212001c04103001d072460100e41501030b0390300880311400003003112014903420200030200411000d682d2686191a4101500c0300124030401a400c001d92000c0c6140020300400303469000f40c0640116040a580c0f000081e245900c0350304414800006d41e1303010410000d0501449402c00d1521000703000312540c041c0001d54a0 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 535098192 1250 535096942 535096949
    0x60e011401090903020c0303180103050603010603020a0608181902040b030a050613030c05030d0c090902030c0a2106090209010e03010e0a0f1b06030b011d0a03260c0c09060604030c 79
    0x1a580f0724280302054000c002c01b1003400006001c0d03030384a540c3ca49030031402c0f281c0c5c0d151050200b800c04000032518175061040805495000b0070812880703003050b00440300b000001304070720038203040f50680400801007040103c5021564000045542d070b520b20500054814489400e07000307501051035903001420201e100380d03000c6030761600b2030100e55150800b00c07060307180c10001401c40c0c04009810180c4003250781000c03071500710546864101035515003044c0c1c02ca20044482e815004e0341844103000d00303031060a00883d4141c050800140c039801080200d801c441140e442155842d50028003c803079540c110b03400d10b0115400300c000304000c048641405031281418840101401d4406a0300c4040201e40401c00c107042c1342c9a4049400746460303880c050300401d26912158042400e44403203075422300d0f44518034901010b01030b0107007503920300c0c41d9643d00d0010004c0401c00c402001600d4440364007440840600034111091009140c1c10000006000106001609040c01001c0400c824008907140500f1076044 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 535099442 1250 535098192 535098209
    0x5030a0e040e060f190e06090613050c0906220501140303070804120303020c06010b031e070e01030b030708151602060906040b06010306031410050a02040503120702060403140a060e011401 82
    0xc0e174920250311903d010b00f444004400703192505440d80954005003240c850304c0c1c1041200c030300d52600c5003601c17002018101c000b4401d9020502015050a00b2401d403500001d0103010003c05d01c101c0400c1d100000780904581324100d507514010401d6090425410b60880c00540140d490440076880d895814451409802c00d00c0825507852010503209074103e440048101c0141d504558440706118010790003034610384406076299000d080031101c0c0c503140c2ca000300c40c80d4807040500780041d40150702400b1440019a810f02848400107030b03000d8140031884448005c2c2603282c80c14a4506001000348010400c03070340c2150311901c204840204000780b255006a0008141c142d1540c1d0180103d01074592500300805070200003580360382140001400754500300355180c040c03259540b0004079004a004d54828650f05602c801c1c1c0d0b05000e100060010001c1c039001400303451034591691120507901140b80725102d030036840060030a090050521600d14280000c0c4020700c00b902201142c01c2c3d02280c18064600e0 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 535100692 1250 535099442 535099471
    0x5091209060d200703350106180b040f0f09110406121512061a060904020a03060e0403050c10090c050f030f01050a020c07060c0b1612020705030a0e040e06 68
    0x5051481c248880355030600d040f0320341d803040b0030b1038010150740c04a281c003603080044c41018030061b82441080301411410341c0380a181a03103041801c0303e07681030603142c50000b240307248800706d80740042e0001400034042601000c014189400c0001310001010340c8600b10300d6143c080301c01c804800503800c5130126891840d19003660040040c1031001000c3c0548012807071710350040005088030800090411050042104200786620102c3c2030811b044000c441035400002003002005a140681c050822080b20380380010f426501c445085001c7c4070240c3d4140c01041c00400c440503141c07404c2044101c81c2c1552441403000b15a42c1d6218441144140500e520645098407800344540b020415811b1a81840000348401e091414a0300300940c400d250b40c941d0350044520104131310f07010b0649642060f41c070155500305583d807608034455030103407880d01108100600289005401c80b07030014000030303070144018596504045d00d000c1d21080781c41092174056410001590b484030700114070307154895014443c010 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 535101942 1250 535100692 535100711
    0x5041401060c1e03090302041103040327030b0c1209190206090103020c010903080f07170412030908120108010f05283209011e0903020a060f05091209060d 68
    0x104403050300300c516041c0c2410f00e80744818590b104024208690017510f04000110b01c13032810554610080700c0250108407072508241a00010400e00242d078051f6100b03441a140d02e80c0d444288020040c0c906a01c15800400e082c280f8042140e5240c0d000302c031580041180031902c50030a4076040d81048064424607001c602c030754041c1d000f0740481380342c10041d90007004852a40c0ca0003400c01c21090300d00f51070014207103000850050141c580414941c500c86100b60301a610703a601c0300a020100040b1804040c1c5510a410009114130094411040500a001d24940c10001e40384c2c00c4483d402c0b06102c0d01420582404050032030510680c01c40d180c00c2c3c4032000450380f00d594080c05480520b600c4400d0038503401d03000c900ca204402550141a50003081826280c0707607030700d07071703034207860304c50100c0c0c014025a8001c000d99690103900c80480035200c1c5c01510000000d64840004a62160100c034000c55101d4003004205182401411800d45203140c03201e05210318030300403a507540580030300380c0200d56403240c050 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 535103192 1250 535101942 535101953
    0xa050d080a03150602010905010b04060602070504020c210d05070f050703120e070807031a010b16060e0d030603030f1e0e040f020a02070302030601060305060619050c071e05041401060c 81
    0x109503401c0003419041204e5860900030b0090071880e500703603025464807490f40c402c1c1c40d00740507403800c03a0440d0740101841741c288801c000003580800486032491007410109100040140c40b601072011082c2c2800da02c07561610401c0041d40d200400003010800d14007850340489400c901510b0341507401d49004021120304101c4c06d8020022100304400b144102e07680002e4130100051106c0c01d6901c20109602c0180c1c06181ca088040341c203016007003000b40305012040c443c40f00b2151341c285071401030f2408183c0e1581215114207103100e0690000c0000d488040038130516400842c0014030308440e15003190365180031900c41c0d600d09081d040030b9081000d01c20b4030310741917550b80d0011040000704c160115510300170600d02960f504594441240a400703420000656203000b0700c2880d21500002e08128940207105403000c910b01d410030f111a00380b000034801424644010040703480503104d0421952502c01415100301c2c4901c4644c1c1c000381c442d50509440e03003000707200d0343d030180d04451003414070400d0a031041c03410 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 535104442 1250 535103192 535103201
    0x302012c03070f02030a0b0117010c020613171608191e0f020a0803130c0f030f02060703050403150501030507050418020d020d0b0c040504060f14131e02090306060a050d080a03 77
    0x2c0c01f8924244008aa1000d80384503030146e070b8400400070021041000d034140d807110001c5070030802c100e108202d010040754115028400b404e4100e441c00d40303400714581d5081c183e2654440107540d5100003080b281040703000e1440f068103895860411510207003d04c840000400042c801070740410400c54172500c2ca550080107034807100b0740d102c001c294070380c500b0400708007480c5686202602e41003070b0b200b40001d0140300044070a060f69004a141c08140c007064080c0503807940b010800f1000c00104100001c00324056404111221480050108181d413440c201149032030b90a80202c0d10440c503045504039902c081402250341c20b607055075040301402c1c0b03600000b424070699000c060030170707412031041001da00e0100c401001a200111410020103490356003260004900e400703520020ba040d60b046903224074002140c2240c11601d01e40115018012018003459100072001c2c283c3c2443d004160403017a07190034842c040d841b603825112001800d160800242400e661240040d00d61040001c0400030b89109400 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 535105692 1250 535104442 535104463
    0xd110c03030403060b09010e010506030c0c070e0403020c1e060715090501051303110304050a0303030e1f0b1e09190902030114061201050709050103020a050c0a0302012c03070f0203 79
    0x94030307260b0356030f07080201c0607000d02040180300d011031400114416445810f4039040e0350002e8402421640c0c0c45110701d01591200280c1d080610400600290040540c05d0f410710079486070f0302800a941b40c0c1401e10503501c035200c0d180c4000d20603842070007200e40c440300c0c1034428541d0406010078242d255480040024000404060210350a04041000d0342a15000c0d01c052144260384910081480e08241a224003450040e258404420f220800100344640c104c0c20780e0750442403e881035005090b041540c0d02ca03030340060610403a2070f549005000d10301845110f044c008424612030889000000003045040b000301810b000c0d100b60980b101081042d54050f035800c5601800030040103082c0c1004001501044030704922031101102003442d882c0040c0a41ca024a8a40e2105000c0c035041900540c06900031403540e104114060007425221441044502c2105002e07800018030500b0081800880000c2854a414003110715a41c4280e4210004115044030740c01c110b800c00310060910000381803101124 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 535106942 1250 535105692 535105699
    0x112060803071b0b07110d03170103050d02010b010203090f0603071b05070510110a0224070b060109210809060903100608010f0629040e0c07050c04020c0d110c 70
    0x1040410840040755003010761414075900f14446541c0d0b43ca00c4524030500d08010410070100c1c5000d0348a0501c0c84841032841e100f03041540c004013059502540c03590090307200b40e07604d50246803c610019028810094681c1d028400307149850301080114245044034028035004080000000344018070456401f6080305444400e0900040d43d814005d80c1d9030150b000b00ca100c0c0799407440d801d0001303004845448403c44480050510000e03550200208544612003c200c0c0152440f0100b80012414000704092031080b003103a040d07070400c030000504000180d080400008444804c084082207001600e90b46030358401c1da40c941c1c0765640c001284c007070300075000c81a406200daa0311005085000d070304240d0a441ca0071008001075040c81003018242c5107036101d0400744030703c2c4100720441418030b14000040802da0280151a06a075121641c01c0c2d10b10864801081c0703100451040b04000301800325071032030750301104e06600308044103004584070300050103010148010301990300301c0d0500904c054102024004c = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 535108192 1250 535106942 535106947
    0x90201090302300706030b0a030f0b15100908010c05040b1e0708160501051515030901021201030b1501030504031e03060305030c0a11040e030a140c010921020d05090112060803 77
    0x2070100503520300045c02010301190400c81d042030315080c1444100f0880f0f8000302c0e200001481034452607070040001d00040e00030422491a10020340b690918050121401c0d654800d11914002419003103668600318442085420002000240c00e288107841215003401d402460324500c3e1810302c4102e00c039588000b41a9940030480d194140c401e800032020642c0107000a002e1540c0700320480403031400c3e6100d403c0d880030351202c401c4124600f4101031584400303608001407420b00c00008004d10324130268803c5078403091007810007240d580d89201100308040d003801c080c80355082958000d040142410790003e4015203089410008034030a420032001140c101c1d05503a41c1d03002001e00d450321a5038080f0180c883d4020042041100c0c242403046d040f098200002940c24280803640c02c0782d000f41d40e40007034406103005101d0030302c00100a1190f500014480c9180c511082808042c803008210244820f03000d40d08441c172190359a03600003003102c3c440300b424030340710b5040c1d0001d00e1400c0044c007082d0404003c61101 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 535109442 1250 535108192 535108279
    0x11a191206021206090c19050d0203090304080d031506030b010c141020040e06060403240f090c0b0c01060902030901020903070807080d08040204090203010c0c020103060504090201090302 82
    0x8a6000303211100703402c149440c06654130400d000d203840c020794681c2004c8408002c2011000f01d03141811080d801d441c03800a00e03000444002c502039070025075004c5103e0300001810401c44804110141c000c400c1d40c202840386000010102e403071041284116414980c075043d01c04907a03032003400c604000a90082c1006150446000029520003080c101703240c2440c0391844000e0042644000b1403a4801d9035841c0901d45424010341c4998003402800c441d4100006010110004117041040c80c02c0000c10035440c03001f095001c150360151019803028801080c0303012011b1001c41d200007854400d98100c41c1d0303456910750300180500c1c010061940402d907a0761010040c031481d4907040d0010526007004900321042c0035142c16420340c0b81d100d548142c0140e0b900003503c00081d180509915907016000400004550007517802103400d64032003680d03400020301101c04a40440d86c1601c68000500002c2d182001642c3c0d040d400a001c0700300501004e48601007603400b158440c40c18071000070108407820340d0480751521 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 535110692 1250 535109442 535109453
    0xc0302030a0b010602121218011b05070201030b0d02061e210103120203040b0d05131709040e0c0f22110703110309010c14070504050c0705010608011a1912 68
    0x802c1c02000011b004940544140c0c80c01c1d070080d500c030300012001000654440e03111711501040c0304103200c281d55407a020441030250072180720024441c03003902c030641d0741c20142c40010102c90315011850704c00c1c04001c04990150703e805041e134141c1101d010b20754404040c1d140d00210300d80110b40d441c952160b41c1c0c00d0300c0c0203420318440c2c4042c1201d00c11b02d10752445c84104201030740c5901581c098000d6103034040c032117441c000410703410a03604030090044840050109447c0d0b0100040c9000c10700c0080000000d801441d4206841600c200322440b0018000042012000171420410303090024440c030260710074140e42060304404110002d914200800c0401480080740106d41c008120a80108280058003003c00c10080221209410b0503512044140c4c820380da8920748601c0405c14000740d20500d40c020030b06840300c0c400e540c001c1f441e28603480e44842c800d140076070940f0354035001003000364106040000d1244c0a40d44518044508445036020905400382400740c1840d254809044a0010700300c2005008 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 535111942 1250 535110692 535110713
    0x801060501092c07111c082802280207150c0506012705090102030a0f1514030a060218090603060609010608091e16052b0c0302030a 58
    0x10380a80b10220195580d0400c0c800312052881c070480499080b240d80c0b00340c0c2c1d0300440d1035548044070741410709601c8203402200b072811001610b203103c00c40d03900c0b404020b8107070080f42280d407242d50404041c2102d00e0168030140151451114048210b070040b81d10407c07859050f1100c0f003a40740c3da0302080c0850b010035030000e50380d56040c4914805c180e07002c5031a015a5200b030f410b542595410400a02440c0d00c1c04103481d9000140d022001d01004042160650175a61402883c0c01412680000368603424042c0106007120100744c020b005452420003641d6480c029100c5160454401c50364502c00441d810012030308181141c50010441c601c0019500b03991882c5007500d40d03415002b03854800040d030b03901040c1070b0380383c1d003d40b0b40b0741e80700d0344080c010003140b8031030000c965000c8031500540b003094168090209030301a00002891150300950750031403d25119601c1c0c1c00c01000d0440d0b091400c40d074807020b0502c2030a1440c134005094203142120f6403e002070201030a0055601904491500d4030302d050010302c41 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 535113192 1250 535111942 535111949
    0xa061817030a091a1c0e03031003021005120a052a07030e060a120f0b0d0b01170d050f070c0302090106030f0b030c0f040b12070f0f0e1e070c0b01080106 67
    0x240d03d5100800c6000750080c100080790782070b0310010f15004181c1940c0060030030502103505001e8944005820a01c0244061800f80491404a50019003184100940740c41d0268030340c4200481400203606115100785001e40102100400284680307541c1414000340c00740c00d03800c8101e000c880142d100d0304010080100285070090340c41c4081c880390380c010008507100c1e10325445e000800d03800c0050070640340d40e442004c036910301d500001214410b140104000d440c51b51404e90340f800404004100c1c050b10742810b08040490607000d011068442e42014042d0b0166440b05901e04201150b2402000020903101d00079540082c2001303050b60f52400000d01030f01d50300e26110070f41d504080f01c02c445800c3c005000440c1260040001081c150204140402024540302007a4009241e03aa03e8210036030034484000905040790401035030500f050944c0d042d605859000c900794040040400000010303030204c0180003c1c2c054060041c1d42c580d9841102c0031014941c0150070443c0460000842070030551118088 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 535114442 1250 535113192 535113197
    0x309010605040b09070e01030e1f0e03040602190606030503040b09010e0907080105060d0209041b020f07060203030a0e0c04110a020f03040302060313081215011b020a061817030a 78
    0xe868503001803009071154800c00580050014000c110954000c940408070f251042c50005001855100e80d68a001086031555048450b21044517032040164040c8a00030002071004601d051715080009550799000401c051302889141c003020100481d540240004680203002c40b901c5a0701c039080441d20f68006601140800e8101440f03c4890909580d0988035054580702d55440d07a18002c04d01860364400c5101c000000e0303080113040101d030b981d031107400c02920000c07074420000c140a020203803402421289403c810703400584e080288941c000100d03544828014070101e00c0024051034246040071004016500c10308003103078500c0959642001d4401c081c40b81e4200c480c031100c1640300c15102e22070f500010350000340400c0010795041d031300001d08203054800c508062a00f00c0a000964a01c2403d4490203a0f80b201c24803030703020940c1e0060409010786441c42002c441d005065000516030001480b0b01c00501150099500100042c45040d00c002c00345800c100404406100b4029202d60000c83c12078007 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 535115692 1250 535114442 535114451
    0xf0106021f0c0c08040b0433050a09080a0506040209071b080f071a04111e040510051503010312090f180f06090c0207050306070e1c050102030705030901 67
    0x254188009410168540d480340910032a07a2080280e401610322640044140546039100300d001400e00c500401c020310a00303502a8036982003117050b01c1a46402900d0b2451032a00c0c5003014030078080180d16694070795290a1541e030320110607100341c4210b81540d11000300c034080e15841209000d030204009104134801c5030802810f40e07032058255080d0043c02c400e032000300b4086e10801c00040049004104a000d5a041a810490980d0300c2c2d03000340340000c1c0044060540c0a0510040010159040041440884006144440511283c601c41c409040454071441c0c5a201086941480e5040030001d0300740500011102c0c01a0100d41d1002da001780b10032200b10801c039202800480c07284001c00240d400304421100078070302d800120707040440d1a507031601d80f040d9039024890380402540b0403540249120400810031680ba41e0307001c6d0034841d080d0b01040c040e8002a003084540c2d82c2c4101005590391080742c252003103040130309042c4480c20b03030280c00a1040d0320001c244607066402c640030307511900541d0028031 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 535116942 1250 535115692 535115699
    0x902030a020913150b090a030c06020f0f071d040c0905070e012a080d0209031e0c01020c091303030e0604031707050c1005090307050a030513120c1202031606080f01 72
    0x40c104d4800c04540c1c8420361811038248070a503810710041c15100d1000b05102c040540329200e804034694a58080d10143e4000b0700c00c0c8210000610460511494010142c01032514000401e1b90780f01c8545c448401ea50700180c000b500300b1a40038184005803115680400c01d618100030040e200c0900d00a000780440c08541e400941202130340c0d15070560078041044410b0700350b41d0740d4a4220300c0d0828031501d501b9540a0010480c0c070744081082da400116483d410400d17030141280c1d00c500300103800311028115088400219103688030881e4498001d000002a9091500030341412002043d076421810124002e500130f02080c968002aa18088003020b040003640392208941610144070f450310100c0503070000120003140070626405994010f0003101601e19101c042c1c1d03240d60400c2c1c205c80048000c500d001c10030610001c0078040d41c402130041010310301110043d82d29440441c2c0b5451080101c4001c443c50201d085450074041c9a250745030100c021038a00d0340316413000e043e0300011186040743c018401c0000 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 535118192 1250 535116942 535116979
    0x8070c0506010b1c20030414010e06010e010905070903110301150308040f0e2e081e1009170f04050909030702040b06090108070c0311030c060603010c0201140a05100902030a0209 78
    0x1c5511740c050028181880007101840c16040104141d4042d0922003008490742805e0144407034a0302c03181c0190019605040454a1056041c2c02075045140340404102015401c14140e1050740d130400c0b0600c8040c0714110000e4050418000d54100103412081c0010030400b04070068002d449240014003403a5442c0ea07107001104801312140c0e800700410005490004040d01c0d01c003284a19044001c100c01c503102e012581c60140010a0301c02071a003d40c0348001801b50610008104c0c0315259000e10280c2a60b46412458014420020003d00c100007040051102441c04490040c2005445201c0c1e51501d517030019200e4200000c180d0045040504044075441d00c3d030211208040141c4410031152128507007200c043c0400714080301446200080e1641c3c261040000d0400d84580e44000c148130b1502000389825281c0f018140070035a814030450000b003101c4804495401941d82000040590f01d030741c2e09100e05040b5901c0302001c00d100205020b0501c680c0e4001780b101000903600951500300605c1d04 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 535119442 1250 535118192 535118201
    0x22104051b04060b0406020a140c0a09020309031b0a031103040506030f060a0b1306021509030a050a020a23010b010905100302090f04052505041508070c0506010b1c 72
    0x1416034106142081c18022031001d50440351070054400180300e03848203010000c5030310a801040240c0e1180341c50404114045030b4403441200401c0c045c20300c0403e04c601040d081368041c0690504540c0110026944001c02c0080e103010f00480702c500d10852019103001e503102c0c030340c003201640000d48030103500e00d1401000084504550f0701070b201070b1071640c0c2c01012001030000039040c2c65001c4845a400901c0111a402604d030b2028505030810406281080103883c19005a01d1401c1000c00310042103890300011050381d44010703290810560311031081c881281811004100104802c59500b1400426a20310a082c0103131112440200a10309660b070040d07903008094483c040c0d201e9114044818201d1080e000381124a00240c0303441c0030490040001000c0c0c640072a1900341110043c0c4c11031113a001e2814108030444001d052180c60315090841140041c03a041c1200303418081c95074080f0300310500c80c050141803541c000003035460550b100ca8484010380d002456900f00040d20303072100100007140d40f14 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 535120692 1250 535119442 535119451
    0x709060815060a020102070b04061a031c051e04081b030c030a02040c03020f070506040201080f130605103c0b0712030915050f0f040b0403111606030221 67
    0xd1a6100c00c40003007003a01e0f4801d10088007155024088500000c175070030345142c040c610030200410704021250501485040020f0031500c02d6210030103c80086070480c001e410440e54030310345680d0f1604110800e1140c4031818482040e12080041c0004900d000402d2070818101100a4010004042420965210344142c5042d61517006000700d9001450b291b40b19604803009070038054200030009400c00c2e11a0000e4130f0949040d003100003004219a0b1040000fa8402c034660601416400c00980c240c0081e1000c00c1c00800440d9100b004c503d00f103081c2d05990004000c0410000e141c00c0c0000314801c3c600a0042d8072512016030740645400180b080b41c407031380a454000c1501c13410480e0303c0d01c903e842004260183d009041d80e600200307010400c0c7c602001c10020080d5130119060400f03000b5510741000080c2014a200c0800e0700b4000080c141c482c0d0705411503011710b17241e50a01d100503075550411303459200c900140303680182e0020310a5095000b40c540000b240283c81c0200040d4101172450580896 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 535121942 1250 535120692 535120711
    0x151903050a0c120509120f130503070e0a0507020a0f05030d14070c08090406091b0f0c020a03320109030215071b03030905070e06120106050102121b010c0807090608 72
    0x40c86203d00030f0a5034040c90380300040707200b11443c4502c0c83c03038030081035881030164000200d0000b407000403100f0f00c0c810b442c00030802a0000e0034050b141980050340290043d2040c10556111004108d00794400c10410f02425001058515550580d15200c2e0356a4458001c0f25100343c10b0403007000c8011050046144100030307d8440d180000b5003556440703940d903c100515540150790b2940810f04607003034410401580610380390307512485904072000d03083e054049034060400c00c40c40004401031326040c10380c0b8100e070345c80f0030105880060242c10900502401201640c0b41a8a031200c114403001500300c0c40f481c0c0c0c0079400340c40f0320801c16104001d4815044803990701060a1007403600301144c01907600c80050380130b07180016852402d80c2d1901c0c1802c400d03600c02e00085020b24207000c0d16203403100c0b40d0600c11400800800000e4039180000c1e460b490310096800d4402000714a0450300c0e00441002204000c012008000708191298003900c015400d94040001400c09003010603094000c8008902822145 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 535123192 1250 535121942 535121957
    0x109061805240d05061810090807030509130504060f1a0904030e011e0302031008150a02030a0b0d0b01080123040f020a091b020c01170f0402151903050a0c 68
    0x142580c0c0d040c44180b0342165044a000200d020124005100c01c9001c2e0703403900d03085104211200f074a50318040301f051981c1c6d4038074a000c250800140641c0c0881d01043d41c1402c00c4c0352940c11207400a410440c1c00c1e294002c445040c08100010041c4550200c64103039603940301000310494600305030030701b90b481801d4a41c0280100c0b0214011a000e40f8100009044c145441000e5030004101c0350042c01c4100003030000310340c000c01800121000500650040c00d110750003000150f81d40141c0e5240034134003810942d0010307400400302d5101030150304200003442019100301c850304640d140107513004400340f048c40c10552800030310054240d00d0f445080c03010401201d80e040f0030b4a941d10f8220020b40f20860899000c41051000184084180500c90840c2c4c10391403191651540f004000c0c1c02d040720f040185042100540c000e42c4250318590b1103d4200b42c2c1032100075426620343c03020a040c030b03843c50f2040d90f15403c080b83c1c0c025a035002c00700c520203c01003660244259269a40b000c000e03141c0d16140b807401304445 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 535124442 1250 535123192 535123231
    0x110c01080f040c030f0c0905011a1206060f0f041e080d03020c0a150c112d07030605100609090b060702060a09051f03050108160312170109061805 64
    0x355100d070707504a8082c02440c400316a49544400c00002450000c8642241000007003180c0a058440c850040c480e1002c003008520103010402c0c407501c54149a07904041e01440860b14030707201e020681d00b1600050660554035280c101000100384c126105192980c11040c1003003007030800c0b0401c0c1c842100c0c80b06005007419103544405401030341040f0451460740c400c11140b440403a1aa1141440039907845200203403159044a00508242c2c0c0c158004030150f0040109420314142003400030381000720a0301c601141007890381c1d10790a005d0319500192410341418240807420303c801e000c0d41c080380e001d5140c203084141d4a04118003982c548908595102d070f07040c0201002b50400100a0035002c1e002e1400c85c400c3e40e2910000b980383c6050000182e07991481002000704e0070b401d807140c1805400c1c0040288981065440c1c07418500303a042c00004c0055940c0310840b0b1126002e58800c0d0b0601c1e80d217a449100c20368443c1100c800074103143c0f0235060181c0107500303a0008200b4a1080c81c0c043c50051100140d0504c0 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 535125692 1250 535124442 535124461
    0x3020d03110307080f04030201110c03031801020f060a050f01080a0f0b1f0f3201140408070e07201203060307030501060803030a0b0306010b07120311030a090201110c0108 75
    0xc1c484120032960008010b000005998540100440b421120000b504c0b6410750000500440e921200340003141d2010b051880c5607076000081d10704040003601d0511080c40c41000403818181040100b5005205031800d00c2504116600020310400403141d149030b05d0713a40d0320602662050b1600c80075001d0808100c2501c00300700107613680c03035014201e00d41030701842400b45580315102c03170b40e0b42c800c5044408100040c4124041e05848076941c078000b03d210f10781404480400d11515050341103184c188550a41a14141100c8030305980003454080c00f039a07000360366505001c10001e0210f0700e440019000d0044803000c1c0d14289041160110b03240000c25100c3c03400c40b0074510300d61024180680c180304070740d00000000c80c24000c032005491664059601d07030400c1c08070b003010784e42802149446a08100018025203101c0e10950301100d400451442d14604a00710590060600e00da0502c042c00002042242900480d080480d0040c0b0030380e071340c0c902d42201e141c004e074540c5840c9100b83d0020b0720300030200e008500b = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 535126942 1250 535125692 535125707
    0x4062102040c3204051009080d170f070e030316021305070e19080d050405041505090a020f1308150a0606050405040e0102160b0f06040618150302220e030403020d03 72
    0x50a0392420f500e800c1e11400080d4050380c882c8441400601500424050900240005103100c0280c2c00d00c84040054071050008d0050001c09007200140c2c000f0010740650b01c6055004006000075081c3d0ba900c9a481c604112503070540c82c0260b009480142500c080968140706891007540e480e0b0301d81c00c1e404015001c10816500101820740d00303140c0854046036128050020f60307411500c03074982c00e95031443d000c140300030b50f0480c1c0300b45541e00042c804204003903206e02d0f4849034000380001005944011618080600f802600d5070040c2e8001203c0000c22055030001c0d50342c510044611041c4125900d0b00814001e4840307900681c000518144810081810140c20207400c01a44000140c1001e191020480700141c01c080c00b9607a8200391024000c00841c0e0502940e00194261401e00855043c281c0402e0781407010f0110070441956a101150701c51051496207001e140c0c001c0c40c012a40b141c40441c0c01520811109040c229807501c1d21a4030000000030440d021640d02070030584803145d1640f42a54406c = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 535128192 1250 535126942 535127027
    0x15050c16061e0608011d0d050f0f1306050304050c0901230312031f06020613030e300d08040507031b080d03020d0507082404062102040c 60
    0x40030807030380c8000e1644541c0140d5014004e07040c0005501d92104086809044424825400315000500b98180b4107601c4030480799013409420742c0e60758895612541d0070040c400d1840694080d00703245d4010911640c484006c2d40070318014001c64219030300080400004031420300c125851200043c0c0c00318845a030440703441d6282c2e040101641e4401c00511001d00056108941d000c4404403002c0e000a41c030340e00003602201511a502c014103044c500b491200c00c440c025030034090180600e0b80080c1c00181da417503c4c201c10040350040d00c40702e85040312407800400301f90784100c51068061640300400c03e034400e41d032583c07040390448000c5c0130441ca10707181c115283c03655500c01841c04003a074802180341c0c0001c0000582101c650381e03005a8075420100c0150854102910b401e003001140c00511122282c03900300c0b0006c000c0d00a500758910340c403000c0010010002580255840880d188901c400c4480c070840040041c3d000341d5041c8401d0b0000072080324a400c65102c10040342c1c408558034601d02641604101d441d = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 535129442 1250 535128192 535128221
    0x124030c110a061d0307080a05090616050d030e0307080403060e01060f0305060403021e03180102070f03030806040c21020c010b060d1508030f040b0c0709060315050c1606 75
    0x80391400c00390b401d0141c1c030780c03080d180951561350482c9207031a0881070084d10b00003d40035500301650380e40d44038801d104a65a41c01008401b080c05586a0b403000304a5465101c0401c2d48a0503000358a003080c0c6410b2004c00c0000800e00c0d1010503040404080101d4081c107602c602c0a524003400d5030795510040510350582b1000b5986c500c0086103040780d20b045030740614002d00c0100410324080c500249080c00034901010b501000d04440b660303825001040d00c45848500340704803011112600100c0c5055240d51005007004c1001000000f81900300a03081d008600642c0c050144803204142079480c000c02c0c15089401901c50440d405401d482070313014100841c2c405001184c004190800100160041d06656a4055071141401140c2c06466041e0340201000000f0310305060701504000d04a0007240f02f1100155400a804084000d0a00840001c0c0c0780c8410104902e41c1c680c103001002843c0323201600c00131031070100411900c102035020307542480c00e0308121171403901e26952120040c1c058406076440 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 535130692 1250 535129442 535129457
    0x10816050603180f0703200a120501142809050606060c030f1908090610050409170d0605030601291c051503210403060203130c0902040504050124030c 66
    0x41d0f41106000070200140351400030321005040d402d044408105a1000c00b081038040e00d103240c46502c80303407080c2d81101c07036006500400c0543c505045000d00b40a82002c42c00780ca05d04208060060030a4a10414082402c0141104044c000c618011240d11000282840e481440050100d103000001003844d1210720040e203041100e0701c0c1075200c1942081081480c1c4400582600510590100c06254090003500041c11142400c8a40115111b42d50050302d00882d11500c602c01803203c4101c03850a11007000414079500d582e00d040c120014840c50080e2882805900000a02c454000307046841036109000240030407003d002c6040d0031030780159100d030100b204408081030220418030603d841075118a90244038070400c4001c16051000e20f82018850032403005006031007040384070680e002d6942c0842c005949464551610091000324800145041c400e2480410070007100c1c2c024100701c5005440501a6036202e241180c080c0c001144810301060b850401d030304446100780c1011210120074180945e = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 535131942 1250 535130692 535130731
    0xb0c0f0708010207030809060f0408160203120a020d020d0503070338090105150909040201020c060409090b0c0c0d12021b0f0c010201090c120206160b090105010816050603 75
    0x40c2030200c140d00c03411603658040303540b10906800804850f444000714000e809230703141c8440c0602041c40090406050b2080c0415640e03991424490302002190b002422940d502d80c906000882e00e0307110125010040c000e50f2594600b440c000507240c40080300b0b80e1240b5065a0718043d0031001071111304420083c88603030400c031410408107081c20380055295007402002e20b1411405102004d14180c4c80140160101c8407030f196100110740c20b072900c001c0d08a50342c2c01662540d00040386010103022065610404c001400200701d2007540c46106068400d0b031803529940d50391405441140500d031191280391300300c0c0c0d000000e00f51088138002e6000c650780c2001802c002c4003507101c0203009140203403001180d00000720384180f040d04010001407071400b48020301800885545201e5548218413500d0590840080340108545c1c0da80196040c0f001c800842c44c0e4029134a04084000c080103407024078240d4030740030012403600d40c04903401011000c0c1441903103005141c0024001c10340e1000344107480c05003d6a0842 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 535133192 1250 535131942 535131973
    0x1806041e0518070f060c111f0e04090c0905310309080c01141e13030b07090807061107080d0c0c0f0807030b04020103090b0718090203010f0b0c 63
    0x603400c44400c2100250a2922280d80a9084206040800340e40e0119030100a5442045000401e0340c1951503c2d05040b910351400c9281100325411441e440120688505000110111003c05419803640c40388100a000c005100485691003c042d1003080c0748a001d10100b43c95810954100d03090050030000c080644180490f1310b0074654035014031195200c04002490707400050680603129110180210f00c21920000c0c0a4450758500ba84a030311010428064202c0d00301c1c4404048582e40b161141c3c1d44220a80c145210815404100c0d02c804104d0080790302148690103413803d99aa00c4010510103042c8601590100c59540038002213110724070011408160030300644000e881c00343c44141c0b00071504d18200c01204941e41101c1c13222969000d04110745000050310f10202ca400524429080d01d807400100c0250142c05000381020800358241710302998064051039800c40c000c07030141c0f1115203400462060740300078803605080500340501404036030111802400c44003182c004440b10b40c84500d462 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 535134442 1250 535133192 535133231
    0x207120f02180703060f05090402010e060706020a0512010b09130b0f1809070501081312030906090b0103020307081204030b28060509180a060b060c010207060605130902180604 77
    0x515082c040c240301c80650140503100150085814822165003040c0200d00c42c10402840a41000806070a0700503d84620086a00c442d402070703070a550707440203580050150ba04c04403c0081c40090701c00002100c58640047c3c074020000141800c0c4103e0740162000e0240443c008451790180f025800d001c46039650500d096009146145080403d14007a00e1260400e400e5a11040c1402050b00811039411401c801103807440d50300a81c2090030002c1d00300b0480042035500402445945400c0305a0b06100184001d075049a208030202c071206515480c3e15910703440380d075103441c2078108140424030016800010556110002c0700546a0b654401c8610401010300c1c29201e43c1c48607520030301800181044591035034408104d04000c2400500340202d669143d0301c410000d01215918031450038550703944403c40e003940c0000d8000395150801414180004d120720b1280368442d10040d17400344408000380c0a014038044c0c00401e140b0803c81c511002140c8008003c014903840365807200c0c145400c100300d085 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 535135692 1250 535134442 535134469
    0x902060409020a080910050103080a110c060c011b03020406092603070c03050d020703170d0b1207060e040b0306040209150d061b0c0b0a0c0903080a020303190b010207120f02 76
    0x1522500c41c2807401003141404101003171b510344141007100510205107680100c40c90904076150603610401100e40080c100801d60302c805521900c0010003812010054000c414a894a0ba0440041c141c200106400701d00c40c61042c140400e545400400900c081c1040e060a2a904000d4141c50390701d1200006040d42e00c1070340e0803a40c07050b000f002801400070410070341800b29481d00040040340d046840310200c221088000348101c4400046540f594003064005107180c003c0a440d59030241d5210441c1034443d40140274400c00625038120281141c60320f801149148800038010b000140c07a56000c0c085c03000b00041c45040ca0750703c60751250160351150f40e03503030101a0040c4400078200c0c070841c0800c412119440b06100130444d40007003182c0803508040342c03d500f05902e01d40010700c10004080564100c2d0143d44040c0161358003086608000da0040029481100103070981c8a000c0e880364003180464950448003801640b203803400b44910b070b1681c2030490b00c40e0701401d90a45440c42e0340d4001744600440a1 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 535136942 1250 535135692 535135697
    0xc060204030602250320010b12010c030c23030709030f0b060916090e100e010f060810030302060a2711120d0c0f2603150a05060304060902060409020a 66
    0xd00e103204c034010340d848880180b0780d00e00300300901140d61402003250100d001c050401c0c49641c020361010360425445014140806800703a41c000311000f048500034038802c4019000300b0705041c500302d445d0b4814069808548c40f044080031101c81c0000c480744403500010001e40a01c003200e6000700228000b01100d400b054410281c510750b502e00402441071a24001d040d181c1e884176200c04424000c0c2c2c2000070002a50010440034035a65100c0c80000c40303020066014004100b942c9001081d03400b01040c081040d40c0e01500c6840300d0391150804008100c1180c44080d0041c3c01880200d160104190092055000c070a0001d141e500d1082d0990006840c4540c81180c2200c0080c19003451402c00343c402942200350800544400042420058641c51140034014501c102e4640032100b0001c405d1028a0301c0c603400142c80d4100e4201d0000c2030415070060702d00c80c2ca1a40d1a0b04000341525200d6103a200396000036110740d003103480703554826002e40052a0209c0e801042400003007043e9036640701401030080302c2d5 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 535138192 1250 535136942 535136947
    0x3100914031903062c06030304090e100b01020303011203082a0d0b01051c09080f030106020f0c09042004060b130f12030509190509070512100608010b07030c060204030602 75
    0x200d40541200c98a5114105030516921007803502c4d010503405d11004000f400741007000c0d03a611000a030642c0f08603007006100c6403900c0140300041d0030008142170b80075920801002001e405200580ea02e0000340f16407101c1100c90511040003d01c907285a0390401a13541c009080526490b01040500c0b041e40030003401883c0105100350a21081d01903101c0c0e003013080c20f00610304602101c2004160510600c0d6040040d11080d45008004000d0f084644654140c000c0c1522541c49903002516035050b00c0e1000c01512500020700518507045400718000e90384a10f8433182c0b038001950b0001403041c001c4140d0742c480d03910140003490076211002840110040c02010644030b08140c2808403480c070f10b4101000648201c112500080d410008856914500b02d44036940e10301c07406404801d5200d2038014541004010003480344a0f6003000290415044411680445956000d0100030861162298100280d0283c0041001502c41c10090000a01070314140c020440300e600c41d00b0690b403050f4002c65a0781e500 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 535139442 1250 535138192 535138237
    0x19140706050a0c0c0507050d0314070c05090f06060a0e0316060305091006080c091803040305010507110c0f01050a050f1602010207242001051f0f050310091403 70
    0x3c0c41803011201c4603041c20080d00909844d45642ea400034000c59001e03171000000c500130300d4000d401c0c4401d1500c40d6031141d0360b641c41d50b282218980465216190060040c0000704440c0c1c509403008500c100c0011740254100b0500340c804582c6079000c1c1840035018090222141040d00400c1c5003540070340083c1c1c90104140c2401500c8520304002108075540c0b140c580b0106210950010849c41d41000b01100c0300300958541e001d040b103602802c0f0002c111644800240082080b0042d00302d9840358500b41c492218804003000038a171502c600700d50142d0b00007524080c0b54480d41c018005040112001d2500500380b62000d0035040850307012000d20040742c80034642002c00c66904010080c040c0408031264008140c4024414000d45c14420004080c810042c4110880540c0312100008200c4540001e00040c01c01242031400320540c081d80c00c8003035183d1480032800d0380c601d040304000c589014004080800969400350010106408219110b19161003020380885003000640001c1e00440b0310081044c07807 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 535140692 1250 535139442 535139461
    0xe01051e07020c15030a15030b0708011406030403031a0303040602070e01171e0319080414070f0909050703120906030c02071404021c1a0f0f03031914070605 69
    0x10000d1142045622440d00d410f96500d41c0410610740c050104095034981d140d400300c0002070480a1702400307100720121000000d201240d8a0781d801182c0030b49903400e050741c071074928032400e901032280e240e00288100003140c0005d2190380172401107040e00b00005145944580001c2c1554802d03800800144d01404081c0880d4040c901c655004052501c2420182904105c1e01c0752500556001e51113050a01d03141d8401048080c03040f82c80b520080c6800fa005d40c90010406400b0800c03d940c01e8410709000b9002c076030407100014400081c0c49282c0340c0602030030b1030042e0080151070010002c40c0c05002d85100080007940c0c2d01c2241402907010340f18000403d06044000b4101c0e42100d4120b070456102401c01c120781c410481034100081c030181c80250381e9503450324204141200100d4024541361030058030002545107c05210f03036a6101311901c200c3c06040f10b0401110b001180e10103a411b8008000c8008113546c0d848907a184031445081682c01c80c0303c9a03046e0b017820f40048400f66010350315603040240c01079 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 535141942 1250 535140692 535140751
    0x71a040501031103042a0306021314030106030804090c0c06020c0106080f0c0d0201110f0f010e0f010b03070e130b04051e06072102040b03011805060102071d0a0e0105 73
    0x351180f6280c1036180517100c41c0e132009210f82c100b0001c960381000b5400151381d840841070165420003c25580c480d003440b202c04199156102e005006982e2051708629840c06000c3c290490780c004039910b041504101c02440280010480501405000c441c1c03500051000d002a002100008000194862030f00010794100068031118201075007140c00b4010003981c40c901c11089850f02803a00d101c6021800c180c80349014480380d00c0e0542840b5001031144d040708150003035801c949211040e02e0780c0c55281e046443c240c44c0e0041c0d0080e410f4200b100103104134038000f400d8a40c0314080715420032440e0015260302d6014141a201958541c2007682101c041108190fa18030903552460020308561038648401010444407a215506822486c411455610150380517a40645401040e1a5513035035500c9a03981144181c41c0d5080c001d60920700018480d40c00401d9040c01c540c080c2c03503c41c0c0c0300414486000c898280060082c51030325035030f10701034401c2c100900ca501c2c8268006c2c824000b28402c000d20710007145 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 535143192 1250 535141942 535141961
    0x60c0a0b090c01110a120302091c0215040305060c210703270803040201110f0706021006090e03030c070303060306020d050402030106150e131103070f030507080c1b071a04050103 78
    0x4060b00f41107400340050500446034000c001180e0320155242e04074007a108000742564008a01059190300030ae82d0085c918043d40b00b110b101e8480d0600c01c0041009009520016000b90010000944000c440500134140e9030402d007074001d4140004404801e2040007920035400080c0d0b562141807001c01c0d1400c0c01d10850105c0c0c0c0d40421b1441455840f650a1301c0010030007070400041c07a03070106000034100000900c495401042e103c410303441e02c2000f946d5201c51a04805900d041c284002450300a9215000d00c0c0b10590020714503550f0740069600e880d5011000c11070405945800000c0814000e01c0508003050503c480070a80c0e003480e004160a580301c5810810740f58103880000900d56400400d041140c4500b5914003401d40409450300006085070040e42e0300d00e0384c000041002055100c0b810038450301c103d0b1000c209648414400302c034400c404640c0103049403001c06c070201c03045618450585090340c10104130760b039154468881003481c01060710703259500c0b00041010700c515070705402210300c0c4 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 535144442 1250 535143192 535143197
    0x6060a0302150d11031e060a0e0f090a06060b280f140403080a0305040302101802040504051606030b1804020d020f0d14101b0f0e060c0a0b090c01 64
    0x2224215000116031400360036030365425000020b040c18a01c80107400441c04800c560001301d8413442c00743c0030386840c01200d1061448010440000800b1490403541840903240007031604180c075030b1041c2c003108860f1000f80c0700e1000c6106808440002940300e00030400500212204107413968240c00180c0c2d44803508000e0007149a0300b44103809219544011590040c04191402c0c0400b80c00000c443c030520f22403500003400d0740c1c40001d86e00c218650036422042c0100d06c82e9007111401d0401d01c441c0011502001c0300603601c0200c0101503000f41c641034002a400c18000c90a540e0326917070b00d00c000c9017a01c4d031f90f500c1180800d494960078a005c2c03610107014404062050f900d10b00a141c150300190b1041c0004030028840e42d640200d0300556154118420441c81c1e000041040c95442050141d43e40c111545440001d142070401039807190328129440c001c103031002d880703500c4504080c9006407140c0101142050f0441000e00604a4190081144048ca50301441c500003090510803e039509040c81100359606 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 535145692 1250 535144442 535144459
    0x803041a06100f031a060f03060108060904030903121e02070e070e01020304090911190806010b070213090512070f050601060e28050a0905071106130b0c07060c110606 73
    0x1140c002a0f6554162803600e000141c840d14901840c406103508004150000804103031b04110305503410040d4040c010907203600e503803607840c0c200304968110304507801000144407800820008900d098440c18640142c1480d8003900d81c14010341044180d1100300c4e800583c003021041200310280b004507508100c081c940300200036000300c0083d44c0c038400d0b40b188140c0340366190207600034880c075402c0c80010000c0040c40d110b03240d0b4031130284013840300103401950101e01030240006070000402c5d040310740031507014003d002441061181880101143c6405840c1405540a1144175030070610003012120311407441c80341200000c0c1045850000160483c5080c00b00352546440741d540c1e2440c02c0e001040a9100c2040e560314161025552881070f580b107117800240b45900031648840b203400c154495059940c0b04606450716800d0142d403a4019900840b4800b0843c1e10200410180110b082e0b0026030451480c1c908041d0b0341e91001281d904100c2c03040000c001081d5121103c00074007103d43c1003541215141c0 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 535146942 1250 535145692 535145719
    0x212012004050d020105300916140f030c0406060203070c090605061909050301020304030908100605010e1207031e0201140304051203070c060e030c070f1d130803041a06 74
    0x44040383c075030342c001e81400408a030703094444045484200701043c104040040d0306194034031141000c1e600f510086040d000b029116208941c0481c0e14a044802c510190814071032800248182904540c407095014001d03800c0003e02c0d611180203030300091a86038002d50b0785500a040c500060150342d00640358031800c1c001c0410944ea5480140c0c0c4403480041c02040044c0d0b1602019107501c1e0851307100b10380550004c010031081c143c000180c41e0480d000441960000d20410503c00c003112000e000b42408650703c18940301380c03030401800b0400c0600000d0304848115459494064101031804820045014640c85c003008550740645248100078080a0490031820681c0d6040d4580c500d403840382c0880480030002401c44c51003903a41141513604141d0400034448a15542d640b80e50003140d140640d44248400052074205032040d28084528843d001d0044410b2600d21a0312903030082c02d220141c0c5001e08104c00031400b0203005600591145d1001c1d41954040e101c08120600e006192038070950501100d40c = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 535148192 1250 535146942 535146949
    0x7050f0f0c07062c0f01111009240c0f05130b07060501050301110c0d36080f0c01050910030207170705010605060712141306033e03060607021201200405 67
    0x141c03170380320034201080013040855076240380000c008900e005450400c403402c428814881c10906189180b580000504404810000180c504100030380001a070401d81c0f8240a03413103240503002c0401001d09220744550381d800401440d03003240c0d1081d04d450780ea0f83e0040103185000d210342110f0558902c8030f01d00700016080b600d52134015124102c000d20080168035801018001d200c0c1c4902c20380301802440001885041c0c11200d4040c0c041c0f4042031182118070b101210001503641007506050b92410719182e404003d00c079450304a50704001c1803540900c600b4000502550580d820000240c1c8851b0f10307060f4506001d4299080c56008a000342810031401000c504d40c9005201000f0042c00d00c0088004420030b0703c5000c0c812550545050a40c2d1040401c00e04e526030004466400745860020740841c40032400d111300000c55504c50201d46000c0e803511000301302d10004c0c40d0701840c01000c02d400c1c2409900070520403440a004060240d540392446c4450035441558600142d61480701141401d0920010 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 535149442 1250 535148192 535148209
    0x6010503011710020304030807020c011d01051b0106030503070b01060309080d020703090504020d1d0f1c02010608011d060a09080d020903030708130608070807050f0f0c07062c 77
    0xb00c407000310300704222040551080241e00300300140c20710115664500341c00c004200800c2604ca000c010b00401451003174542c82071400b80b10501001e51403600703c03000600199150f40c4600c0c50074001008002a00032102e40c01e00c00e078001540104083c41d030311135080c034003100d481805800032802e0619080900d008500540159403402400600050342d420f20343c00c00ba0364058031503102c40c0d40140001010711101640d600452008216480c00d900259190400603840d42c1d1030500c1ca000580c04802c81a8a511081850741c0c141d082500000070000c3c3c90344079142c03d488681c181c40f01007007110303110f861000c42d0422005500101c0824200042803850360b495a0134800c2c001c4040c803440c1c02184e00700941c0e5040c001c8901d5603502a4450713598400c4452114945141c502c035103000309040078001038241c0d00540103188181c00d07070340d10145809101c3e00d9204468100d0032020a80303202c00d110010303550000300501e0000d013041e6100c1543c0b000c00086680e9481e840d80582c00c0000160140c0c0301226140d0742c10 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 535150692 1250 535149442 535149449
    0x30106020a060b0f0a24050418021b06040615140d02101719050f0c2205100905040f090f120e0310020703181d06211608060601050301 59
    0x460055480741c00200c00814030300300240d02072501c22002403802c1e4008210160b04c01301c21a000500c041e400010b40307448c061032041e9410300c681d601c13800d100805945c3c000d000303c01c40d00461102402500200500c0c003d82110100c07851959107046d070706440703503080740c0318018190220800d02c1f040030f44010a4089807a200002e01490b00e4110000d1402d0041c290540c009010300d00c04d00d21031410b8084000c48000c051203c82110703150101003210030103020111840740d5030f0844003614000c484840d91055081c140d50300b0b8140000400040380b180e07200607049800050315501d40c804541010100300484213480a4148120700c0e003400b42000443c001c010061064210740900705444030140245c1f00100b4400e100e036414010f800c0074410ba06003560140003a00d02030390351007142014020510481d600e0b50300800b032a4508540100040003044520a588600084e107030058004030740c4c2211904a524000e01080340e0064655501c00301032240307a8100a160540051942c2d0411200190081c8010302 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 535151942 1250 535150692 535150703
    0x60f0305040c080307030903020f042708040b030c18100f05030901060f0806041712060607060b03010c0e190f0611010b0d030c03030b190b1602090108031905030106020a 74
    0x6002600380702d5120450b030018100c000075a0b039030300e030b242c0b600510a074444e0108074459078034646040c0c0c0310b080610540e20800140304007500400351090f101a2100d06422003129041c00800c004949010b46074051400303050310b029459152025062521007002c81c07140f8840c02041c003035048ac00e200b6071020840c0c0c1c0e680704605015036a9181da86201f400352546030003910504000807400074507401c0c0010710510850007401243c8401808400942082c8948114100d00c00d4203100403442da0300d41107004002207803040c5000190102440c011074250707510203040c5804220210040401420003854411014240401560740c0c00e00388031507410000054007070301c01003250b000c2d5200501e800c25403013032602d110000c003e461031910914004010043c07003041100002d040407035038080c4d420282c0c1e0b5280d410140030407c0c55411f0500c96805280d420800360594040741800184001d0385502034100d001c4d001c03c001956441e44078181c03210701c0281c1c0103007200c2042001c000410807d580480c120a00a5200 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 535153192 1250 535151942 535151951
    0x5031b040f0b0906190e04030206010f0e1501030203090a020d0b15041407080c0c010f0b0f100801030809060909090d1106090627031c0b01090b0301030f3e0a060f03 72
    0x105e41d4580c040415070400e02000c107240b03081c0f01c00c1c59000100035048810300700709004004d4550415074207407403060707400c05140603900040300c1c0998042e030003841d072105003a01202c0107080140c00003800111002c5040d900c0c0b20640f000d01c5144002c3c01000c840400c0140c0c0c0c02c0c02510004c0d8460042500010000c008008956012941025095041b1021656084001e029280c070107071183d801003032010721740c0d442181d0b501c24005c503c0c00c00c510a40310002e00b0b40c5404185070b01c3c40e100d1150302d920140c00980e01030b40c10070650780f4581c0c60841141c05001d40381d00400c010b40c0c0030381d00603209000c2154460000e03401202045180303803000414907489038401020a602c1505d94440c420b1100c01004150000e00010800d264420328403c49001d400316015402c1c4240040c0f030300192036100d003a00482038010701c10001071020406010045003d5441760051103010004040301001c10b40c0440c00c0101101c519910450307010001180b00300842e0b2003150781a603050315040d00906030014034a100300505455 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 535154442 1250 535153192 535153219
    0x80c0312070b062409180702100e01020415082205030315150a0f090f0f060e030c0d0b0a0609020405062703010e0c01090b120105061305031b040f0b0906 67
    0x10b4480d218078007401e84904c00704098414001905540000c081580545152940c42c0c4036100140b900c54010103268003d400000310680c20040a048221011151503400b0400004c02c8803010b0103c0da01c2c7c070000e0351610f5850800404a214030105d45026918032841801c1c0440030800100c1140c0c1c000100c60b151002c0000c1100200f5034240c0c0704203601801810100c1c1100016030000032086520690b55210a1390755224004e8400c2c0d4115805070824800b0500310500199006080040d01440c00408403101441d508001403041c40744444102c0c0c01311f6540c0c043c010f41d40d02c0c0d4080d200180195080a609050401c004607050b030203000b207401522005491490281c400a0701607400400d03010b0000d02002d000c01c034006594850104206000070001d48000071044640c0043c0c800d00d102500311700c0e006919040030000e4580100c07409000001c0003000000760303942c0800c0704d10885c51140c0e01880e0016030910400089400d0aa0201511424800044041c0d0740c2c2070f45440e4064021190f00c042c0012 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 535155692 1250 535154442 535154449
    0x604050c04150215010f0e07080f1609180c08090111071101050d090b01170304080c0906032503110d05060c030a09080c0a0632071116080c0312070b06 66
    0x2104844c1d0081200f4140081140809000000240d40444804038456111102e0841742107904a40320340c0d000126201040c1030803200159145242e0207454058038040c1c540b440c5150042c44003084102e115613480703410b84250b8201441c183e0080720100204481d1200b08040c0d0110301c02d0240051002c90b0307014840b146a030040055942c07070207120138200003d4065142c5401e00c880c0038003600020240765640880040e600204803070a555900010b8402450498180a605107014001070b515004d1590601001305180c0c907844101640c1d000801d1405142d428500038004580c4001030203803100c5050100450030000380542c101208c0c40c5a241da981c0d8083c4448002c03c07035410000c01005000a506445010010b40e400c1c0050040408018143d811500e00804450644580109440301c0c94030f829404001030506521040034109001c00d003440c508810b0405d050362034181d160500d240003d00011904000c0048501015401010301d41c05600d00440d143c001c0c000010610580f00c000a02c141d03d = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 535156942 1250 535155692 535155703
    0x50f0a0c060231050a090203062d010e0405010e060108041103010c0c0c090203010509070e031501080a120503060105071e020a0b3708040303110a02030c060604050c041502 75
    0x6410510464440102509080e203e00008001d1a150062000120480b070400141c85040b640d00500c80e410b0b0501c0e00c2c2e03c0c070000c3e420041c141c95002031010b404901122414040c2900704900043d891101112100054003800310202c41c43d00651070203005000300e1002d0020160040c900f400c1c800d0301d9941d00d01d0310350040406010ad150b055400c1c80c12040802d6003104200700b0f942d10961501003043d8039280c0b1a812400244144c1d41d02c0340c0c40c540403518a500615621000c1e5102130150752981500da00c40000aa030280d00413042e560240e07640310103110307490307102070000e40b15860000d185041c5480000c0142c010f0000c040d05503050790001000b0119550b00f0405001e40c09031102582640d2820382e4842c40c0c201c2d4014440c8605401c85602e1405e201405500d180c419040342400701c0d040c00d070411500f4100060084041c140c0d581c8003001c285403582c01911b440c020b154001c50751440306034015030030200003074800383c0164100389c188400c0300a40b40544d401e41e0110100d100c0c0725080c1c0a0308070b2420 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 535158192 1250 535156942 535156967
    0xf0a030606060e03120c03160c03022e0305010305070635010302030d02070503100b18010803090f030f030901030e120403030201150e07080109020901050903010e0102041502030a050f0a 81
    0xc0349015000282c0507002091a00c101c03a00b103058822031200c0c189070545034882c00c0c1c1a0311107504200540d144280861480c84000c0303004080103c4915104e9010030f5196034a06c800750444000d038800080c03903c948031500118107046207800e00c103651442d543c0581c3d5404501520080c481506001646d00492544000008804061080c1c81c0003658114190f030341028081a40079005019403000420700004040c0126031340a03005010b45111201d0b01c0b00240380714614190702582e100450250300161103211030281a603040a196901550702c100185e00450100b040d00a03000117070b0002e12110b003c0290b0f20003400a090100f45490028504e038180900c4031f440302c3c3e01074004100441411f50540c444040600900b40c055203098407aa88502280b20445440c0c00040103003006004440d03564014025a81d0103041550900200f41d00107825180300081101641c1e60111301000040e08442a0ba50500c20b0390024620f01b01300b0681c0141680726940040c0005503000076041195440303101d0002d0351 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 535159442 1250 535158192 535158203
    0x2122410110c04150503240105060f0403060207061e0b181015020d0f08130f150204031401060b0901020a0f051903020a03090b03011404094b020603060f0a03 69
    0x1004ca500142e9410a11402100d020388a60740400c4605000d08040720040c601c4903400c400942e10b0b000c10000a544100d81c0344c1c450395024800080002c0b058009800c03803a203d400d020400200200901110109200c3c201d20b03c181051000004c40c0c031004241410195801514070160396105191104420310742d0240d0010307080000251301d103e5003c41d0988505843d0754072441481081e102c121620780e400e541e5640021324540c55180000c030361001081041c3d1003502e14100da404860f85010413a00668001d40300c40d0482d5410b4000e0768400e200d00d00c0070303200e07114032241056043c2c80001d60710408100e0080c199030441600b603042c0242084160742c035550190411a010680c0c0c0340080d25003586071790444c0460313200100031400400c501c1c2641d043c3d83e04002c0d0582c0c1d02080d881044042d2100100136144046000c0c1d1115420482407541c50380c140341c60300c89030203100701d0811000c4480c801701548100000c49082032401650f03844201c1e5004030082b500c0c500450070b00400504280700e01d5000600 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 535160692 1250 535159442 535159451
    0x3050601080f010e0a02010905010e010c0b07020a0312020a0207050d060f050a0c0e010804031b0809040908040302120304030b04140c13150618090e0f0102122410110c04 74
    0x700707018001010305006034944001d010400c0042e2546559120072000240840c1c0107103000d04c0554806c400071074052505140850f2030f10181c0d100c9500c0703004240c45003c0140c0003003423a48107060f00010f0100c0180e50780d410451818450000007900c59105004083c0b084281c2044541400040d801180042454800400c810300b80034410500034440026030502107060380110000541c0280d44842c443c5d40c05466401c84400c059825803400612401c0440c0c00e4902403001c80d4198039a031250790403107880382d004584d8070307402c0d4010800b51494003414403803280c4c0108814000140e4403041d007500729600c0403000070040350b201c130a04d003410a001500742d0044a0103080001084141d04895030729007180111004075601e41c07004440440e464801d60180c04030125040020060f50351000c812881800151008900d101d00c00c01d082ea4042d50540514070311060030b20103d41c0c182d40380f4040c0200204c41c2240312a6100010803200f23000c070070705030050190b100c10040307454405010490042c00300907c2000b = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 535161942 1250 535160692 535160699
    0x10e0618100c050f06100b09090c09131107020a3c1509030b06060906070f170d0e0106061e0e0a0b04120c080a03020a1205040b04081b012c0a03050601 66
    0x1a6520310881e00204c54191b25100092200e143c0c2c01224030805024060340c2079681c2d081c14841240c0e1040c0c0d641508a000040c1c40003020b1078610515410703600c40076406075145064010400a0175403504080142c0908040007000390265088100c0b50030400000011404500e2981100c804100c0d0320418440844102262500340c1c41103c1c141a2807007401d0059881c1c07502020310409001d0003003041c0c0c0140c41001500041903850103500750041c4a1720300194107890004041d11980c00889074046026251041c0a4140d82c0a0180c240a400c81c1e28010700d0072081440410607003040032403070700b040c0480c2460b81440f685804414401801e852400710307076517540d200b520340c0410049000542d840803514101041906000c2030304146160198002c003054013458564505250444685200340300d010000003a4072414403002d40002d01e40e8502400729000507032070708180350b683e0903c0c0300c0c1040b803904141030b403134801038034400c02402c20403040040c102041400304003460741c19040030b01030740b10307131000003 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 535163192 1250 535161942 535161973
    0x270807090b1008150612090609151303030b04091e12020c0f01050309010b0402030115090e0c041e03020d122718200418021809191a010e0618100c05 65
    0x9409180789c181213801d40f048801000c0145c15090b1a40a913240300f013281400481c0c425003210141d2034000b8800100c0c40030325918505654140620002d11691307c00002c0c0034013800c200e5030a080607290001e000740c2d2000c140010402c0100081392418040007201052124109502000c851080500300315a20f5840e040400b81b610a1440d900001440309000803400ca08010215030003507811101580c205800c2c400122803031005800c200401e040082e40020150341e6200c01107030020b0290001103445441e07818000e001001070344140302d4018010f41240700c1c4c110141444001c880b4802a013003190110f440d03800004d003032400c0e51000ca07480342c85000b503800101c0b1802401194030780c0784807400c0c98280401c04400ea00403800c0444070030348180f0700b1548a040095682d6401201d852581800548070454801258050320001034040003024680d0220751704640b403120113200c00c0b00c2260504c0b03980240e8940c900040901d95004103890007042801a02912520280e241c2c807205640b2a883d051182 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 535164442 1250 535163192 535163203
    0xc01050403090810110d0b060d0c05040e0f0f04020907030e0a150b0102070b0f030c091e0a14031015051e090106030c050a270807090b100815061209 65
    0xf1045140582152035088000c6482205038003c5001404c6041c03a850140a0005042c14090943c2221082082e440e0b1042030b841096080318041c1c8a141d243d070f00b0f2500d00800031900400e40c031380b040a020140140a8410000d031984158100c8110845076280c0c40110041c0090782c600700480d1013001803034000c029580e043c1031001021024208900d400e0300c0c004a03585d0100c0c3c420101108403c101c801d050ba4115001540d104102d4030b90782c0e28203402c11001c04c80016102640d18001c402c400300e0328545240c01840c0030001d002070300498503840d101c6400262180b03c6440a004829038504140c0340d9115000140002032000400c80030103680f03106501c01204400c1040c2511410b03035440007081d0640039208061011000d9620f0a00f4165055420f403070116a0f071954a0005d00b091440011030542901c45001910341c3e00c0c050081d02e4a04003001040c0c3d28440c040c02c2c801c15035031f031a418181381d000a140360301051583c041540d11350030f400883c0300307803240207225070035100940c0c100908090700049 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 535165692 1250 535164442 535164449
    0x150f09040e0d080106080c0906030a0e01140c1b0c041805010608060c0307030c0e030d030b010201140115050706020f040e0402010e0a0f0611031312020108010807031203110c0105040309 81
    0xd051112000034484262960390308216000454159001071010b9441000c0e040c3d888043d40030a9031034400240001403a6810407588100d6240d100d80442c00304000a029081d0340b250295001c10240c184420400b4040c028054400815550050380f9202035504126040088078040c0081201c0a1441d511040c0d070280c0c40380030344456090540000f064140014854881d60000010b02e055884600044001d080c000000000300550050290460754042c1b214400514041d100051000c820b6130000e425210b4240002440340d083c40010000300300b5000320341308280340768a401c0342d40e0380c100c0c178241000740104000c1201c010b8001c2808150580700c90b001d613000c5c034000d0302d0310b0503076994420420020b14558090300b083d0142e0000100555030107011318110440c00f00e030940b03040540840c1a060100142e46c0103408103030400c2103032425943c20500d584d014110b4403019056890440e2030b40541c18104880b10b8080550f540b140d032a0f2911034034250750200009030020b10080c141401d004042019a01 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 535166942 1250 535165692 535165699
    0x209061602091303082d0109050a0606020a0f0b040312090609020f09060a090c120e010b10090b040e06010309140c01120b03060f06190e01081203150d02150f09 70
    0x100400d14441c0144030070b12040383d145c1d84030f41050785c800c00e505140c1410740f4035450369101c440e080400c03442c001a2185000c0c10000c240042c0a142c01c400342400c1d181c0039070001003550001050000820040da030b00558940e0410410000c9807568a400c651038610903005824817450310310410108081d5800c40f42c4c4250003241c105551860100400400c00001c2e1840c42d07100e90a00340402102c415070f08200c855581c9420b02c2100b199545807142c0035140c821482c052280d5580701040b05500e070483c003c0c2000c0740c061810b8089207007801c03d04045442a4040e04c15604a100b000404030380c400d42100c00c8150340302c0b14274a1114101c1c2c030b4580c4c0d505d45100001d404103444500740558810709114100c81d0703001c014003d0040b9111030085280d089406014250800b0035910105401c03030317101e001d1100602c04190311500301c2d032408102c00c0c1003070010f24030503102440030421b110314205000e042c14000003080f81d0050410785540700190002031640d04c001192000420701000d031030864070207841c08000a4 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 535168192 1250 535166942 535166959
    0x31106070f0e0d050c031002070c120c1a090d060203070807030b06040b0306130e150105010c08030c130302100302310621090c080f1c050d0209061602 66
    0x4000685491559141d60340018960010240d072038500182a40940d074083ca00380c3c0c3c0260f2011010074100600000000c45c031580000f140f03800c2003004d4800304000c01014500e001050704c99928001200340f039100e00554803000e050b10b00c5080009108560503940024070034031441c80c0724501040a504201ca500001c18044400555264040e014040211800a200c14030340740c00d200800c081c0f50409844070341c101284070090300040d011842400c0401c600c1c50010322807256001503100c0f10300c80503009039040012481c00d40d00020b40f168103980d0801112000f00340c4401c40440d0800300360711154400303580010541600d46d1a960103034000d00103881e0120702c02c1066045403c00b0242011150205000c10302040ea040050500c0741e44a000c07220503902c2a200c10031780d00c040441c1590501d2a0607201400c01130001c20401e0381c104034640d401012007014214110590700a06000c0c0d1f41811a402844400213510340050351540c100d40840340002d00a03910b8000580c1c40e642074801d6040124000e6294 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 535169442 1250 535168192 535168201
    0x40e060f1b030a24030201021207110603040605250912020d1205042c011419080325030e01200613060c18050402090a180506130605090a051012031106 66
    0x140c0710b40c0095031b4040e00200b1005d208440041499072040100340c0b040110a0301e0300049681d114021406a401200b01181d02d0610302e4441e00030001241414400101074800000e00c1c0f5004604001100c0c00305108065000003400170075100b200c040c50050140c11200010003003250050090000e42c0e070310039142c1d6905003903865411007403a00c0a95030304060040304010850741940012100300503402800340c180208014081d4a251211500302c2ca009803c045444031600d104103281e09542801c0c00241a5529600e80780070b029004400b0256040003141e00403d154040c1c03201e030528070710107a0805c66070546880202c1c142400c2900300210340c11424030080b83e0085110301c414900d84400d840455402610384820880254002120355820100882c0005074150303182112181c120f00c001d10100300352801c0f008103d0602c444040405929282c0001413201351280d1001903031040201c50000390300c1c0c44e1009260b0407581c1c6540700200099441024601b015440180d0302440d04030308040351541d445 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 535170692 1250 535169442 535169501
    0x40c0f0503030a022a03100c0f050f07060b012a110105121810020c030a03050603160e04020a0305010c05040906151418030712020f040e060f1b030a 65
    0x183d0200400140d001c50412902c03000301c80098812540381410b81030501c2c0200b40481e040c08150b4005600e030315540c041d507040a03600007052071401c02d81403818610b031072400400318100c0c1c029004064203035a902c41d00d041d02640a4040180b40100205501803501481cac0c80c05481c7c7c3c900c4150460f0407020001400c502940100140d6000d41d02451080f8490b60750003146c1c518141d0f1300d441c0c4040300d204900607078101051030320007010810742c07002c06036542e505103200140c1901d00180605000e0f40c0f0045650180304c1254141c2c0017658214610a107045d00e481c0001804001d01c3c4c0c20190aa5217070104101140760414010402c9810120040c0200b83c0d80d0000c525040980c0d51401c008110740303804001c2405515070080070340d00362495800f50224007080c0032038a040c4c4560807441184000041502c01d500d40b10b8541003911808640910050540114040c0c44000c0940480701c0c1401d91400700c0ca9054104100c0780300d0300e12640d041501c0740303403a26001e405095021800d0041600c2c00c0c084102020 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 535171942 1250 535170692 535170697
    0xb0111030c0303011e03200f030a08090103150308032508090a03080901021b0105100819021c17030f07030c090b0a050c011b030b01051815040806040c0f050303 70
    0x32801da000c0e41c2144c0c6081803c40091483c03d01c104502c81d0f0708840800010010b8074581328a138801c1d0006142a840c031000d00c8001c40c4c2510b8106c6c0b00350b002070704000009100d001221070b840c40a19010446440304c1100060314407580d00010141180442000300d0999006941d1107082c0620749038140040810710700b5a070007507054910500d5900154440b501203070103119095081840c1d6000145070a050000c4449076090715012103160703175154424080340808840e01d00c0c000e4114031010b40008407280a901d81101c00d030303150003402451285c05851400c1039030207905100940004400110b16031100e88030b0300560080721410034100c0594040f840140c840d11507840e00007119150345171100e007010603090040e04811445c2d0b04001c0308200b245103c02080c01007064140d40700c609d8401003000b00c14003409641012419504125040c0124510303d811044070b5001d601082d2482c00d804404410101581d1140e60814203081c41340c0000d0000f00020960070004481d80e0710314656000d0b40700d02c00c1503160b1 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 535173192 1250 535171942 535171957
    0x1021905070e060d050d08010f080d02031902030418020901030515010e040504020f030109080d0501140607120327121b03030203060d051c020606030303040807140a080d0b011103 78
    0x1640802424030154403001c02c000c1d00010000c1180c405200240e40701d500d01440d4084107000100710800410070004000441400f030001c0d4400b510045505500095a82c0590a085401402c40300480c11600e4024404c8038003800d502ca141000c20800c500410010f94802c107000c40c0064a000c0c0092207128580b1150141c0398030503074075071200040101c100005000e02030801c0e68084149000d0504580c1c0912030340300264840c080d025190031407004c04204544051340300455684880b02100048c1d9905812203040c01d500200c404081c200d100c2c0304500820000e01034190080484c2d203040b00001c40f0790604e1401c14070a00512803107030788401c000c40c0c40b25281d0703802c4500c0c555010301c2000028000e80196034402c001a007100c6103240325486842c81c03c054840c16203040c042200b402c22405074140101644007505500952460410b0b80e00c0e424140b060b010081c00d000e5003001c0400d10300300d080c010440d03e140c0011100741c807402e141444d4001400e40c840018045131100103440608403010050300c0b240c = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 535174442 1250 535173192 535173203
    0x20303090c0a140607060b03191a070e0909010e030f18010e060f090d022e0801062f06180115030c0b07080c0a0302030403030306080f100e070f1202010219 68
    0x7840c41a070501441e50002d050485601d0789850316024144c0302048a803401e03203414200b01c210b00c9c050b410801a000024440e00c0180f031401e0301009241c030303000307101c111600a00b503545950580d140503d413401861300c550322200c14003000a841d4940d0003a04045c080203c041d00500300708900680043d603130010140304198011070207000c080060112071028050450300503000c0358810a1030790000700b4120114281c481250f250180004041d0200d40c45090408103030b04094405505160000e0100213071003603845000080c00000d8015102901d16994510300d034501203803006d0a00044050b50898892072503281785d860050300302c0d01c180700d0034001c40403280c00240300012103046c1074018105038452003003655103c40412814022800030406c0c100d0b074500a0f400703075441d14110710f002011b50710540d0003e07a0941c060801000d0304071020030807404502070b0400c00071704d102034080e2403410107855501c540313010b045901000400c888030400241c01c040c800d03400c1c1c403068041c00080c4041e504000402501c0b = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 535175692 1250 535174442 535174469
    0x30c14120606060c03070b090105010321050d0b0406090e0f37020109031703040b0c04050102100c020c18010918170306010e0a09020705430e0403020303090c0a 70
    0x180340c00c00f0001040744d1441c41c0c1c192483c081041d201c240301c07410165207a0546c1e80d507420041040c40b01c4041c05941c00c0c480752031000c502c9c850b296030007441801110700301030149540c1c1c0005117903075840342d202d60000d0403403060610900060289254075801c038540c1e04840b9000d0440c001000044a80400421042428044c015034040c1c203907000c0c40c0240d44400300c0c14055030041c088040395548070049005084907041980e00d10381880e010030161030241c13121881840078003040c0001da0300890b0b2515900c0040700002044d00c08648100d142c480e0031038006400c400e061080c034051107047c140c22070503a004600c083c41440600c2d0652240c5031000003020b03121483c001d80d503c89801075140155040181454581c8244249100140e00e801c00340d480500780d40d500150a10400506210b58007050140d13103404d40020784c09104801001c0c04086820036000e881c4403049240d60941c0f1100e00c081c0c00c0c59079041c0002d00d041d1038046e50303070340c02a960b45080380f14902e003903131052504030030034000e54800040c89c20 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 535176942 1250 535175692 535175701
    0x10801140c0415120204080f0a050106050414010506071506060c0605100f0b0a2a12021f0902060c0a080903061012120309060c02010501050f0d0f02010c0516030c141206 74
    0x11240a00202030121550b003c100c0094018020848446904070523005880764003100e02d4241d0844d155039001500440c207049000495034004012141120410303501c2650b902843d28041c900142003500c081c0d0701c649003010204d90303a50322000044020348100c00400880e207400c08503400b861200c0c4299071000d01611010f11042e4020750181c05c000d40182084480d2202c03207418403a08509002c01c0b0440441115495014440314240d00c81a0380245d001800304485131300341841c4180d038170400a450450300c1d18070714011501c45100710341505d148001614440718040c904080260b2200d03041611130301c5110045544944400141003c40d074003ca4038040140e10b650315590310981c2e0310b104074141a581c8140d00080345060040d21044c480716400054198145030400c00249074502201c0d0107407030060500300c00121801240803009409091403501411a40303412072401c84140792502000c040074600004109403001002c05030b42d2924101034500e16554280441120400c806012130791008c408603 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 535178192 1250 535176942 535176947
    0x40206070f020a170d031a03100e1002072a0806070c030306030807063e0f0403020a080a05010b0f0f010c0804080a15110702060409020901030212010801140c0415 71
    0x42080e40d1015111071043d0341d0784c103030740c8114240080f075000b025000010095900d69040c402c81404030044009a01c84011400100703a880021030002504a6079990b01195410020494195040c2c0d13a04400d40d030b03956903803519200040c80b081d4031010054406440d201c040040406070015a00c21200070312055a822008030b0b907500000f00180c0074990b40f81c2c0701002041c0000000d12043e801001e0209140c43c4140452440c503100b0707070585169180345108640b091900603000d40c140c1000e002d2007529080d184004c4081381c81039030f200940c0310403d5400010043e1380403403544483d90080000b0011560550240241c0f039400076140d6030b1041745101c1042c0746600804040710110300400b041401c043e03c42502e141340030301d882c40650b1150100880d01724404890300825507145000100b8604140680d40482c155004900810103da60042850980c503442681502c944281509481509581d02c9103014028040100504107030700c00d840003c1c0d2292a1401103030210340b4a480b030400c82e41c6408904 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 535179442 1250 535178192 535178213
    0x503030403032a020f0f070803070b090c0a0f1a040b12100e090106050f100906050a2703050c010c050723030d08070917070b070f0b191404020607 64
    0x2010014510340300b064411503401c1d148a6002e0f0b00e64000b000300c800e8084481e1325050820100c400103030701c008014000c1030004819a40d540e640308450249640310008010b00702001c414169402034012800091200344016494084a00a48100340a80b85000c258516481203000b4104003500400c10701111360305650a00f5400003100900305812a02c441003c003488000b5101000603a44800040c03040e440c000110030a641030480701110360400c8410007802d882d8007449550107200300410140205400341c81601803d4201080031100b1144075246881702d40c4080c0020340d96803184818030481540505442d00f03030140c116004103296450440f41c04115504540309104074952600620321944041002c8402003d00e42c489803450302d003d840c010408021544904084200308200c2144c07140089134800503612221040c9980e03030114108114001c4200c3c00c02824403100c03008001c800100c031440b01d000100540d6080c4000c0c03540d250034140b4281d0943d40030754881c80c10481140040c524040 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 535180692 1250 535179442 535179461
    0x15070201140705091903030e030705040506091501020f0708070311030303070c021903060207140d0f0903120e0d050601050108010b07020f040c030b030304080606041103150f03160b0403060c030504050303040303 92
    0x1c090340d0517490b00843c000d0401580c401c038003050025400ca0180d203800c1c00640007802041d0340c100010301c1c0200000b4550b45c8003512000c003001c0c0502c00c507603144e4070a001c40700c84d081e081411274024980d9038a050b030f900c031a07512003543c041000e2420f0400389d240210469008445654038514254803980801000e110b01891a000703003500e40c02c000000803420f0001d0a5a24003442a00255000444106040404400700b40080001d04401d00c103000381c00400190641b60401e4980c030851084003810b5650701c54607000b0310b50008812002204200000800505031ba41c280c0e10300c03c180e640c1c5c1c0413071030b440d0040b20b038000c1d8460340803204c001040c02d15600c00422601d162801242402038000820304581c800d40080c14250011400c112450130300b80610788000045001d50b13840c614003180d0001c04125490895480b90391402c071907d00e195400c00440700c00e03001c2d00c0f81880c0340070b645102c421b4850340135102c115212420400c603850110b00a02c0b5040c8101d03040400355140d580c80da60120010a000903 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 535181942 1250 535180692 535180699
    0xe03100515090709050a08011a0307060801090b0d0209040807140d0f05161209090b061206061803010501140a080303041205160501150915051f030b03010e1507020114070509 76
    0x2680040c10703540c6d01070040000c00c4184000500ca15001591107003251103072120300c0c003991101b0340c1000101e5000828604566400e000003c5070250700c0300040600c2040308010f54010b01e18400d100034000c400f4010026244501401110403201080042c1c55556641280001c00d01402404007098000c000410000c09403202e40200c0454554650825880903880c040008040c01c500340206c000f80c0c41440c21842c403c450003070801380e1144601c581300c900100591300409000c075404a4500c01c8400c1050360001c0100280000e68480154507499603019070707018804d00100f400010303110808403c890027280c208280718180c980a0405480a0384050402f03006d003907240c542180400e01c01e10a00c10040c2c0c0480f2038001f200d03e0702640200703548009514000949420200704810b58914211122410548154410301c0002c01402d03801420f14050851300365003000e1814041d45408210782c9000e5003001c030060300039102e455040b4225044c0d03001c1c000030301e40c0c00404640c28a0040014000008005 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 535183192 1250 535181942 535181957
    0x31303020a0c1721040b0f07021e01020c0117040b0c040b07060204090b01020d09151206080304031b08060c03060d080a0309150b012114070e031005150907 68
    0x16502c00100b404264054941d200d035001d2146181c00091001901c0040307004050f0008041445080c2100d2142e8443c080d030080b00011541c120010040c10b540c80950010008040c003180210b824000e05122080d4500500500f0000081580034007da1050041c07a000410515a52561441c40c4140080c3c81200401c1d0240000101998400010198240b2030b250140e200c0b0301d07000907641982c8c0b040074441d05540000f00c80d40f0000d0751004540003240c10a41404000003c0d07400d0544a02d019540001d994a040800125070480008000d100701ca101e1600d460307d03507a42c085548401e01d424001c11801c0e4028070b0108609400540246410485c01001d01140c400c241d0340b1500243d205480e9280072035110580f40041c4005050b0072040144003441c01d200310004400000c08004103c1d05000d4500c0c0d680900704903000d50b070780c07021401d01c01c80041a403050406441c0039105181d00c00b0928401c0c8100004940000b000340145805008032168078502e40c1d07620800c00c40140d40050220080200c00b = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 535184442 1250 535183192 535183213
    0xf0402070807030309050615090a050a110a0314150307060e010302191d0108090312040507050306100e0c18060a0e21010501170a0201050c100f1a0d0803130302 70
    0x201c000b0414507109031000a03000c44140740450424800606040400d0500020309080d5140c0943c4207502a0b2180d800041030f80d500c1d5502c0b0300600150042c0b01c507030000400d0203000c0c50b8040c0e00081682f000544985000da03203096013002c0960041d044150180c011660421080d8042c203890203407584141000340c2002980440328400c5042207031000e0000e58011440c407203041801d000100c0c0d0840038a454440c911740200c0382d80c0c2da8400d42c0c0f0400445600d50001805020043c0700000107010001c0c15650907007442020044101d19138060500002c4c0b200c004541d04851440c1250000c0c0d900300c84442001c4108800c22038550020300d81c036003d200b01d803907201d042642c0c0c0f0009500d881890450065842071245122400c40308160000043c4502c4d841c441074070344800244028a0b00e0f824a091a60b0b09410500341d0300b810740c2c8107201c4489038107000303c620307040045c5d421821030082c45100c1520103045d03880402201007080038010b450f040d81007004c29001c0c4c0c080905588994001d00440310306500 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 535185692 1250 535184442 535184453
    0x718020d09060203070f0206060319020a0f030b07110a051c030219030f0c051806070305070501050c03070311090d03050d021204050c040c020f030904021b0f0d02010b01021b0f040207 80
    0x5601e5001c07241594004100300304141c01028400c074443c2c0c2d92001700020700d03281d030120743d13034141002c1d401c0c40700040140c0e0a802c5541d1a13000e04003501e6a4803240004a039680b900010304802a581d101c00318040a1800d40180c4d00000c4501400350404011301003075034112442a640f442000d0306a003015002c018290f040004040d0707114242091b0340c1c0c000341100514001d030049a06440700041040f104203d15500d1403c1c080848055840407034a00e6511540c5103005ea0f01c0b80300380007000303042d9401d0504008080841d200a10320522103903c0600c003407060003400b40418030918030b060381d00200750b079400400f01c0e100700064545068016401403900300c40c0755001c40c0c940070403941200c2da940209452481030505001d40048582d260005201d20b18980c1100d039100d002d888806801a540807418138109050040c480003080d00d00703015a10701d000c0001e0940d4446500e2080a400740d824091501400c2d403000a14a050703c2e103408106805e0481002080210100d1107141a03205809100c94800300c0c8 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 535186942 1250 535185692 535185701
    0xb010c0807031106060a0b030c1b0d03060f240c11030f100f0b18040507050d03080403090b1c0209060d021b0f06040201170907080717061003050718020d 67
    0x5000e500ca012644444083e098509030740180034034050840000204051800320098070341001041e240e850300c42c80024004041421180c08202941c420100d078010955056400003040d181f444845030180d80e06e84000f00144440c1843c5000d00340840c2c5001c0410503c00d0219054a034403c1083d66542100300d40001e203454211400035a29422003440030221900d54402c80d200070280c5002484105c2210b400545d40881a421414030483d2a0001400b04102440f1110250030010301d52181c03881c0506004001140844d0100c0204508403030201d4100c0c90728094034152120400c16603039001c1300c41070080207508244072554000b0401e004800441010780050500e01600740d005c0003d901c00075102e02d2400e50021800d04894001c4018040540d074070241005074045400c14440d00c5032660100d85203400480d80c0949407500400c00302003040d00540d0410780103207045404481300b685411001d080140c81c5880001d2440d4003d220410007a60300c0c503070488405465400040c244459154400300f0344e03 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 535188192 1250 535186942 535186957
    0x180d020f06130f140a0302010c0609120c0201030c3608030f07020307061103031b0702090a0c02100b060304031107090203011401030c0503150f060c0a0f060c210b010c08 74
    0x3044a4400380142403c040c00c00c80181403200c1074144035a4400007080c101c0e140e900002c0e0402078002481300070300015070412807107130f588412500f01c402281580200803521448013240040c0c140301d100c030f0b902446082c80f94042c920345000051400f07014410703c601020081031207202080016030000f00c5403028000340240d442003a01c42da95484940c41014245111038000740c0500c40b1030445201040d000000b03407603001d01401002e004031128404d49403420f0091220081d07000100108200c4207450541203022540d656400326400d02070315004034402e84400400b40741e00802306000050100307106801c03400c82c04c150705054030300254460810f00d080e0381c0300760010114600502100c0410b5641845040505000c901e01103085040c2880d40802e21100312568500c502c001028140482d5281d008542d03011f210a801c85040025900c0c0510610401010a680251814600c01940342c00364000585841e5480340c03070b100e01180cad00440c00050000d8204107041229160031840010080d5004080300c = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 535189442 1250 535188192 535188217
    0x1e0304050a020f06030118090c08010504150e0f1c09120503070203120f030604090201110712061b020312071e0206100902090f04020c0a0f080304110105180d020f06 72
    0x740e1980180244072440101c400e00840c0100010440c0a000342c404043c81070161101040041c200d00300200400516001880ca651070170050000300b01201d4080c0302d540325082070078800503403001501030f00ca0580d030203202100c6e000300566610081292008240386140d6040809000740c5401c01010060360701031040300d00303a000080300015841d041007044400801804018030700032800c9248072840c040504500d002c0d0751a440344204680c060809600c15400300e604032040c00740da800140c110159840420340c2c5091801e488038160725201006010b56003107607002146003030305080205d03a076000000c1c252010440490b81c003440042c25100c005400d0b1216500402403800e01c081d500b01d205045a1203e02202d1040082c100c7c151038550465072141004c0302e0050310340b82c0750b046550070021914802403190b998840101c00704802d4002460145014241c6504000b1403400159554480c1400b1084034048910800503589048000c03034540e00d1014040c0050060b07201c001c288030750091802d0060 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 535190692 1250 535189442 535189453
    0xb1f08011a0307090e0a09062c0102040f0b1305040903052a06130c0e070f1202090d060504060207060903020c010e24130f0605030609061906051e030405 67
    0x48440000d11200290340707990900e03240d41065500034006003140c0c03192141320110746000445440b45a442402e9941e0001d00500460516441c0501040e10703442002d40d0381e500c0382c07048000d130b40c005109843c2a50704400c41c5106190804104401c2074100b46202c003009903800c1e1001c40c0c0c41d01c3c2d5001d6410000c0c8691105500d0b02d6001c3e60012540240540124050402d0b01c2201400c00c4002481c540025074104c0003102c84095060000c20512107030001c401191039a02407040803680b144203228001425a00e440b0424a00e411242c107030b2040842035a400345d0410091004101c1a82c0044d401501c1603074014540713240e0740c0d41e2400352450300301c00380c0150304038042c40881940c100181c1c2550705822216510a5503c07185058034081410660400380d44000c100102044980200c1c2e1002d001c59510312504180c0d5200001c10644c811134031140641c0c5d000000c20814207003850640514141c81712464011400d03c00d0032105070304808014503800c40304440c1900b604260340c0007140960301a402500 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 535191942 1250 535190692 535190699
    0x5031b0c0108130b040213020c15161701090f0603122f03030c18120307061104080d0c08040f0905010f060507030c11032d010c09050f040b1f0801 64
    0x41c44a60010002e001070500040c1c501c000407805040d0a920550441d00e50510700c10555211f4000c0c083c0541d8229203200f4584001647d280c0120054422900c5402945c8859450002100d948602c0182d6200303010340403006102c801a540c000c40c0d00c0001042d40014025501d8032201da0010038280d012002c202501401c0c0034004207034003102411074603204ca030b182202d0554203640d038912008001103600f400200c1e001358890301002200303640400081c5440441c0a2040300f00d074030fa600c0b0002c11504989410740030910b5850300300544003245d4074400605103410654005407440750900c40200c4881c0c0702000702003201450fa02d1000040c1030345d01c1000543d98180709001d03d0300002d0b50054810302c201440600c00103036101501c030b41542e500034000305507566500082494400d101451500340d40c3d610248021285030341e85007440d4a0344100092041166802058a001c1854058035070400007071040003c01d07041c0394000300d070465006082c0189880701d00b01404c8079402c482010100040c2c40301c0041 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 535193192 1250 535191942 535191947
    0x1051e0c0d0f0203040603020d06090606021501150e090702010e030d0c0936090506041103160509011e080a1124030a09060213080c1801081905031b0c01 67
    0x4440d07002940c28410a11105240040e40e21300891054108058000031036100880f00380d002640208142002880040e403508800394880d46007860340c0005e4606440001a00e000c00304840c034a28905c0e41781c0c00020a011001d108098400820000540d900d42035000c040c00d10400c0103041455889400090b2012030900060203a042540030300c00c130049641c1c4110500141e410b140c0121b42040100700468424150700d030f0080c0c402043c4c0504603000d400d04010520850440b01d80c0854030440c1611224501c107280ca140381a600c2c0a190303005055803005015200401d1f11040162200d2401070014a51740d5442c0303407410582d1681101d0582c40302c20060603038245110002462420f030992210329020000345c0396010700000303207607460340e90305d8024004c00c2c0801c83d8100c0748526640890b41040b1910742c000c40390b03140304040748140202c4100400c0f03808100b8080c00749059820b0340c009400045414944141e0f481030708501910a808108907004502c03503041e1510100020400c041c180c28983c90001 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 535194442 1250 535193192 535193203
    0x2010e0a0b0106030e0f071202011b08070c060c0b0402010302030604140405030a080f2208040504020712020d020a05070e04140d0f0e0d1e0c0b070b010320010801031101051e0c 77
    0x10710782170303600080c0a038000050100f001d0741520007403001c80d4030401caa400100d903007082e08940340e940680030152040604c2039820040948a00944003051280e54814088460310200d9130090130100b010408039005620a400443e001b003002040401d5a292002c0755250002040c0c0c1c0803900d076031000413101001c40e00801c001e0703882820580d68071128900341681341c0c120f50046074010240d01e00501d600d01000302c0c1100740c801506015100b15111300051a080e040c4c0700a0040038000b500c0750041140607580b001840c100102c0d0f0000c080d00703d017494141840d0703440307501900c11503100503e25684c80712000100301e040c074461195655060784807855480a81400001d0549502841100d0f940901148010b4060010074003155054040c44072681000710f580030854104001010b4000389038028480410441e605980c00344a040c00030b40d00e0ac00a50540107100e83c1654040788a0750010070200f542014510100001030600a252a9021220180340c20a404501a0f0448042031148000008200 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 535195692 1250 535194442 535194461
    0x90105010809060f09010627060801050129040b0a050a08010501050a05040312020703020316080105010b070507050907140307110d0f080c0705010608060109091421090102010e0a0b010603 82
    0x1d1600d00350500c1c401441d25107a00a01c2c2c00d48041a80c408601c500c01d0952004000b803060307805100328a540c0c50044c43c08032030100042c15034a41484000300c0c1614062050904850f0781b0182c0c2d42c0c00c00040c10002c09422418130910349040301c00c1c4030010710181c0d08001050000403030380d500b070354514035200050150081a0003071810009d046c030461007070710340282c1220207594009442d56441c51003d081245071480c16000203426000d002e441d181011912400d000540340490024482c81c3c0c2c17a810b2522a0307008055001c2e2450f44004802c2045003800f61026030000c540e417801180c0d810640456040d2540305440c41b5002400261420503110801e01002d42141c0440c50318280c040701046008081c88809404030300c1443c0009080c03030802100350300c03ca0041000c0c0b03081d0350003903a585043e000142003807001a42d002c2401054501d01b1580440e05407014164514030b490b45141107106503002d50032074107207141999603406000080c06020052085040d11441c000050ba605124004080c0c610582 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 535196942 1250 535195692 535195697
    0xb07050d0201020f03060f0301150f15020c030d1b06060e1e0415050907050a03060b03060106090303080f040c0803190e0301062103140a0905011404052d10020c09010501 74
    0x10b0b0b13101444840201ea400007012584d0f41c0a020785680028014564000c032150501c100710750005410644040020486682d42c40710482d0344001d850070b9840e030145150a0364103401030b182c5216218002c05050244805c0107142d01030292450b6541403c07130b00b03141c00c0504040301c54020081001250300d00c044016110610510032070074199950681004404a00c20009490f44001f60601d1b00400001c8001e24005088111595803400d284000b890b8000303990740203005550003c04c00c0b5001c3c0c528441280c2d403541d64a43d903540d540d00c59403042c00019004890003240d02d0700010351148100017a0130380c1901000c82c505521160000582904200e0729414001d1341407100c00c005041c3c000c200c0a620024044a9500088803441d00701d410099842408000550215484841d1980000b88601b0f43c1c1087e00c841d2116021040d10180754010351040c01e6000d0141079800402410398424180c480d984541c10100c001108800101c074000e85201c000c0060344a5041e600007450060621170044c0002e0 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 535198192 1250 535196942 535196947
    0x1062729092404051b0a09050405010503070315021e070812060108060d060b0301090b010611070f0f2106230105060f03130c0503010c08190c0e13090c0b07050d020102 73
    0x1000c10001055910a03158425513850000070b5444014a24550b841c3d80342206a654640400c0300c043c0c00d4450070f015540c0210720708070021505007400103038101980c0c1c010312510001c0602203c004c001e07602c16055217803c24002c25420040b21048809400000d00c40e4500039218003e205000d61003000084c00e5070304001080042c45025210fa285282080d904030070b003c21050a0040403d01400c900003005000c07070000310000511961200c0401842e000441c1035a2086940e080500341c400030a0003140b1a03101c3d0228100f14084100003000319043c0b0014681c03400c001c0b151965400c568610a021a503003044071802104200040c0c07006001d42801c84000d81882080d407861581804000c107107603100c10102c41d8520074001c1d0802c010b801010000c0c024130500c010181c1c01004002d040d240e00084115410105c0d182c0400d034000c001c40020140e4039001d252552004200e921820081c0f0400c07100d94509907140400c5100018030b001c1d0580c1d4490503035424451901510b0840801c10070011079105 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 535199442 1250 535198192 535198231
    0xb040506010e0409050c120607120203072019060204170106030f03051c050709031203020a08040b1e0f011703030108070e04020604080a05010b030f0106272909 70
    0xb250b07940b1445002582c0009504050b03213840d51070592000c155aa102c0d880e20244020104000394080c2300d0310807503958421134401100301c0e006038002540e126010801070900020b401c903091810102140c0d017031040340c80e4407030710b00c0600c8484100032000351080707034001805014080380000d401d00001a0a80200300052840d00d801e15050506e100c01001c001c800110200304660703045d054603030000281030800483c1408500580307192000e1100f20348d03460f18880950145406032003603840b10700007600c5031712050381e69954075031400600806a881d409011010490b0340801851000d00c41c164102d0614080d504103091034000300c2c0000c407609186da104200622501e0700225400007102c09804065400c0d455910006501d405250000e0415106001004c401d000054000d528800300580946050004c440c20607401d071491801105c1c402c0f501c544082503828099040c80501c04c001100c00550f0a40c80e011400051054140400091041c201c1d840e4492030a40b01c2c0350703000003511f03c100c130b2503042 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 535200692 1250 535199442 535199447
    0x50c040f0b090604050a080303040b1b0a0e1f0201051f0b120c04120f062901140d090b070314070906180b03010603090c0b0705030f07140316060b04050601 68
    0xa6a00512060a0001c82c0d1510142c44801c1610302508000b00400c00c0b858480030180e9403504215025100d0007000c40101c0d0a0702c0b48603d01283c81050418071914241019500380c80d0b501d428580250091604404060000030b0340c0aa880e42800b55400410503080c50b002d4004151150504410400c94400381088007207242d408a81070368841d10720301c0c80141d443e0072008203a8060b66201d000100e05120040d4200607210040010491150908200250340c2c070340c1c07040e244158036654081ca07000091650f0302d55070140000403c00c0001c07048403850805601a12400d640e0307030302e408940942e0000e09022040d9007501541440d01540740844002e85414a0010900b418610039001840506590024410701c640d101ca000b80070308050490b82c1c1d59440c603000300241103001080c0c9007004151800319400341190225019107801000442c100450356504c03c01d1039108034011181d12040e0b110540c02030f40d090010300068050042c030b115140602c0d01303080007078401c10005941b080c4e01c0c14040280c1d030ba8 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 535201942 1250 535200692 535200719
    0x10c0b090f0f0d1b03020703020a090e010e2806021c060806130c17102c0307020f04020c0f0d0305070801080105040b040305180418020301060f0b042c04050709050c04 73
    0x130b10700328000004016400e0a07030030300b521a0070194100020042c041626907a03a00005c1c4003110b410004c0040d4101c1c809500d80361025410000c1d40c4480d220b29561182071b18491a0700e485015010040c50040303254104401080d0b0f00040c0845251100c904104145e0180461a07000c0c0081c440075032071900c01c0d52503a07030078103a5000b02502410b400350445038451040040003000c2a1380c440030080b0240e1511541034019400c80c8440e4100d4040c203203410544400310039903507029805011b48245044020801000e500710407210b200501c202440d156401400b04520000310a4031b80b00060315052941004000d8001608110b02e81c1c1c0c181018030000072900910594030a0301850f203261200c0c500c1080c820317003c03641c9541980c02428060301c01d107610f41c00d0348041e4807603108a00030088255141191401d0078003900c240040f0407000d10003085800d200d030f01200c2d000c540d00044d00c1001e00760b070109911680030980c0c0070b80c0c05510015050011030801d12440c0c0d0448010351340c090620303140c99415001d10 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 535203192 1250 535201942 535201967
    0x230604030c0e070509032506020307380f040314030402060307120f0e1e06010501080103030c020a150809010e0106050d02010e1503310f060b010c0b090f0f0d 69
    0x10403040e0002d0f2035584580144d84944100030151038603090064040610111400071b6488801c0c40044001456400041119109a449904105504aa0303500d0782400d84d0352011900f10a040641a0303c1d4035050401c1c02482004001602d07840b5080608006101c1c0d0402609601c50072020400c2c440540d5884064a90080f200d2070100901140c0c02040b0000d003030b03010f990361000e070f041043c11a05203030f011071400b116580300c8400c0c24501c0e00281480303031307111820310a0740c0c003007a940401400070074810200f0241290000d8001134426130703100c1840005001080b103100c0000c008a013400300c006e000303002c1ca45000302e03844000c1c4070060502c0e00098115030004c42c028180706860000001d10b40714011091032801c0c062813040e0316450040200e1145941d450f00c004108110030f4003075008400074002c103184c401e400040b4805888800c0e80d0750f400600c0140c072a103060002038041d46000640410459101c0c01c45203000c2d010340b14004036030030720701004a83c80c0806c81c0c00c040c1a074002950300a040c000c42 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 535204442 1250 535203192 535203209
    0x1e0a06051e071e030c05100207020306090d080f25050405130902010e1c1a070810030308040f11030a05010e01150b090f060d150e010e1b03060307050a230604030c 71
    0x2d22407113280c155003030240c4980050650041c80840a031840c41a8007074440351340280d003640c940d0f54440750400c0e1038034030310388000010031000004500440950315103654030030070020250700801c526858001c2c0040000e1070240015900050a100504040d00310394000b40f0005800e10510310703aa4006044100b002015034007615103901c1d410700510f408403007810195040540210300544481e07a9245548049812901140071035011890400454914030b040741d03010780d20340d8410785480e0303036140d410b0142c3c0c841500c5010310700c0d000c00c02540e014030130981424070403000010640b400b180e0079402d40b603100700305900c00c4003001010050740705480c04481c030b28841101c880c50654580d20010f140d1307020350968002d02d40e00d059862000c84210540f17400a84034a031711200d00d9680c0c0c1d240710700c041f01d0048510700034030781600e00400010401038000d1030700660002c0903181301581300c10100e0007000c041d81c406c10030340600101100c2c0e800081d09041074460400e94100f131030f15046844040c442806441001c50 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 535205692 1250 535204442 535204493
    0xf182e0e07090f0b09040f110a0f0608060a03050d080601081803070204110412030819050403020a020906011b0308040c14010212030604020d0f0504060e03090f1e0a06051e07 76
    0x344240581c0c0b1a9400f44c000a144110782d00f85402c0600010140c80c500326185c60a4415001c0241380000a080440d41500802c401c000c0c00c1142c2122146c00c0600038a40090f5003a40c00710006206015a0f440c50000790358030090ba14000380010b100d01d401419846c00d00944034454101668080102c64000d5015640841c2031405580c810050384200e42c400b00400d202d18010801700356000d40c00c20b0240400c3c2c0058500c0310924111101100e1081d10b0081c056444525041c005060090603a0351181050411018904580d03480d00154a4103810803000164410101310410100603000c074090400014101c84039040000080e540740c4811031850172030075010000075215996501110255881074000380a20325080c200f08024050954040340c540d03080ca04000c0301000e000055889199008010414903440b0760300381700d070015800c1e40d69607080000720385181040d260055958000c0640c2d64070b042d5285500000e03466280709284c0005106c07281044010046002410319103000598403800c2368 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 535206942 1250 535205692 535205711
    0x3140423090a020901022832010b0906130f050a1d06090705011d0a140f0103050c0d0b1206130c060507030203030c0d020706060611010b06030f0f182e0e0709 69
    0x64030135202c447c002c00d89403204440c6121548034100c0c3e00000006003501d001000040b451250036100c2010344580c00014010002d4590f03e00301d040e8a190043c2c00c41c0c005020303d103c25944040d01c9045818000c0262a2200340702e2461841d114924041d10090181c001350034440d480301e885450300e218030350400c03a1042c84a07a502502c0307a00b1041c002c5000b04000e100d107540743c035056035082044a425210703601e04c0c00c01610300c1d40603004861195154400d203d1400c00c103905a9001003201c070052541014540da01d410400408000e558012918003448008200350b40c80d000046030683c0d00524108407003403041c400025000000d91b900840c41c00140e0b40c4a203440030003d00240142c0c00080c004a0902d2400100036402c07212948942c40c20600a01c841140441071280600c81a81e44881e9040300b1320005648040584080303401c581e070716103420305000c0c03a9010f640c60001e039817074508004c8800d0346507540f8411000c000b06840e044080f806210003100e180041d525941284030303801c1c4154179103032001d = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 535208192 1250 535206942 535207003
    0x150103090c090c0f03050c130302011d09040b01051c0f0803130206070b0108010b0f0d080a05040e0c0a0905041b08040503090a17010b010c0f03140423090a02090102 72
    0x103409001040c00c1000f400046001c002c00b0a4560f03004000480e1504002c00c40c8142070904442d0090300900155858500c4c6030300454142d030581c64110940a1658200000350f41d98038401d81c0114000c0b00d500d00654102000c00000103504000000c405000100c228009039180d00001172881e0060400e42d00d0380d44189943c000749400b01d80003035000e00001040303001c01c120601c599050303030b0b207a0000300310003881e500030b002c03480030402070441d40402c5160444002482e606c0c000e11050b4032910b003603420b00380e480c0144002c22200f900d14500d090b01c04690b04041c0c03a408842400240001c41d010721100c901440340007800c0300001e05034020080400001000d01000b0412181d4021029003010400c40d80c501d1014044c100031a0461650350801e0705a0b0050762080803240c1600303412400d00d185001c2240d800ba600c0581e08401441281402d200019010500158041350300d007080100100401c2214108034814200600700d00c0d03018818014a0107a03640000ca042c550240420308207994996a43c41 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 535209442 1250 535208192 535208213
    0x225150b0d080d020c0c0f1309061b050d0b0105090d060902040e0d1205011202010f0810120c05040510080304060c05010f051501020d26040812100f050915010309 71
    0x2e022054002000302401e4099401010448581d80c1503460814502c000c00000c243c02403c60782d4031121801d007801712040e0507031288218520940000509800c141c0b1031107009422080640c010410114002402220302c2c0104491000c007403a041f49050b003500c000480c1c030441c061000e0083c560b604456030864959501c080003c0308040704403000d2032040080240f1001c00e55602d41c0e005802c0400010f4a0301e1301008030010294141c5500d00d58032208074013150744c6000104903141d1240c214000240c030318010f80503003071a07600a01d80d50504505002c00d2005607900a8a60000000e240c1001c2004800200c21364041d911180340201d2034090f14140f060240c038490418800301880c01044c444407504a04440742a06000e0702901d0303107500102030a58180c0c090316000e08141920101d00d00804021410070b80c1e110707104802d81418420190056140c1200403624003038486203001c4140b0482440201a0f40100411110060540740c040d200c070b8074000d86c41a9550506440d080c4403020030564a55 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 535210692 1250 535209442 535209469
    0x4150608071526011502150601080601090e0f0711030c0703122001020403170c07060f0c08070b010f080102180d0201030e0a0c0e0f010e07110708010c030225150b 71
    0x103c80079200543d10401483c1c050038801d004807505035414540e00c243c0040f490306480b056808018184d07958440040d140c0c40c100402850401080d944007040410400038a20701030342d09244290194900341c00c0250403100c0c0c00154840321350040c80300d01c500c0e5000013100001d495000e4058004902c820400391004070300805c0a0b0705001e600f80e04140820815400b800490b402848404400180c050914000b446413036a21000e80d0001802401410b00500b049c0761148080e00d412501c20b02d25481d00203a540002d4001c03901e907548200100958943c51182d00b0103810154021403618a038103003644403040c3c1030b040c414041d40103507039214296802035000b0201c50704d0070301c1a10148811441c05031240441030050b10003070080b59012442600d851107246059484030b80040031182c0794044241c408a402c03600040803803044801c080344800081c012980480101d8130096119203001d40c510943c1941c4036484000300c0d2080101001281e01c40e414903210744036451002828021000114102418114 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 535211942 1250 535210692 535210727
    0x306071d0604030503070215070b0c07170706020a0806030313140328120306150c05010b0a15080c0c070b160c0308121003020619090503010e06041506080715 69
    0x2c0000038441c000c0f000f04103003442200c0a80c4600c8030790442e511640140c0602401d0301d50800b00180f0450410401004107d002d0890140240036444200340f5a5000080c05c07100641c01040e11540c1c250481c0d43c494000e0800c80c00b541c00e09920540003100340b9000e114110301d125000200510030b4505128904018148a0300d42400141c002d0140503084043c130001c8a040d00b4600a51000710312911038102541c2003200b01010b84540c0ca40304940850400c8020b8519560350b08103460282c5d01d11003080c005004150804042d00e070070b10400f61440d0b0000b840f50040450030000345c0002e1201044d03040603034001c842182d44564200032080400f208803071000740144000320000c0140046000030b0708050b5600d91071074a565071124590b011103000d622009410680600010a094194240c02240f00c200b42c03400100250380c0301d00003402c1d43c001d4880001180c1102c0c0921007404903410701007a401c4040f6205110311403604c4142d5a0381c0750540300e981002c1a0004411003041c3c4141c44a0f8220307070014 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 535213192 1250 535211942 535211947
    0x8070c0311060a14070315271b1218030c03120905010204090c0f02150c070c12030e0316150903080a090609170a02040209040b0604090e07140306071d06 67
    0x3164500014842c6913500c100002e4150009080b0314480d00512541062071508100d1052a2881d41800c0c03000681c40500844900c0b040e5022111092250841c240b000040d080c107540542078001c0c10724005007290b40491410041541004c00d14507141015182e0302d4902400c10340c116040031606134012280f03c80e800d80c2418989810310030705401510a07030f65030440c10030210196440c1a25410300082c5c0e420b0250700102d0380301500840b8820550703408000c0802d0039217003225903640c00080044582051038007041260703424080c19400340c000007103840e09400800c403220f007a0005001170701c12403007120203070389130989030303550703840c0b03c0c186c1803000b983d0000e881c640724a814070024013a10310b94000c160018071080000114128410340d10341008090001504280043d1f8080c00302030350140380842d402649038000d458140c0c4640d0700800040504d900001103002030104114145409680928805552444803454655012441c0ca4201d074440c10103a03c5d040034402203010040351900101d500c094013 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 535214442 1250 535213192 535213201
    0x15050906070c03080a1e05190f0e03030d050f0c03010305190638091005151e28080106080a060302031b01030f02042904080307060b1305010608070c031106 68
    0x610310701d00010b0711480d590302c42c84d01c008851038014514144401848c103821590a107000e0004488072250500d80346e01201c0c00b4a0202e4a558001014103403401d80c7c490400043d55102040c031600b1800304100c0a1540d49107403983d030340d903a4869120072002c021841b103080410526a200d460f5041920b04c44203506808170061000b2000750810303480c2030300d0f5042d610084526010440f01c0c464403038182d00c0040c0078280300907c8400198400090b800c2502080300c000490b13100e9020459041c80b02003c2303503a6514189030714402e50039141c41100c07104000758051a04a40201d0042d0541e4010301d007511203039943c0b82c42140500851342c00a5014041e1610b81e203038000c6503008034000080c081e2030a02103140100054006c030310551059032400c50100403441032400304004200607000181101d030703003015118140386046030b1042c2c008952081d901d004040c000d050134800d1860b11a01150104407035072400313001030001d240041c001400c200346120480308150240c007800140c0780740c032004c95010703140 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 535215692 1250 535214442 535214447
    0x8131e08060915070c03050903010e06070908070302011d0f0406030804051c11011b05060c03041401050702120f040902070f0b1006051c02041e0f15050906070c03080a 73
    0x4003401299403a010390000218090070008030014100b07881402e44015949196017201d0f100940c82048003002820010f0b400142d80901800044901d18400740025007000030004d000c40c806075000110a4020803010000751381c21002008011101e40c40011501032241e0000d80440c1ca03a130045640f144c5084008400c0c0a105000b4200b91101640c40c1e41207000804900d00b0030400e030740f00c01044e500307042031044101c0d4480c0e9030704d0f100c0b0104500d4281c0b00003a5a966a41040c50864140464010100400050046074030710114880340810003008603007881d00f002921402100f0010b103604000040f42d521003d4200c08490041240305021074550143d80707010f480340d5000c26006c0d80e84442a201042141002030035070710480351300342c42c0d2601d4400c20b0313803100802c200d060011990280d424400044e0b13841c40e01994004010541c0701c800e2101d03052122030108807002c2c0d0024034000c8402030513580f10713680190071031302c08102c11966a61508041e14218400d03a40d2a0801010b841012a44444258 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 535216942 1250 535215692 535215749
    0xb0a03020d1113090b06040903020102070b010801090302060604060e060111030c0f030d14010506031303030b280b0405030304030f0615032103090209160c120c030e1c0813 75
    0xa0080301d0388030404810b0606079003a074081040145c0b5201d21600491024074042d0300450380c0a120340005400c1c40720315280c50107181e0b0309074080281651640840c008060303040c02120303480700c81120100081401d08140c40b91000d4010041418015400400b01c25004100261441c07181000200ca85840c0d0740141142c890300300703140b0b43d0180e07070070702c4044c1d5001100014254140c1d08083c00b220b044d55500700900041e480c0c03084082d014565110b105241c5900c4d1120026a0a58042040c03405081160800384030035459600464590105100c00d1141303943c04022103040729004203481c085003030142031060080c003850641c613501d22039a500000802c176108844801c01441ca09582011445525040e0160f5080ba60000d40c0403440c00c0000300c3c0c406c42c410b9411403261039454041400307030315690b541c003180607081c1641c0041252880844109584102e419091a5054550600650740344030111100c0c0c9201030000d2540d403011414510340070201107200000e2002d1f100c0c00c459000c000c802600f07450b = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 535218192 1250 535216942 535216973
    0x9131205091e100807050d050103290f060f0604090609060612090b07210c052208061303050c0313170a0c0b0d0e161d09060a0b0a03020d 60
    0x2c40d412141c4120707045294400110140c400350020002ca002c41e0000c5840c0940200311000f445401d0110300407aa0003481054040d5120b0000404a41075208412920350070010b49410404040da0411115101d46807026400500558400004028001c000350b00350042d46c20501c4802e2030202d0000c0d8164541c1c1080048a40c00c0e111040070030b15501940c1c05440520f42c014007018400030104500522596000c40d00b148115880012500e0301e0b0704480a44582e10245c400042000c11900c0c43c800665140b015a0a289103170a01d0311450040c0243d00d81000410343c0d861104204445001d0500500c21a091107482009903a03846503121078001008810f4094502d00b050070040c200d20828000503940c24050308074a4884503d4038100b00121039602000600d6200f1b0f458030b0800340c00030700410840e0b807440e4a464105041c0c50420f00101c1c0400e2401c00804110898827080c000c14140219505402c8410340e0004541e0340450030201703203580501c0e80000d4100601e807150308244114007441c582c14 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 535219442 1250 535218192 535218199
    0x70303030e030d050f040218041a0601050f130905100303020c2106040b011811180a050301060e0103020301050604050103082512020109110102120d15030b0c03100b0a05090913120509 80
    0xc12024124440c02380300d04031801801c0c0e0b0006d410720540c00303440286195010005260151801035a41c6500515802c1802c9039101c003a4092024407402d4464002c5660003040703104200310742403a6450080d03442c406508550700138130a418464481302c3d0b10040710700031251068100ca00b581810f05e002000810b09128200d000441980340c80c07000029070241c001101c94901d142801e0000d044d0f107041d000d05202ca1140e034407241d6100d000400ea2000e004040081c441c0f51646007656255005042c02c0d01e2000301243e208924102c0103100080030b143c184d90805c4101400c512a4003107036003072005200e20003040584201c2c140b004001d0703040e605412031510103118812100c3c14421401c01680c0e5401d519202405001040c094005039800d82c1e403040140d2105025100300366035407a00c40c0e8a40100c1982e4150140354000200300916007140302e01c04c01410094041d034034024102c100140f150080c0c2008501c5601d0000c080790307103000b03609061518690030040d250305003058000064401e51184100900 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 535220692 1250 535219442 535219459
    0x31a0702101b050c010e0609010b041802150c03040b161b0311120c040e01020c0d0509060909090f10020d0b0306090d050f070503040311041805070303030e030d050f0402 74
    0x4014140b0b0140440e103008042018002001c0741c0025501e035082000d480010b50350701c003030002011004120740350041c10400c0000502110f08410b10048e40c0364034030000c3c80c43d0300c20345000005840c1c1e803400c80014041081ca06449070b8414200600317500c00d0358880c44400740007081d1042e4540210700705030111403160024400700781c8409880b0314103071514440500782d00049107088000d420542001d40203448084181c607a810440000941100c0d4081004e24060b03502048400441e80c08101204910036a0308005041c05610000a49180f007a4110507001d03d1020020802104040001c640d181d0120415661441000000b25009410907215101228100183e28100e420081030381400b8810387c8016100c401c1d241400cd50780baa0140d80e6040088004200030300200f0420b10240c00a144207891408241c02c2360700400056030074101c0906800003084013503000240c0c001a03504100c0340e050a004c964070030090742036402d50250b00ca90100302410801000b0300c1006812a0600c01c0d40708542825 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 535221942 1250 535220692 535220713
    0x306020315011b11060306120111030f09061302040c0c060507030e0c10021203070c02060406030222230103060f0308070501050c090102060f1315151502070915031a0702 74
    0x1003c0564290000e45045405450300d0300d2030822000440c1c1c0507901400d00306c800b0044901003070840c3d0b8400081071030118040107210310030b9040c0d04001e82268840008000710304055a03148811214400020301c180d0341e9519168040303005500f6907034010b4119404000728500880054090001e1088001040c0618040b8131003d2411191200081c40958020031140c0010f000000300c66001400341018808010404001070740d03044020400303000d00383d4016072500c0d0040e6909002c10101007544c2d421840078072052068440544003003086101107113190f1034001200c801600100020b80265070001220315010041c404400003c124151041008100c50b6640c0810344090307008840344c0c40d006810603004200c48842004039a50440c0d04180702100d0340b0300550740c40c016007a401030024000c07030311980c40010100203a80c07610014074120356554042440c1010094464001e80600760000e95142c0b0300d10340004062058402a642c40030f91030071082500d10074004c80500444440b401072041e40c5415 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 535223192 1250 535221942 535221977
    0x90504020307140306120106170c01140702190807060e030c03070e011206021c0c11070303050307050d06092409180305030403020f1c0210060e0a020310030602031501 73
    0x103030b2041c03015035150001d6041074071041010ba070010b018103621503201241c0078150310007845003c000f06403021054040540c0403081600309412941001e05000b118445002c82e08050411500c0d13043c0c0c1220340074103903004c0346c00142102100b41c1101c0c500384078508000c02c1441d0030510040d52424200d04448040f00782104140e07840c40c0324024030080321002401000041d8000c0b203060f410038403600015082c452400051070b81d18991441391622251951182817800740c011440900b00440f44020b082594210740f000381140c0300243c00d0204101c1c000601001110307540d03001e94090214000c0c18011800c10861344459082d41904910f00e26080c7c000004802e0098410f00c1d00e840628080d040d9100d80c1e54405a40e50740000344158190f00940d444281100f4080c03141c00206a60056640e0080d007015400a103170603a0b0307100c00b101440c50080140211420b00802e10703130007144020003503034a80e2070304050070550300c0c90b41c001441c0e40c1c000b00901c48074a10031000036041d003000303a076200700120107106103 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 535224442 1250 535223192 535223197
    0x30a022802061806061003200a080103141c0e030a0506012303030304050a3f0801150905040510050603040c080606060702090403030b060903030c07090b030d0228080307030c09050402 80
    0x140c80d0301804544507038102034001d0300420703090501c000000681240c23100d01320109034000500107001820f0500140b082110a4080224030102d84c4d0007001080c99960315103102c00e410b40000f40501c100d10b103500300d842e40c007000604070842d0304c08290307001075a50740400328040e4500d042500080194200d40360b03460400100780c034440c40c0c0081c01000c01401740d455051600184030001c440044010b58100010a01d6103007034030070410078900c2c1160b9190060402000a003041c0c1058501c10302442075151190b5001400c0e401340d8400310340c006000e4844c181030080309070381a409160805d00110800050141046000040b101071405596440c1e4410302044001e01c1795040c000e5200ca13109002c6000301e44a40d001c20b101381d078042d003241d160406c040002883c0da081280025120380c046102400248054041c121403040184c0c01030074503500d0984042c1d1140b070240e150440c1c031240501441507914032107142c1c41b6031941040505030b69084c07404e00200a0042c5032460008030710081000191410540708 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 535225692 1250 535224442 535224451
    0x10e0a0c0303030f110406110105090d0c1b0e161b030c060f11160c0512030a120b040504060c080f09030f090409060e0a020a1208030a022802061806 65
    0xc4400000d0035603a0503001001c0380c90b100214655510041c14034004c0143c024409001203031a100b035541041c001d11400d442e801807031440150844008102101d4001000b0782e12141d01826080048189003100c483c40c01143d400b101120154809205030900c04480703e6504168a55070030340405419084c04080100e0b0640050020300d1b0410b44802107407031a8458880d616003800b002c501d013200c80b007442d02d4541140015006401c21300c0644402c200311706c0100e400400007501d049210450003659103440c0e020f10f4104605100603601c0b4014108080d90003405508002401008142800d080460040c80485101c4012a103206c4c0421520070070b845545124000701001585001c0241d030b50340400fa0001c1c00038540191300c45900c1c100089160052411003025100107000d8841c807801080441140c0b903102217074801c114041c1750007061928040381d50207a030a10001daa0b440311142c3c031440740f00c0c20034002c48021150400090340d250307003c00e40d1070040c1c0f018070a00700844903070800c0c4c0d601c2d4071f030698 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 535226942 1250 535225692 535225703
    0x9050105030d052206080a0c02010e0a060e0a15020d0c0813110102030c0601090b040b0a1409040f1e020306150a03020d031806051905040e041b0f0314010e0a 69
    0x15080c01050301ca00010480030240000002111242c2c100c00c900344c6240f5040400803c90020400500c695180300c1c6252015141c80207003c48602e5044180d12424903042c043c200685501400e0151001005a0009564031000c124144103c33005168000e42118602c070408e1401e1030b0380c004c100c9115440c210f00400c1c403801c02c11103006040c1c2d2020050407003403099a055001c140070410001005101d468001e0007801400b19180d2010402c00049031080420707907111303280688081c481004400498600700005035416401c1c9d031102c5c01d01e5a2400601c80e00241038031081191440f180c041c3c4008080c08910940444449485140e14403806900c10303da1660028190002040540351410100383d80c1402402c01c0c3d40048054060314140902a410500200340b0000ba0200d04421841c0f2003282c003005450120304041c2041d203540800c56010b400980b100c45c01482c410342010f2100c940e0001071400081580780e00381c1c0c070b00e01404c02c90503901d0748003101d500c4c4c1242551244804590a0b6002e94000e = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 535228192 1250 535226942 535226953
    0x3050a0210141210091109040606050a080a05071b0302030706050a1109010518060c0d0905030a0c050609040b04020a180e0103030509011b0b0c0304050f011b05070f08070303060806010905010503 85
    0x15024a21507001c000c140c11306020f070540300010003011500c00c6040000740606810307a100362207003d110541e00c0715441202042420440764542561050b40180c1109403140007141a4868a000300c5946498404403003020040d0140036041640000040c60341034480d140038460f030350703a900030030044944160607614900e20411401d2910340c4240d00070078070003c035041143c612030302803030220388290403070481c50300f01d54840b5015403a01034202c11500000d00c001ca00825201c81c1c83e41d9500c8031042103218250080f0000f003041d1401d6030b030300d8108011101c8003030700c1151101c8268100405d111000f400801a200402070003090948640e17034594144c9405440721450548a9001100c0108004065406011884121900003510140c603980600000500079882e4102801e200741440010041c051003030389410a001400708908a1040c08440030b8203015482d02c00d0b500b01034818401144c001041540001888020180c0503442602a106100c08a618507070700d40c00c440c02100c1d07082c01003a03403544c480c = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 535229442 1250 535228192 535228207
    0x150c050d05090109030b040f021e0607031103191d03030903070e190c0323070e060d020409061e0b041d040c05120105180c1f11030403050a021014 64
    0x403402441d982c00d0624281c07280c1c0d5541d4a50501000055034112003940341840d028081d440d01404540105585551145920b01c0c03000000344188203040005041c01a6000e00c2e8030301a00071f0042c0c0d040314051aa0710381800c42c0d00a0028518030300a46903424210344603055a0640c10008103403040d41c44054020882c07a4200044c1044500008181110302d803403061010048111074011084141100e89001c101040740c41800d8031290707050f0380040340d020141e0040001e03640c0d11210255001c80c064411503030341e68102a10101a10071030f00044e05050070800d0001d0426030546c0a400c10300080f4420180c02c5032903c105025910842c031070b1060304015207400102c24503081e0502a0414402c2240c0038076243d950010035032031061203079000e500f40d668100f0800010400f689007400c1d03039104805810120545e4001407000015854444003896800317002003002405205400703462540d5400b04e0340c646075289491565000360201c2240a16000044401c440e400303404281d1000a2542510b801e2008 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 535230692 1250 535229442 535229447
    0x70506040b0c03040b041d0105012a0501020c0a050601080d020d0816020c090c0a031410030f0c240201062112020a08040611010b0a0e070f0908070e01150c050d 70
    0xc50340340202c80703010421000070400b07000f0b0f00070001801043c081c840f9140104141c2000c11405034420b0781402001110780300380c0e01300303400104030113500d00071100448080350604900a01907814000c0e000e200300803400043c440000f070340350304840700700080322540030790103400b00d8480c20400100f03c085042c0001007440194085c150b00300b045524411219403110030000240341580a450401d84494009008032119600d8054650410f45200e00da000f01c0c2881404400c14040038403000c0e016910303186a01e400c01c0000e4940034020009428110350ba18000826034500c050350b0010b81015601e0b01000061281c0450706c040d00f510010404034405080c41c0e2101c3c8103000d44c5031174401c11801034124250004407c407001e44041e2040b555500c440142071401c1c54210390a0029542c401d01800c4801c20080d100400070585c404440e20b0500b9a282002d44203490504050308901481d00500310003081440b10003003c0341c1210710000744c52035549a40c0000782d500e0280130101400b0b6400240b094440c160 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 535231942 1250 535230692 535230697
    0x513091a10050913080a08070c05010c120b040606021c140307020f100e0c0907020f120a0207230607081b1609150302061803071d0603030313021e10080103050f070506040b 75
    0x2300d01d4200001d807482c03107960745030271621540c0f511000303d8010203a080340b50182e4865940600811303201000400d08081001c4d55032003948814414030145080b02d40c050602c11011002c51480c0c20000711744908060001940710580411062610f100300c44001c403840d4841e0040d900110001c4014194161503e82440f0288030b0061480081d481440160000d00c80100149610b9014401480b900c074143e5100082c1404920b600201c102c01d00c1426299094441c00b441150003542203c43c150b0310003140c135141e485030058420410b00062400442c0000c86404601869a00300c0c50100c803160640380e4034400e080b83e1040c0c11442103040c004030148014281072000380340d40c0b900008c1e40c0d42c8040051001034075040c0710341c120a006907088406445480101c0a1032a0400c3c0110051425032400e0083e640003040c1e401c03c00b9201d0444800300229031640c0b06400b106c01d82011341440002ca0f014500035004e10420f100441c0d4a1064441e4811004e2003c101d080c25076000030480c900d0549080113403101078 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 535233192 1250 535231942 535231951
    0xc030b0f04080d270f11060a090e060a0e070207052b0605060402160c030203070b0906300103030e030c150a050705190b01030b010902040513091a10050913080a08 71
    0x305070413200040034513141c0c841290f82611a14007070320444120b14149201e0803400c0300f0240540d900744080e404044c0c1128038081070b200004113400b03003a0351759000230b1884001a80803001c442410001e000c05140e0200b14070701954420740c0c52120a000c60300c0200710010682004180c00f411558603003000a60b240c10080c2c11050007130000d410540d08421131a1203200000c4100c0310380354038060030800c509092203441c0003420808109802c142640d0003140a81c030030560000c0c85c10f6011000c841e24140b0580100c4544c00040707001c40100c0d0f03160b01d400b40c00340a40440c6144079209081c400303901c600d0500d095842c0d401e10b00b0100ca0408034003031020b459680200804030b6050042c400d203c081c03104c409551411032070261780004c2e800c1d45503082244801d001030304a5106180100800c0c885901c1d0324250140404130888001500c01440c141064076400e41100409089100424401c0600641500c042650401c95035541e21344c440095003060918621070082804005000c8034000340c1c020000b041e8031 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 535234442 1250 535233192 535233221
    0x20f1203040801110a1205040f12020706030b0f0a0302011823040b0a06020304060e0402120f160201090809090703200c100b0a0902251505130237030c030b0f04080d 72
    0x1101274a0b0380708000c0454440c807407001680040c208100c10f5905000741c1c41440020344034201c0710040c410200c0c44200342400040c0c144007100916990803c01004180010508180389458444003c2040500039100440302d074459810302502c1500d5140851891003160040e4004510b060f140540c181e4044842140d140e03030095003480031501d01c61740d103003469205201034070b5041000e01d4090b145c07101c151200b0172501e046a2410b44000002000e07d4100c4445410031510310a60760b903206c2c0210041e000f08044554040d90350302d4030003892200c600c0a000041c01520950b00d44603150f9086c4030480c1c0c1000000d40e07001007413110804c0044465030040c88150498441282003e064048980c03005201c1d0400300c074a181e03031020b1b0a6000d0190f100300c0d80c00c0000180035065040b150340015a141900c00c40b201c110700380600300e4a8092240b9031030528103515400c1000c884a0703490400c0f40004074070b48070588803203e14400190440c0c0044104610417640a4255030a020b20705400c48000d00701d18803c55070 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 535235692 1250 535234442 535234463
    0xe100911070512040e100b0a0e2b0b01150804200612090d0c050d0f092612090d1202030d05270c010c020d020f1203040801110a120504 59
    0xb18a09004088103034042c414940d0381d481c501083c2c802c0d820f0303000b0103101c408000c541091101c000410200c0f43c40c00b0300c40c07401025010441c000600ca90401c3d115147c01c01c1d180c0b40104251032003a2006d41445401030104403c1c90781d80702184498201d00900220000310400001800aa0107030310881c840192400c040420038228008183c80380d02c61498140b680e07896104200130b0801c20010000110b00c03500d418130307600c00b45940315a40e4410b401c16a00c00d0250a01244100354480c1100c0740041440e1110b01066030000718000ba0000c006c004c11210b07502034055100c00d40d1440d9070481d195504060900140030005440c1d840a250b9107520300b0b81107000410070f550f84d0100300d00625001c3e2040b00306182c0c00002d56066204111524428a4402d801c0010203c0d12682c0161a8a041c2030701964a00c03448099440001d140ca24400612644204410040d50380d005000000e80242c419640080000ba1004c0d01c1d060101d0180050304000a00d003501c1e08030340e16075583c10050308644620070b4480c = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 535236942 1250 535235692 535235707
    0x216030201120f0e032205090114030f100903081e0f1510030b0108060a05010806040e030d0e030307021e1f1803031a0409050d0c080d020310050a0e100911 68
    0x1025100f202904d100036902c041030790315202540840702c80d0203400740818400d1580c540408112950f1052081c4c218621230f450207601e49403410300020410103e8031041d10805134641c21000010031050000b41c00058004000490105545882c172100c41c5012024a0340780c0c0d5803060041e0900c00007080000c00c0c1e04000c2113824651111403050842d000d0b180c501003003194002d0001040100002c1c00d003880380d2480b14040040da43c0210045801c00c40940d004103101c1c10b0781104902d07500c15010101d030a649040d06200a244000c0041c40c0110a180c1c00c0d0381c0b0300d030049040e04801142501c03514080e500113540e4001a00c024404803186800b01910120f096841c100c2d9200b0301740d8160500781d000c643c86442c04c825400e44003c02e00000b19040310b041100513416180d45a558204800000900c01e1a07078442d014404c08030155409601c91780c000759560729091008080e02901485179a005512003031021400c81c12060b400c0c0e1158003011b141020b2079140c0110b0310b0150035a407240d03454405c1c3c01c00555 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 535238192 1250 535236942 535236971
    0x80a121101111e03060d060c050c060c0909010b072f03030d14090d0c060902030a020a030c09050106050306060d15090f06080f010b030a0f03030f02071110021603020112 74
    0x60110000703450b400d07443c1d0301801e10342108620f80d020011080342080013040301070b03074513108400441a0411400a8200c400d41c85c00d407400e00c140088403c9610403001041141b030803c1000b007a0b00e0b0420707110101141d07640c501d9561140603900005110049250300e2154101081d41003580d58807006484c10740b0390140002090540d48991421101c550f00ca00d082d011440411307000300d40006019000f000ca550480b1801031864000c00c3d0000d03c2c030b6488000705025998100540d1405907002803020a05641c0c034030740240001c206100781e80051f400c0000001e240e50192007a02d100f51406841c2e14946005048842d000346804882500c840100c120007085c01036180c440d001c210442813900080603070414102610384000c2e400b12841d03036030404540051544003c1a901c4400b0340c49138003004001c80c1490141c001c0c0201188108079248003207a1a41845000c21821340b012000796802d0310b0703458075040d0407138646d401000001c0901c1c1200790204010751140c01e8004d001d0980042c0040c00c40308a00300d9 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 535239442 1250 535238192 535238201
    0x31505010b0f03060d0c12061d0a020d08090907020d09080307030504120203070801020309012f04031b1509150801080c0d0303021b0f07060924050702130204180501080a121101 77
    0x260201f0680a040341c01041f940307201d00780350072445800041080008207030841c0d440c001140028021b14480300804101302c40b030000e40310a070600130203181c41490800300096442c1100300c120300009509407800280c101c8044220707264a034143d5941c074941420002070308408001d400c0c0481e054400c40d00001078101080c40030314003e070807c40c000f00b8110050344244180282540c000c0c511070307c203462106d00c2280d016040303904596024020068050701104035000c0f60720b5551214034486c41c142c44500040707a2003c07021003079a0607030b0010300c8004d4a804003241e41c00386c24046d80f1840c0c0d014200150151414041002c6120700c20700d409883c050110401200ca40b054498600386130b408401055800e5805200c0c000141015152140d031b000e1600038400046d080103000d00100810103840840b1080c030582c00c44141c2030700907290024030104c1400001c02035000740b04e80d400c50510300701a800948800d004085c12204450001c2c003051950740c40305614032003102040b1081c04100d604262030310400303004 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 535240692 1250 535239442 535239449
    0x9050f15060a0b0c06070f2d080108030304020a14040906110c070501080f150f0904031d01090f09320103060c260a0e07080106031505010b0f03060d0c 66
    0x62800440c1089024081007902c2600701544060052103c2c0c0b03a24540010000e5024a0919082c200c0d01c0301c203001515a03080c6200544031743c0e4002c084041783c6c000c0e1052001d031340140c2962580d15582e42c030202d01d900ca0005490007548040b00719010007030030603400c0c19180005402880054441500d59541c0c6c1215620b42661551460100d0340444206050104e40c0c001c03c82030801c205240b5040300c003581c19600c014141e0400c07800c251143c9440740c490101c40200c540d800341001d1094101400e02800b5200141500003200c1c0c0303c000c061000b075108800084c2201c5a85003815243c60801d45001d010f0020360301052061000310715500c40f01d0321158800d00d8140300d0020850300c9941542040e00c1035a1819440c00c00f4040241800e410256a040c000c074001030b840e29490302c094403511250800341c000808031800e0780c4a2080041041c100642c00041240d206503180100440408610425034000340703c0e0f40c51a010500500c010081104020340d40200002c040000c441c5c00b80d540e5946007503081d003 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 535241942 1250 535240692 535240723
    0x1110f01022107030903200c1018142416030f030606050702060d090302151f0f0608011502070803131404091709040e060103080a0f0509060d09050f 65
    0x4180b034001002400d400200f2494188484c540c5501c028001400c0901c0030440c6540700310400e081d070281400341044402009200d01030030244030b5001000712400200c4001b0030083c0400c0001c00a01260140c5030444c400b4001c0f0303000490706803803070011516000880f081e481c4104152007140c500d038111060f04900c03d486880c407840e010540241110070715049401484400c01003000580d49150a880e1100030160000c1080304051034101e007003210390740d216001805101c00b03001519540d041c410310000d80c40d00da8004100da907022040c1242885100b01000b290301c0c10300500a41940713010544400d400c900444102c42d50380d05480d41307194014482421181c9407240180001109034607024081e0382c003200c060180b1010f5440b1ba034800c42172421301c4000400001011795407501e483d04070b01c110441a00a0b5101581c0d01d060030041a0702c003002201c00150300c0020f200c1c1850003041074618110f006403541d42001c0c1859681d400401203d40140ca140c0701e0714800f6480c0d03050420010b800d4501c0c0c00c = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 535243192 1250 535241942 535241977
    0xc060206011e03330f1a0409110405060114030a05010510051801080604090804090509060907030c0510050c01021902010c02030a081f1d09070603180201110f0102 71
    0x58031401c5200d60390080d422540010b208100003060790b10480d41c000d48040120380e000500700b0700082c1c0c00329500c0c0740c1c400c4501d030410042020144803030b0b00a0f0a82201d1070b003001c3c44034650404020886207064802025403686006441e024100355100340c1d40090107040c254000c41c4034400c041a10381044510320403140d00d070b000501c81810010740c0010290064200b89046c07562442c514041c9441c9800003e0411aa54002038070a50703d540206003200d4014680c1c43d038035031321100e0340805007100b100c1245862058101040780710700c000800d20700302c80d0070494080016040404101d80e0a200111003420403109001c00d4508032401c2c4000c00811200e4140b245038240404000790a45081221400664100b072003006080343d0080040c50340125402c540027803250000d8249070940d6050b4210100c05048030544d00405029207603ca030041000b02d0844a0707540d50b50404405945640c41e45c2180711f0340d54080100194050004980040460020340d000d00907142c1c515822030304121004070015125 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 535244442 1250 535243192 535243199
    0x3150f040203070b042402010f020a030506280324020a0c0b0603011505090a0207210809010c140304030c020915120106050d080d02040f0b0c010f0614120106030c06020601 75
    0x3000510f009268a00209060900e411005020746c0c0ca52040310022003032200c0303100d00041c401e50160025210701001103480d803601c040028000c3c1021600c2c503004120b407a100b24080704c454012034840002c6418104200c80c21540e94400f00c1e41000081030384d09454003420101805603001504500d40c03199140e10078171919080c070500280c40074020702d005e40d1425988442140c2e021500009640040d94504159141c01c501e0600030311415a01034038034029560b00c414500708504a4000f40d081c079994000964440d100341d00d01303d030100110380c0041800044420031500c443c1000d5030b4407d009041c40754010b04990007042c0548412944480e2030301c4200d46107191407600c200c0001d004107a01008011380da0070000408c24003100c4e40ea01402413100802c160304005480d8040724040c000612618110f96030740c0c8040710b07594220030007400c000d508101c40560611120b120388001c55510800210f604855072042c40700c4505081910034032035413600c2011002c01d4403c032070301005000d20b600401e2190314 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 535245692 1250 535244442 535244449
    0x90409121b051e10090b07091a03040321050106120e030702033c06061c050c04051909080901030c08071202030705220608010b09061803150f0402 64
    0x81c40004082002080500368045070001030f000c02031a0352054151880071980c0f55981c503015682070b00a0882c0e0501103480100514082c099010300810b441c1c8140890301c070f2601815a0101b8098410409000d10000b408284144045001c0c52a180c100d802c0000783d2204400c00c1c2c81003600031401098402217000b0b03604415100c3c031012400c415003e18101140381d40069100c1f030308450440c00410300240c00740c40b00600c43c4140d80038024910241c2448804246405e80c40d4441100d216203d048a00642c1213862002100c1c20386d810341c040050000d0035a0b1204000041501810b14003140031240c4c1440405c4007184116060346002c0e03000300351101d029000040c2503c402407a0740082107000c1d002e2054594000d94400461a07a001015849507a007200469060258041410a00019140001041c107201005005807034a590b10f0034842c2e038a074072450201e842000007064009008001525130030b2200348a664648900900340d841c581c0c8043c03184146a0419214400f60b00c5864062204514 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 535246942 1250 535245692 535245707
    0x4090e0f120906390f1005010b0d0c05090d03090905220f0302190819050c0a02061e0703170a05040f0206070212160807080102090a050d050309040912 66
    0x441984101c1c60002c0c400d020558900030107064034419019400181500c0b40da1401480c0320010b00c0200349485407951003240c0d69060b08112074412402000f84501d0301d1103040c09614144ca082a05c580d20300f0800006038002010054246c5080000502200c64107507906811400f105000350380d0b2113080707400c0c00f030280104e820142004c1c8020007a02d41602e80c201848205014076900240b45402511407400d06074100903c1c032921252140d454440a0100161003006e0040c0e45800201c00035845a2400c0a54952203000c1404000364091301d00e00c0014517046004003035807440760300e84000510001c0b426002d076401194003107000c501d207048810103c03151119900c5e40801d0294061019040c01d031900c00540d01003d070045d00034880000d0020a5440c0d07204000000000041210358001102240c2e001d4025a0b002d107070f8880c001c076000021034400c14020390303885e40340091200500601c0d003800c00030403441070201260940428843c2c10310070744c0c4a00c10001c21901a20003900000c07511000208103d = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 535248192 1250 535246942 535246963
    0x2100e030601140306040b0a0905061617061f020312070804030f020c090105090901090f03020c010e0301050103020603060111070f0b04030c080615190e131110051c0204090e0f 77
    0x400203451441113540000e0846c0e001034000c0c0459509450341e20040c0081c100d0014058a14411389052101c80c40e11585c54201c0030307441303654440214041118140c003000c82642d5590307102c10395002e41c0020034004135414a5400c83c0e03004413450310409805518418500300d0704100480c00304010041415040110f50303c8602c00c3e0b01c003a080c1103c03072000103030800006008580c001ca04040c005400c078002540305041e01500306042420310b1030189402990b80040402c0140028280786900b440360505010781070503a54024603407030940d61041c004550655004400305541d1203420000078000607540300171006019114900e960352821804c3c91270388e80344140d2120741164003110400c80b816180e110800c0300320600301d07418600c03299060303100c2c05542d00680200900c00c1071802031005400c0d0440e02c04440905c255030110340780105108121342c4482084242001c034004100c11582080781c4541208680d915a0005007003e07144d40b011811a414911f01d13010710341c07001161040320f00d02000501c00d00c = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 535249442 1250 535248192 535248209
    0x50706091407081f020304030e04020705100b040603110f0102161d150f0f0a0f0e0a0c080c0d0e01060e04060c1103041401050c030915070b01060f2a02100e030601 71
    0xc1e40551911603e204c90304804980031540c00310204082601c15a03200001100090065483d4460b40c200940c40b668140066140c0034600007004e1441d090900a913030031a500040c180002c0a2210180448401d5008005045000d000300d4080301308103805541d800b4021034007480c1080b618150305454900805800d25504070206032425406a50391604030050780015200c41d81d02c020001c0200f45140d40c103402200a15642000116190903130303006881c45094105014070690126600580d0001019503603254003100400400814105e60380014079190100320000483c43d41c1c454402100110aa4007245c6076901c80c0d900c00080c590003065502144081c0d409140391904e0301003040d04000314800f9550611501280552028070280240e0f03182c2074014000c145889501d101c40105070b030000c0300403500800c3c01c1c000070807601e100e42000400c110340d90301c400c8000d002400854003a4030a0306034400c40750703144250101c0181c5444241c090005e0150311903060f00b010101c1090705214050308407046 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 535250692 1250 535249442 535249453
    0x92e080c09090606130902030117070f050d0305032203030209030d03060b0d090c0509090c0a0603020f03040f14010e0c010908030c0303150a0f1e05061204020f0105070609140708 78
    0x1c141d5644542c041d0010011610301d696441c01210000002c8003035444031070a144080b000140d1380300c00e400d400081d640040143d400d8641c81d20500205244580100c1d41c215920400c10400203010303400464100fa084074250f071a01280d1b010f550030f114003c0c1380480c0065000710f080141400c0c00c00c2035009248403070606206490500522840742c2c000e1031819618507440382d1222041c083d8410004c409003c0140c41070b1544e10704040b16581d00c50b211081d45000e000105e40001d0001d200744203580c10f0140b500b050f030f45143c40719120304805540c600825141c950502c1281c0d12110388c244122031040180002134411000d20600140078040c0c0340d44118244d80040040c44008180402241d901c98170580080307030940041400b00d9200314803500401c58030320b1848004900d4541500d600340c044000040002102500c85040c81101d025070f01903688404d181e07101150040c81d0115182c1c44800041c0f4009003880c010741c070b4401c2501c13045c10090b41c211f034a00e0102c10003010103000740005010014003d12 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 535251798 1106 535250692 535250707
    0x603060406180f111216030807081215040b120c04151505070519021e131e0e0604080304031d040e0309100207081002092e080c 56
    0x188501240b034005c2c044150006a559604880944030f01003107480c6a882d4600794002000456890300c0500ca40982d03900c918548511500000d0314400d1003480003024081110001c050703440c016200c0410070304441e00300003848041c0480940340060046402e0700070100002141d001a00755000d00b00c1040505030f4010007914001e40900d007502d11001040c100f54903400510540290042550480032000004400c41e0000004000d4a00543d410398020040300305c03498440c024000b00c84400c0042e4032a00da9109098041d01ca0070003c150f90f08013500c44113128000100300408000c10102c90700300380403402c1c50000969102510a00c54031450b200d00d0390702e80e0840480e00340240c20855961007c0744c070020301c0c01d0844401d8009891841489040480a5031110072020b0f044040c0d015081c00e259030030600404d03100800c8030f00410042000600400b0f0950280c085000e80e0424030205 = true := by decide +kernel

theorem cover : BRFrame.Cov 535071942 535251798 := by
  have h0 := BRFrame.cov_init 535071942
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535071942 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535071942 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535071942 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535071942 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535071942 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535071942 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535071942 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535071942 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535071942 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535071942 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535071942 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535071942 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535071942 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535071942 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535071942 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535071942 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535071942 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535071942 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535071942 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535071942 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535071942 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535071942 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535071942 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535071942 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535071942 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535071942 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535071942 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535071942 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535071942 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535071942 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535071942 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535071942 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535071942 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535071942 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535071942 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535071942 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535071942 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535071942 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535071942 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535071942 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535071942 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535071942 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535071942 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535071942 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535071942 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535071942 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535071942 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535071942 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535071942 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535071942 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535071942 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535071942 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535071942 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535071942 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535071942 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535071942 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535071942 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535071942 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535071942 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535071942 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535071942 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535071942 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535071942 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535071942 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535071942 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535071942 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535071942 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535071942 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535071942 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535071942 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535071942 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535071942 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535071942 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535071942 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535071942 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535071942 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535071942 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535071942 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535071942 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535071942 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535071942 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535071942 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535071942 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535071942 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535071942 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535071942 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535071942 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535071942 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535071942 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535071942 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535071942 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535071942 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535071942 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535071942 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535071942 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535071942 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535071942 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535071942 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535071942 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535071942 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535071942 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535071942 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535071942 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535071942 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535071942 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535071942 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535071942 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535071942 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535071942 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535071942 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535071942 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535071942 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535071942 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535071942 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535071942 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535071942 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535071942 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535071942 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535071942 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535071942 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535071942 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535071942 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535071942 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535071942 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535071942 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535071942 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535071942 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535071942 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535071942 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535071942 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535071942 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535071942 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535071942 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535071942 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535071942 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535071942 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535071942 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535071942 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535071942 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535071942 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535071942 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535071942 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535071942 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535071942 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 535071942 ≤ n) (h2 : n < 535251798) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
