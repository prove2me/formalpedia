-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2065
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T05:34:49.526897+00:00
-- url     : https://prove2.me/submissions/9ecdcfee-e3b0-493b-8b60-b3ca6eab42f7

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 371223021 ≤ n < 371402877 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 371224271 1250 371223021 371223023
    0xb0901180b0f04050f031b1c0c0b090310090c0b09060c070b2203050c0103020304240b0103050603190605061c0c0e0c0c280501150e06041107 62
    0x2410440041480321980034000100304410445445601c4900d61034036036005400b88a006842c0e100c43e500e9a45000220310300820940404030070107a40c420240160303000d40320340b2000800c1202d01d9400002d0b00c1c0e46415001081038400707040d141c1241500b01818214280d002442040c01e0101a10210320020621400c843e50210096078414003800407d550740103d0088600314000d0242c00117005040703500034401001c106011030b0320300f108036000c0a2955820700000d00380345e01171034203812107500940c001d40d00603000b10304620306100c062140005404c040c5844042c03e5032103411440003945c140c041c00e07401003421400341c540c0d50b000450704984402036250142c1810340b40d80211b115034031096800c0707000b05a040d680e1400c001d081d007021000007c0c140f04011071701404c0c0d000a90060800001d650b6092040c00c054085c42c000e01301e016140e001764459102252285009420000d80b0901c40d06041c4101c8001c4106050300c0c06906100045004000c0c0707000e036003031003541501c00d14408200c5960f0303 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 371225521 1250 371224271 371224277
    0xc030a030b0103060308131a0408030414030c030f0f212d0f03010e0a050402090406091b0617060a0501120908040302220f110307030c0c2f03070b0901 66
    0x101c903070341e0040700030f4440380d031019000110000d01001940718a403400c005982500301000880d98011300c1c0268213128500c2803071350316001800705102060800c6ea85c2c00e00b03020010101c82c990414100000d0412400c031010b1002c0e50300081c0c01c00d40007103003804030b1130112983e054070005040c007490104c1c2c0140301ea208808111210840c07102c03c5000600146101300c94070b44411601c422944051400d00d6200f80104903285034250000781c00c8031100d00405110360340c0900b102c411a106c5035200b00161220721f9046a050042c40c00c65040350740c1d690389080090000355100b103d036040c4050003a1890b44040d101c80e0084150703a0b401d02150b40c0080100700c2c0c01d205100006012411402d20300c895008540009601000541d821520b410702d504502c24000101d20b010808810a81100070444600e4414247c40c51000c0c000200c01c1c90180d400f01b6200076003402c000406107842e9a5248019101c40d20001d5440c1600f901c4581c980321706a104bc4c0c2076038007074005110281c1050b01100b620b0091814035410 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 371226771 1250 371225521 371225531
    0x106030e15040320060702070501020c0a0302060405060711040f02031e040809010f14030702030c0f0a0c030809030c0909100c05040302030715050c010c030f0c0302070210080c0f0301120c06050c030a03 88
    0x4c9003000030032501040c0c1d40941030300c1403070070110402521a031b49032284a005100c0d25290664611700061003600301c0b0f0b030041203d850103241400384040f0741c022080c103075001c001407205075029440f5409190070341d008030341d8016a2032500d801c2c401c1d41e01d402410101142c00c4007504100c001018801110600314003401c0120119001c06002c8440070807501e94415003581c01300900c08142d80010261541001c44000d586140c0c130022881d5540d1001c1c20005803841e00c07180c004001050681d0700030310034030401038140c44e1319403031600c04110342040995460307405620001080e032402025104000f040c06051404d60710346440c40c0c00007560703107034075000d850460f081c440582c4508034010303000c0715902c1249100912801142900140c001c00d00e01c40c101494030b08210448407000d100f8800c03604040d6000742904a10514100110b070080d5000b042840260300400100d0484000100614000e290100c0d442008040c1b61400082034511035002400b8010240318a030f81a00c8040f040d120f14141f10300e40094 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 371228021 1250 371226771 371226797
    0xb0709090905250515071202031e091201091a060604030b1915090213140d0609031206080f0c060a09170304171c0e1c1b0602060106030e150403 63
    0x103600c1e4202d510045d40204001c8201c0200365540024114060103240034102201c0c1c690000d0b0780785e10078244201e230000e00754001c0c420107220000152034003040c0502688600300700060340d1400c458440c0c0c802c2e1822520001100540e1480818441d880030083d14502c4c10b05245584480f16100c0242646c5030203d424510340103051160390100b2403400d00050500082995420890029803202030009000404040c0104500d6500411003d442034080d04207074020080707840f01e0005004100d0210100900340d00742c4900404540100c1000e0507910000d020307c5e0070540000d920380040c031100e090042c0c10a110b200d420b075030003102c0c030812a44a03118601581007803450841c103621a0790810b01d0300b03d0110040d6021990001031004180c10340c244802600e00c0800740550f440b4040c81400c5a001c0300d2404034814228031420b0310004544903640415110300c402040a90555080c0c00c81001684010010010243e05009401507412010b0107803038042e82210f500011844010000740510650301000c40d = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 371229271 1250 371228021 371228083
    0xd050c010e0d1e0801050d060f0608062e0609180b1f030e06042a05040f20040e0c1c050703061d25090806040b0709090905 54
    0x1180100030070281c50161010100252026040021600e202d0002c80c820080e09030188008605844005141454107210344c0c0e0b420f00681031030182c1c120495218071000909542c01c000241c0a901d050404840030404002c45103461200e10000c460066503244003003003005d070001a010140d440d000f00700301e60010480710f080c001d04074000e0031f95040a0400c500c00640300a85540160303900850360b00b40507000c140e00286550b04400c1d01c02820b85030000070f050710000352a40a550b60782808090000c0030523501c2d00001c0450302100d0b44c00c031886407100601940469501e4040138104246a00d45003004e0401d5040240d07910010910f07000840c000410050380902624a5800c1c481c1840c0c080c000d41c6001000203010301100d00c14941040810b10102a405410801c418411b503c44a4000306042c00e0302c03c1100314129400c0c02d1000d1040040c404216040c050001e64441c3e4000e201d590810304001d41c000705842c4080e48881e10701898040700304001180418607401141c9110030040320040140c10070 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 371230521 1250 371229271 371229281
    0x80c0d2003010e04020a05030c010e0603060d4e1404050603090a0b010902270f090a0e160e072007080604120801030209040b1e190e0c030d050c01 64
    0x30102018010000003030004240007072912070340c402e0707407000400e43c1d0301e4003410b9403021915840c6010502d410581c03c81403c0100180da4029402000309034103050f0b5444007601600800213000403901c145035901248551611351501c40121200108080b181c25034110075901c20400d408420010141e00e0300c7c0b14444888251005402d00400c1c4907540d051403911141d0b20340005100300e4281d004100001012000c40c403d0740c06044c228034291182040802040404110103088103510408260955641c0d407202440d0602c150b04548001581200d00140c0314030304484046400d42040c1c1045050004080020115800c1a41130a1216450185c0002c18407181122610320410703200d07010002904105c009040c601039809021190200818090207c0d500f2109010103500481980e0104000880c0c150321154014450300c2c0214842482d2a50741074440015a14628080f02d280c20341c2d0300501c2c040c49481c02901c2e821004055007080e0308040b9031134441d00d844020078004045069170a0503429045 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 371231771 1250 371230521 371230571
    0x906050f1c090204050106210e3c160306050712020f040e011d06060d020904020d06031b180911060a03020714010504080301050402180d051c080c0d 65
    0x450640c10700110710388004040402e000d074400d41c05c1200003c0c1050007000701d10401c0c103441038407c41c0f079010081f0341c001815003034050300b14030f10852420b106440010621194142c2c0c1e510004003c3cac20200c1000c0c4074400e1b845440303541d1500f000c07148510b20702d548025041117950004011880760744004c41036405a03841c40c00c00050a0000440c601c012131800c0041003641e20281210300c4d01d988a0401c81001d440c1401c103d0407807588140814100d1502801030b000e20060700e800940303000c48843c085020b98000710040010961606030074820408024016091350384019141c0480c180b805180c030803008007002e0103100480c2d072a0341303c2c014022210000380e0344540107000d0558810324814001d00a40c040701041e103039007a0184080c1103524040c0103141c0a01e400c1541e903411a424007007000001e61042007001c0c0701039180d0f01d035043d564603100102c0c542640141c014084d034580d0762090168800980c14080b0410107070300200030203420307014140c5244201c0c40c0b0001809600032651203107000d0411780 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 371233021 1250 371231771 371231797
    0x2011107080d030c030b03100e03070606080c04060801020703080615090904110a120807030f09090f050a0b12060138180f030a0609021504030f0b090606010906050f 72
    0x10300814507100002c1e00254040c1c2d00e90742040301d0503010b075045048405c040c0c2c400da41a040384420640080c1180c0000400004000649140404540c0c031308084900319844100c158001c5c1c5076080300da280500c02c00c001801c0d1140250300e00380da01c0c0c5d402440b41030001c1449109079000740c42c00c1e60707544129082e540008409088411541464207000210f503820b01582c0c0c1c45949400c0c2d0218690f40003246801110307a1201c11181025142d82c0d003600c4981c800c000340010003d04880000364003070341c0d0081001c0b8601392440000c007401c0151480b0181d440010190380a41030744941c5d404c1d100d8002403954111885c2103202c880480035200b40340d086912458600c11000749541010b05458401c1d40104980d0450086459410441009105e0307442d12400c40745505400a0050310003040450704100b921030701c0202007428048080d007511040c0d4029130000e0342c508101044107410021140702c9241c01c41c842c03000a118918000d00020081c170180d0041c0007c001002c109803841d02d03152019651b005071000 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 371234271 1250 371233021 371233033
    0x1303050417060603120a020d050c211c061206020912030403030f020c0114030606070201090b0c01090b0606040506040611010b040507051911120c0c03030a031b1119020111 75
    0x1409181c2c0c1c2d15410741d80d82c2e101e4066015070002140e070718005c440701c05504d82c001c1c044900484400b0784180d0490454502640a2115030303244601c4a200c84070346030381410f00001c0d01c1c0c400c40080043c20f004441c1c1c3c007105292420a040c0020120b0003018034541d03900080160356107070b5034008651521581407801c40c00c0c1c80045004010903400c81c4882d200704117950708440c20703d14000011107009035469810703980c000c1c0400105030706007002c07401442d1682c018100703186030741d40e50001800168080c140c0e144181c2d6448140d030040003050094203402c12000c40c1c4d250305045c103050004155110b50702c50041030015050321001003441c290400041c600c0000c20800442c54140d0010300903030b00894441e0008031441c03039000080c9014070189051229a100103011890244003620301d107074030082c1140b62510500500e0400d03942c00700000e00044400390340c04a58884031240b0140304114002460090040b8004e0440030030fa40062018545420901002c10b80200e6000685008003d899010350a00900e = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 371235521 1250 371234271 371234309
    0x60904110703080f1e06010c0510051503010b06040e040213020307030615050a0c03080711030301091505120a022b050604030e040b06070605070207080d0c0c090501060813030504 78
    0xe0030160403554029140e00880d41d0b265020000401c000300c410b440105d202c000000240302081041560000060411007035440d150344940f0303c4c15013545201c0c0000c5488008000c05071002d403413400c100d00003c0d8024040c10a201000900314000c034020f9440c1c50b458200050107556034200720229408104508540d2400c002e400100581594051208510a13145130000464450303012a03800141c03542c1c0d030240c20800b41d82c1c02c44550700c0142c4036804211584800981100c0180300850003011070010018440305116240603000b2402d031720042c8180180c24142581300c42c0403030700c12407599040707950000307826184500e040c00d01060b40d0004910f50100070a00300700140010001d010394040d41700d000307035400040108815a01c0e202607042d04014107211410020308180c10a03504140280103445210351a1405640707001d4282041c00700040340b04220f401400112039520010b001d101106000769030501c4400380655501619040141040c01d1000042c1841202544c0c05004030030481c0c0301460b14 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 371236771 1250 371235521 371235551
    0xd03020610060507021e121005011401140301290301140909030c030d09020a05030f060109050108010506090402010c06090204020a090e0903181e0d0c0303110a021e060904 75
    0x12500001c0200310680007151460145054609042c0c0c028482c1d05002a02980000300082c1d441c0020741040d482d000f000c0d0001400e00c14600220741e2004001403e6245c240d050641221841145040c004001c10b2120426006000c890568490740e90a02030042d8860040640c56030003042d6064409000c40003140280611462452400c0c0841e05652b85403030b46030000d6100d20542400025640c010401d06800f01c1058100026040c002071a00300324603501c4000c241081166000050303150400801444980d4091003014003404200d8020080b41c42c00c0c002003110790f88050300180c1441050b002002c204105c41c0c00601d40f56502400070354448100b20070140491180307008e002d041c200000001841c000000055a512800da500003080d081102411320aaa50500000d420295091411b124041c2c8a60101864991165040050044c55420018102c180510840e045900845015409603444484001388100e580d0040b0034002c0d0b030030303000420900c14404016042424111030001c5904 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 371238021 1250 371236771 371236783
    0x50d0f05090115180b0d0605011401110307030206130f06060e090f1b0405090304032f01030c0804020103020d0b040f022107050f0d14040b06010306060f1d0f0d0302 72
    0x540c00034001e559140355980003081040c00340c00c400c0342c0e500003510380b007031055008840d05c3e580240600300290b0541e15aa4241c1d40242c01c038010582204119001559015a030580c501d02120003840c2085c6591f9002034480b00c0181904030311015400e01c1e441800720080e07d175214103601050400c40d85580d450740c2190720408031b80588680c005e103241036200150205400c0031650700101d280110a130100d040200030040906102c140b8401408040300144181501d0300310f007000c02c450b86002c4a900103046032526200d400c132074101030600c0801d07581070380c0041c1400d81190303090a01689446000c44002c00500f50000f000764010700341100454094040d5004291443d0812208483c0080404083e01555402d0b2008400130f00104000d041503404800609503104001d000480c60a030b0310600ac01901030145e400b030f10880c1500007880095a018803450008054504200c06040c0d19a0405056240c0c40003861030580002e540858032542c8441388603551140040c00070608160328180255a10 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 371239271 1250 371238021 371238031
    0x3030f050a06050109081f02031005030613152702040213180507030509070603020f04030f140f01110a122a02010c020606100c061103011203080105041b0f050d0f05 72
    0x40c1e101803011030708000111f012a0810380c003900782020100e40030303c02c2c2c000b5800100100300404030100042240e0b541403007a039014821401003201d500710107003482c2202d00ca1000c0d22180051070000c071048050080310b04e000c241104d903459091407c2060000c5006881641c1c1e0703a01180e11100e0340803403000d0351a000c0c050400300b492400c00440d5951401982155016550361005900c03034141082114840d40003011512040c1c009241480e03900d036501070149075401800c99401408642e04580f14404105e0060700f0340d008030007805602e8503100403c8062080b5000c1000300020fa00c4441d419440740d4000c04030520340c240541080080c1c048841428521106040d8010750806014903201480061010b029400041c11481c4c481e4040509a4040d00c00410403a59140c58018415415201402030b40c000c04180d42c1c0709038481c4451400400b0554142c002600c030720700d820266a0f03c44500385605441141038140a4000d40401c201941c1c180181c500e614032207410302d000c90340d8141480d00310798064 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 371240521 1250 371239271 371239277
    0x1504050a1410120f030207080102120402030c0a0303051c0e030a050319090b06040515030d050c0706051602040e0f03070f1709091b0904181b0f0302010c03030f050a060501 75
    0xa0748520a03010540c03001c0f40b080ca9910421a1035003000300c2c58001004c0d000c244280100c51030f580d900d4041030709a800c0302c01d40c0c014050a1074100401e5040070310000c4850801182c0c00c80320581196000360860161201c642c04c44800152801c104c3e41c010380c000211040c07507100f280e40302d140ca001c0040c01507000315508084080c0194400800c2c008a01580080543c0400c4090701070f907a00d800d010060070000d280c0c1100b120418010a520749040c0a200c02c850201e9882a503203c106c1d04807280741030b10740e900420070058208400308030718100d44007401400d54101e070701155001020719101d2801030492400781f054000080d1203400c000d01d960320006503d11170241d80b0705500c2000c003c03880c18043d034004617400244040009036041039000182034502e09000a09041c503010501042c12500c60f90242c0d411002e820541030140f001c100b440980c070500c4581824195810014185401d1040c0d1200a062250080310041010b0013908121032120050100b0807481c0707031094050018003d603100345404 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 371241771 1250 371240521 371240561
    0x1505010e03070b030c13120c0801060f2301111b040b041413051c030e100606020a14011116030e030607023f030a05060609181504050a 59
    0x460a002c01c000080328040c248040c15603035a40c034401c80680c0080c3c603c0141c440c800c1030100700086503414409096000302651071300107040c0700185003199201d80010442c0d006100e001c12000b00662005c0781d803107809c410340c00084080c010050700d180300e2212244820740211182c00e07051510301e8900c00c0f44520b04a03402e100440c415418007044400c10901103c94048080c00600504039040401c82c902e403003241101c80c483c01200b4514948192901040002511040107400001c000c00900b07145400107502000424a4003201961719407003008010614542280540c811741c1003075100110141d21094065503c0010364001545100042806c9000c04c04800481449090024600b40b00b02400d0700140052010424142c42144001c02860b90100c241c02460303140f1001e94100c11401140d0403150342d1030b810300400c020300782c9000400080c01a001445880c5269464209141315015500716001103034075100e81600054800342d996503001410030052201680c480c0c2c1c491440d150b119400448 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 371243021 1250 371241771 371241797
    0x4080d050c0c060405010f0c0212010f140a0b03250509010902070302061e0a020f0702061201051008040b1506210910090c050f12010c0c021005072103020d150501 71
    0xc030500070317802505c1c0000c084414010100b13010f00b904450142c0003d10342140158070806503802e40b40304030080c01e403041d01c400c01c84d55030003405600341da0417084035501400410200008030b0741c1e54595543c01109240c20700303d5a5000d1100c0000d02020f4003019019200340e68540c07201d076002e0f5000850440051154100003981e10031030340304c0382c0340361440c07000c120515484010b040c4001c0d4000e41d890148083c0c0411070440141c1d6404020415441c0c1c01c903041072951703d004c00300002c0e440402c14603014131850300c04101c0000c13030300d031403450b8012900944103030b20b2012400444c000c0d0107082041001d02c40c203607680001098002130340c2442021058100c8502c60340c0c0b80c03001c000360f400c501801444452204828009440d000c0441c440d28400039003c4581502d41c40501802c0d80c9010341d029020920400c030711001e50602e0a5601c6400000d414403500c0d1007010b5660640e18140e80c0700507500c91a0800581178000d220750100e5405141c2004c1c1800ba41555440711071118081d40306250100e0701100c0a14 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 371244271 1250 371243021 371243029
    0x60b0301031a13021e09011d070807171314010f0f0c0c0605071809020315010c020306160504050a0b0309060703110a08040c032001080a0e0714040204080d050c0c 71
    0x5205800c4103c041010703503001e42c24400052140d040c601c01c4a4075400f0040e0041c0c44180c00340d402440c0c1070815200303010074120300c1c40b4412406001002004481010422025088010700c4800c1700000c0c00700358544c0c1c40841c4000c83d8180341200815408143c1d031900440e40054000c00c00d5042280e41c10080386242880c114110744800100c1c001140c8540303e050045000c80d0300c210340c0a4143c7c2007016004c0050390081461101582000344c0c615404030070b1003814124044010841c0c41c00b0b0a10701107010032600000d5548030300a200140d90310032200d952000c03030311910588005140c0034165000c07041d02d0314094800c41d00200c8001c40b04d84600c500064119102c1d0141aa510820103801c07441c0071241e00702118441c000034820b4903214402f1400000003190700c02144440f41b8111488480d000700c04000414043c800f8001640d01400d090b42510f4140b00805e00d0002c5403420034441340c42a095038085400382c0034a50180e4128020904003850546d082401401003200c02e4042d5a0080c05030700800c = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 371245521 1250 371244271 371244323
    0xc030c020d09030201110f010603080706060914010e07091a070209100609030311031303030906020d0c05030d020c0111070302010c020f150106050a0201021c02130914042301060b030103 81
    0x91000502c100700400140d400f40e080302940301000c0c410384100400b03100c265404e40340c40d036004840400d800942d140030f01c850b603c07441001d07084861091207420b020031501000980103004043c1101401804100c0582c050081c15006259a821444100520388800804c540108000307a0046100c40001402c0c4c07024080444103650107030301c03509603031403c40d202120340c0f4910200c000711601c0208000c3c408800260b010400940c481e07900d42c0c40590a2480090504c2228100d00f0300380580c01042c440014400b20a8640c0c00b640c00c1c9006848040d0101160701520f04a1400140718038001980802d055040d0081ca0003030b00c03d602101c070307002c000901c810343d02e0788017000705005194a03a00604c00c052241c1e0007003c09503c0c510000d401d18103c2030f0140d071070106c0c100d116640598006101c00c00b8140348001c1c14002d1008034000c11050380605a200343c00c41d8002c000030030580340311401c0c044080000b03082c850840714a100800240d501e4409280460340203002c11764807001c0c899202d200c514030308440 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 371246771 1250 371245521 371245543
    0x501030b031002072303180f0d02090705040e0a0c02010c020a05030304061109120c01081605031605040806070806090c03070c0b091230100605180607060c030c02 71
    0x18882600b910806030025000407000320351800c0c0070300042c040751032018901d42c010b0b096000910b603115402214200004410188140100c000c4203180d41039544030000400c0040e0140c401e0300113507881703500032101d0b03201d10b030812040c07002e03c0c4003401508403a960011032000f032190000c011204024500781e81e038000d4540c1c000d0495004000040008842d03410040311640c3c100c4443e420405c82c000050250032030032918600c50b0348140c0e008215980e00036a600c2c0c10214104001c4d41e00c4000c1080100148402040014484201400f948a0070310078000c5400814801c0c1c1541c0d6281070502c0000c1c110001902c00c1c038030410a000110346604140c0003100d0003104a515070130340c10000da0b5950b4030700e4900185000400d00864181071400b8402d40e0003002c814101240c40140c80c480c00080301000c4040f1011280a080010100200c0146c1d08140070b0540c0d0050401c1901e034410300300c10070002c2c451000d546822400108400c5d04000c0190000a4000080c1d107007484a903c07129000c0b41e9074040014 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 371248021 1250 371246771 371246773
    0x109090816020105120406150e0129041d34200f0d1101060b040b032a04061205060102030d02160c12120f0503060f0d0b040c0f0501030b03 61
    0x848141d00400000c0ca007080b0b00c18100f40381401c5814900c0300c503103441180d0a0b03a130203843c3c14192070484c0c0c0c00742d0701d58044c0c80c14940000d501e504121551418000601039070840b803004014100703a43c001c1d0740a4800a1243c00c1c2c1e050624000448001c202d80c4080d135000c4190442150f4000080104140c43c180c10301024000c00c180f120500011035400020039130542c00c01c100d020100200d02400e201210782e566a2400a060f1030762594401040f00c0d50f0b000300c1c03000700c0c0d160a00900602003800701711000c9540545000d6125160b504112481000d610340c1a50110f02c4011240d040504040143c0221009510783c00650b00500104000fa1802210142d0050300708009c45800c1d14030f5907005e0140c000780e210a4402d15044c0395103500388400c0b190090030019000e002c512007001281009844144005e1524a110b0f4131088000b4025000c084c1849100c0c0c3c1501032100c4050b01c55180322543c0355082030f441c60395030a01e8240f07021015014050205080030b0340e0004901c5502034043d0050118001d4 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 371249271 1250 371248021 371248027
    0x12030f020d12020304031710060f181a0d06060f031a0a0306180611030f090f06040f02060c060711010e07031e08070803010602010c020115061e02030d11090901090908 73
    0x1c0c0b09900250300080085083c0250b14005105000580042e01c0c401e860b40c6107113242d45070034214043c0440c1290580b02c8104900b5503620040c0c5007602115004030b4012820342040301e000c00400c0320399400381003100d140c403034500400060040c0c0e102d0751030808103059442c100705400a17640e165414150342a03103a0303042039201c0030410002d00950b0010500c044480340d05160040c60759200429981a00b025407016440070040c4a01030610141d03d60704601e0000c0240b130744110860240e03850b0744004001030700c0081c8141c0640150b45480080f140381c08018000c2d200e030341c03401c00005880c089070948400840d40c80d05007000c0b83d524000400c5010b6030b802c06911500c4245c48480c0105080e00340d4006c5176001c40a02c824000075083c4001f6501801a940010a001c907514000030f08640300b00741103074075180e00600b00300807050304144000d11611005a09540d201c415040c103074918462117000035103543c5401b00c2003010884104c050f255410086079034100b00d90740c4050751030550f6035401c0054081c1c4020 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 371250521 1250 371249271 371249297
    0x909060e061e010e060f0304060c03060302030a060207020402070204020c1507140912030702060c07182a021501060e01080c19120e030a030e060739020a12030f020d 72
    0x1401c00900010525050340420005008120ba039040880c016941040107c04d000400140d40217035403000e4003a25040040e41e00d140c001941c1c41802c40006000135600040d039406645403501114103203a0040c10070340d03071a40480e00c00e940d03581e0b0001c81c0c5c080340e010309400319503c1e03407040e00600c0e646500700b550301d0700b00140344042000c01c5011400c00303805840108010801619403002030f0468844c1c0c2c1d009411543e2501c030301401c43d08519840c49d0710103880c4c8008e42e40914901002122029603070070420014030000741c416440c198500e907680744c00509050000501c0c80c2d01451442c96907400fa40d4000c45904c4042e41c208040c01440c47c1e1400265890200d030031014401d04030212010304030032010490000c042d00313803070070b55100c02c40d0700c03000036100d40000000c60030820603982c000c151031a241c0180110207001ca19003601c00301204c1c3e44a0751551031b4040e5590000364001119800030580c51003035940d00016030241c80554011004030703e8907810003001d1800460f50807030b20021511041d10803260 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 371251771 1250 371250521 371250559
    0x50411100f05040915030c0e070810080d0c03210203061008060f06070f08040b040611060f040b130c120209010f030503040e04141c110309010912030207080604030909060e06 76
    0x2e0036140100e011788905000000c203881c84040c00050210103510303c0c141c2042a4018070282e0020a07480b00905280000c0000d81400215a030106826240110280c3e20b60300e000c41e00015030741580340c50142413081034070340500c0ceca500030350003054100c0e910381100202841c1030f80c000300c0032101d0590000a046181c0c065080203002000c259114032106c00a50740f542d40c80403040e4120750854402010049000d010b000e4201c5001015003006200400741803800c04203003108044010002803000300c131100401c0f00c4041c034010401d181988a03192002142d00d4000c525803030741c80f0200c180d100703401440c0006180f100101806c030650780c1201c0554030340760600200381246403000e40100c80450106a0b994100c2c4418004040b02c13035032515030f191501700001c000901d042c60182c00b59000e50820024070265a81041c00e00381200c8805080f00580a41d03030405038201140c661005000e0f00900c4100820194407044c85030581c0c0000400b0030a00c1d4680b0080401c076070007100c02a410100c10406805c080b91 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 371253021 1250 371251771 371251781
    0x61803060a15030b0a1113030203060c2505030405030703060f0b1f080601021504030c0506010927110411130b0a0813050c031608011407020a020d080409050411100f050409 75
    0x411090119540883e404030f401c090b40aa211640b00240c11f482c1032086140c144011a0090423020506042c071140381c4043c40301d0005000310342c004000304552a800c014041c070070755009000080a9403c06d80c4c0d41d080c418042d2400c4074000d010300d450b080f444400c074035041c1403464401d8610f004511041507000c01c25100904040d104506611030000c07400e0007a0102070075244107a2113981c55550030241842c0c038900d07042c01a08205000d0742024207030440210402021400c05180318048003540e44a130808100112004c0907543d046800c0180b18944908840c0041c2140416410209080d543e100100720f064062091960001850640890751140600c1a0711088602a02c1501c80c2002c61500080c03414180c2c1c0e5a91150b20840c5008218200081c843c10030405125103c80340c44d4504004001d4403030540032402440384a0746062041030000203401c1d64044c2c81c6520f010485402d0078104080b00c4090550b02604c10241d03946040549803080c0d60072100c022681d100c641c206420301d0b11039400b0300 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 371254271 1250 371253021 371253031
    0x3206030408070206030c04090c03050405060c090409050f010605180c09060d02091002010509010f090c03030c0515102c0a021e0d0209030f0f071404060302061803060a15030b 76
    0x394050002c4000340e0b561000450256020310981982c49103480d041d40c0980300f90140140c241464070003040302061003c600c10307a00148854400c0d94a440403000640100080880130b00700d4400d80c01007d4940905502280580e44111045d0300d13400c0c0403002d009415603085030012929401070158000d03600b0000090542d104400c100582424944408541001110000c3c000180c4d119410300c0001c40d028801c1c10908161003009100b0100b00d600d840d0034180e4140f00c0201003054000143c001e0180030720018400c4482c1510704001410f05031040c8020035a14001e001d03444a111450501c410381c00284001039004103241224660b0300c880d100b20007508140705500031040915042e0407503a0b40d410003801d40683c1018010b88420343c48040c11700d0422805081e40304c6500c80b417001e0309110400141c08007210385c03110280301ca070801400880d0251002d940b00035040400440d485503542c11000650300705280560450b0444e03920750010109480d4000071071900041c180340300303101003a075268030b4550203 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 371255521 1250 371254271 371254283
    0xe0d0810150302072d020a08070506030c0c010608060103030203070b101503270303090c140d0b070309021003140c041a070501060e040f0b010503121210050a060932060304 75
    0x302c05021a000072010f14102881c074610340e031030008400c51500040c0c14002c0c0c00381e80010114542007400bc1807561102a1421012030408641c0e5289010b09407c500061300001080c1c58482d6034074903020703550780c001d440110398034406840007904804007840d00794200c4448106d0019000d80f03a4005500900c0e1944c24181c4048a80c900170500814860300650501d00c2680c0000300d41e201414607024001c100e81001c00146040703450715a040e519203450761840ca81220805080362240c400c15002040c80300002500b210350b000c10440310640641c02002500b030b044410100750303a105151483da91099000f1000300c0e000c2d8416801e10500e005006e40100e500c0303200009400e6403916210784010000319012202105140c424104001014075058018602a001080c0035943d00c5c40300361840c020b81550200c001440000034403120006e24404006020290240804e19104c0c20700404688171030060208102c4507401e500d40f014103504800e48924410544248030441e00020081c0d03039440540700341c880d = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 371256771 1250 371255521 371255543
    0xc04020307091716060908070801200f043b060a09020703180902070302070b040509010513020904050f071409100e12030a0e1005071518060e0d081015030207 69
    0x340110084c0502805440d107030610b0142c5001221703480c0c215076811a0305039904000345030510b0030001c9081d0990340000304106071100c0183c043c811281c0185e5104c45081e200301c0b1b101000b01c20340040c900030030120303040800c2640c4101c14031041c0849020350701c1d950000984d1740100000c880e66400b402c0120721a14002140c0b4a040024028485a0740c000c1e0380120750004000017010b03010800c1f9001000c00d143c0190800b403600d030000710f80c04414401c2ca4000c2c0b0030700501c0285012280e04031507406000400c20015070030a00c54082c00200112860f8000c1201400964254580c003010340d0b0381400e00600803001d5002039802114000d11020700c0030780200c0350312348002c0c0c500c0061005c0d000312507095903025103070302e060410001e01c554009640424000204124000700311002c1000c080700741154004101e240d1481040c10120142c100041c01d514508100000a108082443c40ea2482c25584442ca0b0f9220b03075142401e4800e0500c5900c030114050001014214000d40141c8981801420b180070 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 371258021 1250 371256771 371256793
    0x90405010b121b040e1f060f0e01030c1106131407050d02040c09170604030305100311040903140f0403061406060a1b021f0206010f0b0a03021e040303110c040203070917 74
    0x5482e0802e07a03a01c80c1b0919400412041e590a50702400c0c0200082e00d0400446030708100f01502400461803080e040648448101e0001c6000e80d0b4110400305401c2c08844091415440d0b2075840100d01d041240c51340c40c00321340301e00248400200201920750040c80003060070070b075908203c0141410341c03651003400034900000074040c50040d1010443c4520601500e118681490002c040307070401000c80a40100220701400401c260000092680201303a8000410070903030f0506039448402080780220709400014000c5032103801c2406071049038400c4c04280400400c0302c0104404110440741150008002d0000005d1244103602242c0d1121444110b255114582e4001c07c460b01400001da0030a06220f501c04491643e04201d030390300500a0440c1428481d092031000c080a100d80201e02d01015004140178243d50310407861107401c2034022510581c0c403507072494094840e507844400c41c1d0543c0901c11400995092600072070b40f1426244e6142c507a1103003480e610800e0006003050556252156500c2c0c06 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 371259271 1250 371258021 371258039
    0x4020a050d0f120306120308040c0510020102041403010b1f05160602090906090403050d110c0708061b04031205030405010e010f0b121b06031308070305090405010b121b04 75
    0x3448501a0b14107000c041124141182c12000302d80d40d007070030507152000400035804201c3c2c10f004626854584000c0644403410065a1415039070000f9610050020881c00303142c2c0c0560045c030446000c4200b000b8454860f108040c02c07074403075100c1a82c004500c05075016181c400841c1201e0030103800d0900d01e050840b1503840e0000404411421a80d242c2e00044900750351034138580ca0f0f41c1c8040f04440058440c80c19640003085802900d40c1030038013648a80c0806408040d02c1c064640d8507940404940c12150b0710240c0c0c0703a480d05c0699080d803078121003000c003102d0032050008032015280c0083c0c070080054502d150403a013541c402071081c0c0e0039558a0b542e5810100b0b0030301503500303142412034000c1040303031509003004903441880070f06042a60000544100040035070a070503c0410302140c1e2641c03130355181840c0f020200c081960042207108000b0f0710030708064201003d0480c1d01410384013004580c0e01d5040c0c013800c80c0b10744511440f504a07010000b928840c0c1d2032549002c02c100d00b002880c28241d40300340b01 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 371260521 1250 371259271 371259289
    0xc0b0a03020909060402091e010e0d05010f1404031b150513020a0803070f11210322030203190305090301021201050f03010228091503020a021002030c090904020a05 72
    0x10100207500003800907501e1500f043c0300c1e600440225001c40c509685480040d002d40d0b2400c103d46141480340d1b40109490b806004030024081010308460703841804c138a030441c001c006000020010619000810403c6d040c0c403d2811f2203158075171104081c95122640e14000402c0301503040722040c036050580020600a401194018240c40a401c1e03404012803042084c6007806801082090780709110703090106040c400007078007160b00032001c207850307040040c081803001249a100d207100218400c0840801c0600000511518401c241d0084207410481030a06204020344006981640031000e2549180442d40700d040f5230134480e0521626088080e8003103401d903000480300100c80d03080c3c40010445802c00c6441100082401c400851070306884a2102220103245841d00c0d251483d00c5142c40c20310780c000c00700d090103088250b0079140480800311006000c2e510441105005018003022843c0002d500d00943c0e0182140d0408242492068070030b00c015450011300c160f80c041904070000a894440c2404 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 371261771 1250 371260521 371260537
    0xc0321180f03020c04020307170a020705010518190201091503061e030c0e09030313050f100605010e010309080d0b0307030812040308160203090405070c120206100803030f0606070c0b 80
    0x1d200d45400c00d90030041d04009201411600460041040000d5207030f001c090744101e02444240c130340443c0c0700c00340103a000340030344c00004001d586086d09001c20451101c8480307100440d03203012a000903510040304061260280c10080c00300b480c05a0902c2038402d4007502ca405200680b8000421741d03564035030b08107048c0d002001c030502c112b17011109105025188095102402d14041c0e046178504121310080d03981e103c0184101d9284003e030a07640f04110341803220029490031402100c40140d00750500100412940c400e00b1b0208241d00e066022650003801143d0050790005544c80c02d14030300c0c06041e40a800c4040b06d05516009900c00800014242806002079444032044404a49040d19019000d903001421440706450000d803005152513001007155070810080e0707800b0619031038400044d0781c00002100002c3c2100030407058904459400030f102c620440c00d28410030b440540c1c1e40f602548078803080e07a500c030b030400150300000d415041110082201c18800c1d0a80e5034196680d0810f04115004016 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 371263021 1250 371261771 371261783
    0x1f0207052b02010c020604050a0f050a0f0b0132040e0c060c0304080d050c060a0f0f0c031a0f15030c040b22090608030304030e04110403060e07060c032118 68
    0x8003075030800d0750900c210078000806000601071803d0036100d01d03941d107014140013030034684482c4100042040c21b015000c1025405240f01c0b0400d40c0c01d150140c8003ca0034010f00220000e105c00464101101c640048030f400140b4030080407400740c540610001d4000c0c50f144a009114120703c0da00d1a407100320060800c0c05401c0081e540b941d0914105a041201d080845020070105022110500c0400b013000c58004015660000b510100001040b001d0502c4154041c4030514180303000c0ba4031901078106000d4110540001d04610a003281002450700801ca41160801010042030504429000007150003500c180d01707035800e080e074401c1c820400da07012010768100440340d242c4602c03003003410480f100301a004220090110750b0034074807000d940b0301000380043d04000c5105005031080c2c40340c0c0c0c010406104500176282c0c1c3e654036410f00402410300301c4d281c5901c5114607a0006a0144980194000c2d542d01d942d9589a113410740c03031007605540000000d0611241d40e850001e007085202c1c4610142948210 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 371264271 1250 371263021 371263093
    0x9060f0306041109091504060909082d070609020d0506070918020f090f010c0516060813080a050d06050a060f110601050108010522050c030105030f1f020705 69
    0x1014082070b40c120106540141030284600f2104c0d90395424416407103150100e03001e0400c400f590024010300040d600464a043c40e145d480400d104405004000c410512110b01e924031000710200600500c80c221400800c120510a12001450a400201030701d0300003401ca0301d410f0095101e841c102002602d04101140050340b040000c54204084048403401d0350400f1400c4c1040c459402d81e05115061b00d26100f13041c1503480b842c00d603020740e0041341c4041c0c04c0742c210344a03120b031019403410740c5082c3d01981003c22a91000984a031174000e551800e416441004039080c000030380c00984254001e81005100ca40c0ca0b020085004e071202040354004242e29902c500c0c40f0000240d01030308907007080e03c0105003600300348018821640c00107021411243e003611a410000f0102d82c40340c1d0005085100060010b0074082070241440c4540d024605a4070110161680410000803565176501110700a01d10f034151031200c000340d030800c0d03805051120f01482c00d4802c2d800144524402c8100820003039240c80c0300c0c007 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 371265521 1250 371264271 371264281
    0x201021b01060602071d0f0403021e1617071517090d0f08090c01050c03120c0301050a0b07030c0615030203030c060a0b030d0c02040e0c0a060f020d030b060d09030509060f03 76
    0x1082220024101c901401d07001b01403521001c5007070b40008103013602d151004004241014820841070580b0f2201413403c2e00d072090000e1100740c80b1801c00712402e044117800d03000802c0500034040072241c1c4a11040003080d40503d0010b6aa0702885482e200f0400c0c04050450b40c6494a05c551130544500859009801c031400c0401c1e0142502c6043c601031000c000441c0208802a04001034101020109080290302c2d030202000d058514440c88040d0302e401c0d00c1d044180080380410202a505961045801040a546504000405000d240c0002e400038075030941c1400030034000d5002000740e0008145462020b0b0300c90700402c0c6550320413000e02c0c0403503020004005101419110f00103407107004602400030306900c0c1034020144118039001078405d540d9000903042c40c41080007401080320018054204c030039619400908020950040900907000300c8072018150741c484c0c450710728603040c0184041c1c00c18104a25807401800000d00840610104000b0709601e5600d80c0003404400d124511155a80c2c40e00b = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 371266771 1250 371265521 371265523
    0xc0f0408031e160b150a0e0609090a1a07121a0103050907050102030a0e03032a0124060e0103150902040f0f03080708030a1b030501090515030309010507030201021b01060602 76
    0x664403480c5021009202d800488214004444031290700020402003584441c200d4010b8001104203e65200e200b200e80090702c03004588a15102380000c8401e810b0981e5041681d5440d8904980020000010400344180030b0050411b40c680100091902448206014074580112403006205102c0c0110055400c2480d603898010310f0b030702c00e4a4802405181d464000043d6507801441680d40c1400044040098030791000c000761040300d0181c142c5000c01080d4004980c4170042e515800340100d500b0410250000c42440c20080030a19004014089252400b001280c074a030022040034101912076a2283d0441c4040011a02514415a006035210318100400c05200107590180000b441440d104001041c000020358040b01c2d04140d00ca5600c0e0380e20f070f14038030080c441090340c031300382c40c6004d0301280400780c1c194030450586400d41c604010a440d281012a48410303623409070350385903000b00014865035210320060985903109000240c1481342128a050fa00c00780c9200700c540b03a039921a401c11500f0780c = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 371268021 1250 371266771 371266807
    0x50c010509010b0a06030c0302190504051302041a0a02100e0c121507050705030c0f1501060e130c030f09080a181404021e030703090302070602030903060f0c0f040803 73
    0x480c0c002048149a140f0210f22060308a12450f003d040d5141a0000c03024043d40440e294100740a0850410344140c8030086c007281c1060003200d00400c00c6814088004845108480544000b0350000901000d400c80012141d805070202900318050340c50f001300510307140c0c01002c5851600d10007402900010b1014040028409100b994259204036404218101c52220042c0c000039240b506681e541311a0510354a14030034000ca01d2198441c000c0301000d120004680dc0d40608500c010b2003649998131001111038205980c0180e600c00000d034034001803001c540d445211002e03e1801d010a011840701300110494205900c19207122400041e602045640810882000d0000b02c81c1078032440d080103003210502c3c0e440c058590245034009000301c80e050508013406c2c0c0c018000f000107952460030010041c047c3c100c01d0411000b52003584008507005001005458030b154000d0000c01c09c03540d850054542c1f00300c016040c242501b03001c00c4139101c645075120080c006000040000c6560300b002d90340790708003d8 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 371269271 1250 371268021 371268031
    0x6080c01030606090506090d0b070509010915020d0c02040e010e0a05060901020c10180606032a150c1a130b060d020d0b0907050a090b01030b0d02060702121507050c0105 74
    0x51500000340f0440e900400803e0a030340c4151000380c4c480b115880420f41480404a0103003c1d01c04890800c007000c1e6101c80102074040081c0da68502e019554074800c200084251944030168010b060401003841c450400c220707480d400140017080400014400702d084461001031081c0d5034000070410020301c1820004142c0002d1150000c520300200324006a031203000c0075810501440e1a40e0020003c40303408071156441581080b810802c5540c4d9240007000c55031500c210900c0001d482408041d18210104e409049880d02821030610300401c180884081140c81000c0320790140078410400c1c0c80368503001c3d10340710b4191094207207407401c41e6041a400340e6400401d03051007070842c000304100503200c070000074601550044619060740c0340c020002c1d042440c0c50f0002600b207109540c1c000b0381003a46800098240100703032010000705d1090400d0089503040340401035004002000140f00509102d085662140081806d44a000741183c800f407840200c02e0b40d814002400c0810301d01c0c440e080a1207040d03040 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 371270521 1250 371269271 371269277
    0x92707030b0102010515030604140a170702040b03060f0c0904110706050f0a05071e051e09040b010e0d020613031a0f090c090f09010213150906113d06080c01 69
    0x1405140d070000340d40c8d0758010002880d801030700a4036010403600b00710342060907500648e007004503292902502015003003540c0c16803103582041e00d0b05505007008503495000304800340741000b1607601c0000c81043d540c005820305030003a43e55105000e450760400d000d017540c1d03441800301140c0d6080080442640e881c002c0d0101814074601404d0004103900502c504007490561180118640d02c001410749403070141c0890703c03d151440504040d40c140040c001000d01e050100d80800a0b00c581c04011a0041d942d00040f0750409881500340e03002d85003001c090242c0211004150352030a4890340c581035071640202d0748034202240d0314140498448176284003603002c01044001c25102840000060403910064108000f40344400d0100d80d4030324080d0102c0d03020003000b5200180c969518442152214040040c0100040c000080403403aa0f00c01d983d14012100450000e0011518032800c1103100c116082450a0000402d0341d810818001c0ca0316072450000c0101d00003c126107000341c054104800031070100c0c10 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 371271771 1250 371270521 371270551
    0x30103151118010f030603140708010c020708030315030102072307140f01080604060512150f1603050c090a03150f0b03070909290a0608010908092707030b01020105 72
    0x64101c004401d603807200b2003480e10a103210300700f05083e00204030640020b00b003201c2d924000c45a1503030010b01c4008440139035000308210000781c4000c90711000c02e8029009280c200b000400c000e6003480c04044a45103004000618000c02903840c051520586500420a03002489880204200c00d0200c14003c1c07011f4441c1d20a000c002d01c0018420900c014502410b100760000415900d850720340c0220701924016001440710180a01580e54401810720901d51a030b400d9000901c0b08004981c50034007603800c0c00c442d1031003651886070603005040000d2207041c2c00c5005010081c456940d080700800191b000e4980e204a2001581d40c1d00140d0f2074031105440040d0a1003103080c05900e001400c03d040b541c01200024010001c2e1030a400e2910907070300171041500058180001100c00c0b141d000d402a401201b0400c0029a180d000c0c83c00d0f100d5903500a011200240000aaa42000390864007111103403100c3c864205210401604c46243c152a02c1000a035240c18004840d40c09102e0160004414554141 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 371273021 1250 371271771 371271787
    0xa050d090e0109090c0801021c0f09080418020f0a030617150c09032d16030f0b1f081f0203040809101e0804031202070b2701020301031511 61
    0x280204043c441d6400c11540e499512040c07011281a6401400307200009550740c15403882c12108982e01021101d5400d40b07440c20404000700103100308241a41d00145aa050500d880584407000d240c020b544000c0540070400a1540c0d400c05000340b85c0740b4001e40b400110281440c482c000707004400d075040700065102e0744554910303d215098041d841514021000d64940c0d00c1c0000c81d04161080c00c1c0c1c400f00045103d080780102c071070510b250402d5500c04045445983c0910500d00318a019448041e0038002d807070b100103000c1030304011995841500c2d458000e4108584400400f0a6911903001c1c0001ea0440016030914010b28203078254100d010030015410350605c0e8444031503500ca04458a48074031041e0b00c081e14503c5c029140460001c2183e203100c000c980503290048c22600e0100c50840025080e80c1d5598000d1801d4400d4480c1550480300d524040c1e40c9503a140380c50381c5200701d08042d021917050000300d803c0c0406d0000394041c0d032054001120700d80079810403100307403000e00303111405c2e504050103462 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 371274271 1250 371273021 371273039
    0x4030b010e060d14190b060324160e13060314010b0a090b0301110706090201030c0f08070f02070807030818060f0708071b0308071103010b18061305090a050d09 70
    0x4940081d0000c078000303c0708000034500051120f01c170750f113520340b11141d00902940d50602803052200f40c0a6410100c1d581c009645100421001e01600c09503d0010840a5121208400c2c81e00e081c0e08140070001151000505000303203003104141c0c19507c03060148204454039105440326200c280080c0f1007250104000b0301a02010701841c1191651040701c155655001d4010f1304801204c000400d170b488142d41065030103854880c1060f800700e401c1c010070700e44003403240300c42415032001c40d170311900319481c1c4400c02c94054034514034003801c600c03501138013083c141000c2c08818001d5118020855032003403c01403004070081c024001ea4400d031390600c1b1081904038081c1c1100d038601d0340b054155559009500c1c0c5072411708104113015014401e030500c00300400111800411005018001c044d1942c20050308143c245c4200103c03440e0080382c90020324001e400401000ca42202d001012142144042a05581101d45c11160701210340d1000c0b500310107003d41840101c0b51854146007a41e030721800d004141c = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 371275521 1250 371274271 371274289
    0x10171b030106182c0d0807020705090606070609021003090b0112020d150e030d0b03060f010f06030b060c011505010f1103190e10081b030915061306060504030b010e06 73
    0xc0c031000c0c2d200d02c0e0b060605039604800d1030303c0b0744071402c3c1d4a6802d00c0c9140013569860a075030550300800d110b4808103840da1700026820b07044600040c0040802c1e0f4524090100c44d400503681110069114081c2d0030040e6a1140b24946403a401e0b5400251907180c1c1c01c10046c4100181d004ac880f0750b410144200150300c80c1c00c12004065041402d03070800b10b29010340f400080180b8400b441e403034007000c29080e1000ca000d4011000944080741191003030b481e60210103c10080c05e114143c20408201010058240070f9000144002001047c03a0f08007050000614251111410071141a055041c000c0c002581c0140b486c00101c100c5260601d410382071100c20b9a6244541e5840e1927404442c0940c02d950301e0f104094403010700c0310280c0041245849001c0150107200162078580544c4030264880720314603a1780050b0391050304220020100020801c0c010100120007030a010b41029a0000751001ea01d00b900602e0010700040c1c0ea400d60315480c40c00c0495901c43d040e0010481c5c0c40ca103905101c1555a20928 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 371276771 1250 371275521 371275559
    0x207020d021009120b01060906031b08090309130506100c030206040b1008010903031e0b0307050d1406091b0108041a0a021306030e0f0105091510171b030106 69
    0x200a60301150b4001030f12003200780d0f4003104002c00e54243d410308002804000504039461500c41d000c150b510f44105030305039030070000c6400c802c2549001a4038100c6c820b810060b00452042c05803840d00e04000045240b0003c0b502d002c1e9481c6440e00240140e6003001c031122a80140a80713450741f4a400703142d80c029111040584054040b0701f050b40403c5d10012095500801041c204000304007035189490090041c10111003030904443ca000c800850b00446801458001c4000401420703409040000b0031034038003000324041d02e404006034a0a01c40c01c008000da2070092100b0300050981c414202032000100402600350307070401c20f13013805000008824045507140c0704500702101b50a6a20010884024040c81201d014003081c1d0480000d54107815510480441000e10103803543c03108854541d6007038640540b2040040d0348054030542d4800001c0c80392075004101425113001d06596442c0f5190354141820030400b9a030405600d0303420f1a08865a200c200c071800790300170322150b45050440e001414000d80 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 371278021 1250 371276771 371276779
    0xc020a1509030807050715030e0105090f0d1206080f0708010b0118060804050f0105011203270b0d02070804030809010e093106050c03010513022b02071a06130207020d02 74
    0x459908004c5e061200c60054042440080824629910010f002d4514014144201d5290102250710703005c0206040c0d2040305010000c007030b2034400242c12221845000001f032007156980c80c001c41c084500303100c207040d40711100e401440841c0c1000411030031911456441e9060000212510003503031414100301c3c0888400d420000340e03030b075180d08150341464403499070700c50301c1d510308400071800300e2550040640300340c0a5500c0499002c3c02001c240070004042d484005041ca45101c108905c030b150b44010000d40141241c0035050101c04d503a06120350b002034004581c21400850f074038002c5d5034061140e0000c50740071201380d912400d10104041c05041c4076000908902c40c840380071500c14200058281c42c0035848501001180b0382001081c030a0b400a0148600c203030006041c41085417041c2c025610707440d0b4440d01d00c0f400d80d1940161001513010340c82800002503000c0c01100041007401f02c5038039031f00e2004d1901094a00d004c808002840405d1f000b03195800d48140f1031500541c8400401c59030f103680c1070f0307 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 371279271 1250 371278021 371278027
    0x51510090c0219050706020714060306040917030c09101b150b06030c030406050606180904240c0f090803030613020c060109140a180b0c0f0a0c020a15090308 69
    0x9a400c03810f000802402c0c40c001452070950008001000034070500710744083c1d081c1c910198032080750f891180e41546045a0051060011502d030303142960042c15070511502e680718604800621104280e00304643c4441055804112500035040c080140c444041052030444070007840c810054000140d80796010b88007080002602d503114a0340e920540c1d903648024101c5803030740380801940c0d0ba594030440701190703514100300100d0030030304002064030000a040f0745411100e043c00000c2c08180c180c0148182c4911101003280300c00480c0b100c0c080200d030920303010701140e41185201c01402903030303410050303804003c11510200013141c1d020060781d4204401701c514903090040d2a0100c40030380501407254049005581c0000740300d89a0380e00c5803903c6800b1410f606510765440c400c900840e40c00c9241740c40e61042014130b00001031004000c0c01d910000700c108050820034040380901c895040700c404040481d41d032400b030809610f01680081c004102213540005119408900284600d44a10000f44202804 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 371280521 1250 371279271 371279291
    0x41d0f07081f0308040302040c111002090d060c02061e150d02040e0303091b0f0105090105130806011d0a02090a17070902160209100b031f0f0603050405151009 70
    0x403002c1001c110a00c0c90066850742c81e4100403107140d0141c4000c900c118903185502558034090742110300441e050791702405485206140401c0a13600005107560702c0802d0420790b0740058001d12882c20781507030b00d038001e084504c0e080003c02c2c15403c403237a00019880748102000900c00d205003101149070001d94000403503014034404940a806a01800000b600010040003c503079000981040601006440800d05020b80002d0055aa44800c01c05000410401102c1c800d940200000c05400c5072401e210a962940d400c0454184a02a08050443c140450542240c0180800c220750480000c4030700318945040103002881417146841040004814030316010100403050010b02c008251200041d599880a10340320a44010440c004031b20921104000c1171803048085c1180d03058030f1000741c619165864880542e0500c2e03c18200800b80180140c1d0301140350300c3d04000c80001440982c07004a028140761804d542440e11001c05145e4020385501004000040e082d0300408544071418002007000c07032 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 371281771 1250 371280521 371280541
    0x21309110f0a1502030c0303160f180e150301050a200c0c0d29041a130201031e0f0b0f090403120c0302041707050102010507090b0d0209010507050f0102041d0f0708 72
    0x40c1b036804016408040200030307400c1402030002c00d11112a80d00c1c214140c1900390252000b40e86d03100501d400c100007020500c01c9034072080351550030000302641800004007440020b42955000c035888100c180e101d5a40c002c184810300b02481c26844050704c0c03c1e04006e6003130b00c1d00c2d5840d40121135452240c00c00c8010002402250000c400d06000b10f46105d00f0000c40c0d800030182c2560080c1c0c0c0c1240e6000b0494105040b14048841c441c0c022004002d0154007612181c00450280c0310190301407003000401e8003181000a2203105102501c0c4200e000480e44120100c100894410a440b00d42e00484603a010400080e41c80b214903d51a02c2d1a600001d031003001035002c40081c001ca801814441e602149071001415000803020708503a000d0707000b0f0203d981c2c2c01d14204d501300c845105058140c08103001d000218030507038010744401c0c80185846403e111550f03c41a02c0c015140305000c41907540001c0910103000402e0f0503205c4d900303411103414920300304040100c4201000505107400c000c84107000c1801e08070 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 371283021 1250 371281771 371281777
    0xe06070311090405180304080f1606020c0907020c03010e070e0c03070c060903090e040813060e2101111c0506010e090402010f032d0e1605060a020a021309110f0a150203 74
    0x180301040b1b0352600e0301c03101c0c02a512562403826003410b100300c04140081c0c9094200000c1500c00942c00b130079240401400b40441e56101a100c8401d40c010361000400c9034070244500300a8032075100080000c58030b0990b4000784020042d0092542034004c104200102d078100807c3c00895034010700000c0c0022103424225441c12a903000407850004000c00e01041c0400c50300540705904041080082c01503070390100380c80418885054540004400c2901d941109141405024645590001299030100815195241d900100c40c0107502e08070310300d44614040280c8203030390b8021401e00b8010070b00c1c11028000360803a040241f000b410480098508002641301c0d4026240302c50840d454120f012002c0c042010f078502c0303201441c1448600d00450040700800024220040441910310030841c00e080c0014041e99501c1603681206600c40e5404810040c6c58840a0902401044100055503061450a174100e0b01281d5042445601800000e80440c0d03070f0032003508101c1e070443c01101c010301070554041c0c0c20f40c0 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 371284271 1250 371283021 371283061
    0xb03010615082e0501030b0d0b150301060b1321030c061e050411180103080307030c02031b0703020a090212061201142703072a0305100e06070311090405 67
    0xa814440e0f203e218120b030b00040c0a07240242c03018024904840b05101c480c26114001920b80c90608000c51991148545655803007440980007003101901d403002502030340d000e020061210440340c2d40c20401d4086d0f624481145030018011010780c0500b64a0040c03402210b040d000d032050703603958401c140e044140d03c444041d0284092080c00a80b0b0310303052140c0388180b92080c05c6d00a01c19480e03c502000100503a00d41607951007001c490030b41d2943c0404500134003440c9010001d41c40f04000d02c00700369502503a1910b02c4400c3c400144906400c600c10301c15003403101d40c018000c80340180907180c02401d0010455511180c140d40c2035450b820904d4100d809400103841103c0b0ba003032404140420200152211015203014091110180341c4100703103aa6248556140a0f000d0042049902030502c2c05c0041888102c110740000d55195850761101030805510044400c40c02c0c0c0e41d8852403030146ea0921460754403e0050604100f01d140050000941d03200391004180b0450350360b40014601400308a1166000c = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 371285521 1250 371284271 371284321
    0x3100e070206040c06031a22051008060f06030a2406061b0f0302010f02070803040c050d0512030a1b02420402060706151409070e01031d120d0b0301061508 68
    0x503010107801c515100b42c8c40c05c100c2140c1d401e101c0040c0303004841543d00001c07661158000d0519540f580b40e00303411a07002818669160003220740d0f11011903800f800040007040c032440c3c64440074440001d508200c840c42d40c801028000102e045e5215826408850301d45682c01c81c41e41c00c070640c01c91404a005006601c2c5445402d440441c1c1c00d024401820043d500c65440748074514510754a85013000541041400010003542c04a5090115840c001014540203081c001020905115000759000c183c1c150122010060340724096400a4003861003000a2449800e1300c5070408601d0445450703507072a44003101801c000c900c031000c5011501c4200440c1d4080e034124404000c0034212116018134890786105960054014100240c45843c02481c0c13070740120305c0c17038031440110402d0b9001540a044001410102803003200010100b00b88140908180c8441600803144e94881d05145c1c2d400b21141c006000e8001c0e071410009100740c5010318001501d501c05402c00040c20b5a890000311070000c0000319a03460 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 371286771 1250 371285521 371285539
    0x2100612112407030e03060108031e0403020d030c060b09160c080409020f210f1303050d14100803070f080c070305150a0c1e120b03010203100e070206040c06031a 71
    0x10a02d103400907005240c400d50390301001c9075401040590b212001e02a5102d107406c20070282d42d903135015092420b1203e03802d040300e1341070a07501c3d00000c408030036910381600843c100e1052141001254032030b02c0f0223403100f1280700b50700f81801d604c0041d4012580d000241407103601c1c0c2814003070103585002c1e10014100440d05640c0c1b9207030403002c07044580210380c12081650745402032182440300c00b01e007075118072164440c1d01d55a680b070400f00080c1c0315100780c0c1601844404c10080780e0031103203402010001c1c041903a501c01c0505000070781c80e4500c1d450303030710008440e00180101e100144c5a5580448095040352003e41c0300d820500e4228142042036100814510a2281120720056000c500034030500060074200324003031042070306850f05504888042d0003910400318162942c0c1c00303400000c1c2c03184142140015001d507000c01290899105903880c03005889900c00070440721104005030b9a01c1140340c40948214142a03464190300703007c90155405054a4458900c00d09074080781f1901072600040c80c11305 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 371288021 1250 371286771 371286829
    0x20f040503160501020105010e150f06070b041113020c03070204320709120819200312090c010c0f03020c18060a06030204050a0905040c030c060504060210061211 71
    0x840d41c070041c80f800e409035090034000038411401c1300d1a684036450f0081c1646000700d1010400800701680340d01d03a80e03c40014802e0300c0c0070907015103003640301d50b10076007910828600f186e040200012010070400c0040340100b0104207014802301c10b40d5842c0f40d05880104110380d6008404e1060800350455172294120f488800d4607134105c0c20f14050080d207a40d140c0d01c2d002d58442c1d10700819070350310351401340000c501009a04101d0355030b04c3c1d03503401468051525440070702031490740310920301d02d84455008030303400800e151762020100300742d107a0000c0c52800140614100c040010346201e204e0000a002d4502505400090600074810480c0c107460003001a02892a480407113000110241c450038025810020045007041c00381c801c0f601910801070841e254945044a00300113020010001c4030740000d4800000009640300000201501c06500d540c2e0701e4a04004000b40341200e00c01b103845c125414400100011081c1c0c0200030051604101080c014103070007000309a4510b04440b0001c680181d03510050 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 371289271 1250 371288021 371288053
    0x170403061b0e03070b030408031e0910050c12130302070b070c15020a03140a0c060c050901020d030911060c16060e01020c0a0e0c031f080a030e0402130504020f040503 73
    0x4681074116151980840710081c18160343d091180258580c6000400100c1d021903403680c0a1940000b09001d0b41d015a500d0b080044c841a80c02c0e2000342c2c0350382c4420b104101aa80c1406100d5109a0101820f03003030440d030003540d8000c007a002c2d1890600f181c40711b032540241882400b122000d40710003d8055503030000c601d0072400300c0c004e51142038801180c0c0400a12200c0c0b000c114a0503c0da05a035901c113010130b21842c01007256004805d2041880003c000200001e4082d0141d0380803e121503c58940380d020040000e800d00d044803003804201441c00a0300c0002449a0a038085010ba0039075110361501087c290441c5840c5000660000710103004c200011003643c026154844001c082e030039907450032540310510000da142400b98413402a504d00020704410030000c051075101c42c3d900c00b5404c0030070036901c090f07009450380d03003040c1510341005181406054009000c0f00d0841401c2e2001c5140c655642c411800281940c007600c0c1c80303180c00080c9000c1a07a4010107880150200409407900c69010003414 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 371290521 1250 371289271 371289311
    0x60c030a1103040f020616021f110f030f03060409060e010b0102010c03090c0e04030e060a081b0711010e040204050a091e18140a21140c030717040306 66
    0x88031032401d00381035501640740341c0240ca0082c0e40c000c0c4070041c10500d40d420040c96422030040c500d8810303000715611000d40c0e20994030500c1e01d08000813250401c040c0b51070091003540e03601d4000c000350b0b000340b8020b00b0400d000800c071250140301081ca103880e51039480000e03005c3c200c007450244c805802c054001c1c40c1c0710419407000440303a100b40c000b0013041c0c1e0710310400e43c1a81c00f0ba4502602e1a80c1c02481002002480766095500074403030300e4049000258040090300e99046210f140300060049401c00841da451448100042c41d043c1264500705002030362100c050312114540e00d8100242c0340c250400c42e45454040e58090000101075102c040e8035072000c2c0000b0510340b0b402c10042c0707140185c2c000c103010b5244182d444800e10720042c60040d82098403200c3c0720340c0740c0c98032020403031103581403c1c80410103110341000e090003200c402141c0c55005800062503002194402c10003c20f080160307580c003000c00006c840541d640003a881031f000d40f4450b07205217140100da02c0030305541d0070283e06191161500c041 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 371291771 1250 371290521 371290531
    0x8031504020724060f2306070507030501050106020a080301170c120a05010b06090a050d08160c140a0609090b0a090510030c080f060a11220f1403030406030e0f060c03 73
    0x880901055200b00141521402d02c1815a20302c1d8184091081d1500400b05106c0b840d441e00301000f4504604021034040d80c0310030030503070700c0303811011051041010a00a5074010300051008009034252920740408900c4103106052000a4801d491944401e052103440e001c20b100070700c0c841c0c6810504184680f1010000402c940355440c0c02e1421219150042c2030307443d44000600207021950030302c8203020b03501c000c4d410b045da070b0060140406d1181c0518480400d004d02d01c60600d0701c010031b26211078002800c4107402024842c441c00301c02444150b40c82144081200c09200c0049070740640080465814a02c541200d24214148010441c1c0041d034125080200c901c5500d001c407031b11f40c1d0740c1d01c0307242c0704c1c4010100c80c106604a0f5001c10b00e5032000f50006a00c684241020510b0100c280e0340711201102003250442058a80c0c2030100000c004544000c0000d040040b1100f0084003450b0020381c681c407079030040f20305140c4da031860141d49031000c00c40704480b500184121411410600140d05d255001241c0d = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 371293021 1250 371291771 371291813
    0xf090705031009050c160f0b090d201b060403060e01060f05012d0905060307030606020c040e28050d050304150b011d19180e1504080315040207 63
    0x102c0001c0840342881039901c1021640012400e00490300c0b001c0c810395000f030700182c2c0c00445002010002c500c4c10010540503180e58002840d90702c0701c00d04040c21612410425000c01c40107055441c008440104c2d10050200450211405000d1100c1c006015802079420151206150103081006410150b005005580300f0780c26450100350f8036001103c2d00c6595070703d604103091100015001401c07403200703410074035000c50601d8443c1c0307030721400482d0060b0030454040c4002900c805040040c16014440b801f4a0710080e20280181560000c04c250342d61012810b031202d07010251060124084681e001e520303519400000c0c0c5120180d00800148281c009540c10303203108940014400703c5140707074444c4c1e40c800070040c1c698188074007c0d10301c023010984025120a41100001c00001c1d034170110120400090040d103103100c1c1501405200400c00c481c2c5c55460381d003659100081c480d03444ca100c1c4000660050b405900c4640e06e558040402002540414809400c28004a1a00c007081a49000c00004002e240703 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 371294271 1250 371293021 371293051
    0xc020a060b0d080706020306010c0807061401060908030a0c021206010e100f031518020402030712110301050105030117070911030406050f0c0306010309020402040806011e0602071406090f09070503 86
    0x804200b51281ca4007002070490320100485030003e5000c1d0040d550007c0141002c844c1880c80c0c0d1955405a44500001c543d0a81e407a480000107236600d250300c6002d449140b400c0c45801d41408c9030300350340340300302c01100c0d0034006d281d090041156140e1601c048121f0302d0405540c40d95035140c0800304108020350725800c900318080ea000ca8940c800c402e010045035008451501400c03480d0b02e0010050124448841c84c85d6425101500076880300c1c00294020401ca6a5001c6401601030281084412860040f07500790410001006140c0c0d000d82035a040d101046031540264400764405840c00200e0341c44084810301b080201d030034542e20000590301c15401a6024062aa500c1503580c43c01c00040320042901c00050003ca542d44d40300b584080401031000d48014a0b068446a0715031411070b0907405885411844520095072002d4001e00c140144000d0008004144c28904000301e08241040900d005600105403d141c030780c2d80e0005002090303005000090103040481c40184103600c00c032031501c081e848007 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 371295521 1250 371294271 371294291
    0x40e0103031b1112030c0a03020313080a020a0603050606040f121211071e21110108011809110603040b16090302030703060f061a0a08010608190b060d0c020a06 70
    0x481071490140e50150314036490000110030404c0c580403100c2d0030003991106102c50142c00a04100d00c0c0c0742540281c00658440c01c4030742d5440312074042900614030580050f62808016114920030806964240c100410290b0b219000304040d800381c0d5110703140d8440341c902c0028000c0480c1a09c4a640c600500c010400190040420b41d0000480340c0070010541c4400c10030090003d82c00103105005c030b402c07021680e020799510b03104248901100341c01c280383e040703141c6608200041e503c5540c4c0c4900007803c1c000c40340c8d0b01d09000c281c076200c2d072400a02841c9450380301da80100f0001c014200103281000f45040d44a0400c0d0030081e960620881d00d8540003c05101e801c42030711b010700c0c111011254002c000b09207079821541e07607401a245a0254440c001c0e10340b180800c42001140c00c0280b00902d0a081c2600c885500000a28440040c0d100c01c06000703100007804003400c000250400c410045c204007180c1c1000141c0811800d10a450f1800900780c6803001d20005194040740c426000e9001d6501444141c2c10 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 371296771 1250 371295521 371295557
    0x41509050d020d02040e03130905180109030206160509130c030e01060b0a05090d050a1515150336051c1e18060f0809071401050717040e010303 63
    0x5403078060f40c045140c8070308600520b8542c00660f4050f40c49025241070407014805043c9500c900e400c4041d5454030b4008005140d00000d00d98111400d65000a200303917030954034040c1d01c030ba5010b0108022144000c02d40d44042d805503040344c110940c05840c515118001c00c9010005003030341d0b542840042d042c06001c4048640502580d8241e40740103000d549410362280040c7c80692241c0e013840d8100f80300300700003c0030070814008400660301035800d000050301620039a03c00c80b0540100305030001910a02804070902c44464086182a035040008502c0381448803034007000c00303240c404800c12021804103905042d10306101e07107400344148200c03038039102d0040090801052a140c040c3c001412000345800404205100e25604416410000c00c505104181d00e0009d500760307000440882c020b41b40140381c165014ac18280c4c820038100c09030840070b0922011051034001c00c3d103018100480859100c0a10000003806001c102401402d240e0380d036550300b15507250f46400d03c407c0d004100e150304549170000c1 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 371298021 1250 371296771 371296789
    0xf01230d1409010e0309100306090903050403021507110609030a0501060f060215011202010c020a120602031816050618041503050705060315100c06180506010605070215030901090804150905 83
    0x15204c400340d400c00c4011410301c0440001e00601400701926100001074503e064030074204124001d07a83e29903030314254014404d84905c40f0792050f1718a00c08024050108445006102c50706004071030305c1d640c0d00c842c0000685403a8614402800c2946854000582300720100017a00481e07410340c00769401407609e00350400c1303d02c00c24450300480100b400055401903204404c01e8601e076200400500d1f0700e40e00c8100311203058600c01406c440311a0b00006000581803038542e42e4000c1a41880102031170810258960078541d550300c203050003080c0204103841c60884c0c50781c000242d840003800820009601d6007a04045201a2009a520780125803001c00c6600b03094040381c1c4241d41c01909410a841c1c1c1206002845102030106400c0024400715440003075034a016450082d20812008028125075040407401d01006900480038000204098001070b00d51801543d80309615841d45034596640603031517400741851450090070381a00180104080b00d0000354680302d4a001d80c6d625050680300c400f4810021 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 371299271 1250 371298021 371298041
    0x50402120d090e04030302040e010806010608130f02011d12150f010b0a1407021503040204050906330d080a080603190f050a1709031009020f01230d140901 68
    0x9414400c081c03180f00450246260010302c6450010318155a600b4030b00c9802000ba080b0201030b4000b00010800203500080c441d4001d08a110607901c0b14402d540c907540c0716070640800a0502c180e9040c0001c000c104440074101684010709100d003140069209162150404080038040100d103801180038103814000c00f5050700c41800d000ca1821191100569554002c4886141100c80401190380142c48201c118400e0030b50041400e900c0f81402e1040105035500109201001d622001c10070410240d1211141c1c03e02c44a1a0715031000154104101c103103114121040b5006080401d8031003c101043c0024640d0004550340c5011584030303070040549900030001031103109500750b8400004542240450720a45101c2c40c11141c00349840c0e40d50280207000c5000d1044000f00120b150305403410140560700f4012402c1000300200e0501e507000030f400c0072000800a04001c450f440c2d40d03035205100840564520a0346681540383d0400c402000c0c00341c604901c6800e600315201010917038a0805000349101c072 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 371300521 1250 371299271 371299277
    0x50a140606030c0403080f090f030d0f11070f12030923210f010213091e090804230109060f0f0f0212070605060109053f01050a050402120d 61
    0x140c0c98400030810180c00c00740500b009101c0802001000030041d900811884913482002d60311074104404000140d03140601003030298000d0002009081c0d8018010216648035051205090346183c210a1501c0b441c0c0d0824500c5444d50540440c01040d0500881030043c400d94a50000740d44076104c8459500e070400d415891000000c0084115103070104503008040140c80c98500541040c1c500b0300e02c2e1012001000d441270b540010703155000070032000030001400050f030081c0200705450040b044c26540c404c040601095440d03e42c0e6041101c00000c81d0003c0c58400e5140320381d01c4900c206002d503503800c01e40442c0418401d81001400900030020014a204180c66102c90a803c0b42d40c02c0d1468600c0c842140c04500482c41e152554250383c1c4082c0c2105400380400040301c0c50f0050024081c42403641001c0d105150302c24414049410030500c2a0042840040c43d03001821121801d0348203092040c007a07800c0d542032508000088100341e0003e44101d0081712400d6003000c00c40c124544500101c1c11035000 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 371301771 1250 371300521 371300561
    0x6171903211a0316051f0207050303071a1302060a03090212030d0f0f0b06070807031704200613030221060c1305011812140304060e0103050a 62
    0x42401100ea050100040c61524000800e81d0141d0740200d418410620080d110801c0c01c42446080c10413180003403070401210340c54540d0401c4005202c40c00b401c0007241160125900020041d4801d202d20402404050b04480e1948441c0c44c0540401101201d8220ac581490000070000750540c03210075113a0350003418540c54001c4480d0118080c00e8421030603600195010810041c90f40f082006111040c00c21034000b80d10280b140c055425900c00484c010044c50030002c1c90440c6070383c0c0c40200c586160b840100d040d91b030821481c041d0340e90501c90a180344100b403928100800e00c1900500d02c141108044489001c00480c0020807005000300c0c9030040a400d03541c80300b8030060409a04446178401410241a80000c101020600e0164202c2e0001e901c06004182c100d0341c44c516400c0400a4102401c001d08012194042645203058500c903081c0c01c4c0031240010001d010b00010380d0842130310b861056035030b20343c2c450001400905031008000e0001c0d24200008420701f034a48036003100b0040f90821980c1d = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 371303021 1250 371301771 371301773
    0x215070503041e0210030b040e0601031a040302010b040606120c090303090b0f3c04030b04061107051c170c0a051c090506010311120c1c08030a061719 66
    0x41c01c3d55a441401000d40da240003401580c0c40400f81c28107500c5543c5c0c04207040505d5014041a1010400c3e04090f40e801600148002080104883c40541d02c50308280040c0d56241401c90141444108990700203103000c1010a00d00c1c2d01002040e104000c40f0001c6c4140c0750107100c1201c1d44102403002030001051100213011044405000340031490b051015241030030300f206000c0c2000080154568840c0099003491460b00c3e20b030380c0c00c1c4400e20058086d0390b400c1c2451604c410070030100003000181401d9031590b030682c48184001c280e03a205c41c0c021040b42c0030806d80340700c21000c0d001161204000302d25031030540d185160302c01c82400d10034200100b0190610b140202d0968044d041000c10303942003001c54550301000f03403041c442d15803030a01400c000c01030fa524506210b07403003c081000c62030091a0307050f541c0454607400140440090019600c1d02030328000700b0350340014504561001032035044008140426051160000e20540d0203622696110003403030b00c10a6501c68010310100e83d01040071001d00 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 371304271 1250 371303021 371303033
    0x30708011703070506191506140d1d1b03120d2013090f05060916120f020414060415050901030207020a18050c0307090b0309070308120403021507050304 67
    0x1a980401ea0310841e41002210baa40b14203060b4129150f85083c40c51154420000c2018080e800e20411041d00c80e00800b4205407000f00b0044414080d0400c8500001d01400550301c1540401c803082039540c08010a100502046510344400c0c40a81c0c3c200012000c0100d901e00d00491f02150305079007402c07003d151000807031512028155030b548040c9800000c80d8064040b01001d0002d280100f11014000c60040c14141d076401180c8400c021001c0880c5170a08014141d150700ba681038026030751942c03001444800b0300c070813220741e030f2107901181c030050070324130f070b03c404035100742c0180040e15440c1400c85901e03660754051003420b002da4411507490926181c3e5910b803642c00f0300002c244466040c5401b600e09a55a008248580350540c0500d1814452140a0755008210b210707968201c851080300c02c0c030b941404580141903280d0390180c00d0544070000085004e80900300145002141e01100e42500d07284040c100c56003e071f604440a401500400d841c01f41c4008002d40d40c10f2080f02e01c0e48400b030641d03c5581f290 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 371305521 1250 371304271 371304299
    0x14010506010219170403050a050613030c060b03070306020a02030c1b0303070b070201110a08040506180606010318140d020607050a080f06040b0307030b3c100e04031e0503070801 78
    0x42c2c41c13044c14041c11000f414042002000035500800c020a00f900c1589400381c545400101480c030780c41c05449000300001c3d030000c42c06001c0e54000b04081540601000003038141101c90788010682032001580100440e0003001170300350030241c5030582d28034068100000944000d0300004030341c150410401ca01c00603107048081504100240b00008181036140309252481d0300038800d400102c1d0f0b81004001c108481088555442011003122a000c2454003612a40c1c0d0507000d0161030505450b080e03000300103243d46800300f030000e0b0400f400e194128280c00c00c0d00d0320380c003030260b0900c018040e8100085000740030740c0899401d02280d070f480712450390301d0701c454050b9803001411031036001da1600500b041642d41005800c0c0950b015641301c0d039035414842006000314002d21403030004010302079041b14030752000c0000c2211103000361003400d9465851501407140c2c4845500441c100c1c0320b60005010905a025100603c00180310700134881e8075103854801e40301400101d900310000307441880144141c003080606 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 371306771 1250 371305521 371305523
    0x12071d010302121815091524010f0e0901030b0105030d02060c16081210090b030703111309080a030f0506063c04080109020319050304090e10050108010914010506010219 74
    0x85c1c44038003900c0d0521140120702506c2a0159900850081540d00302281c00d01d6048001d00d0301d088a14010820b10340d00e040c0c0104401811b014103028130b031070300501038004803481c108001d0011100d50707181d10b401e5840310000c0c02828024031440c40e100d115207000040b01030048000014950a0040c00111040e5204000d1802c4445010030b1085110079010490500e004214a14280d98000e050030700c148225101c0d241218420f902409041000c540e400c483c10841c1c41c010ba1b00c0c0c0d5041070f503082440014110341c52000b001300000080701404254503034000100c40021704028415178684104205550041d01c0319602c3d4000d01c0e81640e1801040f850000d400c1e0344030443c9403041c4550306824001e03039801c942e0014001e65102c03211501145401d000301200815020300200410400c2c0d1036513503076400756000f20041c00d03684003040c00004904000801260f110510f0500c034035a111001030780640036603801164103c2c5c00c5550205250018002e007445410181c2c020a4200c0e0302d00040841d4501700343d4 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 371308021 1250 371306771 371306773
    0x204060509090604030311092407020d050303010f12020f0618060d2a1b03020a06050a0207110301060302010e0d03110105150901060e030a020409020612071d0103021218 74
    0x1400161648560310303510302c01c0030b200c00500a9031605080180c00e0b240a00c074203030303120101041249066034030346d038140001c4400032220a0b00050205105032841c403803601c029500c443d8046403c0100f03c4000001c42c1641d0312043ea040800c0d55458405804100110f00254001d04102d43ea075050f04086025245040c0b0140140a41d0403580300400d800f648100b60001c0c0c080e17280c1940070170b4080400e100080031281181d01200700d80c440c0324001e201007603451100001309140c200240c1894400c01440800c16005041001076050603e0074400a52011008946c08034003501201120b00d418416401202e1301038413041d11440030b1804001420302004811400e00240c041c0b4801003400c03d01c102c61040300c96001204029048800b00240040305911480c01c000c00c1549031406030721702088010f5141d9054801045083c414030010700300f03000d10a440504800210108258240d00034030b091081c0810080001440714101d00440c181e114101c1e071032041d03040084c045800a0032180703001c514418040 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 371309271 1250 371308021 371308031
    0x3030507050d060e06040c110303040201081b0d020d0c0c05060604021303050a0c06022a0603040807051f060504060501090308160b0f09100504020102060711071214010b0402040e01030f0204 83
    0x44401811070710a82c02180d034800008003001001d04081c4141c41010101e03041901e108d41e4400d0030142c0c0c03480001e10003410005c80d034000c07642220000c2d5010303080d0442960381c29107030004d40c50120025080060390026250812a40074000d070b000e0300c2030f041c105810801030f00d4156a840f040c08060751200080d106080200e40000011400c02d0201880c0d1070f203d40c4000b0005807400c44028a8521403001c50700c40b032280d20801c41c8000705c109507a50704095064540071b44030f54a03424000c0560080d5040075280f0700503a46101c40070401544000e90401c450b082c10045140c4800a00c400c450580c00f8060101d10349800500101d154400a8101c15a4007002c28403040481d076100000c05006803526a20115000140305414106111140c01c02640200c03c1200d89001e80000f543d405015106005001d41491400480e5006002c400301800752900d001108808910b044010000c0c800502580d5518000010f081460907000725001c48811200454180c1d0035610380e411030201103c0100c2e4465510 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 371310521 1250 371309271 371309287
    0xd0c111c02120a0201061a090604031502121305100c0e0d020604050411031503030a090303050c1e030d0e16210c060e042018010c050f031b060408070303050705 70
    0x8014255200d440c1c3c00031034950b00d00854040c0082c0701460101d40c87e04103000c100040c0e200c010035101103c0e00643d04204105025801c0c400902ca075601d05c4008410713450401c0712040d88051a50315182c424021142e0189510100d282141c85410904000806014803220640742000c040c82c6400c2c0010310310762030555a080010b08640e561025604450341c0401040041b981882003040e40c06d0301a0084c0d40b038403029020050082403140002003d002002c5444884130a0170411407110b050121a41e0100f4600021060355030342064800c4d0501c242001d42c014220b0101051401320001e0808000d0801d030305107562540b201d550b10700200007065071a0310100208414803003d40080620303480d210040e030448004d01c81a00c040e2150040c944c9140151109203d665000703d811801041101044022003040120303864454494044e0041c03041d031044a005020110040804506000004406240c01083e49445002c200c402038202101840700b070300460700a42240c2e034094001d2401c90310300300107 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 371311771 1250 371310521 371310553
    0x311031207020601090c0203070204020a120e03030105102303091c0e040c0302030f0f0c0c0307060c1707020705060d0f0507030603032a1101030e0307030201020d0c111c02 75
    0x2101039098100210010321620315018002540075006228090003024201507010759a4454240028003032540001c0c1ca4000602c1410345c403c50080c0b81c00d0034043c1041d0202800c1d502d81081c0203091049480c4285100c0c0c9500610445d89007039501225020384a140f03d0300091641c1000340410381c00c0c058460540144440340480d281c07604d1f104e407294030b0040784640a1000300e4404039010002d140c410020300c00304c0300103060007c0d0f03c0301020f1a00302c0d0580d1202500099405241340c5042d603880003041141c1009240d4118050b101103e907208413a045400f02e03410541c510950324080960002e960900003410140c005010141e1100c102241050310059034204480084901200203541c9001c20700400d68019000004080505040d03080bc1c8200c0c600c03008500c0d1610802008009075890004190340640c0001d07291450300800e03680c40c0c1e00c0740d05010707010b5400200d89404851400300300c00303110b078020b200c030f6018000c000d0000c0c80d00c000621403450200d00c10460307400551003100294115220 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 371313021 1250 371311771 371311777
    0x150f09131110030501060e040e19050316051b0a1d060409020d030e030d0302041401030209030a0803010b030f090d080c07020f0a0623040305032b020d1e0e0712031103 73
    0x8043d03070300004e00d5031401e440108504008009944654100038140d500c824002802c030504100302c100b802030600107460141c0c070f9031085000c0c0d200780012500c004020b000c00070446007005080b900d00309401e17548590400c2024440360040d408100301e860a01c108003042200d01070b601c60701c0900002001029a000101c0f04200030004400264517460011031a082c240721064403034040f03090039401c1500346014105a140d080b0340a034101907011420382d5040ea0200104070719641c029001c240d5030b58548a00e44810341c421030380c0c3d00300103240c03e011501140380020032160098081d6202000d076140d031032015880e44d0100030241da02011010150810395195401113006110940b41c00415a03d244c3e41800d2500b0f07189240114070324148401c00108802104a070030030184080f90410596550801e02d000403441001c01e8401d034400f0400395055512a40003194034004890703424800303640c1c8900f081c1661440c1c403d02400707400c220381c00c1100030010303519568202d1180c1816800000c060b0b02180c03440e0 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 371314271 1250 371313021 371313049
    0x1101050c0307122a0309080d06050a0614070b04051f0e010606020604110405281e02070c05190911030a0c0c0f11060c1005150f091311 59
    0x148001080c46026500601540303200b84842d4001c1c03104e12a005110f440c0480554502c2c0381104507058800c0e0b1a80c4203a10032420507500c0402c0325224088071550034020580d03406940d0040209600108100340602400407910400840413840d206182d40c50540e03007180904102c4641c41a82c01d8008403126a071072090b103018142e900011518200e410403030039500180d011a00395040310003804040340c614034048072200310580d408109601c42000c91080040481605a60a1400400600490010b070000304842146001148042c4007038070201e4202e100d0008001c01e21039410008100c18109000212034005040d5007951031166128000300545502008540103a84008100544000188118030302c8000f2403501d00700c8402c5c9940c0744103a040c0c5a5201401d00201d0f8589206a03139186022220b13410fa80784140c034040310301507030000041c0409503500800d06a8648498020742001590070141040040c02402e42c1d8444500e90181e20080b100c0c04d4440c00d50b441c4860596407103801000c9000 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 371315521 1250 371314271 371314291
    0x5120a03180510150e181e150106080106050313061503061e0501150c110d0f110402031905060f1503010314030702061909050907051308010e1c110105 66
    0x240f02110b00d50030442d482440600240341c1c088000384402c02c4048078903980a20a042c102900f00807207010f2a161864480c3c15007118940044805045000411203400245039158104840c1e629541e003501d28200034028600040c0c4180009402c1e2441e55106e1144c513402060000f0f500e031004100701d6001201c0b9081503840c107403503089115400d0022541c042c44c14a400c0c208002c4c1e54148060ba500340506200f00703200300000c842891092150500e841d140d226001040210002c0701031414081c4051011000e407680c550b81014200681854001c0340d218030741c101d0200c104e00049a402c400200000b4141507000b40083c00b84403031a0301e0382120895044850002161290315504e0400544800003c2005464009000b0100140c13030744010b441625007004503448140340f400404846034038166108950000010050100854001004000c045600520f1810302519881c0c0c49007601c0500c401800907034000c03350394000c00801501900101ca003440c11440c0c041c08005442e003550800c0d5a09014 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 371316771 1250 371315521 371315533
    0x5040e060607141c11030906030118020405060714160323150103060608060a021e030c0d110421050304140a1505030f06090907060807030902060403140d090305120a031805 75
    0x84070b504441c00c5c40e81d54440b04000d51030300840d0300104682c3d00043c0f1070301c640b4500e981d0003400071400315010f960190602400e0140c0760a01c80c20100380d0440b020b003120300c2d580102190180b01c501440b0706d90b01901d4201d2500c40c2500b03d0f1105c0407886d4280010105120301079030031030310007110420701614001c0d40180404203a450034a8040da00b04480588108181d07441080104001c02070440421170410504011640301d5650705404119849000c0ba481c1805282100c2084203606c3d000240003958800b10990300201903080042045110f00307100540664002d20040007800da003501c400c0b100e15406420f0809190351140b10040d510101440c1c03102050011003004810342c02e03104600d903c00012a001491401e0030300160ba200c071514040c0d0410401210300080405010750009407450f0742c003400e001d507141c0c0c1c0c90030b108881c07072074840300c1c00351901801d032880080d907119000c00740580b0b810001800c0307010141c480707083e03e55000c0c01045041c183c40c1c0710700550855106484c0001c03d4050006024 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 371318021 1250 371316771 371316823
    0x5010b0403140f0601060c0804030501021c06060c0f02122e05070302040518060105041e090c050c03031f033002010e030708033705060105040e06060714 67
    0x207000d1100d85500b660503884000745080c49240001c0460464015040a107075603000340c14611414411608003801643c00016511016040c1440c10720995000c04001c20446071282001c84030b009004901501c0090b19548100151915035840d2500811100c101c8100000c0a43d405a0312044480040c003034448803558880400064080c2c99802200c51404501c0d00b03040400103241c0c0d802c103c80c2c400a110328400000d03c1c81c1d025130200cee405000c4100d602c014000902d040100c20040d01e00401010303038107001e04002050b0081302a240403452041c050b605540d220f12088202090f02c010000e407140d080f55002010883c03065400c64440201d541e44c0606448082c084404e125105510608580c9445040300c114030002c0103580b140c0e0791007140a5603e44178000c4007100401c480e02542d103095003190b00d80002403040c00a01f0208004080107001aa0f9040c0055825000d18411031105a112800003111403904a0040044a1140d20048031201c810a46c2519000f1580f00b41c0110f4901807004c84 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 371319271 1250 371318021 371318033
    0x5120f0c010e010c060203090f0709150905061503040f0609120206060f060d0b0609101e0806060f0a0201140f060a09091104090302070810051e04050604110f0405010b0403 75
    0x100400c00c00e080c18002e400502000a142c1c610203440580b81690200101e0024081840350814503649134044070109626100c0600c020600186003e903112030301100002c1514450003254450240184007200030742e4412859901c503031008000321022550216000000b401d10b2040a90382409044180c10464402201030300d010740107045144608d848400300c0003035075144812030f078481c5104c07a00456621407100101d01c0c1c2e4082d03100440d03407101c1c44641060000b544407142d10310f80440601d001c207031500506010b441718042541c990f07410040411056002805180042400240520001400c15040d00e449401d043e410b0f100101c0c0711101c0307070a00400d4900303611108054120041c0400090302c1607682c0d0303140002c90f000200d005a8403925200c050600030312090008000000c20384030000e9070011101e009260840703040c44400003c002003443c1201040c081d51240d903020f8010b04503512142c50390100300610000c01640724003040040d003600d4039140200350003800c0902d00d00d1340701c0742145002 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 371320521 1250 371319271 371319283
    0x120c081602030319020a020c130e01060b04060909110d021206131406120313080102040602010c0e180a110a0c0203010c05073504080d0909060501020c13020405120f 72
    0x3040440d44103106000f00e00c0c15074141d0044c0100d0350000141d55803c51072050b42840135000741c80da80a010341005190010481d003056105642040c001c1084903200c040503070f41c1340036078090381e000035800d82c0703080c00302c01110782c413800340340c0703c007400c0d4a0911440c0c480035010f82c0e100c03c1e4032012000d1600b080c42081d090028620361031005010341801848907002d0002d6001e80300900d414840d60420762440000607083c811502110090600c50340306c3c90b03d40c03c0c10b41c085e42c09846410019881c0030100802c061042c9c840c0c1001b00da000340110b00580c601e0601c60030307000c000381c00403030266503c1082d0b081c0110640001c0040d40c1e680e03101c030400344500d401014216200c10251105001c8200710b50000101182a90340e180d1210110003c01800d0401494000c802d05244d190518000054003003054440005c0c0c900700c2e010a60764545511751034644040c2038034150b105150150303100114048851810400320314200c00100b00060802d680c440001d2000b0b0036408185005802003000c92a0700b030814850 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 371321771 1250 371320521 371320561
    0x60f03081207050a052502120f0f120301030615051003140f09070b03040503070b070905034602030a0c030312020304020603010501080c0d05040b0a060e09100c120c08 73
    0x10540c02c1030500500580b50f4440c000c443c00090440140390644098090b181b102629000303042c0b40c0400c0c1c2c0321000d10fa40c4040003406841240309410a00c84070200000c0c8450781c0b41c01d00c80240b401d40e46590380303401c05801e001401d0301c145200700d5004030301a240c0000324140e4007403554020915030420800c0049080c40030f0b08807641035220104020541d54000303076030340c211110201d500340d07a5034803418502d045001d102c400822415005e410f0240309a4030400c0c80007038400840656142601324901c0304600e00c44007000c04e40b2441c403036040d00304842d0f202c03000c1210380010207810207002007194002800c0a1800303804a034410780502003071050650000c01d0512503e40300000718658180390700054001e000c1445030504003c006400606001041402d54107079a003040b1003408141410b10b01014dd00c1011114010010314280d40000c0d03481a66044078001c901c80c0000d00703c180c2418a840f00030301156041c02060041259140d071984c0c1c007a124850f9412100d42c0c50000f1410a085840b04402c56108 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 371323021 1250 371321771 371321777
    0x1d06091e010515010e03120409020d050109020a080a1d03070602040e01060c0c050913081219140c0307090b13030309090c2c0d0803040b0a050f0403080a060f03081207 73
    0x8225640f41503207040c00c2ca400702424121031101c48440040c1c50142e0b042c10184280c440440e00080ca0003403a0080c0038651880d40c010300842c0e0f00d0750b20f030800301d00130b01c918039000075a120007050300d44415a01c994020608614400c4401e0355074540d82e49943e00143e030444d6100c0d400502041486d44007074035140941494030b0460200640e68a400300204003501415100300a910080f038080c45030050101441907024080903110301c4941d801e1210810211010b44164847c0c036907074048100c81c0d1048001300c1e0050302c40728849440340d80540d84507420091a12052003c10b200108046060001038090114680c80700004103085180007001c80c0060347c031841505041c5800280c800340c0045285148481c2103a03602200b1072405448e5844d01c03507108120360003081d138504078424824042e00540c403444c05500d09040325241c00c1c0306013046a808a602c2c12058003c0004280028810010260080d1041502055068441c180c1c0140d41c081a4011900c000d0300151101884ca12508d2060388030000782 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 371324271 1250 371323021 371323031
    0x20d0206041526130314041d0f0606030105030d120209060c0f10020f0306040b0a0504060807050a150c0807030207080115080d09060e040908190c050f01020703050d1d06091e01 77
    0x29405043c032401d2113600900344155881590741100b9a0f00c00e1303c0040c07409030750b04400c0c0941c91038025451002a82c0d60324401c6500c0000a40904100080300c0c12144c01800410b1480d800310340c00ca80104070340010904a03a020440400315a5a841c0500030004200c0050041c0c0015144d61628045030564540c802500501c0b000241086c41419070b5840502a03c0201c1e40d104103000042c0344000e2500540d62003860024007140542c2c000600c101590000d40d55007807407903200d0091000043c81c1802140c0011100f507a941e000450313040c09002071a20034011642e549031194540c60950300b0070311100901011070801004011b000b000414004016400d1600b80f480c01c040e001480d0640a880444c0210348a03540101008041d100b1140c4103c3c0389000021002c001d2171004084034103040060b2010d100f0241c5501e6144410f01c02c03200700da5810b484140c6002130054031a8040e10220142030740c065109240c10061030418010613226403c0b140c003429203281c603544004450680a4100102a8906 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 371325521 1250 371324271 371324281
    0x50409020711011d0d110102100501030b0a2004060e0112022701030b010c0b1003170304050c0105030c0306040f0920010f090522020f07030f08061c020d0206041526 72
    0x45c0140c0706119802084100840102c0d00c0140e1a1846120510005525083c00002808541c41c0c4080c01f0b071021443c00d0001070311040107015600b210030402d15240c0402c100401032140900b0301c5005210040c10602508070103a00204102e0700000d00c41049030340d4031f0340380d0703000480b445140107000394003404d080150301c20050009251149148000300f542416030041140301d04ca0b4242103008550090010350115100c0e011801e40790815a0102d5541c4100040c00d0040e41c0510203807071240807104031213030840d0744510401c80070b801d402200c4007101d555100c421021031f80700c00850b0b614480c0e80d004008401a408001060105203160410030072017058024081d83ea034004000503050004c0307003a8102c2c0000785070410021310500d9001d00b400403000801c0001c05401044541e2050107985403141250b6900052240780c40071044042030100038040040014a02140440c0d2500c0c00500102d090a489035825400101e0000010000c90b42c200364000c080001038225614042c4981d024039074500340313 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 371326771 1250 371325521 371325529
    0x12080403060b0a180c03021c14060904080a08070903021e0a170307060b030106050a0608011502060609041b03151d070b07080a1103040626010302031c050409020711011d 74
    0x9480601304500b6207540c0d00c1150a40300b50191800114031003030788510794244841060051500b2040802980030301c0000800500e001d001703840c85260040741c0c480c03034881442c0d401c03555014024594404e0080c14600032001d0303180c1075178008286038100c8410400032502801c101020919601011900040d01d103141210030380030094590301c581c058000310750794bc03c601c0001d002d401c00e508500e4004614030800107416074400403460480d24114001c50810000c80001ca803141ca0848400303800c1305141300880e00080240031070002d41d400c91506d01081c60b03200e42d40d213008040314585200610f6207900002034450020070100b501074481000400710031b80381040d034529502401c0805008141d02244200348503005001c0b25410900ea0740a5940e80c07501d685c0040c0c0102424511030000021351070000b4040031450560b58180c84e001801801080791111202011554040380b101c20860300784000680001280040c000c40392042c40d190030120001c200042600c400c503ca61804200750351040034003911 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 371328021 1250 371326771 371326799
    0xf060b01030f0b06090d02040b0d060204050108070c02180c0c1209040e0307050a0809130203090307030908010c090e09010b03010914010b03070f0b03060d051005070e060403030503011e12080403060b0a 88
    0xa010390307106c0404003850000030020960918460b8202514001c20b004108047d401041030303d500340c0343c0d906075840d80b42c81140c8900c4074807402900801000380120030000c04019166000c0100307000c0c2440e04c0d40050100d0700f0076250b4008408104030100349440765140600500d90300c9403421000b1400c14560f511402c2e610b0a103007a01810fa071034006403d80860312401c603405098020484155076038206070380310903560703402440103a0004074005c0012032450810701030100c0012442d0b4a80d1600c5007440142003109000dd0603a00340b541d46c030720f045882c5841c03e0207040000c5010b000b110001d1840c03030764154291041e031010320340301c0e030131aa00034443c0343c148205020039184020700301d50303d076920034002c01c1d01c3c01da1803030028143d0721540900c0d800390030841e08403620070600d40c3d403415201040b01040c02054015800000c010480c248018000b4814204041d1210440005407500050756071f6803c501e0040001d8050f910042d0014040c001d1011a000e95200b1a20903911f040c0343c64079101c0c003416010 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 371329271 1250 371328021 371328037
    0x1b0d080306060a110303040834150f0e0a12050a0801030312020d18051002040b0d0b0a03080c0607020d05090f010503090724020106090e071a04030f060b01030f0b06 72
    0x340040360710443c20784980c0304949441500e01c2225900d0804d800c2c02c200759001300b1114401240a060200c0c8050038916a20000140c9800e00c0301140c1d60310f51340c001e4580c104001c0c003050b15680c2c207000e03212140640a144402205ca001500c0d0058041c2400580e05550003608810300404000002925a1002151741140d40514081d4000c0c1f4680300301001920650807c1055075082030000d044100074418280c031b04520800440b00000c0700070355072905a00480c0b286d1001d040302030080c4c49107205503030418500301c50700400320f624050300da5890901c2c903040789402007140c0e848403040256582d010054142c040070103050603030400001a00150455440c0c0003168100034020020403641001000070102520120006450301301c02c155004200d207800f0000075005600308000002c04055034456400d5800401010b0f0040b2414981e603204200603440f00ea14400324100700010125910000d9145964410340010403007a0146000405482c1a1440e8005003490015130452aa6910303040741c80803 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 371330521 1250 371329271 371329279
    0x15090601080a110307030b120c030c190320030f1c0f02150702030c010c03090b06150c031206090c160b090a0c030b09010510080a02040504061b021b0d080306 69
    0x782c0d49054509020386140d001c40d1807007038404014130800d0303a0943c105030b002010968408980180540001c3d41c3d4008410a49030190003400010a45090040b600c80c16064660b640300307030302542c0e5502c2c40141604030840362081040c60007401046d18007440901c00105180c0018040c004140442032100282200c400041c07002c11154520154000d00410801c00c0d0440001c840701d181c00d0b000a91258006455119994070f4446800e001501a1081d01540c5401c690f43c42103940c0e80c03005000990807450401d00b42c1003001d11a01d0840c001c20001064200010b0030981c02c18100b000c2030000002c00a00b007900b15810511080610740040b0700c91112898000c0804401500c8a01c0c00e09d0a00200b804042c0100360141c802009004041c4070710360140c080c5030000c01056917095100822a6034601510300da503001b0210600162070f040c0c0045801c140141d000180e480721040d401400d000182e80d0788005a001440320989105a17201c00c01c0c40f4070300940320101d060041d41e44080c054070000b400341c2d04c5 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 371331771 1250 371330521 371330537
    0x1f0c020a05270703020f03010b0a02010605031603021003062d1a340b1f030b04020306011a0403020d0c051002030409180f030f0c020406090f0515090601 67
    0x15966600c051200034080640401c000c8101c0e60380329208040580034180310049071402048259209200729641d43c0500d603a21400c40e42000101200e039030001da1144215902c490001c139041e682071000d41e8814084006060700e080c61881440400c82c8401b07420000d140ca403000401000304040d0131032049080110381c203184140310300603101903500c00342c010a4694110010142c04410f202c8028640c04c5000d0036403401c02010301d82142da41000d00c18507681c410341e0060300040014410f860341500190065051108041c0841c022601465240c0c01502e11140c04814001542020702c40b550142071460201c0d10b07540000d40c481590380c440e600c8024064900c2188900c2030082100800000d000d000308960100c00203048001e550350407a00402d0b43c12850040f20300060324000703036540744850740180d812800790307025203043c0c0c0c0708100241d50302c007032104030003201e40107942d9441204082d180e40040010403800031030a6008a40b801043c01103c819641a512640d036122020158001d00910b09225 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 371333021 1250 371331771 371331773
    0x7050109090915020c0c01091401050a050c01180818040908030612030f0c031306020a0b010603020f1c05070e0103021216142106220c0908060406020703030b1f0c 71
    0xa041c0300d03400c0021101c610100700701c101e141006c22040300f0340d42e00342e0300c40302015111030003117007c02208842c10303010071010020314004600802c0039080c02c90034030340009451a4844100484842c0208007190180000150385041d03915007032120100e42e0302030f2003c00171407845a4804803103100240c10b5074402e5200c008a1011580104201c030b0805540000080c0c883c440507840940c0c0350020442e000840c203c50b200464091701c00200e4070318190f00050712000d540d00e1300360250003d51196141030f084003010003250942000300159040114120b45001400341352040c40184148440c1703141a04040c01080030f0005010342c0300810ba00503041c0078000204281f516000c0c0d906803810760032a08034650110f0412058500c42c00c40e00d43e864442400d074840341d80d854040040045100c400b0001c09940d0404812042d40d003544042d030105503c2c200300704001d440e0100c980c600102140d003240c125030002486006c0660500520015410035518404a107501800c64484482d14000c8142000201180b0b20 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 371334271 1250 371333021 371333033
    0x1005010513090f050f130b0703091a0f04120f02070e060102012c07051c031d0a0e0a0b010f0207060507060b09041406100501020717070312051308070501090909 70
    0x4001800e2150082010508000306940130380070460b452025004800b0018a1644d8420300e80d4441d103900c031500302c0140e590301c02c09030000e180840c0250317070901e00c00c1c10f5050004000203410340100300175200401140740174a480411528400c0c00c1500b04804842e2210230603400050300000e8134603103003002c8150394403180100e00404034080c5405102446050540059044400d400707440d13403003941961451512142444403006080c20754a24000720b0640e1640424030034803c00880201d03182c3c60707a41e150203e41c0000c2c0c0114040e0010400e9100035801e2001b012610b110b505000082801d04901418140c18003035210326603803280c98240400010104200001540001281c076001003488c92641054204001e180106c00c1c8500b405203d20320100c1c1174041c03501c5c0304a0407983c050f8014008141049480898003001040c40e20403032007141004030004000703000e44800c401c0642d59268480c103900840c0b2055480f1544496000c1e080301e0810300c441d03603110345c422080c0c0e21f0002e00421980308a180039 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 371335521 1250 371334271 371334307
    0x10050a02090301151404060506032412010c0305090606010c03050f07080a030603051009050c12010b090702010b03060c0a0e1c020d060606091a1603020f0703030504030303050f10050105 81
    0xc0c690651070005404444040b820f154001d45d00e5485400c180b02c44580140000c69910b4000c4a61007002800000c12140c641c8034191411841c186c04014581c52407400700b032144001c042c03c20456511003291808030780d07140c4a000c0d8042c03000300041400341888030010745042007a20300a0104480002c0300d0200300e50100444090a0740314510568503040c895000700140800e020840716401201840c01841d03401c0e020b62250980c1203070152500400315400c1245006001c1580b1100755203555000c40d803a030b0340600782449803c03240c00108a83c40010101030510600901002d4074002c28003540c04203c0d4403540c40c01099405a541d028002c5054820140b8001001c00003903203e118005800c0c204110f94200d1000c8400c40d40312400810b0b02c400c484034944502280710740c0d803a0002d10107600300940714034024080c0c0b4040d0043d103265140144140e820465603400c180d0100301c0c006420810164184203d0b0b900060407101c0d00742c0c604180075100801080392003064100600410711101003602c046170 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 371336771 1250 371335521 371335537
    0x2180601020a080c100b010201051005040b0d142b080f040f02030115090506030f030d05040f0c080106030308160e0111030d020d0504060c0e092208030702030913060810050a02 77
    0x300944820114061685d644160195021498107021500d003065005004041c09503298491100d01c0a003000140b00090003900002a48140114a102c0204d400d805101c076907000b03210042d18644110824005141c0c13486603071540719081d02411900034550051200390003030450211900f8580f01c605280003203003c1c0c42c001a6040d464002d0760b003030304031703030281c00d03000311441c0d54070034002039982c1c00401d0388480c241d109450054200b00300e0100020415405198011b200c3e020440320301d42c0b15242c080d1101400c1d0000b91051399210310078010f060300030704a1940300c610103070b04041c0c883c0482401084032080300107460510103000100e606007801441a140300d2412048115140c2c00e803620703504007801050f1015224039240687d810081c40c4244940e42000e80003030401616600c07083c201e00151010750003100007084075043daaa00003250100103600803100b0b07a00841d1241000f80070407130f10030400c001c0e142d0383c0340c6802030402041c0c2021408085014450f070380018299140d854a030081d04c11105 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 371338021 1250 371336771 371336783
    0x211119020d0f051c0e10080c25120210050c1306030209030c040213050f04110f0c03040b03070305150f0f0d0302010f0908130609060c08071e0305210402180601020a 72
    0x140341903030700e548003c2d0640e40d0801200d00615107150f0741b40507501c81c1c1d0b0503203040441c0c110030000c6029050319070b407260080540b4207010800d511595120595039941d90f00120300160001d80251074485418042c8a400201c6000480e20f4028002d0f48100360503502d104020605401040b0345145c0d1340c092056403030800018005668079800c151070040b2441c850302845108007040e4084a041c0e003090b114030030100d121120301504e44141030510354440c0c0c00620400b42d0300e11040001044402495000d1800345d1038a403004600d609002c0101d501020310303860445c0c000d42804100c0e0719030f95609100d40707c0a0006895107441900542001c0b4094800ca20301c6440050410390540e00708940c40e0001c1605418045e04820120340f01c00040b1f0341d40a6a22404000550714071851000c114107000401c1401c0c841c641d907024800031021141c602c54821a0300b034002c10b90220340d0031907043e041c1e40354200011060350088042d01d0140c7c0000c0d5000b40001c8400388810314a030006d1401e900811030188890b811107 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 371339271 1250 371338021 371338063
    0xa020706111309021204020d0213020d0204240c03080c09030714150c1b040906050f010501110d2001020906040306090528020904211119020d0f05 64
    0x40c0d01503003075400400042c1c0407100308007002a64103001c3c0b0a560a0501e603c81c14000303516642c08010454001e40410790b8001e4802c0e040342400071840c4024240724100e1980580c440c0e2a04001a8a10000f038605149103401000c05a030202d9001e500100c48550505000405898801a880c030500812a240e5094440c0072404a045480765040c41c0b180c5100302c800d1400c210740e580c1a510180500c40251f90907501401e0013030039080c1c0c040554030000f80b000c1c1002a5a407e1911100155002030744c2495503090b40400511031540e00511501d41040c0301002490340311200a802003050f5183c0c2801a802028902c11070303040a401c0d01161081c100080015460303030b4480c1000da00030001700c881110144142e01c900010407007021092500022004011550100f4940a00056841c010000c4a82c2200584540c6a110100d0400941120b056560314804841c5070320161520400b46520340b01c8000140210380165100705804034440d60201029448134201c1c50458070345920350561000302000740e = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 371340521 1250 371339271 371339291
    0x110a0b18011109031006030515060f0d030309030e190e100803040308040f080a030e0415090c051209060906060d0c050303120a050708040b07032409020a1806170a020706 74
    0x42c801421420700c2c220191014243c0700e034280c401300c0b40d03503110040050704600c80900c0d00188440c0510f40c00344001d8410341d010306d000b40010310b0031140014201c0110790355140d038400341984042c0c04814070384140c50a140c00040d206522120f4211842606aa458140300088030b410410244d0001003860004407615903860f440d02c04015001801401d0280d80b42002c0054117010004e45000b40c1500747c0c40b40000300601e5420702c005400412071004a041c006032000415011fa0f11500d11103050b0356490513200d400008400d1020140608070500540c00748080c8460320802103400ba0300040d04403404a2400020300e0308249881666102039490701000c624030000c035000300d022500c1100c0ba0a02042a41d5541e902581da032002980c029091101e18400101954000d901c40b03044100070b4481303203041d03000c4007502d242d1724081504840c41e103c1e0040313506d0028540041741c1c0740d0311180c10f444000c0b0050501a00a08000c0b030360550441c0c041011020485e078010300c0d41210842504003078107102d90892 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 371341771 1250 371340521 371340551
    0x30512010e092109040c0315090509010b0a1a0a0215010b030a0c0203071205130902030115090f06051909080618250e0403050f130503010606110a0b1801 67
    0x10403150744400d4003484500c52040003558005004041e0520400f9040094140600006180380307903080d8185991205c6000c0c07504004001c01000b4490300c0400b040c140b50a028260a4510120002b4045c030421041070055840e000b850710350340408c0d0000c0b00d80b69000107034100c2ca05641ca103122480d00d0502c0c00041003031248071005500c146030450b4103000c0c1088991080307030b80744562000603010000c00580070076007602c80c0d0010548000001c2d1510300341502d84100600f268020fa0203a0030010300052580c8103550003040c48801841c03607210341c60303009242400c050480d1051585120340c0d00c03a404004805179000e0b00c014400341098004450b9a460690707444a01d10194408030300d10b511616000d03510802d416042c1b06400040b001400b03140511340510704200c900054004c9007402403d101d4070400321014006070600350840c1c0c1101d403256180a0501d401c640640d00494100140d50f82511300500c0d0016001c481d996012030080803a41d102d2048020300d4002000352442c65003003010300c80b40300394 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 371343021 1250 371341771 371341799
    0x10140301090603050d08070f1206091104030c09060b180d12020a060f05091911100c151103060f1504120501050f070212130b03041217041e03051201 65
    0x3214408403580f40d200c20b02e09a81000c4101c1d000c1001074410050b080d08d440c400c0d10350781c1d184a048200820b105441c5c2081030251408071407003000000000c1010400e102c00300d00c0110041c1804081005000e0078040c0e142040d1103441c0952416001c1100158119190684d50511040e082031002c000e58030b405030000e44401002c0c0c41a40e40f5414000561444036841c880c3c40c0c040c1000000518018240002844881c59401002e446a0064000c109080d488202940d52600a150382d0300304c520940c2d10b0700c4402c4a0000304404c40a40c580348800c082441f4a1081b680c1010007169800982c902000019401d0403841103580c03100600405d00094107181413070101406840303203000340056901c0c011074007a42c1300b003154404016401480c03644401c1074258010040101203407085068103031903542a1440c0d500545088030800c0e504103c000c881c0b680305c03050103105403e80c1344000c10741c01c294070ec0400c8140d05190010002c0300010480701011300034400c03950101c0952607c40580d40e074606e40f001c400f007 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 371344271 1250 371343021 371343023
    0x6040206130317031f05030d0f020f0601060e1305040c0501050d1b02060601021b0303031b040b03090304060912030e0909070911071103030a02100f0207050a050a1709060910140301090603 82
    0x5c5002010040c031a01c0c0c0c03080070015150094000c02052000c14401c80e00c17090502c180d402540580760040000c03010501c0210f018250f16100e02c480011450b0078044040340d081001c080352407601e018400098810052131080f18000d02c2c2098803554440006001400c0c0b2501c0100d1041800c500035400f81c3c0c000c9000303849031500b42c081d52202d03250b4001d2281410384007200035526030400c00016082400440207021900e407507441e0b90342002d0301c50340744078150740c410b81f0b0078011036001003010802107a20140b02c0d00540400c4c022401d81100c6541c02800301184406150b10032808140000c4400104105000c000c0803c42018411200700b040800180e511092040d50601c425080951072400c00208071a0301500c5036004000144aa05801d00104031003080a42e1441d02002040d01145041003584c000780d00941c0501103110b039610707104010040821400303401e40d03024012462940d80c0c034016500000ca040c0c502d000d503609850000c84802c0c448490310208600044000f142484040e44280181c03 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 371345521 1250 371344271 371344291
    0x1e030c08060307030308040818030f03040f1406070210030f0c03020409060906081203090c0d0311012007020f0604090509070305070911030a150906091e0b030604020613031703 77
    0x40e112501070503190070f40c2d03000140202c0c66800c082800945080010281890502001c200070001100042c0c2444107030114514107a0003c40c0501c9050201e1144a0082070030110610b16042d040020403190300038541c01030320640841004070b50b001c1c00307030f0002008004101e80811410200d80d0f0050025002401b45405162404501080343c000e14824007042c0c0e91181d0092203940c0c1e18500c20002580001d0140c01140110310840816481d168583e00303105129841da100104c200d80c801908461000a00d04418040402c101240000b400304031481c054040d114421001103030004a4424450b0794010701400e8508420082c3e02000818100250ba00c02e00c180e58040d07a0311b0030070b031054a08210307004428640403c00b00725054090f51102900020703000c1840600c9a0324840c170411940c2590061220f103840c1c0000e160580100f0760b00101072488000c080100b4085c003004280e1703814001300300900032200003824040034103400c8400002154807a24040c2010070203810300c483c40c0c00903540840c1d8 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 371346771 1250 371345521 371345537
    0x90e0127020607020d151407081605040501110304051020010510090509010b040c030b122a01140a0207090c0c0b0f06011116030c06080705090f011e030c 67
    0x181510031011420103980080c0020300b042070710b8082050700f018955044440500c0082d544801105a0250391441d00d645c4864081ca031811441c007a10f4020011329400c034015220b03c00c0da86140d0441c068405444081c0303005112004050329880c03441c0719030340005500a81450f0340300c02c4103501c101d2804540102c500240030711400d00c0c000500361501911540c807081c06c04441882a070490303620140d40a44184004115150180081021074400f00302110009844507036042d074a00b0080441c08101c0311250050060ba240c00d00c0440174107040d20000c2d0740c02191703130718032014980c4500c214403581d001d02c2da481640c1d044e090744042d50b01ca90307500c640700d181420304076007070100c80c001d41c0ea090130b00c2e4100d5a0380c0702d156125a0400c80c030000041900d4103020035400c000c5080c030020040c1d11460010211600440f90440c00e20604600c0d550380030b141000080c204000320558882c1c00c5c1c2d03210100035034400b102d0110440040e2071620711004924407807c00d005035480115496040803074008030390b4807042c031 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 371348021 1250 371346771 371346821
    0x11808030417060702250504020304030932040216050f011407030204080a0b0a060b04030602120105030c011e0c02040f0506040b0402040f12060603020402161401050601081807090e01 80
    0xd110328040343c1802c0940c00002c1c64102c6c4180104c204200c0400c0c80090710045610703580007404981054805800059072200e090208112940c00d072882c04904900d855103100000c40500e45c3c06c40751010f83c501403900454003160303040b51068203295041d0700c4000d950f1a80b0480d42168001c1010701d2003110702c001a0740208185c1d034024821182a09d441e4009081666403076100c8150790240035000380c02d025502c59001a0a030152070140002e03500c90040569130f01c1401200e45134881041c1c00aa01c6608603c42021540c1c0c0c000c2c010108034065800c2c03c80c0001003200094403511040360010707404c82e090005030703e0300c0320a581c0814803500084504003c5074010000b407004034012405000b511494180c401c2c03003000507480307048002512658000c07c41c65201d43c04102603030070120b8a621880350026544003005103016003a005107043c40020083c0386002000208888e101503c00003035164500d40c1e0001c000c0040c00724501030b2103245400d1001c102d100384424000d011120080209420101c1d0801c = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 371349271 1250 371348021 371348023
    0x1103071d100c0b07110f070303020111180d0f02150a081b0a1b171309050411120f0a031e050309070b0903070906030606030c0929011808030417 63
    0x4425071115a1034207160300d103036a100c1c500f07042c1c0034050340e042c4085100c103e210000c04000010445d0a80790240090a10703600d0b005c1d003903510f02015003824210521035842e0a41c1c00840d10072551408440510500080c2d040000103100d03280c40107900110401c2000031504850340050060311420341c2c03401519666106800d444110350302c070080b40503000300020340c54580705e4400c0e807450080c0c856645900c299a0390f0303450610340b007011803001003c90100700001c4260550550340c0040540007000d000c1480c1c59518000e10000016095118020a29220740c0d0b640b010032007220380701d08100442e00d0805a40c10080c0500d040003980404030806078088c0448144103400380ca000300400c8000b000c0d07076410314510204981000c0c848076094480d021001480b08414001c1c000107500034840010054154203280750030401a4100f803101c42d041070700000d03280701528000c200180b101440c610505e070750040125101d9054007c84400348520100124002e0b4012005208031904102c035501c1c444540d00c01c036 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 371350521 1250 371349271 371349289
    0x105090a0504051515060403060606030b0913081809130b0105040915090f02100f080c0f1206040b060a09050f012607260a0c0e0303090d02041103071d 66
    0x1c065800c003504400d5110241c01183e81c00c020600100c1c4c5c0034080344000320f08140c0055006440c1c598a8207410000c958062107205035036441614101c1184c60b21b00140240004843e4006102d9540056298201003640108260345140244079a205080c1042503d88200343c1c400c0030780d5071087c84400010645820710440402a601060034900b01a0840103040141028141034941c180b500d483e600050340c804103590841d48680d02c1d07110400c0441c480c0140072050061150b81d00241c1000305400c219540c4069600c8000c038522168410b41d90312020034047c0402420a6400c8071010618601d055001055001034403426034072640c0d4001c03400011600e84071001c0c081d40141c01601c85080d2030140300c6a0381c03580b10b80f881c28044003004000c0a06856030500d502c01d800700c46040f40074084217100ca80a446d059890034506a0610a160030009443c0d21421a16030302c5203030f1030000d01d01151601d400c101c421020302c0040b03603100e15054070003606010181168100b0459414540707001c0d880e01b1205 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 371351771 1250 371350521 371350523
    0x20714010c08030c07060216260d0b0102211e070b0105060a03090c03121106010e070c05010605090106020606011202030106021b060c0f0c100e0603070c14030a080105090a0504 77
    0x2540c40c040e0750781d02c0e400d90b5a03201400070381408004000e601c2c041242800202075038407241646101e41c0c102400d241100205c020041c240c00c501c64105400419840c60503213110501e81d41e00090004c2a5000603494081c0d403144803a10004903104a40300c0410340f20240600b00c40d0036040940c0f01b80000d20205541c41154401040c1580c11300043c001410b017500602503401301803c000a07519680c2d15003c4803255150b004681030b4560701e0301010415404080e05d01c40ca0603400091440394182203003644038071002040c0d90200304060b14044203000094002c68010280601921000c1d40c4940d0025191030f02210860301240d0101150a141c4405200726412621540e010706036998820442c0c00952101d018181c0d40400300f44070b103411801c802d0000301e8006041e00000e00032014688240100310801c03020b40428800050648000ca031140740440e5031100c21071074600703083d84d494544180d6070344404043c68003901c00402c500c40139035088005641031350404c8540c055070342d96000d048030940d0030480e0 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 371353021 1250 371351771 371351777
    0x11404030605101806090c050901391a0c070c120809030f0c011d1c030315060801140d0305070b19090501020d050a05040b0103080f09120d02071401 65
    0x10003040810355075030019401c4118a20045005551400388000031103910380c071100d0341551604104401281d5102d01d800e46890390502c03504003940d001c00640342181c02d0144c1801c00c0c43c24207040405104400a5045205100003078034508181801c0c03401c040c1c01111000413031003002101050400401d50305552209501c8070710190414140743c4401d5242a031200d007107804440a0050300f049903014001c51010a03102401804600030190004080e01003440c0c06c2c81c0b040604a560120b01d4585840c01c4950540b25981215a503600340f504a004060960460b8401407000d80c0114010754009031090489d14040382d440114480c00c004c01003801031a00e801008504100701100009280c0340000e81e01280000704012161400c4204000796018541d007107a0596000611126540072480b8281d001180e400d020051032500da13681c0d0140c8074041c000981170304404191346086403001070449002e12005082d007040041c1940d2815a40d02400750b220b40540660038011540c0714410245004140c8169 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 371354271 1250 371353021 371353027
    0x150306040b010e06041e0f08030a0206010905160e19030f0c0902040f050f01030b03030a0201151212080a1811040f0e031801020304080d090317030105090a0b12160807050114 76
    0x1c03245112120070140500481b694400000e034030700d28003282e10024040d40300610f640d061004002401c0482c140c011910301c80c645403e002d5443c92560f10300c800c848007410706c00004464500000d405181000c180088449840c101204104480340782c0c1e08164400d003400c402d86078540b00c0d00401d0340600e02603401101205c000410040c580103502206180c4181400109581d07a503003c2800c5902007420383c40075070344407000000200000d009500080100038a1190079100d955070b0040d015440b07400d006d08001500011a03c00711803507220070f00d41801902c414040c20340e83d180c4011080b00031420b0511070f5107828601810740d4168000c00c00c1c0040000003941c5410040428100135115160741c1e2811031006200204035400100300b940112007680d12074041d030900e180b0742030318100300040c040044c0050500042043c0d484106451703400c44800c20740800c6003400ea03404180c002c40e036818008540c1c4904900c8541203541c21510805450819050b111050348501c0103403014900c060104141160070 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 371355521 1250 371354271 371354279
    0x31b03030706051f0f18110406030b01053f0402010c02060c16080a0c060c03080604110903030a030c0305090c01022a06040303030b13090b06100e150306040b010e0604 73
    0x1650207242c0c072942041e02c5070880860101d680c1d0303010a46030170041c00d03c0c030720f0902400803440324441114010600003003030000703040681044460340203d224850030300d500c3c2c1442140a0b1301a80a86164030003450800300340010080c10350304505145200d42d5036070010090110041c0e5004c400840c8110780607151141b2012541d07081c0042580120b00b8981540600030002c1c4400624014440080100e50000e244610450030912547d48840e406481844098000000001e40000c8819030054048130006440c0b80103a1943c0d08901c030322200e040e814040010800034560b01a880383c4200c10099800300000c1e5205410f655588030401342c210301690102c2d00c014503800c41c0110301402c00b60401c0d4850121040003020038115000b0703400403808217454003101e5560341450940081a40001401030000700c1954840d281039100140040380202a02c689140400f406840c1158000c41c015003074030542e00c442d981004882d0000d47c0d03030368030540c140790341c0203030030343c4039680d44075405100a10462800d890 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 371356771 1250 371355521 371355533
    0x1603020a0e060d171b060603060a021e0702151c0e0c0a0302040207060f06030f05011b08181c0e0411040b0a050a030b060a0801030302011d03190e0d0809031b030307 72
    0x2001088041411300f084100c1c50100c1c1d901e4601c490440300d0006007a50b040000c201410950001c1c81030140c148140f00c144289101000e0003200d0300d11111a99550b41c80c0c900204200440030702030003000c3d040004030100f9032408511392900d407060100c0d08114a805141d849034070790301ca03440000e0388180701c0c44c824400b519282c1d0050521130310941300010b96a04c440c10b2a816100f03258000e0f20a400000d20160034000c0c203014125414034100e20f01c8184003e80c01d03000c0c0c44460050411344458029156507104004100524440070100c08a240381c02c040100c4001c000800c41104076009500341481d1039800021001070301d00b42c40289031080d00300016540102c0b560303042501c60208040d01c941075000030752600002400480c4541c0e650600ca0b60440c00c0280c07c1d200120070060310b8490307001c0520761074030010007510000030a0b20004a0b60500740601107030400402d00c0702c10f86c442c200a00c00070401513a000140580c802c1902079482101c09801c080071507910002c01c0c02d426800800c142400500d03 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 371358021 1250 371356771 371356793
    0xb2d2502100c050403060501080708160303140d0f110c120c03120603070905011202040509060405060c0d0608030c010204090e070303080115031d010e0708032a010605031603020a0e060d 81
    0xc5140c244d082c940d6a488000585600780e02102d51500b045c003007400701d03000520090504801102625030300c2d0746956001082c0d030407a4041810179a1020812101c603c00b0703a0000c82c43c207000404180709202c50980308001d02d50041e50101154031030250210001c83c49201601e206600b0380002c4c6080c10983c03100c0c036607031010050603070303074035025100011511f18403900c201030190412014907a4590f40230710501c130841e4409817140102e079000004110001e000020016480040c2c02501074072b400d400306030a0083c104c15002011140008182172160440c1580038000701e94070140b040c805240700b031103655191401400007030300043c107850041c0301400d02100e582c000b5188501d000500c080280c1001002c94500c8542981181d4540030100035401d420450140980340c1003002d10b1900842d00c0410000b0000c000b4260201a00860740203803a000a40c030200007000081c0c147c0d005440d8912510740103a0190004a116550340003001c01c40c01e4002c2c0030035200745000341c04228403030220b49480ca0184 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 371359271 1250 371358021 371358041
    0x609080706051206120615190308033c060a09110d021318020c0c030105190504050a0218041b060e060309010b060d0b0319020d0b2d250210 61
    0x180300200d0600c010a410001b5038070585e004c40d00b05480070710000c10130260001e1040c1d501000e09942c44240007007100002100d4220000c1e507440d0316810714000300001102d2030070030300d0150003441854518414039540c086030b2146804440d10303281145ca07aa8100c0c1200c03084404400c2c1c00302c040c0088105c0f0100f950052024140000c0b5618280d40c0d26800321707142c0c0042607035490629170085102000c41c001040f1701010380404074000c1c0300a1801d030b0503003000c903c1d180c00003980c401d031950b020406020f0180121f15403150003504054411102840c4a084404c064a046440c0220b03e210788080c400d07038000301c2e01641c0075a40c030480101c2d21042040b00d10741015003911882d5581d500701c88940c0d0b40348402070803010890f080c003203401000c2804050401c0e80b900c60202410034035070090401a5901c0c55601802944030803061420307200c841c034030075000c400c402091303002440c18208181c0b00011a400b403841003607403400c14410702107202c030000560b80ca0000c43d0fa0141e801040303080344071881ca4200710030503 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 371360521 1250 371359271 371359279
    0x10203040b010509040507150e1f020d0c061104090b010809010b0306040303023106030b040207080405060a02071502280b041112190c0f1202010503150d0b010609080706051206 77
    0x1240c23500b491421100d103001c0440003140e4034001c06d44040c101000d144103404498811a01c1c1181b0394800a91240c00d00d0611100300050011030704200030322a88049519960091401d440d581c0300e1b413407a00100140580c0901003a510030006801480502030f0703d0130204090040c0c007540d1501e6030280d0180d0080740494010407c3c0c0b0030056000941c0e460851942e028181d15104100d04d810000b60031604600c410314095401000070302c01103040003040710111103081c1e070034a903118400c50f4100e00f000595001882041d2800300c01c11101d0b580000c48860505041c170507003040e000789a0710034035840c081d01401410b1540f1580084c0100342c3c0e40180606824000d03042581c2c0425900c0414100310850050000341074035000c2080502450005100180c490380b507040003c107040241510050010703801c001d040020020001e05d0258002c071001d032010002400b02040111a40390102d40d15009008510004450f001c00103500c8100144100071507140f902c80030310304500344000310242c00b4000c11031500 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 371361771 1250 371360521 371360533
    0xf030a051c1406120c0d080d020c07030605060f040c0806040f060b1b0607020f0307080a1202070b07030c021605010315080f15060109030b13170315040509010203040b0105090405 78
    0xc0c0403428040c0c2107040420700e1107501c10386861010031120b6042c141c15480ca036072015002404c0b51b01ca40c140c058015401c0b000306500c891020310b005001c1d02c10054159100d00074000300008205c0b840c0c011500a410072103c0c0e19201c611501031000b142c504143ca04006041d1601291030f90419903c003840b01a0680c5000c111503445487d281d120350322070a980f006c081c10b03014101c51040030a00145402c000c2e54030240c4110f91260070301c42c1da00c0c00f40260103000d820000940300881030207403800039244010742030195118201820400012a0202d40f003201090800c00c40c0300015101040a100c2101c944c0d1001c40090708040c0114010002042c3c030b944d0207158440007040300c09040003455941c180c0d800082c07940e00c4804002d200f5000000d040b1906121820106000040c041e0f6101540803200642d042e400c0b541c1818505010003080303840782201d403000801d024020340303411040c1c107480358280c43c240015114103624038200d110403500a01000c00c400c0040c800c610340400816001030090f421501 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 371363021 1250 371361771 371361817
    0x70504020c0a030e15041e0504060f06030b0306041e06020f0f0403021203070c21140309030c09010302030303060d05030708120f0a0c230f0408010507110f030a05 71
    0x80380d00018011006510400586040503031114613a11404030070340e0381141200100c03030502c3c4180154080c001000c00c00b94035004005501e204004014000140709000e104d41e102c5988501c5211401264000381c00d00c001007015040005000d8080c0c2e0740107080100ea0345a01c1200d0a03200300d401002c0380c0c003e4082100c3c4c0e1201292001030050300300041740300e03030b43c851552040112162002d0710807001d680041c050760005c9490b0700422000c4031880c1040030340b58050700001171900140040d0040a80f03041a1004081681c0000034101111058080b91010158401002200c000c01d02c4005d40c154001c000050044c10300701e1003030303030741900c240100c905204096a514205810036090520b12150801c200061a1008003c0a80100c0018010050009000b0340244041c180d035554102c640307000000b030100c0140540c129030001b4100400541c590340c645a030341e40a01000d03100c0a0000d000150310442c92100881c0c0f041c1d8042070b0320300035841e050043c42c00340d80582180c0c8000c445601c05c1c0003414 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 371364271 1250 371363021 371363029
    0x1f020d02030a0501080d0801150f0903050d02070303030608070b0412030215041113110d05040201050c120c0f071811090a030f0308181906020c0f0d0e042c0705 70
    0x14000c014401c0003043c558102000507260007400041c07441000200d100400c038200514411003060044c9103008001307000030500c145c4803c419640004d20070310a51406041c003a03408501c02c4180d0344241d03014400c281c1e0f11058a540ca8105008004c0030740001c00c0204608090f02d2103480c2814440e0069a0090000e070051121103c0c00321800d0361850000a2910454070b40341e10803085641c00c029081103550807106000402c2d000d04800180302c190f80320007017415a8003404c251981191540115030358494100c440c07d03001e80003544106041d10984002c0e204400002c5144001c0c0d0303869007051042e1120b40b21041c070140c03a15014907005070100300b1240e4060f4644000740406507014403850903200c105860700400011004044c442c040b99005401c06144201013040c440c8650700c00d000c00344010481c14031500a1103540341c1c101a500c103e40032266117200c0442c401010600b1a158140c0823902281800141e600d40c641d1403003560100b450104540c101c446030030401910100841e460192614085 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 371365521 1250 371364271 371364277
    0x40c06080c0f18062a010203072106030212240705121005130b24040501030c0e030d020703030f09030b0a0c0216030b060f03070503071401360e06031f020d02 69
    0x809034644141d4003011260304419001c007110408603000312324510300004028010440340304040c035034039503481da0f400c4611910f4001d040656001040c0340c451880850046030b8070340001d480004441d0099a5404c41213846d441298424143c03600c410345003501940d294002e2000c002d000c11089031044402107020f4680b107c40c801c0802840300005000a818010003030a4030440074a141d41c0c11100150407a1400204161012180203080101e01000c21500594880b1503528502e5014851541310790078840d03001507020700b01c2e0300980b5001e8480d240b1711004c4600141502018080321f9516011445081050b8000e01d5070104030302c16100c072060300c0c0300c1844c10381509600999030305040070180042403802180681c0610070440040c41c00701d00e4800841c1c0c0303506044c40703040c05d403130321460b2054496401055543c84040c2d00000000806034200e007007030940281410740000764906c200c000b04042880c104024050b0708010001d1a81d020403c02c8248040d0411030000c0041d5028058034071044000d0002d = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 371366771 1250 371365521 371365537
    0x5151c0525020106180b1806010302160b060a060203070c051c0b07080a0e03090312070204020f0a08092406191707140102060408031803130e040c06080c0f1806 70
    0x1249040c40c0c512a40d01700c6012817480995149861120140d40d61464a00300e006406005860420750b10040107070000c3c003c09460088a200003980b010800c903405072034900c100401c071003025007180c40d001c08903604d0080700c3c001880b00c0c0083c40705026a140080d40d004158102c01039202d400702d0140d9541651580c16664000400c038400280203031102c1e1800b8294089030441c0040d414050190002951100101e034840014440002c01d08259200ca80484078200344500c0030554941085c5030003880302e04100d46480050140800d0f111180349000d9030001c42c014070304803401c3d040e1078003020861042d540c2c62411803a4031145c10000f80c10007400443c0d02c508440ca1000d40501443e00d5026080910540d600c24119001001000001030710601525000300c0c03c0d0032000400c251301e5000d00c1c694400d440c885000d0840400d400501301c026000f4051040388150010041d942e42d81c1d0003980c440000ba41d44000304103003809209520001500039000c0900031045001c0131601420208005900c81c0346 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 371368021 1250 371366771 371366773
    0x14040918080c0a1a06010f110705040212091005041a0601030f0608010914030a0816030e0a0c060e040c0f03360201080f060105040501140c1605151c052502 68
    0x1001c3c40c00e2060604400e124200500d2a1030114988000000c001025000218090020002c41c1115101040241c407000d0003001e0421540c51100340203e2100c0c0d541260103644030300c41c0d95804090150140a041d0203158409406181450003484c2c0c2c103c2c0c0000200024109541c86160f0b04501c003c0380a984001c090203000003502088908082e01c003411001c0d07040085510130816403088a178810f950307950240c2145810f0801c0e013280341041340507012200c550740040c8190244201071008224108081f030700f0646800a20080740c4040c0815201e0108180020500d11045040854040e401c07004141d4400c40b60101151403840078082d03000301c0c0c0c195400c3d00806200c0e8080071560405c000e1030300031001000c640b15629094000a2684c0f08500071641048201c4240104422405040e61401c0c030003801500c000c41041c0c5000ca03561012031080302c1c410b0400310b01201e0000030704811190140141e91042c0030000200d00315102410700940003011a0710869031011300c48000d02c0d0710030b0341d4800640c = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 371369271 1250 371368021 371368033
    0x20f090d0c1a03090a1b0314010246110102070b0603060f090613030c06021803010c0c02060d0504050f07080f0c04141f0f0b0d0c14040918080c 63
    0xb4007100440800c0507180c0c100150800500055140001300100070700d80c4061084455402c03040c542103008895440141220303203d2910700103860041d00541a00c05104504c52101a50000300c07035000d000350f80c0c3e2504e400032204041841c1c00f4046003005052029402e040032008401025182240e001131010740e8880040d2041c0506440c0501c00607400885100503501c0e10b080885075252a0240640852200c024200c48001018000d0392444001358000ca0210f448002c003403032a01690312060340c043c2c886d510300034004242d0b13800f1f00025417139940c001c0e016a04156540c0c208900512300644141c07600d21610001c441d11101c2000882d014002040c0a071949040170402c2501d8069022149071007141048400d001110303031808020f0b4482d000007543c0c2c0c4125000035489981ca0802e400985002900110110704000c81c0300c001d00000c84688000c01078180003400072070728540d28244c10304070000100302c1000b0180c2e90740c0102c070402d0714030041c110803880780380d480354402e42c0510040440ca801c80 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 371370521 1250 371369271 371369279
    0xf0304030f02150c060c250614100b090111010204091509061a0a05090f040513031206060801030312140109060e07020f0d0f090806072d09030303020f090d0c 69
    0x200c0c0403484407107880145542044c81401501e034032254010000c000c0c21001040c04004000000c43d200510000d0081c03407040c00e401d0742064405855960031903550719510750041580c08038415000000ca40c0914001820400e8220045601003100f00b10706100350340901c40070035001030902c205090000301c44281c0c24140d142080d49015a28954410304000650b160340030b803103256000490320b10400314a0b004d644d84860b2000511099608090940c1152500c42001aa5503030608600d50040c0170b41c0760801c05880c0e40a9480554000b801041d000800340401000024095a0499903185000f030000c40c010340844441000803400360b0290140c283c0307940e0100a01c045c00080c0f2908034a16101400419000c62485691680c060402d4010808403040681c0c8032440b40f040d1070040c00700314064559134100204010100d180000c035030390b0b1081c0e00e0040344201f09110b4040e41d040e2003003901d444075503910311745042d8025000480f01c10401001000741c0d00c0141d8944110404e0702d44221b810402850170 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 371371771 1250 371370521 371370529
    0x50c0a140f090103110c060c0a0315051813060f09020f030309180c0d06090903080108160608070908190506130c170109021f0e01050301120308090f0304030f02 70
    0x3000108040980200701550410300030400700d801a0800f820003140385681c01011102900c10070941c0d1b13945005a80c18016540400c10051540050541c3c00f030080038002800a19460183d200c2c0640c4101b0410b007164448031010301c42e560140d640780342c410303098425440390b4080c0c2d8064210300c00c509550390030070021850060415042941d059000310306101151000c24031407101004c1900c26115154001141c545903003040b261441e90001d8140522590365071900041e00d001501240441c0030600003203000c05002540c08040c0646200d1580514502401540d082138090908030401c200c0b080c0100d105641000800310081445005842c280000d0800c0c0c0c0c203101002c2c00c1d110305240187c020801040300010880c00b0348180100240101e5080e850990041140c488000e4200540030150006516034102d41d001540a40d269031084003034060044444d88003d006103014004000e0a140219100c2c00d035265109403880201c800889a0f40304243c40c54100350700803a6054440d441c00811414 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 371373021 1250 371371771 371371787
    0x30309020a0e0106081503070513020d0b04140a0b0105130b0c060708070507021e03011d070b040515030402040e07171006030203120711090c0325050a0f020709050c0a 73
    0x4012103040140754180f400050035901c014000d140b0350803822601b60000d9809001450050600800c0749030b00300c50f1204224040e4002e5030919076440c2c0b2b0708465180c1070505010340781c6864041c040302031556a13a035150100904950030702d141007280500a03000a181600f07007400280c00001c00141e201d2200c0041d440c9000801825a003c111080e0203200203d5004002e90303468030b60480700c03c6080e03021000030700a50b000341444c480c4d05600708124040001c401054102c01c08000006941805494407072810035442244030f0313240c00c90140000c0c2503d111060f03005c0c40e001031005101003220007914044919201403030300712020015405024440d800b1003048640d1640c504088184401e61850700041d0b140d00607495880e965090000700c5404100200341c0610311480005c05c49412401c001c0001c1110350401c0352481351204001c02c0881340341c0040384422002c400595076003468030030340410855406021680300720551080c4034000c101030003540586407007640602d20723981c0c407206c1120300240026 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 371374271 1250 371373021 371373029
    0x909060b0a05031207050f122212060e2a0315010308070210090801021809010602010519020906070b090a02010e01050406170c09181f0b120a0e0604030309020a 70
    0x501455000c100c1034801041a10043c0c0012800a0f205c1c3c10310700f045400d0415024140815000340042030329641b41d001c0161815100144e85403c9150301d104080c40d80403aa4000c0409241200c2030444c0003d0507070308140e812111100c1a03406003c09420030040040c105d0400001c1072a41c1c41024400b400c0c10030006800d07444a005001c59545103450f80c2c100c41c40703a180044d01400c0380c0c1251010007401040c80c076000785000d1000310b52f01e040c803142100b420728080c11914070039002503000060041c81405018003c00740c1009142d800c1401421140081d84881c140725048a01031010b00b0108880d4020300f88120658005000c21031070503c00142200e22140b600d07814000c003031000344001c1e6031280c41211845d1994100c07810725259622100c4c41350054944680d0300407050590141030310140e0070402e02031140d10f040b0385e0b03c0c80550414540d2422a50180c480103000038095a08070750a04a100f6820030141000061014880d6100038207010003101e003540440d403107900c05021401c1030081301d0300034 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 371375521 1250 371374271 371374279
    0x2100f060509160c05120a09090b09060f040b040c080910020708070b130f03020f06010b040b0711040207060e0d0206070806130c1e0e04060902070209070503130203070909060b 77
    0x5a00300340c0002d030601c4000d4010702c2c00010079880d8080050141406191068001d01254440d41d00071007005010b80c041890baa001a200b40c0d80003903100154007a00403402001048803420f81d590390140900c09110242165119407225543c5842d61285c0c0b040440d0036085568400180ca02407082c1c070302d001c41c08420b515410340704104103808540c801003aa42001d030310410070700d2a40c40c0c0c070004003501600040d024040300d40c0100700001309900040c100d904860a44241c9001d6030340c0b130007016140d0280b84a0750034410001c002150029003841780384030089400900050909880d91521801c52342c0d209500107507a40000c604055041c0c040100e070b0391020301c914100525140034004508094451035040b41c2031078941d5051074070716004600340031004241c00c414001014510400170a000e0740314164a0056203000c601081d141000e0080710354082d0040c0485540e91691034044456900c000c000500c1301000710302e590010303079003442100000e241140c0c001c5000d00007401c01c0030894400032592885 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 371376771 1250 371375521 371375531
    0x13110f250f03051b120a0e010906140c030c01020c030405150a090e070203190905040c020307021005160c091a120c060d020c0106090501080c06120613060b0a02100f 72
    0x50503440368650700c0358145019512422480204c40f1341410a0b00c10410700d000da203038282c081080d5000501080800b45c0d4030056141840b20040d62620200c3c0118000690714951417501840134000800381400c02c441160f00d4003030361030a030340d00326004081c6206554100040070051868000d0515594611216210307140040f2810081d0954607984107080c124000c4200251103d4020701c00d032050400e640e00c056400400415009003000403902800307101da427801c241744034458400003c3c0c480d144c0c0d0140a0300c0040111741420b40d01e030740160741c0326112590910680c03000079517075600c140000c10350644e020400c60200e802c0c0c030003000305195015006850b580052018103400180c0010703440001d41d00103a8920364040d80e00040d05c50500c2c4111190b081100c00146000301d03500c441c0c102c900305010345400e803010004101561050f040c461000c010b43d0004034009160018500042107555580040c03199554000d98000360010320025000d81c01c07101c10701003000d0395402040c049923070a400401c5 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 371378021 1250 371376771 371376773
    0x1e030c0918250e011404120b09010615020316020301060807030b010e010501110c04110d0207140f010212040b0606070c0b0307181208092806030f1401030213110f25 72
    0x440324007100c0200741008603010a030182c60285d03004a8018004c0480c428036012802c2c14140300b100001e40c0c1083d4a980782c26800a182c420380c815100c58141142d0186107030013004e2100000c1c112740780c3c0c3d050340c0c59540c03100d0005416504100c0e5800035441540048181c0d07240802030841210164801c9040c030150010400319100041654000c145003203c0001c2c056401c6801240a40030304200c05c44540d1000030b003901405050002d501404002e1003c0790030340940c07113084c2401d130b0069004020f420141e0401090018205010b542e51080d0080c0c0b00e507050281545544003591102d900c0030350300d51300000911015560100414030704403149162102c944d441d003810140c0c5401e000401906520740800e801000360b45110300c0526059030035240c10130040d0042d9010b010400b4510800d03000c0307441e045940044458034010b02050805100c0c24031040d030318580921100140342210b18042c55540c2983c5d406003003408002d004882c0100b40186e49880c041c5e0582c0781c4036100c1041d41145880c0b0000428 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 371379271 1250 371378021 371378027
    0x6090705041a010c11090c090a080a03050702090a0e150f150603010b0c0a05010c03021213111003380d0c0918080c030703030b061e030c091825 63
    0x100c0c84002e00c0d041300350311440d04100000070100c4292503130215000b400d0010001e0361070040c0a2403c82100c20070364807a901c6610580e41c0c1c2c1805c50050118031305100b075001501e40100c03000d5003c41c4400010445541140360641031024103034030034808a0304181800b06001d1749500d841d030701188061070101c00701e402800240580c041441360140429000519250f104028000d51000a5010b0300912030907074440c4c8041d01942112400a070031030b5040000070030b40c2c004010070480840e04000340205140c02c100030b01c52141009000d03041490345414400e4000800c503448822008000c0c1c07078a1300b4003680f40c100e12082c021002226403161000612010104015400300300032510004030008410410144000280e440f206000e00a200c000c12031a660b0034000c03008110f01351013958200880c0550030b00704082401480036440c4294801c0c0020855031400e007004540220503448102d0401441074001034094290020003244002c40c2c1007400b40342001c1d10308104003440801c943c1d290f41501c9000007 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 371380521 1250 371379271 371379311
    0xb0406180320071805090c1909050c0403081801020c0103090515180607080603061612150b040303020717210307140a02031b010509070e0a06050a080609070504 70
    0xd1000c600002c2c4a10301c0390102000300c000245a13000352240c49130040d8041c000241000c444444150290542007000c2d4584446c1034250899a6400c1458003814903401c603004041c0148203c0522030100404008200c0c0c0e01c01800d44182000e0b0448900c02e051400207040003c0d15044074141414102603400060010402440448440382d0030801a600c0d4031441080c80d07114548940c3c1400303140103000700c07544d0159906100700011740c00c659450700d8030f9881c4000d1850a4031a2800a181301d007043c100c004017500a2081a1300601c0003494640c1c46000002c05540a41d1007200503a1209400b001210b03c0e45508886c83c0c1a41405095804402046503054075091400044098000000625000d00500003c01382c118040b00ca00e0b180c509039140a540ca078000100004810303034000b403041e0004014081c0c58451040040504885407a007600111050707005030090005e00c0d110440495507494420521300200711030b00050906e0704000c0142410300089402032030049090000b40d414071320900d10a = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 371381771 1250 371380521 371380547
    0x17040f03090842070c060e06100b0a030b0a06031a0f06040312050c0307030804051606140d0b03060906010f1401050414030a120e03150f01090c020a0606030b04061803 73
    0x3100c0003000f00e168006105408080840c914a1101c018421241d034001075000d100c5100f82000c100c9034441d07201c0603a030740404070745d049038030110140140a00b4042d8009440782c0100c0b410081504030145000400022441c4c01c440700082d6602c1400c00c844a42400c03080380e800013036485900340011240850f4a03446075010181006032031202110080d03205400301c845040040c41640e45507141d600c2c008251031070580d02a1002d120b020a2040d68511184807241180c0349915600071958001320411855040801c552080e40d40d940200140b82d00c0c03c0c08054418071903680a4512581010032400c040c91640d040045080714503071a2605c2039812030100c0d425182019104180f030a02c0100083c549884128003c01000d5495800f841258110643c13844040c021010b0b80c001d580d1404200c00100f1088a4016102d5440340040040c1c403c02e84c0000031010007841a0f580c8118aa10b40b0001d41e10a40d0048600720009010042804000d108034168904040b40d216801019a10b00814a40300500 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 371383021 1250 371381771 371381833
    0x6090f1c031206090207200a09020708030709051027081c09060504080c010c020f030a11040c0f020a12030e03040b270f0103050c0c010c020309190e130317040f030908 73
    0x1842c103c0a032380c4d182254000b001d06103415555040c0d03031b1802045503001508d804003c12641000460586015020740315030300599a41d02c40c0904004901469804c813660304e03030741c403030707007941e4000c2120442400a41c80340d20308552100300344002c0d440000c044a5003a40101c0410100388400d0041e4000820b440300301500929111000c0c9a01d80001a24110b44c050242d515110344640f40c1d04000204045281d241d008450801c074803240d80d0011780e00a04820800001600300e15030b401c0015180300d590640c0c00030545000168040e0102c006840c1d07910581080b4100100482c0f544658800407110350940300f104207101c2a04211100491240c09404038142d05060301c2e00001000c01e003540d4103030794101401e83e0081c40701114032400039440398000080c050041ca0145921060740c0200f10300c103012540c00d02d07080000b40da42c40000e01604a000348003281000442c203880204040c4a240c1a401307176000e184840c1c03401e5154540644000e1352540329445682210340b5007031242c60180040340404440c82 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 371384271 1250 371383021 371383073
    0x7021b0303160614070503010b04031e060203041406060a0e0a200a0e010e0d0309032306010b2d0301060e030a06020304060516030b06090f1c031206090207 68
    0x8001038254000c1c2c507940b009582900c2900814040c0580020420760076081c0800207980343e2450072a0144800d006030594040100010400104040840750641c0320340030002c1605c691a0380c44209a1b0f01c1030320140c801c882c07080c01c442d50020080c0f240135080390045031910f244501d40751482c0d821a0b402022250141d56500303441695148140c0e104d076040c98000d80f040d0b5500b420020140c0908036409050380011804499100d55007040d007550603107150141c84401d1102e103581e94840403442d092900401203094005000000d0008000300b501900f1111082c039220705a220480700501d09051242e04c0c080201c0101915100882d01243d05444403441d00303e00802695010901c2c040c001d24000f40020310000400c418840c481c0c1c820307401354015036090030201000f1441201501d0303882e200c866020400f00304690851600803121852000702030308285030844520910130f101c1d2180709060340411680d03946000ba0058a114481c040d26805100318140070807a200ca130081d000d400c2c3c202c40280155 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 371385521 1250 371384271 371384323
    0x40f050402031e072d06020708010c09050a120f0804081b011e180e0a0204060e01021c0507020a080a060509062a210702150604091a0703020c011103010503150702 71
    0x4003200d0103115101030300f03828145d603a44500a6031041140324010055181202040c4410300c00c0102400711480100074002c114105150381d64402c00000040740c618400d0310401c40040c90080183c0010030f03508000c1c0808401d41c404035001405918051410442907001e05030703030b00e200014110b01c00341c01458104900c0d2000e12210f40c85548603000851454420410007142514a1b002042951020b98408402d0150740c0c0059944091300289280741507400031004c2050303480344014000b654002001d400659540d2402241840400d0809850003622a010003d0f40300007003050b940c01c0320101d603140ca8880d100a004102d4800c802d40c0f40021032030300044040d420411000c140300320a8401003044200e082c1810301943d10716103021075403041d04c2801d000840914042c4135045032507420980e880400d21402c0a1091000402040b0105040d400e01c0007100c0c1d40024454104001c4000841130761385d5042004051515031004000314a58030b4060400640e903a000c2000c0030100304404c2680071310245 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 371386771 1250 371385521 371385569
    0x4030f0f050c061b0c041e180b15150415050304050f071206050c1207110a06050a140115021c1e080f060109150e030c040f050402031e07 60
    0x2c20001aa1107400070489102d914200d61449005000b08811260905510002d0100340c416610b240c000130441640d41072076188160b00300c65048242c201423070f4600307401507031540034041003907075140c0c50341c407090051008038144807400c00074020401e84442d040a14050002800d951010000700800c0b901002180412000300400c980b07420704c55041d501180d4a03001a0180d01400300002c0e240d0130300304000710320411070f40300486001301011b500c2011140e40d0100245c40000490014603254821403400d040486d58521442d4081d600c0081d010034103e20704034034640d020b44d040e040403001040c1d61201c40c0140e9000604042c071200b41c0700400c4d200c0715100b40241c440c001c05289411140d040e00c103000d100254440380292180462003500465915110011140f05c0d490b03011780462814000c20885440d4094180c80c605c10300c0060440c1c981c0f00d0850081010f03035070b201c030641400640b070768140421440c042c444020031441707002d03102040304196100c050381c955042c4564105420b44400c3c107880411307 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 371388021 1250 371386771 371386783
    0x191d0d2105090a03141006030c2d0e07030f050c180604170c12011407050c0102042301021908040509040c0909141908030c1810032004030f0f05 63
    0x40140401d4805699007403900044405c88520100742c004d0007150346943c0c201c0d2040c4d005072608101d000c42003134202850003100300c4035010380450309144640000500c40c010502d5101514801c1140c11050800300006400e50340040c15080c580c90070101000741a150790003d4403020b284080c2601c0c480c52450000c10340505c01c50b0031040c1609030700920a03144101c00501d00088110a8851301220340c49580c21901701d4000034101410310140c680803440c914416005001030000107000189415980c0000d0f00c0680310340003000785041c0c4003441c1040250380512100c021650003d40c144282c00d13440e0354000d183d1080e0b0003102e20a070003103004141840540140c0c1d07030142c4450384081010340142d05100000022064500016104150301954080b0101e000f0b0410554820101c0782140c40b10003440d5195048006062036080d11000010026a41d03000005041060768a001034480c40d000c8130307614440c1c41100c0c1441400010041000080c4003000e0354005142c1090825a44120170710b40541046 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 371389271 1250 371388021 371388037
    0x308061e0612010618030506070c030e03070339090f140f0a050c0a0c080309010e0d08041e0c03080306190807090516091505191d0d2105 60
    0x101c1e02081ca80752103541a00514140c82c455103907403591200d40c1d04c1880b980e038404d0100909a40010000c202840e0040400e0b040130f074424100f801d640d203041404203140100c25403055960001b0003444c0d540f0707013852071009c4a1003480245400301c040c544195000c3c920b000c2c0d104109410303035600c0406c00c0361909a84070304246e84410103100400e003015015582170031010f81d004410140380501245070401d840c0210341000c1403940303c03120000f440d502ca03994141c000030021035441d501c54052055880080c42403a0a46001d80c86d60181d0b42000d080c1301c0c0700b1090300c292100f54802010300305008110314402c1c0804480c0e00082c41607980c0d560102081c03403a0703023180b44250000c0c2c1c601c2002c2442000452a5800e64202c50000c1185d580d852120f460101d0406041101203900b0703402c18800388541409240703002c1d000d07041491400303d001003c1110090503e46040000d641d6826041051a41300c8288003c904125003162680d0070b20744401d20f461402400d06107502d0240380c50004410300490580703141d4 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 371390521 1250 371389271 371389279
    0x4121214010603140708130515040f0302070609052d040e01020d150315200708030109060503030703171504060801060e0c0304080702040209130e01091e0308061e 71
    0x11280218030304400c00c0030300500001c24146250300e84a140440200c2c0c0c4904034690ba941c00e6500d0710310b01c0c0404030b0950641070368180140c240900003900011a4a802207215003003c8500409a0500034180902900401e041204403001000342d03a4483c0d08010300000b00c0e06d680140507814803070380070039403a20005050b001810581d2100086c04194094001d0781c5c14203a061054003441e515814904002e80801003a4001c040e031451003400c010362009410001040d21088000c1c4d03a03d00d0303031905400c180710450310440c00000500c400d400a015040041005800641c104121550702910101034601072602001507080021580385015415968564024104100c0c00d03484401d058007a000500680484410306000b04001d6541309d0200d03445150015403880c14145e141d800c01011754803201da55076000c1303402031054078954031a104082e4008103501c00040e41148901e040722603000c114074110042480b5104060109410180160b4000f404540c00c00c0050480001c40070710303c901ea00c6060308 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 371391771 1250 371390521 371390531
    0x105101707020a0b09011518090503040f090c080108030a0309020a0f0e150607080d0510031703090f010c090519081606020f01090f0303091103060702010915050708041212 75
    0x1015004540c1c4103c040c002c001c0007942e0b030b568840700c40c280d503564690560002400b10040061040055144612041c06840414600c0c0152191440d5030029041184010f030150400c00c02042da5101340f424010039410120707481d42c540340030765849020f04031001040c5602c4000340002c40d40d0300300180c40036081404100780342a454103085204110100d8044c0c104101c62801110640380030380a4a800907844100d29140060310903003e40070700005040c40152450b611030120000300d4842502a203e004081d03055140d02c1c00000700741c54010712039080929030740340820030f080c030540c4040c9020540b80240e4580702d42d5407c1c07240c841d030031210651010b0f18601030400ea0040360580d03601b121003140c03803642c01c41c0e210403003c5212908903281c0d994000c0c100c81e84e040d08a00003900a801040c2c80d00e00030380791b80745141b441c02c000c40e00740380081b501d00d001030355500c01c04020003550900c200980303078841c007040105140104018010032000750015207541c002800b4018410722400c105144080b0881003402 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 371393021 1250 371391771 371391781
    0xc030c0609120c030e030105160f020f011112061801090e100507111b0102060a2c0d02070603090506070e0d05030a0314060102030a0212090102030d0515010806031501051017 76
    0x105420307043c0c10441c0014480c0c2d001d030b80c140c50140102e034040c0c101c0741e401c8200781410304810b403003680d444a480010750003401d0b440c508244c0c003886441e499000b01000c0c99558058104201d1040c4002429103204126044510300209441c000460540300c019000180341414240a240303802950030300c01044600f03110412403001d900114075640462007504540c5001e2030064004142c8604240890050340a640050340d50491900035450b41e040401e4203440010204d1814025250241104e4000d944582e0358a5610360f0b0401c50180101404d10381089201143c3c0d503610340311078014001c40c00300b20459003001c540d50390b00301d1800c08140e070102c2100e0307680c044408042e0140c0f0903030151100480c0c04030300141913540040202c400c180303030603409031013120a1401d1001441d04001086e604503c414450540c5d02507440c0f080b02d00640740c0005240060044400040c49010010035090094000c000d078800314000b094441e6064400440d000c14001ca0425812103000088144140080d680801845 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 371394271 1250 371393021 371393027
    0x2042004030606030501150e0412030e0f0115060311070206130b0c0c010201050105040908190917011a04020c2112040308270c010c0f0506010f1e03030c030c060912 72
    0x18100c85c451002440b0003200086810312200b011320801b041d881d0301e040000d001920703c03044a80c80c610a03003030005040c407500c000d451070312030310500004c540da548110508010603810002001400f80b850309200829401642807418002c0050090042030080b0350400900c41004821010f4040c00c0421a240d803c2c034080b8640d26030303029811502651a103000403c16061501880b140c540d00070072010f203043c044038010712001c5580c1c100384041006000f0041069142400008403d035026000820024152150f445800d060034200034404c034030400490509400c0030070340607110401d20314140c100c650301316280c01c0305100705281c1070b2701206800104420940c111100034004d1101556401100d030881da07002c00000c0612520012f079601074401440151300c602c80c1d1400c0075210382c0030000310708000d5481c1c3e490500280c11044a8a080c801e086c000e194943d40700790b4412005003e151940d92450320051718650740309601a0420407100d07400320501c2226000400c3d40d641c446104010401d6900d401 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 371395521 1250 371394271 371394281
    0x30e0a0902030f0f09061e04261e091804150f061403070303140313050109060f0c0305010e0a020a110703111014030a05090a02120709060807080705010e1306140a06020105070c020420040306 83
    0x44c0c44010b20110001c40480c074ad103041d600001c41c050040100c06a60a030291403103034000780211200042e8030a0010850350301c0c040c1d20355440c486500410000d0030402a0805031000c0c3c086640680c1c0030712001c01c042070b4803041503580041702410301c03680ca8a44000180e043c044152001d0b0003507007001625001c12020b540500e41d040d031400b030100b28824034184101c0c189c074070038410444401140700201d040304003a030b4010100c1d030707003e8100010120401d250a90a11030550b01c160740460054050109a0910b4007091050340070034a0300e080303885e003800d2080006000147c5000d0703455584030f0028120590030083c0c6d0030f070203400a040d8030080000c090966070320040b41c0104074600e0305103040010114000503800064504c068090442c890402c801100d84003c021318880d4415551043e04075209042e110b0744000d08080701031280c1c0d0090807001c0c44514415580712204582c502010880d4250b0b0041066600507411200410108000c4020100c03120401507028000c00001800108122095101d = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 371396771 1250 371395521 371395537
    0x618060d0f0c0308030c03160f0e12100e0321040f0f08070206130f080316080d11031005040b1804030e06040b0a080603070918030e0a0902030f0f09061e0426 69
    0xc0b810320000c54480032181c9e0051400001c0200d215074405042924040c03100c050240c06500856800d210003015413020349100401c41440382d040003500b5004079158111104a03216138602646007070034282c0d41c1e0003048512842c0500114454840c00c4108502001181c00300d540003403500d500c81c2179004680d1131001080c480d510303500003040400250f442c004401d6561614144000c0a21719201c0e44903503240740d00c0480c02145240d554651042b01090750030141d40180480b5001e00c080c1c03410b00080c4002c0310041d05400744519081c221002041310b198803a40e602075858680700418640c0d19000c504140284e4016140000c804164080050313841500d162092030120111115540e88080075030403200b408804001c4000d03220080b0300441e004606e07884248030054041c4035035655400b141c0f000c9030030594492114105d07510a10018800b11000e00e034204056074042c0c002e50070100116100044c0058035038525500b4100010144016403440b000641d4124030a902c202c3d0340740c1080d5441d9400b03810 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 371398021 1250 371396771 371396791
    0x30708070206010806090a060203090a020604030309030b2401050c1002032e141e06031302120f06061e1008090706020606060913021e030618060d0f0c0308030c03 71
    0x5205200007171460103180900701510344107800e034a620020b0351006200900a10a1440500050f117030840140000d50003955071010341411440c00b80701641014200280030588203154070b90410240b9040786080b007007401c2460703640d05c0083c952400c00c042c80c507039200a280302108001207c03d504090000e4444014500c40c0407003401c100100100e100c2d8000c10050043e81003d15050b410300a09500400507412400c0d02181c7c0100c1c00200c19a20480c0d14600700c007588100441141072040c00c0703180e041c90343d2020b00079013aa540d44141da80c50f03005020510403030800d5000c10050308040c841c10a0003101030040501c210042202920420041d10b10030f51511400c00c0004100f440030540b6070080c180105805d28105100081180d90400e203410545c80607401c0107840028444983c05042a100842c0740135207a02d031003002c10018130f1100801d206202400c2c030411610ba40c03200c02001c034496010020710010352841c14062860343c00740d000100181400818002c41e0074000019610617101c81e0 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 371399271 1250 371398021 371398033
    0x1403060d020a3507120317070e0108060102241302090109020304140a0b0c030a0f2c03040f0504111209030711040902030d0305150a030f050709231b0307080702 70
    0x101078460f00b0a040e040450180c0c100079002d01020800740018002d25010f45401181005140c0700314140260903200c0c08046060300010b05042e5170001b028540c0b181090019040c0c030b01f4000b200f0b00c882c451212008000050741c2d000a110444403c0040303401d19006004800d0640c0c54104072780c000d40c001d07242a11100c4030903a803903a04510014a01d1101c603030029048010342c0707890301c500d00c06410140400117072030b8442194031088500b030301c140b05c000000e043d580d400d88a81c1d01405c25000303c624600707882b103030410002031014580d494650006c6802c240c60002e680c101c81c44c0e840143e401100701d12440c1050320b0091000d000000005015020701840148000b0001c2c0d00400040711510032000b03400d0742080c441c0745505402036011641c0184204000d48401000e000010100405904101c9680d202064500180a010001c040140c04100d400f00b0107080c0200c0c0103140784802943c2000604912000102452204014521403800d2681e40703079282d040860011300004400c45010005200755 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 371400521 1250 371399271 371399339
    0xb0a050706060b0309100c120207120e120d050f0c0d0c03030b040501030c06030504020d021002070f080105101203030e100e211603030914010c09151403060d020a 71
    0x1c02105c0c007901220004028038180da41e554030203000204004014449500a244112039050000f40100d601c07a07250084030000d9140040c20420a5200b01402a65021601101480b000624001e040400d050003500e50100e00310341445482800c100302d095008072100410304a8000c0d42c034014042c401d8030f0601441400e142400200c4c3c00900c006828000c0c103070300400046000780d014070f0b005130020f400d500350300e45070b074020550101507900443c005038070122007004081c15011500340908414030090010307040003906074003542c1842c0102c00e01c4a1000c20070b48101070080d1300c4042c0c41012101915040000c107038000c00200081c1008001c04d000b40b100d000e0b40380324032403006610650110007460420b100d4140700340c4050071081084040c140d03581c1c230307807408501c0c0782c42241c04100606001040781100c1c50700c01041548036078403010a80c0030007030500040035004043c3d0b00c0704007141c802413502c0e41d8031800001c800003a006030294222808110100da1068025a00d03208031000d54003091030314402c = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 371401771 1250 371400521 371400539
    0x30e070602030f0a080718080f0f0a0230010c091d040201020a0314070203070b031e13080a030f0203071e020d12020313080a08091606081f0b0a05070606 67
    0x1540f00007141c0c0c220104074084085025102c02e039004a07803440c20440c8110348542e082d0144c0d6903a0404c2c22103138050300d44902458000c021501c0002e88400180040b00303142d902080d01648680248024402e424010030044d0408078071403641494800000d00c030302a904207020300b08140d14081c4055200c010403640320488205d4040902895040e4014000f001054600f2100c5220140240900f0031041045c100980d40c100400006001d0703028500740d40b42040b24002005c500c0390f102c42c502c01d080071020820890710010b00b008500d43c002202030b58071005208110002c00c284050020800d1020007409445540000c00c45261120402550110703200c5402c16071b40c4943da04d40c4c001c0004c040c001d48204441d0343e0b4010f1034014400d9403540d01c2601c1c96031749059030364004404d01c07030002d0b0b40380d000c0141500040000760f00d68403407110f040c040d80741401402025400d00400c0b0082e07070a050074240c1c034010080c201c0440100014160191151001d41c1e009003203900c903800584010341011008181031700 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 371402877 1106 371401771 371401777
    0x120f0e0115051801031a060307120302030a0f111009080c1203150d020f0616020303040f0f0503032805070222050f04050622080a030e07060203 63
    0x1040c00203200b602c003d1400500009080b80004201203207030b5070111101098150130a00e40b03681d8503130100b032030441030f540700c001c1e80e441002c0e62a050590100240a520010755141c110841c42180e04860a8441864804c41d0ba00700706d4051454022950020740d08030300c510301c00d508001c84100107506091410500804801c2c000042183c1c1c180040315952080c0c5088a10001405040e004a01590010780c0c03102d019900010324884045028043c4440403a4021304403a40c49449888070001156148506c1d549040f00f0706022032980f4000c41916400c0c0d51802c0c2c01c44c00c1001e50140801c045450310300060a1000821000b00541c0b0b50380043c002c3c808850880c0000c40c01d00c209203400300c85009041000351881c0000303102c00240c0100750290410b80c5c079002211030005038402e12510540000300208100400070341c118507190541c00c5030600a40080507143c0c0c007551054180c0c4c41344 = true := by decide +kernel

theorem cover : BRFrame.Cov 371223021 371402877 := by
  have h0 := BRFrame.cov_init 371223021
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371223021 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371223021 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371223021 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371223021 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371223021 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371223021 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371223021 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371223021 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371223021 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371223021 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371223021 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371223021 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371223021 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371223021 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371223021 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371223021 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371223021 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371223021 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371223021 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371223021 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371223021 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371223021 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371223021 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371223021 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371223021 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371223021 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371223021 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371223021 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371223021 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371223021 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371223021 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371223021 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371223021 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371223021 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371223021 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371223021 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371223021 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371223021 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371223021 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371223021 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371223021 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371223021 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371223021 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371223021 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371223021 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371223021 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371223021 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371223021 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371223021 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371223021 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371223021 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371223021 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371223021 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371223021 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371223021 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371223021 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371223021 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371223021 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371223021 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371223021 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371223021 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371223021 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371223021 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371223021 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371223021 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371223021 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371223021 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371223021 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371223021 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371223021 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371223021 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371223021 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371223021 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371223021 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371223021 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371223021 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371223021 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371223021 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371223021 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371223021 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371223021 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371223021 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371223021 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371223021 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371223021 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371223021 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371223021 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371223021 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371223021 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371223021 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371223021 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371223021 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371223021 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371223021 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371223021 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371223021 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371223021 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371223021 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371223021 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371223021 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371223021 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371223021 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371223021 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371223021 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371223021 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371223021 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371223021 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371223021 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371223021 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371223021 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371223021 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371223021 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371223021 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371223021 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371223021 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371223021 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371223021 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371223021 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371223021 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371223021 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371223021 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371223021 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371223021 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371223021 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371223021 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371223021 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371223021 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371223021 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371223021 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371223021 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371223021 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371223021 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371223021 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371223021 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371223021 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371223021 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371223021 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371223021 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371223021 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371223021 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371223021 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371223021 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371223021 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371223021 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 371223021 ≤ n) (h2 : n < 371402877) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
