-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2106
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T05:39:45.888106+00:00
-- url     : https://prove2.me/submissions/d8e0c00a-d670-44f9-a5a4-cbd4a7822e5c

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 378597122 ≤ n < 378776978 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 378598372 1250 378597122 378597133
    0x809030f1303060e03091315140d0203010c051b010c08040f020a0308031302030f03070b01060f1715010f0f020d0507020604030204060b031006140a0c06021c06060212180d05 76
    0x426034840ca80301000d2803001981c031b440701d000c1005900f20407403c8941e28181444104003d405819060105a624480481e142c1c1003800c030100e9030081001501940c10b600b402103038620240c2050081071070780c600c0d00c403045000704101741250036580050b400000080002c030010340403411421400d1222407000f0100060513580303441e8030a00303400582c0c905101c142c0c40042c9904600e0100800748070554880081e505000054551060341d40c0d05110311403d101e175142d44080d24510800d40c0c05020031507210b07240f100742404910190490713001400240440ca030141410b602901410001c0c00822190f80248207070044264111029040002c0890300000705001c003000580d1540656400341c40c04603040d1361a803900000300e40600030f02d03603c10010b0114401000030701140b020200c0c2e2008180d41025000c910741807038154024070a0441c2100211400c0c047c800c0d00d110690080d1080b103200d0b0742101d0758000703000c2d81c1c0740d424828920f2620320a20031f00c6156a003820300d0030000c12403a0051090741c0 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 378599622 1250 378598372 378598379
    0xc030806030c10020304050f0f0d1e0501020403050d080705180402090d0203010e010911060301032a1e090e011104090b03250305060714030703240b13060809030f13 72
    0x342142d80310742003e40541c10104050105041010b003640380d00c101254180c1c1e80e22003400c0810860149404068600c0501850011445414010240c00316070300200842d5500c2c1e40e82001a160700308180f02100041c030b00c0d00801e034000d2040c800c0c0c901c10840e030f19030480c0e6448c42a003080000c1d40f10300000354209018041800c0541d50a00c00c0d03440c10180c43d000800c90f0340c2c0c9450f04111400001c11100d1284e0418401400816000c0c0c0d041c1c4100b60b00a0910441c42c0f80c0400d400c030b6545640d43c01000956040c00715142240c1d6800002e208032620041c0c00d01c0700350482d502e15800d0f5400540d290b1200c60052104020712125900003c00c1d107003019081d29080da50b991580c2101000ca022a4800c0d0b1a82580401c00c00c1410000c041d03008000e4039140340050321220f11414944400b4000000b050b450b541e400780340980c1c00c07100c000810360300341401e042e9550300c510445043c0c00c180c821070b41900c0f201034006400750050350326a100d060030f000a14500b01039030720a040b040d0044007401001c01d110341e0700407 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 378600872 1250 378599622 378599629
    0xf01090b0426030c03120a0f02030405012412021c0816120203120f090c1c0201120504080f0307051225020a0201121a150a1e0c030806030c 61
    0x800207403000901c044445040c494640d01c5810b0a420552a140d0040101034213000000c015262085c4042c05651119155803485034090500821080510341c4000700740000c00005510a141c4405515145c11f400040310340b1481c1d60f042c15202d033141c0f1080040c0b44100500e42420400c02050200501107010006c0792588460b9402140c424950540c40c8006102448211002600582c074280700951030024245210000c042c4082c19111968070124041001142d06102c40d540c0700c40042c01840d040154016090064030000c001070f40815001c0d03030070010461075802020b100c1c9401c21100352400944d0300410710258002400c407802c001d4140842010480c11088641c01454039a02089407110981c030100d445010682402c42954001003580d00180d0304083c207081c01c00394000c00004d192800b0f0003030780610036074403940a40c000e0100100310101e502c5c00018005010301940c80c2800c03c01101805041c500401801c0030120765070640080c0003c1c82513100d15400310000c0e09441079010100c021 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 378602122 1250 378600872 378600877
    0x209041103040c0509011509090207050c1201020a14070209040f1a15120606031b010e030a08030109061d2d13030e0109060e04021809040f111008060f01090b 69
    0x4035110003e58008210354a0f12151312409024500001c001200b401b140c05030860b1b0300c501c50103405540100f8a0014000188403c5407070702c2003c0c1c40d44440c1005000302600035805000c4290111781070f80c10364181c030400c070026130383e0840d805820000d00c0d80b80e54446003210543d00f0710480e88151602c000c281e131005183c003100c3c007446900714150403080c4101c1c01c001005020a80c84080e503480301d0100015950001500d0108000118844001440c64030048801c09600300107a50144a666080f404100200009604175070070b00340d04106213034503001640c0e843c19050142084080ca030102207041447c050401c5400c10301d0a40c115448000d0f102c030101040c10045441010120360303544010705160308a045610024024030b08000901e04092018040240034441503024990108402a00b05800000030f034003080e0003014040c80345020319104420326900102110003240c400b03400c40060400292000c459880e80e02d0708a400d0350f90174140194855102004c41c104881d4144c0002c203030348540300 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 378603372 1250 378602122 378602131
    0x1e181207031208060f010e1f1808120d0b0406030f03030b0a150504171516020d090308040b070c09020310030209010b090d080c120d1406041a040209041103 68
    0x290a0031841c50401010403003074902e49005001070001001100d0781c5280c02030001d800309090611901d4100c0d4003280384d6950b070f0080d0241030000390010841582e0400072a001d03908017042502021074131000e2a50300c494040c02c444030511400d21802c1a26913040d0040c00b4000c00103080050752555a45410740210b103007007401c0c0c01007941d80c0c034429400d0400c044000080d00d80302c04265417508180c0340c010031610840c85a40304890700c4451101980320140700509000c0c034035101405c014101820742010030304200807050054400c03038990741c0d861406842110100d9070014880d41c2014a418819184d9900008080381d10007030218020440d2181c1e4401f540c05021080040c040c03650551042c803c41140603000307089404818420000d449d519405000c0d4281d92041009881d082c1b00403a0614007031a10300c01c015401d5010400e070320240c6181d0321598804498511000d9203441718820f2004503481c807102e203a80e01a000040e010780741095001482c0e03690b0081c100041d49002070610400301e030006d55 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 378604622 1250 378603372 378603409
    0x190207050715080a0501060906120207141e011b0309050309100806040b041103180f190317070c03230301030507080c120705010c110402120a111e18 65
    0x105021000f94401d45165000070540c004210360350401d0320242002d00c00e40b05040800c000720814204a40540d0140c0d004541d01c124107102080c4444152504c80340ca00c0c0c00c2c41084110805c450350030f420705004c0c501041c2c2c03140d003000c03810b0340c42d00c0c504401400000b1010351745880100311264103511411444001b1003100c1e9a81c4030701e420001e080009a0b0400e669583c0300d181080081e07034800b80d08c10116500200e03005240000e58549000c15400c201c098480c03941d1900800220b0902d05400e1180000854400ea4804101d0b0179244400c03011814241d400d0000110648510790000780201a4004100880700e0840346405094110f1100c0e03603c00d030001c460741d800c1341004000c502d80c108141c4080090460340c9510161403e18820360354504e92107281d04000b003400d441018407003c2071852410300d10190040d5691941710311a00d501410681c1d17005103aa107840071000c102c0c411a4140c40003488640081501a18140c110300c855412802c44481e40362a004202902581c0e20b10340a5171404944 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 378605872 1250 378604622 378604649
    0x50f0a021b04060602071206060803070f050c010809030a0815040606090f0605270d0f0b09120a02071e051c151103010b03041b1e0504020f031902070507 67
    0x8891007291020303400c00700740c0038906003502481003e8001c9442402e560003504500b8102445003858400b134501b0754889031142c040000c245e4103100202004281d0750340281e0032a10340d110003a004480140d4112802d101d10740050000542845c0700f501602d030040c250300c065010b06505000041e013200c419501000c007040b24014100400b040c1f000222004099604200d42003420000324401c41001440104404841d007a1078404596658440b002c101904400c503071a1958251403d01044501174904170b010384540103c24850450000840781c03941c220317074080c041c420700d0110900712100d01006041e032507461200d800710312602d400910104140e00d020010b041c041c928106018042400003035011024248041002c2d07040411041360304642110b05070a41d65950760400541031003c2c0c47e00e980450035021030000b0099994582c40d1806041da51200317000b5030780c800c02c00c000c07072244c804031448580060002981c0740045500103188074907045005850410700f603841904081d501d412295444000c1d = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 378607122 1250 378605872 378605893
    0x6020d152c0606040b0703030609021303110907120c0c1703040b150f0909010f110a02010b040509070e04140a080415020a0308041b03020a09051602030403031e050f0a02 74
    0x10390030000801942455005050600c4400325200744118050176210390340001c0d0640070980709520203170080c00100401c41d251641800c82038283c040034401907031412482000c00301217242c12202103010300400d071290000c0e1122807650034007400d1805900030034001d0641d0000080396000184e07019107400183c8582d0742e4a03261800d035031003c00184c040d500c1000105120b506640343d070302d07900f480c0200854000148da43c4010225003d061045003110740d90341031116204154801c14080d11903440207070024002c0c0400a030030320040310012106105030760711072a0200a103412258060750424000e42ca503401d801020a1250700d002400344085401c18000030f007c000b9103d004144003414030f05840544251951500d00611146020300003600402500c41c0580c0c000e0b03842c490b42c1c0000c0d80d010345118111551740d94480010141110610100f071501d59100035224404411101aa40c2c5a00c4900301c0d681c401e481d250380e40206d0b03080f000901c42c00b0000035500003940c07005410500146d50041080c0c402 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 378608372 1250 378607122 378607169
    0x91a13180509060405030702040f020c0a061506030b0622030b090a06051005090712061a030108010c0320030a0207141b090705041a070b01060206040605150d06020d15 73
    0x50040084020307030010f00c01c0c00f00003100401103807034264044601082049039649800d00070b04c144501d0608a100d00c900c1c2808203c0310380c000311159642201c921081940d14502035041c0c0b0421000c05600c48420002c0b11510f80220740b084c00810380c034012582d006601e90b0b540300c240080c20745070040b240e40304d43c0240080021031300903c2e5004000111321182c0901d4480481c0c2041000b17450740090200c2e185c810b06000c1d08507440a40105002402d0841d018054401840305610a00130b9031025400c00d803956100034003030f001c0c81d00d101401271008805004031440340e00c0b4940001d0004038007280c080000c0c00100c1c81c0c0400705102d0079200700203001008415880b6180107440366140c68041d1302c040080004140c2c200701a203007114104159903494040c01c0120350064483c2c80c070014000e041400000c110554001903c611940c440d040c00c00441c0c45400e6411038028440d04203641c0202d1900280d800243d103074001d042e40c0b070300164001c6117240044151814803a40364001002d408140c0c243c00f00c80b001b = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 378609622 1250 378608372 378608381
    0xe070809060c0f0a12090b07030e100902010207030206071b0b090f040e19140609060603070b041401051c1406030d030b0a140a032f030607091a1318 65
    0x28184201038903103000000f428900e4050b2001c0542803140070105a60b03405803d40010469136885420610759103400c11001c1c0c010080740100007018480e03c0a140e4070300540d81700324002250140c00600c8400e18541c2042403651194204464174200303402d044006540d0504100054002c1c03d8009841d4003e40c1300b4840c80c048100300f440e106a05168007540101804550111009410346d00110700303032520304080d0a0041c1c1407550341f0061068a00700590082d011034850b005401c12025202042c2da03890f0440e650340034500915600840c6d07110303040e01a6001c1c000414800b0380464212200f001020ba10038111480f0100c1104c0502c42e80d410004946001c7c0443da15081441c1010001402c403e03002c910f2210b1076001d240c00e02901d40d5542501c41d40c8402c2d0107030056900184400200c400c8171140c660180c541e060702c650360740b2001103082240c84c0104080e44039260a65444402c80e14220b04a8007020043c0b007200c1c8000010803001000d000e05207900342c0505041200d00d451f5540800c58030003104c = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 378610872 1250 378609622 378609631
    0x190c050f031b040b030f0618070e0108030a0e150a0f020111040315090503070c0f080705090f1b0f12011403030f03041407051f020f03030606041e0e07080906 69
    0x7a04200315980b5207034000c601402194009440c00a201c01c011000301c0e2520aa01d01c440040d4401d072402c000380b03840c4c0c0c03002c40f120701340b000410f48155a81d00c02d00000c003c0000c3c0038590300c40d0020b120840ca2503104002c030b1030ba0724500601070742020030b450a0500b82c5d5030200d0101d500040e0003180580c0c1158090148152102002602c189007502c0c0d6140c0600034141c1e40c03290f002c42600c40780c610040c001e00b003040d100c40e40c0e044080a155540c0c2ca01c4a1100200c061080d50018040c802c8000340f6031400080052107001890f8002e030075035450070811a8003051502c1c440d5a0680c0034072009000c002c010002d040035800b50300e20501594107100c000500b074400c258441c0d10a81c010044655038140b0441a00c0d04203510101800301c000d0307003034111424036001d500515003010a0889101d400300704031440c8403850b100f9800380c2d00210030031890591644400c40d2011b030055420041088101e0700780055028010400803a0298240c4580f020085110140c0e040000660380c5024040021414031116402 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 378612122 1250 378610872 378610879
    0x8010c0f051911010f020c03030a0608060f04030e150d240b0a0f11120301030605090c01020c191d06120313031e0c06020d03061403120c190c050f 64
    0x410760b0b80e0741080404160200c80000b00103181c0c01c02c604090094105c9600310400600944d201c00e10303100c48990b6504201c0350640843c1c2490300004000f58003080c01c60182301000a900501e94031074078180d4000c0c803101503881d000342c111040c507583c8003012000f81050500180c4041510501004401948054001196803005e01120301304400d40116080350300c000801e0401c0310f1451b400403070548403921003043d4802c07140160344c0701110200d003800082d030590707104403010401c82e2a8100c2d42e0744d481e645003540c030740035070302402140b01645040c40680700004e00e41000c403090940c4030800c8500e02d4550811900100c95404144800c0340b42c201b10a801b60b58451008600701100701c100301441c0040c501c000381641001d844a641e08680d003400c441e00071038102c48000c45943da600b0b4000d54415581c840b040003c0c0c5010404560500103103036022443c05d0080090120446045000c0400d9120030b1400f801445048103128860804442110110b8050072648010301c2c5080d060103a02e000c103042c079510 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 378613372 1250 378612122 378612127
    0x40302010606031d0601090b06072001031802100305190912080f07080105040c1205040b27030904020306030705030703050d02010c111b01030b041416020d0c20090108010c0f05 77
    0x101003130006640e41c1121407880e0f000c034100e641400070540c0703407040990142031001d45000900d00000381c0c0c524011045403c2c2d80403c0810302c0303d004a42c4083d04e9400095102c0014440000040d100380c0160350002c900405d5655101e07032480050040314030011046482113810960f40c280d5035040248250306c540302c0d55117001b042c90070134030042c006072050041e10710555881c1e4aa179819882030b4501040c0803030b291800c1005041600301202e0301e52040b5140d1000035014018401400c4a80e14000729114032100207508003004001000003130b400c004c1c180c5825200d0210000380e550741c10070030500110b004002801500d80025002401e4404e009112414410049540043c08600140614415403a091145201c010f4400120702901000f41d2a56000703090811400300310550200700d074020325201d00b00a441003514001661070b1740c521030240010440c07000c00c003030108030141211401d01001c0340ea440c1508081c1000a40303003400a80217107031a1b80d5110050810250801034a590100ea2800d0290 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 378614622 1250 378613372 378613421
    0x90501182603060a060305072609060c0901050405040b15040b041401080105011704020111060c130f06090b03130206030a0f0e060408040b07031101020705011b080c071e050604030201060603 83
    0xe01e028084c0c805d0384100355590001038440e9204040c500c213582c021303100d0520301035041e100340640980140e40501e00c0d4004d070008540924804011105120750607120142040c0c941401c0100420140c0002034101e41c1c005442049044400000d00c058502c0541c2d050701c0d1810f01200040140000440350705100c041310040c04070740e030072110b8102c4aa0f0284240341c019900ca1004031203041005400303020501c01c0009000c140620308024250b0600c0240384943c0d0703e40da640d403544d805201449000085002c041d0700b401709502000085074411030035240e00d21500071950115031301d03500483d030700c0c030b0710b1541d6070001002615031707001da07440107203008005003014207040c0c680d40d40c5442203220340c000301c00000852608160003001c0f81c940c40303481103008544074003550800c140a42044170681802003512010003080500901d952805584840662030504800355a03070150070129182e5140c41800d40c42c01d410010303204010311403042c0d100346c0c008102d49141c1000541136805442200411512590040303 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 378615872 1250 378614622 378614629
    0x2a1003050702150402150a1e110f03120f090f0a1b050907020c1c06091101030c3902130f05090a030503040209180303161805060d09050118260306 64
    0x1c0441c0142d20b60800e5880640b41c0003510002c1c01d80c0302c001b04588c003a00340040b255030444082881010544183c0c0e0030020800d6105440b40300302560500e0040c001c0c804140c42d003000d10902940705c050300048442002c015030f64185032480d0010112880c0e0301d09031003e0b440d007002100d40b00040c013042c0d1b06840e260500650194131a0b03903d100144c02403100c1c0d5101c1035000b450031058400c0c02c0e084407040041071020706210000248000c0442c0c0030a0810303411140c245e21652240c401c0015510382505200c03403e2601003c0e070540c031030440f0b00e25081c245401015030303034541205054440003d0005011007600000d20183d0f10300504801c40c60b04062004004a81c2007001c032907005c2e80c1241c990b400b640c0c0b0032150802440300940945254400403041001703026030b40c0c800c0090500c203926030545075840c00064811100250207010b80054003070005080fa40c5a5800c0916414031840000c21011020880d2120980300c690342136400c0c00b2001ca400b134552100140c00452014004002441d510785400071 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 378617122 1250 378615872 378615889
    0x2060c0c010f0c05031801051902030903011a1008060d0c0909030f030e030702010e040207050a03020f06010504060b0a030c1205240603010b030103080c07050337052a1003050702150402 81
    0x200c0e22a034206e858449416880380044856901f40e422240701ca12500c010001d50701d40062a066000398a40b42a092064000710241c00c20317100000c004007a0b080d8134030f0303040707401401c0a4903c83c0c0203034488004800007190052000003809141500041c84030003420010701820112246c80241f500e80305400f0446580802104e4074507030207080c464401642003010400910620720080d20030300030001044201035010a00e0302c030300100c81c0704443e0f441e62180e0030442140c00c1c0e0b100f01032110b0710820841d84d0300c13400b0750802e03034012815060410072001c01503e404261002150758074203c030710314404060070301e551450a091201083e91001e003598107040000b0720510041c00701404d43c4c2c0c40440c40d1002e040c02005510050400030301500c1811302c00002e140e10f01d503d08401001e80c000c0e640c90100d030581e640b60f200d41c0300503040002000940f07d007003000845080036106101d03081c9001300c000115078950660000144c01c0c02d0b900010645420300d0020700741030340c190b81002490401c1d0280700c00b42c0da5400c1c2 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 378618372 1250 378617122 378617137
    0x2a04090b0112080927010f0609090c0201020c0615210d1112040b0702130b0f04150503030316090b0a090b0315120c0310090b0103060b01020a02060c0c010f0c0503 71
    0x8229584291420b00da080744c06a0100c8941c8000441003035581000d440c9100e081815010742c40310500e03622540d0302c00e1001a00c0c010040055400d0904200034440740d00110038040342400014604031b0803040503400c0043c102c542c0358101030400e60306c04141c03e1026410342082e10030500c450f00114041580380e124040c003540002041640e090b20448a0014030210086245004040c3d07a155a50200e044864018400c1a441900c1c02e004041040c103032406660030380b000c020040c0d00042d1441040100510052084071000350200720042115201040118024058404000482c0c481c090380100030683c6034200396612041440f221007400d400a8025041d43e4011f00826140d40c0e400b0100350110480542c000e500c042d0302d0150f4401c504000c1400020746d48240d040d61841c1500041820030366004640c000c00c1030100100400100340141c0c0300d440c0015052040d105040280d4000400f190429000038100b0f401100c03000d809903820048201040d0307024106840c042105868158480c0503104 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 378619622 1250 378618372 378618389
    0xc11010e07032604090506031006080a17090a0e040203010b1002030406050309030f04061707020304060c1103030405040213090606210b030705031c02070f05060313142a04090b01 78
    0xf888000d02c4140d0750402c0440081070116662107660311440c0343c0241070150707503030303402405010048900803405008103020b54003c50018404501d031a602c01040140100c4c0751000444240030441d0141d860303030102002492081640700f161f041c5401010308651160780c04074824000f907012800c2054010055030b0458a207810070544982d1112100341c01c510030224024140340000401007003203074022074528420b03a002d8081c1016a900c1c500241da891049001d4000425644541000010004010004071180140aa908081d900c0021409a8010202800d211102000203202c890800d10a4a0040500d4a80001344807000706034141e03d212400c41c00c00c50301d512800e6144464404000400c002c010180880d401c00036031030200316002084486140040c0941f4000240300d07a001203080d03003512002800f003450340c1c5074120040911641f106048481010b0100e0210459500b07011000c0b2085598054554506040d42444028800260308601c990319008a44000c2110703100c10505455080 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 378620872 1250 378619622 378619643
    0x20a0e040201080412050c24091f0905031608270d060f091401060f0f030c0e1f030605040b0612060708090f060a0b040605150306040c050d0207060c11010e0703 70
    0x15001103039903100368600401d4038484c1c480c54059400c0e8001c41c1d04000717804280c3d40405522907034501c2b82c8681022170304480c81c0720f1035510280040e9143d40614a554890001c9038a031055941c01c01071883c14429056922400100300300038801c0301518100303104500600c0400c85103280d4400110360b807002d12000752020f5a28042081100720135840414441e030801d510000f011940c0d00300074080d04041c09050b00c0d02d0300c9110000340c3d803441d01503100300352039001c1034000b403107030410000090b1010700a080f40589103c0c00510503e80e00b1f540344040c0035501600c1c011a8501c0c05052181800300050f10450107000300b50b0419540031004540150866071a01d84110551103541d20740d8580b03d00c040400b01756000d282c3c2480070540059000d0506048142e0307080c06030940d584204061440319440f155542882000000c40c2850142e001141858403030410b1420038035460b5028049800c0200112130b03180c1c0e01c01034101c21a40144901e2003040015000b481411940882d00703440da0b207103120013044516103 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 378622122 1250 378620872 378620903
    0x5070e0406020918040204202710020c01080114240408030a020c09010602030c0303010618031208041b080703030c080c0102070b100b12010501052d07020a0e0402010804 74
    0x720b804445901000070a034402d416115000c0b1030041c0c42c00d60301244164508680b10540c14041c1c21401c42030348940c00c0e114180304000b07859958001005c40301e40764030f84150601b89030070781e5186440071001c079180d03004048042d140400900031501c10b030840d4500b00c2004140e0303071441d503e001d01c0303001030320030b01244603152219203280c103415001d1a0004003142c000890512442d941c00205900300c00f00031a0001d8403a40c0c1c1d860141e0b01c0b841500a403407043e410802c018010b9038040d9240100703891000c0c400000460366501d90030141c60311140c0d400001080303c1c0c103000612044000011000c0c41e25100c4000d814034011600e40d990905101c01002d101106020f0b10911000c40c0c05c0c2c5400c1c0300281c0096645072924902102001c200321166013800310684d00c00304030a207819040d550380d44503142da0981d0b140d09040056030f4131b03049070040c803003c9031906030140e281640480e03003003e070030300c3c0510f41d50b460300124810481e0500c039075004000d244580904001c0540ea1104140303812640154004440c40b88 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 378623372 1250 378622122 378622133
    0x70e01030b041a13200310140a050c0f0c1203041a10061b0305040509010b0301052403060103180f141b0607260708030f13020d12020726010b0102070305070e04 70
    0x68602e1720640c10301480d42c00b0385410007580c02c02c9401d0099041d01e081c2950322008210125081903d19140f4014280146030301d40b6886001041c0c1601d4503030850381380d01070007542d040c00303030780200e504441140030304290100d02c241e1880d0194003d81d4045c9100c00d0941000344c000c1138000005000d411070315004840c68203260184084602400010b0907405082d071b15029115804c0d802031080c1030162000c020b919501000401c4203200792071060305132600d5074949200450150040baa4640700c1100c0c02c0c40d4413400242103480d84050b862081c07609401980000f1259420810074170001450904038941084032a6114811070741e0543d03100071007541e0303d0915030b41c01c42803500c0c02608050351040007914501784000d080145100b54452000080d5035038801c03010008123410050025040342c14604140e002030100b5000c200c05400e14070450350700350b544004402640310b200a260f000003065007200e030845c200038012001d41000a0000340080c1307256981d050390343c01103489124060700340f41c2d0202d0304100 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 378624622 1250 378623372 378623423
    0x22170c01120e07120308090718050402040e031612020d050f2208070509060a030218090c040f05010e01050a03081803150705031e100e09070e01030b041a13 68
    0x49882c04440032503840300354112404005190a80101d001400012504480003460000b641d09413618440b800f0744030300040c00039040140040382d201c0d4170b403c10900d9001081001d0071050002002d440859110b42c205800804c0700640014119000080d280c1c412641007000c842248600c22000c0c0e61f01c0c901046245a61b0341907805601c1070400701c05000502c18400200d400035640d08444844407074481d8804c101c540340342803000070740200005503200c40c2c0d111002402903112100c0303400c0d5841e40c0f0b0100c0000d81121403042101031066500d40c014011015010b483e50701500c004da07000ca41880c00e50b203c11209002d032400002550a08040041d40c40e24140328585051141541c000510305103130001600036041110303010007465269040b00141080300303640d14028441109142d460703505080000d40000c4005041458520806000040303101000c603005000314046d100e400d41070300301480c040c00305080002a00d540d840c9410240142196401203504950b544020302010065a0105a40100 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 378625872 1250 378624622 378624641
    0x1008030301062f0303010f06030b03011505010f1710090609020702030606101215060807090609061404120f03020f0307030206060f0414190b1c060504140322170c0112 73
    0x10b0001000001d094454283e2907408e4826680b424001031505001b49400c071000d80fa03190000c81e0001004001c41d5009810f403100d200000e180c0381a0803c032094030516a5076081c1e07510240404820010444d0040c2c13031044074054201c800080d89811040d40002e5a104c0d0040c0c007291203440ea03c020550f1044c0603180441038540c084805200c040d50610020900151512400c00468540c02c000f80e4418441c00d078100c250ba6103510345400643c144407088071021207641a041190b2800c200c041983e01600515075121072083c01c0c1c03150200d4640c60001e0800c11440c00038102a8000d02043d00000d0300411503d5100e802600e202d0f040c00c01d0ba0000402816040a54900c2d078a0480306000d444544501c1480350000300d64402d000c1c92038844240403210700280b520b400c1c440c4c5290342220016401d50403180e0843c1c080c10100b0101406601003078219403180c9400d150380c200f5200e0751305007041e0045100d00108040002200ba000c60030820ba500c4001c0448160b0401c900305289130400d04142d4000b600c41c = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 378627122 1250 378625872 378625967
    0xc091e0709152102160b043918090609080c011d060606031513050412090815040602220302041425021608101103280603020603040803100803030106 65
    0x1d41820b0605803900e1044a501e0440c104a0032314170000750540d01000035902c00140c800140040c941500c001c802301c255401c00d0b00990300c0f44548030126506014101070b01e80620340c40d6940d030070042140713400c4589215042d81e0311040f01c880e00702d5000c1c000c2001030340590150341040c0c0e69640c0302d014081800d400b541180c0e00000e030461000b414402980f002e03100d58401d900d01070920891480030340b0800c10034450b519070790340f2000c07031190140074215003990014802c10015007080b6415080d40c0b032284400d91040008051507508106510300b500450030481c0d401e0941d11840e04102903030b00708070b580c1c00d44040c031410302d1881a21007075171080103046090341302c0c2c5400c01c05107511a458540c9400f03400e5461070500b81018000c48860350800100c900030803120b07149002000402030368000465031650340d88440c1d5560700c2c1c008050388800000b9440f071441410456900d02d00308444001d000b0b07180d0031614269200b80f0040c814141c100001d503400e078200b0404280c00e10f0782d03044200310041000410180 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 378628372 1250 378627122 378627143
    0x3070e0403051c020d0c08060319081201063501030f03140d020406121404030807180603061707140f1302160c06030b030c091e070915210216 62
    0x642e080d540600b8900741d4150007403003416445401151f6100041d2283e40d03041c0c10820003401815002803548040d0b911030584c50b81840e104c8100440600f0007607010f2404104081c143c16500074504591442c400350700303540e8100750ba0b00c841c044c4207203403c14000140030420340300a10003458040e0203454001102c80240c15030714000b4a08940107074100c0d100c0c0e000030400a48818031843c00b0303800341c607400d0480b28290050395500d0303031421510210050f00280901000c2d41003030001c00c811000b4000a4685e588002c1900c0c1d10f018200360b010780300c2c2003070721610f6004210144040703408030611201c1c0202c100c80c40d40440c1c40e5800052508007600480c0e01120303100003070024541c415852020700050040700604402c9540e1601502924440c1c100964590485040300183d481c000a000f40c01c03050b80085404186541440e201d941c01c000d43c6c1c03800120b41c069208001c0464000708041890105240c041d03a020724443d407002514000700c031031103603081e000b0a00d0031032026a00800c0b68100d411030400c00c1c = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 378629622 1250 378628372 378628417
    0x19020d11130e090a0809010c0602040e0711060411091513091112030405010302070807061a0a062c01031512051507052710090e130203070e040305 64
    0x8496600403125480418602070002406144505103030340b160700d0382005409062410354428071158400c0a0440c140042c01007007d011a01900c0a44060700303004107034039039070f062461000d419000c0c0d01d45a1072099106100b00000100b48031131007400041c0075645819a6101c140c05112245074456110781c000144525507410302100c2c0d041038000313900134412101400a6081400404804004d1080720f5a00810080100f544203500038140c2c0c074010003200307051030510b6540e0800d540320000e18a10103105000c0f10740710351401d09900700040c00c5d00e05103030f210f01c0b400301c003040000d03048800d5024040203000c18001c084c0e40250031200202645280032019141c03030b02c494441003012070320152118441d00b104030000385105c0d2084e038014061600d4043c188007203200b00b1640c00c0244800e415910528001a05d10b6840c0c0300d502c3c41ca809ca4607181c1d030b20841e04000c400c1c0d07860b0700000d164107950003000c2c40c1200542c0f00070680e181618110000700b80244d845046c08d980701c4c031030303210400c007808000020309 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 378630872 1250 378629622 378629651
    0x150507120918051501090b07030c11150c0c010f1b15050f0a0606090303140702120715110c150d02130603060501030c020c2d1009050109080d0819020d 66
    0x107a100d114243e05030146410144c00445203a9580d00450f00005820070180011034091200b00d2a00c5215008a41041107904081443c0416549100c031042c0d00204e40e4081954003032108032a001001e192645100d1306441d00101101c0403130406504108414803000c0600140f125003680c5d032000d000c003d003c1c0e800d02e1310560b0030003102216401507151502d840032600d10305c100f44000c01caa40640d07510380c9004019000b000964072156003281d00040c5c7c550940311300001800f1010040c0303074012040780a82d0300d18801408011413441c1082c0c554111000b41980da640d528140e010f20f2802c942102e0301c0c0c01a64483c90001d120303044813503264540ca041d0018540340c3c0354001c2400d9800c01c2e64144004400420160f0703485001aa24541c000840c00000181c803a0840583d4a440bc0320020501c010400d0000701e07010a41c40c1303184c00c0c0050f9401400b4011541c00c162443c00600c111001050714040010b8010001301020f85500b802c1161041c03160030304034158065810442403610104079480400700c50 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 378632122 1250 378630872 378630881
    0x9070c03020708011509050702030c06010602060709054e03040321081503030708120a0b24030709030b10081221060a0f030b040507150507120918 64
    0x440c0107208540c40803403040c8041c0658160150311250b00d03c0001d003010400700151034010003000c2148018403e00540400800400340207011a401800c1c090500380d00090000d001904814004c18200383c1d04844450140502910304035641d00350300f0a080b2801b507505040050314004403000d0030260b06c0741450680030008000300ca2040c00e6541003400301f02d0009042a001c05005001b15400c000000c4144400e8001f880400da402010360345490616a100315558200419441070184002c0801104090910903490001000c55000c401c3d143e01d00071038169210305140408050401001040031517008030170000c05141c0c0f103c0c00480f030345826540070055031502d203d1004e071032040d070f0406a03400c101c2c501150481d00c600303c1100000c0408000107403c0071005810541c010000b1200003901c20007605031500958424064401242400d00f051854180c00f500107486406071000314505a54001d0f08640c3c0540e4000f800c2d120f0040340724402e03a07005640da8844143da850704003048120f070000b0b0b0712 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 378633372 1250 378632122 378632147
    0xd0605091501020d110a0b18011118030309060d0207060603060e0115050f010c0b040c05060a051206032a03070510030204080f06010e010e090325060b120601120609020907 75
    0x8464010052030b1040f180038a4500c2510483d80059145401141c0081d1f81607500941088203008114100a940740c02c580c80d00c01c0581408901051a2034051484100349404160480085007050b00c03000004615100b020104000e0035400150442044810707080f010003150443c0f1f041040101c0c07a0040f6010b4100302c1c01603c07103c0c402c89408540c81c649203801c03012011040e5940c0b0084241c80d0386143d406003018006580c070004403000091036a0b1004014115000f15540311600c0c0d0603108401242101c01604241c0300e0703082540000002c2d164130603003502120044a50345208204540480d0400085800440d0000a480d583c207103200e401d6002002151403100c05c403007000202c541100c0e2146400c2c0a024401c154400c010004045010a41500a8070440541e46000b007454058070584c82e41808a21200400030500c00a02c007e5214401c803100040d1101803000d4501a1200c1e00d0702c2e014080c10602030b0010880400f4805541d000c0d00681e030b80a4810211410300f01300c0078011041c82030 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 378634622 1250 378633372 378633377
    0xa0302090f040e061512010e0f160501020c21010c18050105070f0201180e0709090c261017160b0a0507060c050d051603060512060c0d0605091501 64
    0x4210514a0520748034030200c00c1e0703c00000e07080c507407210000c00c001c0c0c00e003038130300598001140c031100d000f4800203203d0b80303400592410092440300e41c94407526040108000300a1184034807074008015070398010a0445403c1c0080300e00340e904184a5111003000a050941d0444a42c45c09150031001d6400012141103c54030210040314156900011201481010707c0103110008034280398005500514441c011700c00ca51f21110940360715051650300d01c03c0d04503802c000082d1000b00800c010f080078070803801c4040003450800400018071000d295000004243c88038400b00f00070002d141503054074021405403510080d429440001d200800f41d54050403080302000004102002900c1f00e440411200ba00078140c8600303083c08c1341a19100006d000d00c054150512031b01b0008503c01d0034141c407801d48a2000300c0a103601040740302500804441e910b401c51802100c401080345a41040052402da121800ca01a1640c41c80e015101e0006000c103a841150004449028411181c054041c00d20000e4420b9 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 378635872 1250 378634622 378634639
    0x80d0603030912020d02130b090c2208031605010209060a0c120c021e13050711150705041a040f06050717040b090d02011106090a03021015060c050c04020a030209 71
    0x41104046060443c080203600002180e0024018180204025034840c865000019040000004521080c1d000c50707811074414070015003120111305120540180355628291004103900b42000740e541c920400511030381491a0b00c3d0f10b4030401509404072401d20b840075004030707142d420085000e080b0040d661002c88076017220810b0350280340c0c4a85540c0c2880358008044c02c5500240000085200d091401984c0e0130460512980170014414000c0c240a81c4196070b401112424a5202504298401540310380101880d01408800c99000040d202510350100000300350010210300842144210b5100c0d0001d60b13030800c030018959030080080e01c040c500a654140240000300c1d5440024400c90084094007070b41032010f0109801d0603104502090710606010541080b402034891601c0c0e022120651203a0003603004204250b0305111141c1d0603c2080030900154120110042c1019040d0013010100000e05c105181440b0040000112020015000719078514032108020040c0d444165183e0103107620 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 378637122 1250 378635872 378635879
    0x2150a02010f0c02031905070b04110906030a020609041d060f01150f050406030218150c01060914070f1707030c0f0e0d061508101d030c060403050a0c080d06030309 72
    0x2c0e0180d900c42400300c1c1e010b1840c0c0f45c1e100050604410800d40d220302040420300450700042d0b08019058020f5004460f858121303041c807001c200800000400b03c5000b03800100c42c20740140c49100c02c0e40c031081e004990205120008000500f4002c0710324040c10880d12481080c48140c00c0b003184103038140c501d0140303038841c0d0556112050f9114040302c1a890005001040104815842907024140010445007040030100c03080000801020302048400f6001c040040c112290030424880c90005040308081849000507a125003046600b005050b407081c020111700c554007c62140b444c150a0040d0301c041f14075641001d5034010300a04440d41d4050114414000300700c1018001e01b03690010b12130081130100035000a035103110152900308071601c00c20349200b002103403840c814482c580000d28020b10015440c85218600040304180680804664104004001344080c0104e85640d000f40c040c18000c0c0d5580100c85c003188d174080b40c0e400c050503143c130114480760f4600c4590400360031a40660780d039400c3c0340e44 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 378638372 1250 378637122 378637151
    0x315160f0914061c021b0609011a040f0e03070614011d07140904091a060a0302090106030e100501060206090d03020f0a08190608030307181a0d0902150a0201 69
    0x115000e01c0e80b03140700035111195a403420000502c52407070100c0b00d5005903400841c131a000d9070004d503a421207a10088480d6202a1002c1203041e0f84900900d0007808043d888564007000d01405811140c0110b0312075107840c08804151700085600340c0083c045a60f200910f0a00f203004098036020180005040c0f00000f41c110702d04003404404507a80d104d220506d803601c40054915030340110520b0b1014105104e070380c0b181e50b40c600c1081d007000d0103a44808081c0d9070403042184441e1004012a200e160041760078009030300c0782030415040d1038060270006154a030100b01c4525001c0060070107035620b400c1000116426602007011070207a5055001c5482d1841c1400e4290709031700501d10400400d80081c00b1000c801446003e200e50000c1d884405040c000c00400300307a00603501e8035000400700d03600000900082550010aa00007100080c1158101c0340c1000021094084001c040034a46540451810129040341d03002080ca036038000c1000c03440c030b0503000f09284182c0004035888095460b20694460120 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 378639622 1250 378638372 378638387
    0x7200304060f0c0f1202071a03071e090b1605010f0509191b031a15030601030201050a030b04090b010503010e01051b0c1c0c02041d0a020f0315160f 65
    0x3400707a264611480104881190a02e0b40703141c080e00e8443c42582e541c0701003007034200c1c4810801042da02400d5510300700ba043d249124040e81980c07410543c2042003003155079003d801e003013507080240c000141540541000306c0741100d15400074080540002030001403520b00c03117041210725108130024800c3d034413120802c0c411500212074002403504001c51151200107030010f0030208610440309510b544ca038807800c60341006856013084449000c040b5118209220105100f03a01c98410103109500f000440d01081c2c4812041c0b02c001d051050202e00602014040c0e0059114400058020012001a0300309450f12920a01c5064069460151071f00460403040c001d20b407191400604041d002013101841d400707143c2c0304400e444100d000d04008181c0180d941c0e00c6040300d03044c03030b81d81704e15280d280c600402003113404012000755003056243c01c0c148020703008103820464039011030f83c0c0e001c03884400012a04080500d107a4114042000040040b0300b9000c072100c0d206c09407144c4d145025110380400039a85507 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 378640872 1250 378639622 378639629
    0x31008010501090f0f151503020c030c0f0f060403120213150207031106041d0a1104032a03030e0d060b060d091b0803030f0903190c0210030b0607020d020d020907200304 74
    0x1b40450a0140034141860b014400c0c048980d19005203014645041c29007181c100d00003000f060f420a000c140302001003046401da8038102117019040c0d600741a900176080d40c401c01041c3d84116008034104020307003d0f0094050061034045489130780601803030b40c003e48600c3c6074007040391110705030f43e96641141003001c15101170701c020704080d0408a0f603c01c103aa00d10800101a080c445468a0740745106441d03c0c0c007d000114403d110342a290b00800c0c150000da42c1e4468140c4000c1c0c0d40c0e6040c104007082d804650701810850960b013040d1440c0303590401e80c6c058104107802a80180b00017941054111080d400307119014003460345100303c441e800c42c021002e00c1c900e20030394409500600128002d07080044220b40c010311408120392500d4061403007418920311800307001010943e142400c1c4103500b00ba0300d10f1081c44089250400c040001d18001031000e0040e01d00c06406515107107a20003c40d01e5040400c1551a00204075140e949000e0100030b0038503007041c15103c1041a422a0381c1901c480000503101034 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 378642122 1250 378640872 378640901
    0x203071106070e0d05101b020606010203031003030324080c03010501051225080105070806090f0403021b12060c27100309060b0a03061506020a020a050105031008010501090f0f 77
    0x1201c280c3c1040002c0200190300584281c00b0303101282d02c0c0a05030b4407900ca8a043c01c2c0088200000054001a0404d040241401c2c19500200708124040700c41d07910050a4a0f8503003030004400c2103041801c001c00041d601c20302c00c01c05c07100902240e5948000342e880c1d45003078100c00034401c681e201c0051203001a2500005180c0e907102003c0300d140041c84824110130008240380ca211480d81d991801401e6440541d1103c2c04181c00c0c3d8244889401d001d911940d016005800300410745c1026074000391345030050042c420700d801901c1d4120746580e49440d007422015208908840b2241842c800030030f882d6124590340d03031a562003490711109403640c040c20182066002084a4015100610150b01070408443c0890341d065072441c08060a58450316920b0145008907170008008292040d190116199500b08100795440f00d0744000040c0e41d03058a000a4401c2841c081c1c0d10390b00c89040640010355290050400c1c3c1d420b00c0c0001c183c03541c95030302a8031100003003001030003030741e05880041d070403140342c0000502d0 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 378643372 1250 378642122 378642137
    0x6090604030b06030a05100902010825030c020a021914030d05090904030c020405041113061404090c270501140102060612030f07030c0c0b040b12070c080409020307110607 75
    0x3161200b07021075441600030381035402e4921980d40d41070411602c90509110296078860120941d640980202d0340f0501e40d550206078207508103526001c04040b400c0c41340030103440c0c4e904200380e03c0c030071301004090035800303003803442c0e0f03988040d91406a00394240108280d10320b50302d000c2d002c0b0780727000100d520995100e130321000c0ca801c801c8400e02c444040018819014040340030f401c600181c480c0d01c60907110310b001301c3d99008608080400c000c0c404a0b01b21400e82d1050401d0424814140b0034020103c0e003e9003101c0c0002d5954441c0b6040c12203010582c000c944075440c50324009410708024092030b00b1484517010170440f1f6a21042048001b040122100340141d10030400607d1a051490b8541480500c1e5411a82080840c610014aa5004841c00c500080c4030300022000c104035516214081d101400c0b80f1410207003040540d0806004250341c522101c4155000301c0c01550242c4a222182904501130b550750f591254044006503000340ca00b08001a40c075401c801c003440b400318401d402174030b281e5143d40 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 378644622 1250 378643372 378643379
    0x60615020c1c170c10060f080c130f1107062301120309031e03020129060f040b0d090308160f050a0203040f060207030302070f030803040b0a020c0114090c06090604 72
    0x505110185040f00c4030f02440b158071100100d075102900d00000c0900080c29501c40301000d100c16140703154003c40710702c007000c80e05101415000c201d0900102c001e446200110f0b008112800103028100c106881840c500701e8101440c5141200a040c401d010305000d00c541c00707440240f40d008007050121147c00b80664401402034507110300c0b6400089000f031401c603410340c0c0c0700d4840440703047c41c01014000780141c0c88daa410800d502802841c4d1604412110090b0071400310040301d101d40201c2c894184243c9000500d920182940c0c010342d40500040442c643d110100b444015005101e40700c4190045000307480080c0480352901d03103a00218866907588160000100b030b080d9156003114445600b540014880400d45070044000b131002401d10b5402405171030315500b0081d0034014142c124080e03031501900140040b811950841b500107900c0f01c86c10382150b5414400c0c00080c01140c585602c03d500744540480314205001c5140e00031424502a2000d2101d0f800410000d84245608160050300601c03040 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 378645872 1250 378644622 378644659
    0x30606170402061614010f050910060f12020a0e0103060b040506030109030c02270c070308011e1a07082205030106050f04090f050f0f06062d1c060615020c 68
    0x40b40707041d210341c10191744130f104100c0007425610300038240540246e455007082000f20007001811102203518004200b05410419880801c60340da004219024482292000454507041c3c20380e00100040c0e200849103586924180c400740c0059082944186d0034131000c60117030f00d0184a04900780d075041d1038a0040001d44e0b402e002e10310145070001320010096461400300050304409007841121290205e43d99503480c3c2c5000703000300e03030180c00141180008000c04a0440f0183c0e02003010789138510764501d03842010401c11499840b48802c000d290b50f01c0864180000c0031141c1403e072500c0d1071102c02e00301880c0c41d001450300305c0d41d03580b040f154803030000d0040e20b2032030610340d0052202a01030079032000000001e4860382e203026a900100110350f800009007044008ac00d00415030041c004540000044022107482000c820842d080b4400202050002034416a18405c011066440d50400651120308905000d00108418030550928101181050310841c2c80800d0380341400c1c1c40101b960100034040ca441 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 378647122 1250 378645872 378645907
    0x303160302041205060901180506180106090204140301060e07020a08211f0e0402100807030f15030605010905040c030b0705040b0711010e030a170d020706060603060617040206 77
    0x48418158208000316103030f01030380745041d80540510000c24150400018803400c448a8600c20001115011001400250003040f02c40c0c000182212400c1c6065007016902d0050000d40c2c041c480d0580f0000740040c000014035195200d20304214000c0244503510441401103c80444061005070170000c03608000540782c01c003078449003266503140d200303c000102d92668501303400d44518013040001040d04041080f04121040075101403048101c06041c01d130701240320f07154408442000e00c00080e0010741e0841c0729900105a00701c4510003030001c1403441c00440c0158440d0700080d22100c1c2040000b0500308400c2c0140c6d4001c95000340201c00c4a8503544a2000c1683c0c003070641420050104800100010007a01520307c0600807600e090140c060704001400ea000182c80440c0280c12a00b20318022410344c1004030740c206c403610f03c1550341c2d601030400030000b0300c124800208410718051b00840e01c0c542c1a808242980c0e00f40c0c9450000c480c40e0084207a0010303089800a40c481e008210141c10b441c0d80000 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 378648372 1250 378647122 378647161
    0xe030409090503130603330e090a0f03110111040503060103020607080f34110108070e12241303120929070c02010c1101020a120207090b0f030303 64
    0xc3c0da0030f10758080184e05240f0101c1d880a4000782d00c500b04c0980103c10b540e401e00c0c402d1108a00070340d003200031001d2108101400d118541c0d80030035510000340c030068140010754006600c0b12110140c80a103290240c0181c0e00c5243c468495840c0501d8141081c0d070001c122419210020700030250f5030328581c204030041c1d000c1c1da0101e43d0300506000c101d490002080141c09049000003c85000c054880c14000c0d0f2107600043c000c61134406c000b2000c0c00304500102e0200403c50070f180c044907503544d1800640e06040785155142d0082100c2460240d0f80d000410246c4d0510039107400c07010103807041c030f00b00f044030042991350b0b8038080b890103035a000190040c103452040150507000429554038a4071a03105058419400e10010601d40b80d629014a0606045075400411801c09207501b000c281c0000b010405411401010011042c0c1d0361a5140e0003004290b01555108040c99280d0700c050400075281c0351640315003000c0c5802c00e801081503140041d034102c0e10101c046c000b10b045960f5070b0210411403a0058 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 378649622 1250 378648372 378648383
    0x130c03080702210d0e090c09040b0f1206190606020d1107090509150a0c0e12010209041b02060c040302060a0e040905030d0606090927080903030a09080606040e03040909 74
    0x140070003d52a080c0416844003840d900181c4940001511301038008031908614520030f01401c8200b00b40b6551903c25100b0401e0b094400081c10280700022030300c600d4041ca00b05510142c070340e0600c4012100065018824451070440c0e110030407003091200240c0c1d000e400b40e00c001d60809480ba041c1d10340314460481c002c1001c40d089600307050ba00d142101c2160015980c440481d0003005190f090080e03000c40081d007000c0740d0030082044140c902c0c030007000b41707003121251407050010031190030340e4041c250155201d43d04000d10410451801c56400958401c141501c000580520f20000f0000c070b100105660460350080c02c00c40c0b80030802c0d0f100701c400c911030b640c116501556510080e40481e0342000a0700070741d040c100c0001486802c01c0d070081c101d580254400c610450424038040c21040d5015280d44080401c1a131003030880c0b5051030000903600030913420b990144001b003035080c034055010140800301c401c94001d96582d03440700b8051000341c4120600003201c69008020410460300b03540d0101c19040d0094 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 378650872 1250 378649622 378649639
    0x606030c0d05101103090d08060105180a1d010e1803030604052a0a09080f2503080c0105070905011107031e080304061b05250c050402070c0905130c03080702 69
    0x211040101c4e490b4500010180d00040100704980c1003c01010302203a55905004940e0300c2c0c80d0f00024200e00c566940007402c0310b48031001d24101e49600e4488006800103070100d07000c0540e0030010a0a1444c2481140c00c2000c005011070407007001b240202c120341426a0107940303559a6481404041c120207440c1240c03c00450021a02c00900b030807251101906603a5040da5451030398000624003011fa8020a6842e000300c3c440342c00c4050300013016142000e5841c5d807108200d00118100d02400304983c4054030f0f401000810440b0084c040d40201d01c038040e030f600c9404000742c0794001101e071582100604219035101d5030301030021070304181e40c5880b898941d00502011000e280e07106400c5401c156412188030391103040f031813410015010710326455500380c5000c80c140680e511030b4901c2c080042c0032400c0054107502c060300c02e0100301110754001d44000f0744159503c6095140180042c0391611851102070300e01808290008401c07000b00051a8110100c003a460742561200010b035407081c00200da015050 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 378652122 1250 378650872 378650893
    0x5070b1308060901052e12110306011d10051804021c08070b01050117040b0c090402071b170c040e010f090302060414010615031503020a15110606030c0d05 68
    0x420030300b07109940714030011a1600380080762201d016211206c0703450003521561280c10030681c8a0103041114201d518507500000d0b1814040503400c03003089040c2d00b501911b000032403140d10140e42e0382d40400da0041403440139601d05c10525400040c601a040c2c0c01801d01d85031030b82d00d0005404030f641141c0010456040c00001484000a814900104803401c9201040348410700c0307100340d02e06004000c2030801c042d104072486954a04254024001823006c0800740225000c00040c41c203603805080c01600443d560552410003200b611a4030120042e003000c5040003003070f064070316807a248a090202000b411010136400c104005003c64000c82d0b500d0390350300e0400c4464500a4001d440d8924001d0700903284c0340c10f0504000c83d610310034451080103a81841e00800c64114800813074992803185103800240381505003881001444c4980c00a0350084c40c440300450380792011810b400c0c00000343d44498103e442c40c2c08a6613107880c2e0444020f54035803c0ba050260700350070721548002140c0d00c0340055400007000c = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 378653372 1250 378652122 378652139
    0x105071701090c1b060e0706180b0301052d0306010b0304060515010906270b2805030f0712050412110114040803130b090a0215070f0213110408061509010305070b13 72
    0x35500840025540c1c0c1300341275883c464291000c1c0a8480120150325560500b8040381506042e00780e185007400c50310110840d4880032003200d018203c0300406446903940d4501c00c0200d0b030340051340c095a1062402e07021411a00710401c08010341c00301030310790010291802c14203a40c04440d8140365041c12140164107030b02d40b00c0101c204000b600c9408038684d00c500691442e060416a92001300381180c3c0310052191030541c100c0c0030b503a44a03d8101c205049551000d000b00c0d607007003103400021a210704000600042140740e8860b05420203d83d956051600c4680c14414241c48414411001d01d040400c0441e0100715400000d5a0003450740c1041020301d42c05a942c94004102280e4201c1e4541101c07070130200314a40484081108202c5200960919907592558070b00481c011900a00c520320300c40410301c0c004515004440c00d209038000c915151695003204d96142c1c1070849561092003a0f02c3ca15000720b14204072018103aa801030001c0110608002031407406030300820340c80d07400d4000c41c0d5001410a2 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 378654622 1250 378653372 378653383
    0x60503030706090b0f0103030903020f0a03050f100506030a0b16031803030b01031107052e0609060518010b04090203070c0c08010f0509010216061109030105071701090c1b060e 77
    0x40c810540000c001c4414104400e48400107045c902503480d8200c01000400c0d4800341480540341c04441c2c0c2ca580001100016440181603403006009004040d45014004000301d4a2452026015024081907461108258540b442c07050000d01500701d40010484c52045842d0052900a99050006440040c2c8440500c1040c0c1c249080300000e84902c3c640c2c002d540c4c507001d603020344025580344509054a5586050315420100714413000d2a42d001c1080d8244105440402044021400100f103465111100400507101078010180201040345000305640c441500c1c1504a840d40e404807401c1500345002e0001a40c0040c0c008010400720040b000e0100f055000303604018407c4070300024190218090100c1a40d038020810342c80d90748180045044010071a040391691039100400044038400c00040c8141c07405203048158141d0300c2c00081200140e08040d21141038045403e00c00710300e07030ba2a080301c0c041e0348001020f100025801e0b00704051484050b882148158420307080496a000f6203103155113000c = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 378655872 1250 378654622 378654637
    0xb1c1b0f0e010612110a08040f0b010803070b0c031e070c08120906070f27080105070305040b0c07050c0f040f05070f11120921070308030a06061b021306050303 70
    0x1e1804010000d403a0840321802c1c2c002e4403074500b4401d4000c808108481c0f405601c0b414002c2c40880d90000b001c0140002d2002d81440d80311a0a0300c40356100e405e900e6503600a1071040340c06c02d00410104a80e0400d190590784a00c000403110321090030100c01a07068903030050900004d10244100c0000080d134004017602503002090f6012680c0e1910181013480c105000d411041400360107002117a0075940301d1403840031000740d69000a0a01c030320b4541c0e424404200c1e80032454552806003440010399064200c0760150307001720044030352030321480d07884c0c4428030402c40020001d0780100620012403c5c01030f802200e01d07100900001d84000700040311004e40e00100e81580003d03400b640500c0030285c10400302001d84240c080181011100785c0a4811144240305600e441a10b005118110340304082040300408101344050f64240b550741e14100b2a0b60300f041d1400d0484d0f80c1010008030f01c0328401c840402003010900d030418410265902880800303400d02d208180100d442d9600800c05450400080c00d0341c = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 378657122 1250 378655872 378655889
    0xf03071d06040c0c0309170c0d0503030f0609011202040504230a0b0901060303080c1b07080102090103050a0515040c12180b0a1506050c160308030a0b1c1b0f 69
    0xe480c00c0800c0000302d494180c4040705100306401e1920120354001140c500340c841d0b01d80b8204260140421051520442ea0450750780200e60040900801c030380400a14042e00c0a988540d031303144c8840342000a0940c1c24010506100300380c1c2c0c0c498015103000d402c110f8110b4011110310107140d0b4400301410082d00c20b0300f803c80741c60380711320300410410580c00f04c2a94081e06c0203000300907040c00d50358018064400600100c41c030001c00301e40580c11180740d550440ba0001c84804407101103035503801c2140030350000300f601c1e8042403a000002d014900c00d806460b110b4030385607121342c010000240c2084018141c00104004002041c501a0f281407240d22960760f08951146943d440f10203d40381195504100400005809040110081c071400003041d540341a01c03032505000d6100d0312a40342c02860251040b01030311000e080b1401c00018805c0f004010350088030320b40030a000d098040d60a00ac4604901c030649501d826800d42c880000c02c102c808070310041c1c000700d940e40c02c00943e00d400c00181100750744c00000700b = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 378658372 1250 378657122 378657179
    0x8070306030812090607030b0325050d050d030f02040303140d090816060f23181504052401091a03030301060521061f1e0306090606020c09060f0307 65
    0x282c0c10b03003000031700c5c2d00020341c2c5424000442c420003c0780d01e6008a000ca1004100165015000200e18400d00f0010309000b4220000c00d060f14203110783d43c0c591807004c40001c83d142c4180b45811a043d4021102641c0d00350b103441e0f41c030030410810074170710780d006558458510b640e600306140081c0009008002e0a868440d410190390854113040342141d1030003007000003280c03405009034404410310b00d40d200070349000030305903100342c0c1c44880865203450140c0440d00640070300004002c402e068071480e240581d0068044405121b20743ca026460048952420528006030500402c844215604002c55070003180440800066480c00802e16540080e0080ea000c00c0700070a03154a5100140491050180900034081060400c81f000c07920405800700c480070201ca010803900130007801160307500340c0c0c00c0c4881408080d074401320744018020b0185d409903000341402e2400000f445032000078400c00c4040010304c0c5440750b40b01d9200b00408042075514140e0140605100040d0100d4034103040d40f46c8004507002e120 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 378659622 1250 378658372 378658381
    0xc08010606020c01050705060c090d0f0318060815041107060207051b0a0e0a090206040305060403020f0d0f0e0d020f0d080304020f01050a05030f0403030e0313081903050a08070306030812 82
    0x20b0070151450303d4141040741c14040340000c07030f40000d2503e0f040700d00c0ea02c1003541c1d8a0b0031004104903a00425015142d0080001c2c80000c040d40001035854010810311400f502e0ba44400c0100c40c64581552020210b02044901d10070620b00f640c80f0074100c00310b154107136241003200d541320010b9802032001a903150300412240c0003d1a010304901d50024003c655008060341006586083d0100160400392400e640700205000c41d110b880071038001d103030000100e80d0f503441e291500959a43c16490140c4a03405001c001d503101c0c500501c427004032a4996162264070005010611200340541282a46d001c0744000806919450307030a49000341c01d00607448103590b40781134014450b0841e0941100c43c1000802c103c80d0602035841410b0720b0f00301040050114003511981400c40250102ca200b0b0300b041c2c08001401e640b000f400c1c84005048511642c1a0b070100c4d110484079905002c1070100150110300c2c10004550303854462680b41da88034043e41000150710342c84c0e40b1040c1543e0041c800282941c0e68072030500 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 378660872 1250 378659622 378659627
    0x10302270f03070920090d0b1902030103080712050903150a1d0a1101050301051008040f060509010b09060a0605030402010f050c1b09060406030818010c05010c0203030f090c0d1403070c08010606 85
    0x1716160004078414070310b0316001401040284108031005055403800f80b0102d14146800c5c5c1d105c2001c0c3c801d410f0f041d501d0b961070b81442c1d1070303540c414413040f901e08400903d20301a0f01d003e0016140b00c4800240a40201010720410041c00000140100c1c034299a0f42c10a4100c039404400c1c0580c82142c11000300800c0c1c04500d00b506c0c400c04041d5280d4107000e0b0034401000a0354420107240b14000061402d0022900c0785c1c41c144600b800c2980000381005d080c00d0420082010550008000020803076805c0140d031140f07004e11094400600821001460070000140954001e03000800008090301c1c01900c0c104e20b42c0c00083c02e02d0b0b855a19903003001c4e0386400039071003031610810381c1d50480b07000c40701044240d2456071903648034810307540018500ca1380c507800401540e0280c00086525500040244688090800c009480b0b5004a901803a841c008a000c01d141c4040061001580074004c0c15031052207580f0f4031501140354000c0114500313440101308038000181a00014001000300030000f280d02401d00601 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 378662122 1250 378660872 378660911
    0xd03121b09171f020d090b1504050c030705090118080d030e0c010905041a03010f0207050723010e150d06060201060603090510090602071b030b06010302270f030709 72
    0x24601c042d803040502d0314041804640030200007403460700300081d520701620940c0640076084880301c4503841c1c06942d405110341c0300240c5118140c0b1101031501c280211080104494090f2030109042c3c0f030030300c0000d1505009800929803074005040c5000b0381d034002c00c440034444040e0b4010017070079000a5800b84002c2c0d098025498a90f0b564002303041d00d0203656000900f800e0641c81034502c21511030b214000b003c08569020180071034054020721542a00c244100c01a42c0003180449a46c0704245000079241482218503012081d90340f00f0200750148800111107200c1d203a014541c0c0807401e0f446a101045115004002c1801413180c003040040c41d11500ac0c0c2120a01da0010040c181000d48001c00184003044607007005111501c00140308d6035904003070009000b407030002000b241e002440000345880c07404005044900c51516103a01d941c2d2480110280d003c1c0c402c13102c004c0d4241c0b031000b80d03c2c09200d403490703403001c24060200481c2c5118500001c0c540031855102030f081503500c4204001101c0300d40c09 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 378663372 1250 378662122 378662129
    0xb090f0402030114090c211f05100e1c0303090c060206010f0303030504080c06040f060605040c080a0f0b03031305041109063106080702060717060d03121b09 69
    0x80c114110b6240c001051000c0a44020882c0b041c9103081c002a6800300b031400391004600724260700c21000341e02000c9014802c0069980081e418459034078070b000301030701c81c003218181d50000c0c150f01420340920714107841c904682d65080342c0c03080034030800d00d0140300c406070540a030038000e503400b24041865090244c001a542c0c0c01c000e00f150403003001400b94010f43c41b10700c003c40e0380c103190004940d552418500045c1c00b8290128450340151001c2c00140054803001c40300180c025001006916950400c01003256038900d1110041503401d80004c1e07a0440c03d40c080707070b00c04244000101da042101d600103800d560140305810300a03490400b003417007181414800c61003400b1186a200b860400d4000000300e641c015550440607114130f403812014140702e02d07419154509082107648034455160b00300a0103048003100c800005101d194001241244240548803c0300450410340c01e9a8440005102d042002d900b4103501b40840e02071340980f090a1031003610f105040001d88148040c503006402441d0302e031300e6071 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 378664622 1250 378663372 378663379
    0x80313030e121e0c0a060c150b09071d090c0d0b0409321911220209061c0f0b03342606130b1b12010b090f 47
    0x49210340c1e00c0d00040c0c555220003041c10f0f80086196224629841d000015060980203a6048000221241c20580900595204641403011f16140c0d040d45030841d44499501d03035104040c1d0300443c0b00280114030480d2080d0a5001c10641c0580300d06c04516843d1054450008070700f00000c503200c00805511458442076400c540038418400e854403245602c40c15104949911841001e044071901c0903048016480444001074858400c0c011900568040030020b0588040071304580c008668900020b849000d002115a4000c0024841e40207200a4205032b2455800070410800c01c200f0040f1941c04040e00810f5000110b01c0e114079540c0360050b100c08602c0f0b603000e03520813106880454660001c2459105000e1403945505441900a480081865208c0d035800e20341c0f07a500c40e5401ea0620600c0d4800503000e000c98101c0e848801001001024565015000ca06520041011048028400c8035071754443d910003400c1089074000515106400ea0142c00f280701c00088904142c10003560040c15404100e = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 378665872 1250 378664622 378664639
    0x1506031a09011d060c030606091002010f0f0c05030a0f06080a0c030210080609131e060504060509030f0409020904020705070e0906010b09060a03092301150e1005010c03050403080313030e 82
    0x80f0491a03490b80080c00da070b003113104003100003802d6450303640560301980402030401880304941c890180c020104041414000340c1404202d030302003040b50040512200d05955840d182d41c2e81c840d9100014003c01c1d011912081c0c840a0000315103004105410f00c050007607010049240c55481000034403405500d407402848003140800045030f41d8171403a994040848803460010542c0f1380f8111121003140d03264000f00444e0300c113032501480200c3c3e028034812441040100301c16103032401c0c00c60752802040c240d50180c1c002000103010b80c1c0b0686e009007400764005000941414410358070b003420a64a90010b05000b03103404c00700300742210200281401400a60980d5107041210408905584250030601c824161a1180802000620b080c0502000320510198015003ca41042c0f0301030f040800d02c130780319180c401c0c2c00410b90b020381c1951036000310180c00b50071032440e2802c0f00541c0c2100307101d10142c0600009202c00400b044000004511454040038014800005460094103103010ba0391010b001348003a = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 378667122 1250 378665872 378665921
    0xc060e1314180307060626070b1606060b0a020a0c06030e0307031b140313060305061e1305010b03060406120201090b09040b1905040c08040f1506031a0901 68
    0x5060301da401200618002d400000b00380080c07880c5110300c610003004c0a1800d000041c241030104035a132400ba1205d490131544107102103019955040d0350213143c50440c4100001d1458812001cac16141c8a8440e040105284e556100684010380081c4460005a040840500d0402026529110180c144ca08040082247c0c808240d0380d0f0303004d80a0000e0501000b01c04040725035402d00f00ca1025584d100c01c19002440c90b820030700da1640c101008a07000714151002c0403c16501078020148200c00c050a4411049020a070b100052411088042c0e0015051141c4205a00c03260203400d01070b24004402e16038a0a115061004482403036014610910707007002c00c1e90060380c0c0001e45070125404104000c0d00c0e41c21050000d8000c10300006074580c0140d003100481c20000b07404819008880341150204807505141200f6540394a04850042010320090003042c0004c050303800f00c007031100601d40c001400321707166942c24601c100010300d00d440412880f0200716074000d0034007400540310146110158034018 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 378668372 1250 378667122 378667151
    0x5030c0f0f03091e030607020a0209090102092206080d090e0601080402030607120e01180606050406120b091603060b0907091a03040807080a09030c120f030807020a0c060e13 76
    0xe5910410712550840030b65a014095584c0704000c813001c010700303448441c1003101000c0d5458520075801c83c000e030001800038000761410b05c240e0b404d80001038205207601c03180d01c1c450401840003e02c6a10300d141d482501283c942402c0001000c681895102c101405060074107048028000500701030411250074104001a2400305503980c000d1000d00b0040c4d0603540c201c00c03d40291119440fa8034940d03180400e40c404510034a601c1c0202c142c0694001c1240c9902c41c410b0106413101ca000b0310001c003425450a8000950400910354003030b03a2102075820124030071402004001c5107038030654040b905c4040c200120f02e031003c480344e008811818117111262804e07411041d2107028826503d4030000c04030000b01400301c1c80e012107800c942c1c4880c0312980c884500c440a80030308000d0000341c405500313010300414406030300d00841c0700090304003c04030f940c01041e039000c4441044c01010b50085010758030511000403119003030f801c050800368654070000349034001480040c0c41203241c0c8450300340c1041060180c0c4038 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 378669622 1250 378668372 378668377
    0x3010e09100612110102070e07021006080607050f0a050702060313052e0c0909050f071d0303030c0a05070b090303070f0315030f1406010b031005090403080a0b1c05030c0f0f03 77
    0x1d0744120000ba0b0a82030400503400c0c45180e81c40803402304150020004050382c0411610400007000b60708000040e141c000a83d03850000b21003d00110b041044980e10510b0404068041b0344810301e001c0d4641580c0b98040f03080d5030015100c04813810820b0800c0170800c00140304402d000044000b80000e8400c58059010039491440301803080300342c1c2c81e95000c0300c0a1140a148000d401003990600c0f041c00c3c000018514140101d80104c00035280d0b8803600403424001c1e8412005e040300a00031411600d44040c0c0f03103030b00c0c0c0c086c0c000003051041c1000711000140c030b4043e40300c5c40341c941c0f08060341d04ca14028030b014003414a00d2815404151a00c0c14402c2c03600c044070404d40541c4e0300308510140141c1d031481c5c148800060044203032114454080000350241c00c0400031131195070f110350703400241d0740e5400c24040e1040b0190340081c0452054000203110050b1035200c040d0003d801480c403500318092a0581c400380389803c2050360300d40c00000c1c22401440c02044000e00301800c0c24002c141161001d1142500ea0 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 378670872 1250 378669622 378669659
    0xf111c02030703020c01021305040c0203043204090302060415060503100203040f0b01030c153216032706020d0305040201020a020a060c0506010905071409030f0303010e091006 77
    0xe502002003402075200e9030549418943c01e9008640d2065124802c10030030600e0b02c64580706500708952100340c248040306031400c90300f4100882c403914500b2111000c844150a19441c850210310000e072049030758a000f421420fa0194001e070000b41844c0c1032060391081ca0b4070389421201d083c020704000039100024032104520001800503100c1d01c0b107140001c41011003460180a0070956400070091010505160381100c404c1c14429240e00e26841e8152080e0908549280102c1c00202c0b00403c0c85c0c111710300302008009122103c902d0009100022864900800e10560010301c02c0e40c41ca44d41008100c90302d10a06411902750a030181c54580025a1090083e00d010201600d60001c01d0459000b00710000d6880d9004100c03030788254455100800000c8091f4060341c65110b0303400001045c061754840d0300c0c0507242c284d03607000f4000e40d6901d0940440c3c2c00400c0e62a010300c94400301e08541d1805102460282c840880c125070541018a20149408246405c481c0c03c24501001005040000d14030031254 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 378672122 1250 378670872 378670927
    0x30409090501091a0106030b011d040b0f0301060605041721070618240c020705010507030c0606140a24030b04180b06100908060a0207081605010f11 65
    0x11940303a1400601500c00d80900411360394421381c220110010f1030b1a0103040c1e8159942c00c02c1610b40c03840044070008210704401101080c40005c0d0082c508050300801d084100c054484246640141c0c00310f400c441841e0b1003400040c2012030140500d41001e18140b86001225005159038031603078018810440401c000c600c50640002074410401501e5004030380d03524240b60348070044001c2d50070125620141201900701400003401c0b03807001d109403889103501c102841c0d4006c00f0f00c181008010742e466405844140c090001000c000c2000074164062000503004018a00c1c0c2640b8143c1d050002244250b0452900c0c0d01c014618000c03004900600e034044050b883c0b40200d0500c24100104008212100c24525070300c90201415061228480c80140500c0c820340302d04180400c00c285c1107070074031140c0c0a04040e540100d80030030844161900603017141c90149103407625061507040c409880e0591110212081c0c2d4440125400c0c00c842881920000728214149a280202c4000c0d070b0424554541d00742d146 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 378673372 1250 378672122 378672131
    0xa020910081e071112090a0915032301020301030f03020d0c05031c0605030d0305060f030a020609090403020309030a0c030c0608152103040306060f080d05030a0e0c10120606030c02030409 82
    0x1c1d031060420506445004d425541c00039035000070103141740e0040403414041c0000f50000220036503e8401e208900030707851040390f1070500392341e1080c5040c0210041001d404040c2c640c0c00807604028401140210301c50b001502d9120028903019061203c5640e4110a0014800c06000407a80200c201c0c0e90404010844540e07440405200d0740080c9050782109070180b0030020011078080c2c040c3d200764091202100d490704000000c0040560b1070408180c020b400101c00d2000200a050000c5680e81040c824016a81406001000b091402c0102ea4050360b20301201c100403c00d0004240044000e0401c42c504020589003902c03000b02c240d00000340150141c1421020308003461901701d44038400d41984d0040e60394680d6a41003400243c4010700400784040c1e00b6440c00904840300007102c2014841c6900c400b41503039600402803000b4800030030600194003500d800d0415036038403107006a0080e14035844000260f010342000700f00703c9600d504414141860492842c2075150000f099904903205180c011a = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 378674622 1250 378673372 378673381
    0x81006030e1e0102030a0b1f050f0f0a02070315050106080c031015020c040b0f010c0b10050d061a040905060a1104080307030e0319030503190209090a020910081e 71
    0x9291004620441c2400200d80841c40d404110640082d4002d2a60b07000511a50a8010412a280908c0d10980a45203483c6504c01c840601030005000781c24110482e160804d2202e28405000303500c01e018410052b0041c500900c104240096034140f1012841e504214541c180784000d0400c2c1e00141200903806004000944664038500240c40038141d100069400c3e82d440c060080d42d1010368071042482103050400b07500550400e02442100494140d4a000818240380c54800c1c031000094a030700e007801851803020800b5124080281c43c9039210307000010304030444000e035603480317a200a101446541094610008182c001444981044d5840000a011104011041c28a100c0e943c80441c0900000c80c070b00050503000b000402c038804080d0103450101007140c00c00c01807070109100c02804160f007840403070518000349a2100b203050600760018074286d4030b82c4c0011105d8600302c0c0d05902580e0005041c41190410b0040d900c62402d882c24854900d0a004000180890b500c000328600921100c0004 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 378675872 1250 378674622 378674651
    0x50f01060e0d0822060327050312100b0705071d090d0806030c04060308541e1e060906091c080301030b070c0f060b03012004080d08100603 61
    0x80c20062101244d0f445140d07036a44000d00541541041c0c0903410800501d5840710081040d2001c0b1b03540d81c450051403400d841551038511842c03025086031150541c03108003040714000c840040c5030042c007c00082c026549090400990f4044843e1002c0b4242400d0060001c0c00b100003407480740d01c107072604040e1003a40d100d4000c03c2c984039500304c64641c0141007410001c10b11411034000e100d4107038141da0030400c600a000720640d00c180001c003604036000b1186611200e2039038040b405c550003850168410448116000010404003900c069603d0034280e211600070546080f0741c0726204005d102020f40c806155260000d0764601400322694084d03034001508010503920244803040003c2c2c0380300b0036401400319091400c0705070000d000440b522103480020a1f210381c014410301a00550040c407a80310445a50f40b15005002182c0c0a0380c1c0564036400303501b41002c005055050019440d022013521240741c10801c9190900d40d20071441840310f02c00c14042c4c05007621791120160b80040c08e0110310350405107400e = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 378677122 1250 378675872 378675907
    0x703090b07142104050c010509100503062215060207060c0807020f1203071101031503150b031c1202041412100516080702120a120e070801050f01060e0d08 68
    0x110000d5440c88200c1c10f0440248002d041c1c02103004070122080340c41c0b00300043d5014880d0200d0a035103c91540c9840140718407490081d84c0c4428003801c424a000c0030891004401030182000c044002e48803e540e40300080e00c0f00c1c038200201058402005090b24116003d0300341440a4000340896000107019030540d294900000700e86031002e0840b0050442107044a0b4a0340c001000c21103d40542c0d28880034198070a0062030040344107403015072002c2e0b16603514124601061006a03002a84403a900e50700303903506000b0f00d244803c4800d00d40303102020180d001070a01240702d5210a6040c8180014890040801c2003c2c03040380080c0c601060144207090100d160008895501004a04007002c22a5a0941f101004801010360b2503040071500c0305d0100b80e807a10b04886220035541030a014001880d4842c5000303861980035000b000500e0400c00d0b04e801c3c24038001c0d8008004680d19141030013078000a02400c5401803040c0e240c8034240000c00ca0004020b000c0d01080070305412008920021665209000c = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 378678372 1250 378677122 378677137
    0xd0906140703031803080103140303040b180c15130b03130206070f051b0a0b070506070e0109080f010501030308061c03032c0a0302070803070812100803030117060703090b0714 77
    0x1c06640302c010305e10b401090b0710800d00007100c0f901410b25084040f0400001524011507021000002e070750343d000600c1c0c4c440810407105002e07900c58850303240d001d83c45042001e40d11041c0103810655030301242d0180307000614268040c40303141404204114291030b0803000410b880760304a622995445260900b80340303507100850040c0881c0078680215505450414100847c0e84041d1169a00e16039600d40c0e40d6014050300c02c02601e90b0704500c0000d41118070510940e01406c1e41410002e030701540380e0003820700c0c10318401e2890849a6440005006040d00400103d5224208842c20b2480d226040e01c00401417005c217000505164640101700e811004950b0041e1043d81c010541c00480c4005603481d582c3c03040350301130a80c094011040046500000802141c007415000600540740051740b0300b40c1080c0c0e4400401102c0e0b201c1e444100840c440c041480218001c096100403c5260183c00d11901e081950207081c4d80c003858600f11078000000c2c01005205c2e0f204980b82040711000744c220315a52503d2181c0203 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 378679622 1250 378678372 378678401
    0x2030c0f0402120f01050f010503011413110c03030405060610210209060c1e0111041412012a02070e04120908030c010603032703020915040c0305010501020d090614070303 75
    0xc100390070301ca208807141210b02c200d90324205000b1f5000103607254031007030040c0031040c541609092083e0403c0b06200c3d40312100c0360000104291419050200c64121500c1143d80750800030610080c01001c0000c02e401841c00c46080d21481400c810141951a10301440e1032440d061a04414000c54244d054540680c0701418465840e100d0406c25529203092031a00c80c00104a00010008a0014803078845030b1007114101b00d1501d4100304883d00719404030028a5030000c401c00240c10b02c1c0b042030050141414442100e10106004038601c0c084c4040e03955169021584610b0702008032040c07180c045e6411941041100040c1e40218001f101c1154954100d028144000075021111940552000c07081724040c3d940d186051b440c0c0b511180720b8041075900c00b4003800391b0743d40a2000d860044402c68001e50660708650202c4030354004501034030541001c01012a50f228010041c1d941c041c065034005510034605100100d08001000d480020103198014200002160180405019611100550340c507007 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 378680872 1250 378679622 378679657
    0x908010c0f1416120f0305010b040506070c0b0a030203010503070b030402010c02060706180309081006050307060e01171303080604090c030611040807080303100503030c03120a09061a09070c02030c0f0402 89
    0x141030034511942d9940c00304000401717455100701081d10074424503050360039410341c5c0d07440e05203404100056608003d0007924140303020b4900203001204140100b03086003050b200581c8961600c003c15080601c83c0d4810495440c0c01c108010050781c0c01030588903142c2d8102c0d4019102e180038144030009080800201c11102d0048201e80203150304030417040101c68001040790402e42c200e05c0c914068481511810b901031b80144000e008103400f96107000c59048041c0340003120a1050180320b00100010390320724107004c107904000c6042c150b100a24079400a410f0300c00b072003010700559443d4006081c501c00a0981a035610703103540007000f900103d50051042c0000c803100d650b00c1e1102940c480d031040d104003810421800c0001741608010042e5865420f50744007940c200040350101c0001c1c40030041030129500d580740c0f0300500181c40c9100741d205940d0090300d000441c089e06414032290040151200042c000584200c00041c1c1d00000e86000351041030303c0c0b5080d0341c41d98002043c0603004500e03442c080c0e20b000 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 378682122 1250 378680872 378680917
    0x90c08010c0e0a0609030221120f07030f08070c2d030201050a060509010e01150302040f0b090f19060c0f0203010c080f070c030504060507170c0703030908010c0f14 72
    0x480c0c042c00c4002d00721407003c0c1007650f96805503194100c611000790400e88e00c20414501d000700b03c0c02c40c54030006d41002d4811680d0615040200e55006480c0c40d2082c09004c02c030902415803145c0c003009600520300b00071480341011305018002201e8904001d0113a821002d41241c00300119066541c507141c9102c2031580b1444130710b07000c0e018000403260b6050f26860118001294941030b14910704030f555031800420070340d0030401c1c400c030081d040080381e03070905408120000e141112500100c00070300103140707115241c0066004000c004c110005c101407080301c41001001d025000d260300081200c1d2203003406408403e56140165900ea055203000e13501d0f504e000e1107507501030b800250340d038031424004060704400d689450081e0785000c1c07003034006000100c0a000a00815004400601e0824010440c40c0343c1d000485074490403580c000700c0160311503000128100101900904800090040000240800e40d99810010300416103550720004101d0a8111010318244a42c1143c0008841e1014040003a20 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 378683372 1250 378682122 378682127
    0x717030f220602180f0604060c14010618050103120f02030d0e07030c080115060804030c020d02030a02040c0509030d2a140f0106141903030e060408031c0b18040204090c08010c 77
    0x1d041413107405440760140e10078980c9040700c1102c003079403000d8841010048540e168951050041e030300902c001d641e107010101d9210070f40c05c400c00140d56201d902282540c158642100d019002d05084418444141e041068046e000300c00c7c0d901c5070302d01000004d0107201c1c4440b624540200341e40042e050a103115008140400190000c03c1301013a940301d803902c01036035a101212515003c80e4090002a2a14004801440d003540c00300401400101199142c000a0700080c0c22038a102c14060046100060110f44604092058500010090400030941d001d120520320000c3c1c00000c0d03072a000c175403025110080040448a0202ca9151102110001c20701c1c0d00089000300a01e004004251a080014682c00c4c5484881652003104803103908150510307681d0242d0740340445211a5601c07a0301440040f40030321041003d087e4a42c46c00a80b2040682404902d000b25002851100c0c02405a0700200d4030760228072000a030040e9041d01c00080e181d4035401e04420801440e002140d0310350900c8082e800103075 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 378684622 1250 378683372 378683407
    0x1a04050a0b0a150903081c020c0a05060105010c0302030316021f0b0906090103020d0b0a0e0d09171203150f09010902070b01080706021f09060603080717030f220602 72
    0x54502d0705100361100d41414803800400003030000580c400c0303400d0000035070f860060300c40540e0020304000c04032090070f040340680e040a80c918141b68085400ca6040c48410440d10340140808c0c03d0030b450740c60854a000b0740724440140740103018081805c22948481c800c000d0380e80d01d48400d40790b460358140542201c0c8050081d4148152040d070200d4042100380c5001c40c40c15048039401048104505044d1796030458100d0020201528555100c140d440d040e44103003c0400d003203515036101c0c0302040c00c040814880c0d254604034a83c69910076103a140481d5401e05c02c07603420008600880307050380d042400003a41001440d104507000100c0c4000010300007941c0e0080e2918600c620081c0b0700a03030f01c43e54041c0c0d40c2d0403140f20388001680044548250416184c0130480410080d01c800b080308166900e03500c09807000355002f12581100002c00c0c1d014003100079041c0701c84040e085400751441c205220707080182d40000d4a80171490080c0f14400010429880b007201c02664000c0c000e540321003402d8402090407 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 378685872 1250 378684622 378684641
    0xd0c05041815120b0405010605040507051204051f0b011b020102210c100b09070c03090b0a0302070501020316080a020304021503060105131512060b0d09080c1c110109020a03061a04050a 81
    0x1f98204140402c9614080c0035103441901c007981c580b420540741c0700c40000e682201030300586d42c1d0700a49d404070801500e03422801c101901e40e02130200da030000700c0c030005041c41440c0544034541c003e00c500b084010303079000c6200045500808007050344010000c071200710911400702d002800b449000320024000341544c0184210705000c448c090641e0b56100b07002d80c6c02c45a0740e20001d00040c0c08110902103003203140c0180660024038500103050451aa0720f5508aa1040d02c07014410151480550211903000148036032180e0058400e40c150f080c141e02107500e00b0032065101c000071030b003c40040c4a90348138400b9160417210100b442e1076240e81e20003003018118112045800007802101c1362000e40c3d40e550240e40e04695003440641d00c1c0c290348911b000d000b40012001103030700040805c100e6103112010801d014848a03d4016162281c00c4048003400c041e42d0500c0c690103d074104a0003002580e541c1b8100340071a900502c003c16840e442982c1c926880300050b0015600a01e40400d004074600142d2004485 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 378687122 1250 378685872 378685883
    0x30504170c06010627080f01060f03080a05030a0e01050a0c09050102030f0301170a080d06091a0f01030902061b030c1002160f060b040603080d0c05041815120b04 71
    0x42640100511024850007003640c41c29800000104074a62051031341040010b541c40215205100070030ba140007a428039889407489a22200300c0d0349601c0400e115000003007100000d031f0480b0b1451966900407a01542d00041d080c80004030000381c0320b520070b8000c5000b841e0f482000b00114600440030710000e18800800c031002890441000c52254000400c45807998141113000e8116881c0820409400b411109000c0b003c2c0110014800011088400b40161490300040402e8090810300c800044a40c00380780c25000020440f0b503100c442c2c0b9468002c020300003007880d011130303007001a0010070410300c01c40b404481d074402c6000e20046000e0010006c0c0921400c22010759040a9021508105a00803490142070090030205100000b41024040140903442201e003c04c0c2403d4600005044651680c41901e040100190610b250b2401e4410545c81c0384075401c11034101400c0019018003502201c454002c0950b449854503041c4204260781c0300100100764400c00014003614150300c9414069408550 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 378688372 1250 378687122 378687143
    0x280b0103140d110307110303070f08030a050a0b062517180406030c0509040606081204030203101a04020c070317091903030e010c110301050405010209031908090906061207030504 78
    0xd581c820f0b40c2031181c5641000040d418000c01d51240d40408580e203034215414401000300c0d400043c62461714109060203207607203d0701c900d0b22000c10b001741c03440184000403491500c3d41e00b1a00da501c9405a91a0200d10b0300d8051488180020380343c200810748001512100003000280d030b400c1714020051001d800ba104000811100710b1060005072940d500004100751000703101031049042000d5140c0c0c0c01401203402044480e13440018504105039006000c0015000007000e10540c1030411040f88901c00c0100704100c00c10703c10101c0300c2412125040d42e07201d81c0d00040c40310554481000110040c40d0403440341803560101c5044011250b02080c5811b0081f061210712840c1c0040c0c0398500402c80340c040e03c91420322002e0714011108102c000c00116002d4440444e080460389013403288912403886140016900d2482c10704042c50070194049070840400b160089600040c169030694240c403900b030302c0c415070585400c070000b40180200294080b0700701d0400101300030a51b02d44c1016000e0741c0125400c90 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 378689622 1250 378688372 378688393
    0x13060603080d0b120d050702010219110928151e09060f06020d030209041d0601060311041a0a0203121504050f01121218090504050d03020c280b010314 66
    0xb0741508140700c604c50303030708240021440180140000c040c00c0b481441594a850034202c20001031104203802a00c020829000860850034900742c10740c5c0145560f4150300800344481e40c0d4041204220004503c0c1c95188c0c0c14420154501c0d1392000c000e40900c44103403203a81040300c42c41d000c5000c6c91242101250500c4c80000312040703040d207004c083c0c2c1d840d43d024151880d141c3c041600650701800702c1da5001503a50798a09116240d0800300a0a9035848000d88404c1d45003100080a0325480540ca0440c28000c1100b003043e00880107191205603141003520791150038107501a400c50080309020441c0f034031080d0810215040500010351404000c0b00c082116440386045c1c02901ca60034010303030500c2140d0500c00c40c08207800140080f178809075490051103114140d5100c07004284a91310105006e61254144400c1050511a05140d0450303031404504241088000c00d07070b81d5110310b039202401100350048c10041900031800602c066008080008196901d181007001c2d221503800e01b00441c00342c0142103 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 378690872 1250 378689622 378689629
    0x371b0501050f0301090b0a051305060f060a0219050a080f0409060b0f09010c05070f150905090f010b0705101b08130209060f060c060c0304020109060801031a13060603080d0b 76
    0x112140b035640110b15082d80c1c2099204002003000c503107916845100c1200010381ca585404000c540300030400d0f0b02282504001050242404540d55070038031403031050150018040c0c0c002059190b4001407450000044c003d0b0605c43e040c400300d10009070070400c001682031003505803c0020304c1101c0107500304101081d96000825082c0c0a0030340030300d1092a0070840700036650310a10389038041a0154040d2601c095413100d6521694000350b02900c4081020903200c2c91503504071041c480105400d0710440400c1c5008581e1000c1808140251744981202041490502204002100da4070140c2c0d001000207425143d41003504a4681e80c81c1800101c40740002003400c600e014041082c180c0c0548644080e0320b4207010007200003002018a5007114090000082021b02000002d006200013001155a424a030000400710070445e0040805d1081031801000010310341e044503030586203125070f203a00545030b038501802200301000c009480c090401d1004401d0040c100d0052503400300d110700800111501c101070 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 378692122 1250 378690872 378690877
    0x6050708090714040e030c07090501061205130b040c0905010f0302040c0e09074b0215040f020d0503130e0a0605031209030304180507021509371b050105 67
    0x900480070340010f4019030340e0a03d82c001400150744502541c1c00e00c680591810b241811561005c22000c1e22100100301181c2c01000c5045d070310049410910191a06210140d4508031000004200b0061600020240280d81025801a162030308042c096560741c0c1055250076480f80c00264401c03441c1002d2007014600805000e5042c07400078041d440d4554500700191100b00d20820680688c000b06004600580820b10419581d4441c0c0800315070443c022068180440b03c010700c0400941d48803039401018080c0f00395541c2e40c01544505120b501d810740b84086490403412040c000c2461201142030300e04a86103145000540c3d0914890404940d12500c10348203a0f50300784203254054004a04260303008103603000521000070060100c03441c1c035944052505040000004a100803a0f5402c18400a41e40c10320001c1c405140c00d1441303040701e0034008204c0f500e40800700c14100200188034010036001744588035207000220010903c107120714960070000c1d08514015041981500c00107004160340d03000c0c405 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 378693372 1250 378692122 378692129
    0x60402031009120806040e0d030204032003061801090804080606011e090501050c0f0a150b03030307050d09060b0301020a05180a0f031502090a06050a0201050a050c0a1d030703060507080907 83
    0x240d503910f083c40c840c159103c001c05409190015116401612456810020844582d58036039006940e85d2840c1418401404628400d901200c10002c40e5500b55174009003054110581e00000011183d0780b80440c0d00406000f54010080704011a00184006020580902c250002e0703c612402100d13603c0500710035000000d60401103840d030b50f02800103501c148082c000c103034001d90440e50b03001c40b07040740c440ca441c0084004079801030000040b2240048940107101e071001068004506604003008080c1c0039004d02c0c608400b06954a40340803051103a250001c0c544dd40d80034000f150f0710441c03128010324941c002c40d03000d9588071a80049800ca42130062540c000c40720b00c8000c810310035007140d641c11402d000590505440e81c0d000d1111401585d0781003200380041c42c00361102540d07803695240203030a49a00400340241113241408100f560080c0c0720440724592a14038080903010740c0311803502c00d03500e51040c0581d003602c10700300044108078180d4455401031500392035070340440d542c03541001c7e606c10b228003 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 378694622 1250 378693372 378693383
    0x4170c0a060c0201120504051c03020903030306100c20120c1f020f0d0f120b010e0405060103061805040201110d020a111302120a110a0c32060402031009 67
    0x40d03080001a00ca02e031041c50b80c40c8145400922101d00903215826605c013030f102030b107441d0420031070ba040540001041144003541814254205414200046d03124003000f410140a0660005081c0810344500304a45201c0d41c094215900b44244e0400003411f0306044501c103010700c408403240b280d0907000041c0040884401090720314500c201d086a2030162259034000802e5208030900340a40c000c0030b1056109100b000d40d1011a8607441d003c0050400c0114041042000d2810b410002c0a036440700b08400644410b48000c5065194000100d0041c0081d6108a2080300d0b0181b9074150121240c00450086000340e075801c1c0070201c50000592a11000ccc011440503034814070304800059041102c0b225001c20041c210a14a0124626541a40d00c4001d109240c4480c04042154084451041e00009040f003d01603040038442c01c0090002031036017102624541180140c445400803008d0041c43c40c80d90401c17950b40c00800001740d99500c2009031800c070300c01e0007074500c401c0c1200c1a40c441d800d0b100d034112 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 378695872 1250 378694622 378694639
    0x30c0912021309060204180f050112030210050c1b0f100c1b11090f06100216030303050a11071202150408030f070e060310030b0606031006050f071704170c 68
    0x202c4074000400c1d50403821a10140c013030000013089180070104c519070096400d00840c440440e0002d040440704160400d0001a03458401640440e40c005601d03110b003614000c1c001740d203498119490240d80541640441100d080e03010710b11007264003140074910702000340b084808005000b081d55041d15441214031000030760074490301c0984c1d80340509080f0745a0161f80002c4100e100480410740d00c00c0115042e50b40803440509001e03d07814821038038035800c20b251024080c1c003009020400f40b0021144000750425440e000403440a1210364462013100300d43d070019079a5103001d440c01140c0309000300c81c0840980500b0500c070051100e0301503043c1c880ca60201c541861a5038000c7c00b0030b100300001d0150003c010100c0120500c5840f0b1034000c8d8062150700c06210304291a5141032001ca500052215008120920611805580303980005040d1351031410300644450041da41c4107540c3c0506840907000103100721b404141c201c01103004009840c2c1d1108416003510000c05015520343d080c1c5e541c40d4100454 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 378697122 1250 378695872 378695899
    0x402010f110d0908060f010608040201182c06030106181a0306010801091b0b160303092307080f0c22060f0509061c0b0c131d0603070806130f0b07030c091202 69
    0xd02c24081900c800a591000341944590b80b4500c400f01c0c3b5489480d1176107112030a00001c031026004030341c4c4180201d000f400700394200400101b01401c03c2500c01c6d03085458002c001d804244900b880800d000010703086a0080d0b0317540081d075000e40031040d010303074001e49a07a0b920103076081c0042a42c0180d8610384100780c9019074001458281c5034843c9000c0e002c046d500d24003040020b0b00481c5041c40b050700740b92100710300503014507001d003444200d42c00480c20f40c1c8808442600c1d80d0010804c843d1080e41200d401c01c1e0a1070007800e0448000c1c0c2044680c0e945458240085940c070f0281c916582601c005452a03181e0365506000d001c01400085143d0142c0448448284005480001c426920842c032208c05820441d040900780e54803405500004009120903801c0b458480071808a954009000c400a25000b4600340710726460780340c00b50407100c0c2c4e00d14600354034060142d81c0031646080d903801200c1182c90f280030b190003401080441101300014070504000500f061081002e141c005170003c0040e0400c000 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 378698372 1250 378697122 378697127
    0x303011203051207120c02030909011401032c07050906181b0a05040810020f0a030903020a0b010312020705150f07050f0f0a061b080402010f110d0908060f010608040201 74
    0x110034200300c0401108014645850414901c1680900010b468200041000c0d4040806a4015005034811940244240711042d41c4a1815604403801800301200c1e031403001c0c3c0100d0262410745200c00c0c0d43c00e08201c80b50320300200b41c80c02144005641083c0d07480b17541c80b44204420f01c201590003591020080f1140d01b0201c1d5401e42c801d03000076042da4241105002e8100c3d8460f00c5d042090004041a80460108100503017440542c1800c019200c0842c80d0411412f0b0003c050302500d00b910702010b50301c4421030b04043c002c0044c8548150410160722503981d4a1400680d900b1102032070358018001c070400040d903400d00b800844d2207a490718507240d00b009100845803800d608001c1301510f00307218102141c4c40200f0140300f0007202000d82c10190800600398188a02a80d210a0840800c00210140c5034502c0364040116034203d507091800511040d07650320100e0b481c2e00014600c07038031800703852105c640301904112802d00315040340c4d050384c106d0303a50242403d01e03041c401d1291314042041d00001070010b41c07 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 378699622 1250 378698372 378698399
    0x705090c0c010b010e15030601020c0901060c0303240605030a02130b030a0b0910060e0a050a060206060324070e13110301060e01181401020f0106060504240903030e12010905031201060c05030301 85
    0x3001841112f00d10031042e000202244001ea209e8404282d00c640c0220a141c0d150203800559021107031203400d90080d0940c90702e00080380f441040b04106001c00424402091a0102d440b00303000e040c800b070b10450b2911324a47d0158030a55112401c10302e04000c0320142d040542d1081d214006960380c01d1040c1780b814030f050396012106180547d00140041c4003080d10340d20b003078001d005400c1c0f90b8014243c0b0b14060042c14500810341658130400b4003084080d03800d100c3c89004596000f10186004070740f261400003c00d07040c00d110307410710751001d0601e10413054086881c00958101c0b400d503540e00102c0c011712401503c00c01c1c03412a0410035062104002e0040c81d0498016420314101803044445040c4050481400c507401e81e0002c030000b4200090410405080e110f030800710149014896850780440c04000e000942144401020300078818181d03903490780c480894080f031030341c0700000b4006225075140c0b141e00d9070b120619003070500c10f20fa000492180e115943c030001e042c0c0e02000540c070710307403d2a11441c103a4 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 378700872 1250 378699622 378699631
    0x106150e09061c06050a0207030906090f090b0d06140f0c07080d0506150a020c0906040507021009050c190302040f14191b0e1002060903090d050705090c0c010b010e1503 74
    0x14440741e01c80e03e0004c0c81901c1414441e4011500041c0c69000303920f001000c180c402c0d03001c4401c0107400340052040b03000d0b0307506040c21200c0d01400000c40e048c8a0700411606070b1051300c080c0001d80780054001c4446c84402495104a0382c1c941d602e5080e5440e6590b511090085203005043c042c4d09121803844804c440e80b20a4025400403e03408150300c1c80369000003070b9400090300c0001030700100c0c600c2c1d43c0340c01c04540090b0011f0040301c0030f000078030385031000035501d4003265051002103803030710390200034070030180001c440ca424054180c9004015050b0104140381c000d01c0224003c0d454000840c00440803403284460040a9a01c00f00aa4658905494000403000310300b071001d640c2c0d9091201e00d00e04020090070100d846e40c8804180e07088460400842828040428003590422810408050800b00448821500c200d40899182e00b030b5050036403501c8070f6900043d8200220400340b02c00401c018000d002c0302000c030002030051100171001164481c00010341c00c0c0e000301c140c0314840102c20b044005142e00 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 378702122 1250 378700872 378700909
    0x1506040f06032004021206010806120706200c03034501170f190615030207140d050301050d08090901030b1012050604020d0302030f0403050106150e0906 67
    0x1a060846000d6048030300c1d9600448440311080720090518400404149020004460850410150b409038688940000345020b04001034140001c2c0030b95600100030240410000c100c440c45500d0710006482c4505034401c070003900c480c031402c1140c400c40c0003480c9180c03030802501560409110841d884242c4a450310408a0450501d402d640300c0ea69188000440c440c0b520500c00780c1c3c07481d0400241c0003068001c0f5241049141d02c042080c0f2041031110340e60401442d601c002e00b00e212462120000f083d4613000303040700d4502105060441c69040e006072a589008007201c4401081c280b00e21179590f15684800c00c0481c00034401000649030003005403000c00d00400c0c16515150b20200081c100752000d800c100d4400000320203204403601c1010b00d010140c4110304090041c4061a198150758070f20080000744110500e100303010400d40b00740280c640e4034110b0922141c842d1b840303251541c081d10b10b50040340380040c450741403850460300c501c1c0710094140c0c010341280702c10f842c0c2c142031000850f041c4a50320107 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 378703372 1250 378702122 378702131
    0x6330b12071b060504061107120503130524090328030b0414041b120228080c042a230a030203040b01171005060d080406051206030f150604 61
    0x1009400b41c108402642c820580010380345007038030308a01251288000002d040c17005001481c0003840010300c01e04281c00340d091494580d1b54070b01a824400003042402810f901a00400350200c415800340303c003202241811928a50780e95800c501d40d28002d8010402860b510207204074012104050044060040751a0200e000450180070505803240514000c00d00788980080001b4040c841d4190400108019500c500035813130451006000100c0d8900179101e2101201c6207a4000114181640e15070492071807114070315960b40103e51900070106100d4003071070400c0c14108802c42418070400000d02400c400d80141d00e1540c004032016480c0400045500000442c1d440e46400000041d001455140e6400343c0d492030f1910705203020724010303403280100340b0074070360000e00401011030360032110146140006901d40d60f410000d200c0300c03041a000382003a00c000a0200307005502c0700c014070141112024880e0315494030f0050582d65609413000000c5a040351003040e116035546032140b07420610040001c11b = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 378704622 1250 378703372 378703397
    0xe0309010c0318030218100f06090b0d06090e0304180b0108010e07030e10150503030f0a1107180c020d0e060318030c1c0210050601082206330b1207 65
    0x200d403031814031b0718400150840010071002c051101c40d0140541140e0886800d11751400b82c2c040c09080140c020041d9040f0040790703240d0700300303402d5010a00400c7d00391818003e00d081300700f030039840343c2c49402881100c800051519001450034000e403a410107040c0e4940000b41c0c6030051b0b0000c3d140001d0440820075843d6104110400020802c01d0706100001c600000c051010704a081c40316030b041e5002e24002d81040c45a00400700c220b0b07084c0c2d8481b81c07090529114010921144901342912a00050441c0300d501c1c3d50902c03100140e03800208500c0c99902210b03640c05031400c05881502c125031043d540500200300140d559140c091003002601801e004481c00d00079034800250910b40c2503403c143c0340215030031540c951580d04005280415100201c10402806c05000003002c1450041c0044841e6002125104401d401e15091128083d0072120410440828096031121a45a150480c3ca00481c410241446100e5041c204084906141145103001c0f102c84400d000d960005201a003813001c03014051 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 378705872 1250 378704622 378704629
    0x90d050c062d071d190b0306011806080a060504090b0403030b010215011523040501050715050703050604050901230604181b140f040906060515030a0e0309010c03180302 74
    0x140251041c0d01c620451101510200c604807103203400044c802c642c5d0059452840000600100c156111014082d42d43d699000040e03a8030b00c20004500307030000c07002d000001d99560002d4000c2c02406541010300c60f842da1002000f040d1303034212002503c0707c0a06004500000d009500c49000f05406005a8540c42244c0d0f0801e103084e0000d034131404030b202c80803600c0341502d9400f140a9844109010a40e01c2580c4507107441c904600440c06814103005001440e0024011061821030b040d00c041e08060015160a045c01400341c00d09484850140f42420041047e644040c01000c1c4901340030780d514001001380511001c003520000d03081d2504181d449000c000044d0409030225213007401062440c90804590482144d1003215030700008680b01e8800c031103c4286d4514001000754501181d010070404580d09084008100c140c0c0020351003882e03146800014804000550300c5090074002c02c01800c10b05078007250710fa114809541e4002000802909c0c002030050440e000001700c045243c0718039980b00e5010 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 378707122 1250 378705872 378705961
    0x51c030e0f1f0e03010507081017070b0a0315150f140f030f071d0108070810081c02060a0203071b0c0905040c05030c0d02220f02040e090d050c06 64
    0x1100050700d0f00240540303a08090103200d0f0803910510b8001c00603c3c001d46100702c110340a01401c2d00301d41e078080039141d48400400004002c0c0c074598440b681d64200020000d4000c108400c1c04803250b03949600000380c1c240210281d005072400c04c1d10f5640542c6803801080707882403004060080d00c2e050074800c901150060030041c520800140c400e02d00c80341002e2002034506141c1108921141c60202d02c00700350b07030740e001d6041a0454141d0078250055103526640785040016600407140d51320a02075000141140c1c041c60104140454003130301c0780c40d02c03682131050a92004a4804005c42c24215490403803010707651101c4d034028040c0e941d10201a8440c4208825680c0c26103081d01c0c036640325a07050105107800d2000d0a20b0301412035210708a10f05513030201d0000c2068400342e445903901100242d40700401a00210040c595045007150b85a0301c40a0780108024165004c1210388205c0048034803040c0184100c0d40314a6002000301415074802c10802401c182d1140d04542d0501c80f50855464010842103 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 378708372 1250 378707122 378707179
    0x30a240605040617060d0201030b040e0a0503130906080c060a0c050303010e0a050a0b090a0e0f03030a050907080a080702040b010314090106030210020123060a050a030309051c030e0f 80
    0x560701d94642c81c000300100610042101c6920214510b01403100c0c60341c4820180060380c1e070a007404103c4890780740014004107880003802c445401505070b86410072070701200419070284022030038a102034036183c1d180125500c9020ba12900e81c40314407990030518000f40031380340c0a441460280464070003070ba2890300390381003070b4010003071600e240c0c060110064080c06525444110424200502c50102c00001c1d41240d01500c452046a82c0b003a540704668000e20409000e030440008595503802c120342994010324003240c07101090301614001003100c003000703c3c0314880960007000e01818414240c082200801040d003003e070601d48d45021003d1549111140a03108a00207400003481900d5401800700300040c0036001401c591414600c030030701c003090945001004000385600c010030360b82c5901080c2e1034a03075a04590340c842c0c20034400104065004485c00c1c10381d9401c0d10035500100f0080c034040411221003000a001c1413840a0f070900905050210b041003410081c09003403840d41c00d0307140c0d41c64903181c03c2 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 378709622 1250 378708372 378708377
    0x16080c030307121a120102250b090607210b041802031b0a03060b031203190c020706170a0603021c0507290d0905030406030e0c03070308030a2406 64
    0x410411060341095080340703d0802100140150915803030000000340e5218801032240340b155500d04407086095054074640d000824040e500f07600680108920b961858001300c803400040760010303201c08404105240203420700e4a54800340045c6040600350307000002c6c00c0c65500e5540d20113100156031540565030384050049107c3d60491403900505051100e0014040d10b608084070342c0390501c1d1558004001240c1d00048006015940c40c0002800c1c000c0b52110320884040200a215030801d0105200c841c80d182d500301000300c08019402a6201c0c2490b1145902003000300705c0b9071079203150102d8080e0744480070100000d52162203900155441003a045000c020302c8405000504200d4204800d5001d84003452303c2c5041401c0c0911011b0008240001c403404400307010500380c80f12025500407202242e030000c180d940390354450308010010700c00701e070b0840000e20901030101000e0501017074040649401c502880c0c134607510071421201030900f00e001c1c0e542c10401c0140e40140851001c035804003415165 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 378710872 1250 378709622 378709627
    0x91c0c110a06090905090d021b0402041a04050a060f0e0d06180b01061715040b010c0f05061e04020f040b060c01110405030c01090e0105010c0807060504030305040201080a0605011416080c03 83
    0x1300c400c41110002000d42c4455441003454186081d0005202501c01d085050303510940ea121501240c06800f5540c01031420030400b044c42c01e44030030280c0140099842c00d5a450420503900c0c41c007111480710040046000c643d641034110102d04100b058907002c14011100030605500d24982e0100014060310250385e1980c61b0801404165070001d0f5000049450202507142800c080c00000902104442403510903940e40d42c2c4c4034156401041c0c400d50140c2c02c0002031031030341c200d41001a25041d0071110440354441c200c4000302d00c0041400f90718020344d005442d04010203040d03130a02009140c10b400300382d40890180400e5520060074041d00c000550000c88254413a13240c2002d1626003848002c11506102c09007400b88590740c07109001c10304496007441c1c0128004000e00f05021f191040503809800e00741010104000c3c99090340049028074400e90325034080f03a844901d20f0040318054000c03140001c150481c0c3c1e052040d00c00016205481520f030114040d0800b9540700301807503111444034513450300b02 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 378712122 1250 378710872 378710879
    0x3040b2536090e070b07080a0206130f0b04060e0f0109020a0501020c010807030b06041715071107140612040c030b060105041508130206160b091c0c110a0609 69
    0x100301c1070850110351496021181044110a04009907600403800525500c551000c61084204a032400a00429003490754400f16410440c4103903001c1400c59026200d00008200000c0030f541108500d075811121005c440302d0390b5950071a01c0c0e000030b4010b4a0254460441c1c02107130030148900c084188031200000b409503028814030400718400d520160640d08400040300b4141d030450040c1d0361000d424540011420901c0303000030168040c640001c0220400068070000000c0c0000d11960101d07418254000705507a592400c64148000300100c001680003080c041003400e9600084e00c42c600401081581030450b184081400100100c07015540c254400d0710030018041d4180c1c41d10b40201c404c2c40c00c0c1e8502814000c04442d02d4000d51000020041840c0c00203c1c0c010084014041d002da00511040d5500071007c1c1040c0f03a03a110a07000e55010068001160716804c00041c04004c4c0d20801501099440c4004426980b10454140641c0c0342a080c00f42e010555031881001c0f40605855241d10110720304 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 378713372 1250 378712122 378712157
    0x70609081905060402010507061e0c020105100b040611030d020c010209100e060316020309040509011b0c110415090203090106060f0c0201080c03090703151b0206070503040b25 77
    0x15480c01080695014030205002c90700105070580d11540a00b411070766006186042c80040460110080c80025800f16126002440782c00c62109186681d00030701c00c5888854010807130540da442030400929041004000b0b85000341020304440503c902540e042c8803007985200107a03800b02581c0c1800381d60018000d0414501007010184a02c540d1500c0541c154104c00426018070016087c0080420560500007003d48204200c1e0400c1c10041c0040c00241000188580a0300709106121000c1002e81501b401e01c034810000b0400498000040c10110010306040c0b0000301042000045015001500403582d01c2040c0000e40c010042480000381c00d51401c04c0040c000b8000550510030080d19030b04050140c2c2c0e0042c00785070000c00009617190b40e03440d010415171a00c15035610007030200b00d0a8103942c03520083c5610001b9031600031202d111a40707145010072038441408030b4504000c41c00601c089400b040711070342429403140148417013401080700103610345134100c00d2034251000030717144c41303604c07242c118 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 378714622 1250 378713372 378713383
    0x9021008010608040605250909061505040b0d020705070b0d1409030d0507030b0d060509150108060c030a0b13050a061e060e030a02040c05040314150a0c020f07060908 73
    0x41840c1031025541401801403900b400030300042c1c0065160700109108821401d400c0358a000c60802640340700c852107401070f00900046c0300b804003c601d42100081c0400209070400880e240030790301e451805080000c40400f54010b01018841d1030380c00e0024030b00103403080103200040c0c40708252868403100041c0ea21800d81da000d54003690411003500c24040d000768004240c581c07400307140e000400e10fa91038540460040000c0d400d1540c0c00103e9103049002d01469500ac94043d0841c03a080e981c0300d04504070102c110b54000e00c22860b42da400580040d000114680185030042d082c910041188006440060743e003500c24010104115036540501440141d03a1081c08020011488100a42080c1c5801e2100c59101e034403c91082c0b2103801c155503000c0d60180300c02e0400960003041044084c0c04000020050307002400300b110705626007844000d00c0c0d00f00086148403c62a00f400398629642c0444240240000b2803009096129414059096940074810384016100d503995080da40307032821412605e0607 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 378715872 1250 378714622 378714649
    0x7050c1903020f04090213091e021008090c04090b22032c03030d020306211e01140f16050f0406141c0221090a060c03060e0a0902 57
    0x20126401203056041000841608694040750340046021010002c030340a4040781500079404041d9000f0601803245c1c542c05142d0040c090020300c2c4445d0290780c0c43c0042d0310b00c00440a503001d041d5400584903035110302d2019030b1008a500584103420b2084c00407802380c400403a4110f408481d1002007060100e400b04a00c0c0400010440114020300c0c00d8030301402c8100000d80161044010000010080030002d41c801182e806c0a000c40340d5800d01804018029041a140940b0440298018094a001405804024200003c094000130a039010176140d0a54000c4e00140a03549407402480344a0001002071310034000d612269146150940d00c40c8100005c90b84a07005011043c040050090030050584040c2d90050502101d440c1001081800c14043c003044c11050a00f2600601100741003a00074100001045881501580540032030a8079444115010445036102050140c08101c9a4004403510003490400080c40381c2c8440151a91071800c44404c0101ea4541143d0b6003182840010070210 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 378717122 1250 378715872 378715879
    0x3010510020a1211071206060306230109270f050706050406121d07030302030a0e0406080d0e040605030106031a01060503010503060703110d02031e0c0f0a080a09080a0507050c 77
    0x508882e991200d448421400c40384080205607103442c5902601001001c018014030300d01e5142c3c031170b5076240802c0a0141c0e40070854000d03041c9000803440020200b001701e40741e050440d00d015a0fa007091a035500a1064600031508004001c002e6130720002c2407800203220b00c0c080d40450300072005504003a80792020a5104404000c0100402c02ca4242d02612000d1811a1150007207a83e91002034840020001080c1c00207450290000000403d50000014142c100c13160301c4180c00c2d81e081808210843d2103510423a109a04a8803800140074403404150b50f10240007440041c1045e00c82002c00c0c01c403001e60708101c42526036611070f4000c2003603034039103140140540c4c50301c14555818800429202c400141000b401d06440e064901842c0c0a44800e40700d40354140c59085440386400b030000f01c98082c6180e8104c0144205c0004501809104011107042810a00310341e450015001c40440396410000e01e01000c0c503030780d61044000601d2a80050950214540c1c0712a1a011a41465420101c0386001c8510 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 378718372 1250 378717122 378717133
    0xa2102061b060615070b06060f0a11060903040e04061d0d0e03250b030a020d0203070806040f0606091703040e070215011d011215060303050c0f0c0f0d0c03060207080301051002 77
    0x200d514242c003115105c40c0e110380621140d0321404007003002405442c03a0303801d40031008034080c503d865201c0d4001011101c00411203046464141c2056240d03c01d50150303200c00450100001d02180e40784d000902e003404045a1031324280c0c0d00f1522507050900c100c18800c001880400046d0442ca810042c0c40c502607a2080340201a4032602255141803140d172044001480b0b02000007080d248450303040c6d5500c40d032032030b40542d0b503440c22404c020080ca5040700c2c0e49100310720b031014240700c1c81e6661007082d055501d19211a503045041c1741d000780a052600300c1c445403920007004081581043c0004082c00341134660020038210200640d9228000ca05030416074140512404c4503a040010540c151f04448249403010400032003420b00600d0340302c0c40002e10784190309010f8000304041c0e0040c02170081926100a581d004140c100303007540c541c283c00031090341c41080c6240d000d0540c9030100008030803c0c0b00304c0f6240c418580c0c87e514034090341c025078420f03a03045101000410650816110321035500409102412 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 378719622 1250 378718372 378718399
    0x6060103061d040b0405150708040c0e07020c15070611070c080a05030a0f030e1902041a211f091b181d0f030301090b010206060a2102061b0606 63
    0x31003800006201502d4684c110300410306200c41400b00036000c0080980c8908a440d0002c0043d005110541d0205c0e00c1d8030204200150310400b00200c11f00441881d405020440b00c18410040722280070134074158500c41c10040c0b4400500580f150b400c800d04450021600c4012a04041000d9140782e0320074100da8002848800004001100315080391416050840c48008031a508a00400f02e09151801174410082143d904d6155880c0c0c0c60b140a00c212003d000251102c0349841c600e5071200380e0325800c03810720705001c1914221030744100149400e4000f1103028203a10542c91000d038a000202e059050350b12448142400403103060170000c6a48000046070071032800903800c0030403403006448056195107031902000c0303041d03041842c40f405607000202c4c2c01c0040c0703a10a29450358000e1207000074091410303003548a1940040784141c4558001024521090301d40951000061070300300d1180c6001c0c00d0307285204c006039a4030b00038252070307135000c10f40c108028114004980342103405000750348140001c41d07220 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 378720872 1250 378719622 378719669
    0x1c271406061f050d0b040f1a1c030507050a1704080c010507030906030510030b0106021605040e0d120e06040321060f0b0a02010209091509070504080706050f0d0e0606010306 76
    0x40c8420b0b02e103181044c0d4851318032200900820034000b4450307001d03040c030300d400c0700205554200c000c0281c2d008d01e404c841c049020702084a4030304090303200d01c080c14010903058003190181d40135004203400342d0309031503015065955075000301c04648108859490041428445200308001d000252002070800e01e10700260b54502800300700103841000300705600e0b03100180b00006441c401c140103640c40b81520095503103030600a0b458484e035442814511045010000d05c43c60720b4028107c8824101018150b03003451541b044500d10302d008070316a449500d842c1201e03180b4104000c0c0b43e109078060750f112600d08011140310000d0010200013001c455003040c409110140c11032440c08212280c0715422a40d07a522084182d0187c080e88030300380d50020200003004642501d43c100e400840030200c481c0c3c582a92500d6040d1034502880c09652203540c003448051000c580114010505006444121801c002c2040080b5068400401d032004603900000c041c80b5540d43c15000307071030191003000c80c8943d0a51004510 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 378722122 1250 378720872 378720919
    0x7031202010608031903020c10020306151305010f0908120a030c0f080106030c020c270c25031e0903050609011808090414130c0b1c27140606 62
    0x5681a0b06034010105d42e62900950440b000d03040000309036041c4540f03509600c40250070840c0e07024000e40c8030000c002c4641d25820100c65204904021a0b64a01d0901004440e0781086610b24402c1c1f018144010851781410026221246040201c0607603540d0040802001d5810080c850014170400550030340c0410f400c85071143c107449841c580000c061102020881c60160007140c0107070840d540c00c17584110305050501001064031010a81340e8036803200301c2c00d0348a0348034000c40c00c0068800360b8411485200d00707504140d6254028a80380c4402c072000b2580d07010315240c0a40c08001f0641004081081101c20b10007243c0c0400c0f800300801c44d50b800030401e0700b840a100900141008000503100c94107036504c4c0d00c5880200000c440803a01c0341ba00b40c03285048100c186d80c0c00d450700300102c58001180108001215000468103400d103510001142001d006080009600c0d00c0008800c1300ba1260702078400701b0f841003640500464103d0b05018948503003023001c05072409010320000409040304408800e40e = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 378723372 1250 378722122 378722137
    0x130b070804030618122304090b030f0a0c140a0b0c01090516081f0204090504030906090b030411060313021c1b08151003240c0c02090606070218090703120201060803 72
    0x504100c01c28198606200e0906584585402e10001040118141008c2e40c0078041101054049030300003d469030116a40e95a13000000b003924400480c284280c914503820081d10410207800e82c14040d03160480c00381c00b40c02c84100720100380e65800c19a42802001c00c405554200c4040b40544498207000509803603010300301d1402c00f5888543c9840c0c11181c4240e04440c02884041801c110505140c036004125890b00e2103800001000d013800030504410000c00c40380103541c001c0116218240030414001d0a403c0280010a41e03100844100050389840c0c804640611289100d4035040d4240d14246510140c480d040d142c101c09496000d01c002c0320b00243d1080407030302c0780e05a1400c95a4150f40078003919031641009010a40003038840c0f10700308a181e510545425420418070040b001450221481000745034080c1d07001150f9004242c1e07905004009024040c000350902800c2140d10b503440141450035030701c405507a880030204000340722009030141c20080e950700c005d211319483c100b601741c0e030f90050f0230 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 378724622 1250 378723372 378723377
    0x9041103150d0b18150f0402031c0903020f06190302040f1a0703032c150c190305090c0d0507090b031603122606010f02070302030a08130b07080403061812 68
    0x80d09030070089000c1050282840094290082c5071800c80d48060161000703a0b002ca01920800b000304128131340845281103442246d40cbc0b003020a030f01d90303020404c0d82950311350055005001040f903400007002c424503a80030310b151a03c01598aa00c0c29040024034402d40d4002c0541010301e801402414410508403070301c02d501342ca030203d10801c800410300c3e8803209a5122100320300c81c205a04a5541001c140c103548811034451100d020743e100031f1030000034481c0070740d4688003480b042c105400d50303406a480039410940780011104450044408101543c40c0000290350390703805000b04201c03e0226001d1403109600039000f500d4580800200990640301902000b050414812100b40c102449001c482e0110074910f224240b9245c0c1c4c50f0a000101c0784103880d20303800a07000070344a80c1d038140001500c104499010700142803400c0c49032a81c00c1c0c19040b00e17000da05902c846400c005130081e01c0c0005090308034000d03140359a84924514104003140e4605c10100841803000b0340d0034011803049000d0b2090040e8a0 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 378725872 1250 378724622 378724651
    0x60f18010b1305060a0c061802030616210e160302091503011415040c05030903040303030f090807050f010f05160806040b04062d03050c010c050309041103150d0b 71
    0x20364a01d106080c00c0c0c0c001540100012440c6070171160f00503101c011881c001c04042201070700407189400f448079440c0740a0740560110003c50152042c52981d40d803611450b15000180d041c5c01100c40c41c169070100501d41c0015111103070700030002401e00c640c409403a420ba00c5c0c2c00410345980c1c0880c0740000001c00a50b11b00420b040c007444191802e410019000c5241c0c070320180d140c5480700100700b00500c82c00d074881c011032800500ca00058000c4040345d0107604050300640c00c06107940c4d021000b8000324030302c206115444240840c0050742d16000b44c000c40e0b201d4405400700750742200c40e0500312440d00c0c15081d03085003001c05000c0c411003440415080c942c802d141200c41c9649000205018090668486802030303d810400512031406200742032070201101c0d20786140303868000f5005008400f900000e4280e4118850601081d800350706464030300c40c818416282480305502c0003600b111800070007422032000010400a410b0300c2e10a00325040d1a040f40c030508164016194900c0f01800102408490500c2 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 378727122 1250 378725872 378725887
    0x7120c080613080d0b130504050c0a14040b0301110c07080607020c0d0206252103021201090903110f060106030c050a0f080a061a04051503011a0304030c060212060f18010b 75
    0x4c9030089601d054010b003030503c10796802c60a104c000c000440d400d0301c650107a0000c040d810300c2c11303444480480e0140150b000c03007102240f003004000d00c8000f00302079042d0340c1d800510300841c610b50060007800004201402400e4908207036a03041140081206003150001946a5000d03030701d0340b045034911034040d50429120807642d00c280390804200402a0504a041c0e21000304100840300c4010701207003880c1c070386030a880350514160144e00030385803241400c03090b840042c0704a4240341d11120006001e40b4080002e203803410b060314140034104120441d41d800020040c03102076010700a050503203d15240203071402c0821301004041c01036100c071722001c00403c98046440d8189940104010740500c1d030880041d42d003840d99030105a8403921480f80512503200041100844000590f812201c0740b0180322800340d01c4070f150007610750000304210140700d244210800450b00a201400000000e01032400b400c0c100841003000100c0e0701c082440c410001c60082a91410360000340368112400004119254142c = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 378728372 1250 378727122 378727147
    0x70e0c160804050316060e010f1b050309060705060f010f030f031404050a09020c0601060903260d0608011a101209050106050402070c0e0105060f030105060901090807120c08061308 79
    0x2c1d0390001d64548905140100024103482d45a01221041d44440c4820143d000047d5045036000c01104041005582d1003004a00d88000c441d20320352241042e00c1c50045031000150307454100a109a420364880d504001d441c1300c1403001c2e1805001d450f10b0b415a010b00e1513884d0041010018030040402403040d00070801d020b40e503401c0d0f4001d4040100303200020741d00d400800c0c000303401c0002042498410034000007003041c000c420000075607800c610040d884074440503071903008a950021100048104100078128214a071048102030720f407182c00456407824090070002d84034800302049110b43e0b560440031030119005010a0303558a04000040744104041c03e14500401a40d448950028000a001e004108900c80081d06844034844c100796a644c1391024410180a400400c00c2c440804000502407032038040d002e0800304405140092260f0740700c4200034200810756010032840002107424404110801100740d002d4000d50000306070394589030f010303a46243c41104001d403195400049401c500c0c40c = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 378729622 1250 378728372 378728377
    0x30c1403060112260f0d111e0f0d052502010506031b06040305010906020c060a1a040b12120a0f11120a0207211505041203020c0a0605150102070e0c1608 67
    0x82910113401e8407a214141c040e0343c65032200c1c2482c0c0e402072a041c00c032014810101c080d1040c0a0b580098082c0d10502038004181c0c0754000104410030b2007041c800780315404418091207100b400a400e40c942403e204800741404c03100001e0741035096904000400005807000260900c050150b560003541101d500030200c1c01500c19908050220b50900c2c98103000d209040e0014400c800c40c810481c0d86075903a038050007003100d00300c3e0751844000c0c000b81c1c0311500751b150641000c40c0e80d136001040746421110681040d403410100c404c01e44449440401c00380c0025801140340300b42c0c640c45050070300340c1c5a13003c2e00d000e0300d070704010454101d40d00c0049511612140300704aa20f001d00038011600c601c3c2464210032580d440001d00080354000303944504403803d0380e80ca001e001d000766801503400080e00140d14094019400042c1000b40521032018540301217203840c010103005000b00301d02031000c00400e200081c204001c41d0010465010302200780316110005004503400c418000000000591061500301c8651 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 378730872 1250 378729622 378729683
    0x702011e1d0609071e08061f0b12010305010605060f040e0703181412040e0708190920120709020f041d060307060201050105010909020f13030c1403060112 68
    0x284119001c000701020f00003101e0080e52082604881201441c440031002100b450081415580001012800020010344202c0b000b002d02c00c426503e8948894444695400042302e07107007180594401001481000c2c4030700406003400790307003062030680191a101c1d07261069100d40561403855038002405503200ea4800301c4100d0170030800e65607440c11410690a680d070704810003c0c0b203020301001058841810011201100c000040760803442e0742e400c10590300450028105008070704590302494154140b40702d004c0a940c0b04000c2075003440800c4115441904400c1c1010703000b4101c46204a032400700002d204401c60764900d40240c0e9480d500b04824546000d594041c4c0c01f80c68822030a02102e058080e0000d00c00c05043e022030300100c0c0d41d480102d003070b100c082c8541400300c1d006800c24002099142c0081400403812121240b0703200700303280c01c850303003001d20750090b568000340b03550600420440d450400d045110840080605504045501848550480000b07041004e0703003894070000624591040b154 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 378732122 1250 378730872 378730931
    0x16081b07290c03100e0403090501080907080607020318030c09062101060e010918020913020d0c0605090109091b0c0f020a03060b03010b030708070e0c0f041503050702011e 75
    0x15040c01400103a06030816100381c00c130000e60180128505080c10038803889543c2699034480c1003131802c0019521000e001d4902103050140000100c0c50890400c071090103024581d0085075601400303001210007141ca648124400c3d002403200c500b40340d0320340410642205044401c800390946040750906820301e00c0a610006e5404c000c00080c1404801a98070304030354055005004441d011598400c0c100305888000f58020300b140301140c000791800d001183d400340b026000700610b031413642302d60004075071990240000810020324203001d275034030008407001800c469005110b0089800b035003001c46203e6688000800c0080d03c1e0400034005685188206a070700034040003440c648070300b000f9020b40508900e4a001c0c0d824076a4148030b60070f0004500301190041409042103505113030104001c0c0c0317400f92803081c551900388a8105082500c2d0000d000030030040004a200360403c0801030305032100200001c0039a49004030383d40c990f46d149000032400c03c0502d0070001d92415504485c262089803444906107 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 378733372 1250 378732122 378732203
    0x15110d02060403090501050903060705211f0812031501140309010c0e100e040b041b02100606030209100c0302010e1914121c090b16081b07 61
    0x20094012505074041c2e40030355110b000f9103031070308019259440b070344d20001d4059224800080040d0b2084001c1e20001d40900045807411042e070090070303201c40c015224000c4014401e0039031405180400f0100f0000e21904000d08030f5100001d400d5121400010016407009010f815122082d070310a80c2c040300c024148068841d120304006859500801240741044040b0340090303900c107110300e0031000e580c14a140554402c91440c1105c800c0c031015040f03954172940c1064072041099075000b04c000041c2e4000c1d119900604100d031309000010191007141d8015014540b040144102903160380914030182681d50500c80c07402000b603d0100c3c018402036800441c2c9001c0d0080490f04080b00b50082c5030f403140114460780f011400394103101c1e141e0214400c250406041008085066819540704242d07000482c000080d6010f00740e11403240b4800308541c40c918a90010401c550503070b80007511540c100d9002c0302000703112580001300c10310b61b109404001d80701040d804404007100c1140340104601d8410074000d41d0 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 378734622 1250 378733372 378733393
    0x402030c09010e031f1508060f07020606010305011d0711061008100c082a04090c1d091305160312080a0c090b03150d0308010503070b090303041511 65
    0x9180780c00440a040c000b419500103d43c42d07250008000d2000d890401c002070810440724003070001007501c2e080840c1500d9040c40001038141050100703e100e448842c9032400145841000282000d00040c81d990500d890440180881d40340d0022890480c0d5003201c405c078458944500a6178002904190f0b40e81900c6120208601c148004003c00d08443c0300c08210380c5c0c503403002c04040040e10001c1c011100011550400101082c1c081082c00c8144074a03403c0c1d810307980742071002640d4907502503040390480c40d031900103141c0400d500108104c0c1d145404803180c1540507903000000c00b41c40b4017034800d003000e6200240900c280301c01804044032484a0203102c8454664a2808009201c04202d001001c11414000507250b07510030b00078294044030a94807030f85841d003403080d104400d42024210218840c0c81d00e03088015512000f00b00150700307010780c80d200d1040d1724003801c041ca0300b10315422204007000d0501c50408545c0300001030b18143c41009040d240c507403000800403582102e8441900550348604034804 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 378735872 1250 378734622 378734641
    0x3070210020d141207030908070503120f01090504051f150e07030615020607120f0c0320070f06020c0f0d17100b121005040f020301090c0206100320040203 68
    0x3410b001d100762101d8103100300c41c0340ca40d0341e9030103615100a15248404000762050b03110340c1c4041043c3c0d21841c1c44c2401e21289803034081c59a00a8080c07141c1941c0f543c001d004020258144840c0180b0030b41d4414481d6207005d6403080c0e201c00c45076a10030700a6883c0c86a91200e07005903004110340c100100600c1c2091039861054012188050b90040c010910b000404112824010461006054660020861138a8888044807184050302c42c41e8089030359100a140b042c070060041c2000b00c4c11a560124002e000720315940020300401c1c1d94210445001c00c0441d0002e83d04820710003000760071000050f1201c0c01004440d0500c3d0540040a042e03000d12440541c0140c2c00110440c4900305a10303580c02140c0d100c0f240c1d2000928640906031b581e11051001d04000c2054200e00c1d9444580070b072140441960301e0b0003280c01e0314548048445080e401000510651005200d90140b1500c940700914650812000215000d080c038000079003e0028903245200141c182040c1c10148000580110359a02e40328032074 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 378737122 1250 378735872 378735883
    0x1a07090b1602040c03090201090b03040f08041205011a030d0309080915030a05010e0408160c09060801060317030c030f0a090f060204063f090501020711100306080601060c050307021002 81
    0x300d10484c64020001945440b034841c103019654107856010910303003407550494840e080100101c032403800e840340c0c1a0000b44400042c20042c8510303280c05141d004640b50203800c0d99a00105c209454031380e440c0741d2013665030005840b50000c11030700340000c0c0041503013891003107131003014602d0b13400004140d0000c01e9034550800952040b800c0203410005640c0355181c4035405581902c002c1e00e45501442011890180490288196413180710740c005015038601c080700a6814036480201c10b070b507607020704005004403040003407080d1400b070360181d25626000400825a01010b40003018400d4984001414098180d0011490720b07081501c1c3c840703001c1c40c1d18000001e90303c02d02590b03000034452840300048144644400010400800340c440310004201058517840890250220505403240003000c0810000e10041c8502401f51903a40d00c001043c50501c900701c01c1124040040614100d020071403403c01180c4103042d241130b89440780e2040303444d040a0f86140a03640019500402030761202541d1600001c4 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 378738372 1250 378737122 378737167
    0x9050708011d01050108010e06190e1605040b03041b09091b12050d0302251505010b040b040b03070509042f0702030c0d21050d0b06071a07090b 63
    0x990541820007019010b01c21900f84211030101e00020018084030414128282d8803840142c0b0100b0b42c0011880d02e821402c42341d901170501c01c440e00c8144454144034010a50101c0341a082040c13800b0300d0294505154440140702411716101c08007000501c2c40100100401440c6901050080c032030baa0502501840200c0d0310000da0700b2900000003a5850201040142c09810002924600039010820780195000c5900121000d01d00401804c0e13288050a0f6081914014451102e1003031403200044100e9a040c2c019600c0d511050100b00255801a012101a0f036203c040f100e8580e02c54200c296010b01400c2005503002d803c00d40080d030400548030020500f940000180356407100121100090b5205080707010b50140c02c40341040c034041c1426008101e006101c2c41000341d2001003401c0c0d500b003004032500b18071300007000000c8130304101c095401134503010181104c100d0f142403070560720055a1032203c030a40489440100c00116018040c50051004095609400f07589448003c4801e005050860 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 378739622 1250 378738372 378738389
    0x7060207090b01080f04020316060806330f09060304140c010504060e061305120f0d0801050d1101120f02040306180f0f060209131a04051006030903090905070801 71
    0x1030004441074240142604010180c68582084d11400f4062121100041060380c05110304014603244a4000140b000209000c0d600ca900320304001c02013104105440582e807e0141b40c2007488403900031440c07403070201140d0305000c0c0c0740d0340c8803c5403507d0551300481103042c2e4046408000c1100f407010380821491b05070012070a0f107841181200042d03416009078007410000a0105d6400c182c203003003a00080c18901c1e8043d20383c900300c0d40e640000031079410400111003000d0300500c00c60075012034200701203001c01e1014140455258100800318001c09100c40380640ba800000e004040340740d000c0d501450000130084402c0c071484609401c8000a50300c9444200d500c5850710b0541d46859000c0000d40303006590000032250502040d0f15408961041c0700415500d160b420464025103a540c15403280420000400c085201044000c41c0030700003040300f0707206004d41d040c002002120f00d4200c0e801c0050f40c260f420002142451801d08860010b0907401c03500344a4030300000d021a840c1c101107502d04807810310 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 378740872 1250 378739622 378739633
    0x20a06090b090d09082d070308070510050103020906130e0d050414120a060b03100609090c05030c0108010911090a09050117030a020d0c11030a030f0806031603080c0f0f070602 77
    0x800b01107540c0504c500c00c0d024181c03c958002c0883c03541e1a4285200040c0d101d0310540c502607a0402241011000e51040780d12481c0018464100101441100c030000c0c20581c0400003503140d0b401162164500500061241070780c5210b005000d140342c3c0c45140c4110040c0c04031011405181b4001e0403d510034003038030f4084078808951507850710303000002c04c51201d40c800151040a00c00d503156400381135039203146a490b0185c1840300204a03807074880c010003400c208030b011030700c41002d050a002003041900550700a07000301e6035111969070800c480c141150450b20f000210000b40100c4040b003401100c0c50039a00c070301708650005100c20365404c654140d8411008400b071880d445d100e03241d81c2e44100b00e141e00c050f13080603001184407030041c4d4080201c01d014070b0885880d803414500080c20b0800c582003c42c08140d940c0d5503000e43c42d0b0302c81040b640c8824150005d00c080034115088030319804540c4402440513100180a90344001c0c248100300c00598058101d0701c5052114207066115010303030082c2401032051 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 378742122 1250 378740872 378740893
    0x902030a180b040323041e08101406010518090c0405040c0504030c0b070209010b0309030f1209062406090f180411040203040c09021620090a050f0115020a06090b09 72
    0x990107171a4210903118902c5146c1850b04199068002c00c0c0d6101c0242688072030b0001482c05401e00c0030180c0c551403440001500540c0b115003039007203c1c0103424a410003000344841036520161120305074542d10308071440340131070b500c610454003184601e800c05500141803110b110b10a0760000003500036039200700b10400c0940d8450b001c0070071074080c2e0b03d00a5030200c281c40040000c003015a00070f41d00160024142c038075042c001c001000f4281c3c050b125102d00103003048204040c0000c01e10180303070800c8900140c00781c0b4980200c20401d100c0c401c11181c40c4107400c0014850f040303950311214408c0030343c009400750702e041440441040c82c542080303034191040d8090182c610030354640343c82221302c00d546c881240d01c05071381000b0a01d0000c0d00054103c0031040740d420070800c0810034410410a200210407a5294500b4001c1d041c0222880090840078000e41048140000d84040c0501c4a06440c01c2101a503031800c207000080707240c0041040b000d0001072901c0c94a0b01480745483c4040e100d1250b0804448aa0a1 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 378743372 1250 378742122 378742157
    0x3061d0c24070606080618011b090b0a09050d05010e120c0703110d0b0a06060f0e0a0306021c2f0a0c080c1e0c0411130902030a180b0403 60
    0x110141d80010200310301c0042612410038101800440d070003403000203a16505d8446441ca860342c15580f080c000440300240c0c5500100034064841111011220758500046070b16028042e03898038020b6042c41d180c0401c02200320751151900e500240320041c907902141005041c0b003402021400d4440780c00780503a5925820070a0108100c03044000403c00030200a0301d035031500c8400100c2017680640c444400b07200c140104000d004414000d03000d203440000c11526000014240d0220b90000400b4010305900c90403050307844a41e02400c680d0003080140c1c1d914040d030403040301f121180712040185480d10015036200b181e42629440341880d108500c001401c40710b21618214040d125880b00045c1b4102c441c10005400600903009801000b02142c090305082c00310615181c428480301c0300e195010cd030720560203184c0f50081d504444000c1d4034251412101c0d1100c408221940e0140c0f0001e142c0001c007081c001129644040140d0020003160014500f0070301c1c101100715020344007071b00022101000d0848015 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 378744622 1250 378743372 378743389
    0x1031401030c120309080a0b070e120318040207020d110301060608190c140c0a150204240c0206041203090b1603141b0d030509070b031f03061d0c 64
    0x2d4100b56500411854070780c0c440c1c50a0415201201001101c0c0300009016408100704140248a130b40201003924085000074180201100340b148900d85018581c03103121004002c4404c3c0940002c1044414180b81010601034421048002e4106400e907040209100c854405440d100324120000c3c0052940c0d401c04940f1018190707104003143ca80e400000c400354005520101000326503091041c41000c44162004840d00a40c100e0741068200c0340802c0c0801556002050018a004030110708040c1070020300c0f698600c4d842141800c1c0f9402c03040c95040309004041080b140e43d40105141c3e6120740764140e415406100c2c600c12004100000300100d480c05a00742524407901c0070b08400051410541c40440340c1e454403018505002200300302c007580d404c4881c0210301070f0004805c002d040e4005c030f40b078006046480041140780160062407041c000101c102003102e0b00301480c0140b02214894003080040310b0042940000d00380d41c41c22040c8441d0065610b070410305030001c40c080d40c020440c48818001d4a1 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 378745872 1250 378744622 378744629
    0xd1704020f3616080a0b04020409140c0a02060106080709030b010605040e0603070501050901030902040f09110907020115060e041506020705120f060604050c120c090f040b0109051017011401031401 86
    0x5080f00c2d80900745244a034220b580d00c10110741000c1103528480d8042022644036801c0b0582290b01d03842000c04034400c40d8040c0750401750341280e030f0b4603102210b680251201310600620041201d01c0003c60821841405424041c1d9004041003010b56580c144c003510547c000d210b055900300b040740025071071b0b00d404541c85007103c8040e180c0070314007100d4a00440c001c004110040768896038540556440c0e07500e500c1804e00280c03040da00403001f0400c000403c42c00301d00050a020031a8100700004d108100102d2a8034100c401509040b40301c0250300001070b0250060702600d80352044070b0480040d040740d00042440848200360742444540c030104601035164100080c825055038009804245941059401a07500c03102c130144250400d611141510703000c400a45601004a402048100c010300d85201c01084c00c0324200c404124282c60790002030100000ca1090360300c100c6000707032850361040c080c001810300c46030081c207a601d4542c0c50b2000c130700d0448003c16501d8002490f044030700040402c840c4459058 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 378747122 1250 378745872 378745891
    0x50703120801090c0c21110f07080111030112060f09060207052506140901050f0301060201051e090a060e011b0804200d060c170c0306030f0d1704020f36 67
    0x14042103041206c0b0301c0340e42c2c502c0c0400482c0070681c02c2d581000d000c01c0400820060151a0180c540100c40703083da5580501c4641c40231042004010044074045825a400d502500111b1541203002401008184030440075080c42c1c00011040104080800c803403800c0700c1090b080d00b80d99614002d240c03254030300034002c1e5404103d802d028001185414005403506640500d015441e0a0040b0b011241c60f800c280c0c04000943c1d145c80500c1480d2030918507025000340d200d8041041880c10705501a40e4001c0d0600140800b0354074911040b07402429080900e00c02010700180f100b154044100512040c0c1c201c0d0142ca1071000c49214003024a1600c1d032661421b1001042d0141c40607a94492000400e003001740c0c2c005002201302d4a440d0a40050302240c0b00c7c2c2c07900b40c1501e0700c80c41c243c001d2504011a1a10041864008103180010709030098884080c100c8070f01d20300949551144041110041540c01d402d502140d10199000d0340200d0881100d041c1850b040076540002503910204281c83d81510810311 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 378748372 1250 378747122 378747143
    0x41109031e100513061506030c03090201050a0f030b03030f1e0301030b0103080f13060e03010c0c0803220209010e041a0c0304020103020c0c0d12090e22050703120801090c0c 76
    0xa030850390380c100e280c005005442400c3c40362150399400e0200c07149406c039403000c00c81e605410450035415106564071400182021f014100243c0d000800a200703147c074003003d00c100c03454101c070301920a51241008403000390460303a940307206240340c3e00d40c0c0e004184404803180002484a2410700a2016213048a44c0524103643c0d503401e640d1215420b801c0341c20340110030320b014030070b0140e441c4406061500401d05178482c804e41d0b009070014113003540c0a07520301005000640c10f0350f60001c1c4039082180d5000407255402101c07401800c5a1a59641482e9000b940c0502c1c884c0c000f0400684910380c0b103004074410b00c5034000528240b44803181e5041e0031601248011310500000d400b5500a800a11036001440309a0769609101000039105052400081c0c5a100940b07905404054211134014060001000d207001207241c0014078001009240d1583e01e0402c13000e01680003005000c100300005158042e03040140d450004000404907482446a0100641010400301849020740480022540c01c010840d2 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 378749622 1250 378748372 378748393
    0x100c08241005160605100f0503210903030f1908090f1c090504140105041a0f060903030f07080c0c12061602071203081911041a0702041109031e 63
    0x86040d000f0301094842404008880c00010703129106191246800c8070100c9030711410a05482ca4040b11500024020740c0560041c0121200c29051582040b4241c03426940d65002500487d0540c02080100b0307038110004611060380c2d120361030b4491200512907650000c035a8030000c4880d9510303c1c1c14507000d090703003182d005016601040890f402d800201da081c884c0c0c54075a1080032800b01c8800301142d0700d403101e6020050105241c2400740102c07030f0210242c0000040003c000084010640001041c42100f000440307914a031818001d0369841c14031210301d60345a9400f42031144159000040300c00741030190103800c03241458140ca2103440300e020070004019640c1c1d0515580000f000002c0000e056201d02c92000901081440120003880d01c644c1d01e03290f050500b281034074003865846440b0021345050072080014007030000c05803800c80c3c816000e01d00542c03c0424040040d40314035071010b034100781040410035140c01a0401025884002d40c2100d0032680b41800040780e0050b00101101550808070b40c60 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 378750872 1250 378749622 378749627
    0x10b011409011709060703150f180905060903030403030e0106120b0402030715020d090504110313060e2a010c0305090409050102090d2307030f14100c082410 69
    0x1801c9814060403e0311480c444400106201d48003100c09810580c404001c012409a02d030041160308032016a88007220f40c00d001c02c085004080f8090b60304024103208107800d40d94000e8110082840c4c10034181c0301507042030b0098135129031044900760046810031171b400d05909014440d4400b142c0d05d2401034550034075a50b1302c02c04c46560107041a41e0500c110a0003103013848000c3c0d0700306c004011030307002000d00d00b0401ca400342c407848266012911407441e2a0407001c0c9903400d60101ca0f408500c080401803000c420703192481c001c1c46001030b04075051043d500d9518007001c030b175461920311041d000241103e440c80071004503030703031441c0c010001d000139001d108440d514102900039882e40c4e880380001500b040c030b610009c03c0c2c3c1c003248809c054034601044054510160740c00403007032410b0303c0ca4038040d0800900795240d0b40084c0c1180c0388002d100d00006225040070f41c9051016141e0034105031414444500301c1d07400200703441c80c00d83c2c1000345006095a0340c1c641c00028014503001c00d40142c0141036101002405 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 378752122 1250 378750872 378750877
    0x40503031b0c0f010b0a0f1508040c08120a08010b09220902090a1505011715010c0803090f0f0a0c051306051203040806010e070203120c300603010b0114 67
    0x1800410a401c0c400b12009039014091442c600c2e40c02d9000060b5a0f818208010390429a0380c4081004030341024240070344100d103a800d8611000721709201c0c269032543e29141901204030791049005006286810601c007810740300604140a0950b08c03001c81c2c0e40c07603011110319445010340081e88410340410056201001402803004501c0c000b0001032100c0d415000b2650320402140c061a40da50340ba00d41040041c41e103040300d030261000b840d00d4180c416001d01103001c00280a030070410040d00f03038580340b04070340e1045031014481c0340c2c0005001c1d243d05001115564841701f80d01032031111f0040340030001e0044000144c0c0700c0007541042c06258a00d00d801700b44403d0025410840e2201a00e035040444c00780ca54000c203a00310b5004000a6a40303030700d4000c1d101e08010301030700408400e1024100380903000b5800415a403d04100311109042512141c036014018480e440e900f041102100118141700c100d8014010341c1780302d81c10b450494603640c90341050308070351203140014042541250400d8103016400d01 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 378753372 1250 378752122 378752161
    0xc010f030e0f0604051207121d0d0321110f03092b0305060a0b0d0b0f030d050903120f040612111303050c011809110706050109061d04050303 62
    0x140020004426104075007003903400606140d00d40d01071002e00040160410815000421842d0314904150040e5904a41c04001103031040401c0505040d4140354214500f501c15025030003030501c80141d000d481c010340881c40d00c4031416060780d0408404100c40300b80b400384203a2004030740701080c50070f014110f1403201908041d01c0100c5500c1110481e9400f030b054070440e9039030500032400e658044a2074034401004e849000748103601481c12171204002d046990001c1d40c6080303403103401c0410440c2945002c1071000e8035101d549075047c4203000203803003880e8101c0000c200082c0140c0c03d5850300c20030780801549070310641140600d0440c0821042100724801c1030301c5c46482c030034081d0100b00090b0314050070b806a042a180e0030381650500c1000c00401c0000c01c54420540000c1c00c180e05d0801c82040b00c4242140c02c1e02c2900f81d0141c59441c954260140c030802c803210315500100c10482940c5800c5c0c124024881400750440051003204251078202c1b20340c0360035202d00d5000d40290300c1c42c1c1c0e469490810140c01c403503 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 378754622 1250 378753372 378753377
    0x50904020c0f0105130215090604030311101d0114090604060b15030705040e07020610140604050402040b0405040506120601060c02060f0d0b030d030e03030a0c09030c090f0f0e0c010f 80
    0x45070b408942d001e010303007401404004a000e6801d10140101315000c44030701c001d0040a001042429186e4495806950440307801d41450503d00c51841c90847c2043c108c082210095841c21111552400305000c0b0418264001c1c0e000b044182181c3c407120f500084155096074040c0d216400240c005005900302440102c8040c0000e16104404600b080703241c0c10949040c1b01082d0302081c01c0c0319201844280642c080e0541c80145820b0403c0e06107103500034024009c000b4035006455200960b9140c0c03500301c0d0300421001d441103654580c4c5248040c3d00350003602409100d241000c0c0800c08500c0d000d052009171385900c0300580308607440c108040d02d16141c01d003070803604544140700d051f801c400c5020240001c02c681d500c3c00715440c0852020107061082c4030707281c007050500c0c000e0901c20400001003035070384c05040b402c400a1040000c20094849184992005040382050130380450740540315004401074082600003444680c080400010a071943c1541032507072944072446803040c542c8070300d80c4080307580e4090 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 378755872 1250 378754622 378754633
    0x21504030f0303051f030b130c0f060c0c15121a0d050c010801063b0604080a0c06030501182414150301031703041b0f0303030506030d050904020c 64
    0x907915940068060075064020070740c2d800400981c10005140300c6a01c00902c400d01d5401415030741c40d100c0342c0c3c0000e000c1c00350000c0c03460b249108110250036140064010380d8a118a90b0740e0310007008000c0302759080c0031030311401c40e403c1c0011600503100c50100c4061031600d844009068003203e03039000341600c0207056042c1200e85081c0003c1d4850704901d0f204580150058410320b4078240015103400c1c01a03210300300300f048080440041e1003d200c0350320640c03881c03540d888844900c0b092034002c02c10000c594166200e040014000354030710000803004c0e48144038a80d46000302d07a44000580850300e09102c0c0300485014031321505943c2856a00c003801038071450308021002c2004036001074946446130403c200c0d1107004032150070607103401e03481405c0c83c407008544d462666055a840c08501e4000821a90034501c000c00401e08112500021003c00102c50307501c00d81007a582c031000d01c042d8249120542c0482d1408000ca80f03a81004900450a1140390b101c0a01c2e1480110a000080d488401681083c0c00782 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 378757122 1250 378755872 378755879
    0x2060a03020d02041205060708040201020c0d030306051206040c080313050603130c080c030c030c0a030b040510020d1407050c070e180a060b0f0d0b13170d0903030b0a080307021504 79
    0x11440134001401d4104880c4200c2d41c000d14015140034005024801801826010080140c0e8000b40c00d200c180c9040e141c0d210210700900e4103030040c0800d03400140d481004403201d5501c0040018059200b24003a0241040c141d40c0c64031125180e210b242481364035103030000814041820a4002103801c21840300d401c07070305180786803150300b00c840e8150000e80258000b4079030384240746030070080000000f00440144c14102d04050015241104d503201c0184001748400010307092110038000e13203074845d6152000799512542031030342c0e000a0001007811340030100004c0214031102c4c80f0f0820ba42c141640342c001410f1b06800d120b489041a00010702c0d6882c0040c10341101c07801c0107410f12403c81c4e0715116100218504110004002c1c00c4100c07402618003034a01c207501d40300410000381141b500f29009507404404e2200034140298003d4014134001d001c0e20b400104261140350a1b4084805c170b6000e0340e42009407034500c1c5c081104042d80b900c1001603030b40c410b002c0e00016240c0110002c10141250b0001c84c0ba1a59 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 378758372 1250 378757122 378757147
    0x904030e0603040c0609060e0f090402010203040803031021260d020d02031b09030a030c060902090f0403020d08100e091501290a050a030b012d02120a0203040302060a0302 75
    0x8890803200f407150b44c03004010f059041001d4030080e211905080403001c0b2080046027007011400b2601d41f04100200200d810359000344112000380540c0c03800d40c4d50724584220740c003503441b04a12031180031620b1565075198610b000610140000c2e8411001d5401e14070030709003a040c08a00d0b80900c2d5802c0b00402114448007002c0c0300400007540900009a120700e400b800a0012030008021000d1800c0c040149290ba65008928443c450754103041047c3d0001d101e0505000410403001d0094000c11120144440d00000c41001c03803045103e58220703000c5440d0b88034112101c1c0020b580c6c5840c0d44140c1da000707000c00101c18a9070b56200e800d0104407490b00184030104100345c6001e034000d440707650072080c001c0e24100c060300365007081100b5003c0c070610302045058020b04a2140b071070164201940c3c3c0003060b4040c0c0c0314480c0400c0304000d2100503601600d460070002c0703105560103180c07805403003541c651005410310b080c1600c0c4a900319401440c10686140c0a0000c240d0010442c81c04040d400c0002c0401402d = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 378759622 1250 378758372 378758377
    0x7030b030c0a0939051e0f0309061f15350a020f07030305180d030e0d0207150503180d02011512020901141801030501050726060904030e06 61
    0x110500403030490300960444500e14002001c50b20720a00760100d01011003403004a00c0c04c460204e24240755240200440090005907100f4801d042040014480000e074040402840c01000c00c0b0b01a55919140c50721b26544140f000c901c40a9007403907500c020403000c644040341c422100410705240000540c5201c1006d04208440001c01546243c1580002d507504d2048100303902c2404001e08624041c0b800180c04021701603000003c1c10142c0b59000a40803413141c0300a00c16034001c140465103021013040002e0080e003400200419644545080d032141c492000940008032010940c14003803c0d00c10710002c0307131103034401400e1b181985400b801400412004000344c1c1300e12105640000740389403940300c15842601003503000002482e6803100c9040507a60f1200258111a01c004151180702c080001180807001d8074141540a01c03601d80002051043c103400040c4030341c1080d5120b00310080450b02d90180100f401c05510750b00028032000030070b0b5080031580b068000303020341026403410348035000081311039 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 378760872 1250 378759622 378759629
    0x7050f010504210207091104152c06040b0a050c0312011d190b0301110403030c0c08120d09080702040903050a030c0503070f0c0f020a0e01230907030b030c0a 69
    0x369076540c00c2006001c5061000820503482d078110001281440740025030f03a07802802589081d40c0d41c0e01c96200c025030600d0489000340907a0000860344030f03074020090203810600f860900079111130364240b60b410400d1030301051a00f500412060825003400107440003500f21660520034000100103043c000d01c400c1024211400100400c29410b41c10186903d00741d502c5c844220b00410b100d20103000c45002240c0c0105c010200d04c403000941806540002800352102461100780b15400007804010b041c0d01401c0303101d4040c003a1401000c1c1540c0c0e00155640c8802d00090480010b10170310818026a403660010074a96019084040c240a041d8001400300d44201b81e0440100d00005090040f8940601a0000380c86050400f681149845100a04510b0310b64200300c0400406010341400c005200c1032000e4910380140000c44030036103921108840b40780c01e001c1c22204990380004e480400d103181c2803040c54150080c0140700591030360b00b01076001d48914401a039240c06244001c80884d01e030f01007000f008 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 378762122 1250 378760872 378760903
    0xf080d05130c060f0522030804080d02010506030708060f07180e0103060b01090e070c020d0b180f03090109060c05011d1c0206060a0b0a110109060b010306090b0a0e09030705 76
    0x195050b140050b407080c60b070350100040c440c5140d12826071582210903124803403138900c525281c164900c00b400703c1103000364200a1400d0b00208020503140b00009460800c2034130b03900200696141c00041681d02c0015128040081e0f00c03100005000a292028581c1c001c0072a0404e0100130451081440701040d040c0c00030340845495600400c14030519010b0308143d02c1007800c055210302d081084100c5030820003045c0310144074190115070700710f480303c2c5820585640c20003409030b07150400c04481104e190540e0b2078010503200300c001840394800c001c0115500c0d0304050f1207a000c844c0c5010001ea03202581541c0030303a01556103075410810313812010701c80e040803080c0c840605034600c00c6c0c1640c031500f181000404021903120f041001010389a40085030203584c3c030303610f6242e201c10843c802101c2c20410034940d10b20765402e0641020400820f80c00a001080098a0500c1580e40b03075860346041702c1120f03404a9000358407120400c403522103035a00b2500960700c3c3c41500d1030241d45894042c0340c107140c000309116 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 378763372 1250 378762122 378762151
    0xf040f060c17191103090406120c15051903060306090c0e0a180b040804050312040801060e13171303080309070b0a020d05030601031b110c0402040501020a0f080d05 72
    0x801c5081600001402120540142083c07100a81c040040031014902c0b428000c00c02c044a010400400c16650032100081081c02019160402d0051041401c0350807680f41044001c00b01c1d0040402403060500545070b90b4041c1095280c42060501c1c81c41007465605142d40c0301c01c040089810b90082c420010300401049010314a401140c01236210700500380300010340780481108840c160805000040c03900a1000708181c1c5070790412034098850341e440b540d81407050003100c0c940101064090400c60300e00000800001d60b54445981c081ea07000c85040040d82d088070f01c83c2c0001100700710007a01c1020140f4034542003418800c40b00c5142c90792074005481c3c500010042225090040043c0000ba103c8580588d00f00700c026070010b0f560701c60b4480314009011000c0000390b201d9111364440c40d003442c0c9800c0c62a0f94688081400b070403486560700036071428042c1d1a80b04903d42410300071901143e1069000300411107813625a6002800c40d440100c075503080403c10095031500e2130181c01d002d40e00341c483c07120 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 378764622 1250 378763372 378763397
    0xe0d030e0a0f050a0306150f0e01080f0109031b1a010f080f010c020307140c0303190f0906020709020d1407020304170c060d0209041b02030c0d02060f0c0f040f06 71
    0x25202100d81d0040200402d02c0205004a488400358201140e6010102054036024100405940001ca4000350040750b01400c0000e4022450080079040f110071000341d901010780c443c0d00e542a43c0d00400e01601141c220599004c0860064104c6000c0d00c0c010f03030042641d040301d6540c40b4040b0f1420390241d20301c240518414091100d041c40101d00f6005503500130010b0700031400e8007944178041c4480c06800c8620100307014010300c0060120449402e0024152551400c23a8200c05a030a02d80c0c18020000510390002d600c01d4030f00a100b810140c0c4e14580040c00d03091b1a110300080a07500c0003841070209925000d0115580c032412246a001e01c11540143d6103e5003040382c00860288000d00a102e16404030b52183d02c0c5451387e17012a00c080d0140300c400b5980700c0100d0081805001c03450284120f044442c0030340e407100c82d404809010800c0109054424501300000c0032680c0300000d07141400b00c0c0d003114003c00c184881506c02014034080e00703500c03035082a45d55068801e1102455000c0c0b00070811288010 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 378765872 1250 378764622 378764629
    0xf0f0d1b0e19020a17160e0301020306090a110c1603021912110f1938090f03030406050301030b0106050304050c010c05031c0608060603030702090a0c0e0d030e 70
    0x50500794062000e14540480324550764440c0012440d141540040ca66541074403400d602c540f80513894541e5250741c2421500450122111814100020030f40d04090200386010b0084130700460004154011035203c42c5034000c020016031191240165040000c0054190144480360f18100d180301c040600c1841e6005102802100c22011064181c0c41c0c10148051030200c1c8400b544142c0280200510300c2c03891020030344c081c40d0180360903406148104000d4104250309003080c161240f070314031504507040102c05132601180d0885000c05003401c882014518410b81c02c00750910810003007100d01c911001e07802080c156030190f040303000003d000100600c240905648100d0040403681b514925500c0c00381c48107500c80798003c80c4e444c104400d4440c0c420030f00c0700810544034034035105101c2c0700e49032000c0c0380d440c40100030a100f200c0d45401010001040c629000c01914005500640901c0b103990710342c201c0000815090380d2450610014002000349034660000d035806281c0303e41c8481c03c9207038030b51080 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 378767122 1250 378765872 378765923
    0x70e180604110304030c08090102071706090d03060f0306050604021207120b03120901210c030c120b0906060a03110a0309022e140717041503020c06060f0f0d 69
    0x32240c2e00c00030810b1000003640840140741d85900b180c181c503241c4030300d803004074100302061344030b159081409044c08500d10800f0034883d000305034080c1119952182d0070400e6095841a101c0c1103040200b0050070004164907820256000c1c500900040c0340092000030f100103072100703440c0301000030300e2054846405c01c81407180305a005811001030007000819011500d6510421036143d04201c8100d000c0c448a000e6101c0e10018000c4512040c405e507100410020024a0307a401c0140024004002821041c2918414001c80e11005001e20030780703680d010140701c00ca900981d03040c010503640e001122007100070100a407080329495074010442c0c050500400100a12074001c181c0003048410404021051500070349841114506181815140c500124801805200c0c40684552655642080c0c44007450000300140d580e2100444410682480c6c00c400701d0042124200c0c103980614080f400c02e103013801c2d8040c0d9604c030003010b1031030340071299010901c1500307035030412250349915111030141701e490f2007030 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 378768372 1250 378767122 378767141
    0x4030203220503060106110313170709050f01031202030712030b0a140d021c150204080f03030115050304060204210203010c020a0b0f04081308030d0501050d1a070e180604 75
    0x2841c1000e07080c0340029483d02c0d4103210342000c3c0200344407400840741c03051080d20000190b206c803000b0b080e9030303034500b81d121074031101c0003075a140c0901c50001c510401140b0800e4000d07402d0019460840c2e0a564440f580d003050624a81c0a5100134032040002401c1e1a141c0f541080d031660340410050014000d1046500c801d4014000340ea41b00d0300100c00d181c0342c015000b10030f550122a04500100103200020600f40d1000002d410b0a091525403101a08690005c008990703000e4100da5156030107109198582c0800c0c0030711801d038881800480c070300c0d520038005103401c14040c00c0018580ba60f1000c20b008581810480240706107110401c01042d8036080c03244c60010182e41c000382892a44550b0703100b06280d0300802c0720240c91102d03004070342489130140aa40303c20300d030b055007540e920b0f881d0609990349401150750706070703d21705100001c00c850802401d20310b10743c0c0c1d00c1410340c00c000001d0901e440c0030b043c0080000042010681118003a5941c003c820700c154068400109802e0500805001c2681e03000307003 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 378769622 1250 378768372 378768427
    0x6090204031e150e060402031501030203030418150312090b131206060e0405070f0b0412350919030512070837021501060c0501090203010504030203 65
    0xc42080400c000200d480154107009410201074070740d0785841e8807003229107000d16140038900440141c0c1c0c1e400014205003d80c0c000c4044a0354020a84c07a00c040441c42404000c0d00f41d0800c1c4400c11600d0382c9a500880c440031551008507010b00843c0c95000600200d500580d150102c442501c01c0e929000841030025103d521202458203448200d40c60140000b0b1040107001c100e240f50200074040c0340d500c6240070f007860b0701c0e0740f5100d0306081c10001e81d00c04190003100c1820713204070800617a003004142142d00304c40e000d0401030790b020001c0d02c624900c40c0049607000c01030300307020b001d4500080200d001c15a00d1140a01119141c201e08400d02c107071101da00554080b0b84a2482040c0040380d0b000400b50b00c031180d2840002d0387c4088500d0402d0302c90041582804100e030740d1030100f10440e4414640340440b032450030380d0070080450990040340d884080d0718009800507022001070003024800e420849a850050b8004120120a0741c04203084413402c0707800360f00581000c00d02a9100c2011280461040140c4 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 378770872 1250 378769622 378769627
    0xc060e010507090513230405150420010c0c0b041701060f0b070221030306090c09300307110111120f030402010c050a050105160c32030406030f060902 66
    0xd10001e054191580606840b904000005540214880d0401e0b84d20540202d400300c0f00e00300200341b03004082c3d416103048500317008600ca02c0ca020314280040711b116a400c520100440c801c0020341c80d240d40d240d1441c01d0b04024403210b0304404920000a410000e013100254103a8461400b020701c40d00c0480c008e03801c080d523414640c040007944401815007098a45130041e403070383c2c1c104500c00120341c103c080d10025042000358050101c40000400a03600c1607070140c0d001c2c0001e50340c002a42503203100710101141d001480000c82e0400c141c0f04900c2c0340b402d013160313903a4001d48400d00780b000c2e00e5500322110848100003800000303a042c0d42d10104406c03403040c9850061070390b0307480c5040501c818028038507003500a240c0400080c095a01c42c18140304459044007c2d180c00844505045010f000c04540d012001509601070006081c42a51280111500081d05096403044500110f1070103c800501511050a2030a00c00e24030740240000c00080032706441c002a01c405000f4002c00b40d4407154040003081e8810b = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 378772122 1250 378770872 378770881
    0x3060302060415030e060a0b0f01080f04060e0309030f03040f06050313030f0e0a061706120a0312020d0216030207050102030711090603010e060108030409050c04030f0206030c070506070c060e0105 86
    0x107400a60341500c1c00c403030b480105280200b500310010070300300e680c41165200f50302c1880f810103181e500203110014140c400141281c0e1810040d60403d009650450540c800e8200040c080342c6154004c1d00d07524100c00c241c03417a014890002034034024400e460003215030030000381000703142c000300242c1e401480d5a050560070745c544400303044807007401d600c00035050090700c03100c03494220701c03680c5503203441200140001c082c1602c44400402d07211206452050079100c1c0b4002c01e4992400003001101c1c03601c4280288086441039800311102c28001c00d07112801c0344c00780f180000542060018268000d00080003c0c00720395181402440c00d00c0e0341c4d00007815900100004004602207a0b00d01e80d910000f030303071180c81030348580010038010b1010308183c4100307008490001c240070b18048010303c1216a500800c0c071064448010700c0785107114900c0b0081801c91400e50180050030b05002555212449900f12801c01046d074a03020308000040300e0b2940040c03011a481010040640f107103020443d4508020003c2e85030 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 378773372 1250 378772122 378772129
    0x609110304030f0e0603070906020d02060603120703140d0506010215070203070609080903010e210f040915090501080a0b0f061008100f0b1e0309030706020f191205060103060302 78
    0x4090009010002038081c3d0007000380c02215400b5041802800c0b00c0ea407468030b41d0009060301d02a02400c0300601400003402c2e00030344002401c03400368400030060406800807544d80724042d48400c108400f0b22280c0e40d141c05035804228060324000050100105152030181d000a040407140c09040060515007000c0c03012a5600100392140c0c9a44400b0025442d039040c102158140038800b0015415824541001801903000ca034505081d08a808400740011002c00540311502030740d240505100130502003041003042c282c000e6024101903108000e4604d480d2141c5100b41e8109801c80082c0d64032a050633001c102910806903408822070380708041500305000060b0160450b50101c0c020022401c010900c403200d00742d4214010002000c42060550740c9000c00342d5160409003080180401e2109540d2241742c1450489102c0da1000c030185141408580d44c2000a4220b03440c5400c0e80c19040c403003506042c102d994035034244511034540c1d00c52400c240e43d004040c0d441c02170400d410141000000c00040e01c = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 378774622 1250 378773372 378773377
    0x4060305131502030a0e030307030b030f21030601030b030f0d0206070302040e0f040201021608060411010203070803010b07080702060a03140105030d020a0305030a20030403110c0904120c080f0904060911 89
    0xc00303480e03002d60f130382e1100c2400702c01a0042e0b2a00781c900b030000000340401190175a00c080b0741003400b42e041d16503c49080034040c0e11002929a85507942c101c2d95020300410118a00035580700398141000138410780d0840200c3d1406000d00c031015402e40c0401102d00156404210b1207a2003e1701f4a01545410b0030068605c40c0980702409079a50442d10f240030600710383c0240031a0380f02d122503050310b4800998849042e0354916068606071200d140c804030084c5503500c084120b809564002c002c081c40c40e440d00944641c190b100350400c0d200c11009100355001a40e894004101b10010759030b010801c55510b580e141c0c079007201a8004e070310a5201e441c039100348a80100c2c6040007180c050400b1038a95031128041c001a1080c0c446144104000342024441c86003104080c50145029075a01700250725841002a6203a20f02089030f80d11140c2c000000700004d069201d00c002000c401d180c85840c00165556000700790f0068003900e04001e80c08546c486450410780b180c10000d0410070350a2101000524042c0e8491 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 378775872 1250 378774622 378774653
    0x3070c0201180b030a060e0a020f030601180b120108010c02010608120a1b05010204063209030a051506030c0f060403032007030f062409051009110406030513 69
    0x6000d628424000c0c0d10b4100b0034010080c0400e00f590700d02d44600302c0c000030015806039010b9000018080307070645400c0c1c420340d00180c0003240407a1540d1511001510141d514400600032850045400b1852a03020780140c1b4003401d0080d42041594180109242501c00f00c0043c4000c580c5443c0040014240000d4005074103070710000c0040e030700c664001c0121035080b000988217600308ae40c0aa400c0801c041580104115900c40c1d5941c01c0c0f1107118900c8508698480d410314038900c40c3c106d0b141105440600c004d28041d0401406c850801405649540c100b003c08920019444a06010401c842c241400313810304680c021222801c228840a00244880c01240006410031030305140e440301d03000180c8000350101c85060102c4201ca9501d00d0007544000e403103d0121030160400c4003022450140c1c13031030703000c17001603200704901760505110480006240040003000b0701c190300c074000100700c0c40c1c0e8428003000000701880d103940c6070308140c0c01405540380035115940402c954400e58020601905514855 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 378776978 1106 378775872 378775877
    0x20d08030609130503040603050c0c0609010e0f01020a080c030601091802070314071e030302040519170c060406030905010605040612120203090f0108040609171b0303070c0201 77
    0x380403c0500103005171300c10b00060000600a411880d801030007040e00c181021004214185840c2003a03c07040020f9540740050211044144080c0459100c071100a61138100425001010035034002d1445200c40804808584268400d650600052030f2031807414207141201005600250300040e411008a41c1000700c007640c00740c190003514449600000145d40440040d000420001c180c80303011070406a08000200d12039913200031041580601c44000b08586003080811042c2c3d05400008900a51017019225020394411044400782ca0390380c0b50100b40f00a2902e403444c0036240c59040180d20500b00540411440b0030301d4401107006014190394246070b00e0014090362a03201c1c015030550000340c40301d0004c1e403035405070100f9900280b25000010714400c550700c520145590940f5518000f60307000585854900c568140c403442108100045e501d941483c0001a201140900c0000d05 = true := by decide +kernel

theorem cover : BRFrame.Cov 378597122 378776978 := by
  have h0 := BRFrame.cov_init 378597122
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378597122 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378597122 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378597122 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378597122 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378597122 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378597122 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378597122 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378597122 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378597122 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378597122 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378597122 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378597122 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378597122 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378597122 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378597122 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378597122 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378597122 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378597122 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378597122 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378597122 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378597122 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378597122 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378597122 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378597122 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378597122 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378597122 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378597122 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378597122 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378597122 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378597122 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378597122 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378597122 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378597122 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378597122 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378597122 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378597122 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378597122 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378597122 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378597122 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378597122 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378597122 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378597122 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378597122 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378597122 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378597122 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378597122 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378597122 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378597122 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378597122 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378597122 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378597122 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378597122 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378597122 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378597122 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378597122 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378597122 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378597122 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378597122 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378597122 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378597122 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378597122 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378597122 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378597122 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378597122 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378597122 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378597122 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378597122 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378597122 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378597122 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378597122 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378597122 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378597122 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378597122 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378597122 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378597122 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378597122 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378597122 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378597122 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378597122 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378597122 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378597122 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378597122 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378597122 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378597122 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378597122 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378597122 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378597122 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378597122 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378597122 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378597122 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378597122 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378597122 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378597122 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378597122 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378597122 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378597122 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378597122 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378597122 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378597122 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378597122 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378597122 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378597122 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378597122 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378597122 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378597122 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378597122 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378597122 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378597122 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378597122 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378597122 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378597122 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378597122 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378597122 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378597122 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378597122 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378597122 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378597122 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378597122 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378597122 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378597122 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378597122 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378597122 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378597122 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378597122 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378597122 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378597122 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378597122 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378597122 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378597122 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378597122 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378597122 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378597122 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378597122 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378597122 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378597122 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378597122 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378597122 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378597122 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378597122 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378597122 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378597122 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378597122 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378597122 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 378597122 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 378597122 ≤ n) (h2 : n < 378776978) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
