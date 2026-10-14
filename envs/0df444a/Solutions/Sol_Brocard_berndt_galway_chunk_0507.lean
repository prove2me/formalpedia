-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0507
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T20:10:10.441152+00:00
-- url     : https://prove2.me/submissions/db5d2bca-531c-483a-ab4b-291ed512821c

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 91007194 ≤ n < 91187051 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 91008444 1250 91007194 91007209
    0x3110414060f120106030f05010608010503100c0201060b04030f02040b030303040c18090602071a060906030a1704051018050108100302040203150306090a0203100203040b010501050f1303080909061e 87
    0x100d4410400b0410040100a20301c0485500a003025540800c60160f01641e5070261541a44000c0c01d01c80c00b603005000c542e070b01084080703806040705c0c0b000518505902d0203c3c05000c160b807100d8046400010b010082c001d6000e000c1e9800c60007aa4107100b003074200000e05590340700071140900103280c001c9040c0811707040b403803402d034240200b00008101041d10f038075030001701da200250071100040c2030305141542d226072420040d4006001c54a0189610300400482d88960040e0b5006202060f05030482502c500340000340c50180c20f0103060400b801ba001c5402401003080c2c002071507141320605000041641c4141140ea21403d6690f004940851855090001a40000e00240c10303040040d503184c40d00391800c00a1a10681d07010780201407242c00c0c0c2c0140350030320b0100c0c0003140080d80104108000305591190f41411541c0070300c0d115640704800d500340210b0b40a11041c1d4030b01c42c12f42800c00000e02501502a05103500100d500d00c1a80e218a4200607083c17041810b1401c0c80081c1c078400500c10301c0c0892 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 91009694 1250 91008444 91008457
    0x901060c050703060c031a0a05011b06270512250609060e03090117091504051f05070906020f0a1104110408100c020d0225030602190311041406 63
    0xe0480700c0301d43c3c90b540c070700c42030310103800d002c2c0e00280c0d8480840098400d40f02c60350148403800d90b0030100803401c00300001c01d00040c40141b24000300d5920507180801009501c14080c00c4041e1980e002e80f104607080341d4100400d03442003550316110380d095602c480c0c01c2c49000c542d8452004000e05c03484080280926901002a65003551103650781c50040010900f03038041e5a40f8840c4800203141c0d22900c440c0098009034240c0000b866010840040012800e000600c202d5000e00c00350001c0007039622460050700e8407102e5080399403003032465039a80501c0c185540240340140d60030380b602076070a03880310030803a541c08583d40114910b501003000c20010510b814805081181c0207800460340054000c2c0108080e800341c1e012107000d42c8030815508100d0421700c545480c208292000d841c0842e907402e0025030310710280101780d03d11103000080e104103040000038800111307800301c4250b445801045820180040080b10040402d044c0050f110843c0141000c841c1a00c82c064020b00c060303000d01d0240300c030641000 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 91010944 1250 91009694 91009703
    0x11202010f12020a09050a0618092a050a1407080714030415020a0501051e01062601090c0207170d110a0206040e0a06090c08010504090c1a130e060901060c 68
    0x2029425801c2d9114001800001c2594850601252401c02070105150701c5501c410208880282400ba03145060000705089562074400403800100041b1480008105410031422170224010b000c03a00c00e400a01a01403100161078035134002c020405d00c0751092150200062200c041008080d002a0441e00d1948090001130100c90034503850b1055080008900314608000d0392200c0524010410309010f140e0b4041e0046010303508085082c03182646540041c02440240400c0103156403c01c0c64102e007a41c5a001000181801540d4403040413008115044220b001070040e0207010548113101043c80d5a10032a05000707150b80d03154250200c0d881302103104805503134000d0b0100b030320140e50f40d40042d001030415802691060b041030b11002080b01c40a91180850b00e050406043d8841c1d0000107090441e00160b0740840c4403138540c5041a11440303581c000060112107080420351701404c10015000c80401c0c04030000000c1e845603028104120112000c03540280401d00500c41035114410842c0c038207214 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 91012194 1250 91010944 91010957
    0x50d020c03280503070c141e0109111e1e061c05072a050f0a06050612010b01080403030902010e030a11040b0604150c05100e030706110a08040206030603100218090906011202010f 78
    0x41c9419236410b884802e4075045103139100c59101092200f150344c0005944000c4580200b80c8040c00c3c480500c0702d15014225108100f0860005088100b0010f00070301c0c0340303004040316528403201842760306440c6c01480c1046d860303180c880083e182d9805034140f081308180c50302d10030240002c10390620b145181c1e5070508603040d004141c0c5c9507100c140b003041440c04940c840c010114192803c0014082d140c072a100340c031000b903810402811000d0345c2115107560030030340601d800b10f6684070174001687c105160500450305403186100ea40c0a01c246a81d5131403908400f01d9061148140c0c42c010003103d4001c40c000c407508600c14503402c01b41e080c01a0307181401d49210744141e61b95144d628814608a074140c1d80e00280d1074000040c0441001814032880c4c41c40441c0c40607007818041c2c90301b001040d0302c100403c002e0203000008082080d07680c1c200075070380020420f8001075580d50303004041780003001c568200c1c0900030300000d8042800c400c00030034518180e4613007903940100607141c0d40046810a0700e42100d40c0c00e00c42d4 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 91013444 1250 91012194 91012213
    0x1305091503100c1b0b24060a12050a0608070506251209270c1e02070e0109060b0a05030a060905040803190204060e01050d020c03280503070c14 63
    0xc05001e41d03036003400c1c1c8500004810321241070150400b4480d21844541d400c0a0228130b0008040012003500701345084e010390f6420f061400f211030b840c0c60707144a20354081c1011817402c05540c0d02c00381000030b958880b2020b10040e21128400c1d0162a058000d01c107280c0c120f02024445070500c2006809480d184400c0340a02d8031b2801e2840400c40940d00064820030390000c02500085d070080651802400a000346164814449003103405907902d60051a101e95120000c0c034460f10302c508401c401c246a00412040143d0451030041d641d10410300c503040c20002600000102004a48510000c48124030348003031401020b043c08035101c0c0c0c8000d12440b000e9985d0a00851140300c42d20038030303100e94480c644c403a9032810704444101c41c1400201d11b0b40e080500411041c86141d03803101030b8101d0f00c0403e0a2454540d080b100c107680190050a02c5034030700b4403021a10020008107511003050001c1c1044100d5025101c1c11421100c52000315040c00200c0d0b03440482400055a4201c8500b046462405940c00b404 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 91014694 1250 91013444 91013449
    0xe06100623120103050105090c0105160302070f080304240507020118030c0f05031603050705060c10020d022503051209030c0607020d090501030603020f0105030c040801060b071713050915 82
    0x30031a000304510b141c040d000501c10070800348512900410030320700510440440d840001c02320301c220f07410070440841ca6060b6108040c0201320f2800a82441405614000e48a1900c10fa59802501c15140503010f14104180e80000b142d00d254044126a500c02e4501003450700107503103520001d903261400c02c080c10390000205082400d100081d08041507071034046803400082500c0c1401e094011400709501500c100001400001c039031045034401c2d05c0b62070711000f2010440b4100034181080d00f121900000300c02c03d6802c42344d402400242d070440d41c00052000306481600203c81c641000802040b401c015002ca40c036068071030241e010940b101180d00e001072030100d4506028043d9461030143e1b10074001d84460710f4120140301c014180030300e002c1040b80d00e0360300001d0f501c00d040001c041c103008000000c20320000500d0101c602400c6000d00038803003155070b020b40084681c030100064503c41580400031802c0b8020004542075005941c090380000e038148001c00c810810b01a0080762019480440b040994 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 91015944 1250 91014694 91014697
    0xb0406140d0e01060911031905060f03010905060106140f1c0906020a0903170915031807030506010305060106110307060c051c0b0306070203042103090e040f060e06100623 75
    0x9031401070002c5402807400360040195146c9401d80c0e2404113050013000f4500d034024011090800c41810040780d5904c03100c0100d0389240a0f42c2d8015055400c0c46d22400511500207010381c100e990342da891003500c2c00e4481201c1594012200321034180101084a0900d022648014225405540400207800c89160f60f40d81d08076800342d280540070032240402041403000242c9507106030780051000a15008002e4002451200d040110001c51400030002c00c50488414035400c00501c0918101d65509840e4242156200c00910045405100e86000841c40900c251030080c2031999500065050541c19915103019210500c2e4010401c4001d00041c01e01900c5070024402d203003284140003900d0f811410616043c190000c3c150025540204420801800e500c103413900704000900015442c001d00c1d140450351072201d0380c08220036094903424001403244405850204d948179600c10003805091591841d00da6200712210000c100008000704171031030040c2c1021210502c21440306204c420340090b0303040507 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 91017194 1250 91015944 91015961
    0xb01120f05060a090606020c1306051002030d0e0a0f0b06030109050706030c0e0405010303020a150b040606080601030c08010303090515040b03040302070812072d06050a0506190b0406140d 82
    0x40030786400500040741401c06141c0080c2c0b2105606100540c240000650b0783d0000340c0401d40942444d01401c98410650741c0141c02500c4014800d003400c800111009590b03070030110760784501c1c41c6840e043c0c50b0382c0c890004c0c0d2281140c3e40070a070340c10500107580b40c9594000700146031326099501c135604000003032401e200b1440170b004503480016030007580c0040101440380c5804624001c6240c0001030020030740024400304220307480140119000036190f1010701400007425042d40080c244940401d000f5040014140b040750b00780d800308800d50304070b00100c0e1118428130001c0c005c5094004c06010504040d4505080c1141c2030003070782c3c03031310780c2e41d0070301400a500464003a40103030000c0e28248084101481303c0306c4a4852400903a0a285080d1076881c1c25035071a80c1118054903805026207041400211110724494210004010626011000c180070b0041210080e101d0850b91070200c0710314000f03202c048e0a90709505034290400e403d00b082910005104001760305049804d00c00200b17640141c4c0921b000 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 91018444 1250 91017194 91017221
    0xf1306030b07020f0f0c090714040e0711010c080403030c03020c0a11010201110a050313020f041d0f0102040b030c0702040b0d0507061404120b0619030515130302100b0112 75
    0x74903140001d40281081d10740c41c1404c5294008804125045a000908141380034040703076290000c0d10340031001c3e01c61581420b081c4c220000007083c0001c107480010001d52040380644c854031083d40280514030300301c80482e0300d2000400c00520101d00424400d900c42c4040c40c00070b00b401464051000c2580d1701c0c00e060010121544d0100d1504840c103541c0c203000350000b000900181b2400c103141c0c01c1c8040c099003c01401d0205503c0810020800d65440c410f5194000c0c801920802496112584100f6009c1a00003030600798828070747c015210780f2051007260100c4518a4105c3e0039600c510325044d2080c0d010450503a40b154851900c25401d549000c40510a03c0c4104009c12410b40307041030191946008911100c01c0304000e21040000007603082c54911302c264844101942c99441c5000602d00303032464095841000010035000c81040000920b80da050a1070240802c10395031416071740f5425900b01500200103030090f00c0c1c0084a101a0f800020403541d0506040c04170701c406a503100122844e00c1d14410 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 91019694 1250 91018444 91018463
    0x40803070c090e060912070611121501110c13060305060c0703020d02070509010b030712020c0c040506040c09120f0506160f0e150a05070204020d02090306010e01140f130603 76
    0x4040c100e28403d210b80c554071a8084c110900d0448002500c4603010746410303400c00c50006488041201c44d50100440c080b00c141001e48a2031450702c2c3e000d480b5800c40352040c501c003030380c40c0f4500faa42c0681000074290300c8900081442c0140c81050000203c0708401541c001c0361282c0c8044000340701409200e2007a10300ca40002d03220912030500a2034136640c3d001c5581590844042802652030301250b09040da0369615110342c0e03d407501102101d98031058180c030101030b4130108407a4041d030b2001c00c00b1008104102c8089c0081d80381c0742c0405c0100c03002002444040340c82880100040d03114043c2c00b4541d5070140380d144040c4c600036250681000c008071102c03d0150004036000c0c0b0100e820400d20200c499503454000742589a100c0400e440710400708107400d21003400300b24622564464000c40305440e078046c00035501c80c141e90301c03c100a074006a044503c4ad02801d0000315115543c261814100d8122150000035031854506200130000983d004a80040c440b070403650350000d490054800a5100d0b00c0100d = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 91020944 1250 91019694 91019699
    0x2060601080a05060a060c030e09181005010e04021009090203040b270a020105160c0305100e061b09040b0409150f09020a170f070e01061d0603070311040803070c 71
    0x6201c04801404442c0c903d2074103080c00707002d4981480000544038a41000001c001682c01e050314540c50401c2001d50045884040080c0b5858000040341c440e082c0e8001c80b0700700d88060310b9101c180e0301c2c00d00491050311600c40c0003801610b001440301035002110308101e40d42d281c0302c08841c1c0c00da90003241c044c0c0c6d069588605101080301034624846407529800358060503044030226080d103130094410702904003c1c01180c0303451040b80800410091541c81210700002a95074641252190040c060020b40703940b070300d8414000c0704030105649101d154140301c0240840e20300030044102d908076200c605c0c0c00c41c2c0d44980c1340010b40c54a00c01d07a10503500400030805e003014038800072429510b07242500c0c400709090044410050303d481c648103040c0c80c0026045800010300502c0f1031701d04000303000215040d01c102d010029054007113140d054140c6c0c03600c0d5202003000c075000140340d104000400d0695001602000005c041500c00e034004901100740d0542c4500d029a10f1800a1840e0400c510503a07880c007550300304 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 91022194 1250 91020944 91020947
    0x504050102070e0408180307080f0c1002071a0705150717010503030f040314010b040c090e010803030c07060e070503010e0d1b0f030c0503120a050708090a0c0504020c01090c030302060601 82
    0x20b03140141241a600d0400c3d14155441c0060342c02004607100704d020015114194a680a00849000e0000c21044401c2408079900d91a41c41d40346240e1140900440002c01d180c00307201061400a54001c2d040114404000c3d29408540c0d1b03104134000c1e0750318054030041c4401c0501d50701100c3c0c0201b038207135151022900140245810b140040e400240300354400c001020000c506c0005480480fa080394110b00a4995980f103203002d044400c1d81e082d4803500d070102400c0b403540c120980601303891800e01a01e0a40ea21944ca4a03a0ba10003651a0207101009010410010b02c03160007102c8107041c0c800546601c25595000b29007510301c034030b040d41c0103034100c01d441d0400142c0c4152a104441160550301c099441c1540700c0c0c03042c03d03490590140402111401c0a01070040800842b11040c860281d181c21038601011400c0003000b0680c0c82d5400514500e001c02c0c5292000500260880d0f000010300502504d46000c2100940c80241c40750703169500c40140f440410601c5046c5c100941c0260051f00e56890003000 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 91023444 1250 91022194 91022203
    0xc030302013c0204030602210711060411030f0d0206070e0402091e01140f070201030501060201140a0507020a0c0902090a0b0c0304060e01111905010e191e120504050102 74
    0x100304501d074810000700c28a0402c008100c00e000c0071031142d058000070002c1c041c0000b0b8450764001600140c000510850071607200000340c284034040d800c0c900f1146c2c031000812141108803ea800074103a00c40320204012490402d04c10540990044c11110002d1180903101e003040c0c4034612007005a00600200407000d60023084180101e00100e400318a00101c80c0005180030310405da05d000402d880781c000d04000d9001e114200034908841065549903410300000e0318640e070200030202d001a090100000300c0134014051740c41407501940030300c841035450200c0007000f0b240060284086204514084000c2452055608060701e0a00d101607914943d0006124504846500031681a241040202c1080c2408800e0b6420396900e0f1408040c00962540101c2d490151228002a9401011002c090241c2d06400114506100d14000c3c82002000802503454010351540c1349942c95040300b140d00040c0d034107905c22203404842214407219000c0b54441c035412882c9495194081400080c040c13029623010003 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 91024694 1250 91023444 91023461
    0x6030d0f020303040b070201060e0103140d03050705180307051002060103050606100504140a3303020f042606010e090f0303010b0f0a03060302060c07030309090b01091503180c03030201 81
    0x820091808100000941c2c0f8840203102902c0404207001040e0864800c2d0014002400525010200355860f400d00c42c0d101c0381c01c4092100302d407141c031440040e82070290003458072071800c1b17855050401c0150080041c980c2c00b40441c241d414007030030001103819510110b07a02c1250180307034018036140d8150700c4c1991400b8030140c26079108003810321060031481c0d17020080b501502d13240b00c03641003031043d040c0120300c038011160080b42c009000701c403440d0641c0da2401c0403007131045884100780171000000c44003030b401c0340718454070710031003060410041c4a41c00c0389907200074102c8208050852002c4165180d00d0501c6000e13040089042045424081080010400d0301e1101542031301861555141501d103200c10321031894080e401c00c0c40421252842da00a82c44200159006002d03665588007002c00182c403403860340000c8010032003182010451500034414500d4800040c1c480742580c6051000e20788081c1d84c40c4102404158517201c9840c1ea401400e03068075800c0d0300c51003001040a0031464060f007500d00c40d2 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 91025944 1250 91024694 91024697
    0x203070929030303060d0f020a1502011a060a0c0206090a0e0907061b03030b0607020307090c14040f06030506060d09030504030201080a0203040b04023007090b0901030c18021b010506030d 82
    0x16214514982d80801103d41100742210000c4550720245010100000100c42c040e40c403403026a40007030200b8641082240c911190343c02048440301c0c12280c1c0284841e840c0c03c65410003420700100401c40c1c020f100c4280510300017058030b4101482040018101e0302217801c4040520300c2d101c140300046900f08090809480307a070030801d504c60904208030054802800c00541003680380c2e10a003043d1b03154603040300c03042d9401074191000e168030790102602520100d00048002080010300c0c6400380c1a0405541c10384651600740240c86c1c0c40e18070114044d0401a00c0c165000350108038100640d00a4440c25807076074402d4403110b850f54507500009d080100010214030800340100108400149003414541e40594101c40b00c0c4444008074802c0780b0f00b00d2045104901003040146139184c802c03000140340c000c03182c00d00c40c180035201041c414010022801c0c4402043c040c41d03071030144031841000d10f00b40303003036055040c005050010707800ea580c0081003825800e418a0f55210280702040c20b061100705d580001c00e = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 91027194 1250 91025944 91026011
    0xc0c010b01051216030906091406060105040303121d1504060b12100c1101060623040f060309030e0d0809090a020f0a050315120d02060f0c0f0903010902030709 70
    0x40b254820407410700100a060100c8501130304c1600b0502039441030312002e40141040040b1846841c0c1030780160201d40c100300e4144150f90003d800c5612034801c50301980e926950b17400910340c0764040703180a070101404032010040d6540b068007240008200c1d08592080d011f28003156400d02d402e0080440d0410742040b405002c01d41c82c9c0b0680d000c00000d0700203056070356000002da421032480742144d829110040c4030089509004000503119401440c41c4040c02c02c41c00c0e049400b8808001d00d0055103d54481d01500c491b055808001d558000d40c0603403003041c0030f410000e400a40703410020305a22880c00d0110380e40703d0041000001418004801c0f070b032018043d041145403c0180039214070380e002e4180400104031000001a411841d0307026844000302c00a0411000c08910114a60b00d401e00400b05400500c00c01e400a8074041c00d031170074107000f24810900580f50421080380e080391507001c00d107220381540d26800301600580b0100724060040090043c0054941c1e0105000c400302c045404c10040903140 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 91028444 1250 91027194 91027207
    0x60b0402130314120f040e01090b0d1410020310170d0e04110903030406030615050a0c0305090619020708010e060c030f09120703080601081608010312090801050c0c010b0105 76
    0x200c1c0005400d80341c201d0215925881c0440c00c451500c0b40c990244c2030210302c00706216000701d4026015100780c5101090605140e030b2142400001c8034101490b0580c07024413404003601145100850620810383c0105540c00e03082c09a4890080c4d03070080e900c800d000c01e05204104855030621a030040c84a0305600034003d80e46905000801e00720000114030f111b15911540c0254144012084901219003d000d5a40f40c640c3c0300d0015000701102e22071a281c860b25803410488241c840c000b226819403d94482d03401c2e000040d1021220fa030400c04440e40c2025080005501340c5410b1000d0566048665000344500c9042410702404d44c0c11841c2c0680d05a40b00005121041c100c540c280c170362043e440850100180d50b108400e91070a403040000c00c2c0140d00c001040d4003496401501c0340d05c00c02080c0ca85280071b48480228200001441e0190f86c0040e509100600000700e0072140103c0300000c031301e02203107126101c1c40443e00711001074440201702c5400041e01141c140c2d0a0141c1044c80d0000d082103400c000 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 91029694 1250 91028444 91028467
    0x6030c270411090907110a020a0f050a060809061506070807140d030e03090d0203010b0909010f05010506180111011b090801050109061802090607120809011401120326090a060b0402 79
    0x113202070101c40c02c1c8a00d031049000d46031001c200120025400414000c4200e039103111807440320006000b40d60240d0715400011031114010000c0314058410708004040c0f507a64500c14080f045d031007940b100e038003601c208502c00209101002501c88640203c84aa26021105a22525242c1155100030616050502c000201030f00032050382d840c1e90302941e40b002d03008110300c00a401416004d0b1388680c031240400502c803030110150711aa80c03e80c0d1910007045103980721001c01205004e1f00008100201800d500c4104552140031000705030310301c03d0004108d495600e800e54010f0043c0011260005101d42410804600d0074000d0300c0c018100141c0801c0308600f80381d410324020b940b2545140400d5000152860f03c1d445203400c86500035046007170038a1060301800004c244960170345040155608010b0b0003402c1c08031050015040718007801b03605585e4452643e0955168082c00030240004c2c107000e0700444007031036881c5050711400400001e08210380305850304100310f4491240b101d0040384188420b20044 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 91030944 1250 91029694 91029709
    0x10905060112050c12040c060201181e11060301170c0603060f21070b030412020c010801091d03160c0f05030601090908220602010605010215010506030c27041109 71
    0x14038181c2c0d00410b044d0307500c900080ca10302c120100204018460b40800c8140484079220f001074640c2540280225180180700c0000212001c1c8040c21045091504000c511614000e0b0312086114001464040d03111000203040d980090713200004010364488510100340b07040c09603000200702160030500f1400d120001c9186012280c0015001e0030b61038240a04214000108000300c0301c03404101c0b54000d44801c1003050710b81042e00c040701e1a02c000b002440c201800403c00034208035040c0d42d14603076607182080e96405880c3c0503a444086034000504035010040138801800f140c40c520980c9058130000745404103094109134840f0400034039400040c48599804103041c0c0c11101d21316004101403410f403c1c02001481a05900c00a160703620400c2c89404000c844060121006030b0001c014481d40c032001641c0724131002408141100c0f540700103005034541080074641020000030300508190107012183c00502c0d00c0c001c602443c0462501600d40c030324160044462071404268203609003016600811f124 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 91032194 1250 91030944 91030967
    0x30709020301180603110609010507050d030b0f0102030a080705031905010b0414030a03050a0f050d050906010305070816030f1106030c03040c0611060414010e070605041a040506070b04030e04021903050109050601 93
    0x180d40e000230400ca03261302c58800d0750360580d00a01654100005c040c4054020104002c159000306600c0000040075800801a121540f066451308280b59540d00d9003262203070700c010207540100d00d100c1801e40829111b41703c1c860180507400c3c40141d90360b081a00d4001083e1030241c01038860390100c0f041d200065405003d41c0e900260301d0030510a02c241505060f24603008007507a0200ca28640401c1210b14080003a8181c1240e00139810b89000d2034581280c103807200081c02e51a030704084110740c1000040e0300b40701009101405002c2049249161200040c12076100b5181480000720120510003480401c5d0100e0006044606200d10084031801ca02511194000e0019000303032030601e14a2004642900b00060407600f404c01c1d984583d8683c00003407e250068014028140000404141c07a8204541200c2c1503400c0102803500380010341d40c4054031008000e104401f003010300c0200070082c1d03c40d400940903a40030020003544010319010000c00b1030300c0592228000c4e03030404c400c2c0310042e42c004444110 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 91033444 1250 91032194 91032199
    0x5030f011b050306060f0703030b01030c050c0d0c05010e030a08070e0607030806210607030f0509060c09130204090c03060816050f120102070b0a02030f13210e03070902030118060311 80
    0xb100d84c2c031200084d84600580c030340e035003612500241a500301545a4440c9100003400d80301044003c02d0b0303103030444050154492000179039105400c0c2c08030b640d005000158030710384514008a086070160007110f045400012146020900c0d01050007141c68000350790580c04501961054200760031520b008000b103001414076805011185070001c804600741c0081c50811450100329180e40c200944d00400500ca1a44a010440d01e081d011402106000c80d100780100405031710a414020035004000c0b100e0f10602034000d4203907003000002801855070050800703034070885d1000505286481c2e5401c0c1401e403800d42c16040031295503418810741c1c0d03031283d41514011080d110010321000d003c8155009120b9800e0103001c039074560301001a1780305190001c510071200c4400c445103d031940501d40300040c04d0040e004000c50416182c1c0d031150021401018440b145d20f00d00300f40d04038840c0f00405d040c00c0f07850b000500c445030000014040741c441452100312610403a00300300304481c50341d100e0150682d51041c20f9407 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 91034694 1250 91033444 91033447
    0x602210315091f080105040b01090209011e05030115030c021c0e03191b03030509100e190306050c04050109120203032802011109060909040c0b1305030f011b05 70
    0x1420400040c40750306980001402c40d00b810f09000c40107001901c0042c0c42416a40c2d4104800f10b42a08180100da0282d944a802110a0307400c018410004e0b422003031074541040b0708041e907214400800c215625008065803202c5551354113240b03800c02c0044d4200c01c150285400c1074100c80910b0750014a014111581400c180b07503e20b0440301c00c07180408210320322a414031800c00c4a00300e840c4564030304011103115001c01e1718400381d442029561040148005000700e00d041c004a881c50074030038414030100342c42e46040801c1482000003d01c1d041041c0b01c0e00f10030700c2c1612400784200600c41c441c0f5030300190000321071800d2a2812000030407a8800d0f015015403e07003a07244040c2107403410000d503211032800e100d4118040c0e004590302c0c0b030352840f64000c5000543c02c4c64510000c4d8030b880021940c68081c09005213250481d48028807040590103442294160074800d400107000c1d00c102c000d00706144022115088803840c200070580b42c00807000c1e20200f01e0f494070040007403100001d2144044400c00e0308105 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 91035944 1250 91034694 91034701
    0x50108040f140102040b13060c0c0611070306050103030e0f01020f0a020105070606090507020a05010f0c0804023003090102070e06011e120f060503160302030c040209030f1e0706022103 81
    0x9a4000010b00c03482c01d580d60000ca0007003413084091010309140411000384031b840c1d55450300110381055000102415414542105114140c030403d080340066004004030340450ba41c0381d5403d411100c00340d00a0340001d000303c100309040d1a0060b121060500c0900c02003c0c06e1030066103150b16000e079100000d0502200144030700412000c1d400140042071010b030b08000781c6c0750200b0069204c0c0d440c484101c1d055445d2100114407540c00e4410100100034a6840e00000d03510341d824000540108022074030b08000300c0455009480041c00d052200941000185031940f00500006e0301d01030290f000442c0d80f0342c9020400c02c035640e04c54404d000003000404110028441c4c003d041c1d80d001c1080c8404d0940d2030405034804030240d007541046044402c00d50842c7d420080180601d080c04116020080d4541c0002c4841d04451601350041c1c370042c030f002030942e42580c64210300c240c80d011803401d150700ea209000c001e0403010382c810f2044200510160000e0910a01e1080d0000c1e50501850030f02184414040040b = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 91037194 1250 91035944 91035953
    0x30712051005040302030a080702070b0706020a0e031002180f060307031d060709030b0106080411090901021c050601110a030c0201082d10061107050906011106040605010303080c04050108040f 84
    0x3101401c4814940070802414142002901c0f40c0c49000808045000c00740421850b5100040140c00c0b25140c0c5401800c203240382e5541ca0203980aa00b018040200d02410504280c2d41441040c0e0103000f801ca005a850541100343d5aa206264001a2241600c45090860750700c1d040d044950107081441d0000d65501001041b60081010a42c00f2905e0b118580400140300c0d0010400340036240a500155400d1382c0c2e4250855019208540042003100e41504c4171a0500b0074544083e00401110300260500d41c2c0000540b403c1c01118038151a40754880c02402000d58100c0c01030200490060054400b040b01500c000c3d06114107048004d04118000c40040d40d8680400348182ea00d19154086100310340c180c0096880d18075055540d182a100d41140008a00e8061a0f10800700c110100240220354a01001c114036020002d00700ea0601c03002100000030b08d0810300005110394072842000500d54110305000f0070100c4005c128064407a003c100920160380c20404299000360700c0b00d8000ca0703181680c0360 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 91038444 1250 91037194 91037203
    0x60f0408060106050a0306090c02030a120b03190615051c0f0b0a05150f0112051302040c120b0103021c0b010309050303270622170a09030312090203071205 68
    0x3181036540122400440e661358410018410400d1541c0c0034003544c5d46070f074001c0d0212010004601c0c0036910070001c040039140a5031412a6400f090b01c000074510b004000401d0620b0708201d6100c1d00c1b4042c030311540041000c00d100b5902403040400307001c1a42810035001c81c050301a0740341e14204410808222004102e0550002240c13680e2202840106091010f403960242030103844110035440305086489003410485c40703a61041348160749104482a940071000c004101c0680a070f0b84415030080400b01680b038500500003a0900c0ba0358a2103a40c1d140d08200045550b251600342c100740c010440c220070940b85800301d00b0304000d00000020310000752030040c0d0080081c518000c0042c00b001c0100070020f4402c80940c1d461124072902101c400080c55a00758845804450000d14061480503c010149000c041520303080d10178040d4446884c08100c4000058006400e05000141c0c080000c3c020540c0c081303290f00c1c03111036005080c0300d03403480b0307034002078461842c0d00881103200d208003509802d0060401 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 91039694 1250 91038444 91038449
    0xc050a0609060204090b151602150c060f010b130605090d14030a0f030203091b0d0c0b0307090816090c170109020705060603061e07050c0d020c031603050309060f04 72
    0x1400300010301e80ca2501502a4002c1e02c9061290307407a00102ca4043e05010580800d00d002c0c00c07141500d400c80b0440c03a0100c81112a8043c3d07040180c3da0912107862140c0c400810540b40a44010011b91402d0a0301c2201c0c054160401e040c030407401c2c0305a01c1c0824214200c0000d50b10242407441e110011034001c80c59407401d681003d456203150000980e517007803000c4014190441699142c1c6142090410b06909130309c0150b41ea44a160b00c0340840703135004882000b038420300f003000500304104100561203e40420301d80e900401060b10b00081800380003500045800b00401c0c0c541d01800138603080c04500511500d0030b03c0340d9403146031507010100d442441440c03849514181080841250b50f1030390a141d00035003042e01e08580c94030508000c1400d0741342c0001c0c99845084804013041a000070038080780000400640380c6402c3c403405105000c5000001d01280c80c0354507542e4020b1480850b450304051030325150f0400e6400581a0000610100300048102c44036000244d400c9580d600504640d185148902e6 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 91040944 1250 91039694 91039703
    0x30f0303020909190507020111030109090201030905150106080f0c070b100b040603020918010b04140103090206070605090d08070909110403050102030f070305090d20010b12030406020105090c0a060c050a 89
    0x410080340204c603950030015114240e42c00c00055a80c0e01c1c1c02c1e422542c0e030b018106401070080c0010003404d420f58108140d001d00c103160100d40c0302a50303581c081c503102044610509001085c0014050b0036400105250301c440c007090030301014102042c1c0480c0c41d00c1500c0010b402e6200d0382d00018000501c0088036001840c149112582d5155240da0040c002c0d080b2601e0a80300e4000b00d150003a101e4060b50681d416141405041c07490325152040b82913a03c40d07444801410b05441d20412405a0ba03550007a1a10500429000c40d0502d403000380c660401c1d10380308848083c04000010310040c40d80c44907100c0c0031346145103c0000c3c00602c504003e445130142ea0b000030301e10360000041041c49240b8039801c1e4007400e00b90b102440300341c94010b41c658940711500038010000b00c0c2c3c103501c548110612201e000c54013035080000240708803da00420502e101041c400d00700d07540005000c110944c2d092107000da2004912000d4500100007c00241013603200d4481e1104000d1342d5000c80041c01820711120700300d107910 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 91042194 1250 91040944 91040959
    0xa06050a18060e04210c0f0606150309050c0d030e042f07110d030309020d03030605030c03061605071b14100c030e0405150306010306090209010807060801030f03030209 74
    0x740d600c000458005203011407007450419800154102402c2e0829000b142d10180c1c2809800100e864180358181121005d010018800244400315101d90300c6e1254041c0220400304d0558180f411811031095100030040816160500e6040030450105034003003407031022070b0343c8500c0c00708500b4115042c40e1101c0f030341640603180140c484a180c0e614141f04901001000c00020300907002052445e6a028001c0081d180340c1100c200781e501403800c01807410110b84a03060000d48030b030103900411452041c0c0c210440101350784101c04d02480c0303400c100d000c010388011001802c144c580302c100b480c00304505010010030700c6008517039042001858181c10004442c8030404040c1e803950b41c2c000c0f6104910f5000d4503400342034110a07510345684264001c11001c1c1e050348480c1c0c104000c1398140002803000905000040800d824292030a40c2c0910000d4002d6008543c0803400f00c1890041007090401a44500c25907440a03100700416a003011740b42d4112a0008040030681816040c00d602a2103541c01c015849603c = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 91043444 1250 91042194 91042199
    0xb0414090304031205070c0315020f07030206070e1c060203180a0c14040207050d0806060919030b0c03100317070f081c0606200f030301030804031401050403080705030a06050a 77
    0x5000002d0800c0382d000c0c05100305035040d20390095456105020001d0140e888410003480891007211a20100075041c0c000107181c00702c00891a81c0c0c6412544003103005800040910030b0056000204018a80707040360034035109001ea0b03042c00600300c1f1044004090b80c2c0c0120000b440d40d02c001e004c1000369582842901d00180c554500842c0020150003660034451414030074413498109071080d54661035010004100300c60987c41c0130f85013108002d01041c0e01c41c80411141800741c840d08608031030032100d241c6130791440f410b520300340c401a080240543d05000b0b041c41000030b400c82c1d100e11242202c4d005101d007032310407212546180c0c0c00c4c03062580180001401a03510400c0203000d10040c00901d0002e0290481d5000c5170b11044269100c51107404c0000b003002c80c40b0b08903029286c002c1200d0480c1c3c003003141c840234075001c20306042d03130026071080d01d42c8100460100b0501c83c14480c5500541c070780300000c200b2854a070754058030f6144003400540c01c21034080006221642d25031300032009044000e080b01030f5943d = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 91044694 1250 91043444 91043461
    0xb03090303040b160e1c060c050a120908040e04080708120a0f05010302030d1815030e1002090a060302030405150f07020708120f0c1002040906060908030315040b0414 73
    0x5206550448a101c2d1410004e00c011282c0b5001d207511203541d540e41d8032220b0034201005600d00001081c0000400c5020032500003071b04a21808992550302c6d21015201d0b1001c04c400381c5100c202c204d0001149043c0304580f400500c040c42180d040d035500030100140f640b11030401c0007150040b100000c0200b1400180e00e0f4102c0b002c040c6d81c62048008900c00c1c03040c7d000301000801904c800b031000940641c800500300b049240101c1891800c038900403060721503607a444080c204140814514200801e648110b8400303140c0040c4000500c0c0c8006007170641c83c2035041000300320306600910402c8200350b804000704d0100803080c49036440c200c07080c0142d00424285140c4415500300305668440143c468035400003004000403603420ba080d50b01211380c5040c040f600c5259459a4000662440107000b0356551444080292002e04082d0141000000c1d9003401d140d400341c8050555040004c0d10b0344180100b0240420214142000141c260b0303020079a4a05c407008240035001d20700741c6c4411b0022590400080c0f9 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 91045944 1250 91044694 91044697
    0xc0102091e0306010b0c010e0114090606090c0414060405040c08060109080d0503041509020901080a0501050106092306090315040c06050a203c010b1c06060b030903 72
    0x20308225101c2a0340080807408046071a807403101150550810801049000d400601030582c0003129400401c41108000a00d400c41c3c40486940b100044a0014840589401c1041c154460b800303440d0160310b801e00154034101401144030f007040e00b0035601001c801a488100c03d8a0042401901c2400354200d07400c3d02074551102140c440c0d00190b070700c0c200004d080342c000842e80c40006d0181c503001d02e59120740d21640a64541c100482c0d02540d101d14048005132120045c1c10300070207460340900140d2842d8501a805e60b00180c1c08a010022144000c0c8078902c80c4e0004400340d0802e10b441ba13400302207040b001c10068000c13855482e40c035010310301205240b607180700f40b0300c1d00c2207200d00c90654070103881c0d0005031114028503100304c0004201c01c1c0d11440c90002c4484050403056840101c401d8904041c3c41401c00315207c0d020020000c440d183c040201c270b420f0560028847c0e0500000b40b2002d8585400320f4020b020480709103104d02800f80c80130042c406154003000140040743d8003243c3c3d030316040e6681e076070782e = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 91047194 1250 91045944 91045957
    0x40311030c01031104120618080309010c0801052209080316110102030f041403040503100b120f030306190503060403021e010504031d130c030506150c0d080c0f0c0102 73
    0x20707000d05185030207158401c3c46002c80c44018403101c94102400c03c5a109000086041d080342e10310b6990121304000510b40b00420040303841041c4685e40d03843c1c80c1c0d003001c0c06e441e014151071003031040ea000144500d681d5a654800da000002013100503100d8030150743c00190000503c05452a0350001c140210121940d501d010717484490384505210420240080c1d08030320040710304c1c101c079051103070102e00041c161840300041b5411950459007043d440d00c001a0600c007507078040c803c046664809440d014100600d21088034800e8201600511a110b24020303141d21000700254450100b0305c06054009501071800c4024203000740407100d85207401e00d0301075502c5110000203c0d9980e0164545450408140520381c4103962650398114001e18240d00510281c60601700c0c9948000c80310100f80403c411441541c900080c03555012132181051010320001c0c502c5c5030742142c444030040003c1d82200100003030f02508201c03103180601c0c841d9200b0450700c405014030242040d0804001586100e440c40540190031f0 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 91048444 1250 91047194 91047199
    0x60308030f090a1b0f0e1e1b030c18090403090510030e0f0a0308180304060309030c080a03090605090c0d1509050609071e230120150604020906030109050c0d02040311 73
    0x44143d218801d441ba841011140c03040d203d901001e00151480c070144c10310b0340011144403942025103440703200c0f6500350421078000d0300100c1c001c500150006200d6022241e856800c0d61458164182510020b003000d030326000d1107020b12014003001100d584260320079510030b404c1406554003c00340b14409601e41106400a030300048101d008910b018a4015010009044220040d441c1620b0148140c01500c40b40c036056051028103c0b100d0040f070003a5006101d000c80b1581c0008001200785060030440742e000d000c1c070a43d5030180c161700704503840d6201100c0344103070800c00b925007503801c440700c00000d4000100e000700b80d406000e060102c01600003070a01d081d02c400b100e445280c1c1c259081d185003544190f100f9480d5801e101c0030680003442c05105030b49a442010716190902218114840807101c241000180d0a90311514000a00c819111689030304400115415454900d80c00000340352400103000318030f0071950ba60040b03042610458200d03815040c20780b00c02d5450329982e04024030b4922041c50982e0 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 91049694 1250 91048444 91048469
    0x2e0201090209070e10080a1103070c031715090c040302030a030c0606090b1008090f03030c0a17130209090106050915010206060f03060a0f150b1903060308030f090a1b 73
    0x10b0f040c074042c2160303040810300680041c4034440c581c1d80807524000080c148120095884940c14031040c001001944a00f407280c079007004855107032a00030200c0344065045144000f00744284030502c0203100a1903c45e000c100d80c01c00c01500e0703919410b581031050b40d20003035040c402c08414004040c0c00c0f00b22004a58014134007003000304e0781c0e80780c14401d4981c8580c145600200003c0c039410124061804160080d4000f02190255214610018551f900548002d900c400020500c08204c55001c00709900160024500840909000c076911465a0319804024841c0004000298038448258044002450010154400c034204461aa0340d03c10b180840e413030046c014071001411905120034000c08080c0d001d002000303e03584110750030f001480080413034458152103402c4102c103004905026006091074000036030f5079224140804182403030303071003c1c2402d14ac2850790400210b1b00c00000c1d258001a07014081c59240e4451600d42d00f854100c1100420a03030510064000d5100c00d003200c1001d40d004440d242 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 91050944 1250 91049694 91049701
    0x3050f240603090307020d0b010512071208070317040305040302040b0f10050a030b030307050d031b0c0b100306090501060e090307080316200c1509010e2e0201090209 73
    0x203110300c2004031200c64104403055810411800d0500c000c6503c6400407064a003000c075a64001111009200c40c2900d00c0c805803001800603180504141c03070f51041c0d00d8010980c40745030403040c45000034031050160a16501042340d00625004200c40002c0c2d090841e010b4a40d13160514003d08290054003081c0d01036450725000e0102405c061140c4640440010014094243e88140031265684000b41c14410503403250480030050300c04002508081c1d1040004d8110f00502200041c1102c036504403820300d00400903101c01405070030400400d406074001c001d071846540c560a40c00542078003076200414080c90303d80d00006121040d03100f0342c1920044030001120340c40381c0d0841540e074045d0404c0a09214020008110100c4843d1491a1940d59606004120455034400d00044040040074104a80c0100c014448a843e004020703008441c4408003050030400341d080002e1000b060703100d034940950310002a01c10103404034100101d1441244691a00441034108020701070220180d040b8001c82258010 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 91052194 1250 91050944 91050961
    0xf010c0516180b0303120a060914060306071e111e01090309050105033c0f15060f0a0e0d05160609050904050303040b19050106090302011701180e070b040603050f 71
    0x210505060024015810030181b0a0000c14055011b00101045176803103400041c440c2c0705000d401c1148118000b45d544900d003240500d424040c00070400010400208282000d6004040e0729103410525403421075541810455041d14160540094110207010f91005038140d00303054008117006803007585d0b03503200a40c4e100c005445a0100760f4050540c54903c04005144003c444843c1e03c280348001c000c000341e8001d1244d00745161a064032015100340309102000010280d007550003180c0c6509031031540c586515105c000d048c80c0100041c22081005a2408003400c3e52010100d019064012080d184029140401070011071128441c1c440806c1807202e001409280413240e0070312035078100014500c0c40c0d603140c0c0c84500b0b030600109100c40ca5003410301038580d00c008500c9601c0c040d0403903844030120141140009032080040b01c00c0c0c0002080401c00620081c0b144c00344605603034a41050100b1001a5444440d09001403600f00d2158110302050000300140d05401013400b61010700c070300760303d685c480080 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 91053444 1250 91052194 91052201
    0x91a03010510080910020702061608042102030c010f0c0b0a02041412030409021e03040b0103020f04051003110f03030c1509070b031609090203160e01050c07050f010c051618 76
    0x2810040c941103042d80300307174030042900209a40741c07005006901e000038200b54600c990044070f0064465060200e810b0050600e10903c9420004410641d400f181c2c1d03241d400a5a95111820010304102c4201085000701e402100341c01065603002c5031450325481c000c16090000c1d0014865100c540d1050207025160741000e040341c0c0000d908600184d845c00d8109822000603602c01c9280c00c01902c0f02928608010569802841c010b5101d00c1d801011945540108120303901d4070854a84107602d8981030154140c1e180940d101120303882250108807034501000600304940c0001242e030175006c0001c480000c608041680402c0310b4041242c2c00d42a203c407600540c5c0d45016009030381e0030200c2000855001c150a0b4084d18102001e8980360200f01d0f1500e00716400d1f07801c151140c101414508680e050386030742001b00d40c0e030f4400c002c2c40c1c03d0382029040403032584d861140e03128a5000d0b1a4403980e000c0c1c41c0c2d01c42d00e42c0c419403e400c01c1c02c0310142450b941400c420187c06204144809100c01c0e240b86020001d0300 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 91054694 1250 91053444 91053451
    0x30f08010f05010503010314030f0c07050307090c1e030e010f050604060b07031d06091f0306062c0f09041a060a0303050901050d06031509020405010f03080712091a0301051008 77
    0x80d84e440c1140c2c256540c0c040d44921110180715584024065040e4104041c0003c04142a1080c042c1442526203401e240c03400c4c01d21780150f2141410070074040d042e030f940001101101e10f00319110110b003826038a010b800911941c8900c80d020350a100707a1201004907034000600a03401640c2c00c10429541d00c01d0101180124003004000960764004043d80c41c035449509540004003c003814030301070f51035001480c60000301030f007070620800c20f540c09900107800d07200f40c1e0020705450a143c0003800c6034021062501c2420212107102e00400c10440d1141c4c0c4415044060f52207000e401a4010b05041c03c0041e00c0c0645002a506100c802d940020802e05040d5106030440e98541c0300d55003444107240054615410004400d03901c2035407100000081041e18440d194084804d450004218201e4011700096400581100354440da00110410000c0c00d14421140916003041d4045050b08100400300c1b001c5001c2e42c84100200208e5502c40c1d81d694403030000354104c8900311942121060320f4003051b0ba039100102c = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 91055944 1250 91054694 91054697
    0x261203040b0c1b070f03030201152403020405060f0c0709110a0f021f021e07020904031b080c030406030b0405060904020f0103020705010f0f0605060c07180204080604030f08010f0501 80
    0x98000c91840355140340940050404001611490049000980d1130a442030b800b0b5041407851807010420301d50203115100d070f14018070b02000955400c1c2442e90307009061a00e00c446480e24041c0d0341c07a00d454400c1d41a50003802008001e6a90380a101c0d01503a010b820018544025010300900001d290f812482281d13004011485901c0c00d194800d0025111640e080866000758003480c41840c2c1010081800c080300a1000c410041e00c07000c0954076032101960901c40c0010982041007a14013590707403007220590140e4107107000d55040d81010400c20711020040001803149d1000300d009041288044040d00983d08569000c1050341c000004201c20b031201034078081e8002c03000034007107005420f0510109101d100c06050162605189590369030031148107801c14441142d856111034036034400750060f01c009050448440c0c0c180200c4006450300d40c42c81d846041840b8448540b0366081000c0390301030f60020020541170301d41c5480c080c00c01a02100340301c1c0480002036940340c000300d0300c504946558815550107 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 91057194 1250 91055944 91055963
    0x50f030a0f0b220303090308090c090103080313021305040303200711150c0a0b0604140705130308030106050702040506090702070506090307120302070905070905100e01030626120304 80
    0x10b40c590038449007014203580714601d0042515400c100c0016104000f0b28400e50700050364420b1410004d0000d50003800d18142e5800c6a1000d0300c080c2d442c0d03424941941e17040900c45503a0b4484858400c00081c0040c03009410541c103504000c0ba80000c0d501243c4114080d44052003010180b40020440741c101e8484c1c0980d540060040c400452b94005c03130780c2c103030b007002801030b80080128448481041c0c2111891500030340c4001003403030402034401c0186403c8103064609014141d011607104020b55801809201000804181d402d6035542c8108810000e58225500381d40d2544c4402006080b5030100700168021410719021a040f82015540341e441a1030383e038040c0084a04240410640754051082154140304d01c02001c0303002031007000103400d01c601c260005d00e1402e203441c00510548900401000510039000020041078850034143c0b1b10703420152034600da060003947c1c0160000c04540e003196101c000d5a4032224010030040c0300b0900d0307110f03002d0221100d41040c0401c2445c0380c4001c40b4010490b128 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 91058444 1250 91057194 91057223
    0x30b0a1e17190809030c120c01230a231801022505010302070602071a06190f06050c1006090507020f1f18060e010203040c0801140705031f03060204050f030a 69
    0x201c2c01c025201c0c03040c00806031b0301e01481c0200084c5045004d0107000d0401d8101483c0c03584150780010320307000c5074089003003034018140d003184070000d443c0030b00110407050040c209848103003000e031003080001d0f1220003102c1a417943d8030204d69890f0b50219002c0f041c0540300d01d594442d10080103a902440d40044140303503c2c1064140401100071350031002d0115281d41d024440c900c009400000c0d613914240400468079602d16261080008000d0f91004100c130b00701140009004030110307103070030001340d41036420955646c4007951603661a2484038400b020040e46420030100d000314040d04828014003081c0d08613488510b2000c90a40c81e42040e00f400107042c42000e00c1040c1521041d04446e0050345035501004c1c00d0304180d00c8070402d460f0041354140003650f000041004000c0c0840c110720180c41106e008000780c2c482c0c00103400b45880090206014000c0200c0000c504544140b0482c02d0ba0814400741034141e5520b20308040a50024090148218804120001c040c100010610340030350b04080088500007 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 91059694 1250 91058444 91058453
    0x50c030f040818030f1c14070807110907020706020709060f171501060903020103060f08060f04020a080123160909020918010b0c0105010806090d030b0a1e1719 70
    0xe001d00f02403029181d8816100016030f405101c4100117101d160090507440405800f1006050702c00f852200600503902d025042030302c07403041600d0381d8a81c81040742c1d030b0340c4085082070403507150280410303603224410700c040100701540840c400c02280e0b02d54084031505038480c4800b03015a10640181202e03401904404c1040c0300407505c0b8285100b69080c1600d8500e03c030052200c6030000c0c00d82010000c00d800070410411964140308000c0107000120300c041c2003500782501c6944800c0c01402030040c40541502103002e654031200010001d1048000030030664004101d00f0715810000718000c40c5203030001c0c0000302c2d841c043c4018013040c0b0000d0b60303610941d2810100c09000941151050070781000c140360107016840c410510460191a400316540c1d1904219a50f26017511016002030169812000034440000700019101812320403071b08000c01d10710070500125030340c01d4060b84500c12000080107510500b8400c40c4c8098140d8900f04404000c14070118080340d81d40010107039902680025415880215 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 91060944 1250 91059694 91059697
    0x15061401170c07020d080406080601020a0b01050108151c0519031b0501020f0a031d010e06010501120f02070f0c0905090307060e0f070f08011503020a0504020a0512070909050c030f0408 81
    0x1182441c00f8242001c98001c12008030402d1070840d5040c400203010b02c90a500b00e9446a40814241b00030000c440303099480d10305200042c42810705000350701000c140071004074011103021100103841ca2011541c2c012607900404601c0c0d40640d4140141003c180e540d460300c41c4003600040e010380f40c40340038803000540c266a000c505a01a01c0d155030038042075002090b02030080490340e45a5038080382200381d01001e8141c51207030380300801042c1c1c54040d4001175110007141c5541158002d00340100c2400710300f0107890103450880e07003c11403c3d00c001010303010403194070000360940d80514140d030142515961503c0c00c031030098500d0318182d402030050000107499504582402c014100c00e44011480d000302061504d24181c00c01c0140c42e10068043c01002000d2052400900100c05843e800c03500d540c0100d40203610b64000c10b4022a000146110111f006200315001074030203456285d000d2500080c000d1140c0b1250080480f110b0078607021904660403101664000e610707450940702ca41c1c84513034402009 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 91062194 1250 91060944 91060951
    0xb0601141908041a090606010e01030905030301030515060612130602090d050d030c03020f0d150b03010902040e060105030c12100b16140604030c0f1e1506140117 71
    0x95000304400c2444a21a100514141009480d07454281c180382c940240c0495850300220785400034101001020480006c507150040428282140e0750100140101e0261007012405030a9120000002040000c00603001034060036400014496480ea001000518814164404216040f101c0419034400300e082c2480e848902c6940d006203009505404240c20b1075010340c0903039003900045506165603805000e09003800c0c00c40e1600310310308031020000e10020301603a80705852180ea01c180d840c1008d110080c5c4003001d0884c402c803258903503075106031310300c0603500600803c2402100780000c6946540110700303480c010007441508500b05481d82c594200c2e0348800805550700220750000c0021006424402000d0720001030a00221244042c10290005d10300651411001d902c0a030070030011a92101440c840251b000000e655448800d040100c95100c0c00400303042503032590311043c41007102d164409200000f401e078040c00302e2039941d0030440501014400442c003050700c4c40701407002030040b0044540e0 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 91063444 1250 91062194 91062227
    0x7030602090a05040518060a050106090311030109060e0313151209020d061d1b01140d02090306070e03010c030b011d030f16170a030c11040e0f06010f0504090b0601 72
    0x218140d031840000c00317035070055a107024080d030141e1408003441002e01155911800e800024041545001320041221460b48405018080442c81c2a88150f40c290030014080e50407130341c244032191180c004203449038041d41c130b804007000d540880000c01c048401800c424410003505c41e01400030b49840000080d003481c9500300d91000c480d40c4c60000082a920503100d03205026100112000b00311200b240c030342400100c04030103984c8400559042680d00804040480496042c0c02c1e4940c4030345070321040030340220003e80e6858000c0740100505d19500804403a802c01c4118000d011305015450143c040300e07070b420800c0c1c3c005000c01441c1300802400c450700412180c2c0181c1181c11460404103050f0500d00f5030540c40940349140001040030107a0f40300c04a05880191025002da0940c03564040c150f83c42e8880c0082c90743c201155044615603c03070b88451010340f030480a592460707001980c1c0c9515070009014009280c1039503a4003185d241080d20035030034442c0e03000c0f00e40107054480320010749100b900340d0100030 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 91064694 1250 91063444 91063459
    0xe090c0d03020f0d05220e04030e1f020c011e02060123040f02070204111801031a0603100303030c0c020102100b03030f0d0203090c010e13050402060c0d0e0301060f06020703060209 79
    0x205108410806850b542d00e0590341c250f2100b0207a01d9250311b41d642582d00303841d080845071040c8a26509850420b80191789410603264014885000c82d421038021040074000d000700d2110a00501d40110f08000c1c06402603881c000b00a0310f601890840700310201c0c0042c0181e100b40014051611450341c040341003101000c480e00c0924001d40000d00342d4589002c450b041030740218100701103092500500031030400c0000c00750f041500d00c20200492010044001e810141c40b03014400f2601c80450b202407141e40050f00c881d9503480c0001c03044d05c0640451008600003481c0441041c611071059481d115016416405852419208200b12018000f02d5000541c14002085080803540880005140d00744542a0140e00d81c81e200b14103a0030007260440303c40c14000c018a6000b003c1c0d81c1d1130314902c55112110710014142d151400865424011388403122491301c00c0780d000159540c1c20000c59405410704030000e01615480741c8900400c010284120700c0035900a039002d2001860310307005424030641c080d0207503 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 91065944 1250 91064694 91064713
    0xc02010201110c011a0303070312050a0209100509031018020105031b03041407060311030117010b131a0607020d1e0204090605041a0105101103090307030b0106090e090c0d0302 77
    0x20b691540841505505695612081205600e0305d181400d40000110051810724400740c4019004424098040480c1c0369607800149a06a455068901d00c1d100500601002c08080201800396441501464030034402c4091a0010150f140580305102c2d018084440398038150340c0c01581c15801c0645400001490381400d003e560054202545c419030191144003060b5003a0f28001e402d1901caa04840105803c00c1c030308080c0c425002c170480741103403034681110344c0350308000b140707103004180d003000301d80e8051819040d0703400c0280c0b15084084800c118400c4501400c000604000e440d110b500402508800c0d410030410129020110b0f18088240d503480110f0b8105e03281c1d0000f400c40d52038080444480360b884041c4000e011103602c0840010032050384810345035041800013480000c0b45428101000f0f514015040104000d10a1f40d4070040040c0894501d56100d04c2d00c400e40b44070034000c036400078000b500c0000d043c0240c821881c2c0184e8405024040c203402c4281408461014180103030203511072500e03031 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 91067194 1250 91065944 91065971
    0xe1201060317040f0f061b050102090a0308040f06020102030103111009030b01180e0a170306130207080301050f030a03050a0f0e030d09090e0a022803050a0c05180106080402010c02010201 82
    0x50402c900604010742daa82802d48114015055412121401c102c02c00140726041c0c0003c0b0302215a10404051180112a843c12602920a01000c15080f0325201c1d40002000142c50180c800c3e500c515012803003030358a03000300702d0803800240301c0a482e140b500c00b040000c608000c0040c914a0f103240c0707001d00c42c8944075144e000a401c2d080c0c2c000d0b00000d0303100c444102e1084180c071503d015102030202801702c0c01c40b0303600ca5900e0300305441d607101c1401034000301052041c5d903030030140c508049a00d5420f42d1201801d0902507242c2e0800d1017018007802052400700b0030f0380f401203196213006501d82c843c0c5060010700c4c45e00b01c60042440c80c01c14280808203004d441d880c0c1c0c0802640701c011481d42e40305201c280c18029068140d50703204541d034441d9401181c100700180d554100c0325400034601c000d8401a201d100041034095480c0da030001e4007070b0050141c014244403000e03031002c040c2c400a4840910051150380030300851542482218002800c04020600641c441c0c9500e10780742d070051001280b081d024810307 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 91068444 1250 91067194 91067213
    0xd02090603120307050c061e061018120203010f0915020c0a06020c0a050d0f02070b1c060f060e0a030b0a0f11040603060f0812121305010218130605010e12010603 71
    0x4591300440c1020500e800401003c004a035071240342c032011f01209800341c07800e0808401003e88160700c00c6d440881c1000209104a00c3e840e016185000c0d91f22226544450b00e60401c122503205a00035401c144500890803490300030410785c00d5000c441d1040d40408400204c0c0203400c02e0010030618005c00c95044042102400074141c158800c601400e4030508500e03000785400074429484061000001ca403080898000c140141101c0c0d42140003507444080c0805805501c1101c985007a01500c1c0100200c1c601540504280941300385840b412040c980840030003010005038440100b640425034001450011181c01600703585001c820082020821000d25400a4006030444000a5501c1208103d180c10030496180180755100140c8100740d544c0314107600c140300da070030540025541500810315540010403121072403504074000715241c03118000d5692054280880742403041c5030a90000802031018810318040300c80584869502900030410301c0360740302e085103440c0019507940c1c00c0000801d00010 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 91069694 1250 91068444 91068451
    0x30901110705040603111008010e131403160506010603020c03040512010f05040602090a14030a0609050f060901020d0e0115180209090108060604050f090a02060904020408100506100e0d020906031203 87
    0x10305900d10043c6c064240111140341e00c144404010341000100a0b024400b0740301900041c4120400b40004010b04058840c46900017601c81c06201c0040e2141c080c0d0340300d03915859098400c03019610540d070f032585c04074268003a80000c00c02c9604100f00400440c9081c1c031490a802504e14004150030403010000710440d0700c21201a0349081c0c001500b4022403411880c508082c0604a060062244402d00402c0e42c3c0c8140190040480341e58607040c0c004d04c0f00801c41030112403442c00c220386c000d151441455010f0740011080c40c600c1c07410240c0242c011001805400301a0140c260018401841d06d44288441d00c0f68428550455034208140b15680c1c0f2100100c601802c0c5800007484281086802d03c42150001414074041141d49800e108003540d01080810ac042d4040b41c40e642c40c1c0820742e001400900c62640f081004e8440c0e8500b01c410340000ba0007851040e44101c0c0c2401610304000c00030b403103400c051101c8543c840c002c044140018a814035410fa0400005001c880c00d03123088090011550344142c = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 91070944 1250 91069694 91069703
    0xc0705090106020a031b02060702030a06090203120403021e0609181f1214010b0d031e0302030c122a0706110406050a030e010e0106120b0c0c030901110705040603 71
    0x11141401542454103500e0300400381803004207000c0c03003d038074000c00e01002100500c49550308103420340195540c510980b2211500141560343e1041e036071401000402aa180c128041d006541c00402c0005960055404498001c0c01040b04c0e40850803203c00201d80d80c0704c005900c20b00c240700c3d44900e601c682280309074040310000d451140d8184030006044401c941c0c0200d0740d0103400c4201c1404020b01c26140820070030b5000c0c012811034091510080c0c00b50806100050304082100b189000b850350150b050fa04070640401c55840c0b4004000c000c50503032004407180560100200721000c03a0104202d41c00341d215145a001545c400129283e1201c00000e03050308407070842001c100318061007454451100d441c555003040c0c501c0c09107010304c082d042d4010340c0c6885043c990f40315580540c50500b07400c04020351190703c0080004607103910108a0322024090103649410400000440c0c070000b41c1c088a07941a413aa00450030700c1e8150004480c400703100804070742d103030213601000200c0751114018540a54480d = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 91072194 1250 91070944 91070953
    0x11060a060905010506280302040b03190e0d0e150d050705030709080a0b0402010f0c1502040801150806060906030a15020405040f09030e3006041b1a031009020c 70
    0x41070754500c00e4900603004244214810488110141d4184022903c0400304400d60030781d004004d43d05900901540e84030121004000081049060004c200307481c1c08a1104003c0100074174814401d60784920088080003c1240d0961042c01c070315003180b805510206c1c41c4019803428444031400f0090b5001541e8440105d40c02005001580b908181070f030001e8452200100307031406968503010307981500a80003074140540403825601452003802c204040d00d4000640c41d401b104030400c0d0000951151043c841e06518141501c14640c0d000f8403248200e85801000b40700d1910b540d000c0040010018044580c0352160400c0c01c000070b41c2c02c4d034000304a55540341c80181c44070310304405d1005840c0080b20125103140b501c03840c103000a4105092104022050b20412000642c00c0100c150540c949680801c2d4400b40311844170400e4000201c40e403007a40b051002e4003440c504115070039400c0710907000d551780640d5881c1c4018864101c40001d554041a15040e0000290740c4260b1102260b000c0f0008040d2a0003 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 91073444 1250 91072194 91072199
    0x60f04030209010e04030507110a0503031315030204050a140303070218011401090608070c060612060b1206010308030106080901060f080d0327080705070b121509040b0c090111060a06 80
    0x402c5251140108121040901e41e07203455a0b00804030300c6a448002c00c2c41704d41d50b81555040e12101c41180180c072003e0f04680c1d40c0c0910788540c0340c0c040700c2403003070504030f603044101c40385618402d00a071422144090400c10002e070402d0500c480214800a030b858141c4010310410016a8964a94140504c900124254554100224100c2d2441c15188082c14451001000c0112a61000f040c42d4400320524040c600200185044805012603a01c015240f4017103d01280501c011036011007048c61045541840821a81c5402038590b41d00341310140501c1814001001501d024610040d030014000000141494a44140402c2c5501c075411462280d402002c141400c1ca400d441035442124101c001c0021184511a03642e100122100008088060201e05d5030104a42080a0406400d0ba0344c90035468030040001c101801d42c0481c1d01c5c100054590884400d1070514a500c035001310b41240b030001c0690356a80c00c1004550005c10328504115071030222151821086c07010900440902001240452 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 91074694 1250 91073444 91073449
    0x2070c12030f0311180a090203071709010c08010506070311031b10290a15050307020706080105011407021809060907140303030a0c1101050406022503120f0902060f040302 75
    0x100010b01c040145441c150f40c00b40c0000990b4155130f407446004040e0343d038a9080101048500240c1d9200780c0002c0d0010091115280e000345a1381c4414040700a1194035913a03412829091b07408001c04100800e400c0070051141e41407800c010007441d4040e040c100400c51005105514550000d000000405000c0414003031104042c0000440324064a20074006650100c00c1e403158003e0041c000488070f1030103102c1421940b0740b4041c0c08002c0c0b100c103c0360080b02800d483c0140003a441104c543c001401007107000305220740101e04641c1a220107a48107900940c01240009441d84504021703a44200300700107004c01c1034040381c40c5610940b26140901024105041031525000585d0040f12048165090040300d5481c000207481c1d21116410021a1a001e54942683c441d00359100c100d0095080c64108014024241c004150a54200d950b041900311803281c5001c43c215880002030006465072a480118822038000b4001c2c0144030f40005803101c841d900003100c0782e01420100540d000080703010015071 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 91075944 1250 91074694 91074707
    0x30a0f0f0b07210e0a080d06061404060509190b0a0e01140a0e0f120f0c1e1c020a0801060f030501050a05010612020a020a0c08010f0509010e0703110402070c1203 71
    0xb500034203185440c40d0800140c08101c0c0100e4500e03400c0f03503954503842c031140380b410401440504d401c44030456442924885840c040c00700d501441c00422005000c00300c0c1200c00c841140e04442a42c0d8070603040c401c1003002c0040d21500d01c800c03140c1214102502103451a250001024800b101d074481d150903044910014004440420910340c1d00305080c1305038540d5540000c060442200c048401800031485007001641001b92800400d01c24030031421030014203800001c2d546140f0400b1905000d0403000079026903844035003d082a0782044d40741e20b1112109060741a80360f1070920041110030003686074410b40b03003110819409241040b81c20402001400400c0c814550041c200c11018065036042c0100030742500c1c01600c0083c121780c1d00156803446a4070034080c4140c104d901050f480400d0b40c0d230341189800f80400716147c4907442d1074007000c0307501040144104200c05200401800c4d0b0705146480f03036513400d548009403c0d0010f03001c002c04400200071480090213030004840b070b125240a40d00380145070 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 91077194 1250 91075944 91075951
    0x2090112110d050c0d020a02030d1401031e060608030f04060e0603040b0402010c0606030210080403030b030f1905120f070b0c030c0f0d09020925022a030a0f0f0b 71
    0xa8619003070200d16403500c03036811182e8103400c4441c04a46a29080d076050040e10a0b0540004054130100d064049142d010000f010201815039060280704c0e140e800c035a001400a110040c0f0100064001300d8034243d20308015489103001c0c8a0002c0c0c00d5943d140d001c2d0031907101d0880d450204000107400d001d0160000d0031070310449000d0303920504500d8990742d80c1d094032401030300c043e051208d031ba8042c0040020503007004000c1c56000c0c25030081b001e070440001d0042002501d0440200342400142465030600041040c8030180c828000c0102025003600da454048200c0d034243c440340128060041e08032510300007408481550780040b980c40d01c081c14100c003580e00140c124104150b0810038080d1486d10750060b100340b1104000ca40d070340c80c50943c81d164014402d0040094201070a04104034034000c1c885544072500412101070351030f02a109204036154540c84c44641c0300105c0741030310328105400461043c450f581c0042d00321541c070340c403649030307144c0000c0c2c803520440c3d50a0f2034040703580402080f40011500f = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 91078444 1250 91077194 91077227
    0x5090f0102040e182107060b0d050a021009031a160f02070303050901050409050f040b0105040b06030a0b0d050f030d0c080c070308062b0506011401080406110409050901020901 77
    0x30b01e8103051424191210207880702060350192100e281d0348420a000560b842c400c102d440c00205488180b040f80789401c01007054039011f1400101424a00303000c01911090380e03200018000e40303280d036800c2100304055400d041c010003841c9600400080c0400c400c03002942d015100400c200e1400701014108514400f600398100010221b0583c140e50700080c6590642b0740c5410140e440ea0301450049a2500495100420050401c01484180680c4045003405203000b10040b03082680c030780d424041541d803450341c91030b0010810000a465540c00b64048000114000d100b00c0300703010303207031959813a01c0030207407400c0c0503030304009151810100345101d454000035080c117205219281c01c070000d10a40c060310301c014003070010140c00134201d59610100011003040d421120b00c640f10381280c1c110300c1ca2040000403100e511a450000c0307807000c001041242448016515a41c0c16520b554507040a0005e0400f217400c500b106000c04604191036000e924828107101000503125a4410001815401f000c05000c0 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 91079694 1250 91078444 91078447
    0x507091508070e0a090804060f14090310051305150a0f1104120c0b04080f06010803090d020d05011811011704030f0e011418010206011e06080402031c020105090f0102 73
    0x10007240410074a0880300c44081c20541a5200413042025050445e001010b40c500000e01248040e02700340310a610f28040e9a44e01d0906031880300000440c8601c1c9409034ac550301116108508204a4102641c0710f017507642c201c203669201d44d5910b4503015815410708080c040203020410340c12030724404e4003c1c590005a0600890840358400400361046000d000d0002c10f4942201042c48a103001410043c26a01106030781e85640d00c0c003540d1140c02900c1082c41600030390000180c00d040c0001940c1c00c0400c0101506000c2ea03440e0300700401e651688a00710350a540703402c0c07040c20f80340d16012644030850040400c0c032201c91a4800040041c030210300001003055030030050102181d44072200744440da216007000c4204501e444c0040e96081c2e4180b94101211500040c85044015904031529580b84280c0071141c007643c955440c0c5040c0c00d40c000e00d012001c0401a41004000c1c8540d05864100b400030307003034512149038048040850242020345401503074440c003d0101c50381c02040401603020071b440003107 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 91080944 1250 91079694 91079699
    0x30522030504090c0c0506010816091a12120a050702040f0507020c0103050a0b060409020703030605030307030c02010f0c140105010806150f090903190e190b07060f0b03070305070915 80
    0xa041d0340258042c150701e0b150b031058600c040301c0c0980016001c543c0c110003102c0056030740c0d0b012140c0c0d03016408441c4038282082000000c1c401424024a0400760000c019000d03003140342c1040c020308000d079040302a158480c000200d00070440b607800174a55100f107079440716518030ba240180015140f02c181e001e000e0900c1c000400103102d50108116903000c0003440c02090701e80ba01c220f4100500017007000281c0c4503900040000310b100e06ca41c010309005220351000e103c1141c4c0c4004140c4c4074000c0182c043c2c0420403099000c80150700c508070024400c4103905001d440750b00c2c40d0312010344200000400c0c4920369520341c0103002c0c0c03510801403950700818100340d039030010750003001203034810f0030941c00d00d0300031101c80c1c0100f85209000d00507a811503180c0055031200f10032046c00186005200604d8034020642c072011002c0004c2240141400c1e24841c2200744d00e8200244d440800801d00301518081655031401c0e02d403032035030b03080c001d22000b5030003800100b1800c1d042a61010450b140301c2000610b12859001c00c = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 91082194 1250 91080944 91080947
    0x1118010e0105030f070c150f020705010f06030302061308040e01082a06092b0b040c06080c180406030602040b090a0506090307030b0406090b07030606180b1801030e0d03052203 77
    0x855210703d29160004a00016140c01f00c49a0700c0350001001213814004500074424150380540502030250000307100300c030385410111b000c40b02e8500015005810050003d0340002d0280c90010344e440c481d0606510f059600c00c0c2644c01e11801382c0092525030016218041c0c03280d54002182c1158440c1101c241c041849034000414610a85404500807011840343d82c2c11034641c020141d0116480b80101c02c0c06980510300101440001c4130201c81c1c01000700d6020070f10b244036803a802e1240004444551804402d17030004510014500c10169000342c0711000071002900500250008010324201c482d2260703c030108210302040301f504481c3c0078890502c102c50075a0340001e000e50480ea01326000901549950074142c01030000003202034480405e00c4144404030758580d001c08100c035001e0f038810a101605600541c00c0e131016100d1402100001d2004a122280e0b40c264581513500c14100050318002083c2c4450510450325030420100780d03031b1400c014080c14280103044030354080403074030410040282c2d070 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 91083444 1250 91082194 91082221
    0x601050303041e050303030c07021503010b030a0f09050a0c06030606030e0307020616061109040b04020a1205090304090906200a0c081c0203090a0201020c040212040f0302011118010e010503 83
    0xa901d504440c0f00b80110342c1a9450340801c005090080c0c180c035980c4c42d1540d00c6c10101c1d84210012070240c902c0000c003140000b88942980c2c160dc5d007440e6401d2854a802c12240701805805c10081101503a031007005000510805c500302500388140d280064440c0b84c03007000703800c0f50b025a03c170900389420403081d9084070401000702c40e100c60b4115403031500d901c01c65500d000341541d401d1008081624000c0070034039524490300a403074051800c075010300c02d0660610034842640520041380012400c0c03252464070600c5160031880d800030849040b6801e1683c2c5000b400c00b03603030030203038250780003980e4800c61800c08050640005005e10020307005071170806808002003c0035141c201c0030f01700c2d0343c3c0070400510314048518503120304003091105641341e042c07818840c2d45400185600301d002d8490f01c41612610b041c036000f511071245501942c0c26842c0d070359440342c0018140c4004102e045544c0c4691520701850014084c0407140d40c0315070210140d9807000005001c5401440c8142c2c1804010300c100316442c8860300 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 91084694 1250 91083444 91083449
    0x20f06070219140f070b0d0b010e01051801030b040c0302030a0b09010602031b01060f0e0a06050a080c0402180316151404090f0902030d1205061906080c0403050105040c060f02060105030304 83
    0x1000c80ea110f1241c940c909180d8030b82a094014041c3d0a80001c440b0f6211000d031582005500d403c10603116803200641ea420303c000200d5000c624248280041d200c2d10020443c0c001d04103043c003082c2d03010400002130031980b00104401c0800c1d80842405461a407503c5900081401030b101c0d041c507541455006136076400b5208081d40920180314480f0700d107c100390020b20060007000b4080c404c8940702c01490700103000c215400d078407032803402400040515013140040203c40c02000500102540e10317041c000a076005403040d0000300e00140361865107031070812403000400b117a4801e005500c1c4c1001c0f2a209120382c21070706401041004034075180601c03040030803581102c000440029244688125050140c4496034001e5418040c0e0001c490a0341c1d04086c0441035007007406820450341d40c80a0400ca00d00402041d540003c845120f400d0106501a80c0800e81101640808600301603aa03a20f10742520411101240c00c114582c1041150603005100e12049500e2400600040d44c14403001c41d603640900e1 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 91085944 1250 91084694 91084703
    0xc05100501051c03020a15020301090b01021615020304050a0b0c0d0203030f0f0603150a0e0706031b0e0d05030301030507030201260f1b0408012004060212030406060b0307020f06070219 81
    0x3c10001c1014002c01104c1001d6500c5080d00c044ca4000c01c0010000790002d00c1030181450410400400c1980b001c94001c2c1d1084246800001e41c6052005c41c44800e56045c8030081944030800c00810a0341c1c1b643c44042c0240449581582c0c3c900810068505080300341c81503900355481402403041581211001551000300c0f5031405503940d903880c002a20f001242d084004101b40381d40288603412402d504203400d4541c0c2c05c002c07100710665540c022400c480c00050305111341c00d0302480141400348680301e00c0c0a1040b0007082440082c4654490703d09541c020b900031603840d80091010421035800c045140c3d200d6902ca10032802120b214680700440450042034070700600710310707000909500c080c0704402c1b56505250081d02d840780e40f1101d84600804040b4185040880000c0320718011103e46801c43e41521026030203802c0110098040038001d401c09842190300c0e50710f0791008103186140b0f4001d584103c002c0c0c0e004040d0184c00d04280b42c20103c2c0500b0360000c6410840c00072511f014003040c440011a0700 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 91087194 1250 91085944 91085989
    0x902180405091b0a060e040b0402040914180c03100209060f0f0406030f1b030506121501030b0a1e020319050403050a08010509060a06110c0405040b010602070b090a030320010c0c0510050105 83
    0x14235000030700030303c165001006400d03e4800340c040c01e01c11002138588200d201d181440007030724050803400d9a52010000c40c59242e80108071610481d0029009018900805080303e400c2c80b01901040c0182e0300038041f48074030b0820214040002641c07501950315050b41c0c6100800000603800e55070340a410701e00c01c0c0c0005241d00c0d840418200c1c3c848881d80c859412084c0f0550791496854000007180103401e202c241c4c0d51399860720100380c000b1b07aa40b29071981450840f2000320000448914034001c2d4000410300c40800b4030805d0382c01d0f4424a0740c090180714078829036800b50344400c844400340030701806070440c500035450384003044102d498924907034080d190b10381044040c40d60310203040d516148150145581050400c0240400c200606100d207041e55130b1a026184105d4442410008070b001d902c1c4410707400b81807948208003003801a1a88550035a0a00301c1040000c9022182e40c00d542d03584002c000011448a50207050117410b00801d01194100c407030a1281d54506000104038900b850407248020b50b8 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 91088444 1250 91087194 91087211
    0x30302071106040801060e0c0a02030301030b070909020d1409011a0402161202070302030f060603061803070b071d0105040503030304080f040305060f0402040b12070902180405091b0a060e04 83
    0x20081071845081c01c000703100556554035628810b010745040c5c440c1e510091110383c0420500c0400360151804480591b0003542543e18503111100d003010080c20300d406104002d00c1c045005d400c3e9000130410b0302500007021800c42d180480542c41120020300705c034203591506400460084902c1c40c10426203404170341c0540c48107000003902912070074654009140b0306503c0040d41b202c0b03401195141c1100d0007182582c1c03c2d0104d00350015101c01c4100d07009a8590402c20014442200d2049030003600311b80d40c2c0441e030a00915540c1e002e00b103602594154003107070301d840744640000340400c0180c82ea04020f1034854103051610000c40e50301e000c06071000300004000700310000c10280d10002d80f4011600441102d5030790820420004130148182d4050303000d5400c101c07015010382003059a010300e00146000078140140342c540d41100a401119403030308441d1080d40212000d43c2e5a0042c2070040c0c4044029021406c03854844840c82c08841000500403d6500c00030044c05070444030721980c40d0320550780070601a1 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 91089694 1250 91088444 91088453
    0x17030601030b12010905010605190513020c010905070810020a090b0c031c06060e0d0308061201180b2e0306020c0a0807031710080d180e131a04080703030207 69
    0x41d05402e0150080e6451103418803021054210b440140c0c040c4d0000c110302e5484109019402080102c0200e006500071010041810101481c0800910301035005041c1000040c03190700390340403c2c0c001d5509500961041c0100c41c424450686500101c2c0800c61807c0c1c0e050342c000e403240c3d142d482040400440401d4503014194180122003203000710480d8014041c0d2181e0003140240317110700800000840d5844500308a0400d40c185504a54064807880504d544407000c00c8560721001900e4203040d5203424803450400b0380381716188001c1c0d00c580928681840c0100c100345a00280700e0901d50054420103000c1200101d03840074805494000e5009a511600c054030781d494201140c03002010984001390711410316500c00c08200e084503c80303c0006c06030f112880340e494040018014049a50405803a1086442c09400c8002c101d1051700100c0e000140e481d001e00a0420007242c10f902403c80069090080284019083c179061044040e04425810207440300212405140c00003000d1650003d140000d00 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 91090944 1250 91089694 91089701
    0x204181409211902160803161b03080a0507030e06070c03030c033b0307050306011404140901090203150f040f030e0a0f062c062a010207110d1703060103 67
    0x1281446946000004400f4020340e9594858a205100310001c2c0c00800d0300716006c804c880e0648550a40307025204810789941006452070100c1c1085c10810480020000e02e041000d0b090109413070301c441d91a081c0307509010304a0038040301e070244203420070402c500c0082c000380d0311a01074035003500d8041980d510b81c0c501035032055211005502c000704642c2d91a00080300ca41442001d4040818061001800e00c505065448001c1e004056042d008203005202c29400e800603480e0340c0c8070060000c50300d80544054900c089800352040d000e1030b5161000d980942c20100035005403000c0b1141006010b203802d00f0009001840038100400c0340070300c0b807460418988100b4982620003070007010071001e25550520803040e00340c4c41c814800802c52002c0700501c50061000483c00b1028101d140380c810010400030071030268020206001d484201c1001800100c13940000001d01020b80000103075205810b0600035030b8103c00541051246500c01260000100682c00b03405040400820356520b07600c802005070040e = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 91092194 1250 91090944 91090957
    0x18030f0302150103050a021804052116051011041401210c08040b0c0a05030604020702040603050601060914091e040507120c030b0105010305010b0f09040f020418140921 74
    0x128210b40000c0180800400c4410400e44201c0c0c0000c410240342050a141038001c0f100549582c010044000601200c51910b02c04c1a22007146207242807070544480e00003110040c0140d80e650301004030012246003603c80d117818012000c1030f880c1400e1400a1750030b001c0c07c621207110f04010f244241071f803030071032141c103800300404841e00140716903204500300411501080301c05a52000603240400c01c1c40440200300d501107440d0f9503445245960f10410300c4041d500c0080d003245c2040c1e5822000010405c2032100901a041550300c504441e07140c070002030070240007c02c4003803042c1030500038002c08a4011000940b52000d07151469005e80d02ca00380b00e420700405500c985525121101d017601005010320000050368030030703d503c8000340d888400440848da42405011510300b401c0084030b9031010b01c10060301000e1002040841e05001d00e6207103c050780c1169100301940c000800122406601d14060f5054022051008042518042c2210340d034031105102d078034501c6407c868200300d1070620170b03044810 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 91093444 1250 91092194 91092223
    0x610030b15091f02060708070503070e091806010b04030303060e060603060d0f0818041d030304030818190b060117010506070501290907020d050304121803060b010f18030f0302 77
    0x8410030f1040001c2c0d1031310b104559800c0011980f0b40018007042c010010382c1e001c0d5065503203d142d480b902c4020b11100f0304000d0100c0560400038404c50548060030403004d406030050795092503c81c3d00c0d40ca40502640c00c9a007048607007070b011380f04100c0aa2180c905580d40070710102c48640d030b080102d08108401025290028110235800100710004004052001da40e01070705070340030801c1100103448c00d0100d0442e015800f007160010400315000c0f0740724202594004c0340c1c21002880380040120454034010041c020200304071146c03031806060005041c0800c1c1e0145003801d040c075280d5045c0840e400c3c3d41205000d05481290080b444000b40300d030951081c9103507400306d4030103041101740082421340e181c1445810b41c450706080d400541554804901718801d00d80d1030f1542c17411a103442ea10740b60000c2c2c46450748002c100c1d03498000c4107840c0d80301300207400035406410002a40c03850b5000046c2400d00403207030340c0240081d8200c01c4d804070302c14046980441e0340014000c14192400d18007241480c0040b8000407 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 91094694 1250 91093444 91093489
    0xa1706060f010c0f24060302030d030c05130f230d02011103040e0a020c011805060601050901110a0309080d0509060f1806040f0906120503090d1b09050610030b1509 72
    0x8104090780318171500260380c034015030003883e03480d2003000203803211404025019001101041610781c000c1c0c212420081c0d82d400c0160520030340c2644404440e00944c420402d004100c0c100300081503d01410400c078541144000001e48103d002051031450581c5009040000134201c2d0320b070380c03001481568041d01400603004214180700301c88002035080014003500d03039482c20b40c0b080854440c0c898039450b0248e000c4050401651804019141900040002410702100b40c01501c0d00a209101785481140f0940354141001e0403e424a0b2400b0000c800b060b062100c1005a0045a5141e030309407059410548441a039450114a804552201e002c0c52540c01010100d808500d8826080d60352003540c0080d1000c10101e079540d02c89841503469014050300b0fa80041100601a050001080001c42d006051201c0314415001c1c500d01030404580c061006140d42c0d0b81030042928065420380d803004290b103400d00420748141d00007109100c580c5c0002013009000902e110f8591200d481c441640801c2c0398209 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 91095944 1250 91094694 91094723
    0x2040c0908152e080c030601030201021509070306060321110c06030a0e07060f1d0114090a0e0c130b09060f1b01110304020f12060a0911030106140a1706060f010c 71
    0x203418440b900034004e05003d20b69110507507050001d000350403030390160b0040c080b003a801c0c43c5d441c00c5034401400c414442e00a80c0408400308005000d220000c41c840d9a00303144080300901d907045104001148030381049088000c458001e030f0000340d00c0c4507c24085900359079035111604640010444a0b88446290190a000203015a0440e9030a1303407480c102e0b200c4c2520014070302400c0030b40803544085e943c0400c0b45a48003514482903400035001015014025107000768480c216840c400c0d10454681c2c00300c07400002c1072044010720b03121010007031500c440d03218280011400003c81c1030080c1d54010306403500100b6440609041c1e4104062095a000002c01c9282555500c008140e40101c0c0c00346d016010b28044c0f2101414800c04403040011b5482c094402511b5a01c82103001e001000000c0d103104501810380b000550b020302c151350040140c013245800e41e8091000f4080110490350144296820b42442000c960b0340100e41c080c0d010340c045403d900052560401070303500c0040d081010f08080760000c2c04 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 91097194 1250 91095944 91096021
    0xb06040f14040f020307060302130303030c0e0312130506070506040803090a08041d2203180306020d0f0c020a0308040f031e030506030c100e0607081207020303010302040c090815 78
    0x60383c1100d0300035410344031203948942e0f040e0306031302c558081105290040801000400d12991040d2840700c201c0ca4103042c11040640003918120030720700c50003c3c090340090000040c1190030300f5a0000c0206a40942c01c044e6280c0700c1a03220a4020000fa00300c810000001d2801b40007800750109080d807000c40140c540380c607140102c80b4400c000aa10b8403940c480000700d05d0215041d140302040c00398500140f051800d10766400c450b0740090407426031149510301e001100050490010f02145662642c0028201e00500f0301c1006481d0704e04482c40941d00808400c1000c00c0d03102c240c140d4081e03008040c0b0615464140750031038500e4036010050060003480816030140c01d9041e04454024001181183c40741c88402003007006808004592fa40810008201041d441c200311001c0c010042c06446c885080080303602640c00001303421100b03500144c100000600462400d44500c00142a0501d803050400382050112540c40541201040b0310200000000fa8a803545108803000700740d5181070380f400004484c2c031 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 91098444 1250 91097194 91097213
    0x303011a1605031c050103110103090c05040221220609020a030812160801180e030408010e0a030306090911060c0c0307060e0a0509070918020408060112030e030a0b06040f1404 77
    0x7800380c040000064800389540c4d80500d03030590381c11810000120300c001005400420b544003044900d04242e81c000259569148050702c02c07030421106024400114400ba59000003000700ba00750401c4e50111040d524213210000d046005900c0100024840c40a00000d030645409904c0140b01e080c0001c0c03512494180d041100b402012907162072103074518201c00549514800340160070901420030006044012180c000011060084042e645846d4503001c0f03203402d568000104a042d90320500c01507041540c90300c90b8000a200616041000d000f203540c03080448020701203201e201e100d010a400c2c282c10400c1c0204520b0320070041c105d819083d910301024112104268809109d40b8900e1000203150804020301c0d40724100c0d5540d500425818210503440c540340c010300c8192886d6003484080b50554003008180d001c2c02c501100f418488016180007031044084540150082c1c00c10300341e2400180846880a4200408a074046589a8003468605c020041c038210600341031100410b10084c440d01e80e2 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 91099694 1250 91098444 91098457
    0xc0a0b04031223060f010309080a0507150b01020d050306040b0405040c14010e0f01030c020703050d080117010905070b03060f150307020c18190e03030f070306050d0201020303011a160503 82
    0x19002d00203684000c5100402401d21442e010912452030002844ca00c1c0509401009043c1410006442561502c070044560010340510010900001d0002d00f408206a402c04620303800f001705100e840329050000b501d070f01ea0030140f44248074000c0045019a99260040101d609015104103e10303d41414900042101d610074061054100103c520955100381540c511405003e0100368190495100440080c924801020110b0052043c0400054010301401e1348414040e0303541c89555040c445d030401201680c0c0e160800e20f82c500704560f000903101080f854100c4070203655607074403035880301d0201d00003c0701c0d0b0701040d43c082c08000311442c03801310f284003a501400469003141e80d402900c0701440f22009840c2c8040c141000c21100081034a80001c0c1c0000000a441d0b0012420b407080070b410381d01c1c5030000c1c1c07030f0760030f21008000800c18800e03411312542009080c00c4170605650034040d00040d44a20060054030380281110a13050303220a080307000c84519400d00c20400700e0080081c00c01039103036049007 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 91100944 1250 91099694 91099727
    0x31903030b0114040b0a03230702010515100818070602150106081e06010c0b0f0402030f01060b0412021504030510060807031227120b0901050708010b0c0a0b0403 71
    0x9450340450b544030f001d04800c0d01d100c240c1c03075924150a000002d40c10b500a40640b004142d140c145d10404400100e0400b0002c2201030921440327403d02010107429640010020304450808580c07600d1255107400d10312110302c040b81094841c1d034503410949070304c4080c0e80b0390705903041c0300d00b00d00002c41581c0010804208408103064840e03070f980728501140d40100c1900c0b0300c4e06e4960201086c0724101c1c800d8070181e8101c41c050401001c00b5038560303258003142401b110303d81740541140c0100003e40c00c061061041a080520003003000d0760400480c40c080e8002d40c000e03d403034064a811481d00315202d07511500304161405001544803030352450443d42d80c4000c0c841e080c1c050380c207048000451031400140b040c103803075006010010010f5803a004440b480803614440440ca51400303c5601031220340c1c04c100018008011003890f03001482d082c0100b6a11000d0181441c90b8581420000480d510009150554400b00d00e0207035036000b80d0078038900c1e1081c2142c0c0034009220f284140810950408030000c0c005141 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 91102194 1250 91100944 91100951
    0xa0905030105070203040605160b01030c030203100b060a030b0a03140304060f03090210030c050d110a030b0316030f0212030a031a01080402030d1803080c030a0201150f030b04060b03190303 83
    0x851060609941c000d9406402580c070900050102d81d000358068000c4094a400800f180c0e8810b454000b00ea000a920540344894411010300543c20103112800400160080c107110541400d80414224030561762014105640d031408000107686508209000b15003228144900c07034155020240c5030b41c00381c032803000411403281e40c3c0401c0034004c1c050a92280e80040641c0d050190a15081d4042d210704034000c8100601005032001070402846241c1601d15a1650f40e5100d500c683c0c0b018045500c030640c118425440301684107440200d907180b14003070307c0e40035100407807402243c404240440107114070a607841c007001c102c00e01542e42c9075100c04110100c0145a8074a107010400644c0c1ca4402a41e0280d0540c000155440c000307809000707500c0f44d02c4d000e1418007ca20b6580e40b15124180c03c0000008400e4000007080a5543e909004007003c1004440030300c40c03283d00d04400001041660320004004032202d400140910040d0f41c005201c4081c043c00380c588240c2101a078075094030070448110042880c = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 91103444 1250 91102194 91102199
    0x9080f01020903150f150d140c0102010524120f06010312020705100e040e16060509130c0c0308150d08030a2007080702120102040e04140102070803040204021812030a09 74
    0x4804c4001070040303481800103034440d1201d001040c1c00010020200e40c200748002488000210a40004001e603082c0c1c5c00a0905024420002401e5800c007620031041a04804010103002d041c0b850a07402001d01181c0000c08003c14545031800e110628134101c902e401000d0002040c440c4041e03a03011501880d500303840580751a8403c1010014a05d486000000c1e810110101d40c0d0401d40d000354081c102d102e040300c4400c140000c9030320b01d16459802003400510041407803581410840c400d82e4040604a20510903c420414003d107540915000038003080403d0020407102411071080700291031020700640c02001e11401d00e200070340e0050b0360342800c09140200100c0600300c2118004004000036a0180c98203416407a0860f954100310300c142d0340aa40b03d140d90703000d0107003480200010503d418854415103800e0400d003218002d403c81d40f14180e40100700c044001a0f80c001201e0f40158121001a1181000c5c140003890041030986030b40c00c0b8100046680301018000041d1500507503e990b001e0f4940d4 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 91104694 1250 91103444 91103473
    0x306030c0d05160f08071a03040303090c0e01060906031b020c090411040c0807020d030905070b1b030406090f0608090d11030702040911040b0a05090f040311010207061a03161509080f01020903 84
    0x2141e0303c050f9615050300f4030102700000d00c2500b04880c1f041c0281e101100881d150888018456001e0f4041004030320450410018075416015440001d8030b0343c1085289800f54590181d220031014800b24400d4032400c0002d07040210912102490a80144c0f040100d10500000542480415107015002d4403911902c4c2a00902c01e0082c40e05a60740007000c2c2010510b00300e8950450f8106035a0480d40305a5442101c44418041001c1c4c0000e044540d20070110a18050918071001c1035500103a0801c8907403030401c403032030800041d00b210848152500c41d41c0da10410003403d00b14018003800a604c0350400e0710b1003040c0000c1d140e40c940326003821101005404905010440c40216070300c0381503080340f06540080c03411240c0100d8998001d000e41040040083e00701049401c990024508031030340c0e60f0396070076032000c908040c084a24180060b4002d10010144561000030704e43e4610400080c4030384044103c0207188510001401080300400701c820401621f8200d03800b035040f0003c03c1c0c0c0248500c843c40c40e4000d = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 91105944 1250 91104694 91104719
    0x250f060609020c070b250b0103020f06040b1c020705010903120510030f0212071e060906030b0609190b0f04090e0712061a06070b0f0603030306030c0d05160f0807 71
    0x3101848020030402d4588000c0d107a45d034105038a8500307008900880411020568495021880e2081300c900c1d003158110320410101c0c40340350304824080e45040c013080c80440940c500316001c1c80f54403010042080f8014030800c0181c030840070020304550800100b0300403d600242d0442c001d01e5000c074140001d0340c9555440c00040000d204c080c1003428042c410802600780100c83c00914060328094407801620f500003280c01819140c4042044080b401d81080306682c0000f88001034181450240805e8140c4000038509002d400802e51042808603031100c030203521114600e00900707554142c40c1e11a03040004111035070300300b03208291131203003171400ca217904540219840054030440c0d1520740c1c00c00030544801c2c1c000c0941814840d5011100c01c12800c413907032200088c003003180c400c16942c178562400040404642002801d02030107a4800d00622001e07903008114001b91303a001340e070804040403050070030328070303041c4001c6090528810f0000082070b041004800503041e60341e0b00088406480d680c166240c1030 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 91107194 1250 91105944 91105957
    0x60209040b120a0f0812010f0e0901331e210506010314031c05090c0103050106051b0c060301090207051c0c020618040507090504060e0405070b250f06060902 69
    0x940e0041c0c03d0000c0014400034035080b41e54054103016044c00951242040305404c02c0c0c000b0400107070150000c0044c0904a01084d0340500104024069581d4101308034070200141081c1000c5a03100100c4007410080443c10300008201c40304280701c0704400480c8a4401108500403d0382c0b1034046403240411180710421025682e5011004001c80da1868540604000001183c0045804204101031400220813140401e51f040010001031a0400d00107039450050140001410b03d81800d0040000c0c3e60020b0075607040e00040f03618030500c405280b20380c904041d8003060b566807000c00400041071528541d0302a205151003402241c440c14000403440310203604145002c1c002542001295005081c4a406021082403142460313542441c030800040541d2007c0328079500098030003208220920b440d02619000380040d010103215402c1a4071203948490f818000d44845c11000101c120903040110030b50500000c44201d4541d5013411460040c54004280c031056a1480c01c001c07004c540342c8814800c0724072 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 91108444 1250 91107194 91107229
    0x60f0414150406180b0a2304050115020703140f0a150e0619021c0504030e03060703020703050702101e080906060603130f05010209040f0e07082422060209040b 70
    0x11000c2e4440c051320080d00040c86201c0d084409244002818034507c282c0c0d0071880d202d03500803d070340c1b18880140b01c00c907003050340024000c1c1c2d100e20784400d6440d00800c20703400390380d00042c050881041d20f21100d46407044203c180c0d15144078240c048010b00000705404044844c8524040c0240c4031701100155540f82c0940b02c1080148061405c0b9011950039401000021010310001c1030401d82e210f22030b001c46004417400d03004a00b82002001d400d00d02441116840801400c086050902c2c0c4d450040c02d0340100c0c00003e008142c00003102c0d81807805040403690140703c0d485040104506540c00814410068629003001d2141c0000701c0c038286807a10960348a125000350b012043c1081d502c0304241540900302c147c6180d54201704403480c40e00d0b0340c00340883d4100c072518003080188054691500d000a507610401264110000e404488100c0300819010903411a02d101c00707540302c0b41c080280030507d110200c0e1041080f0400da0040100903000b8017411030381144c0801036090010140880213080d203000a0 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 91109694 1250 91108444 91108469
    0x209030a0b0604051005010f0f1701080a02130c05040506030604020c0106080a1b0510030504060b0603070e0102070504020406080412020c0301021303290a0c0903020a0902040e1008060609060f0414150406 89
    0x118000d100b00d5010301d62084a250458102803800000c020040ac00c0c0c01000244e00102d141078154108034803a60602d241401080104032046840200180a980034081c8142c00000100341640d4958050700c0d06180c040c80204103080d690400141d484c070341c060040300e85580351841490b03102000c0020104440020348205200801c0c00300807001031030000c1088504030381d11880b41550340c603488083c0d486040107844640c2d00745003180c006850304159602c501c0c42180100000e00903c4c0c0c0c03040031160403a0344840d90402000400109900b04450241c8054042d840407880c0138813158400b0100c01280c1c0100a411041c3c14800414a810301e1040c001c0701c840b10050000c02d2001496510260030168189010001c00e516640010380082982e4003015101d50045414800010014203803504454400d0900745024a1301d00d400f41c41c0e003c010001032041c03003d00300003010341c0c07281c42c1110100c031030003841005800c103000c3d02c40c20802030a550008110b5080b204003071242c00c003031040300c047c4c1d20b8051499 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 91110944 1250 91109694 91109717
    0x7030201080c13090b042003091018030309020102030705010c030f0507050a08041b0f0b0a020c060a090b0a03061d2706060f0f0303040e010905070309080a030507030209030a0b060405100501 83
    0x1409082055186030704a9540c00d09051040c01080d070034070341440d00280e82523a034200603080510b80391800c441e42071264034002510810a003400429042103034541408203841c01c09000507030039801015006401d0703500b8407184040280d456404241c03000300c0d110b800c10080c0c440f044200ca46024404821010549a0b0042004583d281e403c604040c0801c072103038a1440c2e25282c00706104c01c515400f8540c2d070740c000700e42d4038001501400780407080b8100740c61641c10f2103010507005295404621600d80a140300142d0004007034482d410400281c4108501d001c804c2c181d4600c50b0060000844e49207112024040c940c00d58942401055104980700030010031a0792120410400002100b8018a5101250f5843c2c101d594900b803014000602e001c52a483c820743c580410942501c04c01003e80c010149080c50400000e1143c4040d074007549881c0c07400180c0b030b9440c2d82080d0002e1040e180705030391610805082104020303800d004d05214000030340f0180080c1d02c4494409040c1c1d004d5014a601182c03262010 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 91112194 1250 91110944 91110959
    0x6080f0f18100f0c03090503220909050d020c092802070218070206160504090f090507090605190f0e0417070605010e10030510020702030f0102040807030201080c13 72
    0xc140c10202000081141044a141c45480c246069144002c019141c00821840c091540b1400e4540165401c080c440029540c0c4c1d02500c1e8071859000e15140ba003a00399121000302210800e501401901d0010071448282d0300340309544014130b0140c54018032800744400e42c80c2c20f040b4050745c0101c83c0000100c1104ca0749101c02265030525240280e02c1075170a01540000d0383c2d0300d81003044040300c510210003207400d050f5402401d00700000c0ca400000714035030103020700301c0e41e10904940440320703207000c00260050a498814007902c00030384050f181d40f24100001c942056903a00c05000c44004480c2c1203200c1204003000001401d4503c6802c1601011090030041800c1c1c40030310a501a224002d80b4642414074911120203070084e000a8850a43d11001808200c03000c03d1401d4000c0d0545131802c003550701d0350b92001d0b03661404c04000481c4540101d00e00e4210b4604100e290300d82c5100000039505c0d0354032140c42e280e407030406200a9001480180100c5d8112010710111641010100d0010b030300c45052028 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 91113444 1250 91112194 91112221
    0x3080f1e01060f36080705030a330f0b01020708030405090403260115020c03060117030f03150102120705030306040207030e0402030a0902010806030d0206061903080a0305010f06080f 80
    0x9002084c488000540c0110340c11300d6000110201960006008100c111440301854900a0700b042c8001c0d4003040c0140559500029030300d200e1544200d0b20503c58420409100c42c416019190300f82d441c00ca03482e0490420113540064540321140700302005001643c1c00120b81d01c003502e2007104030301d82041202348030324140115099071203401b90800e20076100e0b1209124081c0c80380002800c4072141c00304014001614601c0e514034010301540700600d5403001e0100003c0c1c039200d042c4230b90f5080a2000c180d0f028009024010340d00096414000c0381e489180c41003512040a070070003240b500602514a8406840d007d0000382d8013680d0300500150309641e42c0505000c000c2d8886401070b0140710412240024907030303c40c0000e611440c444480842c15082900c00507040320009400103100740c0110b0401c000c81a800101c0542c041d00c11103900a503840c2c2d51b0000d074880e64903a00090204500000c15014503601070300090704840103810000600c40e44d0300003c9a0380700d07060781c1589030354081c0e0000c620404401c00 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 91114694 1250 91113444 91113467
    0xe01030b0703110409020d052d04170a030506030c090c03072d02010b040b04050903070f02061207020d022e0b18090a0b06030703030807050f040806010303080f1e0106 73
    0x340000d2451a50600043c0d642141e48100c440540000b00d40f542c0c018940500ca80100300c0d100341800d001c54105c02d2220880003881c404108a40b86000501448a80e001c020041c03038441d039420381e5810580308010301030841140c5d824000d2288c94a0070442c0e0400c09100c5204070b0304440c086047d038945c0039044503c0c859440a141c2c0c0301a800000400d03100700c28070800e90230200d5400000358120104107000980350a01d01c3c180c842e915100801a80c2d40010080714070643d0701840030504000244005045400750b08050964030b68240100040c8540003d518403072811941c00b00d5854131003507102c19450030503001c0130b4a0b10b081d120781103488084494002407c0c103180148541c0441108107076107070088034201c0d11750601398041107144080c031500b00c200f5074001c0c00682c00790250b2419034502810b042806011001088000507022425182c04015900a00700b41c00035030f4000d59490134002c001201c10b8038204040082140400c00c074041c1070802105105c40804800d513180e00e0030304144c9070b030240c12 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 91115944 1250 91114694 91114697
    0xe07020d2303010e0901390504090e071703030606091005090301090c06090815010e040201090b130e060607020f06030612030f0d060b070305180f040905150702070e01030b07 76
    0x181c1007030803025600014602034440c803010003403140380102049080d95542c800c010b45d2003081a00d84180101f50401c584540882d0f10b040083c0c04440703134804c0780c50703100c2c80e8803900311685480c80c41003d010020800000300c580307803448001c4004052214549a1205417001a4060b408100f498802e09002100708602a500c1c20f0103400c2c82c840c01c0200c7d0940d500d02c9001c42e210b070030040084c0726658004040e14060010300000303002140c41c008a80c1400700040c0100d02c6598034100000741168892840c2c0740c060041507080945031005403100d094a96424018071403801c02890004106050101c10795036001c0e001845210325400341e1003800329690015140da0b4105c02818901b0307044000c01c0004018a01111503850b503921503d000071011030300181c12002030f401e802c000e0f900110381d00c40203031001e10400d078425031640072021000804490a0b9950a6001420000e244080c4000070a821030000300c0c04120080d02c2c3e581040890700e0b00000d00684244403100c6c0c0042c008103002110b2280e020b10b99 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 91117194 1250 91115944 91115987
    0x10e010e040819180b04032409020a0303020303010f060512040f060b0a0305061008150f060109030204110a17070f030207050a0f0c06020d02011a01050a0e041a0a0e07020d 75
    0x70442c1061100030a42c90001080944c041c4e00100c0801013484001094001003541c14641165112105125a2044a0f60050420f4481d9402c2030444d407003441c12907070091600146590b07030700d0080e4483d0000d04c95061203c1c10032800007031482c042d0b000c5400318400912a2f00685e42c1e290784519814481c00c0c400c1c0c0e4030343ea031440024450349481d0030710700c003075400760707004000b80c1c40d01440101da0581035402072044c5820488030707004100e920700310b41c5400080c1d421900c5495918080100c82c896119400a540641414115004c0002800003882030303161595403c0c01c6410804146003071160140c40020008400e8441c00c0c00c190b00c071780e01400296114070b0645110480c41e440e05a000704c0042d409403403000c81840c0c00c0190f00d80400c00002c41c0465030000340820707141a1030b0b804e00300003008583c50600100045200c180e510542203604000c0700201304000c003820144d600311900c00c0c0c20b100d09004d40c0c0e0000c804102011002c811510900c3c00754000e20000c1c0c0c442c1d00c02c4400001085289421044 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 91118444 1250 91117194 91117207
    0xa03200603010b040509160c0f03020c09010b0a031803092d0902040503161409040201020f0106081b04060b0a11031c02090f04200a1106010306020a0801060206010e010e0408 76
    0xe03400001d5000700f1801c0e01043e16036040004000421901a1020246044803550040c0603900803030a0060b40d60012a50720004402c0d040980c03c9c42d50b041ca000d584011040008a80b8510b024050321202e40b05e5502001900101c14110300c0440541102030081031401da010840d200b8401010000b17201e25291003d244860341014101038007698100c450810340110b018050f508081000780d00440105403041c80c05450b01403030700e0201c0101c445460040d03003020001825a4004c200c0ba031112000a8000c0007202d42c0c480c011a1604001d03440e409907240e08501c801c3c0c0d94a018040c06099451445d80145009a00c08003500c0294403281641c206000c1131101c003166102c215150905584208030140c2c1d9400404108031ba00001081411b209902e03100464004ca00280085d8611480d4886200d550384200c0006480030340c022400000d140c865000080204240c3e41c01512050000d40c2301c0144691b20380304140d0300d84800740614500c04050000400040360304030b000079000360003044010720702138 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 91119694 1250 91118444 91118449
    0x40b0f090304090e061608011503020702010e0603090d020c040c050414010c15090b0112080909040c150909060801060e0c13260d0f0c060504060e030a0c11060403020a0320 75
    0x119070149903403054029104200030700491b0f50a0184840107850852869030401e06020f24441052006000305640824140211b90042c002200ba03400000c0c0300303e45a18080f81c00303582d242d00d4594210014080c41c88615410f040030b01600c0301c1c3c24610748032141090304003544254a0030440c104a03040000241ca084040340149120844070f1068001c0440d02c103141381082040e04006070b03c60703c45060f020035450045a200810b81d1060601154101a00d0b00c403800c02c40700c000741d03d40003c0c64456070345080034006504400b095044801c042418400140e517072225500b01c0d925031040f1203000324400d0004411002c080d000b81080c062204840300b0315512039000001c0c0501680c080000c0030900d5400c05030303510007081954000d0030285405e403460845908000d041a91075003000f0030003621070b00030500300b1400740c001d50f131031220001c01c5a0b01d4104005004188a1141c1001d40d551031000142c140d290070701d20100c8060302d402070314240c1d985142d03a0710340058a41d10b4914001c1c40c1c03520089600c566 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 91120944 1250 91119694 91119701
    0x10b100315270507090f06090308030c07230708060a050412080c04090203070e120c0f0d020d020904060903120c0e061b07031b050105180907091e140306040b0f09030409 74
    0x4d4155542d0a080c0e14141000f00d4424042900701344107100716100108000760b150400c8075444400c0c18407c80c4c91316894640340f0004001040e0f0030409460040d150050140d002a035541143c041c0000c90b0b100351604c0b4001c400b1100103840240501e072000c01081c186034001c2c02c4540c0c024004070f988034949980d41002000701d03007041d0768580000b81c0845c541c490510341125004c464032407030005001c41c1d012100020759100211943c450007450007040090070f55546000070b591039078001d041a0a10b2510f031804c0ba004002403002100483e80300c00702d040341070b840f81c0315448101c19151038030038028042100708182500141c01c0284501d1405046072903145050040c0b4005521030040424080403010000002c01201d03001641000424003084980080f0209410902c68090312003480503103540c42c04031918411b94000d4903510340d82c6000d05c0b07040c10405a6110850320304032003c44102c0040c408241c2c40e403406480c06842d690001000c0f03413245940d0f40710b0301e800815503011246003d40d12043d20050303 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 91122194 1250 91120944 91120951
    0xc01020d0903080108030a02101509050a0f0501080303040b01050d06090618020307270209030106050d0b091204030b180f0f011a0306070c030507020402090d05010b1003152705 77
    0xc15407640801c00c201500004464050f204e6500554104021114003e5032160104000c107000c9072245c0c401c1c5820301030318603501c0191441000904c55481c00368802c10280250649804049140c40c0c000645c0c40c1000c41641d02455000301c1c141c030140d2a00c0704003c05a000c02009851b85a9139502c0c0b140060407a1050482882080f0305141d20340102c0d0041504020b841d0344000c0300d106228012100031f2048000301e0f0f00c4a4040309005843d00e42d5070300400d00403c1550041178114800014004c14003081d407c1c0c5c688584901411140300802c880b2003036516001d00e20008014000390b10214114030003c91880920481840490b0790300001380c110b482c41c100203c411900165500d60307800300080d803985001c5244142c1980182114200024024481000c2c004041c2c20001c0115911045580e260102d4440700e00050410440d0046800c01318000c100b049102807241910144620030503020340651910140c070b90300c500b142103280160007200d4001e04000c220814094008a003540b81040c40368500 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 91123444 1250 91122194 91122217
    0x307140423010e01020102030601020a03110717060a1b05030105040b0d0b160206090c0d0f050c1509030d021515010504050415060f090b0f160203070303030524060d0b01050c0102 78
    0x30490740031002610900d0144012411a40104100045641c0000380c40070f805038113140c079001400124400608251603508220854500c551800c603404000294060203001449410041c40003c00d403681c001910031072590000c60402e000402c02ca2605501819a81d54060209202d034103a5030307542000008100c07502d00c0750202140162007459030400010740d000e03150320000c2c96500312070300010f140010b800b02c004240f24201e5030901c0400031b003403007a180100000351588500d00f00c4140b044116410051006000b803151107001c4100510000c2c0d1403042000c0381460751060349a01000b000c02d8460320f41d5080c140301d0704010001d00c0b92114410341885402440402030003a003407050080c5108070940d2450100b008010090240301817003011101c0300e103246100b1603502c408101c4c001e4501034031042d000e980f50240001c00000d143d01600240d115100f03400c1c4040409031a0307810780b4000b242c20b084a540050003071141c0c104022059200c116043c405050140c180b680c0981d885099030711415a100 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 91124694 1250 91123444 91123499
    0x8070918020d061d070308040e06010908061303080703050f04120504031a0115050a050f0304020103061205060129120a090f060c0201051b090d030e0307060503090712050303071404 79
    0x5903600c0031500104e030741584000182504070710307503160312500d40030328000c000040c3c001c00c01282903070707001c1c048050090080c04181c40c620300e804030044203401801103003507000c558480d0001c0c4c00e091080c8103441c49810000040c08860b240c0c4c6e01c5410421100041c06000d00000304000305c04035110074030a50a203601090103050300e6041c004840c90311030401401500b0b01006101c450740403500030041d1403002070b0b9540003584907500c500040340a0142030344074410002a200a20f02481804920342d4140e9039034003245808031244200000000c8006420b202842d502403285000a025801186801884421000c105007445231200501001c10050488815594400e0300200503020f004460740300800c4c403480042e070220000d03000710f54862280d400707100c2d071182000b010405000d10014007074801c0280495403029150000601203500550b50500c84d4441c140000850043c81d00710404950707800405107046898004c401e82e084d0610344042100d11a040c80041031030704070a00c03203c1003c540d050b40013 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 91125944 1250 91124694 91124711
    0x2412070f031502070812090a0804031209080705030c040e03040e09160f0609090e1002031e060d0201090605030c07021309110103060e07110c090108010c0f02030408070918020d06 78
    0x44054442540b610032000d0b00600c07101000c600d004050b41e0302912280c038200c480d03542c0d20540505000f2104801059288003080110501030115404600d0301c1031030f04d0719030005880392040e507aa407442c0c0c49925410f0340454131600242c1043e4211010500d1400100c0c3e04103510380607822030841086400702c0340e076440100c07036640a03400c0b00d1503000140261852030700e03400e0a00800a181c03020030b0241415460b12000e07103130128102040001c0f01c06c84000e034115164182802c182044900d1040b510386406a0b03000130403e0303450400c40080c04164140c60300000d451402c4010360340d5800c020f2405855000920600c805a2030380d5024110082c2a554000b6000038149000402c251900c200c81d8101464000103011004d0007601d9250404094240300100b2580c1c144c41c686440d81d00ea001c10382000c070010000826507415000821000010b8a0344601003500790070480e943e002e20b12460181743e01034602088446090382c0144240d6600c54116055040c81d500420304140350b1040480b0034965400c8407 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 91127194 1250 91125944 91125953
    0x180f110304170a020606120a12050c010e0c060304020d0507030f060501090e0a1101120609141509070804060b010c1b08070b040506180103021210090c05032412070f03 73
    0x7803590381d031000342410741000c000550003541c5d8140140720314041c3c1311100c20340c16a850100a05050b04c0c0c3c0c02008048825101d003002422504050340d00081c2c2d60901c449450301c28030200f015181c00401400d11130555480da000c10140f11ba4410065515010b03900300400400c5811144010350743c0144004107195140800c0d8004a4000a03c0d0b041242c1182c1d80b0349000421102d00a01c150740240781040008030030441d940c2c02080d1540c0a40c6e40c2a15000d07403000b02c180341568052080f04104440c60030b02400c2c106101e81294210340d004002501540041d00089e420760115108000624090100350400d6860300c0c501c40c00246150106030003014104150303003080001c1000762401c90390345410189040045200d502801340d501444658011800506921a45c151a404c800d80ba4445080c0e041401d0298842000f40c0119030400382003561380c80001c0d00441c200d03405a860924440c400b0090750008100e030001003642180d209003800c0c00741c802e200041010001174490681840301051846c42c0c03 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 91128444 1250 91127194 91127213
    0x1b100905060a05010501020c01030e0304050d050a020a0906032301060306020f070c0f05010504091107050307031e0806090402040e0114090d080f070203030105011d1305040317060a180f110304 84
    0xc50b100035080038014130003a6030214506428000070708000c0740488550741e15a0942c0125040307140c00c8032440d42480d083c8000022214043c900a8603180816615909060f069601a0001801e4101985101101001c007800e912110550780000010103e40380e5a440c4266444800f41c540084000708100d0b00340030740d03a00d11400030301c000007500b0b0242c0d00d010000b074001c0c0038500c1003864135503850120300d0500e24200704a40364540e00c00f069903540c42c802c0c50040c01d6aa407503103c18a0140b08100400320f09405070344080e000785401000d500e0155566800c00016200180c0155203d5495940d9066200f242d5280a400b0b102d00c80040c00580d07a60300e00c0100950300041030300c3d034003079041d40a1240c581d03000720840341034800070300c1c0041c000b00c4c0c04004503103c7d40c032000f86070b50044155801c0784002102684018001c80c4281d940c01802e01d4540034140901c09c0c140c42d4194002c08a0008000302a07003842c05140b2440c54a4010588122001a003800ca40054028503c0d4a00010400080040401 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 91129694 1250 91128444 91128451
    0x160215070b16140a020703020909011401090506010c08031905010308190c0c09050c1e12071106270708031b0601030b0c0a200703020307050103021e1b10090506 70
    0x208400400304414000900c100d04041d03c0007504800000c00e035006520038050440a9034020301540c0fa079043c0b88103d81c4c02401e55100400e01d14500c00000720303801646008160003100140e46202c14100d09484e400c60035130020340301185180c000d1080811814650007024020360082c01010b4588030242c10440d10441c1c94941041040000c0812200007181120640156440010009030a40c2c410321020794501c01c0e404c160000c005840d401442c600b518030000c14800d968144158001d0b144c4d80e20035295210005140701c90740e08000b0000710281c80f81070f035007182c6004401b20050040880b2401c5424034800c3d801006154000040040b550440300d2001482207030718000911040d0300d10b840c2d240d01184064800740c00b5141c00280800c1c5248142072249007100c4103450360b00c0c1c0c2e1048455403541d40c149407100f24040c1c080c0c1d4000141c0c3d58024421b44444020005907007041101030004e800c0c0315030040a07202c119000d00c0c981c0c03903241d0030100525602040d8480000805c4945401c21524005004 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 91130944 1250 91129694 91129711
    0x61302030705041e02030a020921070f05031005100504060b030103020301060501050c030a050702060d02160308010803030114120724030e03031005040f0617030912010b0312160215070b 81
    0x44001203584002000420b04d4101d44400140c49450320050301c00640f258205036640101019a0b01c401c0703003d000c5041400c4c81740c1c682290b0f1036680c0d840504410100c58410158913070010380038400c03d1000341e002164842800241d00d030b41d00f5241c0000a04880490300504080c0101000501c1181424880c0102910090811034100281e80300d6541d900e01c43e0310000020000040b607000b0440d00d560040d11741600d040041035480712140f50030040100000c01043c0e0000715880300000c3c03001004400c49040e19001030440814407050070a0004c06440064591064400d01c000042c140b83c5400d19604912802e881c850b100360920013000701a504480780340c61154104106004031000c10001d01c20845409a50110f030703d03d60708402c1d00c010702e03440d40300c0d0407a070242c04211625508080000c000c4c1040443c0c0784000c8011a9008030b00721a068103501d80c0580c440c01000039401d40200c00703000b01d070112242e0001210f8165010811007000c0c001a04407883c004244981005504440c581d400300b02d5 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 91132194 1250 91130944 91130951
    0x1090501061208070f08130e04110409030f0315091505090c0406021b01050c0a061b0c0209070804050307050d03050a0b090601020d080a11031603150f0302010503100806130203070504 80
    0x140d1900b103c1d07071140d1040180916524501041002000e006840100c400703621014091036503002040300212040360202c0310786d01c18004420b001d180911518032035540540d5140c0c104210801c047c0d0003010f6440001c0c2010f03210f54000104038034140241c07030380c02611001c104022407030076040c0440301070042e0200c40300031020300060040d03541c00110019000c0a5807800d4081d0b1500c0350050702c2c148250840f07140300e8001c05403035106001e45500700b02081010f0310148002d01003103610445401d807003140b009602c5124840407604540c0700e0180950002c0c020380a8a241064a9a034140b5080700c208441021031f0311001000000710b5288101c0000c2032003590341507214900702d00001d4a50701c03516502c13010302900344080348010110790300007100c014036581d8045d0380341451420b150202c0c80410300c50000a04003400c2c5c0001034100000740085a414100740511141140c5c0196040e030001480103c25039440200010309400c200800d50140b996500c072860081d105005050a00030580c01150040c0e04 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 91133444 1250 91132194 91132229
    0xc0307060c12080705040305100902030601140a03080306030114070c02030c18071d030d0503010e0603030a05161110050304030f02062202120102041e050a051003020c01060312020109050106 83
    0x1c01d071026003010b00720324100429a0b524081942d4902840d0009030051040d84c000b06200d0840e036004542d1a4004c800302c0d040c41e83c4e140c80d2107031000881c068554000c2104c1e44104000350703200c005107030846001000410050948100c17500d480c1e030304031000b82c0010390821100007541800e010310000b064041c2c2d014036500c80707050302404200710050502010410010581003c0b602c041100301c0d0749030402406c2d0f4280c08a811001081350b0000c4c006c0c5104054041d020407201d03e00042160014021501c3d180d0401100b1140300c410340901810035a024409079407a41070303940d201c004105050503e03403141078a0b4182401d00800c0c0508032042303482503520100038400203000c000c0240c07840e40c14039440501500c01e24804520203c0800e400500e096001040128100d02e11400c160402d00100c2d0003142c00503030319803c206991f0203510407550003444c0641c0d0405102e00c03a4000780002d640300350011810a540343d480c07180750042f15504000507559100a038080120a0046c1001000c840c10050382018 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 91134694 1250 91133444 91133453
    0x310090203070905090402031006150e040231030f0f05011406030c060705010f020a0c02030d030c0e040504060207050a06051e040b0c1b030408011523130f05090c0307060c 75
    0x299001d030030300c99041700000808660301000494040b84140c20103000c4140d0311440c070a61000404402c8010230b01c034034400c4405050034825161a6580703183c55440300901c09241406254030f140950a40c0c0c806c0210100104040c0d01130803510038801c101c0c0c242c4600700c07810800c6c210b51080020703001c000c20754820300c40c10303030b40c00200d184202030102c400c1540c4044500d40140146044d55801d4410381c004100b10390203070380108040b140305000380d040e9504050550740c11000c86980b9500308000c15040c006140946c107066108950040c4620360051421800c3d4440318945512414201c48950f25103040010f8a141d60007201c0c82d11210058900300d5061540d40d04181d808001d1000c280364001154000c810f14099070840c9040c19500c080d81d6555032605043e90190050a070080b10b1000d40000010f002482e56141d101104510f108080b8014588000c1200740045200788070f003e5515546407a003d44802d11030b1b02d024018801c0100fa002100ca028541820a1a4011828000d0f480000340204 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 91135944 1250 91134694 91134707
    0x1030b130c06030e0f0118020f010f050a030504110904060c030e0706021002031e010807050301060609060f031d151608070f030f0912080405120901090e060301020904020708031009020307 82
    0x440071401d0114413480184d0301a0316003079994074405400e40c00c140c1c210500e604000d1a00302443c0c003d40340181034041150044d1600190800440e0004204001561950b4840da014981051103401e8070202071840d40700082d07084109480c113940e22a621138196240c80d8141c405e03c0039864605028154091074103901a407281c501d8510102034580010000710101c0d110030088101c1003002c200840b140d41c44440c140e80c0e40000d4098240a507291113404901c950080706101c088600320345c0e0321210340450349821005402c80504101140c1005440f1711072110091025010b9907a9046c2c00074040d141164824103254004400b61041c481a0b40512800e15409207150884030024140400c1280681e19008020710100358041c100c0240118800c00c402c0d4080c1d01d130742c056030142080382c242000c02c0d1041103c078401d1001007400b14003011400c021a041c4400380640c006401400141044130307080108069a20408088407140030000070441074060003890203001d4410800110b0961808141c042c061 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 91137194 1250 91135944 91135949
    0xc0604150e011416110409050f0f01090b1812032a040f0e100b04060c02030c180703090305120c1b1207020603220506090106060809070e060105070501020a0801030b130c 74
    0x213503031101401e00d0501c9692419070010007400b810030402e102050901548605001442100c14082e000b030364000a50305015802001d0b4010f4a51185925000900c80384c8400309186000680290600303000c526840f0390203140301e505002103100d014881c054401100c45145024200065001d0000f4410349501c0c2c0081c2007a1000d8200b00c6e20030340c403010110300c03066030b80d94080c5c4800c100c0007801040d0320390700c4030394203c5023807083d811a00240e0321501008401015500c4070780501c814980081c038454442e41202100c3d40c02410624075060070b0800d0030964180031914200c11503000101040c059040031115030f25507200c00040d003281088103450107010311031260080d22807070001c000b091806405030000b51703103400601c004041c040c8a5180180c0c5480048890103995440c00f640001c5260258401ea44141c0b1746001600031281402c00040b603900d005020903041003014804100000c20034801030a03c89419101c0465039032561502c03619907000108411052419001100300080b000b0341030005 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 91138444 1250 91137194 91137217
    0xa0b0f01050708030f10080106030c0501081e28090809012703060f060801090b0a0c020f03090910080f070f05011412060102160306091202010b0901031101020c0604150e0114 76
    0x141c03205903002580e080c59400c001f265500e0881c00008018040c03001000f2160280c0303c100403682c682480c0301c0c00c3d0f240a920b07103484c488880005002441c01d443c0f455066501d0101e106016442d03c4c15690450342d044500b2240c1050001d808291507030002300c5503505008880d8503600f082007181d520b1300260018070008015540313400c030028511301c075031304040b014146080003084914845e003001582e2020584003000040d1a00000c0c3c800703a4808204c140000e02e054000711300d403030085814043c140800078508581d00c003500070080341014090009180c0c0740486002008018201030020840c40407035480325041c002d40e8210381041d005ea0305c082c2d1b4080c00294844083c50769031000180d0421103840d16044092905010200c204101540f040c00441e00030322489041503040201030707013212800490381e41c0c4401c085004100113509444410034100040c8150b6a0803403142d404034060341c01c41e070806425620322400d5a03480d55070206142c44052003d00e01446812800e03104400584100141845c = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 91139694 1250 91138444 91138471
    0x905010e030c07031403120f0a0605060f04061b02030111032509050d0507080d03140609060109030b131a090c0d150b01020a05070e0106080106030501030213050702010e01050a0b0f0105070803 84
    0x1024017841030711f6107074000804e01d503660b00c2c14682001c040c0b0400c8a841c51340ba40751000c0801d15081c98015100880400c0c401c45240c0b50414000382c030328011403899107403510201e901400050b242030007140c05c901c0c428103006443e0704214504920329030007841d803d0884008044001070142d0300c40041070403103100365603040e411340082c1812030500c1d10741e400421031391240000c0300d81c02c142d0680c0194892035000c01c01d8a003940320340041118894040d500140041d031a80d105102041524030358a810000840c005c1034080382c0c594401e0b2010700d51140700c000d400c292500300110018103015035034103c102141d040306c00c4142651040100b070400c1403410074640d0b0314242ca001c0e9034000c10041c2d51050304007007140d503500e640e043c00022080e02400b40d880060403000001078106d000c1d00465050302d43c000c15848a01d0840d080e55401800e0080c40001150b403100801e452040d42881558003a404000c00410740304101c5050200d202110b400c0181000000c215001c041400442546d420070074200034003 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 91140944 1250 91139694 91139723
    0x2070317090907020304060306170a120221040f05030613080c1e030406090f0b0a0e0103020702130f0b030a05030301030b040512031f09090305070215040906090905010e030c0703 78
    0x20181c0075450407281c20410b0790701807284542d000405001200d0180d541030200300d80794522000c5040c140c8501d41c400c2d40c445031410000560303029206c150312600380b040301d05108820081c070b040502c080961150308100082c041c802401c011035450050f08055000b4942c0d810094100300c41c00b10a00d07009054218045040c443c00341d000e1180f40e02082d911152116091070b60200241c89a04c54443c1c0c8002c900c0c0780400203040e1382c0e044003d07021030340c00100d004e0906100303c030305480b06290030613034a0405500300f110a0042c2e881c5111404801005100094503c1c0c04804000c100c0d509900c1003480799020000c0113000600000859066a40c842900e2000d900c7d20302d0140c0c6030404010581c5c031414404010050314503440d03085812481c00a40c2e03442e50709583d44102c00304a0b8074818004e400202d0422520003d03062181c43d2513801d1408010a43c030f41075540484400320380070754200b04011902d4440c242c051020901034461000c0542002c0c51419403103d0300389640342a035200c0103003003038500b170307140c = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 91142194 1250 91140944 91140983
    0x5060f041d01020408150a0b06161a010611010606090b070807050106051203030703150b0f0310080d02010f06090203310b25020604050607050c0a02060d0b1807020703 73
    0x30300038203003401c0c0d00035501c1e60380710a00d80740c48440c40b0a16060400007440001e1009005000d914130008003d05030302d141c481d9405010280070700b4020241d130b440001880d1092500e140c1c00f81c140c020009640c985c0422980280075900391200b681c0a0401c1000002c81404120034080445400a034800328090b43d440312032810502500c0540d10413540411a00fa0501c000080400218858903260341d0400c090400d1494420809849004d0f90302c0740d1070144050b2800c000068010750300050303850204281c0f950344a8003549400c41d4110342400607510307240c2d41000465a40200f40161110090a41c00c0d480c10400d002e400d00702e40d600181100c280700c01c1069080d144541010004c64010785103c03100d103414071903c500300c040c207054078080ca941c06103028110791000c41d4140c011039100c00a042ca50320760840442d44c540145400e020140610300140c00181d132047e0080c51405040e080105030901010b0030091400542c0d00000c50000d901410801d44681c04200c1e442a40c0e440b4006820450000c080c = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 91143444 1250 91142194 91142231
    0x6090506071e0b090f030c06060405090a020d060e1504020f010810120503030708160903060c050912060a0b0a15051e180910080703110d1b0503070905060f04 69
    0x25038030a0300c4242c290303000f403003030440d0020b1040080d04225416900000b4206642c4d100b070150100c8242c03c158007041c034a1030503030044d43e046141d10040b0752001c456030300015126204214111030031583c3c1c0010703200d031040c20310070803414501c0152404141c0c80c041e004681c0720700040907510304002c400c0d000035100d0071080230340f4000390018820301c81000c00345150580e40c9510513182c24001c00c603c5400145c0f5500822001d0010000558a8211051035695080d018207441d0f4003500500009010b001d50503200c030303024074a40c030107810010b202500705800164229000c1c036030070b5402008586400c1c840c0c0c0b074001c3d880300140c0607a881c04507981c2590003c0c2071800000c00c1388102503c1000200c500710b01d05800590482d065041b40d01d8900c0c1e032170b440032aa203034241c1d620441119410400c410008900401c540f880c00c0e15018146040200a82c0d03180703400721107035a81c0c51201a41406050003242800c01018014000781d00e8100500d050020000c1d80d1031405050544c4240c4c1c41d5400d8142c0e0000d05007 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 91144694 1250 91143444 91143473
    0x41506052d161e0816080c01110310050901030521040b07050609060a05011d090307020907021e012901031b0905010e040b0603070c0302160e0403180609050607 70
    0x14401501d442c0702c2022407030100100c55007901e41c00282d03010080c80c00001c0307585151055111690b985000b00506107082d94001c10b00c003da40104051040e51141c003400e000350504000d2804540d55640b42c9280342e20901003240c0c202c0d42c020b0b41c0ca41c00510000f81c0c0000c2c0c4c84191558144510450040fa81709910184503640007584001c0b80441c0c2c030020407000103440c1d8002c044583c1550b10603640c0041a404480003403062688880c03040d103041c200d800b80f042c03025402c00072080a8a2601d511900420054601600c04600507403021000504141c0d140c0066806600c1d004000e1060304144c4c80d40750042851011640d6148010708ac011000da03000307034071013104600d844142c1c2440030503014002e004000c061040d94007042803038001032480c0c0303440d108096840d02e00902c4035055464042c0102c0e280c4104070401c5055114444c4000510b100e40c000c0700008003000d01c145580c51070280740003007465109400020408003595000e201c2e050704554540300fa01da054841d5911809141408400f100c02e20 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 91145944 1250 91144694 91144777
    0xc08130b070f030f03110d090201030b0d08040e011202030d030c110a0302100c0203040e150d05010203090105062d0f0a090510050414040305160609020612040204150605 74
    0x7034034400c00c1288810030103118000c0c0c9031880001c04002054007614500300b00283d807503604200300080e00314141d01204030302d0f00602d0300040440d5950042100154035540954141402203010083e0141b03c41031070b80941300304100d0650035940c1e0360211ba41e440d120b40002c0c00381034481040c03003100341c41102c030b0480362211030044400300090b03820083d403a182c00030a83c003586801d140100b02501d00000450f8219401a24100b0140e5180c410ba4081640000103599028010103204000300e003007400a58050340f4210000900ca080110030482d4241d4511021005614030ba2401c111f144e1010130400d500503420b0380c59669402a5100040c0f80c00c0303a503003158040f107151401740a981304e0301c810500c050b90800d440400c80c603480803081440350700341101c00500003a0200508600403041040e201c1340b55119140100360703c421940090016080702141806d080c00000420082d86014007480703240d159203113285d41899040940c020807611130060318041030b90303c0049034031030341d07610481d00b0300e400b00310 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 91147194 1250 91145944 91145947
    0xf03010c030504020f0a030c1a0c070305030c0105181e0f010f050f010806040b0a0209030109021005090109050907050a080c04090501030302030d11030106050702040902040f060f17010c0c08130b 85
    0x400d40900240425102070b80194588140c010040c108203a004090302e0f00b12504001443c0341100100028594003841c8480c405e06108042c0040010000303013025621440246881c3c0201041c4142103510080203c0407403a460b0356852200040821100320310100562441d40015040c0900b600e0f203c00c0010808140d8a481440c492034041d5030300841c0603080d00202d0040a90b82d4031400b66441c2001d84015151103150400f00f141412942c3c01480c400d85c0240001c50030301c445030000303014261040c00e5180440d800003252941507034007180400291004540003145410300b580010924064000351209000075400400c61444c220002d940040040c12024406580c403454001e49940090940b82c0c10341d0300780a10701500108840669040c0c460725074507a41041d80c1602044080c0c40d0020702640c0081e03950340c02265030301190082c0000350000714024243d191402d140070f0900e1380c0e640c4804100303915101281c0f407103560000190320480e4011b12819110001e010059524202c0c1d54807500c5903510 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 91148444 1250 91147194 91147211
    0x307090b0c03090f1e01110c0607060b040b1504060c0c0306020301080304170604050a030813140c010e0a05030304030f30030b180c0c030c03370503150f0301 69
    0x1c1c00001480101d4081e02e45030024441e9105100b8084103664a001c1d2640a60304100d01a51150040d462443c1c03030941103403070040302d03040800e002da4084442551040d0702d070240b41a03203041600500c0b0700d4250a482e14040c405400703a1190035402180551070402c240551210103101020f41d400c4061508080219038a581d0342140d5507403139120b4031550548000d1040345403124100031403214400c68001001d440c41520030794003144d14aa00408468100d1140c00f80500840c600071440841143c203500100700305a01c000014140880e5a64000e120b0b0480450034481500c01105031000c0700d60144100344544041c0c5446500491005c401d00c40404039401d08a943c0c805920021104c02841e84042060071290001d0291410392401c10240c00442100840c511849100c01044503490b10300550781000c10014006041d40c4c011121010f0f894040da00c1c25414484180b02541c3c6515003020100e4030101d014405016808001d10010480c3d00a44540c00d0769250314191491560000b8020048080c = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 91149694 1250 91148444 91148467
    0x9060d0e010501231c0b04050a03121e150b0a0305060a0f030203060628080c09090c0102071404110a031d19081608030403050a020d030911060307090b 66
    0x5402500d54096090000014401d040c41c1341d2042401021200860341601c1c0344103104000c032102401030380a10141d5069400b05900060306401140b2802c054031101e81c0604004080b00d01d5040b0900920740b4000b06030030105c07540c1c0b2801e1b0a52108001c0852180c5100d40c40c09040085130344001c40340040000d2190b01542d0540c0068424041200c040300481c1c1c0b1351014007110030380b41c00029007507404640407030f941c0d2820b07d0b00500341c1100c1c0102c090300c10131009118282440c240e48511705079400b482e0130314110f182c044012948101c841004200c1c403001c20300000d60317500644c86254a03401130201c103081507071030742c2e00801d015203000c00380c0c1a51181c241c00014020306d00803c00d50924010640ca80706502d0022030200084103c046424012000303e45410400f40d103d2640c00384001103e000ba04006800b44010358491402a10385a484c1c41c02e2520190510b80d03660191005c040c6042c04803800100181042c18006209660050301c1b9903d0003401e0b165030119810200703036600080ba1135013100 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 91150944 1250 91149694 91149701
    0x20a0803030906012103050301231302120606070507050d030512070905040b03070305060c160501060605120901060b030a0c031805070609052205060a0909060501061d0306041709060d 80
    0x303483c0c1140e201c82d400c5000c17014842e0a101420028005681080104040720540031005654080031901c0c03215403c0c81000600d21140c208450080142c021803100b18201c641000341c0c1d84280c090760ba0302e191844540c3c07020f0b101c007094010244030711118810070090610400a4a1032240700b481640c980d4100000d01070030707030340452044034415070425035030600742d0601241c510222036101c00205440c0c1c07103c1030720702426004190a0b0155803100000080810b4003401010000d0200392a403c0d603070302a65019240000b40100801c0e042e0381000020002d81030502c2c11203900058140c00080c2c51494810202c2c060130025582150722950422114280b22012845d802120065114620159951014042012000d4404500c0c207202d40081300c90070700c844c0d040954400c3c8003c16015681d519a0085401c03180321030000d8881e5540c840c014042d094101400c0c4006030710f03c501c400401c2150302c0001c1d903600e900400040c400c00031454511a44c06580c42581e81e150710080c03a0a03110b038900500d60005 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 91152194 1250 91150944 91150949
    0x1505041502070f210918020c0105040c030618080702090a0b0306090606040c1103040302040c02071d1005010503060603040f0201090b0c010504060c08060307170a02040e010911010f021009020a080303090601 90
    0x1210480481c280106038940004821310781a841d001607051420b1380f00f02c071110b906114052200c1c0c0802802e002c0900c2031051901c220702c201c0c030362550681941044000ca502020106070010780d60310560002c22921380581e407071268101d61200180d510000007074007803ca0449203503094450704041c03190307402d4085541d070301c18007003038404002101c20800101e4020b01e0160715088280c00810061000d42410b802038205000940122001039581c2c01900041011005400300703007501c00c034203005040f01488601c40c02070000740382960075800e15070002003207407202030300040000004202520440e4083d0303060348020440661080d4642090211f031901030305049604442c000c1c80c200b0380040780c80c0146500c5020b1040900182001401c0031407a6088070300116165040e40306000f100401a501c03801642c84028100e000860701c0300349494403040001c00080024140319003001400c10907036001079018042226068049985481030010a18541403038000c003041e404000b04000b00ca80002460604 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 91153444 1250 91152194 91152203
    0x60603030c050c06090a0506130b1204051006060e0424060e01120c050306010807020c0303030103030c15110d15030b04080915071703060f1e030c0a031505041502070f 73
    0x400f19408009103403084051403584a5090f0304284064200711001d40241a60030312581c00003616014007403072a40240250204002d8010704020402009100f00c0300c4110355a8814010242800c6c40505038900440c0c05234006d40d501e03c40201d410380a000440300c070350062030180f4251a2100c0008144442040e01107001c01d860240f4003002101d94443c854501d045560f4250444c3c82e00740044035000d00150246013103100700d403810349150380c0c02d0008500035846915030201600f200c0c070703054414185000b6007031822440c00040d015440800411035100828400f800030b0300741004080440000180d400c00b6102800400400041000c010000d00307280c2e00844441d04100d4442e14401214815858020010000d603039100d843e503201240a103030001001040340710704120800c04903401c8204154141d003a0300d039070b4620300400d00b418040d105001506440110005045072030f8240710a854011500800c1d40c4c501c0010184101d10b4400391030244003c1080d9620b101900b00021a825860700a54 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 91154694 1250 91153444 91153453
    0x3210204140f15030601021510030201080c09010801060e0d0b01030803010302030c060403080d150816090b01021b0607060b060d0203071d09040311030408100e0601120c09090c03060603030c05 84
    0x141c5a00d803801c42d007610b826008004140100d100000e142907a00701901e0541544030f0f001c1c0707405190f031103038802c0e0340b08004403801c003410b0038614000148603407005040c09044050421901c062640c0c003c2d5201d064405a00303103d20a07000210125003981c281e40c1014041c0c000d030b04000310801201d203008604a0f402141100d6640e5040f008201c600d100b244801050420208554801700e1810307040f101696901d60141c1104568a496190521038070011004e080c0700d0208040c849189188104401082c0a00c0241918102d0204106503a04031081c05031060780007240207070800c045500501000301015046507110040245068040d40040e0354150210300344810007000f10342081081c042204004044d01141d44a54801743d8bc0c000d40981000905e000c1008045001c0740c04004c1110b150b003040c40700041c80200b0014040c24083c0c10307002000080c102110800128103039004120545404000000b00084146401801849650b100400b01d40c2420000018150801e0f40003109034060820368 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 91155944 1250 91154694 91154729
    0x11d010c080702030d0510090905010b120f0d120b120a0b070c02090a050a1409070303090b030708040813091103040b1506190507060516110304031502030403210204 72
    0x1a141c21a0444116005030300500100c0650340081c1c000ca43c012614400c000311785a03c0300120030644149050544041c0c0d102c480c10000741c1021001c3c882110003100142c034446010101e40303502c0341c0810840204201040c81c00d0031920314950f000c0504460000c1550444a0200c12403e0b11000106003d944506d05e4a0018900e50300a80c02d06540d01d40c003d12840c0c09607160704907a002018050480303c082607a8014201700d042c0c1c1c2c4c4103454040c0500f940148091882c2d072034010410324250700040c030000402d005107e42160052a0a60000c0c2e1141e181601d41541c20603044072241d90740e1240d0012802e00b4034402c0400706000080d40118081d01c135400e600d644240540011074150101a9000303034040221480901030407d922484051500d41301d4a814130a8581c10b003a1403003500e141c1d01c200c0d00301e10490030041e0401401c12014800c00c0140d410585103854a240801000390b014403c150008000703410503106941441c080640e581000720f0207a000058080290800c1c0121518120b001070720 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 91157194 1250 91155944 91155947
    0x1e070e040f021b0c190e0604020f09100509030f0a050a020d051221010b07020a06030c170f151203030f1323010b24090d0b01291206010f11011d010c 65
    0x502040d20000b0b0941a01b80c1c4560341404025400790854003801403051101c60100d550b0b061001d05a00714580d110307a103420b01c10b401c00d400c2103102014501a680841c8a03040065030100700c884155070101c841c10451011800d01a0070240481450442c080700040e000c0d4100d50400403248044581d01c1c1001040ea03200c1004281c103101c0d60a0296004000f03c1c02004518030070340280007203030244c1c80d03d4036414013001a0b0403841c4d81c0035501039914021507810800c2d00e056403401003c0c011400c4616010504040c0d501c5070f1240300180051400d00e5404001500806074a00c003889540e6001442c40007c9038501c2504d5031072176070100400001d5080c09403c0b445072078115520034000072100c0a1881c59582c81d07080418035402030303550036000318400017480089a011400c03180208035070b400d81c070b03c582081d1103041d14102250800d042d02ca107003405804401540380203190391064082c01c214030011f1180d0020b4403003400441d01c00c3c81c40c0d8280012205c00d4112512191801c400e20348c001d0000c921918030 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 91158444 1250 91157194 91157239
    0xc040917120405070f030b041407090c0201020c0f0c0109030f020f0d23030307140318010603030804062009060a030e07080a02010e0307140d060905060403081e070e040f021b0c 77
    0x140c0000507d4021801141d42301d4850a00300d0995001c03230308020f0f9603110103000d44500611041c0581d501049100300f4200038400c009503150070002510341584401d001a20a00032030001501002c080b50940d0300310b4590010a0076122801000100001c01d685400100c51403218681c0035104600003010404500000a81c0c1c00b440064450345929040c07400f8182c8503030001806520240c00d10304090891050a21034003000c2c500946e600c028a1a080c10400e054803107603a00a880c84183c0324084c00c0841d99070302aa41082c90480302e1540d01c4c1201c00c82100903181c584591469030151100c00102e40000003030501a183c404e895038029280b91108150304e90b000d6108400225440780c1c8c0b50f2070a85403007a9144405480364038001500c1d2403d86881e894003104440490100344040c8c2407040100d01070075054000149219145554900030000800e100702c00300161307000700e8894524404245250f01581c0c04030019000288100c0050041c2c1030f529055414000c2c0541c0c9410754403009400d040c0c0 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 91159694 1250 91158444 91158449
    0x1801060303021c030b09070201140c07020f0409060f0f02040f050301020315040e19110a0902090d030f03110c060403030509030301140f010903120201060f080f0c040917120405070f 79
    0x10082d062080060120503541d01c3c0e21031a4404240d030784c41c0011115a1403030f40c428000c800e141d000080407145c24490040704c01d0060030304100380e80706214540042e520b20b18103001c41d24007501c010410302c0040c0740c6880070700215048602c17190304117210302c482c2d100301354054000c407007050ba802c01009680781c0038036080384029a021314a5840c41001d801082c1050341140c0503800102d800c568448449422071100f10501f03031002c40e039410b0b507480300e40c2d100e04c1c02c515580c0c040c0840034411464005480d0009182d076011540c01010301422860880079240654418100030124541690351006024052500c604045400b200460b14000210300282c1c8000709907410303680e07201c0c1c0c4025000030b01010021070300340e2164030f43e04001407030102000140384031120900e14041500086010742c01e294100c013060b80103070403905141e84240541c80450703000081c43d0240303850a036400190301c0b94a080c1400c00c00a56426010a468001103682c0c0c40402803110030b20941c010b80580380d40a80b104440711005840d40b = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 91160944 1250 91159694 91159697
    0x3021806181914091302060703091a0307053103050105010503010507030209060f0f090618030d021209060c030f12040b0f0709030305030a1413020405010f05030d18050a09051801060303 81
    0x50b0203207119030400100c05034005034401702001600c81c80e5400101c079a48412003c400152860200b04080316160040340152190504c2c0c1078154640000001e01c07e001d200d40114440d005400f14900101104150240c7c14030160051110a626400c140703010740340a11a85000b5840d2200160744d0030300c00e10030754a07181c4008101c1442c180001e01e0080c0103800c040200c07641428200041d03010790f03940070010304c41100000c0000c814501ca103070805080000841030308d02550000c102581407070b03440108881c1000802c0381c0107a191340c1c107001d11a2440c094585440138a42002854040c0074240015081c17043d8804c100407007560381c60034401d5010107003d5854001107a9000c1d01072000038055006194803401c268000a03944410121201c511001641c0c1800e46811210044084d424a0b01031280580b070306c00e90b40c0646603e4107001ca0342d9030006817030344e10401001001400701e60860510350b200804000f09803050558039844142d00804068a18120391020f140780645540010701944040700d805 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 91162194 1250 91160944 91160969
    0xd11060c03061c05150a050105040b01020a260408010e0c030d090e01030305030c090d0c06030b010c02030c0603130b0a0b010f031a06030619030f05071d0106030218061819 75
    0x1284203c0b10030503440c4034103c034140508a5801d5200c0298180c191107104600004126035143c4804d01c4112503800190714115007003182040d0200790b81d80c200f1014240503d43c869072440313507110b5840450040e9000a040d55013018400b02031210b00144040c240725045050301c0d01c040807554140c0f50a92148078509001064a004001090052002d075a100c160701e00880c8c030302001000080c200c0d80981d074080740c4540104c102842004e078113100d101c488500a00702001442c0c0b050f000a0723034820b01056481c4c0710728000030001c2c07400410010701411440d80180012010f0070005811006054242c8201d8006100a018a1140d82c40303401400000c01d003a0811a41d0032540d1414841c6030742c4020045c54000d0301c0700b0102034180e030010190000940c01080702c1130742e40c0d009250403428243e259214404c520010107800c6140b141816a0398115102400c0040e591081f26004011004610000c10b0f400035010448203925011108110318414048803001402d010301034000700032110a01450062000 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 91163444 1250 91162194 91162219
    0x3070c0b040e040b0703020417011e02042301110d020a05060f040803060f01051605031308030903030d020d1506050910020f0a030c080403020901180b090105060a03021b0d11060c0306 80
    0x96003266170b8014603540740c098580343d20380d86078052041100d241e90b1920782d511580f06000c11151248280c1b80403941105502c0c1c0b51920000603140140030341c4103e50200e01c0426a1920780c02007100c4207148100700300b030300d0700900c1e0094003a48452000200b40c400c1c0c01144005440d40c0039807846c00b8890356100006a045403600018411000800041c680c140f0038200214820a1060521100000c1c807800041d541c940100c052441c1c51480740c2c1c403001c407550081c016504199808000d441445031000300060325000d504506902500892104802035000c0d0340002c194994042d000b03184000040c3c2d98410740b8000c3c04001c907542d80344030342c01f6886504012140701c00a40f080254540d181d002d80302c050f08054880d000111140d00a90200108141524001620f00c169000b2140703007180891b640d080f25071609010aa00e807265840200030580d0016201c580e80c2102e40850740d42110000444008080e0034030090400352a84004280520a0b00002a202c2101e24100c038031402000c0c001f0583c000 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 91164694 1250 91163444 91163453
    0x11070309060e0d060e0c060408100f06120f0305130f051009140f06040f08070302100809030a080c1c0209120a02210f102a0c110103060302090903070c0b040e04 70
    0x1079125480d242c0d0040c0001b000050341c0c1d0102600141083d400a40100c2c031341d6594240884504c0c1c481048041e0801c4030400034921085400326000d604000d4070001840e1a290880d0284201e0003441c0c2629044030020a50100c082d2030401075400958610356441c00b40e0b01b0036503070620395224220410b45600c0001d01d050a0099006d6100c0c1009400c4c00d060540710b6400404001ca6508400c425a003c00c400300107515010b1820b03512406107062909660600d0805030f51240b103151039581c18400c010700441d20040400d02103403960020400003141c40110403415901940c05118200c0c851003490300c154924407000b064480d0381c260700420040e6068150001040c1804845001e03a440307004d42c0d07041c4500014203000c40300c03440320500c8000071702c0344117a2a10303200c6076001c4035070400b84040c4003807088400b0380100d0641829900884009191205040100c0107022035070002074005900809016070f0380d400002903c1118810030841031000e464007406580c9008910032140e1244c52a40840c0204 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 91165944 1250 91164694 91164701
    0x105010509060f0d0c02071205060115090b130504060b0c031602040209030601080a02040c080106120902060c03040e04020901061110270318050907050a030b031011070309060e0d06 79
    0x411010b04110b00b0640740003500c1400d5041107100c00c0e002c989496100c4401c1d40e05000e05005402400d0018421108503142d266864205004050000424000c5590441d014030b400c0700085c5031542c00c02c0c0d51010010f002400c1d40103a0310685010301c0c1010300c0412054014001d58a850161a00941c103005c0100280d54080d80340002c16031300507608000e15801500c00340401d601a14028000b0000202e55105100887d070405002004228402c0c7c0148070b199480001640324410004022400d0556800001c00c24410030400009600c400100000d81d000708144c40ca220340d0017111442583c0c0e07a0b610382a180b80b6802c5501c1c00c4150409481d02d18410304641c026142c1346000d140300f45031909544c10690030b81507000c1e02900411038060042c00319902d00e51401d030190906444541d0581031044001c1d059002e807031070b000c080c1900c401641c802928100a00c0c00d102040500c00e22011100010004090b40035482c140c0000390058000702d050390107148101e081c01740c09401c1ca05a10040d44448004 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 91167194 1250 91165944 91165957
    0xa090b0609040f060305010e0303010e061008010308070302070b031006110102130302090a060b18090603011e022805041809020a0b0304050a1407170604020634080d11030f01050105 79
    0xb081d648504c0440800c034240314030b0000c00c08000c0216541e50514651440d405001010944201401c180e01d04202d544100207a044942c0500e03030710b4841805281c16400c08501d1f4002404e0b242020003086200c1f00d0aa03122000c545440e02c8911144004d03204641c243d21441c4080304200d54205420801401c001d507070f142d480301c04003600090003512942d0b0380761180c3c001d0742d210b05901a1403100462924044071840d0304104114000c10815032044d4103c0031107090b08801c00b1041d03a0201d4980c0d02e241c51001c03080600d1b1911088a40305c09441a030142c02500b0900030b00715a0b800b5120301070741002482c49848034098005002c2c4144528182a0a10395840240116003d000f6202e4043c001514096401c1d460030308840642410713801d00c85040d01709412205d1820442d84402c080c000903840d094103c0f24085110200c1c0c2107aa450a0345040a0100040341d0300005100c4444003000d002c4950040c0001595241d001e1090214045881a60340015101c1c010071440580040103158041c00087c0706 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 91168444 1250 91167194 91167221
    0xf0106170c040b0705070b0307080709050f0d030503091015091b0912060f020720010504030f08130f09060e07030b030d0804050c04020c0709200706050c040e150a090b060904 76
    0x11151a44465601502300383c1e04507000c0380d400820301a0050304501c44d000507000507214007007184084000500c0c260715419000c1d090210000128072024418030010f041c03011032120511901744101142c4040078850301c1104045840c21192501c28004009000221181695202c400d542051100702440022040031501c036542c1c2c02269280c0074842c005030604a004200460000406150901c51440c07801704107410003000700300900000c4c4170f4031024201d154029817140c3d1144660181c80405180300c0e00071100300c400c0001c00203102c001640158094400302d10403220340382c944210a501703460b07051028541c560088401051054482c03003074983d0040c080c5041350708450540001c40c040341c0c8903030781c188501c2d08480010700100307981d401140c0d03034142d503041030b1500b108403500d40320307518050f1010040c000340d02e800129540c040c610041d05c010700b5800c0c00120780da08011383c107404003112449829028658000e00000c00940034800d101c90308001404091800c500d42042000800c00c00303400b000f = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 91169694 1250 91168444 91168453
    0xa05090d140a0309140a021f0f030b040204050306010b0c0106050114070308040312020d0209120303040206030420040f06030501050601090b0a0f021912090e0910050705120f0106170c040b0705 84
    0x81360365217800c2100020000c000c1c1500c00181d0040c0000301c0542d47c03988655070105a481210103520100c100c04454076464001010310000d400507000e4440c41c1d1020340d0510500002050302d224410040ca1350754141c00003000020381e540010354000700e4000007000641028816800482c1c0110b801a80c003034442d00d444c09040711040080c404a801c03012140980315404a2884202e040c03a03620081c0808125006605600e005c3c2d0001c1c009105c020002443c52450030b01254800000344a80c28403e0320041061040c000511003190080c682480141e03507960a00000c51803550180390f0260030b642c44206128034101e00004251405503041050034118400d0741c00e6410110070380fa005000c4188100c015000380c100340746000b00040c1d0306401c04002100c40f1410711005020000e01d0f80b4540b807101d500070900303581d00a01903949028005c40f010a4504400400c101103404200660681e01d151300ca071704144540b03c0c024680050201c90f403005070b0000304401d0050301840000381c151a4070510454 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 91170944 1250 91169694 91169711
    0x1005091c080907090509031b070308070828080a0506010c0203120a0212030709030b10031e06050903090307091515020d02010f0c020c090a0213030302060a05090d140a03 74
    0x60054040c0c05418002401030041c4200c00c101840303860020500c00000784154140101d40f561a880f0b0158010100c5002020710719400005115010041d50403034411603c4034602c0c10484070503400b865104500141d500890459810150615500302c0701540d6136141170f40e10343c01c01030014000500850b0510a60755000c40060364204100300340f0f0043d07184c50fa511400192006850500205524243c0031024020020f502e0381c450494012240c00c81602c40440d202e070f80d0700c2400340300780303070005001d25020280c1c580506198100e07280c9000d2040c0e60400031603894190040e120b004880d030b072660580203908100401c2605410007030601180c81401000c466885030500d100380c0d00b04a004d800340e003100c09454160350302880780300300da2580c0e004203210107490110000d41755405202144d10807a0180b02007070140e801c50703060741e0004643e500302e0600e4270b8030382c01c001e5030303c8104494140c505420440026540c2c02c01061515800c45161100d00c0d00e48110030720351411703820a110550406a5800700c0 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 91172194 1250 91170944 91170973
    0x60a11040b040303030911010201050103030512101517010510091a0c061602010e0a0221010e070b040f0b0c0c010813020414160908300c0619060503100509 68
    0x8200a511075180044c0c0080071f07181c8612410311110489040da450680108003180d00a0100c400702e02214603c0d001942c5c82ca070405035544240d42001d0f11050000e050895041e403c08810001d03152004102c1072a0f03a61030003008410502c690603000029804c903002c02c8024100c3c1600400c4050403848a41407910ba01007851410704202d40e0407241a8101680d01d00310b58082c07259042e03003034140007e04102c1400c2d40102c0d04a9481520f1107a02e0140c43d00310680040c000c5d48911801c0248034140c40c045a0b44da00d003881541c00030700030025003450aa0001a004030404d003222a900d0301074024000c1c4011090045da141704000300001c4441e400d0845032001683d0703034032685800071540c1ca401c100900b0654101000a00c01d0034003d424414410402c1c401c0c900c6c009000492000e9481c20b015000403484010303031a6100c4c02c0010120400c01040000d1000c6010486510625007190800100301290f004001030700c40a101e10764058208034007002054100781c03c944e031320505a60031944081d800020 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 91173444 1250 91172194 91172197
    0xe040e03040e1f09060e0402010c061401030b1005190b070203030409150306060b0702031b010c050307050318010518040c030902030a0f030f020c0307170a12020604020102010f050702060a11040b 85
    0xc400d40442c0b08840d000125560045100c4081c04e41c450040101d582803a40d01c541d074940161020b4107028407004040100406034209200444000074100e0385541d49203845100e107042038402c0b40c01f1151024007c105400e20307000000881501e8407200c2c40251805000f0703003041e07001c00c40a80c0c00d40401c0001280002d8103004194080d00c40d8940320f10b0322441d600b4110308030b600c0c642019218200400000300980d0b00041c1c2408508603407000780b1a00100b010040c0d454400300c4030014028040450f806050100c04409060141d071882c4120300d14800c07050044440e840f844e4150000d440094000301c06a0600c0da10041010340750f801c0010b0f007038081e0b8000034544003803036104880010300c0300d03410402c150f8400e1031490320188500040a86505000000c0d80f82d0840e40505245603d0a034000800e00004110f103041890b00030000c0e10100300e51120082d1140c4040b10b0503405507080c21101400d00e80d1611810384070b515154041c142035200d603080b920151289103901044d0060622000c81c01d24003080 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 91174694 1250 91173444 91173451
    0x4021e0d110103050604090201120c02010f090602250206070803090c21010f021305010c0203120301030507081203040305030f060d06020a200c03060402090703090501150611010c0e040e03040e 84
    0x7408181d0701c400080005042c2d41e03004210700d0095082c1101c40006036084444600c09010302c00d004201a40d42020032401042c0303081c45136242c0303824484c421701400300560041a00302c2c082e45107600795040d00d07001007011001c403400c00cd40121040182c034001c19122406160003100c1c0b03030203494280c10b812000441c00050181c1701c20030807a40d80d40c001d584840902c42e04c400c40e0803e08082d420810b0030403403004440c81500c2028180407411088000310740d0240300000281c6040550300c2e40383e52712400e11035a070750b81d00e025000f4140b15113492a100c225021007941c1c031880d4181d0b5007038996580c0d05108141050043c0c842500581d104044900050650018100c1e88849644000760800e02400813240000ca51205110540005085502c03c0c2c0300440d610358402e030192051034050322100000c4006002060015005500e07040400c0c0c44407060442c800102c074129500c81c40b104210b841258221407242540c0c501240345691104c6540c1441d410502032004810300b43d03400c1584c1c0e4601444929001c5 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 91175944 1250 91174694 91174703
    0x30a0e070f090b040e070501110c09040b01171f0b01021c0201020c07050118090b18070c110f0904030f02010e030f04150906080406110c1515030a030804021e0d 70
    0x8000b8070060b031041c403403400e241100b15018424640c101c042c0e9626000103000f0541000015035900e0050321080003d00c881d9000900801000d142c1030a148072452020702030100d4a9194600f15494104005400d8452500c20194003006a001c2c4102500030004500c010781907010311151600d1613039803040381b01d04e0301e4541e400140c0d8031000f004c0c089003007601c04d40003cad040c0000c5031111031014003400300352410703226030240c0007072070761301c0080040c54041000200c0c0300711145110422900c2c0d41e10007092402c85114015003060280800104202c048425050507081002c7c0380009010920500c40800c10000398000042e4400d80d0200032425540100d4218191110000d4200100001002441e0a51845140296405d41080306c014030802020304050000c680f20403180c2a41128881100d00c000140030071140400be4402201c508200219414020328026410510107810040750b000038191345640d40e0308080d9120f6003000402c0484200c0c81c2c903090300c2e121070040c1c2c0382c079007460301c10215006 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 91177194 1250 91175944 91175969
    0x509042103090521031b04081209010206010902070f030305070e060c0106031203050103030504090e07170d0801050406051008090708010e101a060702010c05120f0403110402040b030705030a0e07 85
    0x1c3c20410b103480b100c0c121907018980340080c41114400741c1003e403034000701c040c422016210300306003005895029a4020701103a008548031104200115001400f64003002e800740c030090303a41e0320f00c03210890041fa00003820621080740444006482940320a40c00080b5050000e03e00702c181c2d001c00c4a980113a00d46d00340d070740e54460060061012142c0d4100d060f480354907042c4629030561741c0040c040d002e9481900022070f11407006000300f00d000e01c00300c0050042d5802c00340384100404102c0d60341340c0c010500d0001069480002040900300350040364103072900503110581d020003200b0101c0b0340400007004101c16000d403c0000c161044280141c0d0010340200d0000c004803001d4050b15000c4580344010912880702030143c1401704c0e107840c3c0598803a50780900b0040400c0d011810114204484200d684071000000122600141c61542c09041601c0c0510600940c84030307030703409000491140780540c5192690900026501034400e1004507409103006501181c50000150414940255a0440b0681099 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 91178444 1250 91177194 91177211
    0x50a091e08010506091e0408090619121a010e040e0607170702011a010503061210021c0e070302040209130509010b1e100f0e030703050f070506040303090509042103 72
    0x10034041e103604080200d0f900c0b046070600310702c606d8111842c2032000700003100c5800000d01341310310304058480d52413001c2d0080c0e0ba20340a9003109801c01e1407042c07101c0d0201d411040083c0380d500345440386182c515586002c0d1212102c85c100103460703000d8040658bd5125880750070bc04817984c410300499000307850030b4590241ca15400e0f00804c0800e040101f400d811689064240c10303154070201c014100b054803c0c2400b6649032911004611120522101600544110300208203584042d900030042100b4141402c0000810850344009650300305803440c2e11a4800d0b1024005440d04d9401400d41c680000c200301100c40200030404244c850803902800315075034507544500c560a00c140700001512820054100380c4181c2c82c0012403800c81c80ea010410410b00c03240e800300300c5010300380d100c0c42e5102c01002c40e54440c0d560300e011961800c0c8581c0007a504d0140d80000243c0d81030203400e441c01c2e0780c1d140d240e0708501384c04c003810320850a03001082691040040c2c0c019250865a000000d020002660b801240040 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 91179694 1250 91178444 91178459
    0x30c0303020c15030408031503060f04050c15030118090b1006030f0203160c0309120c03061406011d03031e030f0f01061209020301060f0605030a0c0203031303050a091e 74
    0x8120012450040c03681000380c0103e402c1c84030403030364802d5000c2c1115032240c45030360070580020746400700c96405110350010f00801e60b424844c005d00c124030441c00c8411083c95003051148500d600d1071401031400e001d00040c40030041b100040001007800302c2000940c091291181010320310300b030b00d0764030802d20320395024841c440c0d01d40a41802c005122000751b25504080092204100c000780c0c140b0200102891300b94205449018400d0041079500301900020045080007030720f00001780b00031100503140c00703900300303201011400382c6100b00d005850303a0301c154580c070a140e5103415044040540c1400200312403900303a091394070380c00b0f91a6040c004081d200e2500c0e0008440c100009030500325105502c00042055a074406040f00c5120511400410319260301d20209004d082c440d08460100781e02c800e0040340140c1d1003405103209145160007130198946810f010780c1c0328401500d110021303240309440480401d000e5802007071202010303c2c1c148403c6541e015608400740740010241e00d981c25843d002c00400 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 91180944 1250 91179694 91179703
    0x90115030606020316021309020402030a0b011701080d050703020a05060c04170a02030c04020f040e160f09030b0c210a1d01060b03040f03090e07050304060c021c030e0304080304030c030302 83
    0x2d0480740001d52416040500d03840c0c1c4e103000d861009109107405a0701011108048e0070560060b50b02501c203540340d0414920030009040f244420600240c9030110b0000c00702980c3c42c10604070f0b011040504004000c2d17031006c4915074001e040c19000c0d442500904000598100300307140c0b00d00b02d408041074440c5c0c00d10007012540e00c0b500f0103100007a4428030f19200503990120b03582884c04d170219401030361440c81020801181c02a6800480c1402c60b60003008601003e4050580140266950307906c1c1c0140e055a058484500a000240c00c00c41000300095409900f00300070060070030140300020200d40382c9040c0000c0d040088071000d2500e901c625004401c480e002c1000f090303a4410000034801582407079205601d90000600150005c1070110301c60050600900341c08019101c0602c0504882c5007989000e4181e506c03d83d8111542494113400700c4005102140c1d00d01c00403d02094014090b208200403400380c2210080034403140070800c0000380d81c0c9010002040110b00c144a103021080c51404c01a050 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 91182194 1250 91180944 91180949
    0x1403040e0f0f1015020c0409050607080c0c03040306181e120905010503041b0f121101090819030e12010f0609050705070f03020a0b01090b130b060703110c0901150306 73
    0xb1195250188044524a044100141d030442500d00d2415680ca071002c914158210300c56642007880c1041407010f021001c42e02d9845004292900e10071900d0300c051902080c410308000c1591030304180414800902260400304024540c5050100400186e0b21801c0062400860882d14100d080c04007104020313480044034205075980c10200c4216241000203070881c840240010302440054110601078582c009955010b0003034061581d0810303484920306100213200e210141c0c0d803503204009201c800e6110f801d020069030440700183c419114814000304a80701a194210b00340040f8100000707a60f1905200c805641c02024008034210310201e0080044500c183c004440142c00d050822500315004030440b61581d038003410a0707910710002d0074100d00300b080c0f0700750080520940ca80001901030458001c10740e0351608035110700066004041c4401141d2845c4c420302d8006800f84070000109005988090405c1c51080a0f500990202400509400341c01d801c046030200205482e074602c1940351103030802 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 91183444 1250 91182194 91182211
    0xf0a020f0d05031005060c100203011502010b0a0617060f09070e0108060904021f092102040509010603020121020408010207081b0601030201200309150301060320040603091403040e0f 80
    0xa9030514151280c0c00c94130350302034140900000942c4000f010340c03c01041d22000c3c43c1007000c43d05c035610340583d0ba114603455482900150700f4071003500341071b1400300000001c480d9580c91340300d044c001d03040d0b401c4004013000300a1540451010f203002d8441d219065464402c074810354441c1c10040401d4009406018040e04080c00349100f00100320060300d0759500d0300d200c001c0790171164403800da200368112401143e94000b200220500c2012500110500060701c1e01540b0072139013031200d0b40d103003c060707401c07210144000390014911000241c215840c070070903010310035503048004d880e1644802580e800e9a0101c4400c584d54000060104201010f441440003a5450346016041951454000800c41380b441e51500c1d201d0305501c0103d4880c3d05080003110310140000e40f84202e03a0030120b040070002d8009105810100f410450712a80e03503c0301d0b01d07600c0110f89120000340d05080c00c00c1d400310010404c0400031503202c0c0100308079501e03a4004001400041080d40c0103002c09103001e82c012070b01e914002c0c1c040c42 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 91184694 1250 91183444 91183447
    0x203040c03020105030421020319080609011806050312031006020703050c190509090d031506051608040f090510050609010c02010315050a0602011409070e0a0f020f0a020f0d05 77
    0x2034010a0301a003241d030246401a10b0b92182d040140f1035030f40100b10740f4022000d51400f00718242c1c02001500d98001e12004410081180190503950202e007225101e0740815424018000e8803a00c40100c4003041010b0000205681c0700d4001c45d03e0301d0b0180080c43d094200100c01c04c00189a40401c1001610032480a84009840d40c2d54250380c8002d112003480c40f880451000d92030301c41241e07a4880c0280801850380c0094240451aa07481b1044080c034000040d00701100b0340f44046c1c2c1c4002c100b0454440340d039090b28100002c07500388030203010000d04480c044401c0000154000841c3c100e84090441c2d000d00041c2400c003085984102440c945c031181c041d45050015222982c2c0003582044210b8082c02e0118000700441d112010031242c5822995122803551408035001d07a05502229081740f007130800c0c20194450f07802d00c50399012203205111280b400040014880c1c64140c1002d0810404032501601300a6002a24001c7c1d0b000540f4403001079000e09000705d0b9030001003003045480e034507904100e0f = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 91185944 1250 91184694 91184701
    0x519170a0507420207060606030213090e0d0503100f0815060103091502031005100201020c1204050a06050a02070305070e090d1403010902071b06090509010b030903090108070509090a0b040f0203 85
    0x510b140207852440e250003005003c007040e4840d21540444040710740c46038082184549414020b40207401100408034072295005010689101031b11a49040b4000c14009224040040c60202c415920041040c1850009804009200c0d41d145100c100900920f40150850f000324080905042400a040d5810542804050004289a60366400c0c1800e40100007580e2981c4880300c81440300c4140c0d02035500301d1201e110f00040f1541c1075024011860f850420f80c2d00e440444004109280601e018007688200c0b01c010400007a40100700804140342c49005550380030f80d03030740c640c507003008003030707480000d07041d00a60801c4101d4038184400503c40f403050034140e5004841c40c0d02d0104034003050003001038680e070028210b01030101500800200e126524030001d285d54413000700030160b695070f1040c04d01450255002081d64410134040e24480c019002c02035050013030000044841e0300015111b01d083c41800c000803001e9445407020507220780034071440801c150010105100c02c44a403804000034003441070050 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 91187051 1107 91185944 91186013
    0xe0f040912080a111809040f0b070c0311030a020a0b06150d0b03010b06030f06010c0212010f0b0a210b071404060206060102060c04030519170a0507 65
    0x41442890b52444c0c20080c81d00448114070004540040c02c41501e00709410002d610600646103c2c4940e0126200c01400000a85442002440202070344d0305050300300042c0200300004400552a101e2420f80003902c41c00c004000414604041c4081040e607555020412248405180c00d83d17030711001c103203090004049400400b402542003c840b011030745019410343c0e204204200b03d00c007440d69140700460b03d0a41c040c001b264044800412503103079120903c0365104103075004000103444040c003401c004044400782d114001c80403034040400c103401e1200384480405a0b001c084031046444003401600c8007102c02003000240c10020500003422a800600240552003c2c1c0996800351500312a000d00c91141d80406052640090b406008115948403c550007078080e08103400601402200407a003580140c2000300007c6012689506100c00860208810204140005072b040c040840 = true := by decide +kernel

theorem cover : BRFrame.Cov 91007194 91187051 := by
  have h0 := BRFrame.cov_init 91007194
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91007194 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91007194 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91007194 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91007194 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91007194 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91007194 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91007194 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91007194 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91007194 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91007194 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91007194 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91007194 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91007194 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91007194 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91007194 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91007194 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91007194 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91007194 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91007194 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91007194 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91007194 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91007194 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91007194 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91007194 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91007194 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91007194 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91007194 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91007194 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91007194 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91007194 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91007194 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91007194 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91007194 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91007194 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91007194 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91007194 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91007194 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91007194 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91007194 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91007194 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91007194 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91007194 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91007194 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91007194 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91007194 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91007194 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91007194 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91007194 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91007194 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91007194 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91007194 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91007194 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91007194 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91007194 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91007194 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91007194 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91007194 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91007194 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91007194 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91007194 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91007194 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91007194 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91007194 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91007194 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91007194 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91007194 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91007194 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91007194 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91007194 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91007194 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91007194 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91007194 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91007194 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91007194 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91007194 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91007194 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91007194 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91007194 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91007194 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91007194 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91007194 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91007194 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91007194 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91007194 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91007194 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91007194 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91007194 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91007194 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91007194 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91007194 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91007194 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91007194 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91007194 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91007194 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91007194 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91007194 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91007194 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91007194 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91007194 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91007194 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91007194 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91007194 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91007194 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91007194 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91007194 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91007194 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91007194 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91007194 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91007194 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91007194 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91007194 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91007194 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91007194 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91007194 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91007194 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91007194 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91007194 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91007194 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91007194 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91007194 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91007194 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91007194 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91007194 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91007194 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91007194 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91007194 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91007194 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91007194 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91007194 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91007194 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91007194 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91007194 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91007194 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91007194 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91007194 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91007194 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91007194 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91007194 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91007194 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91007194 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91007194 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91007194 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91007194 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91007194 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 91007194 ≤ n) (h2 : n < 91187051) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
