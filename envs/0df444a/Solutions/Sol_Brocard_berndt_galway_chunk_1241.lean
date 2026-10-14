-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1241
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T01:56:26.622606+00:00
-- url     : https://prove2.me/submissions/d44a1f10-6e3b-452c-af98-71bd8c299b65

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 223021582 ≤ n < 223201438 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 223022832 1250 223021582 223021597
    0x90a06050a020c06220f0303060519060908190209090a05160302041a010804030f050f0403050a0b0f100e0705091f0807091805060301090210170a0902090703050717070507020a080d090308 82
    0x603600d2703a001825488124100145042c034117a885512424850040c1c4101c840380c11112032a44601948403044107142880d0040c90b404403891205503859095007490900c80d050300400d58090740440c04102ea0110b1070580603a442101d05100110b0468100054001c074040c1440c001014400800c01180c06000c18035190145443c255142c991004031000e80c0358080d6000701c07810380c8140c42403c140020486a180c0025880030f001420381008032841c80d40d104070340a0103080341d00440100320f216000c1c40031184075507005860300780420080c2243c0880e004644140c000411110000204424400c058002c03e84868010b24815002c1c0e0640e000e000b405c0041050350107650341d20001000da66400f00c0390802d01746c29603c0440d110f000f0800242d42d03030809400c001e01203041541c0140180e40b41c5904961100e00c41c03400048603a500d00d01141c503902800040801f81140a06001c801c0ba40b00307004152540c000d840e2801003a694040e560f42c3c0b00c0550044000040d110300d07090000520540081401 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 223024082 1250 223022832 223022837
    0x140904060317130e0c0a1b150204080f0105040803070c0519060209120c13090609060510060f020313030b07050c0f01050105010e030a030f0305090a06050a020c06220f03 74
    0x5140c0369910220307a00714584121a0300c0002242d42c40f2111100702c0707079001400c5200c030b0b01596414900741458070790007176105240c1800100c07440c0c00400303115184203400883d0041d0303681181c440541d404100a50241c0941d40403801200a50004403a05024140c041c42c0c2c8220100c2c9155117403541220984d84c0f050b400c641601882d104406290fa07404031150b926401003a005036901c040604000c021049481c0801403604141031082e803d50b41c0402e80b0341c1300d040d0108040b071104c41c0d43c64807400401111304001d044074038181c18803020b44902000704040d50b00544543d0303140004001c0c240e9480c0900107241c4070030740200c0c905100107001800a56001800d03410660300b03000b084103a481c01c0c41341000e903100690390340e40010840c542c1d000d00b0410080e601a009001980203a4400804e44d1111203042000c1c10340722000b00f00700c244100f00d1540725a410840030032690420301d098101039402250318001034031514010030440042054201c242ca41070080b844145203160380c80100e600c0145405906 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 223025332 1250 223024082 223024091
    0xc1104020c010504060b01020d1407112b1106091509030316050c011202181e03010212060f0901050a0311010315060f020106080102030709050d0609080a080109140403140904 76
    0x401401d0103241e0140d4802c0d4400b1401b045030b40d00091031721211000240400104181c854006038440342101c4806402101000f1042403036000303c4c612080000c520103a00c03016484030541c1d00020f01019203120301c500030901c06651010204881d9003c1c0341c2142e40c0c00720350b114035a900d10600c98010291008081c054a04041c0c0c0000303940d1410b0181e48086d1190340010b100c2c00880e690045100724041c1c02064118241588c0842c01510301c1076442c5100c1c0a0140100d916080100c0305c040114031040050003599034001d0360520340c028880642e0b80300e0044880c050f10758564503003a0f05249c1030320406041180c55a16688505c0c2c03650354460072071818150745003010501c0442600c182c0c5c020340306a4803918a00d4118542c0242100c2003603100400c0e40e40305109004500340e20008400444a080301c01c490b0000040c00d10100078a4010b85c0103000d0030000940350700c960b4001451504031030602c42d0400c401d0b44114140780b0b15810840340100064007022100c482500e01c10041e0109031409800080d = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 223026582 1250 223025332 223025347
    0x40f060504090f060b090c04061d131505030c030d0f03140a02040303020f010504212a0515010b0706091b0803030a0b030f0309092e140301020702010c110402 69
    0x400721800107a0658a1011041820080c05803c0c00303411009142030b5000f841b86d1034103000300c56003030080d40070b071134100401c084540410400b402d14420541d4001000d500009600303c45200c02440d00036a440d08140d9880c8c2c0000c0c0d14900403a0001c1100c0f0003a010b060f2010110b0002c80d001e00c0d03600c0c8840149a40c4800689078444a101c4240c4110f550041c016965825420040e240815145005031282c0c10801004002000d082071013039a8005100b0301c22402800700e10a81c0c142030b986079070309402d11a1700d41048814055024484445020710291188079450341c002204504007402494a81d401c01c0103102c0010711154050b1107114001c41c201a440d80003050f9445c03882065a000e0f02803603002100384424181c0c1c030b01c110b14404900318000c104216802c850191a03014015481e4400c4403010b0000381021071848445480d00c050b90f80d01210811502c110007803035165030250756007420811100d07000070b042c144202e0300c8643d0140c4039426075000d01d90351145405851142c0c1900180c080c41160b = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 223027832 1250 223026582 223026589
    0x1005070c0c140a090218100e0d1a010b0309060112080415021e03040f0504090302010b030609070e100b090f012a020405071704060e0c090a0903080c0c0705040f0605 72
    0x100068600302104400304480b03907040000868850b00410701e000d2041240c3c4025003198045039007000d07026280d2011203460650103a0310304c040041c002c0c0c1c0012100d14407904101c64220307450417440003401c8103400c81c3d1301e60400c20003600045800b6001a84001c0052088a0fa0000d030848060700c104000ca25007925004040c46554002899a000da400004100c8485c13601540802e00c09920388000c40c1010701d4140b4201c842c1090344141c0b406907541d20344a405042c400e400c030b0b0501c1d1a010b001c5800303904052810980d13510321442103908144414011441810386110b0343c03c1143c84a400080c2000700c030b002000368520348102d001d818058041d400401c024072200c1d10280c1c0119040d43d6103181c2d41640144820707544020941820400d5411002c421100c2848400c0d8000d40c221100048009031408403e1030200b03011050b9a00144940030001184116080708060078401d81c3e421a440e191910345950500481100340c0154000502c1401207041c913078840010030000f01d40100b00301e40d464010 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 223029082 1250 223027832 223027853
    0x7060903020327030d030f140f090f010b09011e080d09050a0b0a0503040b040f0807140114222105091801030201141c140703060b0c1005070c 62
    0x1100542c101148109000e030802d0844801d41407a501e001840001c0c140001e40c544035612030705010325650301181d03480324110780d0000d5596240c14802e112a410440d40f00601080304881020992180c151880301c1d207403040c000d002e07904070060030318100d60b404c1c162251018040507541d0600030402e007800048104d41004249940e801c26101c0c2103022341807409100c40310501c1c0e0406d4030090810007041200b107a0000480c3d030b200750000300f2032515071071f40d2410704103406600318007921000e8041101c4041c007820701d40503c82400c0c07500003009100302d0b48107011700e1120300322941c02d050f08081c42d000050301c0c99080c1400230365204406d800048a00d40c44008500014403091000040003c11560202c1c02c102e444500000442d4690413002d624550000b082c6039030307007110009124004600f0180310078101128210042c0030341418040301d00c40706400ca030030020441d40fa600007820001c00007030344480391045412104800300034040da58040c2c1841d20103010050039000401500c45003040114071031856 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 223030332 1250 223029082 223029101
    0x40e0f13050a060b0f0105070803061005040803071a01091802010807050408060915180606010c02040f05070309290c0304020a050a09020403121412060a050d0c05041a01020601090905030706 83
    0x20001341e203402c3c0d500b07118404a0400c1d055050020070441c1c140411030b801c3c1a20360002c000c440d903c0103954a04011182070185500004441c880030824400b08004040070b12001d00000b600070603640c0e40d0322030725001d8072400e110100100d4022141000503512411805a100385d041c00c2903403034a981c540c4040c1c941801251800003680180800489a598050300c20760848a400c11184900550b0501c0e26100c50b406005030341800504244542103499035000300342681d413083c808018524000c0009005042d981404031004034103a424040f502140100c0031102071141d406610041d0349003101031407a0381c00680283d034810100c03e80080c9603500c0d1080c030780141980e62005602e440c0303940360403265514003030241024070803140b00c200c50399456801501c010040760410140c0f19100c44010a5000c4050f0304050b811840e0355880609004a100c11401201e034195010000800f10030038003840302d03480303881f5203006820810040044a805030005c01d0600d000300d05480c60301c1083c0c0d40d004101c2d050002e = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 223031582 1250 223030332 223030343
    0xf150906040e0603150702060c0a14041203020f0f0312090f010905030a0e040605102106080d09090204030809090702030f0a030902010f0c05070b0c0a050102040920040e0f13050a 78
    0xc2c100a03040c202400a01300d0019180707034540650800a001a40711b100042a525180744045040d008162040702c0d40d00e4220481d125140d07459864240710030940040d010207402501c5003a400504012000590504405021010790705240c440010170080840c044d014503264800d888030f4841c6440e0030303ca281c012a1160b0011581c2d000e107100c020f011385468106041c410b81c0b0b0030104002544503080c00d041c5460039494900d14190682c6910140320040c5038035000241d2a03c1d1001c0358801c030006c1c10b880b0101c0e0035100c90a255030750f00081410b078403079400014800c0d941071280ca821420000c007a40d8105089006036420041d0501181503160030a100040001c0c3c1c03103400b41815035030418420090210b43d441d003d001d0090039114181c2d25286886100b0300b6900010741d800c2004010301404003001d0b0320200a5640c0d5603116110b10190203100308030308554241d40c1490000000610072a4111941da00050b401c1c0d590350003900000b9800200203045090241e0003180004005001c164030891040 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 223032832 1250 223031582 223031609
    0x70e1903140c120d02030313020d140f010f0e030a031d01021612020604020d02061b0703050102030f0c0703020a080304030912120f030207020a150c05030d021e07020f15090604 77
    0xc1d0b040110302c05900705030b60a10f810804001048643c08811030b0f90000000140d5041c0d500e462010901c1e021281102509541d50a680c500490401181294040390204c2c000c4c000c01c680c841444080310310a54482d0314590007044032040050081d0084000425488601200d101600c862142641d1106000201c0410102d80c49010400c919036200c4d0742558604c0244114501540801d0500008541c042d10074400031450114902902ca041e44106031403c2c16100c01c981c0d00c0c07400d079000c0e404c1070fa170708005401c6000c00220350380c0342d840039103a885030981d00410b850b101035103076150107a001400c243c0402140007070200300070040045010b00c091040654028050390444000c241d03000d0f100001d0105801000341c000035030707104080701d03081c0c0310850301071b40d084500c0340010b503200107100f5801443e0340408281c00d104081da65000d40358100040c0c9160400c82e22602c40f03480544034205000794481d60741ea90045071030800c080e002408034245500141307486260800100302c0e810a5106450b0755820b0f = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 223034082 1250 223032832 223032853
    0x190b04081c1e18110a0506160209010801110304030305071b03110c0301051003080c07081f052a0c10060807030302010b1c20040903081e070e190314 65
    0x44040c038541000b0140700308001216058884200d0a0000b4040d0614106820048455940140714402854000d140582d284041a150700d208200c5160583c498074121000090040043c0210301c02401510340f03040c41d517035480c0e906400034400642078104003c80720014025641c1d441c882844114065180d1925101e400c42d8058a00034000290a00a034186828444c07004186c400c4501601d0b802120661540e500d41107261407d40740317a112005a104101448200905111006254409044090050b941d8803d0211000b8004403a050041c402807030305520020b843d90064002114400c00343c0302c06139807200c2000c00f62020b54202014503000380100b007081540900c547e641d800c8083d90b5882805988074042e07030000c1c100d0034002e010610000703400c0c4039140580740c0407022400c00801c200400d5003107060003042d0810403510000103417042e400403150300460600052141130303165070b4200090291005c2c070031840301075006801240e610795004400140085402d10400e0420b400070200d0800 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 223035332 1250 223034082 223034111
    0xa0b090105090d021002360307080a050616110a05030c07050d020d06020c031b06010609050102010b0a0303260a020c0712080702010818030c0a03030e190b04081c 71
    0x4010705110041e83c0001103036002a40c001ca5807003007921901100507150b07000078500340c164007858020301d0321b9140980c20002ea142540c140d60030485d034040d012907110580f11002507540300b8035090b02400950181000895900c1026214101d803603151401c00101080d525020b842c0c2640d0b00c000b26929000481c91300d4105e070080100c18010f001c110340c44c110300c1d00980c0120703400340c0711000c001d402580c0004042c071075540200101d40b1007071402070b1414001c87c00c00020036180d14003805a400040c20380600014258414007074045c8104c402001c0c05000c51841e80d00b50382620341c1c04028170060079602d40200144803c41c0d01203104080c0c5940c0540d56500491003a410034840e41c0041c103002e1b07264a44940414444001e0300c4110b80d080c2090700c025212084161080c0c8040114100680310010b11441642c07004180b40c03a000e4400d4606000301b0342c3c040590303030711034080034081c9400d140c7c14480d041c0824400c1a000760014005c1d4102c611b13040310074468581d030100f00c1c00350f0400c1340d4803800800451030 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 223036582 1250 223035332 223035341
    0x209061c031e09060801052806050408121213020f060a020303010e060105040f0e07031104090e061005030d050f0c0a1406060901060f0c1b1401080f0601051c0e0a0b0901 74
    0x45162802c03a40d02130909801a20314007040c000c09006150301504078502124000241500f034018030b08190b80c06607204001080c1303038403a0203080824043ca90414521540100036100c01c078200d0720104150381c0e901c2081c50883d010000083e0f07440400c07499507400d15101c00f80100700034069680519a41d41c100f240c460682c0c1c07005040241000401c00040100c01da01c040c0d0032040d20140098002907459400e022000b50803860700e014240f01c000500005c01640d241c2c090545074280e07405844150fa0b608452480c12600c03481480d0b0140c005501c6403500910420051400350141c116842c1030907268083c080c641603001c6011034031504102200310a030482040301d5603100c88112032051a07981000b0004042e070203144500010310448503807230000c02152003040041d20818959290403541c0c0c030000b08510410a001d00c134049003122000c200c5503130340005031a02c1028103848844c40c1c07603000300f41c2c0340101c603c169410559613036a180384c1174111803e004044469000e201c00d840603040071200ca5003143d = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 223037832 1250 223036582 223036637
    0x1308150108030306100309020a090c030e1c0f180f030215070302030703210c0e0f0102160509100801020c061608060d02060d0e0303010e0703140f040209061c03 70
    0x2550010010440440c00004a0340d2051060b02c403039404000c0f804040d0050028024000d60000d0419004981002982e0065134850300c160307802c0c041c0d07008410101d52150240c20300202ca1108006005607128001d401c2504c0c03150300d13844e1401210b08024001440000c0c1600a002c0003809004200203500d413019100c00064056030001d450310f220717954065600e11640000400b400030340c9414a06045c040003200030b00303007400070040c46640c0ca0b2981c001c000d88494088140f240040c23a90807010f07544001400c10101000d1400ca2004500707100420102000040184800d4070b205940490f200402f8006090810091402007823103041085c82428015014014071040104000401c4200d969010748100c1107501600c607140c0c0c40a0f82d00001001e400380e2400701c0c0c0c40744800400000c1e2035100c8001507206a195950030040000d02c0310802002c07402c107951003030302309a101004c5009850941c0070030303400080080c070f411241110071060b0020343c02a20740a03030225440c0c03d8100014a6a0f403c0c0d4210f1 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 223039082 1250 223037832 223037863
    0x20c0307080c01020106061841011d0108010b0d110a09050a090504020612150d050a020312030f1504180501140c04050109030305180909060a0c03020f070201030b010c06021308 77
    0x14800c522803180450311300d80c46109950030b24a61201070318a550b27961407003080c21024200789041c0400b080141c40b03a2865940c14001003180c0126241c5140314011808010300503524424030381d00c0c100c0000171981040c4051300300140c0e0340107080343c0b41030305000810341c58110f0f803a2140224604000c010400815a0010350014240401c100040e0341c7c0d042165200c08030400700304030f00d84801035406441c10b0001c07401500700320310451800510500058122a0500c224121190a0b90050403243c00c2d000940d1540400c003600c1010500700010310050070020702c4050300004401018180c000b0b1a445400001c1d95180d642d00307203c1350100c84041441d030b8810124004103142a00e0800001d011084920002d01008030108089a0a076100710300c4d030000900c010007504050a140305000d8503042e00342c840c41c010924110103114450b01038001c2d01c8070307903294103512410405a900158040d0842c419010f0400040300880c0340087c2041c03010300301060518480c2084a801c10780110315094001d4103040300c = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 223040332 1250 223039082 223039097
    0x131d06011a180d03020a080f09040608150105010c110411030105040b04090506011208040f0303031e0606091403031e0a0e0906060405010c15060306050a140402010915020c0307080c0102010606 84
    0x81c000e01e80c02a40c20112002e441250002c143d904040741003550210008014020001e12003600d03609010160601d1101210104031107130355005007641c0c0f0b00c40314500d00102d2000c480100019800748000344246401810b0180c0c0ca60b801200050440700c1510b40c69462a40210050142c0d0420344103e0820010644d8200000016512810742c0d038078051060804d42039403074004030b042000050030380c3c00a2811000e81000c0c96180c0c500500504142002c1408003400003c7e5a00c02c100325015840445695440300036400d814940c0010070b081592440c1c070b80620081101080c40003062500d00c0f080541a8078458079141e2843c2d00401c0580c4804500b84201c01301c40c00d100c8640e40b004119400c84400f420009e1003510306d8504081d0854688248030300082c07400800006028254000034822801e8000800101411403610028240203aa000e800100a460140b00d80d4440e01075041c181082401140d0303126901c0f500091a00040c0e0b0030450135074004816250295030240a50000f8068030b00b0301a0 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 223041582 1250 223040332 223040347
    0x20a14161d04241112060d151109030a0c0602061b030109020705010b060a120605060705060f040c082b0306060c030c030320120c18131d06011a 63
    0x1562400050406816600a0600c3d0f40345044a85254200c52210b5102400842010825080759810011003845000600b4000440901e05800e8040000354082c01a107429001c07050800002c1c40107003440c154441007041952080e90f001c2040501e41c43c880d14401d2000360400310024109100a8034540c070703501c1042100780d2940c450f103043d2410744a90140041c7c0303600c201d041c4076026215880c020740e0811400106141141d03402034800e0b049030a1038405004140c5d403103090001038843d80d44041c040ba0480c401089d50042c0c50401c0d180c02600030942880181d850b20301103401d04d030350300717079821100c002c07184020500c51a9801c10f02c01a100340e04040203454a001809081c3e104800c0009042001d100c000904044c0a980005081039051050128a0f29180c00440850b4401c1e00307802c003001d001500185d490003000c4116064425000c0d414540207809009024a5468404e0305031921034407a0703420303c000901d403004d0007092801d45009040c907501d002010002c08114400700d1210100c10007118 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 223042832 1250 223041582 223041629
    0x1b0213091b06140702010c021908030c07140901140a09020c03070303050c071a0c120a020d180c0504090f0b1620030702010804110a090f0b220b01020a1416 68
    0x1d44044da020300b08907001042910001d2404d01b0643c14904910040c107001080d01c10340003014298090105c01180e01003500d42c258000b4000f40500141e5000300f84070f00502044400c40281242030030301810992002ea15003030400160f811142102d480c0b54404142241416490b000300c0c2d42081c09120140e00d00200303600c81c40e070304c01d103468903864040d2900c6e000328015001140c200c4480601c1034610b8101030400e1054200a0b6016403803004a090410103241100612003902c0d80340c1c03039440005290701e41e14110a21020f8003141d04150303502040c0c14010400b1802c21005240b14031840121003c108580e81030141480190a180e0074980e400e00107122060f41e40041114022a02403e102080d43c0d41c82c500800a441660002d40d00000603c00c0041c80b00c000d40c0024507480059032051222800d11070030300c119218581003108400d0400f40c811041084584d110003260380061054400b18903041d04c0700340362946507400044950340320f119802c400760004603040018000307030340c4030121100803036044 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 223044082 1250 223042832 223042837
    0x1180f06050c1018151b03050603030d0207080403140d08070513080a0506010e1602030319020f030c04030c1202130b0111151006030c1b0213091b0614 66
    0x448060240000b200b102c0700c2410804201e8140c80303c40d0a0046404640003100c1c501c25404003124481c8440352105031002e02030060111020758030340c83c002e0004000000314040c040180c1402d8241c0001c0001e5a540c0605000030100f0a00903500d0030750340d519600d40202c0000072a01c1000d030507000924401d59082c0e2080301150812680c2c42e026072580301a200c1100c942c3c03202e0303018032003d200e0300085408100000c50801d040b141103940900030b03595240c01140d841501511130386c0044e002040000d05044e003a1141e0480342c00390704c10060502e1000440c440d4260b02c2624a0000210040b404004000d5224208006800c0c8900d41c2c41c1c03c01d10540c041781600c04076081401149885201996036640b240882c80004c000e00c20072202c450641e00d683c80d030009407d40c0c502100104613000841c1c50f9000f400b400b844110503640e20058a43c1742d05980302e0440902130101d074894142c4030f56080b41403250081e8251680a00c8030315802d0008103c0c40301043c2ca2580c485014800c65440205d030701c4a41105 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 223045332 1250 223044082 223044089
    0x2405070c060e04021b011406010e0f090a0204080303070513060203040302090121062d111207020c061c18020a05040c0207030803130b0106020606150a02100c080601180f 74
    0x344111038080410010f0040d0198107041109a59800c4035180d1414054000c440c0c4c50a501d4801c41c4c984d02c84100449442841028094100034004214182402c01100e129809120743c0001400c194694054900b107500690341c0d4000101d0100b101d00300001000c01000c010501da0005515113817443d808905030500520a14400e000032031403001d09900b0456540e41083d500a41c01c00c11030188a0402c155038019040d800c032521110018054206014821070245c00c40040b401400c04015100110051200900100c21030281404001c69501e0f50340240818291401e40c46801101c0e10321403000321000004200d103035a112040160240e1110592003056842c191000705074182581d0382645024001d03880240030300000410070030300c00c2072040600d8905101e201860056640c0d00c1040b0391b15041501e0b50f07075001140d00f41c6030014000440082203645030301e0050350020514844008121441d00484002055160301081010340e4002c5428488410000c03542422508014001d00868400d00 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 223046582 1250 223045332 223045337
    0xf0608160c150509011e0e03090d03050d050403082e0302190308040306090501060b030f060d0c0305030307110c03011a13090b01120b01061704020d0804050303042405070c06 76
    0x501c0d82052000030b0801c0c0c825004030000c184201d090224100b402040c00100303014903048090400400386030b0700e0113207c03a2030390300000441c1800891400c1214001e5412070840a00004104101c2e8040f00e6015841c4118041c2c1c46140c2c3c1c524101c0400400b0300a06a00c1e0009504502c0c00030401b05c1641e2991001ea90b0140c4600240d500310040c0842c0d501e1081d00058240d4501141c0003040180a8214411441c07184c4024045980c0e24142e44070680400d130781286925816600065190804c002c1c039000c050f0044188404e001c0e43d03608c9850440e841a14084001812407000c02c0024004002181400300150000c00405129400c0c40181c840004031444c41038140850494401000b50001081c00381c0010345900e240d607440541503d405140a41242e80a0004000041d85401925242a06456a44c2d100c100da07581d03900f0071003600d000d60f4048461030400d00c404281a00d0400250018000452008550b00451a28004030302242000c41301004410820301002a06030b0140b941185c4160 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 223047832 1250 223046582 223046597
    0x403021c21050c010e0109020a120b070302090402090607060b04060e0606070f06020405060a17070203040b25140304080f160e090106180902100905100f0215010e010f060816 76
    0x454007141c2c184922101c8031403560074079210040030041984000c03500d61013155200b810660341c1007440c40c2d01c1080310300680300c500d40c0000900c00e070740030784c005160505000340014070304030301c950020320319400144082d00e640342d803041501443d08082c07140c0e4010740180400c880c12443d25000290040c890300794010035031003c0072100d004112160701035401815004040750749806c07440e000288240110040c0342c88103e040804203142600100c112004d0300c14140680c0d2070101e0901d010007180e460204040051b0f4070a440c0840454a8148407a1240d14042c01841d900e80c0f81807205454444030321181d20b480c1c0c010600442c20300142001503000c46000c0340f03180109a80c1c041c0c0707050040220390b01c140c0002240c000c088400d2072855011124003403003180d0312820b01c070314880c080754280400e002c2c042e04840060452080309028001c001000d40c447d1044600e29601c80004030200b4802f0b03402050024101d00043c0551340c00c4609400180c10a482c11341e98601d0314015603421350403030005180500c80003 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 223049082 1250 223047832 223047893
    0x6150103090501020915270306010510020c040c050d060f05061603091503020d0c050711040509100608030909091204030611070203030a02071503150b0307030915020403021c 76
    0x3901542d440c00300007045100ca140802c80215000d07130001c410640800482c0301c031f050300d04042d080701568400004c1c00510250303007001c0503c29800107400488065110f100c5000c0c64980c1c036402580b060599560324191074070541c003203d0064500306d80000d600340180c2502840fa5031581801da0780001403049074000300302e005060035101c000c1070b5004803544400c11000c416034140c1540040c190004052010001101345020495a0340601c0380c00500c0044819032003003c52505401040e00302007806c09407507109880000d0481151643d50100b0025080410008080e2a003940b81540c07283c00240940700c00940b00328554150b10075400000e0030f0507034640070242240c1011046c0c0e0038181e4042c040366594110743d94040c0d50707803c0c03c0c4a44010f07089500601008248613008242c451850b81e681106d245040450b05400f42e00020490000c042d0360303a40e080c0100d480320100c04020000100700695a5085005201c10282ea9080030440c407501903034000c000900c0804581103104100d0080c1246040 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 223050332 1250 223049082 223049093
    0x91e020102280819080f070804060c03061815050906090c0a12020c101b02120d180b0a0f02120103151b11160b0a0f03060b0301030b0f090615010309 65
    0x21040c0024101c59804240c049214201303c210800307a4156468092040d0786420040108417412a0764000207458036000c01d0000340710390465902514141804a4002c1d1100b027088020a2030000030f00c1015100c0c40e441c030884103c4081d80016000a85a1800d5072030010041403103801c003e4a4200e4440c4001141307031101e88600300c05c0d519000000410b55440d080107144595541410400540061074000340c22024684d1800703c824810441e00505104030740030080c1041ea400c40740808003c56100c00e04802c1c03448600c2c0d50540050303c54110f02d042e5003020714280c0e0442d5042c00710009510300c10007007803004101c0301414604503a030003042400865070414008000c0c00891809054481d28803001c001a9604134255a05d4001408111040e41c80019026030174010700b07204030a0460f02c10404540d031140b248a440090034401c2c180030a00680e41c23149603019a10981c07090b108a140309040c010501983c660581e088400314000300180d04281010f0604078800000880c18503581ea0600000c120 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 223051582 1250 223050332 223050403
    0xf03060504050c04090506090405100c0e090103050303100f060e1e12070501030b041e0506060412030503060109090c0e0f0d0b090a032006041b1701091e020102 70
    0x30140c818000c500304900050031580160140e83c0505041a0004485040c02c0401a01c2260088020007c8200410f81040100540040c40d420410950302800c40c0780c440e5008980290b20800c0216501e181500580a50101da81c005422610b0310740d408010159100d0202090544211100110841c2d44061b08a50b05414111590000046070902410030404110070084030020f03203060242c0c441000411046071030124a6140c0c4203000340084c44411900e51210380c2c841009024140303421f03101d41100110030020403080780015000001c0203042c0d41d000803101d00804030b640080c044203a03030ba100075008081d03807008180510390709141d41204e907030f0340261101c1c1c0a8201020136000d0500b070b03502c1501d8a9100d001900072a1940c1821030303040f10141c20241002540d00b0240c14180c031241d4900c455403000c0300241800c004218404a1168210240484042d0034800005612a418541540004040c08000d2200d0510701c03403441c090303600411600143c2801c0c0400060400b1883c10000450 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 223052832 1250 223051582 223051589
    0x10f0509040903120605010504120605040c0e09070306110c030714010609020406020f010b120615010302070204022701020313051c05010623060a090311030f160512010b01020d0f0306 80
    0x30b41448503880038550000e01040000802d00800d011240e00c1e50015907462046105007420240700e50418008618070743d102c031350020b22400022031141da88042c5801c0d0800281c032480c00682049804104108040c41002c5c1142c9004131030500b0402004903190304d0780210380026205100700c02c0d800312950401c0d8422005041c00b82e03001c644403602c03048001d5881e115102140895860080e010205191009060300c3c07803140e05008261079995680f99030807180a007100c840c1450b4013803100c80010b82d514000340210200c903c1c05042418502e61000c946d407044030340404c0c1990001c101d1036001c4e010752032110040d982c0a41e58500315188100004111200b6480d018186501c0c104001c64450344e400f05e1100b10300413001c40c41d6050001d8400f0005980308011400000c0ba400480800004003090f4000200c4a0003d040e6104500700790020350030301d02d501e91640310400d08200184241e29042078613503402506ea6008210200032000080d54844000800c40e0902130b0540050220718070907000b21000c1c = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 223054082 1250 223052832 223052839
    0x3040b041b0609090b0402040b0f0c031c1e1b23030108300304120e0a06020f0f010203150108090703240c050a020703060f0204080102030906041a0114010f0509 70
    0x180e4581c0000d21943c02030290703081250900144905a02d040e000b0788082e1840f10000038542003a080b184802035000740a101c05500040c00342c582d40508000c020042154a0b420228105018000d0703180741d08a403040e25080300346000b5a84081c0180d8802d0141c0d03a002c0c0d428201011070f5204040303410b00341d1012041402c200d0000c000704e00d030720000c29180c8004000869112149a4203048a0480c3e0621941c00642c4802031000401083e1004000c2e2054a400d043c1034466100020200e0744124a613041040942d00c492001c00c2c2d100401c00001c0d01a940c683c0c021821428210301020400e00080d91090402039902c0208107100c0b0188242c5d0000c0d40e01c02990800c049001007032003500080ca469070480c40380b40149001c2c4d8036010b0001c569100b0b0813980a03140c803904540e039010042810560310480e01b607091001086001e000d20007180900c1c5041e000784402d2601e45000c3e40030390385102210504040d6000100301621502e00300c2200c8080908009100e80e6144408640364028080a90351 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 223055332 1250 223054082 223054133
    0x1803030d0b040c02030304080d020a09080a0c060e01030603020618041515140a0e011d10020105010f0b0a050a0c05010f111209011116080c01111b07060503040b04 71
    0x40e5000d465006007403030030041c2c03014001552280010b98490108480c0070b82288802c101548070189294001c10b01d40b40b00303040061b4040c0c7c555085c0761411001042c01c680580e450442405019002154400401024a000d020041c217650101e1954000c4000406c5001c8800262030706070b079207a800c8030212020022508110b90b03990201c104030020348100700c501003484d480d5203540724000601214500510b07034880068034031440004407000912a020313060b522403070103664922507541241e11810394034203600104143d41000030411b0344442c9540604000724080002041881e0800c0c00c1d0341b0010290306103603907880c83c80c1c1451405801d5a0142288480c54020903080403801030000d45920f0302d440004501c02d60f190003205080744c40242c05030140c81000e2140d1003100c044e0181540e2a1480f400c10070f8100b14400e1800380c00d40f400c8400140d02c0c29404260392070782880c4002d02517584440403004210390340c54110050850320025001400343d0400000287c01d10288011007604082c01045148 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 223056582 1250 223055332 223055347
    0x1103090c3706091202420a03050c070201170c071a0106030518060c090307090507230f03220b180f0106080c1009080706090f09140408180303 62
    0x216090036028401c00b0418103e80130844100760b011480c81d041c4d0260100c2528284440d40600c2c00102c40e03070a44d4280d03048030f13641c144a540c00480c10b00c80c040e601d0030140c031541c1c088809010760718020204101c11605006400140c0c0c1e0008030b100c2113903110761b60b040003030301c4a0131446c140b80f0403490081c282c0e84044044221103c10741031503030304070303006c0c0c1c0e804000c80c2e240e405c00d14610210f4403810b2031042d07100c107000c1031182054200034050303104000c1c21120550b6a0b0070303800301038800c104c0c2c440e00410f40c0e15010b01121034038164940000d4280c0e59a00d485d01e101c18188600501018120142d400190810380b0600004500000101c81c1c02c605414071501e46960569000d84c0c641d0024072840c010610800b4400805001d0841a01c08141c003401d0100740714010302c02040001c201a1080114020300024441c5050011101421031a610320001a0400800728851000c031340c0056202854901388600c00030715942600d402660100640750360b4a0034003034030345680700041c0341c041c1c0c140000903540 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 223057832 1250 223056582 223056679
    0x30705070b030f0708190203060612040506070e01020a03050406080604020d021206130e07030b072a02090705040803090f1f0306080706090608070f09030f0302010c031103090c 77
    0xc40c4900c0d024000368007259680413045807040c0c426128604407106040d1145c6610581d0b070095644400003506803070618100c50b000c0f00c001c01d0151810380d0345070481c0d41400089544508403494120080c001464041c0741b55800070f11500c1240b144204101c806400300f541399a850b01150000d9486150954031100002c0d28411084030980e02c42d03101d150122620000c1c40301600600ea8031801c3c6802810410346980c030b03082401c12009140004100b0b403583c00348e6040d030000213500015000b461300010071144510600a26410142000f01071002c00e2000f00100c0100104450b850a4190355007101c0c903141030007240000304a03408120002a1803840c04040503410b0f0b01030f80403a0002000c5890302c95071048203850107041c5001c0d1600185040002542090080d480d2020700c00c241c1c90804055640c03034460b41840080c16108400503511000800d050f03d41c94041d0000b10528282624a1410044425640c0707840d03145010380180140113040410001c2d0000003004840d0607014007417000b0756041b00 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 223059082 1250 223057832 223057837
    0x40f030305041a04060b13060b0a081312021b0102031812010e010606050a27060c110d08090f01020c030c040905010e070f1d0103020607021c0f080301090e030c03071103030705070b 79
    0x1130a02815440f01048032487c0c041c0181e400f10b40c4003081280c0ba00c42502422103000000402040c1c084080c40200300c000741b11790116040c2e440f065401350507080150301c0354145440600404074119402403007026000b00d05490b15070f00341e0f2400c03a41000c020000e04511405056100d150003d2540f03060781c00112950400d00038020b41e15103648100c0359820846d03942408802081c50700081e102406d40500640780940305030900e0b94010b0800c66001c6a04000143e0400001c45044444c2800425802c506043c20310400c0d8030307a2000d0018091956204010944c0c1d074110310719041c42191103103450000d00001b0f5101c00320302604102036034031564075640a14410f4140d07218520040307211401c03010b00385c44104c890f94140e81d80101818513266040d000c12824016070f03010550745410030540701300010b40401044050b82d104410302503d962401d900e91044442900400c1101e400c10041140c4100c804003c5a2400e80c0c41f00b210660508038401217861401144401000c0b44940c000208602c03400c44003 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 223060332 1250 223059082 223059101
    0x315030123060a1a1e0708070501061d15060a050d1d060f01182d090c050307030215071103030a021005070309021c02060d02070807150203040f030305041a0406 70
    0x1041e00707503160b643c0c3d0350b6080113051000304d5107102014860820b0b44c003400c9500090158031407801900b003454540b5030310016440303803100311001e0790354407800c001c03c581c0030380b00142845042745010078510b0302160650004e120340010034403a00c8009040644a406003090703502880b6254000c100c7e00118440c00440808448107a05843c0321b06000901c110f101c020030f0b141607a50300ba2100009041114115020b880c40e620010a494915010802201400d2959020301c107103011007c0740070b2086040144a2803a69007003a4081c1e00003550502c05038072023108034000102c4c00d802e0265500356900348508103e05d0303411555403600000911190581d400548a0380c02000e0f03040400050300c81c14001d030110365035130400075046450740101d0101c070b0241d050682010f0380040d102503d00360b0001340a034100d03400365004450742c00d070200341c6109200c1c1d80e45903000031700e8070b140b82180b850400341c544010305491403500804058032200084d04008080700b0401c500c07211808a00c2990a0510301030010708804d04 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 223061582 1250 223060332 223060339
    0x30402030c040504030906050f041802030a0c020318060f0909010806090d0306050d080a03060f060242041a0a02070204140f0c0c070302030d020102030118020f031503012306 76
    0x209803000380e2901c3c2c402e0502450b815222001202e103005c0d800d4030250000610024000d1080c040041c480701320b240194a55900110300590724035250303051400b10b0b0080c2c2030042c210b5109200c04464820180e03500c0c0e105035021211251269900701c0130524900c180304200e90080107240c0009840440050f20a001c1c82020060342c45103070b41c59000f1070446006114196202d00c070009000040340000c00103020101c0310b407a000c1100d039192170074601d040030071b94004001a800701c6d08059a40441d00802d031060551991a102c180324010310305901200d83c0f40000c069036a012020504000c2e0700c0b55202071070044804100b500303141100c0100c00a4010324026800b81e070408003080d600800300d41400740b20b407ca0901a4100c2d4840010741101604114007111007885001401700150341e08102c1402000b9147d400948d4940c10048441303a807100d02c101020900d40140712030704040741c40c1804e881e40300701c2c054a00ca000015078030020703000d460700000f0210050b03041d0040980d602403400c0094407034403060f03 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 223062832 1250 223061582 223061593
    0x7091a01120203040b010501110c030604141605090403051b0a0309031707050604060509010908040b030117030c0705090a0209090f0103050706020a020f0d02010e0a0e0105031b060306040f06090606030203040203 92
    0x41c110201684021503000349200d203030000501c040e41c01043c807450001007580032035030403181280201e441c00d030060354242c40c0302482668541e40c7c00b20130072002c3c800c009011203030f02d4a103140070080344040001a0005041c07110108016055030000d0f090883d503c152401101e0318a412410301070030b000c1460000703071000d41e0046101c21070300403003008903102c20780c0c09002410181c7d5071b0780300e5070020f0402400b148800c5d525040a00081500000684044e0003034004060360f075407601080000d080c0509106031540d410601000091000208282044410903200d881d41e950b60141048002e1095000d0264454500d5040c00f20f113003c0000c1260680b41701d4812a2071031030300d030481640d0315202214007c0d030080e040344900301c0508164004144451040c105100600400c81c006003100a04d17030803800c5041045030040005140411039440d520903104040e0550080160100e01d8a120040800303019586680240f142c0891a60159009120807102004110384401c0010040e6205403010380c864880d4 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 223064082 1250 223062832 223062857
    0x1030606090302181008010c170109060503070e1005090403020343060e010c08070815011d01090512100515030303040f14060a0608190803071107091a01 67
    0x4441c01d00c2501e4000b006045140900c0e8591400028001c1000380400710b8842c000072960024001c43c0800070903515840c0300c100c010070303042c0d8147c20140c0c40721303212900f020420090303034801040c13900a807144942803681e1903135011401c0369100f000d9440590000c90000400090560107c05030000d881c80e042d8002142524181071040400040700c10b440e2080c181c144510200050b800c88010f41c2e01c103103070200e80c2c1c402c070201d5242124126458000840c0c2034004204400e94461f04440d4049100c0b0b0480340700e15409400244511210030006082c01148a0300100d0f03680284c01c0304000b030400400e08843c1c1d407407210080d0345800341c481d0301c048240e00380000b041140043e840e0380350380e40002034001c5045a40360b444a90040c0b100d02d8054801c0c500349504111f1840f0f080c00740c640710f403d900c13402051241c64100303010310b055102120002c04031002c0e0381c1480000c41e0b0310304482e003281e0140307845000710f013500e20814209000c41d0f00440a4624105282c0140103144168072a42c2c142600d450801019 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 223065332 1250 223064082 223064087
    0x180d0b0915060a090c0c0501020a1e030c021b010e1f0e01021b0d0c030602030c04180b010f0e120114100f0311040510030605090c031b0117040f080d050601030606 71
    0x82030b030b11580d2115032000103200b450050340c084029884249045110306a280d2502801c83c0d001c40b003981d000070900c00c407aa1402c050300700c0b405d141150514081000d000032080080d2202e501d122081c00c4040b5281400520b0ba00c2451204400076008020036503000044c0000f4042061a960344804110104181c0300250f00200d8084400c210b9043d108281140500030064000318020003107850720908040480070401c0ca10207148101c8221007070641c0d80c3e0411401fa40e4102007415400c07405410b040f80500640d90014244c0050038550500c0b8110100345000900b0f44000015000080d40c0380c00940d582c1800c00070280d6015803562804070b03c0c0f0a448a10010400f05e20307001c0500241100a100500d40c01d055118541c0100102e19200c08130b81c4940e1740c0425104182c513a00c0503644a0f9a984640c1e00e420701c924a8a9000c400003900180c1842c00060400030781c16070892750a000c0300700020184007202c1144c156240e4804a6196510004480c103030040006503042070020b450030710080b54550 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 223066582 1250 223065332 223065373
    0x1c14010f06021e2b022a040504060b100507020906010503070804030f0219050606131a011412010f0f082103060a05040c12110307080705180d0b09 64
    0x40c801e5014120000759400085030900e006460b1805078031078088420413030b195510354448080240e011034072110290020091801c1410081591610703030481e071180703480a2000c00140e48020030350f00850789a66a09101008040d2046019004522032002e116860380c000c00500e1114402c8a444505444100c011500c60204480b448082000c0700d0208010a00551096400d20341500c1180c2c0002d41c00c1007901c0d040c0142d100112010742c800c8040c403e8510b03103008030340d10180c11074004000030903481482203407840c0755240c0c89040c01f00880c540071100403110304407070041d4a030301840300702940e4401d00002c4c5400284500d4030074648607000414050304c00f003104824804010605441429840300c401000c2e40040c3c65540c0c040565640042e0544590042c000c004510351105800c5d00c0407a401e000550b80409000012041c00300b041010a44d0485950340e004045440c0030340d100d14050040728400c001c49100d0780c3d0300a0204d85004100420008000e21a055200660300b000c46186110355401 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 223067832 1250 223066582 223066589
    0x18030203070308101814150109060c030e06030906040c0902120105100e0a0906060201060f1802071416090f090b150d060f0c090501180315021c14010f 66
    0x503002044008007181c480e42e411030700b068503841448046691280c8100500b2403801c0d070580c540351208a0141d183d0940390300968003242d100b103004104180400000c00e60907440c09020140030f01e80d0340e41001d00d8400d0b910002c43c200b0160400e0342d6801c00c00401075071000206c500701c2da140010100419400000e000359041075181d511107024070b0f401c2504114820964030f6107401003002114054038a43d60701805034005040040002800508200000342903e030950807901800038841c0c001c10055544403688440c0080da80300060315041685003c0c01c003007240b1065401640300d4560710800c02d85218505408aa201c01020020038046e8042a41941d14102018280042007800596040c021040c0c0c01e001c0302000300722601040326a0344207400c55180000b08550140e070344021100710f54005400700c02400090800e075075500d0000c000d00030300a803140001010604000c0500c040030030b26406413481d40788103550000700c44204207400030041c004180c01c2a0f103900b401c8000108919840d0804c0c095 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 223069082 1250 223067832 223067837
    0x90603021002071d130605040b01090e1515060403120503010801060609150c03020c1206010e070305010305100e0102070816030915050405040e07090c0504060f090e061c05030301060c02041803 84
    0x30400001300c91000c00010000c42d407440f11003140200280840c41110321440c401c208458055049c00c00090449541e01902e14603a4440c0803110013400d17074002c106902c00e00b80c008000903c0ca5078804600240540d40c00181b00400300c00811030750641100c00780d41a544010300811000d80c0e61401210b802c0401d00c80c13030406018950381d01140903c200496408a0301074011955102603080103c0d0103550544482062034014100501240d12001001508000c207450248615411038603405d03254800c15241200c150f541c0d2406a00c246030a4040d80d10b41500441040c1d200c02c0140c8030710152101d504011000214200e00200d91a0380391204001101c00c035545030350415040005000081003000d120f504144107492000a5102d03241c0181358032240c456a5441d116450984047d16080e6940030182c00c2c000250014031445185042c4241d2000040b603200ca0b10001c00c060041140d07091420152243c0000800850802d1304031f00703050500341c802d540c2000100c0c6035094090f120004400d00500 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 223070332 1250 223069082 223069109
    0x40201050403020d03171303030e0c0a0e041a15030f01110f09041b03090506090c01020a030c022106270307020603100f0905060429060f040e0109060302100207 70
    0x250801604c0203010718402d0401d604c50421050801317845110031145c10a2421300c243c444401c1503032501504a04030842401030038408030030400281c1d4184140a0003c82c0c2901c54005024025100f4019030300032141010189182007020405416410740111207009100b0600a0041c143e01440781ca42d0354411015074505105400103a00c80320b600601001c1c0d441600c40d0103850040c0c10103a80f100e000b12003510300086809007444d0150815100828107070450700541404180342c0d130082441c0381525407600e00300c403001c003107480001d2806885c0696220511940310118039108400103c01e4010001c903d1710700c0b80d1714840b8143c01135150001d904080550014041100181042c901942e08900042c2000a1042e1035910316418100c0a070b11140041c1d44840c1440711609040c41440c15000840b9400340301c03103480c00041204140310600160040c0000070303035441a502c503603098070050000d850126906503500d00c00d510181c0160300040e40308151030740c403400d24140001100d0003103510381c0000b6607 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 223071582 1250 223070332 223070339
    0x90b131410080106030b0301061e03110d0b0a0b01050f130810090302070b030a140c03070e0d02030c19080d0c0c062a081905070b070f0e040b040b0a0b071a0402010504 73
    0x30086c22207088031a8242d0348860380401c07070190035904041e00c21380546101e50058550700f480d800c9111803174081c0f405403018a4105000c00e0000030510350002c8000c40c042002800d180c012181d0340b0848840d00103401020840342048008884c1c001c04540b001ca00f203d01155175105100b0885040483c010b02503030200c0d00412007146403501a41c1d10078a407010000f01c1902c60350380c460340350904803034041b81483c00004101d5111b4101d41c02820041e02940c4490413403940e41d001c640e6504401c14050310070000c03010883c0e000b8a2a9403040050880e100960300b0903200d41d50050111011903104a0b46550890404103c00307210307003d02b0140100c0e109000e16041c600c9010034201e821046001d880c0480300f000707240c507411100340d69075600c50200d0f0741d0690303184050b05041c00d0071030019291504002c4420480b603c09544100f2880c0d100100b201e0000b0701c41141030000c0d00510003619000e030090342064001400c0f442800140c4061405407800606038202550b809080c11011900280491028003052 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 223072832 1250 223071582 223071587
    0x4140f03030601020304140a080105070908012702040209150d0906050c03040209060603040510150303030f06060203030121060608030c060a0504021005031e01090e0709150312090b131410080106 85
    0x7912a082d000d030091403900d480e400e8807400d5881c11110333000451020041006441002d10419803850110b0030741c2050040c0380e034100500380254460203407080c0e030003207a40740f030075680e8242003c18241090403555482c000e8480440252115a400342c0b0410700e04400142d040c0c01c040100da125950050003031400d662403404105d103a41000c1c00c241c0d040d10034a07008030101c03042d80c8500c00340c0d144028041315010b8910b02d00103054618100e08192003e0400d001040103a03000415a0b0540760032500c0340b1072007000c080748012400c3c0c840070003500d22410000002104603011008146401e09102910103a0759811000d00540b00e0a480c02504140b109a101040600c0340000d1a00518002914012001950040c0070856401c0e00141c5d0300d19a02c500c80c40401c1d00c03c010400003888102018403c00c00100c503c091180c0c000c2c800078003081c402c00c00c240c48c80c030310510744203029140c582c043c50303108c200380011641038040354041c00307003091110143c2403850301d030100c040c2001c0d50b01c40e99500e03000c0e170030030208 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 223074082 1250 223072832 223072859
    0x80304030c0317091507030920060c06010e011d15040504030302121501030c11060402060f0415030b030705041107110415030609052503030e010903020904140f03030601020304 77
    0x1601000001c0b2054001070519025040c0242005001005c070740f190003100040705a0080e00f80018940392041b02d00c0000c0c12460b04000e0881c41028049580d007441000c10200d2007141c051700000c1c010074001144e14803000c62018183c1d404035540740401e440c0c0d48000c122840f01594120780306d0f001800900c041d0301d0540c00c5503a009100f0318016040c01c0c2e1030f8100c0351007018265510084d003030b40381c41c0e920305550b171612070360240c03283d2440c01c402040e03103a8500030303120b46c070290010340903c100140802000310740c04100e90007880d801181f04100781405100900905801c1e490902c01c0c000c440c0009201e203024010f9a022118691440f85003c03580d0f5500f2411200307905503182c0050312140c3da000c2c03400c0781150810086000303107004624070340140303821824500140d840c80708001d99001c20044131030012985c101582c1d85810f044090072000001a40c1a20851b80000e502600c107a04001c02c1003145144046c221170100226035540101c0900151a80811138400e401a88144020888210000070 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 223075332 1250 223074082 223074107
    0x90e1506150a020a02030d021c080a1d03180d020f01050702040902040507110f0d08160905150c0c0103050f1b040e0a02130b04031a0712150515030408030403 69
    0x1e0599009018400c14465400042114001d078014180203000e6080074002245404041c0c0301609403141205540c12081420850802c10003d00b10001905d1078184c0c2c1c46080c1d81c00d5103250f0300c1b21850300c0d400c1c0d6640d079500880c80b055903100c070003600040b00c1c24240002d50840703600801d80300d81141e00394011201d80c3c215041c241e0b481503c0303403100710240e00c81c4d01c0b60b1405000940d07214102501942010b038607008540e0542c804640c01080218041d6a0204100c0d410000008070f9141d6014080c3c41260400c9440e0071155100406030407020078a07254100400d08600001c0a48149141100064040399401c4030007200c0340c0d4801c80001c02400314102841100d22055200500f0180c80f442000404c0408a500480e461360004e958521400e2410301135009100c10039013585050304607a10340c1c0494841082002561603c0800308a000780150b101d418081c00b40320381001844883c8000201445180c41784600500380000142038080b080c00031244100d40100c621803940c1c843c1d90b001c0300e0742e4100c8507 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 223076582 1250 223075332 223075339
    0xa0207090903031416140c0c040518070605040e0f1306111303060f0605100c08030a090516032a150504050a0810050604090b0a0b150703020102040f090e1506 69
    0x10081100e224451840e02a1042020407110417a8400000d0900d13070130036280701c510500070b004404005000185283e4800d2041d40e0120382034913076030a00480d0048041c1030081d540a0641c0c081040c0d42d002000d0400c0700d044e034281411685030160580481c0030309403284644030001c10071070030101e0166000050100403505c41d8510702503021143d800e01441d10f4108461b810340f1540310080302c0302c503070040b400a07100842e0003040641d943c10010349407a01c00c10000340f00e40ea0100000369840600d90101c00310356084007e940310003c00c10700965000142c0e0000b00c52902c05500c1b540d07c00d025144024030b10422442c403800e440740c00e2640401e06180392841407401c12800b00b10100d01071b1070340c1c80f40000400703020000300080c40c2900540026200e00814050003545401081408151101105a0810356501d400070758a2003d60105061f4070a290100f000b4400002d07004c410554158001c0c801c9451140c40707c1003031900d07292001700340c44909844851583c040841e041080c0c05124080d904400000e = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 223077832 1250 223076582 223076591
    0x50124110102040609080c0405010b070b060406050414270c011805061c0506041a120109021c030206060a030c060503070207210501050f100b0a030e0f0c150a020709090303 75
    0x9040c0c2500b607038400e800c214005400008100001c400421500392000c1003210240010740c100645c0382680d005d041c00150201103c2008034100c2e488590100300034210262041c408903510a419200f1a00280c503141c1464030a5910401100c64000f144060454000b01a0140c42124001100c09840c1d101c1102012406030100103000d5481c0c40c003c200c115140800c123007081c0140311a40c0210384004090600a81c203181071340c1400c203109102d01c2e8502c3c81c200d444404591707540e14183d0040c416850300a400488a052600c204007a030b84101415521a5003203031617a0b680d080511008055903c401026151002810704c06240508042e41d4003054501c11a03003100d03a01c800c0c03d682c00f400c0394100d5481405081080b02031100a02883e42c2c41401c0d0400881d250400146c50018a0240e00c10081214008100121214803941042d44100c071413400300d03807130414030318826900c0e0700c40f840d0040d200b00031811a035803003a4032000070707501811040e07009060307114a043c103060040e1004003421030815948 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 223079082 1250 223077832 223077857
    0x50112060914041218060302210103030305181c050c0a0c121a04020121020d0e0c030f15161704061d0309060706090804050a03060c030f050124 63
    0xa8415002c99000e540c07005035081c00c290924508070781104006070b0820a401c012520609030300d58046044610500c0d006a0f50107401e078020041e5282c441141c02c0400c00c05000005156043e0000c41c0140501043c0c000f200403410304480e82e400d4015158000661000340003d0514002c1c03010700320319a0f07144191103142034250303107070070706210290012600707440314154171800e00c0b00803401c030702c0195002e001c6400d46041c5600040c0c809400046d54200200d030b60b02103094401c2c03094040d0b802c0031030303880d0b01840144504c4118030f4a5840c400c4002c1c1c000e100300004c0a03001200024858103120320400e89101d84c1d25040515030100514290070b4080c02442940404513082913404140b03c0c500528002032000c07200244024801750028912185600c1032159840315510301046031400c40e441100021030050b10307d8a8102805a035120701d074440e500350000014080d0070740160014044595040181e101c4002c680e00c00c440082c007484642404200c0890400c8c0c2e1008907411b88402c29044c8030043c41030 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 223080332 1250 223079082 223079099
    0x1e090312030412030615020a150e12040801110406120b030c1804020306060102030a09141c15060b0f041203140d0905190512070c050d0303050f0901060e0105011206 72
    0x40d10100e8161400f4100d04020940c1445007802500041071030344038076210040029900d4600001c06090312101401c020101c000650042e45035000c140184c498640320051604034035001845001031550a22150b9020100da02d0304603400d44000303403503038048010f403100d00c1d000401006001c0c03a0544280b8080160a581c0c0e2407010961440d20030000304140340ca403041c141048005041c050655100740003402d40343e90024040c500361030b004007106840040c50000903d4203441d448059240300030614411050200b800c080c0600ca804000d01400700c03a90342c01902c07016104640944c5002c031401d100034044826200ea000e61628024035052000809a030481c0f00300b540821203428825a45a40700340c2080003e0024290141084600001c0d0408544480d6201c1e0000007807685403440014a240401604000c40e0002e04000b034510885182a07290140080070140c0e11031000254800002e4a0f40c030781409040c082d109003074003115640c0d05c1c1400641d000100606010700031600c0310004100201c = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 223081582 1250 223080332 223080337
    0xc0420160602040e0c0304060b090103080f160c0303170108030403030e040507020a06050906012c040f1401110a090519060819050c09040b060316050310080f211e090312 74
    0x7500d00f2a1030350741f0f0405203032607000c03200800466405882c000303004002190b01c1c0b42c242d61f003031106484040d54625400304140d08119240c407000f420070750451404010300d60300c8101d52003404c81e2130301d01200c01d0340c031004440c0c0e80c0d0250b480b00030b00150240480c0020743c200754001540224a6004440c2c0040c0fa03565102c083e03076001c0f610f100c1d1030b50102c00100440c0002503650050480074102c0b9908400f0403828000300b0040007807028010040d030454440030882c442a0b40602114200003c00c8130b03000c0a101901981d00c15001d41000440108002c1050300c3c2c95460000e88070491606595a40d10740300013620030783c00c001d2004148045106a45400c00b008bc0506032042200c03001b610341d0303640c20038100b0049402000000d07000b00f4040c01088004001079103c402c50582600f8825169614040b040040d8a0036030082025402002c0303440312007003000194030f044c2031004402d61600c0706920b1401ca1031805520108070240c8000c0e40380180c2210120010240b042000d400e41d00d4a075224102d083c2e065 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 223082832 1250 223081582 223081591
    0x40903050c0f0a0b0a0b0105040905060d02060a0201020310051507171e12010608010f03060905011508010b0a0b0a0207050402130e070206070305090106050f01051c0e0c0420160602040e 81
    0x68100c141e5041c200080300c0e104d141c0c4404200c03000c00c85400788100080042c02280030300c0c000d259987e400300d9080e82d1809419482070f6070041510340d4071955084024080c0d00b09903922a11100482000320b4280f900c43d0f2a03988040c0640035003418103c0d02c0d2204d00e805040e080850100501c100503c0000703003081100394000351b111001c1c869a4100c0350104000c0c4410580c042e00400107442c00501000e0107a0344440e0072a5000070b00803580d40303040d040550060140030881c0300c1800905600160015042d0040c042d02d520403210710704102c4c0d1314070042d211480780521050058004080500240c0b5040d400342442c03d42c2d40c2c8030400d04645407035190344844800d561070b6001d40e000e00c0411902c150706004003640800320b0f00c000c1c4629854140411042c48003080741c9414400046100c14a0f4040542061601e1040c81c1c024440c603100d041045841e14040d0702603030701440c140b1501206c0704105d000340d41c02003603071282c0b0103103807120b8040305980707011900b1000c0742c10079000c1000141414003400341318041d = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 223084082 1250 223082832 223082863
    0x311121008030a090e0c0c0a03230301141201111e070203060a2405010e210a0b16020a02030a110d080a02010b04060e0f010302060310030203030403060507020d020714040903050c 78
    0x48508060117150b210308000c010005140e4100035615180348085007180c41d290341420a83c010b240341c08052490302c203040f03400c441d045a01200008806881843c1c520701118161160a4401c5042c00001c3c280c58855140944143d4100004007254800c0c41d105108a205000194100305103680041c0c00c00c141901c0d6070100c0f54440c01072640114401017031401d81103056075400c0c1c4030707450320001820842d20507440a2083d51402d6444081b00700c6040c038484070b480345a003550340031615440c1400c40d010301501c0c1807004150702091426407a00008949003082d400074000c02da4214182c0c0d9500003203003140c8000742c01506e07001c0000000b40c0c50134050110003e445d00040f41300703d04601808200d6006074880d246400009061141c8078240541c0740c3e065079015103520359640d480d00326962a1101da0b80c8007e42500c800500001070003641d50000f0f0081c0095401d407540c080090200302c0e034621450188002400492406542c03c2c42c06a0001c0d08440c4641461802d00c07201c0c004690030206d002940c03110 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 223085332 1250 223084082 223084097
    0x303070b060306090307030c0602090a05060a090303030b0114030f13080a080f060a0b12060105090a0b090a05401d070902030c040603110c0115150311121008030a 71
    0x1d6180c01e0000681c8495448011404c0000c16180141a4803155802070045a400590161280c42d00404640030304406480c07103607200c1d40884020300140c2203110550002e4544402581d8941c82100684c444000f1007640c0303400c68591a002003100007014101d9400036200410f01c0c80015400340c043c0203d28455107818030f5a00c5d00100900e42214006c001d540f09a0848406000c214206400d98210b180d5111003460242e8403200140c4a911032005a1907102400039800221082e41000401d1414001d98240d001d5961b184103000329048542c5040744520980607859100200c45030031001141a61070114540d081d0800c02c0808a5103e010b0703110308640c00301800700011318100001001445038800c214a035142c4800101003d0251740075080403d5100c01030410b184104406840e0311040c40d6008100d0004003550705861091980300b24010b1700390807245610501e001c1d2150300101410190f045180545460348090100350090240781211004403000c106c4003410000352801d0340581e210b404 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 223086582 1250 223085332 223085341
    0x209041b092103110c0a0b0901140406020312130f03090905090a02030d270803031e010e072106090519050105030a0212070e0915090a0b011707050303070b 68
    0x80c6941c0160b0000c40542c4006950300b50140380c4a0124101c068141c0b4000d030f141c1800d07040407410000280455944180c20706004a810305008005084804090300c96036111002448411001e004602c91100035800620028903d01c284004440d0b1080c402805a104041d240e035a081c1c07103004c0c556054001070b019880500c142401842403a0300400048d00401e000140784d4006540d9102c0c103029401045400368a1402e41071440d00d4031004044200703041e81c24503440d0001c07199070341c10840305481c2203845890301c02c050605581c0c4050503100b010f030041d00140d40301001a10f4040d04070b5001030740c00c605007200d801210198030515014001c101c0b8081040e04001054004010701a00004840c0c0e02e070100400c003559000500801d40c07a8162a01d08582149130205810100c081e40101c50300c045100411151071408107101d400c40d01030740030b020925164994140c1c1d4540300c08800900c00c0f4410401400607450800d00705d007903840c0500c01c5880c070540365070110f41180c1003001c085584445140034007 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 223087832 1250 223086582 223086587
    0x90b01050a0e0609010605090f0a0914160203030c071707030c020a050f0f09040804050a060c061b051b01020418050603071d070503070e0d120201061e0b0c010209041b 73
    0x6100a0840c0b900c040c405081030400940c4035031040c8200070600100080008181e00d07541403030090324000a240000040d0f8403408040501f182484440b4142d41c5480001c2131911502c03005510460540e00031425540d41c40d586002c2c0f83e000702c0c400e5424110300c0f0b00c110345000654009141c40d500c0396461084071300ca0782c07041c040c066034250480361150001d0b52035521651540401d0505800b800c4601420302d4a440c00c2c810340c1845036800c4560028040030780400c14030b0b0862405010144a443c00704609101c06001101040061150f1800224100540300c21142c0c0703031810086002c0c20034001894280c3c2c1d41c0b00940040c9a1700380a81c10a1344035801c02c0070382d2a0074000e46000307000d00b005086404610880c880314030701c00144214113024021020507203207485072241c80c43c034210180c0410340c556100d08050100601c001070200040d030800d18046074034400841d881c4900009024110101d0381095064411504950007001456600f0700414109590324051000c5089001e0302c4a000340300c3e040d500 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 223089082 1250 223087832 223087849
    0x1e05090c12010b0105122205030304030806010504030b0f04021f030e01110c0705011b0b240d1106070602130b04050108010803092407050d0f0e0d050a0b061201090b0105 74
    0x400d0740381d2400c082020140d0b00901180d640700524401d4448a03a00c13004052010380f4825600766403c110101400c0400400000031809107009449500b89a666440111aa8402d60100130035048035140454a074a40440d4040d4100c5c2c80240010b5808a0003203c200030302000654403400243c503500c6401ca007160a1050781d00e011007000e0541c1c54803180880d019030300d00c0144200c1d410802d442070241d040c60240b100301200c003540914000750700d0415401c414ac1c02d0041d120195101400e076203080e0071502d0b15100c925411076026024845401c0140104030300d41d0004501034801d580c0030403840401c0c1d0903040d07030707000a0069180340700e450340c2c2004001000c642c41600103610320307442001400510b507a487c000c00c0451803001a540c0300b0748103840e0b180c40e041c021014001c02621035001c2090030703a9040808072044c014a03a0b20358011307121700000c00008810240c805042e54204076070020100302c1d10001158000d0010704910125203440c507903903003110250002038400e01e0758a40148031034a0705050 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 223090332 1250 223089082 223089109
    0x504050d1202040b121807030302030406081608010312090e0f07110f0309150d140a15060e060307090e0406050702060601030c0e010c050c04020d051b0705030a031e05090c 75
    0x1d086080504241441c034140c07003405101500d804200300040c5528100328035111110b0aa0015241031554138034000c0e50700d80243c01004086a248400075081c94501c42d032218060003143d6a50322140d1a603201e100300c0805503080b1004004140201080450303038910039a015484420281e030582c03411540041c1070302607010514040350080300480055110010598111500880701c00301c1d1500819503c00c0303c4d219021071405400d00740800d14001c003c029207660b10602e1001000d20040141c0d00f18440c2c162050702a10300400c1d1580290561801d04074055a03010303000e0708106810b561a4604208860800c44c1d08603070303850b160720801c1125903044c402c40d6000705007800c0900c0303641c001ea440902404421403403541000b11030543c3e1340a0000c01c118120b24010003410455440c1e190110080c003824044407074080c3d0000c1d941255644031704400860303030596003081c007460500d9120081203015000c1410000c0e02c400d81170304040f030026158400d0602504094005100281e903410900201d22181d24 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 223091582 1250 223090332 223090367
    0x3608010b06030f010314012019030b0607030c020a082506080f07051e160b1f0e18010c05070203010b0a050a15050c012301141e04020705010504050d 65
    0xa1110031050030b43c030b09040d00e5000c441d0707081880109800c41d00502c00c4c0002d65070000001a5808650361000004110000385c22600040c02000c2c00e80c20340540d8000740220340c02100410000300802e01c502c0c1070041581c4014100381141c1c1da1241c1d0030f0301c1e00100400d03014056005160280c5226a19000c0c0d0300282102d04001c003491606840340350709480f006191b04148500062480d07411982a0360000041c0c1c0d040200c2a210241e2401100e003a07180e203034088400c210071501080c280c680c10607070000b4400c0704a813a481203070305180041c0048040501640c2c4900002450032002407000c0c00b0b6011108210364a02d43c40e10b810340101070a55000d0b01ea07aa0107004e01c001c061116031a0001400f00355020a0001121482c03600422250f520440f80d8503801546011000710f04405400352070790080c00907191219241e40c94500d03840b8068212901c1541c005c4600c0e40c07614850340e106e4459220b01200800060034000c0a444c2d560a461084404607420381100e080360400347d4002c3c1c0103190881007403 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 223092832 1250 223091582 223091587
    0x3052809090902060705160801140f070509150a080613231e10030309060504141905040e060601020d05090d02150f07060c1416033608010b06 62
    0xa0001410084490054028498503000601d0654458070100c3d1031081e401011550002e02d04101d0460a081901031660154240280c48980300c4900202c503004040a0302c00c1003403910b80e4041070b43c2d2a41301c0c0c4840d0f9000201b5048402c101000f21029000c81c2000d619194414500308040181d00d01071006c10120003407400a200320340d21501d001c80812384802e00318040094031040c0840354402032861002401e80c10039000c0006460711180f46000300ca1103600da401c501034846000703840c3c9003d0f0340103d003c441802108400203250020545200318071385200c1043c0c0c02e03120720219040e0380c50b4001002841d0700c100c050003050b503810810fa001d00259440c1103400c000c00071000440b001800c85020b0b1254115140001c0140d80601c215081518220f140f540c0c0d8150038507164026000141d61900400c40c1c540040303100c001c801c404c03074003891401c00c801e803130200580c1d40599400e03292040c44602e40c0364440d1001d04101c0403190a01d51000b07018981d42c00c07540303130040040c25101d1013000e11340220000d = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 223094082 1250 223092832 223092907
    0x1021e0102041509061704061b02010902040605042d02040f15230708070503090d1202010b100503070815150408190804061b0609060506030c031f0b040b06070305 71
    0x100b000181b441c10840b82011182d00c031801e00c0d40c0500a41e40e05042158040c0c1440e942c1e1980540c07113000300d98403d0380c090184903075441c104021140c8010841100e0809928452140c070390707140c11045520078120b001400c168590515a040b4041e54002c82e0406c0340c4528003030992604078441c80c03000001414031150700e070020304840c03803540141c080c000d201c4100032588804100b0b00f031007900d000441c0507141a4940ca1141410701450700302401040c095442e1400c642014184038401c10512403580c3c07545032842d101d00c442101e1001004100004510400f940300b2599030301d20b80c078141558020b00da040e40300d504042d0310300c1c1040100303180d90519550f444060750003d80840c2c185c0c0e0031240c06081c448003040c61850b46209030281e608006040501d4444101e08011050303200c0d6010f0081903040f540c4803460803040c0341d56080c1040304c900340540c1c1e41418448400d15034201001107807001d400440c40003a00c1e004500d1542003000220080f810110304d1a0030010111035002c03008001d8801518150350 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 223095332 1250 223094082 223094087
    0x60f0b060f0a0306050306131a010e13061433030d140d050405030715020a09140604081005150d0f020904140604030320090307050f01021e010204150906 67
    0x101800841920000b20380c42c50039601070740c4840020b00c400750646020745405c1001800c21041810201e0700800c0a020000340c00500842990503a04110104049070300c0e064101201d540c4550070461340161144100c004440101143c08d00500708599209080c0003a2517246219021080f54201c40c2021100c504040356800038411129440d030707080c0500d130700845600c803409034462106028206401c0c0001d101c10001c0000081c82d4540c040d581200240e001845500c09901c02e04e201d48000801c6108184040070159001c0d03507032402e005003020b150603521000942805c8640961400c1690b5540c10000d032414031110007403648008460602e46169240c0d01c0c05544022220701900401400300001c1c10024043d544249040c0c6000845555141038a40180a4001c42c2c82c0111218050107003030540c1d88159040d21045c0c803004015104442c204418014031042c440141411031003820303103080100d0020150403107881c0d00c0307800141c3d455003401c0008040a074000c0c036800070042c0801d000c001056 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 223096582 1250 223095332 223095337
    0x611030304020405150d03020a050610060806040b040204090908040905010b070201080408030a0b0409050c01090504180602030606070615080d0c1208130204051005040605030105090d1103041a07060f0b06 89
    0x42d03048500241549a0f01c40b0580f0201801041c550000d0303110f40c03280309050b00080da00c0d84140c130a8007115220f68456600841203c030702e12440c80403443d1900450340300e25080d0070208445801900050030a0358800714101520f03aa150203842c4e208001505014060303042c0207143c007418007000c405150490550008111020062000e030540f0700100100d8140704054002100001c0e0080081c00000c0c02e6090441d11170000ea40010301048031040c001a490529001c0e0320540350070303408003040000141d10b031b84019601c000c0c1910ba111404216100006a2610900d144904400d281180b034a003840e124034540981229580103006154102000113a2082d810000b4440c540c60038200940b40c10204080e480060750000394000e007014104031100d501e05003803500f01c402c01c94060001980e5071060508a9105950301d020035044000c01420007401040b0041c54001c03c03d003102e00c2c281e03a074070381841c960306150080741448a002461400b03001c070f240541d100400000d0070400c8850400710001d000c0d0b1 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 223097832 1250 223096582 223096591
    0x301050303070227010f08011404051b01020109020d05030301051c0803040f1506030303050a180c15090f1805090303090a15020d020d050a1116080f0d0e0a0c06110303 73
    0x20441222041d110016a41200e05120042c11070702c44d40d56190080501c3d074441034000d0f03040541ca4002408540d2243d100c2c403034007603900000904142280800f10020b144584410b01381950340303a024020050711401101c555660040c4051a16541000f082141489241640410351450a502100482c80c0d88041360782103030340b2403001389150015180032500035540c1088020b100b40740001c000705040e01038110511943c26802c04108550b124207442e219849a00805054900e10080601001a118205030050380290409054181d500c1015051001c6030350000c8405a074174145082003516640541e41d08908100051800c40c500410800c1c2d80300c091003006420340100114038a6989500d9044541794400100d041d50741b0b004040c03c2001034041564803a0303001e4a090812040300080c4130039149110200211032080443c1c545401a064104600d000c074061020005000c0703010303051040540883c00c035806840c0c50750060404036000c2e2010781c8107405111050807080c80e40c400200c00c40781d10 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 223099082 1250 223097832 223097839
    0xc0921020301052a070201030902120604020f01110318010905030d0201090b10030f300c05070602011407080901020f030106120e0304060203040e0915091609110403150b060d020d0501090203010503030702 89
    0x5507045c5000480140a481d800a500200c6445050301200c0010801c64410f60090760a4600c07a0404c3e8011540d00e0304800b28240c072500284444621040349444030058420140b500521068603100020b080401161890000d83c3d51030300e40f1001c010f90407029507409010304400490ac10f1454032a8a0030b1a180750004091214412100f00019519850f1400218515098070002210301c54050101c5401c21010703240e61169910000705680b05008004031801c0703000d4207520940f16201c007550348a402501c44081550240007007900d1340001c5000c0d500820140d903e080040824031650703021100440f48075041c64004001c203101030394000003100d0484055100fa42d640f5a41c0522060034504c401c1041156070040300180f1828010000c0c03402850410b001b050540035560702520310803581102200d89548006000c104080b0f08110108034048109000210b0351044c0e0b600014941d500241c55640140d6001c5546013000d0114481c15015000788501146554182000a0350740d002d0004000e10 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 223100332 1250 223099082 223099087
    0x623060309070b0f040e060301090206070b0414150a0b040b090c0906041508010618030f080304152d0b03061302060409050103030203031618090c0921020301052a 71
    0x10444010812180103100307001c011a150311071001003550945c068410515180d80038000302e038051506110f4054600e500a0034a49000015541c003004c41200410594600d0402c01e034000504801380306041144190625551492901c010508222030b22070800f640514940b0a0143d807c0c0c0b82c000b80d10703400044602440381c0315136014000034054030540c0c02001d0007a410444821802c0d4112419906070b41d13164031050740c41e0750310501003900c1c0340c00b92201401c14074140c00a00c0106800c0401141c01030b00600705140003400303480c110010b40d0300c06410030b40161060402d10340c0d00c00074040200c00b00420448148102131422001940d110b0f0301030295800e14010b0f002600840d9070b0351080310018084158203004540e501d06000e522604211020345208004140c030f6850a442001c204240003016251000e5060030107080d40001d00c040c0100d4020300500e901c0100710604440000c2e0f40c4030403048144421014a803045c182074800c003500800c480c09801d5080c905084600d044485603400a035800c54 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 223101582 1250 223100332 223100341
    0x60e1b0d0204180603020f06130b1b0105040c05030601060c030e04020306030115060201270f0605090708120c07081501120515190e240615120a06230603 67
    0x400030b1080380c0c0f0030890254000d03e03142d07000c40107800c05402c0724000c0310f100000b201c0541c244082d5200d8000100d5002c80451014860045500042d01c00c4820104080494062030035280c3e084501c1510700351900e1070440e00030030082c90b0402030540500f4051400b45140300140e50081d0082c00c0c0036440c144602d402100281d0503480940c014030380902560841d4496a903240300c064000c4c001200759100c486074142c2540000c0a8040d45405265400014400e020032540c031104000c2070068060003082c0610707803001a8101c4108170500d181c000482c482a5201c0c4a0080300b40342c02c00640c4160f0a580264501441d002c007121080c0307045415402c0303502d45108280c585281000c03000d03089014021500b90600102e0380900c41c1d03080c1c11070075407441044201074020505e513503828805403120b12460410240c001ca04e001c0881d407500301c071020f40a2a11180c0c0e054003e451600090b10b610102c800080c01c00a00031901d006100040c03203503410048170b4144000c0240b0704820001d030312500602d00000400e = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 223102832 1250 223101582 223101607
    0x3060a09020a0210050c07210305060303090609010507152322150213121109010806010612020f07060c090f030b0115170a021309020306130914030c010501050103060e1b 74
    0xc1f042c0c07650182140c0790103086001d03012400341007411a000000c0c50900000c0c52400d001080b5840d0810007400207040003000c0c00115482d40c40420100c0f0302140d9000d12407520072640c080d51414002601c0418401e951140104900200044c9442d107005400503c0710168501102032404050f00544d03040c1d10108200c940001034804d0315440c0c80c0307c0005210006003804c01e841a02c5002e881038039404002041e1400300200c41f4000e00441c0c03110b4014a00411080d401041035540319025000058104844022214450340003c8000d54400e0b40313500b040e03080140d00100580150000c9585000102d00790307281d03580140c005008030240c8140c480c0d001c4400710700071001c14101c003020040507800c5140401c0063702079080b119010041008102d80171030a180b50340281c0f489a0f4018000080d1341150003c0100a40141281500c9455542c0720585581500744000e212411480c2d00200d4594500340005085903500d90142080041c1e84041c0079956010302d41ea180442c5240001a40714003200568 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 223104082 1250 223102832 223102837
    0x3040206120615070b0117011a040509150a02130e01030507060c1e032c0102062e0e06030706140930060405070602030a0212030a0b09010b03060a09020a0210050c 71
    0x307003449080108a510802c0105c540303040c140c3e078007540200c513011900d90751942610f99a50b010381d81c41c1580700d140340d15810140c0c812940701840404072440e4400d4003954081d1950242e488580054000034050182c5032a0702c4124002c200d01424000c0e10340c515201d00fa20b803034860140700200850f0402d8601404161200c0800844481e103031490705996504c0c000d407026411594010311402548410002c1e40e14000703501541a1060b0064103842e6130300b250507490510494031120f0950242d500010340440100040400703440c1660910341a801e00e1380c20549062816402001007050444600100000c81002d6441001042e036a5144507138503452544072074007511100d005455a000340703a503080400003562a0060340207100b9a041c1c40e498050481c5c491113040420005640a2403401443c2c6410b50b0046511590010000070b640142400060410b81e083c1d03c155009003012080c0000342ca03004800c3c2c0c0003404000070452610710071440181d12899030244030112159078100280b44400c42104 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 223105332 1250 223104082 223104109
    0xa03051806040e0406050703020903120904061d04110d110105070507051002100b0d23100204170c0a051c06091505041208040302030403060c05070f0c050f0105030402061206 76
    0x745039222038460003480006141100e090b982c1c641044003180e0605c1c001d01c2100c816003006809000003a20406a4400c01d074010383c00f964100d0342d5808005507012110a031301c43c29100c5020010550705250501d5074803801e60342440c41c03003000b402d01c402d400100b03038a80714407a105007030038a55201d40490a0450a00050b54000c3d504030080f5469014481c1c0d0104901d01140066a8208401807461013440407003550040001e1000840c14003c1d00d0803141102c011101c41d400d08101d81800b8504118401642c000f5841000d0400c001001ca0045820034028030410000540c0c030900c1d0b503442e080009102c20591700b410100c00309010902d0042c810581c1080c00c00c00d42290020010704000009180108401c480c140d0303c1c000c4520010252601c03486e0000d0180e50585d00450505013581c44100041800222201c140f0000b00300303840005001c410b5203c181c0d4040c90940c100a40b8000501c1007200003404424100720040040000503034680c0155a00c2450300b0000c5900c9564800128400b180d2000 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 223106582 1250 223105332 223105339
    0x6120b0619020606120c060406180801060b0403030809012f0c01180c05030d02120a1707020706080604060b041404020906030a06060207090b060307030915020a0905120f0a030518 78
    0x80706110380d903000a0001d010741810786424602d100401c3e24580c41d00b11a0800650015041004010691161550004040c020581444507a540c1c190036400c5602c0c80d03002c031820740b50104082040c150803111280c3e00c00072000007840000903018915043c0300d035080c0c0d241c046044c1540110540c00e012002c0d6065940444020881c2000c4149800119014501d00322500306c4d40c000301180c64203000c281114400480c2e0001d0101d030b50040d0f2900030a40000700c49404100a068420500c00e40f00040d03503002d1555500680409424440010080c100042400e4007841c20314004212020b4000111402c84541d00b1165102c0c007000b00c0000c0180c8078040c0195808100402070000380340c0a0740c40b800c2140c4070791302182c107050365a08005d41520700c48031b03003a43c3c880030a01c0065019402504a00640ba108440054002c0518480700342207030800140c42c2e00160040900303005a080003020708195201180040185049055045549210840000341006070120301e181e042e03155890343ca461020001d = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 223107832 1250 223106582 223106617
    0xf02070f06080105040c030606050a0e0613121103010e0703022112040e15090c09010e040c020f01060b07020a1a0403020324070e030624040f230106120b06 68
    0x84400414142080c021280318034502881d06c84114024801c3c9401c44049854082c00c18203144400e0b03d07448680e490f0150000810800081143e4482c0760400181c5413103c0200301505081c10407034042d200d0004d107580aa8509030b4840100d80d400200ca03000c03268111540b41a440856048007070708070040702c84e40307486d00c00c16400c0446118801c010b0410703164407003402e0b290b650b1050a005101c01e00150401d4012a9050114107608503610040c40700800c18103001d1500c4443c00c011a080b9441c9140010051b0447ca035813a030420001e000b581d000300f800c1c503041414500c0e1500000d50000c0c482c4201006158044546d000086d00e040685000f560002c0a50740344814526100110740300d80f1145901e40c0b03222100241015008044072107132640e01800506050740c40302900c0781990704100040e002000c10480440a50b40d55002d4101c94070100c2c4408a040304a0703441c82d00886c8550315a110b074208540b0014000c82d030b4003048908000f0380b10440401c0d200c0304a0086226031243d0341c1c9a52594000 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 223109082 1250 223107832 223107839
    0x4051507060c020c030f07050105040909030216090f0c140d050405070305060103030f4505040e0a0605180a0308060607080a020601140d031b140f010e010c0c120f02070f 74
    0x450130101d03180c81541584c18210250f040c0c19142d1015000da240840d400384024014680f00382e014001c654031900484d1080d40c0d800003154030881c903681c00000360603200d000c0402105414004d00d1510781050400800f0300090b81250f5845000c0c034207200981c2c80e80c4000041c24032a081006100454008007514125612411300903d00d180001034100424582e1155291514103108070821070100c0356541301c109440c040c00c0028010320003810a103900303030089010859607210b03c134524000f56498002c0100c8100791418a0a8a030000c0488074169080080c440704804085038488145034585000c1a09a68950002e006030180540240a05001085414050790002100b03416610010881c0e0038842804041100e1101c00c0b540003000110845017948810360403414400050344110001c0816881c0320226500c4e017902c1d2182d822043c4c1d1110004d0203550000c1c4a109a0140c0b43c0c9041d555000d045d0712403800c20003c080004e820001c1020314442440d1084c40000d019103030245805054595 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 223110332 1250 223109082 223109087
    0x90b0405010b0f18060d17040b09100309031b061161140706120b060f0a0215070c1407062708060c030109050603060c04051507060c 58
    0x102d088040d008004221101e15a403030504108010180c01007a0181d0645d40c01040c040302c151101411038204800e401030001c000819405070001c1c2c11001311254940440787e00700100c043d1100c84800c10705141c901c030720001c03d13401050f898080d24000340220300d1101615245005000b4004520050000440d03542c2d6003821111518400d07008a03040e441000d213407d070f01d8840c032940010f016403c0c201e040082d01201c80c00c0e42e14007010070413480090a141c021545032800f00203101c0b240700e0300c6900a018148001a04084400341c2038038417074420440c1000d0880403400500c54600074040941d0041240300e4818405c00140b1220b0561407102c101078144a0b07800703003001e000c4100841ba4585550641d840072400090040122a020b603110400e695480003900d02e402c07041754110a02071540c01d004030b40645c08100b0740380101030311900c95589615200d110000c64030043c00e11446900704905008000b100e40c01070343c06035602140d182202c0400c504a00b449841440d50050a090400402854154 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 223111582 1250 223110332 223110341
    0x15070503070f0812061e040b010905030a0f0b0a0504030c0602030402042003091905030a0810030602043003020c1c0203070803070b061c1e050609070512160e060301090b040501 77
    0xc504c00c9000150f0300c40f00100001504800d0310b84450705848a101c0c8954a4690802c040b44441810030400300340c0c5a80201e800c0014051054511400d002c1201c0100004800482e902028810f02080305003442c1c0e0300101691401034010300310680100200303040d5500d545c046081000844001c02c0200b0062050a96580081b40c5260a90040071181a029a1146940c192403a40b01020f185414400b901c00d6844800142c10700246900d1003d01100096440c8014000390040d60b8498070030484420144400b031491024003440100304600190000350000340c1090000b01c100c5608050040140080065019483c40a075151054130300001e50660044010440f44d40a01d04c00792040d03840c5c000340910b061702e0340e07420a601007040500303002140e00c0c1645032004c03c01d85003508640c0c6107a625810701d094030956050170300380c1100a0801940c40c0c8126043e115441002c060f10504040050329031740c03850a480351344900b403840c10004200e9034003980003074049a070184580071a400c00c0d0800034000c0 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 223112832 1250 223111582 223111597
    0x9060712020609071805040309080303040303020c0106050f09070f0212130503060708060a060309020301150e180d090b0705160609170c090402040914010c0507060609020915070503070f08 82
    0x140102c0300880c110324400304003c400d665051071039081035100349001000820700100705030100003000034007154211082c8001c40c0103038000d40d0003588903941002950300b1a11554022481403000c111a43c0c3c1c0c9445130100325900c1200341c00c14400440e10b40f1000c0e03041c032204420700c140e001800603203110780301d4268040701e00f80c80b020b03000c803800c0d87d44105041e07031402c805407059540b20703d9101040001512030b4210743c00d4544013800100303007a0701820701059000d500360403c0096080358030400c1000703a82500c00a041a0190f40100702d040300034580a00400000e000f218071203e00000c0d03a00512100304900d40c0764500c018054225596150b2008004001c10300440001075815400380c4148a0700044a0500b000000e094484684440e0308200c000c0103a002304803001e103503c0c0303190300c1007540a2181080f840308686406030f4400300b6190030012145250400740e604e51041c0f00d80829901e6004111103a9407889404070358600060500d41d02d540a14000203207500003064400d404c124415007c2c0900 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 223114082 1250 223112832 223112837
    0xc02150c0a090806060a0e070215160e0114041a07021503010f0f0b0a0c032606030c0315040b04080435030c1b0612090a0b0f10090c0509060712 63
    0x203032900e550383c01e5280c14066400a900c0001004103110401c40c0300392030398001c00140101c90b0701005241d60080c07119070803980c040c02d50940a40030b000d00d9800591a241e0f900c400d1800f05407140c41151001c4090007503002e09000b0340d044003903200311189c00c83c0071103400a80013001103003200c20042c1d03100140d910901419440e4981c844000803250100441c0400b40d4080c1140c090402c20301fa04215020654a1000d40c100300e11840b00c4441d282c1d80601c08108514585015030251815509040c980000800d030700340298010f0000503004003400a8180d005070740032001407546d0303c0307900346a84a030003550044030740180000c0c2c4030510380c628600e00b00b408000d00151100461981010ad51302e9002d1000c288105801c25403c00c0000c00c004103051200c15001002c450410250301d4008200400480d9410501c1c0c0c020710091044c0400607428075445031030360780e1041c40342c03619200020410343e0a10420300fa454440c0f189500c02809a0b007070302c404000241a841d200c1c0c000b41006d221019203488040b01 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 223115332 1250 223114082 223114097
    0x40e03090f09040b0114011e031b2105071110060812070b060d061806090b0a06120611120403020604140106060c2a0303050c0105010b03070806040c02150c0a 69
    0x450b0800940c054032031034101c241888140c2c030301a400c10900854114160400c0321402d086004c061501d03c44884409150743c0005100c0b000500c2c8984400340030b024a41404001820a13420350800c921f42206c01a05840100315502c03107110076141058198011261390160066841c0e000c1e03002c0d4030840c1101c0c0c81ca07003121140e80280f01c1c1c40c845c0e0b02c500800980f441c2c0348031000807650306019200090141c030403400081c810303091901c4d43c6a0340545000442e081d1b038660013400280020285115040360810004021a614040e001000c00202c91801444641c03959041961400c4180c00c0d520030480301c3c03451300d0582c03408e841c0007511010102c0b42190307814440716030190b8005052040d80152082610340511607500c90b114420400004404280f0803c64140c0300c2425400b0b80c0ba5a400561107a228103803100016105242524416000002080010300403c08201d80c0a40300d590006010b49002070000981d400403800c0856040010304000b03c56014061901f02c070400500040f034040e5150031 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 223116582 1250 223115332 223115359
    0x140d02180406151e0807080702070803030901020a080109061202010f0c08040b040e152101060b0d05090f010504020108040b0a0902032a010c050a06022101080115140a03060c0e040e0309 81
    0x20f20741134036000780da00041d9440700180ca0140034030319036a001141401100c003e41e0f0b9a01079107103958811184074049075004244400d45076000b404403070141150150500243d814050490003544407000041d0401c10080e00d1240068091007104208030b401652142d5666220200d0070901c0c4e009100c0c1c00ca46003111000a003450b2030040e48c0c41c080000081002c0003c030401600828411710150034a00c0556848500080003584e1000034a011031400341d0200301c0f8504a6451410301070a20f0064580c0e074100340070400140c7c0e004851340c1e4081d5108c0e0002d0059202c0c20741c1c0342c000f0591407000075050711642203264040ca400507040130001100d16042c0b07501e198000011a4404041d6100034042d42c01005c034040001c07015005081c55800300e0660340440c6080585680c1c60044c00e80c464041ca955809075a501e00e0203c15062014016180c001034100d1070002c08101c0d0303080248009000a59660088240c0504c0b40090142e540c50041040c021031491030301d210707182c0d481012480d10500d400d00445 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 223117832 1250 223116582 223116617
    0x240109350f1b01170a1d1e070e070806100318060b04110a0c0f02041b050903070e15120313030b0f0f01060f110106030b09011b140d0218040615 63
    0x4181d010b0080d00d1800c4aa12945c0c04400540300d050500385100e10030b1080a0740710302080154085400c0986c042e00e0801c8010b80989080211a4000c00302480802040200300b40e048409990440400d1711081d88100c1d0666003107000308031107000c074501c04044a004d01c0601000d500b09154900741250304100904949407110000d100d4034402d02c011868038681c90f40810010b6419028003130001e0008510b00e000801c1d00442c84038100c4441012800210748465181410403404001c0d125200f2020003a04210080055450800c07041d244034010120007500c4005050042d17829208180011495043d241d1402c0400f41c00211004e1040010600000344407010320546107049078081d40b948920007002840c00c44038034101c080784603000e40d20361000100148000000600c540903d00000170364210407032201300781c00b558041030010000804100301640c20584120341540103038900069640407051701e4104218402e5103400d0b845450030000082d2484c4103510810120300e15603403003c1d1b00c02046880b = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 223119082 1250 223117832 223117847
    0x110a090e210901020a060203130503040308030103060b030c011b02031f020702131a011803020d030f0e0a0302150d110406020a050d02011109040e01090b240109350f1b01 74
    0x10b240140d1040f11440d000c120942c1c010b5400030034030108120000700c0342c0c4130240303154420782c0110383d1030600100420900c1700a201c0c28842c40c6088020740102c12050000a080b00c41c0c3c00207101c45500001521003c40da410001591020043d444046151448141c540025080b0a805a020350b03851070140e08407109034442d014542e00f00782016450715a000004481d2400203480c07401441c2c0c200e01002c405641e031900540750b130300d01c0ba50741e960150710050001060023410003001400349005400c14401a5030750104072005510744030310b4580b590b40040f044d5018200850070150414000200401c02d02e0780851554100790080d002c0720011159108124203d645846420034110424040101149065004801c0007070703074140042000b0340c2e5a1520803541c10103490f91011066038011828685119000c1e0b10740152003400e000f240a80707004064180003000403071400044d01152850f207110700c3c0c03903c82c1e60b41100001c3c0c03c880340e0603c1402d426035203c170280324013004100c017a202d0005940c4541c01 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 223120332 1250 223119082 223119097
    0x91005210d1404080609030a03060803090a030605070306030609120206180a26030a1506050f070b090a050601060f1713030309080405040f0f061e03110a090e21 70
    0xc00c4101e003520811036500c00403420b000ca140c01d0030480094103110402c0343d07500501c42980a076a4640403004050304032985980984583d810600110000307039a04503040c01103a4001c5d002180d290b6550004400519080d000105203a1902c0f0062060000b10070b141d00071444590220742840d03d40e4400c0003031a507104840080560700c0010094009002c030314043c4030b616012141d010308080c0ea007240b0b103025041101c0002d4a2655080c01d44007142103c10013900800a41c107140d85803c000c1d95445116109010014004003168404a0f0025500f00900d08280da00401a2205561034010040c08803000c0e90b400000101404401d2101c0d5042504103402503844021054902a050b501900a07000a40f03098a01c003c0600000907aa00da0f030240110aa0710b103032000844ea030641d82904211031182c0c000c0c00303100c4080c0403242c174240100150401035a03008008440765480e0b240000d480103a607030304080700785400c000030481600800074507110240344802c0c00c280a40c2c11003415000d1380c014441d = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 223121582 1250 223120332 223120399
    0x507180806060907022b0212030f0603010b0105040f060c1704170d0f1e12050a0b01080a0207030503040213060909030c11030c09011505070203030a050304150b09040b15091005 77
    0x9000ea4101d0071520404584035880d00540f09588d0301407075020038541080341c000c059508400f042003190715003845686826102402c080b070400c0d0824400c0d0081e42442d00031541400f0320b8860034030501ca400581140e004c0404c0c2401c556441d200c40214400b00d0402001c19100d106011100c2d001034010500f603c01c204580da14003122001040c0c00040365411030303210704280308880240900303654071401000e00c500703070340180802c9041c0351000040042400a00c0503181c244180076100000790301c58100c0c1e802c2601200c0c4544015100d4849100400d0b42e41c4c45880028078001801c002c041d0400071244019002c2e90b00d00d000e80b0b03580014180c45441c003007405644010070000512135041440b52000b42e024280c07405a040010b40e40c00700345580e01009544001c52400310410003048800303211040703010a01d160600440070040041161110040c0000780380603882c0780011f141f81d078146d04040401750000c2403107003d82412054400b40550720300a03b406040300c2c685806043d4083d00c0c14602200380300c1c = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 223122832 1250 223121582 223121623
    0x9010f08030a0518151e090a151101022a030a0c060e0106032a080f0a0308062b110105070521040302060403080c0c01090509040204050718080606090702 67
    0x1c0c504076034560184113145000081d1180798009900c0302c0c424a258a00c0138190180e43d07100700f80c510317640042c4050b041c1034400e2040001d0196502c1d9102c17140c0442d10203c0c0c418015080d410402c1d540d5601121110750650b2021541c583d040210405517000741041e91001184d09400200803511f80c45951160f40104810303d0114001600a5014042807161100006030300c584036601c01803040700c450320b9086138944650342900c92a06042c0214000d124100c010800841c01c40702d003640b2200000000380c2131000c1c10000624945641c012200c240c20f01007615459400004280d200041800800f9a50f038225202c040003d0b5000e03404660f40b50790007400624501c007030200c1c0d000c0c0789070303601605610040041c040080140c691101520240d441020307480c2d100e4503002184c624003c4a849014104180c08d0020400c03900c681441c00c3c5c0007601a00c02085644d80c43d802a108101682141000c0380085000011004000b00303069001ea0002c1b60092200e4440f1807040343d0703030a0044a01e2000301d07002c = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 223124082 1250 223122832 223122847
    0xa0e0a0b16110411090f040504030807030f112101080c06070611070f0302030403030305060303040e07030e070b300615160b10061710170a050105130209010f0803 71
    0x1e030080700140074400c01c26034920900304008507064411028202004200100d4180354034a820a0401e10b03946055404001c60714054038014003c01000d041e6100381742d40c446c0c9800310344227203411861407100c515107829030301c03c06980e08041c1189031009a0091501c0880041a81d003070101c0c1240c0741d10310040565050810b25240c2400405000040381d000c11410002c1d40c0001d15440c0c0c7e41d9500780c1c040e070082c680b11481c0d4180074003546d0300180780380d101c2e400c00c020a00031800461482c5400141c42d240001d103200c00c3d00c000700d00d001ca090f0840392203840c000c120100c03507100c087c0c214441180224505070540500680403000c80c0010341d4140c3e4000009100e440e035179013910300500300707001440034040d10705e400f00d4541d02c41d45801a5001141c003040c1d0070090102d0b903000070808000d1074102c442c00f012881d00104c103280f140000d0154544020784a5103c9401003c20011003807825040402000a800d0136038000e150303060745150480c00340308660000151201048a040d08032000740d030155261925 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 223125332 1250 223124082 223124107
    0x160806010e030102070c031a0a060302100302090d0b0421030e03040b0a0c0c0b27030d0f020a020312090f01020d020c0d020109090504050705030c0406030512070c0305060c0a0e0a0b 79
    0x580344070a60b0159401c0c01420b000c00c8045280e240290b010300103065600c00390344c1003010f40407001049001c0c41d60400c403003080162550314005409400524005880d807160100094074050164009040c1410341d40502003881650815820120480c000d1040b14200701442a003e0341d00d2003000e1806604207000400c01100407000a0602e00c1c442d11707081721590b00b40d5079910110b0025801c800b1500001107029001041d4814a0004814482200012484201d00000d949807403410b8440100a4103a1070701800d123000f0481c03403810765401420384217421071441d5201604d03048815200d101d016062030000255001103100a68000c803070b0302500e4120800c86c04d001c000041000200d0401084646c0005d400b0f0051003010700440c4610003a19426240004040c503120703c982e13106100e9413420f2010000039100103004084c0d500d5100105484111a052032400e41e29a0b60002e0818001c5c0002c200340f0401c1c20004048401c86a25454140d007045418080306441901070182c8250003003001030400e08 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 223126582 1250 223125332 223125347
    0xf0a0803011206060b0d0c0e060403020f120c030f010b100e030a031b0206071208010902044a0711060103120507051f060918050606010804080409050112030816080601 73
    0x140942c4004c1070355a91203210480076032100103034544280c0d41c0d41901403044d43c0100c0c0504001d40c2200c56070f023007609540004030b00314241c503020791050420400d103026078a0706200b40c17001c041c0020145c8165200ca080c6150180448080651003908029815210180902441011054083d0040c5841401c0741d07025140f904005041b13060803202240c41c0300c01030381c07964011304c1c6c2030748103038001d003048801564060501c60b01a040700024500510050185060703c0000410014070150640d4000e105420b20020007141c526070710a600784100300c0803640449404031103008680c6a502d00c1010003c01d11030540701c2c002070100801c0120748402c1000c040d841200981010350141e0252282484150304c81e25054040a1460065507100e040c2000028402c0c81040300c60540081c40c0030724001c43da51520744404005003c01d041c0a820300210b81030115000c02e590103022204801c0005503110304051840600701070088000034450300000702140b076000d03006c96240c02251a083c072952a03410042d075a81 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 223127832 1250 223126582 223126619
    0x60f04050c090403091d0402031b0a090203040507032105030105040902030c030114011802070c260118140309090601080601110709020403051204060923030607020f0f0a080301 77
    0x70311456980e109540d4807506598000da1083e04c80002d02c51410000104442141c2403c003004007202c0100805a20040b408103001140c9176190b102d400e41b402c00050145006811a0108500c04820401084400545802a81d025102e520200a00c00d1f2600d0740034260340340f0304c0001031000c0c00100000e040580044000c1480102a50144001c1101090840e4007881c2580c8820401d000104000c05962030120190b965008040d460a186621400110341c0f01c1d20402501040301c840300c402010002600c50260080c2d18001d00100717180720203000c5c009040000030f8944010b0300090f6041080000111226410040c2c1010616941d450054641c004001e00680c1448107400c02000d46142c2071110b0400303080b806900680300c2b41541082031401d00a80582c040307030001000280310990f0420352410888006000d100000050860300c21011503071040015010321591003030040036a0041100036000d101d40742182d064825020380381d0b998150480000c1c00390001000103221075008484811002c = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 223129082 1250 223127832 223127843
    0x303030712050c0409150303080709060c0b06030a05070915060806030607110c03010629040605030112060603080c010506010810211e0305030f0c040605030a020717040f0503070801020c060f04 84
    0x1345540e846a113829110391a00c0454524040d4006004050f0043d11068015072035280c01c9a1080c00d259009d00301e20443c0388060184806000001c80c0d40c0c3d820031049400366803040c1030320321003542d41400c80041e05400c050881d0342807000201160813889020000c0c490800100201482d880c3e4160a4405150381c402c00c2c0104c1c00f0300c1c0c007414000d480901501000349060003075200e003c15000314400c0d40308450300701c1d004448000c200c2007081a902105680c159030155a000c100c2c25803914000000703141c1c0340e000030700501010403540815079042d481300344a1102030320b42c0b10f19940d9000d64024491454000c40c050f0380000c0118002c40c0070541c0b03480c0201c0348a00421466031b1042c090250304140d46030011800140000104402d440e2100c51054000d001c2201d00717410142000f9000e490303400014540c544040d0302180328414054841d226070240350200c0e036100e42e0341c6c1e1101c044080100b900e00445001c1e1180880014202c0d60500c220340e0341007070701e4015100079201c0c1040040c40070342c003410550b103 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 223130332 1250 223129082 223129087
    0x170706081b180604080a02040609093309030807080702010902150d020c031b0d080609040215130b0901110a0f0308130c060c020a0e040c03030822050102180303030712050c 75
    0xc5902c3c0e80d0014405420010b00400385070303015204000907180c1a4119032811410f1111540015900c258821000080c150401d140480b2441c050f042108100618010890a044c5c18a00b0706401000650103009640c0c1c45218954544805030b085c0c4280c0100290403c01c50301441031005907a2015040d44d035071120001d4541810b5034041881c50304000702c0c0505905000940e607056910411851442c1c000130f0800d00f01074980301001445000d0014800781c0199540032502c110b02104104441d449031140c003098a00944895800005407c08502075001c104a4541c500a10b60300003120800310ba80f10701d800c403040200d40c0e006c03a1580e0014101c28154080341888000140500502201901d825628003440c10750fa401045040002a8088250b16424605200120350308500d40b03019290182810a0b0030b03180ca02c8504418600442c20143c040506091070381040070640041981c040e024501c0a003401e510b10815849110650f09103000c5817001510301103101481d00b21a50160070008501e0 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 223131582 1250 223130332 223130377
    0x20117070903020d08030601200316061410060f0201111e04030206181f0509040b030f0f0a06060609080d0e030312250813140a020307170706081b 64
    0xb070814546000032159580080104002541e100101584d02c9d04105e0340c18a00d1801442120344034415403580002030a20200b104050100701c1c1c00041e41c66170a201120210b281c13900480010b20703204c0c0034903800110300000d403110061050181c82290002c4842c46441d05d803010315461843c20300001d1820050100b80000030160f5247d6001c0d1642c248118280460702400c0e00410890785102e121074001c14180c2001d80040c0c0d0761100540d40c586030103039400640000781100291504418201645091151b01180d448170a004074501c0503403882580f05000c11354171240207584000c214025600c9c0c5910000d21030401501c140f031202c1c1039000207001d032407810a01043d4a0740d403038001c4031080791003d40788200004c00340c80240c00b5106a80d20340b501864604100c07441c0c00c1c0780200c0302c1000d42640743e80c095800d081c2100b401401c00d9903500070b040b504801e50b01c1104003802c80344203200011a0140b6080060030341d0041c81514032815800070450318108031040042540d4111210700b1642803248203040 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 223132832 1250 223131582 223131589
    0x10e01020c030d180215041707030c09090606033e100813060c050306010f090b0f070203010e010903021623120309040e03090a09140112030210051603140402011707090302 75
    0x10300d0102d00700c0c41c140d03661f42c104641c1030b011504120f080e95066002000410100d406d41c80c3c0f08090b07030310f0104045100e411504040c00500362540003c0c02c0204000b1001c0340640c03081c00320724403548140c000211603c10204440f84501e15810307110750008844000092100d10801440b680281040c10aa60003042500c685007142c01111f0004040b61001042c07100e650707040307022400c62031200c4c40c2c1800c1d01410298094014003400008029001c00410050210f54081d00174201d03c0c86464001c01062209080003503850100c82000d203d81e8100d104042490f0003581c100d5644902c4500010540d0707030208050084928414600d4807140c0400d02c00e009003580c85008219007105080000c41c0c07202108001c0009070641640040a19464001002c84441d40c240325030b811101c1c80c011002480165003010703802c01c16003401a00310f0740d16102c1000300306d400c21100e0000207055a917003000303010144c0fa400384107004c09850103408103041c030712039140120b150010307117601c46880c0c581004445d0762640803 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 223134082 1250 223132832 223132849
    0xb07020a06020d0b0a0510090e0a0b13050a06080f06070509270405011d100221010b070606060801032102011b0309060b0405070f080603070f030b0702010e01020c030d1802 75
    0x1c90000c0c0781ca5003100c80700391802e41000170162a0071500041c0b100502100508244c51501c00c2508503e19040055058105507104105541d0013900d0a9000005404040000d04d000c940c03180c00580340023008180210009000c0380525500001048070380c83d808000e541d99048407220380d0340550000c1210001920500800c0004812a03090107400d00301490300c0d909441c0d14100d060310244240444900361000060300300e08080e01d0f441c4c01a1740710095603083c8210b1084800b882e06030441c8200005018001c00000c0a07042e02900c0c2c200020703500c03604101c56030711080c0300180029132014040c0401d052110290103011000c3d0000250b0040c0200d000c00a0b0321a1100d0800441c0d600c65100080c010030303000f200900503080380c080040c0e10300035030058440030700300c1d103031408103c803c40c002502c94408100007400340802060076454142c3e82d2030f00c0404580112501c00041d401d01c0d464031030362030050007640d588820f800003460a100003541000300815800d1450740303425605102e25000740e02d40041 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 223135332 1250 223134082 223134097
    0x230607050d030b1903020609040e030412060c0c020f0111010b031c231209010609050123030c0a09090c05120102040e0f060102030324130e100902030a0b07020a0602 72
    0x151041c200758900107070881c1d81ca80005401401c0d0194038288001c090000c1105a941c1200d40c0ca0300e038042c010120f80188100c0100c98410300c80014003203460043c410001040d280b01c1c0030300740555940c0403412100601509802034100400b658521195800b642c14100088a035130000500400b070580007030b240900e50000b1450107c030305207504215076485078100383c11036100001540b200d034046a04488504c900c04031071991081c0000031919072442074010a0003130030280c03414429540c48141d81d041d00c400180540c0c1c0600201c0307145100c54140407980d9582c01c00010f1281c0c3e0001d00c0e010703d03500541070501049500850345000440e240da20340070300300a520005000141c139541414030010400c1d1015040e0402071002d9001c0107066a800401c030b0303a000e802c0a030207410740c134000361030000c844802c1d503030007a40011310884e5941011000d0b0701c1585604003100448104400201002d004c0341c04103440650540c0200c0c9451010501102d55603422910a2048400300c9280f6120306080703807c000f8 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 223136582 1250 223135332 223135343
    0x1020706060f1404050c0301030201030e07170c10030507020703031821020406061706040b0406030f050f1b0d020d05190b01090c08070206150102031b03091302040807230607 76
    0x81d0180150743c80318000c0c1c580a50305075000c000508140202c24034a0105200084c100b644490803c1c12551040c0554001800115000118441c0f01101c240e1249243c1036804d0003000700940d440c44c4c8074400e0040d98018079240e005449420b0550300c08071000001d0140c201000d518654000980d40c070702d51102003000c50724070410304134155240b0400041d40c0050380003208101c0b5a07040311140312010321415811003000c550010702c1448640108010700226807000c0e01c4c0d071030003d5035041030210100d260318840d100441a220b001e00540b80b94844100b01d50038882d005503001c1231001c010f080071b0350122885401007044400d2528014026000d502c0c2e0100c0071101c0c01000303001000400810300410105200c81d007084000e91406042c02941e42c4001000d111440d0b000c10305180541c0d000340202c40c44500004915510b0286456202e940d95104a46150241c00c8405011400d8505407080c0c40076520600017030002c2c2d41c5020300c2d25603074846800b50014880032468103503103540d40b0400103104052080 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 223137832 1250 223136582 223136609
    0xb090106080f0303160903020a0b0d060510020309030105010f060203070b04082b05010501142703060a09021e010c0b0a021c09031706031009061401030309080f030703050d090201020102070606 84
    0x444031708144c19400740d080e0f014001d6a80c801c2c0016550b400781c00040c0d46807090841d407600ca1480c00080500010b80c0840d4010310b9603858017980341d50200060090450030780007440140d036207140c19452001345100b00c50041e001444032900141001041c150014052000c083c00e05002030740707000c9142a00d800740070042110a6007180c07a1455805810300400003401d10391010440c0d001040741c24410b45d17640911511040130594200480320300204482c4401800329081450300a183e01d0090040744010381c4500d9030000e885003451807a0034040c0d402d200694505108041941d2412015500a0300b81a044c5070248904201e001d01d001c40c81d4a0600e05101c0440d00c16074a0601600354042c0d81117400005031810300b08031131a1400100fa0b1003a4540c54800103c4d01d201e41040c034014a1041101000b10490030000420305a0240e4110252030380340068600000070004000d0342c0e8070412200401040b8288243c8410158640c42018460b0060001600d40368460340c8110855002da0080c0d859112130 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 223139082 1250 223137832 223137841
    0x3110f03040501080a020405150901170a0b0a080f030d0506121f0e01020315010f050d180c0b12040f0c12060617070e15150c150c0301030209040b090106080f0303 71
    0x84c0c103460704018103075411483e15050070041015043c04a40c03103910420001141d002a0f403040c016800e0506050405c414541405180e48000d04400780d001482040940004900c0003070100b079619403001024011880c11809c0c049800141c040140800d600c24980d00d10081000b01c24842905081e11452601681105902c0f62400b11406900c0304800c0b6841401040810000109043d0040c075003402c2240290340802001c0301c2034400d5112180004e0309204000704158001520100c0d0280b05010783d170032198840443c06468010000215400c10900000c640840d000210090007103010300101d9040c15158507102c4404d101480d4205c41c10b03907403500c042201d508400400c5e210802140301a011803032814802c0c02c8545009007104010700e550b00b030b108240340d80d800000700640340c213000c01c26290080c59280d10f03144c0002550540d45407840e0000900351000000442e03040e60b0b030003007404000d61980d07111100c8a500040c60194550350f655004942c4950800c440101c030035040300115501d241 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 223140332 1250 223139082 223139087
    0x41404060e070f050609040504061506050d05060301051905041509030807020f030c0706030b031606090816031203021c0608011d010507050f1815042d09020703110f03040501 76
    0x880740d2000003c8810880240115a114000c80700c00e80c10843d408143c0d5107817404c05400138042c3c4604024101c039003a400060607500500070b00100424910200b05954400040c1400e03144101d400e4582c031032408007032b901b14517215446960414021501011303902c444480708000c48d2049101a004200701c5020415055030400841c4101d080d4000074608000300c02e540c85681c3c0382940208028583c07102c12910090300c08121014455010050408809540d100040c2405125001d411954064001880c0c1c041c0c900c0c6c1c0038001100e85c054440b0810ad40d00c18422002900140034220300c004a04405040862030f03801071002602e0184000924460000003a200c000074090402150b82d0407e000c0210140d007000075030300504c0900b84601c2d030359110701c42d410040c0c1ba0014002c1da800300a03900d0286410503040007400a9031150001c3c2c01405d00032810401c900c40400061003611151003000748402603554019040562003800c088851206011849003052002c0761307004410b500125040042e5a03 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 223141582 1250 223140332 223140343
    0x703080a111b01020606040b1512010303080a0501030f08030a09060f02130806270f0a0b07080901021303120504030203030301090212060603011409060105040b0c100c020c0904020f041404060e 84
    0xb0503024414210503581c1c000030352180001004540304070b80d1000710320407d07291150a240c0c0c00c91200700c52070752190804c100010200c3c02380000d40c0040c0d41d0000140c41c241e110301c14039050b070b90400d45a02c1c2c04c480c40c0e51980c40e980d000401e40407150380c6a85403080040d2280c06110004c2d10b40c40c1e03025884641e2052241b0001085600a0f119a4080801e2040611444188000d0700702541c0a550607405000c5a8a02c7c0003810810340d01280324141c00d0340240f00340d0512039801840f81d03541d1142d60392900c110301420b1703009280b02c0b540e1405080d0000c100040c5501c005040400071814800d04103030341c2f030700041d00b1600240c0c01044043d4000400048111940d041d4540c4000101e50f07803070655042a09484030030040880190149410304081106a8050350507540100352555205e03a464500d06c0f450b41c1c407051128290072405040070044040c0d40d00100d1840b114060190109506070380703540801c40c4031840809030540003641c0d420311803c403440f0110918407131401168040364080c0284042403824 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 223142832 1250 223141582 223141603
    0x207060e06070e0604090903030b031f051b030f060102070503070602010218240304080706050a0c020d020d0221090402070f0b0903092d09010f030c09150312020703080a11 75
    0x1503c1d10059403150344400648056401c021400900b0310300300e1405900510b01070300310030350512410b41d5440352038402a00c103141403c0304d4081442a62182031070140804012940095003010038000201048030783c0d001c1c150300050500c110b40c40e156441000c40d0800703000d07821000c0143d400141000c0c0640d40b0041c5142c03540700130b442100c01c000107050001980a8812a0440c0b59080040403c043c402100c095510343e2303412810412080c24801c105000030030b11000b20300003500800d00c0c4130030489c0c0003050100b0700840e2038010380f031a4070700600000c000810b1581410060b000c1446100c03429100c52001e00806486000c2c1d0105040141c284010703580d000810391001344d80100050f10316902c401c2941000381c080007889050b0600c88482c031088500a280b40e503034110b014880001441c0101c40c0105044034000d0203c121010b480315080c0c1d0545010150a18541d03404040c204001103e1588141021840340f0503605960340b01c0e59005950b0307010440e500700198030103400707105102c010710190000 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 223144082 1250 223142832 223142837
    0x9030705120c1504060b04020f0903010b030a030e040e0a060603060b090a06211a040302010209040f02040f03080c0313090c030e0f12031308030405010212070f05070f150207060e0607 80
    0x2840320416015650f0791440580803204524031011034200540e41c1c01201450074014410740d151100e2088000c030b03540104d0300c014401e601b040b5404125080104608001c250940e80703c0c0382800c0d400080c00041d1010013180f1001c0d1150082010208910380311b054083c5205500104540c4206000c0145c040000b91910b0b03c1c241c50444d0401c40c01e403c0d05042c200400c152101812841a00d040c19102d00440b4280450520320810401c420558190f000f400c0b8400700b11410010400000070301c400704c2c0560f0113820502c141c3c2000900104840c2c00c080c200400340c1c0001c5a145c420886c0e180451800381743e205a2803181c944d11221601d94040c0200c0c00d84142c03130001400502400381c4c0340e540d03941d5800301d16070710484000080b4032100540c50480e556507800040c125035a08042c0b40a900030f502503507941005109400100745170a00c94145e0b090400c3c06035840b241040c1c1952104079007a02203441c11110008507a00b10118607800e4005001054011040029000c0184583c14100706000b00107504 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 223145332 1250 223144082 223144087
    0xc050909060403300f201c0b030a030c0b0c030c18011101020f040e0603061b0a020109140604030207080102091c17120a060603062304060b030903070512 67
    0x2400c000001c0c945030300c190035140603002c200108004011080100c0651a803180c03002803104245075050704464040c42c10701600304140c45600f0100045601d8900030000c268a04108240749a41310303801b103072580c104429000030070034040c4000900d0092a0b507004c401103491004594180008818820341c85460040018070790320301455001030380e00ca00d0b44da48100f06070032440e059850348a66030601c402e98110f0000c40d07507510220070705a200e810611483c0501d101c00c0c00015501d003400308209000b904070000c16048642e0202c82c0a1080e040495508115961890710300b02003083d1390003103521441c00c4405440541403a04000b81007240c250405010341c0e00410840d81c5c80c0d1221010380090001003d1004c1000c00d072460300c1034124100c500425010390300450440f0410385941141e901402c10030310304210841d5140003d506440251154405a51518514040080d140000c0f00180b000c0104000386164840f41458940e03001600d1420039a031010541d00100602004090594280c0c0c4d09003e0 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 223146582 1250 223145332 223145341
    0xd050f18011103070f0e19080610030203030301180905010903030c11010902014a0118060e30010b03070f150c0515010b0702040506090420030309040203090304030c0509 74
    0x8010748000f0f030201c0100724808109000c0d440c070440c42c801203d2801088445c80e141f10314000d14100c0d0740c82c0100d064601802003ca1221184448400d084036806000b9500f580c1c0391a01c8003012102c0100c0098144d40c80e01daa070780c0040c02c284900c16000d071007601c0000e070212007000d00500c1030181084c41d5003c1c2c0e00d00800a400750b81c201d40d076102044404801182d121820480d8030031080c2c0b203241d0901e00e50361882803540c08000d04240341304c000d180aa99800d01c100b221040350391501001d12800003c03814103802d0f422a0708000c50008607808120b80000300d480d42c40380300b41011000c4a11000307202e9545072642c10203441c007032116500410085400030101403c194960390701034044641030085c04a03d03805a001c0103000c3c000202084200755000e070080d80d6071180b075060395006c0c00d400c9100714030f404000b54882c0f030b10070a92030181e070701320062801a42d60103d108001083c0a0f1031158184810305c00e01c5020703a214001188100c411202858075207141d45044110928103801c2240310388154000c10 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 223147832 1250 223146582 223146611
    0xb010513050402030a0b0a0f06020c010f08010614090904051615050316031d0f15070804030315090c05040314010c050a030911090103060e070506090a0b0c01020d050f1801 75
    0x40c419074004540040e666100e030076920000f40700691800390400d1848200117104458941c1d80d00c1102c1c541d40a0307403c680081001100da80a04600341000310301000c005000c90351040c05030b0a41001782c1404986080000f00016141a20441e0226095800303d240024180d100081584c0100f4007a480c02c02620703010a00540750b0300004108224415150304a518454400e812011041e159030342c0341081c510281c401c250300d404840c02d25614910030300c5030803007040410082e214810781d51a650000c49481e1694101d01500c45a0b8040c080c00d0a604400303e03948419100b0207400a1817038542c035640b83e141d46010594080d080309111000c0c0d14144103070402c203811008941c0c23540c070107140009071801e540c500012428002c20102e900108175000100401031540c0c0440d4400c0c02c0c040459107116a103908007d194031071102407a8000c1c80000c010004078454801410100e4201c01c0054200110451240102e50044030b014414481c1c04062101d040d0011240c880c6203c40c030002884441400000d1 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 223149082 1250 223147832 223147867
    0x60302180f0a0306020c060103060509030301120f061e020403051605060a110328030e1f2a05070201081501080112060207051b0a080303040b01090c050f0f04090b0105 73
    0x84074080c4100e200354071a2995407509500141d90b1109086450f0782c605800265104401d00044925502c1c002c0400d01c038407400425a4100c80b1148010110503c4640d1340401c1104c098604562403074075200e03000314148e440303034416903008289a00143c036203141d0f050081c40e181d950900155410000ca400780001d071201f100310350061a90b07060204014840d030304264030310f20132080c03194030710318640620b1100403036140070914910580e40d40902c0a1003450580646440e551320441e002182810007055056941d0f8200359900030960981c004611600712440e80154450300c0070710b000800c005940802c40da0072070141c50304100c000101001900c1c4400000c0c00341079040c0a0740307940030500c8440100300302e0b06030102d0713588941c1b0000303031580244049501c800c220701c01c640d0148602d10f0014041802c00001003520300c43c1ba00030391400c85591030000300000401001407400c0401c54104a203a40d40320b02440102600074407414001d981c2d80c138003840e603000c5400d0700031a80c1c1040303020403015408050b241c01 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 223150332 1250 223149082 223149127
    0x110f060f0909100306060f0e06120c09090a02030f0610240309080403121701060c0b040206030a060b03070203031012050307020405102d1d130f0c0e0a06060302 70
    0x450a00c0d0f40c464030582d410194640d40000c0c8524241100412aa041081742c88122100610300d04e07100d8a601003045402d1648103a80e200540c4070024501d20f901d0a0300f03a254201d60601d0981c0c603d00b0458000c2414078040448030300065100d441400f01c0300c845544004001c0044901101c40d003884d11609504840400740c0040c100b5841d50359903400d00016000302e800550f4006404d01c10603408900c007400f81111840365103221003400b000043c03120301444000d0902607000c001c807500c546e515400c01c48503810140c08030a0f407658560700400c04c0340001004500070354071038000b10740ba442e2a16258600a21541003001040e491900c4800003400000660b108164100e4010420b541c03040341d51416201d2701e503c07107000d0b50340145044060808440c02081030034451010040360a403a090002c014a101102c00d26540a400c400034400d0100609040c1da0f00d0310078045034403140c480c5c1d280d0028075640c81d001441148401c805000c24400c40d07203d18001811641425801c02c046103180486400784040d = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 223151582 1250 223150332 223150339
    0xd1707050307140d33060c0614010602101b0e010302030a1407030c020f01050f0103080c07030f08040801051f060311070609030e0114090f01030b03030d0504110f060f09 74
    0x40411202401543c0900000915040403512445403012002c060703e8000c2c1804198041600507820082c00700e1401d49800d0150b01104803054035091040b82c0c2481005801d941180c0e4440f03d00702411850840f0a000b414a035000b04140c44002d0340b000111121015a03240e1003140340c06520b422908911480700c8005c00b420016100d40e100495a4083d0003000d00103400b21900794204000703560581d120034540e104907800c07110000f40c00c420041c200d80c015100810b107800d010004200213112480188840b13130420055130003040c0c2e42e5a0b04d442040e2640c0341194604004182030110b541d0902c2000da03c2980640b04c62544c69071580444108403041c081c0c00100340c1c884070180300c207480b2041281d5071643e00220801110840b400d005200c804817000c0240003031444040c40f241110448242d45c400c80c1c005211034a151910401500240070000b18240c0502050084079980401803150301e101e1400350409417000007221003084556820300900d02d10984044c08540300c6420183c00781d90201c1d23006e4 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 223152832 1250 223151582 223151587
    0x14060402090c0f0705060118060b04180b03070e040b0402040e01140403110f1504060b0909070e040204090602031003020f03030f090d140a14060a0c0819020903030d09050d170705 78
    0x82d0140e83d00e07106851000e06684a400c00025841d0000b451840000e01e011108001007521384414007124417a500c2922683d840381c10041403104000d51000a050800604540315596034080315180c0d42421981643d14690100401055080a0046043c2482441d000b009070816900d1504004070024002500b001030031420305103010002c010041d548504401182c10550b501c0e1000f030b00d519401c640c03c0b00c0e140d09162440343d0302c2c248611440c0c020315185015019003400d1912028002c0030040c03059900c00d03203404405000c140742d44021402000201d1003c1412811030041c04a000c0a40c0c0c8454020b07841040020003406480043d24511202107803112440740c40b0342000e03212000705030035010b00790140c1209001000409041d249401030385c07800b92000c0b681c403400f14008548100070b810005c128510006581590703111141c29403541039100040c1040903200100b8030f90f03008180c444061070355601401d000e00904100c03080c0401c02e01d00c0e160741400f68150800300404000f82c002c2c028007001 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 223154082 1250 223152832 223152847
    0x1206040311030904060b07020f030d020a0605071b03021c0914090402040f0c1205011d0c030709090c090501030f061424280201050903041a0c0102030103060914060402090c 75
    0x2e20031070307480d050300030002d101040d01c8406458499004400482c820340000d00305403054217022901c103410b65010b40103001309c0042c984030b44010b86030007040c910800180325168840c1c94010b201c20881a1300a0b801800310180c503062049046d0021500d0f40144608060100030498150072040b04107801030355800a992264404940a81181d084260080e82400c840c02c00083d072000009950f03c007421004d102c1c23079980311640d0b11244c0007125410794040803440010104c801d030400843c0c000d401454084001c544e90481b08048600d008500c000051503a20300b00050f43e41401a146039515065080001c0c41c503004581d030320440d4415006000b903d41c140c070405c1d980000782c403000a8143c02503150340d8071100b0011801c8810754a0100494051195903e049294414442c0500c207800343e40046d0b1074242841c0810180e05140d200400b080d40d803c1151650408080c00510700a6129040125a95402d403403c1e10840e0382e07280502c10240e00c01c45c100809a9a018851a04034201034511a41da111 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 223155332 1250 223154082 223154117
    0x15010b0f0a1b111f0804030305150a0e0717060a141c06050414150a110c07030b0711030f0a080606040302100c02090601020313140a0812090f12060403 66
    0x1421880d1441803041d5041c440c00d11207060076601030b200045825490000c000101000d102d041c0c130344880c1c0014107540004000900a42c012a08002c124502060480400e40080c08a0b280c6400015080700c82000380801c00341c02c840f0049105102e9154600c19140880114440c11b4483c85504040903090940c0e2a80ba100c466283c984401900e000b40c118610743c1c00c010001c0c0905481c06c4403d0f4201c40914032050030046850041501521400103440c0c6072140c4510240c210b8075a0510701c900d04003c85208500d003041200700451054540c0300b55441d01c4900a402c50040c2c10700100c082c0c00030000260000d6204080b40c40b914032508224240d80c0383d00002c1401c40c0183d8000a42140d1411220f50100741c00080390407082e03208491000070b55455500482e200c0c005c00000d00c610604e030100510060284011030410482d010348803000d03440d034541c640d078a8140707000c1644540b5000058210300d14103110507080d400315400d5480f500b844c0d0700041c03101e41e641d0b0000d102a08002c6c2c1c45146456481 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 223156582 1250 223155332 223155347
    0x20d110306090c0a0b0306010e0d0302072105010b06090d0b090102040b16060501050406080c0402091302120f070c1101030504170307050918060303160f020405150315010b0f0a 77
    0x49014040312128580300c01c46554903480010301d584145444940007450310b8150040b02d00c00d420681d01c106040c0d041e4000c3c0404844210011402d50007000c1022032015a131180c2d48100c27923940d0f20300601d0035042d400c0040c2100d00c800c070f866000304000c00200109807105180e04c01d503188d02203411030300341d074421808500a000781e4024040e003079400030310810901001c58141d0311490007000100210390341c0b0003c00c41180d003c0d10401000d600510b104c280e003071070245c1c06020304403400f0b0008841c90080112280413a4030244594200300348070018461183c130100a01d41d4001e8017420841101c0403981c403040c100310318078001c0c0e604064841000808101c0c0002000807000752658050307480c0d003001d8102030002d400c5114410301440c2c144445059071205030309598011740001d80a10b180c5100d01e02511607544030034205035101e0583c4642e103001611244038203841003240c15030310250414944101810401d10b50307820716000da4440014000d00720242c00b19441030700b014107103a07954070304081c0595400 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 223157832 1250 223156582 223156613
    0x1180305070c0f06050406020609010603050d05070f081315030b06070b0718030809010e1801060e010516050a1104020921010f050108011d0a0308010b0d14090a05011802010804020d 79
    0x80d0b4100034001413240d040f070041d005030786480d000e0300c03143e940d01c050140c03c81e40f1922024001c0d43c0440d078801d0400c0e000314000c00c0700c140540141110743c040750716040a65800008141c0c070300a8800400c01400010662039018100d044c5030038005a003a1a000030b000d40102800541002d01c5440400c1c0494000c0d5050054600303840e401d1202d8680c3c82c14125620b03041b8805040c04a00740040010881c50301c40710424102103605010322944c1d0a0000481e07000010310b01181c1400020012109401c0d111083d9400c0a03114a0040c40c00340040c0c40c0c1680c0314000803048500943c018001c1040e1035031002980c10b01560008a1804a801d0829409000d05002c820780c29816280200214035180c0640000c00c021502005100f143c0e511b00c010300b6600c815650024000880d000010f10250b0b40a80c018201c460b0310140100710749407018a5126920800d0780d00f8070b44d0358001500a810450b01b030060b010081e01030fa03050040802c5d650006481c2c40c400500082c0304080c0280030604009c000807051092 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 223159082 1250 223157832 223157849
    0x40c05070b0a0c080106050f04030b0901021308010609110f1b280b09070f1205120a08040b061c030309050f07150212090d020409030c29010801180305070c 68
    0x907420300e596088000c3c0690b00003000003680f52000401d4290013030003200e10284000740a5442e09182d41c6038200e5002001e000f800065400304a05a03d540d0000310700405042c0e1100001249850038007508200d4039016841110610184040301442d54104240c0d000c0300e0314856a110715115a00415040041041449403a4045840e014408140c003803000c10306603104801070256a00c910351704035622800e900c54101c140b5120b440030720103007102c1520083e16502c2a42180d0400f40d2096440c06c2c146c001c817080d5800148040204400d000100d02c0c500d411050541301a1010351142800019800708070760702409058403220050304210381007041030710402c40c85003594130158482c000540c4c5460380803903040052060b00310b00c03181030084030100d030f0300c1160050809651417296420700000d0305001000380c0a02038104800c9020032030040e915558480100840d2061021203039282a503a001030304191016072601c480c02e83c941c540c03511034202c01605402d14a40300c040c10303d0541d160340d139540c001e48613 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 223160332 1250 223159082 223159103
    0x50109081809010b0c07031b0f15020c010f0801150e15091801061b08130b030a060e06090103030302160c06030c0e181b12040c030b09060f0105040c0507 67
    0x10120740c11020304118030701298011400e990307400c0009458090078000103403d4110342000c10006121003c141a4060900314128489940d02d041030001d03c69a031140f0710914448015481c000d50501502c980c14009081041c021000e480c00101a80340501413513490100c1d403140001c10314003c5000c480c2c140e000074092810b2403140c02c0b00e808260401070300d16018401e070000003080000c69000c2181600c00b15031301d0301e00481e24100c1420942d00c0801c0309490303c070340404c50034045003120141c0340041c1c890040700c1d550b43d051100b81d40f02241c00030352100345000300c104103005041e41c622042c10304498040c0360168482c50b0b0140301c0c09a010740c1c44001424442c00c075200184071a00350b000b81c25600c8113919000043c03a04102404089900080240140d01c0302600040602c8217041165503400500d2034824108201146c0203001d1600641d01950741e840d18003004c00c01c100b401c1164941c0800d803040640903500340301d4840a04200103020b007030720540e200c07151410000c0c400c1068034011a0060140310 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 223161582 1250 223160332 223160347
    0xf070204110403031b0803060906061b06060111121b1603030306031e02010e090a061203020c1212030411030c06040b030a060b031b0c0c06030c04090e01061a0705010908 74
    0x49142d4040d120480c0440c401804504292a41c07000c00a0200d4029110302c5c9156521801c101c14203038000d11041d0310450521507c03440c0c0702c2a0342c0305000d0f020235070010212410300b540050500e00c400c54528040ba8001a1130114140d00c441c1500d80b62202040d501400064207006c035403c1c0b2010002090f407204170700500005240e0300da0400421240a8507000708010b150311000880554000c0c000381c04120410810041030030078410b2194031078000240041c0d02d40e250b4041c0724540e000220705400581c040d40c444400d41c03620a09010300c52410300d004290f00058110603400c039010080016240e81000c02000440351402e004215120100400381d540e1191240c0c403810042e003043d6403020302c0d5071403e4404900509200c003101c3c0525088c0b641882d01111144801d600c030741c010b046210b964021120480d0054650a000c0e601415520840e1500c1d503080860318411208000c0fa10301d1140e041c84070811500030402e120700c001103000c1c007400f81d9032091801c10f0b0b4094440c608004040660010302203 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 223162832 1250 223161582 223161611
    0x90703020415140625060e010c021509070f120812101805150d06060305032a010506010e040504060b10032004030c0902030417160303060506030f0406020f070204 71
    0x1102030f2004101c114468212001c24418039024000c62030000c01e04c82c4581035218141e4410a5404c14819400442c8002810a0312401c1d80d803003442081c00340c2d2180640001207500104001d6010b031450b030003001403514003a40121026402e00c6064000d60900f001c0f207092041c48002c586102d140700b0409000303070401c01440e4004a805100e40140c0c40140e000e10001c0c0220b900550380035444c520720030f19814844904000e4505001501190b410342c0d02c013000400030b0381c00c1c80a0a6000041000030b039540d810040303c5101c019048810004070b0740b40c241000355580c0c0100e00041c40200603140011140c0d102e2500b03100606080c6051070b8020780e15148880004e41c960045401c001070441d034114140c554a598544a00540c00b0080403a10425002e001a0705540c2c05944d21502914183d0095101040030180ba0707400010641903903c07000610106141c0c042c015030000344001d0710141d2035850202c001c091062006400240855000a0394813a0310000f0750aa9990301c0d00140b00b000740c09001c00700c1 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 223164082 1250 223162832 223162871
    0x40314070b010e09010c020c06030a0b18060f0307180902010309020316090606050a1223010e04061805030a0c060b181009020f18060409060b0a02070e06010e090907030204 75
    0xe514880c190301002403083c500600424038100c6e01030b001054070100300f0341041001c1d0401080b2140c2590303104504015941c81c41d8a20156259040d420b460700c1c10200d080c042c50582074000c090285e800b10800304100210000e074483c40c140c020340d0000d025040c0380b0040f0060700d0801130107581031180c0ea0000303205120340b98640044680042c0e082101c41c0c0c2d0b680702502c0a00440c907104010803c07074500070100d082d40307802040348810f600f400c40e0451104440300d1025040e082e000221501c584504101c03c100703142c4189000b24659010355031006c207070f9030f0b034582d40e0344038108245080000c0030500408000361a001796030403a4000707226522034081c10104040503842124503404200402100140c2901d03d482111480040c00c2d26903490300003a03c01c280440c080c80360f0b046401034010080003500070140d124110280000b03818441d80d40d420b1410080c80d00d200742c0c0050104003510700910185a0300540c842e40c01d8903087d501c210055a44128284c2050080e500181d00541006444c440d43d0341f02c0d000 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 223165332 1250 223164082 223164089
    0x70602041710180f0f08160c050a0b04030201030e070906180f0b0d020d051002030103060c02010b0109060815030f010905010501060f0206060907030506120a03081012050309010305040314070b01 85
    0x4449080145860540c1503842c0e40e1414142d100207400f050b0080b440210380340d0f2040780a8540002c3d000358558030b0071010340c42501c2c20302e410000d484503103003080b04c074580e50750003403504071200c042c2181401120440d0740300e544802410f059031500d40038007840042c01013130014004020204001660b450341c040c0301c1c0720801080da80c11850481c0500d0141b039079104041c0a02000380c50440002520750a0000d110501841980d0314400d000c4941815080c0d8001540654400d07000032612501c41d40b0b0282c02c3d107002c400103905100070781c1001d000859111020310f07448031201d0103200600e011040482d040501204040e007165080c5030b03659051000c150080380c102c0381c841d03031088417440416004980701c0d4002c4d1021a400883d02d004a10114441d4007c1500070070010301003044104412061841c1060f03004c0124041a2146c00704100440850003040041100e180301710054540c0740e44540d224492840304074149591107001c0b070103040c41042060380120102603030384da44504504161740c09410900c07 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 223166582 1250 223165332 223165379
    0x1050711090c03071413051005070609050304031217070e060408070f0e0705120a0902120307030c060b010c020307050603040501320a090206070b0712020406080f0709060206150607060204 82
    0x3400c1d46030802e40e405c04c8a01122580c8885203840e410701082203900700d128226401048000c2c003419021991310700c01d604206104100444d039603031541c0761002d400e5481c4041001404014890103459440300d24445503c802c140c03501401e0581410002807460159800408251068a0703021035022400e10240044c0d0f80f0007081c2f845699620300c03007111700703104c3c4420100c41c036030071100898005080c0d900898030b03940c40107150105030460503144d6884c2d0307000b081050b00000c0d000303440c127801e0011502c182400341c003083c41c1090405c6082d0700403c0da03270710b240d201c5d942c0540d80003c00501445400e5120b54400604403110802d8420429810b0134210104449071406142510211f03855201a200760303540070754054890303401c1c105c69480350b0200480007044102030000300c174004140c2c0d006520040c805083c0a44610a0508080300000721182c0c00503c40000c1c0012410140002c03500010702c02c0d84144044a000042805080450000c0c000e080703005010a0001c5404100140888100e042180c00304 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 223167832 1250 223166582 223166597
    0x1202011506050405041d19111e040507020d020a080c100c050a030b030105100302130f0c0f0e03031e0307110a08030103050613021c03030213030c060801080f0c01050711090c0307 78
    0x1410200c80000c0c0300281d11156601041e40d440d420584441f15404c030343d0280e8111070480d0844000b04e00c1540ba044400d0301501140c06011110703142511905400c24000d100502c4540021100655a904401c0016103040e4000c940c1c00c2d036105007040840380300d200c2031409000310440740001600a4001040c0c41020034180250071301641014843c00d881084401d034080c0d101441e44c0c00380402c0b94500301818980c05e4480340e10281c8001708c0d00030700c507224111340e0341c851202414042c000d241c0c3d1b80f00601107200350020071050841c414400801020050b604001d0307981da40305c80c007054484070f800400c100d01d94040c103100c00042c8001c55000c1c41c12079021300c09642140c1d0ba0a03010b1000c00149000080d400b60315400c00c0c416480801c52804511072003410300600d4250586281d0b0303250120f5078011030b0b00c100c01d0b20050044550206000707004228090003840340c031700098441d036218884c000c03009041103004103083c0c042c40780c001c1601482140140c04000c030743c01c202010b901c135a401100c8107008160003 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 223169082 1250 223167832 223167851
    0x30123010e091b040c0201020c01150503010f06031a10031217063003070c030503040305010b01080c070303180210020d03050105010f0e1005040b04080309010f09060804120201150605040504 83
    0x21480409522004202040c1819a030f41008002c0c044502c210003159424804402c910809100e0070200300440708998045500e040d00301400c1d5030849480005013410039908100083c842d2030700c80e03c1d041c4440080802036681c46501c02010100c3d03070000c0c044942404403402260340094003240c03d00c03072627601c0d20200c0e40d07101d00384564100c0b440e51420803400003a100c0a000d000240b080c6040d24551420340385005070b1a201c0ea20598038907002076a494000080c20030030042e0074402c80c003500c9030a0078640c41034500341004008502078102c026040c140c80e14584e149015400d00d5101105500901e41300300301101e101c00a654455103049400824030b000000306107507005504001e958620359a410910718110810700140d001440c490134103101d02071101041251030000508060201c5070001e603221a94140010140e982e130099100c1407003d030b01001c3c07040c650300c0310845a010f030300820324010500d0912030882c0104424108200300700c40c0c480c2d001c90b20946c0240100708440c41128140400d00a = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 223170332 1250 223169082 223169101
    0x5100b0f09040f02130209060d0e0c0109060801031101030b090712050f310c0305030d0609140c03070e0306150f040e03031306020d0f06030320120702030123010e 71
    0x80a85000d000c40000d6604030f4010302d0010041c5440e01d240041c0542041819404103525400550401110700c0d00c9565a00e03100c44100300c5000c1d0320409103071000d1341900c1c204000c1d00c4501c040c0005405d1520408148901e07174000d0308810345210004c0e25081e81440e2040c00103200d01c202c41107480d0110300704008a40900e028110180c043d62001d03151900d40c0c155154809044040e40c00002621110b0034118008201d00b141c00b0030095008030060b564480078480704034225107158000d81c40d0586080b2085059030f44408070103502c0038189010566a486148040c1c640850440d01c2d19818031503007041045c103160144043d10002015103190301d44501d28000c010075079a4852004001d58028000660000c054411111000c6d0151800600c0e00400554020584640d21062a40c0d81c0d07c91000b001016400744032001164081e50011013000061802d294031064030211030b419000001c20b440701955029402040d401c01c0c0b240c104031281000c842a11480f2030248103002c080141100001c10700c0c0c2 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 223171582 1250 223170332 223170349
    0x50d030903080c0a21140a0504050a02040e010b15040807060215071803050304091b020c0a0e060a0b0310030201110a05070b13090e0f0d0302040302011d030a05100b0f 73
    0x180d264842d004555900e80c6032803015080030400404201c002c030140c4005012885031001441100080480c0003c1000e80c90031b10b29102034031820340b06207404100300c081400403403083e01d110303412200440c01d400c10b03c03804c1d4013401032801601d50014000301940d4915400b10000c00403500d41205460000795207050580e2640309180004003000b14682c006203400c0c1c8210042242c01c40241454800151070b5160385242d40c20640242c03038220740d0b603500100c4803000707407000d400c00f1001e0344014607149060b8804180204018030507808801e1490000c034440c0e41d00c1c00031010240005401c115240d1801030440c0705070401074070042e404649645e0101426100208040b12141d8101000b00f9556181007640262541303c0000001803c1021401040502803401100a6201428000c01030804141e21007800c20300782901010605204101c10801070342c1040c0d0a4455585980503611003111480110b401c0040d0b0782401080c1d40519010321110404a90040501c01c000755901c00c1c29914a401b4054443c = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 223172832 1250 223171582 223171601
    0x3091b030215030405030f07050304060801050f181902070606050f06030c04060f0e130504030810061d060c0604050a1e02010804020409111207080610050109061404030506070309050d03 81
    0x1c00440400c0c58101e02e00015500284603a080300d01c3d014039250007102c550070090741107a076a003001400f08941580b200c0c0081c050403045070306458003900d007000600520450702c03a031a47d034401500007460f92120144a6000d41d51050390a65841001e032515400a0419005152017011501c1c03c2202900b090310a82e4030030440b0200e5a45001e040c0a02a11007424004e4000b003040704401d10b9000503140c10300003a220b06050140410b05082c9468090419030000f0103103000c00080b035508102035613000c8a10200b1002c0b203040c03a802000b081c4c010600d507100300600700001e445880140700800500050414a050051050864be49100c2504e000000007815001c4e00080203840802c0c09460320358440208644120010717040010391401140d1f01030402001c40840d5000250108043c20013401126400b04101c41c400712000d0034840040c044650501818003042407009149110f07011200440707015607000310072034030388d032402030801009000358000c21905030048041030817900d4020702488010 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 223174082 1250 223172832 223172839
    0x91006080c241c0506180403051614030a23040308070b0a020d050a021c06050904110d0b1003150e1b030309060309010e0f12040302092503091b0302 65
    0x70a041600d107080c03008510b800c82c180c1c580d003000805081800720080703040081c0c045201056030b16042c03040100b041348410800400040d40700802001a038094101d400018801d8007925113032450b8101500d03002c113003100740c0c41c0500c000581201c910750411048020a001c0c1d01040381c814565414807a8240140d200c000e181440900024000600c550300a55118100c1d6034014140045600e0034030607507000782e07040400c4a50002d00700329000c144001082c00d40201c01c10034881c3c1c5160101240c6030a0000384060a242040540a1a240e854007500b81000e5000044202e40e030502c000d0b556842e50062000316000c8281c0545608031000e2801140d80c1e60281c00003130004058030a0300b01c01c0c0f074440a207449916010030451341040d544c591020b18007480b24200000758048080a007145054038495001188e58000d82c440c0c400784405038125401c0c5c9030705841074900e5464030304091010051424440e48040e8228801d1040154590303c940f000354083e941600d074000444203824003408250001035003 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 223175332 1250 223174082 223174099
    0xf230a11040b0d2019200313141c0b0c070209040506100609080c040f020c030d051014030303150d0605010e0403091e09021b0106060801030c080106050f01120b0603091006080c 77
    0x11714900803200c002100d820355100400c0d00020b42411421580300140301400f00d4081481445000796010f0b5140624405803421100085c048000c1200c070060010000c044104e180e0000d29600d011400383e620340e9501602111080c2820710f0002d44070402207441203050741c0319183c0080c03020700ca50382e00305c1158034810203001414014402d11001c1c1c10540d007284115078003000740c0195030004000802181c0461340000900d07080068600c1d682c5046c03030303200102500810130745070682d6a01000b00e0317401c81c4801d2003074074a140c440740c08580e0942c0c43c6000900850716280002901700c41520030380e0b20861180c2c0d0b412a02a88075100880031024441103500e04140d0f2001c00d01c40e181c8150300030130160410300c02a401000044a45500703540f00b82d0050000141140700400400c140c101094010300f0031a4000e0012505000200340100b031480c00550407c20300d07402828403c0b030320750302c140ca2400f0050400384e030320b25184010540e14440720000d4400f403458070000294441000c030796020360aa00138400c18 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 223176582 1250 223175332 223175377
    0x190e0f0403120c020c03070f0f230d14030a0806040b0a030b06060a0c0503030903040303020f030304021e06070c03030509010e010219121101050a0f230a11040b0d20 72
    0x200024210360003903200743d840c4004d846e6410441403000b080d42c0b09002c40c4880c00c00b00e01103000d6516500183d1264250110059900c09400b14880245000c0d20038407000f0103a4104000c600064442282d218000046c51071051a803120685110700700c1960140b040310220030038040507441900c005040110900c020902c075191807002401d11400c41c3c03a000c582e5101c15241ea50071907205442d0108194000030742082016010712044a120000d00003a41c214582900480c82c42c44070300461968a50f05503603068070315a503d40654840c0c40d008000d02c24465140d144c050490380c4aa6046030224002c58021100c2d9880007400d00c401140e800201c081c40052552040754200540000350700340003450781d00c0c0005040901c00e1b140314100491010402a031148c10050031200d683c140c41085a820030186048800c6841405402191000001903a810300e4920500c0a000740d0300907840d8102c0c000362210044400d0f4010309242009c450598100405004a9040c00e2064240100c1c6504220702c081 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 223177832 1250 223176582 223176617
    0x111060c0a020a08030f0601020c03030f090d0602070813030b16050912031213031211190909150f09020903120a0905060301090c02121312080702190e0f0403 69
    0xc1c14107a166004540620000c0d07030790701a280e00100e032041584460a0100907040d030b410015404158020303800385191a040c060b25803110722410000c00d0080e020480400e040040c90b070f04030350b4072981048000d0b482d4004100c0085509800e844265589000071001c509004500d009000f01c0551a403100742c6400c0c010000e102100040060143c110700044c85440c14803001c007401d41d4031481ea000c451000143c224038001c2c21030990780d540d005035140303000382c0c1c00d010000e88412544400740080720349112203007011040300d680040b90400a515400c00c1e2522541f555500b214038183c800300302005442507103500f108002c81c098080a940d260744200d0218010401c0b40000300a602411301d0121021522900406c60950080c0d100c01503041e902d9082a15031941440039803245510820f0042c60f1502c01c1055014210b50381c012202c600400e98549004c01c001d4904030b80e0425406001c000e49580400c0009101001a1040c546030745c0924001400c040c8241018601c0350b80d260b2103482c034a038801e0555 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 223179082 1250 223177832 223177837
    0xe0a0504050a061203090e090309010c021216090c120b010e060c07050d0308040510050708061512010b0406080c1e1c0e0c01021501032d0f0302030d0b0111060c 70
    0x11842c030156503990105030148401d410030344040c0203864007484107280c00082c03900110020041410f540003401941c03a580c0e0702001044034150111854a03001141c040b142d81001c140c00c0c03010b20384241102000603000030a0708a410b6540311510b550744000029092042075542c54400c0ba8000742c81d60251103640d1a00d00c01034400c1c0e03005030044401807070b228000f00d0640d5208010503004600ca0b81c040200308803081005e14040c1e086040244080d003045840508801c00240c07aa500c00d400940c1034030341041e070102c103031182d0104184120021756514050f1401690080c00f03000700249010000a9080c000f2404541c280303940081868450783c40c4002c10001604a015a032801074281ca0b5050050f01c84c038001c501c80c200c0d44a001d0809080030400282c40d00b0ba4080c24a030501e490300340100046403c101403d003424400d81146003208800b00380100300010f40020090800504610040c1415400405032078500c030501802c00103242c5080064900814800f0a420719502000014020301c100401 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 223180332 1250 223179082 223179091
    0x5010e0a0b040b0c072705011502060c0307020f0601030807030201110c0a0602090a0b0a090807062303060114040303090303120605130b03030d02120603010f0519090201090f08010c02010c0e0a050405 87
    0x7600e02490301c407542200c410703946c0b807200240e0042c11141142d0882503440b640c2d0040c800841c41070000b880f52800070751100801031841c60110004400503296500074449032a0140030207040e144150303164039100d0785503001084180c00540c0f07000e0600c070034038459030200c0390000d00003001003040000c00d5845101075400399000c203400641400d80080c440c48404050181407210761109081c60782850812031409049a00c1401001040c0c00c2080e111480311107000b90080d4110050396407540c074103005032424a15058030341d6501c08001030001c00d16901c0300503070058a100c0c0da0740b1030f1242c0d46030100100f590224041c040e0b02002242d03c3d0185410258011180c610014064038200405203000c40100d8114504c00058000804100006490207114170701c401e5690013010041820300d14561460003a0621a00398100d6031142004190b80c007a510744801000503001c24001d05858400941c00390448181e002c0140d801d110031101a14011401084100c001604c582c0c0d40c07a113080100005444041d1 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 223181582 1250 223180332 223180357
    0x21060a09060b0c16051503130812070e0102011109060c0c03060a0605150a090b161b0603050601020d021b04090210030e120c060610030e0106090605010e0a0b040b 71
    0x94001015102405000028203030200c040e520303000042d44040c10080c008088080e000c070315a100303105607510a00c0c40000360812a24013902c03941d0f6144448082c000c0340310054500040415400c00d0306200021180c4280c08640d5480b4400a280c001a8240c600111500582d5081480b11007190309000014255101011003110350144102021908080095600c0444941c540c81c00b4840b03802c5c1a0840494006000852440c1442121000700080d59a00880762114000120000103014110b0201031a0b5000b0080c900041c0181d074052115600c248500b00209007801c000075095030011408048a0b48c0f9a00039100003900000880e00c0c0700365190001d580161b42c0ca10201c096151030b02c5c0384a007180282c0b4009aa008d010360942c5c50301e590310600140c0c00c50100b00140d415400410403a41050003520041402202408150068550310650104540c60120000b5028a076504103a040318001e0f00c6142e1480006001c1c801500340324003445c400c0301000c220030054134400c04001c004e49030550 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 223182832 1250 223181582 223181599
    0x702010302090d0c0b19110d050705101a0a05010c031d010c0503070516050306070e0d0c0302130609050a110414182e06020c0d030306150c06050603032106 68
    0x507030300c0c4003420304a600000d00c046004200700141c400c4002481b1410f003514104200341100b06540d03180e0b600a0b01ca901c2c030400c0070104035002006401c2104407803c03201101e0600400d04545038800c481c2a1452007940700c0c00321204001100e5010303000c03815589030107585914140400c85020100130f92250003003030404c030300c0104a401051041c8058a100e0388100040d029520041068610b8600c7c2500f11900c02d401c42c1c1c0900402c01c0d00700300301d0b0401d48070547d4080103100381c50038107140811040e40301030b400c060419411810880154065802d450500030100025101c40c80d400b012514841d05002d1540b070300300010f00900c44201d071441f040308401000c61300c0146190b44111007004042d600e411b5013200c21140b20107004190080310f50b4410381c07921406142031510f44002e41d6030021140c103d0244240920311302c1414402d03000900078041681c0d00a191050440c0002c082c1c0503041800d44070580b620011585c90b00d0044100c40c1c98800b0152101501044000b05c40c80e40304001c1c1075141d104420 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 223184082 1250 223182832 223182859
    0x902030613021c1a0105010f05040e070e0607030e0102060f070c060b150a0903050606030d0507060507180807060e1c1425061707141e071212020c03070201030209 71
    0x14140300c2c200c104d00c01d021000f6159a03410020090b40030607008241032104c7c1c40300104c540c590042c2601c040b2000c0341e00440c035544410308166003044445014039080400081c41c43d050540040020710005000e03030840b0110385c0c60381034203410081e0a81d2102c2c00120540c0401012600303c2d000303a403921400501ca214030712240c510980060b40621400400310b03040940400c1400310501071140d12030342c2500a80303150101424000d203171303105140000f0440c035036480125510a01c41e1a0380e4a80c1d8940b511941c2c0195112201d00d951100d0600c00ca40005451010308040d500304203140c07401d500c8070403001ea010042c1c540e0383e1012041c00d100c8262030520030070496036548501c0f8000c0001a011681050901074100b240c000d14030943c041a07200300301d01020034010301546c0142c5484c40744030502d05060b26420041803940c40000c0032318140e02c0408001c03d03084140310010b18208161800c07501d542e00c2c581c0705081e08400b41d020b4001082c0098000b1300c640710155000380c00410680000400c0c44160004 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 223185332 1250 223184082 223184119
    0x102060907150c1b090902120a0302030720030703051b0105040503121e160611030618070e090108150115080a1a031501180b0a17150705030613090203061302 69
    0x44c99070004500d5501c800001c1c0942c00d004c001180035000801c05403081c94156200a0769074810860024001c5900e111540760ba00c0548010306042d600c000d041c0c0381c425a980c1007031035803140211806280300c4107019038070350258051022039040f294054064040742e200a066020603402051010a002000c140040500d0034400f00909861020100180918a841c1002011150103800810200d0001c20911015540b00035524003a0600d20208008590701c0e0181155070480503661590041d060300000301e0b4080000c10b50b12a24030100341c00300410703a641d0150841125001d601c00b004145000c001c125402000d42205604039114401c5490b201c50316030100f0f140c03444014045c1e407900c015000611079942c000c2c000c80d00280e0881d000703100016401c070008800780658403030039204403400c00882c881c03e00c041c880301c1d04a01001d40d0164030b503d44020040c0c80da83c0102c9145108070845849200005a203100c1c01003521f801400600065942c985040300044546000b0380e070007090070319072049048 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 223186582 1250 223185332 223185383
    0x112060e10020c0106050604061b02030c10020109140d0914060702060403051b04060f06032a080f0a050c03011712040803070b0604020906090d06020409060608060102060907150c 78
    0x20201d20059a5604040155084440301d801103403188400300710411105074402001c4515020840da8004401a035100007440e01285101c280d800c40b410341d0044410369019030003110b08500401c2152020300001000913241d0a80b48040f1002c2101c0c5501400b41d840c1e10490001007a8001d0301591800b070080d00000c800e40c0050380102c500358800310714403000b815408040c0b08841d400740c4041c0710030350a00944010305090750184000300355446e03083c40c4006410661281d1081e4202d842030704120417900e002000800211401112804000c0c0844d0400030343c0d1107542d1051050f8844941580d0914000d08000e21841c01800038034450111418250700010000300000d00e91400110f42c0c4822034a03024103807110003050b541c49644107002c1008940c81e44000c0b10704e0058216408007001545181040080c00b958112542e240d141400108411380c04c401040d000761426021990076903201345803240d950425008140c001004404215083c2740500100c00c80244200c0781044800c503184440799404 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 223187832 1250 223186582 223186603
    0x50a060507021915020a140f090109170312060d0c08010506040f090c030602071406040b07030f020304020f0f06040b121e070804031b06020c0f0609070e0112060e 71
    0x95030359200344003006030104020322508500a41040103101a500c07001440b04000a01100307058000610407411446429142d0a4000c4ea20f0139549440c0f50400243e0190408070b070050100361003032408903054210718150381081d615000114035107000c5203460310040303070040d10341c41c0c12008400f42c2d50002841c0600340c01c058416140001034500d0f2040800080e035400061500207603191034402404035420300c010109590300407038090380d00d034031510301115080682c11102d00540a500305100410814040c1103000b00c900ba030b0706000d10b00030b48103103034100d1105a8000758841036107030041986003000e40384422411402000e081c14190341d0b081d51b4030550302a90803905005445002c022813400f13550a203400c82282c09600d2001d500e0a0071002d00110405170000d001e00c81d42c1c0c00012641500603004034101540084255100c0d140080c061340d0f9000c02d1560740c03255005041c0024441400015810b0441e912901c008010740d00c2c0441006044040f001306540c00d584405040004100030070003032090 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 223189082 1250 223187832 223187843
    0x50703050f1003170309070803070f0605060103020f030f07030e01090b01080d0807020d080910060e150907020c040216140607140906030a0b130c21020f1213050a 71
    0x585400c1e104804640c00c001c0040300c018030a00d409001182554100039019050300410b1941c9868030018280390103c151301100a80c480050240108100d04c0f941e50003e41c030404052145880b4840103405034002c08100702108641800000c80150f008080070f9000505401d0018944400b1300c075650945202c0c600075178020030081c004000b250010048030300041010301e008000380c145071034002d4071190015441400c20002c400403a00d507040c00c0c00a045c480e4076090f01040101da99401a90313298100700e521858400c4424070f00d115905013148554414007459020341000c0340f154040200a41003082d9880da400589030304140010b41040d1045280000e100080505140040d4014007400010b50301c18418601442003003000d80720304040c3c0381c100704200e002094080b0503201154400219285018180d400c01601003240740d00212900000e200000b00060b00808559000f4107a200303466860041490410041080080600c04281c001c1c4100442c18051002c6881d15481c080010005940 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 223190332 1250 223189082 223189091
    0x6013008180901050402090f090408041503061e0f060318020301180b07030207030e1507150203011e0f06083d0503060f0406020f0412080403050d1419030e01050703 72
    0x140b4035042c1c070014014007007150154a40281030010400c8080040e15160041c45840302080800040109440281c80d20080001490b0682e40000b8013812080c82600c04030300400c005c403600800703a488072600f904e0140301c1c44180c50b4500304044004103d806032030301c1d04507a0921402c0c0166000c2c01070705ca810a4102110341d10702d805040000000f08003500440505104020704000240c104040c1c1c180000d007150041601007001040c1041881030580040000039903072080035a015003039001d181a41c00300640c00d01c21490381c0c3d0510712722007134900403400760b4103941d101000300500c02d41d800359100403012020041c000c202008100002c1080c420014003a51400c1d0340c0302204019000380f001000e0490080c000c0f810041c45065240f0340c054070282402ea00051100f0103500042d084800134400c0003030000806101e82000d141642042c08100c503980100c010f000c1d031540c03007111aa46604202c031000c80c9030814500c000c11034030005e110002c3c18552a0001c0200f200c000307100342c6100302c02c561400700c0c = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 223191582 1250 223190332 223190377
    0x9160f1407170315060309070311010c1b0806130b150f0603010902040e06184002041d100c0c0204060311033007021804120306050306013008 62
    0x10300c001c13590341e0445d0050b1824010404494000100034045a1704036280b180c15107030f9207004039011030f18013601a04010403120700c0042a0080d0040104503220790003174a415441c0c10074001001c44103400b01900d045002c13400314280c0c18040002c1d90502e0001850680490400400f08074950002da0090b0001580814100540b001c5000d04070b50018046828800303000040d000d0400c441c0c00074045d0850502c0622500d02c0c20800c2c1e4400f1030300c0a0580001c900120109650040d0060340d000c01240603038181411b035405d070340e215084231018004440c09041200710b00d20040c0010000250b001c400c000500b8401030141e1110701c81c002c041c50240041001c1400c020301818a0010620a02043c038030010400c070940030411a031f9811240320244011b03541e4515400003845440c18042c1c0c078848001900306200400480c15100741621070151418005a030f501ca04254803105e0034481c0104542c00b4024001401660700808c2201030500028800122001e858140442d0000703a00900031405824040 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 223192832 1250 223191582 223191601
    0x909100b010912030c1a010f0602010e0c010e060703170c2208030421020301050a090c0603090206030105061c0c05040501090b0f070b0c0418050609160f14071703 71
    0x550056002c0c01c110110382e1404031202c0f0142018000541001a20701c607603803c00c81c541e0f42c0e2119141449803071503007558540b100f05000308038910a8801642c6000e1000c41d00a0000c200d802c80030005846c0e0503c0100c8500c01e0260543c80151704508100085030103291006481315202d00450030421015100c2c00140c42c00005000b407603d010301d5559040c01d0420551000008440c140c40c9229a02c0c200f01e048900b000303038005600c0800940c59400e0104200c81c8080320740c818103c090190390000c00895580ea0142c04407004988040c1d00300344100700502c042c2c02c0c0700f0000c086101001803000f1b0390706c40c4246140d00700d5043c02d8010001401c0020100000e41e031051f11180540b050035000c91801000e450840014400c84400a00f1b251480c0d00150f80136030303444190703030040a0a018072500801c001a1400c0140780c1154428403413200c01c00456105c5291101c86801401c550302e45011145ca907100039100c12102a00200c104c80d0200300c0e120008004e90201e41904c0c42c0d0140054803400c120003503 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 223194082 1250 223192832 223192841
    0x33009011d030304050717031e07020118030309120807050d0909050109060b04030609050a0203100e01140103030e010804061e061401030c0507080f0f070b040b0f0601021b0d02090910 80
    0x1c00501e501c18024030012a50215201c011100d14a40c0e804200728450300030b60075800b07140324074101404516050303190010008001c04c2454400d0b42d9440c444a10041030800342d103914000500060028a414000c2c0000135030755071803160080100504000c2180d644d9803a000820250500160306124100142c4440e070294601400c0d08035003e112140c24002520b402d801380348400b03450300340ca82003c4802d000d018450002c001e5005015500329a00d001000c0e00940300e40c4401c1000e640ca410004440981d207900700c2816243d00d0396682c4c40c0ca0710000700446603488c0c044c106645455031000c92486245000c903103507200290307580002c117500c0c0c0303005040301004504004190515040c0650f410859901000312503c083c1d12103455034592244920a07440c50286050b03882c144440024454103110071071044a03c110311070032159019544a01c0c0052032500b05032425805640620035503100300c02140280c0c528054080c01049040625800241c11941d040e1244801074010024480c0d5046c1a40207 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 223195332 1250 223194082 223194131
    0x51902070f021f0c030e0a0e010b0717090127152708030306060a090806130605060118091a030d03330306020306010c0203010609060501090f050303300901 68
    0x8101c007200f400044007600f84034500d803000f810031246076042c090070342e1403c0000002d0b00034910f0303000c0b0640c2c480c0c0f1050026800030b142900d0441c00e070312a02c0e008458a004071031302c1410603510204404407100300078480112a01600e4100360f100040410b141c0300c00c440d40d000e924100d6462440b50840f2107518131007000005843c2130185403448003882b07000702c0003003101e400810548445540b5803907880c08403001c6040350406102e41c05444103022004603001c1400f544540248010809500c41c1801500c032003172005455000c0207600c400400007000380b0383c4031a9101e8088050684800044000070b402c101407116071401099a840b1400740c070510304d1491903107440c8055268852140450300e101d10101080c0f200400b40d41d0000300058082e4440c11080c51501e9010b0024094592108000c502070102d5014050000b0400d500009030705e110900c0341412118050040c61401a8000708c0303402e4520500d14512540740a030002904034031a0b031454034410100d44000140003074003003500702d151268000307 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 223196582 1250 223195332 223195369
    0x3050301170615060307020f01050106020604020a1d01180b0301021209060c0a050906090414041a09030a0c020d08040b070602090102010f050403020c121207210f0c06051902070f02 79
    0xc0c100403520411283d100c00d040d0b0704481082d100c2d540c17010100d20744080d100ea100c08a500b082d00020b45640c0010702c1d580118421107032040303415129601c3d00000c84c54106030950480e107000040001a913003c2000200c030030f00030400300c0c1c0a40c50380003080c00d80e8030031344dd1f044990300410104236035880c0034014242c01c000b0241005142c0075a0781001001c900480900d03d224103000204040d00c0d69960340700111405403e40c12011a01e05030070324661510407401c44c07071031503030f0704400240d0010000f0007200c010100360f4480746038003002e50b0284100380b40241011242400200008030303c640001000d440c0305885144007582d42e0354000e00090030b540386401124803043c1404c080c0b00000e600841c00c900310780800d4035000100d070344043c601440c0050070741c0d016440c000000b0303030308040c841c4122605548c0201e4158207000030f1450042112070744404040a00041d074403a40c00030006809411854103d0030842c0d488107400401c80d030070b00480e400003a0443d46000225800c004504000050048201051 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 223197832 1250 223196582 223196593
    0xf1f0e0a06030209060d0f0b130504031106100303031e05011e05031902040507021c0c06060b0a230403120c110a0b040603020c0312010306050106080a020f0406050c030d05040305030117 81
    0x80204017140900c40311088081d48076031100c85001140d030310120700c9440027004104030340382889800d00109001d803400d03000210f08084610f0b41010003da014010307141c501402011610b1910210003c100041d500081301c146281d90703041d016407074001c0034041c2c120a51205d1009403450f50301c0765241101c7e406680a41c0160420719109800321042410003901030718046a1a07541c11001c03800c10426811501d00c01e0b0b101d248505505500c0200700c0c820038460b10381048504d44500d4145090b024052001002a40388201c20241c4081e1803003261042900c81513090400c1c0e16540c03101070402c55821b204d000149003d44035001d0150515004881070020340322000501d01b4100451864456400f4180900d6000940000718480400456030300c5480303c46480b80320358480c54600054032080c8a01c100043d0102c0100307060122074400c941402940d10b0010340343c20314090059030107400125030418136010501c038007c8820814003c03e88114800da89441d902c1d0305002c0d40c0348038074641d41d031400345580c0710 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 223199082 1250 223197832 223197847
    0x10906020c010f0f0c15050109060603060b030a090c0803030a0903030c0e100e0102030d14060f0303160209040201050408011b0809030f03042a1205060604020304110f1f0e0a060302 79
    0xca07a43d116038031a4039041114113007000050350155260280100810705d4034040a282d44043e6001d241640d042a40c1402440c1e61a881101035420034002c1c2800400c0400c042080b080c0709601c040d580502c82d85500903419030f2a842c82d410364000301c030022030290b00c5001a40800d40e040c80707650040400c90501a4441c540a030205505160040c039080a015403d005907030160b0080082c0d030800d01201c8018011603038542d580d9050080180c0b00280500c1030440b140345103140101c15121186009610601c4400e0207400300300321508003900c141d061000c100008a02c1031028002c048210703c103003201100c40e2500c44401084000000e100c1140d0ba001880a51074030f069000c2260340241d08082c0c00c1040e1480314659032025000307001046401e610610b40060020046042c20b10054001c1c804c0d2009540c541c418001a40300464000f03180d000d0502810b0510704c0d06003211800040080d00050020398140929507881881e001c140000c140c0405120000d440c00190301c4025044900e015800c2010 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 223200332 1250 223199082 223199087
    0x50709091109310e07060e010804060207030540061d0a050424090207020d030f020a05240c040308120c120411190305340e06010906020c01 61
    0x2480501c0e44a0b0355003000c81c080d03500c41c50321030f0302030741c103c100c1e03107405592400d940d54009102241901d66180a03035a40012005d00a900849501c1010784a600c3c159546a807181e000b580034601c101c003444020300103180c44007611460995104000d0101c20320f0b40d43e0495080d04813440c1c1018500d00c0c43c40c0003006002d500d5010345c034004030501c18680e00001240c0b880004590b03442d95000a030b04140760500e603810394008548858405080207090003178080c3c41e041280140d1044880c065000440b060301d41c80040d201e03643d0b41c2c2c90004a44141c1c0c9015100d44c4c1d803142070004081000341c610346159640c4460481160405400c2031085401601c0c25140d03030b440000c01c4c05130724a00905815a000000c1c04c01818104a4018140d001c4000b00945094a81500d16015128056004041041041d0b40000581580205484e00100117101d403d16245903186c02007020071520140c035004041c2ea18071f6440c400550806050b40c1c200d8610300c0c1c60030340001804084140d20079011503004070203462143c1d8 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 223201438 1106 223200332 223200337
    0x1704030b0109050403020d0e131104080106061b0b0403110708100501051e040218030a05010606030e06070f0503060a17060103140d02030d150b0301090507090911 71
    0x3600c0b502040700301c41d0211001005684500c0890030443e002c1c070007480f032151000700700452140c6280807a100b5104005240c029500c400f081c18080c128088c003815001d009507203086011801e608055a089541e03288c40035082030b00302d00c04102818810000030b007203010340360700710752460b55901c1110769034240079041c248407580390200200780c0b0300e40000d54105c03442e1070080481c4044041001c000080d4400d49407075540307480c20b21002d090f5881c2401405005030060300001a41c91902001405840071030481c0181a0080410001240d4000100c1d0464401f10300d032854881e96450041901c243c0181c00c000002240020381d20480440081e009040c0d912a21840e00c48000c0d001e24183d0303c00140c540f4201580080c0141d01a040306680807000d481c80b44144131a4556803904400302c3d507403003078110741000ca031a00c0402449942104465006100c52401000845400790041d529070 = true := by decide +kernel

theorem cover : BRFrame.Cov 223021582 223201438 := by
  have h0 := BRFrame.cov_init 223021582
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223021582 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223021582 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223021582 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223021582 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223021582 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223021582 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223021582 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223021582 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223021582 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223021582 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223021582 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223021582 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223021582 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223021582 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223021582 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223021582 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223021582 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223021582 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223021582 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223021582 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223021582 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223021582 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223021582 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223021582 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223021582 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223021582 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223021582 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223021582 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223021582 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223021582 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223021582 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223021582 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223021582 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223021582 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223021582 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223021582 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223021582 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223021582 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223021582 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223021582 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223021582 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223021582 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223021582 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223021582 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223021582 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223021582 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223021582 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223021582 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223021582 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223021582 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223021582 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223021582 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223021582 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223021582 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223021582 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223021582 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223021582 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223021582 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223021582 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223021582 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223021582 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223021582 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223021582 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223021582 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223021582 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223021582 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223021582 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223021582 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223021582 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223021582 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223021582 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223021582 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223021582 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223021582 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223021582 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223021582 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223021582 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223021582 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223021582 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223021582 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223021582 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223021582 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223021582 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223021582 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223021582 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223021582 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223021582 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223021582 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223021582 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223021582 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223021582 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223021582 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223021582 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223021582 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223021582 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223021582 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223021582 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223021582 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223021582 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223021582 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223021582 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223021582 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223021582 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223021582 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223021582 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223021582 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223021582 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223021582 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223021582 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223021582 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223021582 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223021582 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223021582 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223021582 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223021582 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223021582 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223021582 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223021582 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223021582 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223021582 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223021582 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223021582 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223021582 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223021582 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223021582 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223021582 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223021582 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223021582 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223021582 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223021582 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223021582 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223021582 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223021582 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223021582 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223021582 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223021582 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223021582 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223021582 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223021582 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223021582 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223021582 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223021582 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223021582 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223021582 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 223021582 ≤ n) (h2 : n < 223201438) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
