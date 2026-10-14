-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1238
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T01:55:29.216791+00:00
-- url     : https://prove2.me/submissions/1d0a2859-2227-477f-bda5-72811392d1df

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 222482014 ≤ n < 222661870 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 222483264 1250 222482014 222482017
    0x11d06120103120206040b13020303040e0108070e0a090c050906060904060b041701020c0714011107080105041a09060406051012200904050613030905040507020106080111040b090609030a050a08 85
    0x32400b4030f004042d101812078090380c40d01070481d4000c09003010140068010600305000058003070000d000c4a080caa10b03980304c82140c000a0f000b03148207500000d02002110510740c86581e2101c1280d806201c03e0a0503911040205030328003505103e801c08400040c400d4480344140c908001005100b88482a41e8000701c485a034401c5c003404105042d003405910314210140200d03100c1021090050803050700d0090310840c4a8a072465060400508000b0765200800401a51014000701c4000045a00305454892400d4130b2102201d904540500e0400034045c8003c0b48181d801038100d0004500f42c2c1d00c120126564035013a411141c11000d00403901c0741070040340d4000f0440031101c0008440ca51080343c042007040d00e030446e401800c6d0750001002401c440010f80b2028070051090600c2804251034200040030b9540c11144500180c2d590a0204252502401912900b03000c8120301e924090a241840226105040c42140504000520360f030280d281000140041034200e0305560105016240c40c0055 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 222484514 1250 222483264 222483269
    0x4020708070c0f06030905190201051303120f080c1b0c122109220609061401030c030204060905010e060f03070518010207050d03030c0e0616141b011d061201 69
    0x940c3c1101030100310710b800f034070a001031280c0241c004d08100d00c3c030010b44481241c1180303049041150500c40714040d5040c03a200070001d10301c40e00000b61603111652004101d00c9850071750000300044c440034410000034030781c11140d42c00c040c143c10f841e10301c4141081a140c182240e02142d040056a542600c2d4810007060714000e80b891890fa2144002c050718116150380500702c2000d5000903018221011006100d516842100c1c00780404210a642d42c2001c000b101d481c0d60081128005403800e007840d85d070b03140c8540542d003101801d00f103040908202000b4102c900d54020f89040c007002c0d402e039030003540d03480003940c1e40d2003803031081c26540e03190041e001041a0069440c44030240d51408054505600108100040d80c3c000740141e044485107480032400350803242c6094061100360035090485032108070050454101c0c0305941d48000d100d91400e4440c10000e1400e440740d94200c0c225111214035940c84100d40034000b440c04909045140a604d03643c2d920141e98241d0080c00068584140b402d201c690780d04 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 222485764 1250 222484514 222484529
    0xa0507060e0a0b0c0303061e04020703030509010c0c0506011203050409110408120c190807020904051b04051302190b0403110406060c02012f06100e07091d0604020708070c 75
    0x800603030360450383e049800b41c100b203405984c10a20014845041c540240b03610340040e12041030071300706900c004c24201c0c3d1007201c056001a0b2550100b0000c81030034001c0212018039842c00c4174040401d9110780d40c039550107000b6582c0d200140004036090611984c240c601a11802e8010000e6000207096040b00c1d038081e201c0c98090380103400c91701e412449002c05541840d00c0031801b8140c500d0b451007010001c01e40341c2c50215481d0006200e5071000d40c6801c62202e00ca18400d03402441c1040b410524103e850100c00100c500c614105806c04c568103a00640001d0116030541ea8075100c03240034200440000340d03d81000343c40704400300b000800d010fa8007d881051940a1b14200005a2107200444084500000117408a920000340d13114420010045442880d88c500150070b4007101c0c0b03d521402c00800355078072401a0201e803000c1c03101c462079a040540000144c01c5c4810380a00c0c0048455081c945692018982d042c4100045da49880e80d070100c9502a0340205203075942c90480c681000392440780e01070300c0b8 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 222487014 1250 222485764 222485779
    0x1401080603030a080f0a0603060c020106090b120703060b061605060a15060507020d020a09090c03060e19031b1a19050705040e0a060308030405100b0d030903030e030a0507060e 77
    0x8003103003000700c125100581c40c2e0391092025542c91205210000340500745198060740c45000102044951182004c1e01501c1d81c00824084d242c0f0140314142d0384110b4066215540f5030806400704d81002500800b2039501007004101d58100c5400242140104a1052107024034078115104005000c0703176603413241910346400c101d00c1f40902c2450040941078021a0045003042240c803000d8900024407001e01032000f004c5c2c500880c0c65a55075020f85031b07500d2040340e501c1c004903800e00c100009802800320381c020341070041403410485140e41600405005019041c4400c880b8400c078040740000c840b40d4410340007840040341c02040050081d82c20421110f0002c0640007020559580e102402128003468156a403a810581442c0b048018243d0103085000c800381d0b1044c0c0000003405810203503100c1d41c010000b40002c181c0b0444034400355071007054114810b1040042c0440007a41188616060700d8152034070207190b040c1e28001c6480c00b40a03000150091003a02030000e005a0310601003903142c03409450720ba = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 222488264 1250 222487014 222487021
    0x1091211121c0503010501090e0402041d01091703130209091c0f180501021e031c0b011211030a020d0212040b0601020f03090a06360f0e16080901110301140108 70
    0x1c40f014042070040900240c40d0a0b01000040f4800c104d50303070024002040080c80c592110001d102c9002c5444041801c0d9446681e584e050250240901d0103040d04034611078a14603002240302090214840020b11a0480c540030035040c10701000a0800880d48142c88403e031200f18901604005c101214040000c4e400700200d42285404c1788040e0840300181c00800d20810380c00035451102c00c00600303c408a21003400340900b0912a8521030461140403840020b1008240c00010600759043d04692030f103d05010703202003118005400c603a441201200d005880b2203842690340080e1007110a0134400403001000c0c0400d2101d010340250042c4000d8003103c4003000745020540c0c580c0a8a01d261b680210b10750300400c11903001e401116030298504150588104614400c110f408103440d414516007000c15a0a010340c40310009c0e504041d10403201c140340549400680c02411003030305070303802041204800c04a00030754400d400c41403404002c01141c7e91250b031541140b13240d03450100d043c40e0010340c0180c0070 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 222489514 1250 222488264 222488267
    0xc0c0a0f0b01050a05100f03020a020102120f0a05070f1e0e061b070504140a02090103060e0a090606060e03030904090804050418020301050109140f06031f050f060102010b01091211121c 81
    0x12002d490320355407505043d00d951fa0400303130001d4129415000941d5020000c00d6010000010021b2281150042d10800c0e41001d020200c100d0b0001070207001440340360384112241c3c0b03411044854150300f0244189030760031031102c0221034007040541c0a5400a00c00709e55405040c05a07000c000c000080041250f4041c0c7da101d0070481a2214040c42c10300740981800450300100c0340340c0050603840c04c107060210b072155540c0d02d01c000010f8100d40c00100305681c0c40d1110100591030003040001c0c0000d260083e00c01d00c1c40f00000b9168800e030031005201e81d9031341c03110a080110071025607000f0200200200300400c40390381c1004180400150403442546440008100350381c051080c800000200202904550b0f82d134070a074003208034068640c0e5410b108071011982c07aa0030901c5458201c41401c4c0000c201e50030a4007101803e144083c001d2415a4100424440d49980c0003001d40125840c4403d400581c50700783c02d10a003001c40b5a0300064002040c4c81c8040c50440b4000b81c2ca0b44007589078000070308071a90f00c00c1e0 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 222490764 1250 222489514 222489529
    0x17040b04092004050a0303050c0a0507060c0b09060c0405060a09081f0b1e10110a0c171c0318021c031b0503090907020f07030507080709050108060c0c0a0f0b01050a05 73
    0xa40707070b11003000d034021b1000c0b91260b07011300303111002c00701125800c01490b1103007440d043c001d510440000b03091408002c10005661203440d00309200c0c00061402e03040c03420038604540581e014007401220301090000704188150781c0b0400030480c0b00e0607116025240c402e544104c061003140310a00f0b0741081c456040604010700c0000b0b1503100c1246544440c1800b004014148a90303c0c04241041000b104211400800b0b01c4088595407090003013070041c5184c1491580d00c00701c012140f0075260807041140000ca8201040e80c900380e40306140016800e1024442614440314990001c0e40207411a0719489070020043e1009924030700075143d00030030120a403104400107240110040c2581c10600c807195080c00c1c0b40d002550000f0950050300d04440d040c15200d0b242412960042c0c03425480301c40200312032001402204043d044e9100c0602140d81800c40d256a901d60141145035440800600f4400c0c20006110b20522141d01030520000c02c00ca90a00e10403210007806203e106441241002919180c00c0b01c = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 222492014 1250 222490764 222490769
    0x4050c0307182102060d1e0606210c171e0c03130b0a090803040507030201120e07030b1305060702150a0c0e011d06070b0103140d0c17040b04092004 65
    0x3e500f005841c0c00e07000340c0c040f103100b40100e030070038000e10042034070a40c940108000040048007442415549240501c20740c2e1941d44032006010400c0088080444c2c40000050a25104500850107801d6264105c916003404030407a4440c0d110341c401d210044c01c0e40c000c40204600318060701102515115a07103140c510081c0c2e04603071f100786003100002c00101038000d0709902480503403000840c1a2151100303241e9500c12501110f0640100905004543e0020408003000740000c00c104034201a0700005655000e140c000a007028010200040e140707010040b075648401c0c0d203e01903c045041c141000380d40c0304400d003019000c0c01d50210004080070118420807207242c1d1236903140280001c5a400540d1100640202402d00d40b0f041080f11030580c4540000b05202c51140e09004520b40c518100003410014403a881d00c0c2c4c58201010301119694464122254650084940220101186001710580c23181e50700c0019040d20102d00040c2030034065200e401c4100c6c55800d00c020881900190280e02d10560 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 222493264 1250 222492014 222492029
    0x9060b041512051f1a0403020d11030f07060915050f2206020f010f05010b0316121811150d020a17040807140d1706030a0204050c030718 60
    0x1403004010340c1e0381448115400210718100075a00c288601019002e49004031040f45020300d2003440c030780040300c002811000400b14516200105200c0341001065841581f0011780300307640028207181802031140c1c0800080c1001002c4450100d4a1643d03207407250860320501021843d68007000444058149c1d1030700038060203545083c5400c0900c1811845500700c1866000441c002041075011464054420006010146c006002c0708800f0000c55007074070000310340000702c103043c1001007150b00e19841c25241c00c480312044030702ca13614100004881c40c0d08901c2d0402c981d5802c2c6003003038501d44170038240c1315141401030801c03c600140d441c05008078044203450b5088007480401048a40101e00e9018001c450340901d49238214100300d610701540300303400307a800f5220b40500180c007030704110b251551980584005005400341c0544107002410021240c01c03032100011001001811954041c0300301c6c0c8150794020020062814812180c1c40190070480d40c0d0008102003080660704061042e1900007110700b031 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 222494514 1250 222493264 222493267
    0x2060a05030421200c0a03020108040f0c0b0d0b030118110a09231807030b22030903020310020403050a020d0204020403120e0f060a0807031508070603051009060b 71
    0x150895240c1d000500a5504078035840c041d00c541045034407a038500039001c1d40c500014050884036581d014144109800055008124409098036428000c1c4100c9409084c8800381c0e9a460500c150385000d00705c0001c5c140c41080602207440c041c4403028100000344580c00701f0094000d001810b00325208100313280030035a540c45c44640081e482c1140398059a0700542034080180d0344070700340170070f481c200742d8a00801140c1000c000000d0854560b0f171580841d8041e8060046018501800e40b0b82c06103020280c0700c05040000a07464054400d5611480d10a40c190802c205000c0d080050249080340002c80c403034043c82c1140d1200f08040c0c026142903d4011000d01643c0840e90308010082c1c1420700304a0704183c00340310000104100f107903100040f00554441350842d02140f01049007411484010611070203050042e0040c46500c0034485a06c1203440c14002083c034405022280d40c0c08150780104007078422800e0200c0c640d6410303003042d40034190000c00b04940c0b50328ac0f50040e080d5401c0c4d01030000e400f2070 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 222495764 1250 222494514 222494527
    0x501090b0f040b03030d0e0106091406090a0e0a0215030405070e1e042108100509010308090112060308040b120a0203010803070b070504051809060f07020d120609060f080d0504030206 80
    0xa2941c00800f0700d80000f0b08407031400c00244528000d9803e421042c4855075903508040020382500c0c05100d60045650200b0a8079150000024001d44800380550301082d0380e801100300700a074100900040c06070001c0c180503509003140c2040c0e109a10889046446015042e000101510155a10f038012034411038681035107040e8840100d99214000c01c117a520005046105542140411050103c0c111903a5464039501d08160443c009040740d9000074040c41400b001040440c0122003564084030092800d50160070140d541c0a01401c400d40001d06001d00000e000582c3d0007000000b4803902514420110803503a401c0c20a0049000900c00c0c040240c00401c4600000b841c501051540031120b81400d0b402c103501d42d0b01085040060704440080210b0600500948034000c00c2042d178015400480c80405252422000b5102c0d50b20481c01030a024004001040e510500d40118005e0501003c081100d035036903907010200c6559034480e152590140b0728907410114415001c03181501c1d0090517003032900c0c2 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 222497014 1250 222495764 222495769
    0x21031e0519140c0c090f04021014090a0b0c0706050c070504050c040905090c0909030712050a090314010207120503040b19110304111c0507120c05100903060501090b0f 73
    0x8210031855070401940740d40001860841c1400b4010460310080200382c401d2941c0140101c104003d440c80034540c001800f0000180d44080240c032469099107801c7c06484a44a6004014000c0c0600280e01101928020480f041d448c3c01414080078440c00319403202c0d540d0003090b18140715504944001e238100300c0e130600003402c16803c415088018045001e2400d039548803030000b21581070b1111065600050004c0c40d191502c411700301e403c071502001852400c550ba5a6684608901045c800148040415003030340c51805100080700664002c0d160340031346208040d005000354080c0104581000f508982408028071910a407031049500081140b103680b220360a541e403103c5c1c2c521f0441100c40e21042d017010b0b20041e54002d5409103104200540c6840d4401d4100307c2d500c04144c801d010b2549500c41400041040042d82000300e4011001900c5402014241000d00e288180c002c550000180001310b04166840185c2c4411680142010812640c80e925602d042d100322140340b81d880000700003200c0c10751 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 222498264 1250 222497014 222497047
    0xd0203060f06040e061516030809010f09030e15070c090908160f0309091a040b13062408270a1e14010c0203121021031e05 54
    0x342a819585080000070720543d0090300728494280300c9506220950600b508092100c0300549038003420038810500b8414040c046040240030080710704003060f29070501398001ea046810741c490130300040c44107040190928407460403d81c0952141d01004c1503400780305058800c125405840140c40502d0107460402170305601d1400c2e00d104000308490380688000d4240e80041520038001c0c00c21f80c1650b4113029094078020f41c0100012410303c5894180c140704c801d01302d0381405040360001183c5219001142506444500401d0154030b4603602180c0880410700907401841c0b11081c2ca6120140082d0031981540e00752811229104080c442c0001100c00381c0c9451140c80e0207030304542a111143d204c080c69120040804030b225040203101006100c20105207200ca0218032000344040138400100a50701c0c4901904490041080400700d4034610b000041c01d00240045030514001e001c3c041300c0c018a80070031002c1280491145906020091401002c2d60040100364803818102440c000001e00b01 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 222499514 1250 222498264 222498271
    0x403240b151e0f1207050906040e07030e120327120301150c110d061b030c02070506210603100c12060608060a030201260103050c03122809080609010e0607050f0d0203 73
    0x9015003403140400c48d4a0f0a4003400041c6412010b10b03c05050800c0d020301201c00e12007818916801100701400461390440491380c2046952940c11ba42c807103215844401d264000d01359203014040e900d10b00340d00c542254040c5050b198075401940b800c0c1c40310002503541c0b052800700102510440c10030946c1c2450000c200207a090300490000c24640c52802c0c441c180640d03d04540da000c640e48008200c2d050342e04002410186c06e00b03545140c581049004034403c0d105000342c100c80d1080a03000041d5094505000c4d2100d903c000c4c540c103100c100c00d101d101030503c00485441039110751070414001081803140f140030f800b418010340240202419178004540c1812090010408000c843c03129031124800580b11600960041300a0101e10303c003807041504160f0500340c1d9640c00b44081c001020f5201d080f004141c129044140b0084032441c11140c140c40d08881d03503000b01028000c0b88100014900103412561241a481e801d9034140d540e15001238840d80204a40707140350b040144203241c280003c40e402541c0 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 222500764 1250 222499514 222499517
    0x1b0b040f02061b010606110706050f0d14130209060a0b0904051503070b0c060a050705030a0209040f050c09090106021209011b0b010803180102030403240b151e0f1207 73
    0x2d03080350380c6800c051040f840f10b100c0d0003a039540c81c001c0200f83e41c013100460741142500013404206190070780003841c13402040c0c101c050002e00020a0184e110321a07124010408003101ca1301c4c001c3c6004d031030484000000318007d80c010b0700c0b40c00000307459282c64907144041c3c6804502e41814006483c0510004050003800d25039542600c204440c01554100715090041c01402822a91460144529402c01802130070f0800081d0804042c012410b0704042940da1081c000100141c403800750f04000f60260900c0c680c0c0801b040d15207020320a000a03020300900708080d00307517504401030766955400c0703a8810405156201c03055080c0110600740d0b100d0200c444550110100000d0781c1ba2164a07050190718082c1c1c00b0940710350000a0b11003103043e0a802400e54845d0900155090034034540711104a00c1d860b4031490381a10203030003190300301000796029241d100409041848010004001d10600e03030b0040c0540080e61000e220407034410505d0004449144850040310360400d40c4c650580c46501c02e02a20440 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 222502014 1250 222500764 222500767
    0x50a03090b0a06080c0d0b04030f170709030219050112021305060a020f070806061008090312070e150702061206120f01050703060806270c030109060b011b0b040f0206 73
    0x2020607040503907a03001e68030490740065110719100301c031482d10b01d6400c002405000c3d19184100842d4030526070944c415010b08003280c4c0110001030403034003c1062850302031141030007418002d5040e07100d152142543c0c8282e4208030f1500b50090441c0326440284a128000340950316000001203458010340a04000304a11340711003912000003da843d00301e1044440103034418100c989444c10100905001403950001400582c10008080390038510080d102005003c0001c0110318081810800c655484818040242030341c2040c400040c05201e10300e8045108940b4800c2025036640d81d202100c52440e4024001c80c40e059010b00c01d040c44800091010340d01c20045c3c038174200444010302080620004101c00081c8501d45980003804a403402d40107521180e0201c020031503020000450000080310504400842403880c6107428640348078071208070741550030701d0400c80c04c00616801406400200340c035102c01c11865003d00415410484502074620592400400d0110705500c203080d000a0020384602d = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 222503264 1250 222502014 222502031
    0x60607240207080d020306040b0d4b060f1406130b030a060f0f0c021b03070b12090613030c1401020405060f03090d1d04050c04050a0303110705061603050a03 69
    0x1400c03c0e800c100c42460f044c94001040040e00e2510740309005000508403201e444030186510303815045807041d000c0e503040030008260110011502c2001281c0c1d00d012403191140702c074a00d1401180400050360489021b41400c203000110881402450501200c00c29013040381e070b0312a01045034000450210081c90b540d102d8080f213040d01d041c845020050f02504011405015240c00306c811200c2415940340603610742050442c9031540410345c1540e0b00d1820702a20200910103001038106440c07680407400c5000005402201440d10402d405d02c5880c06406036201503440420900d80c040b0403420050000303051064504c00a05d04d075281078840289107000604080c1ca41e00810306c40d0340301c1091103c84442c0802001400e0304100603045188080e0f02c0c2c0168042010084080a800f01000d141e201d15118000920b5148603001540c00501004ac407124800c1e9903400c01a0802e007940c2148030035401006401314007400d15104407051044156a00000b5001070307102218a034010b80b5240c0105a00d5003500b = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 222504514 1250 222503264 222503273
    0x2010c1b0f141e0f01020702010e01050c010b0901080a020109080a0809010f0212030a020c06090d120902030c0411040e07050301050d140a050a030201050709090b0a0e041e050c09060607240207 84
    0x11080d00b066000220003c80318001c440601d8440d00d00343c2445140e004001c5d010060740c0c00728a40c244501b0a00308180c80b012440301d40b5015106003070754140c004541200001c0c80a00008900720ba02d4001c0e00c030034031000e80755007440f070b240d00c001080509105400c01c1210525445030b2010a000203007481924045140103030351658030f43c015940030320400c0e0041001c415484090007016040781c01c0174010840c085141a000d802c940440e45044411540c81d141c00081d5242031082e2000e001004008100c21110300788003481581203401040074102c4c900700080ca0060046d002c80e13050300d00080c01806071b140340350750f040d0f1003070500414200540142d140c2c480004400700800302c443c2e4425000030901e0314150500401c503001503070110128030304120749250103866801c003090a0300c6291071105e0290f592401e1000049960014510499594262003003c6c450041049800d60408840620f055100c240030440f40d07014002c0c019004a650742c185200c61001c0400000c080000118007504082d40c03a00d5 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 222505764 1250 222504514 222504523
    0xb0313060908040e1528080a060f0b0603130602071703190b03012003040c0b07050321060907111c020708070b0f0301120c0b071202010c1b0f14 63
    0x142166400c402180070322030b0401c842035080d40f00d03420000310540c07280171400203140f00901c0064010446004091100301280c6c1003581c0f0040c01b030b658120364860100f454403400a00104905040b018075080c6042540c0c5081070450780919800092481c040c1101d0301c404009610210b8100c0744540c0c0d01c2c0d02d18103148100700140d48250000000100508107894610702036401c1d08941c1c5100c3e0b494240b0304071942c00c000e14980100c52022001c581c8a0f0342e14a020b48810302180c008043c035881c086040307010054004010050b40605002ea154198080c3d04880e18801082c0c0f4035551043d010000580180c1c86100b00811130741c0e40c0e0049a82100c40a000f4400100e4034003082c2d001070704000c0781400244000c00244000b85407070080249024150611030b0428041030041c409072803421103c00c0705100c01c0f602c00303e000e0034403001c1c070035580c050525201c410b15001e0034020b07003d54282100102e5480c050011180180030040d13166510103580c0da209900040b114074100c4d43c118251920700c0d2400c00400 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 222507014 1250 222505764 222505781
    0x90307050a03051c030509030403080d180807110a050112051510020c030f030405091906090204121101080906011401020a0b0a05191118010e030d030b01030b06040f0b031306 76
    0x20082c1840103844100c0101051303201c520f00c020f1605040601c0042000007084a0840341c01c569841c3c0c844158441c801d006d01300070090a200c175040d00c0355400600200c00020944a41b1640c10b0507810003c1400b8000340311418883c0602265918803c064440815003019900046250022600740a501c0c0015050a281407523a00144d102d0071000c00113043c10043d20740050541401036051a03e0000094910407000300340d0366050307903c0d804011000c1269001071002c1e280089081d92165158003642b005481e0b0440242d50312580e49181c045103501440d580c0d03004003401c80c00750006a00b001e261034101c1940786562411449803030300403400700e115140b100c1d0050104d65000705042c20314540c08002c0f644408011101d540c5811142c4c1e00c607000810880c1c0b0a4030410704d54000030541d020050311402c4400d509281c040c0600403007201100d5041e8043c1220700001d803130070042114203805004d4540141d02070781007441050344003803183c000d1a602544d40005950350101c80071a0740d503580340a49001e00c = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 222508264 1250 222507014 222507023
    0x705070b130605121302010207030b160f030504020a0303031107060e030a0f022a1807030b0109060306181107080a170717040209060a08011103100f1a090307050a03 72
    0x101d809803901e40d1920040005054514229040510350860488a0400581014161078018004504690080c40504001d6801180710001450080a007400c0000c0000c28880092907030030000901c81d02a10409005a401900142445081d660154005c10704031520003440c100034409000010a9800380702c99040c0c4910103191140302070710002d020341e88480c50700c0d000e5410000c100d10364007100001e0441c644488812003050209540046190b5007845001484406414130410001c2c54264100e450140070030303030320300e04240d0791108110222541c5000303c14034210071990f80912407160f604045050020048114505a6243d4070303440b40e40e100240110200b04d521901c82200620390710400c0c5c0c010042d04014075032601e03103036032940ba1000042000344103013842d201069660b02c4681010300030b072502d0780003040205010380e0300186c50f400858910700c1ca020140301c0070590300d0802444200321034545200d80340e600b021400c181d0042d00030501c1141c14ec81040800512503450000b0040254041c = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 222509514 1250 222508264 222508267
    0x40b0c07080610051f051c140f011a090a0b0406020a0c09140720060a1505030f1518031c1d1c020c0a030b06010810050a0501030209010201020705070b 66
    0x1e210420781031410041820719000c8001004021503122807920044941c528000d03402c0010403044182d900d0300a4105000f2522210600442d0500040d445451062044880142c85942c0c1036a4100c64403000d000b00e19a14090465089140740720070060700442c10010102c0c03001e01c3d25131517014a960030681c09240140e0001d01c401c801c1c007803090880005059061003e003d070070580708280720512070280a40c02041b04411105016038004045c000300001c000d000d4034501e08143301c6d40d001800403c81660020070920100080c207280009905031841020f501500c0781042c00858040f40640080140c2d151100861110300c00035000e10040440b0100c500404e01c2e50000c0c00081c8080380c01620140c0e5004641045110303040c03d0010b0a035030301c070340f10099820605544500403030031303c40644076060704038080074000b00030072954020301441030708c082e40d80e00115511080c40c000103222520642e504080045020b01a55110750000d051015041c00054a03000c040e681d90352030204036034440f9610510 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 222510764 1250 222509514 222509519
    0x3002060d050f0c0c0c010807030b04090501050601020f031305040507090906031209050102030702010905060f0403081207020f19020607020109081006060318020307091d07270e0a0215040b0c07 84
    0x1002144039003200c0b40c059404d040945030b00203a40e883d01168001414041136800189059129801c2549040d130083c1c4240116003141c90403a010f00000d4030018054010742c902481c688500106840340c2c406403001441500d0310301024000203002c081c02c60300400c40000d00c0413a00c1c05641c02940000c1d485142d6142c3d6a000c00000109445041d8010b9411500100108805070303038010b4102040d41e0088910740d50b10548000781d04698441e642c0300130f0040340b010400743c0c0304401207003200c0e02c500c54580a40702c3c161441d418240e00c0d028041202824480001303006400740c1482e002500140e80f06040c552170480e201c0b00c070540780c07c2138210540d0310541c80382c03005d0114a0b13050040c000c039000c070150058145282c0c2d600003510f84420340a04010346a4519100d8807681d100300c468061008810180c8401d25180c141010004ca40c00e0740d03880d000f00045580820186d4107115440903004102c018040c0030103598200221403101d1103048034804130901011900065540041906200c00c40090403880d2 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 222512014 1250 222510764 222510781
    0x4020f06031608061c060b031e010e060c07200f04090609020f0402030115031112010b0d0509070f030219090c0207030201090f080c010f091805090c0405013002060d05 73
    0xd80c02400680070304c1605840803039800751440c1210007176601c184042000400c0001213480c100c02ea010302c0044981c480c0004052401c10340c40640c00300508410f46069a4852200310410300c0380d988000d100b0348501041d6031004590043c15612420000d01d14540c01d0f42d01800142600e0b02003034291032a540d03807a4503104519040c2480310503000d059070154190740c5081e107040c801d19644e68845040c540c95205c855000a039403800c44500c00350640c1d1300c183ca0b5131643e0500c0c405820019404803980e2500d000702c2c030b4021000486104803039082180001860441d0309202101034214503124201c00034000100c0e20104038002e8100f41402c581c010800280345000040c043e140c1507000c1640459441c42c140050b00c0040b90b9501080001c0c00c1000ae0b40c4a0014100c490789059403105030207040241c140b0f16600095084079000e040124100c8040580400c02c10046840a00c9164401842260118011300001c4429144030342011540e05021040381c0214095511500720468110b40ea40108803044 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 222513264 1250 222512014 222512027
    0x30606092702090117070506070302010e0609010212060f0f1e040b0108061f170a05071106090c090c040801090b06091605040504020304060219020a0303050112031704020f060316 78
    0xa0040d04025041441c2074010440700281070003002c051719007180310210311000800a8030300908016000a41d04c9106080090003403402c00000c080e00c5c0254008150381d44414002d4501c0070700c02258410302c1e41c444404103c44911980440c9030020f032140344225859850f481c1070000090b14010484040701a44100011a100c070001103060009131010300c10ba603201c038224100c0e004800009a820070280800c250b0303617a00031510380c07414054031104011203004640c10803801340c001c0ea250548041d103080d150740d071a80700c126560107950340f02030345071174580c0b07040401175030000c1da0507110a1a054643d2003e900303440d20320070280c401d0030180e000e001180c140306c65010350110003a000e045410102c6603000340103124520880c5d01c41c43c0c0110100d024850540c1c1140d010041c141c2a210101c104000040e442c2e1482c01400e83c0841d2030b10000044103080003085038680c50f45a90780e600303904100c03e10398189203000341040c0c2e0400000c200055032901d80c0c0000b5400781c41038807040a1310072582000200031 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 222514514 1250 222513264 222513311
    0x181e0b0c06060306130b0103021203090603100f0b0a0f0810082a04050606041e090e0a050709050610030207050f0a03050403060b0307051c021504090c09210201050703030603060609 79
    0x5e01883d00049004550740012085c10350b64102c8842150b50500704180f8614000c6107400d5501c80000014403445103400c10310141102c0c001c10f070100c0c2c16a036614000c802c40c0201088400441c10a042424030b484c410080503500c005000a071510340d0b40c45003829890401c01003a0485418980c0f001110f160084288183c0040e1041342d042c0a03170702d84607004c203059007e5441444410000c10500500302446940c034035000d41a106800c0102410000c0340a54610340005c05442d1401744250102d104d1600380550742c4109405442e966283c1601c0a04500030b501500d415119070081002c44a6080400d02640c1c82c0c86020ba030303840d92111b0550600004550301d0234040c61003644a13620400090f1514030138008d07103040c54004072034015040e00104009130b02401810415090005020454a072035038030540ca84034141d0340f80031034681c6895003130010318403244044807501100c1000b00015071181c0001d00e20503100780f40c007144903942e036684c01054035a1a0084207a4a032564082c03810321030300c10000c118 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 222515764 1250 222514514 222514531
    0x71502010e0124150c0503030f0403080a0b0a0611011b020c030708070e0c0f1c020a030f05130215040e0703060e061008060603090307050a080301080c01181e0b0c06060306 75
    0x26812941c1407040703001030940709080c1030b41000e1134a41c0504e0300801201c026190007a05807517407454888a00d06001104884c1200412440000314118210b10300c84c5500415000c0c3c02241d2146c10030406441070600902425019034071084980ca01605d0700140c07035840c0c20709400030101c4040032410181003c10300d8000d040e10f60f00c200420030218035407001540c0c00c0604600b901d582e070f05010b4040b40042c8a04038501c0080052140c01281416080d4010500980190ba00700015024410403a00744c801c20303a000c20400c6070302100c0d003000d450081402804e07402c0c100d04040c07405554003a0810000340860b00400400e948505c200302c1c1c030f4202c3e101c5640c070a0b000c480e0140c4503d030009002e4107856024185901602001c80001c12000d4100100c46625800000700e42c502e0301280340400d042c0d0710901860300c02d4045c150224001d035000c0d4008206040940b55608589401d00d03904074102c00c16120150541030035860700103034903d0a2401011140d00040c090060391820f40b0034589030203c054035500 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 222517014 1250 222515764 222515801
    0x614090d020303010b070c32120a0b15030d0804021302042106020c0106090b100201020906221d09010e06100902130504020f0a1706010e12071502010e01 67
    0x205015404003c903419910072180d41a2542d0090901520b0030741c59800c608a00181003134009005004c0c1340850400c2c0640c41c0c1d600080b003030410280804400407440f0544264041514180018900c40c5001c3d40420352100041c1c889141d0b000003458688481c100300080368200c010b01c829070600b808124000d280b04d1405500d01450f00800b0150307401e191860829203c800088034080000136012150a10b4209009200a0b9152051030004013007030260244603000c02d41044003504c1c0180284c03210107000400f5503041500701c400440302007a41c034031000e003507030355040b000718032501040c181c05089418905403c00c03c0c0340c5044654212000c1c560034007841d900c00b404108a0307500540c1e1003c141c1d55004400360310b0b4002c001061540a50b2500211340c0680003150a0261702c0540000c2c0c907020035240d5480040f5805602c00c1e006010086d981d16001940326044011142052a209049032120104507072607076550307503030711403c001001200c04010f2351500940403014600340076096800d42c1505404 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 222518264 1250 222517014 222517033
    0xd0e070b12060319030509010201090501020307020f1005060a03080c1f0f0f0506060319060906060c0b15061602010c02041a011706030d0f050f1303020117240d0f061409 74
    0x10303894134214100050400c40300080014250f40700303410120300150b00c10002e5469042411001c1d49626409404038010720605022912606d01c038000c0c1e5028801c05003c0080c12400c41e10349601641c4011901b64003031041c0428800316107039540440d29034201030f0000088890740c114030340060303444480035900a581444103000465032100c08072900444602038401d14581140c6002c8041c00d825840801c030b041c64100002100b94108101201c00f81c894407051300542c0e100f51900002520101442c1e400000a0050340d031059002040543e030f0500506080011044582c0014140c2e01110301c0704044803090030039010b0a5801c07980d001901c0114102e410300700c0c602800480c0c0d4501070021400c04000b191a24503000c903006100312542d00002d008144d603030300020301c06000c83e01d409110407030014220200b0081101e86540712070b40244010355060314040100b04102c80e00200b00c50480d07a004064880101c0000c0101c00d059455910984010503440001d12982d04141c40041c000c4c09581c2220605 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 222519514 1250 222518264 222518293
    0x906060316081e01030c09050f0f0103020d1103030d0605030606150306091b0d1a0406030809010e03100e07080c010c020a0e1b2b06060e060d0e070b120603 68
    0x24010111001d1400b000580c0d1203082c0002c00e020411400900d2000c40b000101c14410205403d20649041c06414005600c80807111901c014080340c190880c000c0f401c00620041ca4121019980d260081d40c9032407000e002c0c000000c0c190307480300f500c21251940e101d40400141c01c0502c040b981c0203c040303800746420701a041035116144401450540709030000d1001514061800d60400d06020703458042503201d18810b01c90f20000c040140c1c07000080e0002070421141c41c03605004010940740e01040b80760515003c0001950084803802c0e00b1350381409003480141c1c0724a554402c0c0500109102c000704401e901d0000c1d51404c016034a2400d9041041c80d641030005603e40c1001c5508640089440302069560020301e0700c10456040c0d4114484000003400180010716180240341e04a0320720201320403094a01c0151003251001d20450020500340303081e903680c1c0e1400402801d100785200b040440ca000400b0141420000c40350000d0821400c04520054003440241c0243c3d40300b10183d0007021140941080e = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 222520764 1250 222519514 222519541
    0x70e120d0309020d05030301030b0f102114010e070905010f030305040e0709211a040210050a051c090506010f08030706020906090a060908120711010f020a0b0408030609060603 77
    0x30150103040d2150a203004645543c00c482001035004800d4a8613561203160144d2104002d455224800c1b1008001c92035100040d507803d012911407c4403601d84420841c1180528800340302c0a803a60b840d48041c084610400f0b000f0030103041141d030301038041e103402c101c003210803207406800540b100300c0c3c0500240006a04042200c0070b41c3c101c0c6040071500d544540d012951110b0a030002c04688500d0031081921441c00403c903040c65105281c0d4120310f1a07245000f6890320400c5601a500031015074181040310301440c0241083c81c4145080b0b0301d03044030a80d014003075003162444012119580c80b01c14042c007400744160350241c04036240880140340303020f044954034014164040c0c2085d03030019641d00b850340d07091f0440b00c0003480078005481540d40c602010340311a0b407500c10a0300b50300030811032205060500044a0500b5484030f40301d11080104001125a0340b4501000001d51144803100c3c404030750017200075885144a41da5107a43c910f452014001000d60190103140a00300600502001804810 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 222522014 1250 222520764 222520783
    0x100605131503120e0a05010f080c090a03050a05030c01050709030c0510050706090c0501080114031c09051e010905040c0c2004321b0a050f0f03070e12 66
    0x1203000c03038150024445000204000e500040c000c00c802d07489014003603001800711085603011102c454142da511401520f044030401070321000a82a8030000c0c400c4003410000d0700f4403200c040d00a0f801c49071a591183e290100120040e1003079400841c0890281d4424018940d02400c10f04d081a01c0618550701e4000b001e20394001c0358460440b0341c2d410030181c1d1051065510654201c10706000301d8429003060b00c020b08540c00f40e1800220580c0011802c205590703003960781100302500820101d0580002c04162079080540c1100304080100300040c20303510345a80210040c0109107009d40011050000b400c0e08075158401c902441c01c207075902141036080311000c24500e420244049030701403118031b020404140800300310703030080c542401410041e01100d22104203a4220f4041c0c890410b2038079040c4581e079011140540070b9215401d0040050b12040c0140c01c00303039842d041c198101006207401c040e50790403c1d650707499062004810445541d40c40340030004107140c155403100221071b507494a5601c416481 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 222523264 1250 222522014 222522049
    0x6091503080a02100203071d090c0711030309040903050301090509070f061101112209200c0a0c0e0403020610060f050a0903050601030305030718050108071b02090711100605 76
    0x21800b650402e00030311465900013940001150789251282001e44040d160b404848945080310310000f1150030403007049402400d0201c0c14505202d01c0d90385002e116000303c1c64040c2c050105001c981165162401044203840c4a5250940c4a43c1407508400c1107550050105490354400c0c54104a82c0c003c141902c42030320001c4c5801040900309110140c00341621042001c00b9490014200c030007100046401101140405d8a0301d03552a912495442600d401d014001c01415031a003950b5400400c8000034644500140166907180010340c0b105010464264070070f5a5a12200c002c0001b055414403071258405040d28100c801c05042c1070008203100e01d8250810709024001801e0109a409640268002d560107c03c4916547e140e2070010401e4006075203000110318114906064190002c802c0c009669040e135400e4030b280c2d00e5250840b029030190710303d24170581450326094050303201d14148600c15111500c0e00040d0300b801d01c00440c50800e0030514203601c0ca25002040c0600c0d82d4031002d1000810b0724 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 222524514 1250 222523264 222523267
    0x71e080306091314060907050402251a0c070606090c0f110309030708030a091a120c0708270a26031923030606120a0e03120402040609150308 62
    0x8100f11510402e5500c2d10291003540c3c03071543c0b0903a4680005105100c1c86000041d10b88040d61071083c80280d008119094000b8000021034031580004071038050034140c040c0c2c0c40034000b40041a20446443d03401c0c1c079040102c1d00c00007101d4080c44001d000720300090000c600e00b040011081c3c440103000f00d8984000701c0810528140c1c01001e41c40400c243c0700751741001002d4401d00717542c8884d1103940764810220000840c10b66080081c0f000004801d11851021547c0154586103952003001000d210080450843c100180071200200719844040e008610758a01e00311034815400c91110640b5041440c03151203550020014400030b903104e8588490340c0302558203e01800302180d101811406506401e280d950451380c06040103035401580131030090107020141000c00b0300980030144510045400c940c008004006008000c0808400700398440341d861000a5045038201e030040c107581c084024090baa84a0200303010075440c0c0340c401e50340181191201000028040c207680b00109200d440060080c400 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 222525764 1250 222524514 222524521
    0x30b060d0c150512060102030f03011802040f08150f15040e010e01090308041a0403091211040f0c1e0206190e011d06160905060a05090402070305071e08030609 70
    0x790148500900300501aa000036020018000c0c040c1d0440102c92000c103c0c0340b000b081d0709500100440c3c0180100740c100d203143d80e0030301400b00e010900786007115030f60030b07401c200006207000c08070981d00140c10350320007404000d242810f00142000c809884d10201c1940c820a00c84902c1c03162542c1c504820080e00c0100d00702601004d540d004100500342c4115a5007402c040000301740d800346203903120328850340042c1422207450940c0d50446804a4005000c5041408184030f83e07281d8203005000d40380300700d000448058040000ca001d07200e1100314503018a4455501c00201c1d900206484442501d4060080030141080d0001750380b4500540514004407202030b00143d85002600070b90f01c0c0803101c400274405441300c4031030040c01c092500240d4109010f0b0070041198020048000b00b1810060742c0c038540150309200c1040269030029450303109105042146a50701d07120b500142440741d019490346602d030036035070402c03602c0755111503800940500f201c071494002403445c905036600290309580c0c500c031664 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 222527014 1250 222525764 222525773
    0x30c0207030b04060b0a08120403030c0f05010c030203061c050a030e01110714100503070819020706060b04060905030601031203020315041b09060f020606040c17070e030c060301030b060d 82
    0x1190704058942d0360400100000e1250a8208843d004001d580368090190746030301154841c012940000104c007420481000880e1054001c0390301b943c0a0381e02e1341c041c0303a080d5503102d0840781c0d483d2905c808650044104120fa250980c064072081d01c030325082603154480c9598641d00c4a0800a0060600a030500114000e0b4401d4200e520400c0d5044200e51201c2d84801c12821407e8000541910555102507104c1d5407510880a5038055425a26101c4103a100c2c4039041040e40c21050b01020040e609004038000300b02c0c9409820300500000a40c940e4031811701c00024a06280354100034001e03404140104009226210302d40f00600d1689001602d035255112003203014180030350710b50361007401c1c10040220342912951901041400e91150b00c1c0d1150703658420b94441c1c158202c8500580c003c0d200150040c1000d0700500e20603111841c0c04242e0246540e0300180107141918010f00084205201d480036050401c98841013007801c84080e0f04540c034550301c1c81c244a01c02420b00f03004084a484580820 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 222528264 1250 222527014 222527023
    0x50415110a080309190b060d1401021b150c0d0f0906050405010c0315080d031109090f1e0c031f03050316020406090605030a030c0c0503061003050d0206010510030c02 73
    0x854454007580c100c50520700304002d8075041034454000c140a00d007086882c1e8955041030706001c81c1c2c080700c42c0d40c481e1749020400904c6241c20790213440300d0491510b55540c550080c401003009211a070b42d4031182881035108917240162508110300c03040291030030700c4a102c0d2108291000039801c1d02001c50b1314845c07104020046c241c00c1c84000c0415003408140410060107410020840c4001d960030064020300c03800c180000d8850b440307a0000c41d0031070000c6c00000b0784607800085c400242590603601d0100b00c031011030000300c411940d5419840311102440a5003003541074224408041581c03180b00c43c00c00700c000389060700c00a0804095002e103d402c000c500904400010300854102c0140d0b604c07880c500c038400c080d81c28155000c034402c0345450004200a03e00780300d860151040a80140b540008955066600310003034803065420401c500380003d81590104100c61285004030081c400652940c6081d624100300c80c9201001d40d0040e80061180c0d4480754071854600b00c0d1807601154642000b03d050307060 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 222529514 1250 222528264 222528287
    0x60a091e03050a03030e010e1606050f07020a0e06100906090608071701231c030507080f03130b0a09050d031a03121e0703050306060a090503010203090115060e01050415 74
    0x9801100f203524140354040d07002e030b48540040390090252050100c995910346402c071000058585542c142801001e1107030002e042103440c0481075618201c242e0300001c10100c0194801885c04540c1410041207007400c00c41c890318031356503040a040c4242029800703480c0e083d50b4007403030041044120000b1401f6129801000881e00c03101c01d400d0a130f507159048858a00030000d019812603400c2e81c040c988074246107812040400003002d44525400050f5001c0760b45500c5080103176446a014001001c80d050306c01c0055000c0c0700702c0725228885803000e1806c0301c0306e120001c2130780410703078506415131000c80c00210f040c1c043c04881c0c0c0b5001400c6440000c1040c00950002c4d2066014443d404100350880150380040a1007601e52021414030115180700e51900e1045103002000140140041030311828580060858018036041c90703195240c603900442d0881e01b04494655080e07450b0310001800741007202c1e240c1c2c0078203094030380948440706840c000b0b46184039a20950400740000d1201c10b20745481041c10000 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 222530764 1250 222529514 222529523
    0x2040b180103110d0b130c050316170309030609010b090610050715021e040305010e060c0712170a020d0606020705030a020d06090b2410090b07060603081b010b060a091e03 75
    0x8003401c1c5102480c010050b00c80040710315407180440423856180c0041e40f09607121a800c00e014100703090003150321000080085440c3c4130b10061101000e29074086c82600c3c460041000001020900340b8108007040c0380140c03841c1d020742d46600b030000b00c4513446401c58860541101c12603210b03003200000000280300720802c04c00038002d64101c04020340c024000a0007128007a1009214008980e0b55a9840e40405d43d0b0b0814610010000310000030099002100940c5407814003c907a011020318050446008803001a41c50b64000395941c0d207081c0500ca14006400c0c14030042c80c201e030611000ca5641c001d01080a0700c94a425011241002615080001c1c4140d01c00d0200e070040c1844d402256941c1ca812101e9503078000000640c0220b8201204009900c1d4025622443d80070714145c5540180e61040d03400381c032442e443c0c402c00710129a5440c0140a095071503d0640641003613004920b00b128100c45a061081e502080003580440c1d003c0014016203000703c0001c5010403103994503d0703014071903900060 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 222532014 1250 222530764 222530783
    0x80718060c0b060f0411070213021201050d08040b03070e01020d0f2a05010207120807020a02010804030809160b0a0f0302030f0109020c0f0f01020703030b032b121802040b180103110d 80
    0xf0881224050044a80b0940d2080d112043d41403007127003a80a40c3c0018125410004010415403420040c140700080c01001058509030b00c42d1140085688211940b40c0801c4100301045441e5904009010b0500600d24040c035202030582c10042c045404214001c4400d0920140d10a49541d45402c4441456002000b15600c44181c0307068012200e5070681c01002c2000400018030250000c00c0c0020300e903605958826281d521560305036140c5001800300e1605108a030b009800e01918074002d0006082d910003406d4698991510050801c0301400704041018018014040302004e02c0d40f11a0550340341d003034013580760011809807030b25110100100c503100344540a01c9a02049040d4000e06482d40030741d8081c059100c040c000e160b5110000303400701001091044c034060311030542901c40c10301d401162400480d6000d20b40b02800c00d0f80c644ca04e504d11340d403210170449011441c00348280c0461f40d0055a03010701e40340800c040c4803a1450705100140c450071048210000c0340e55000d01c001c00096110007202c = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 222533264 1250 222532014 222532031
    0x9050f1201020412021c03080703050c09100905040f020903070308070203151305100c0206060103150f030c08060a060f06030b01200109121d040b1201050403080718060c0b060f04 78
    0xb1300c0746200c00b004c1a13000d00e500b2500d0301001c1c20440c403440102500b58440d400c8949038104101e006003401428103402c14018803036030a07036a541c8041100f000741c03256100030740241002c0810045818054004090500c10000e81140d52408103040040326000828103890b000315001290804000b46403608001404808011002c5500c605a02d8602d000d1030403200e21700380b8a011481242c1c940c90300032001d42d0200002400b1903210390860b8000d1740c0c41d41c15096019036030748940d9140c070031160001c40b0b060202400a0044d84001c020559000700d140a050091a00d4200318007440340c0380c0d005050800d500c4084154030340e4080c6801c407410750031a03040c145c40c0c6100f404482d4020203070000226031030b614a2130a8960f862041c40b00300c100c800ca5225151040c030200382000014840d5171a42504240000281c0c4e600840078800e95104600030b8403100c80929001c83c2c014803c0d008680c42300360001d110013080c84405d40c861141c0c1207240d40003d010701c5603100d13100020714030300c241e146242c2d1003400c08450 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 222534514 1250 222533264 222533279
    0x3120204030b270601140402220b12060a0b0f0307050f040315380d06110c12030103030903060b03030c0703030e01020d080f0a0b010c0f030e0108090a0309050f12010204 74
    0xd400b481480e500300543c5012101c0c002c00e8460741d00780701c6c1a0054454002010ba20300c0c003035000305103050300f095400c0c1c402803030341c0c201029201055102c4021014081842c441044404c1c640c1c42d03101404a07000740c045030425094035490700940d50703155211f05000c0001002035000e10b0032214142203802d5403e031525034914080790060700c104118038040303040c6108100801100d001400e409100b401c3d914202000014000d0110f0746903060b49517000b0a041042000711346030344100041007140c00c03180f41c0e49500b0501c10310314260042d40d00b00c640300ca0400c010000300742d000c0c05560903664006070214180c08080c0007c1d140d401001c00e000980e014a581c000101a041082d00f04d965000781c080d106034645070301e0705840606045a10307042401d1240c1c001850520345d9488110750100506100c80340c0107868071007001201e009c00046001c0740390305ca5240615a00044c1065201c80d044004068241c11690300814100c00703031040034004c00c0807009201b5680d0741c02600c11101c20200c002151a1591a0032 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 222535764 1250 222534514 222534541
    0xf0206040f081c0f0801060f02100207080d0b0d05060a0510051c0c0906081203042303030901060918060c0509040207080405040b0301020a140d02071e0611041203120204030b 76
    0x43c0500031524001c14404a00620320744806150a85461409030301c0c0c60000e41b40c03002e4080040c01140180d800c8001c45070743e01c2c8003030940c0d507002d03c01e05034451818070744a5040b80c1d115042e46105d18185d001110024000041a0394442e8010801003041e46844507500c0080203190005603000032000855580c4054264500c0203481c0680740d2440c0c0a07640e04040002c450b02402910803503041184030f560350214260055410134402d070144000b0048140605000301c40711001056550000824054000800d0041002500600c1b008000702550380c0b0f0004800e0448000003000162264504036440e80208142c50030310101600540d521809841d000716640e00c03d000309441540307131207049201801d05100380ca40440080d1650250307495400c600042640201d40c00d005030580030000400014116400c0c128891080e100344403c0303030042d02d00300060701c2485801010071201070104200403210020404680c5806040801d441c0e0703810b69040c800b078800e540000c5e080d000381c0e002340040e103c170205 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 222537014 1250 222535764 222535783
    0x9010e070806100e04200703090807050306070504091a10030209010206100305120f0d0f090b1e060f04090605070c0b0106140f0a0c06060608011a03010e01030f0206040f08 75
    0x360346000a039500000c1244070180001c14034009000d2130207100242c1026404a0780c01000c0075440b40210420149280155000110480006241c40e0040108490800a2001400d01180a0911490003c1300101240541c2c42442d00f100c0c0c0f50180c00b65501fa2a210503180030b0000f82c4890900c41540602074080d5101c079038124010b201d040d0008031020304440b8104e081d2640807020701a03100500100c4c0c442c03038011240c503001c2800e040160021003a40e034403407004ca088014070040b6600b08282488142608010300b0b0280c1040f00c041042202086880000d501101c01c0342c42c40f0891100c0030108000f031207902402005076190130240a58a90000d62044155101d8107031060310b85e80342c03042120401c44180107511610700c00c1c000d1103489514800a80021480c41c9404100071025488100560b209036000f03c01040d80000113200980c1c4e14600281c1c040a400c01d0b2a146515201e04207402d0303041480068a6803180140ba5003c550701c110880c2d000345070b12400c40305425103071260191039a500e003 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 222538264 1250 222537014 222537017
    0x6050c0316090302061b07080a0506040606080c0f09070306180b10051603080c0c0312010504050703090302060402040506060c07030b01091503051507120c0509030114011203030e0c09010e07 83
    0x107000c50065900c00c8081c2c00c20380307034050442070500010300c51400b405400c40c1c40140c0c0b0350140c3d640129030b0b52000c10a000079280500d00400c40c1c0e0505081c08411121103801164240c2c001c455400c1494440815007000f00800351070030803040c0d458800890040038103400680360303414174078100d0b2660442c541000b5140301088075049540c2400580540c1e4034840c0d40601d04081c2081040d140209000310188ad41c000c00080318180b900c14055042c6040d80e01409100101000140051000c0e00341881040c1c0d1142e2107003010011b03030126480107591410001c000a20607a224800108140c5960b03081d00c000e001442d0440701240e80b6441d1a25500009005a0410783d240c41d02c0e100c26040d41c000f0000850b504140a0b0031701e00c10700044800660401089179080c0304200d400b200e6080c1c0705219584038411260b550301d4882c1e282800f0103007075901000945072440010350040c02416045102403920540c181000103000c6640380da441c3c02c00e00d200c0718841c1e008541a0001601154007400300e44140c040c0e = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 222539514 1250 222538264 222538291
    0x230a090509070e0a090e07030b040b0901050906013006020c06040339230c030f031305060c0a06050f01140d05030d020a030b0409050d17010608041e06050c03 69
    0x5035181158014240303150f20760300541a41d0304000c20350150340441d06182071401940d40550300e0b52075002d90420240c9084485010880c100480d8003400c0c8241500815510003500040d45000c00207021000212010705440e03d903202642d49145400c90040c59659000800350346814031292820b45440088034140c0204250302ca0140300d40e82e407110090007850040d90030b210300300c0010508950945540900711203402207030030f9020300d41210342c1110207078891700402401c400d16900180360410b03a81005c00c21980d8010b0042030425601d0468401c02e5070400c3d074009840342c0880e61704a10348082d8140141c960391515040c4851260703a48480f44c141d80b04203580410014401040c4020b4260b03078403015110b90014001200c40150a400078040d0884a240208844154800250445600c5107003100c85030f00480c0300301c0ca4076402c9030380c0c009041e4208070360600541c034033200035264000041004040200c41040a40c1002d0011011644650030074003c10007072904144031000e030391081c2c1d041403402e0348 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 222540764 1250 222539514 222539521
    0x303090f2e021b030d05030403170406150803030c0301051c060f051b070512090d0c09020714070e0f0c0415030603030e120304050603090a0519030f0305041101230a090509 75
    0xe03103071000300e81d4001341c0100307034040c1c8042007200c1642014000700d08000000204007103c0c152601c0c0240140e00410000403c15400c000b240c009503460340c890802c9401c107104002c5440307000800d690455806071101400000c044003021203203c0c00510040ca010301e0f014812601d00c0b2541d201c54480d0074400e901001c52403502c4607891a034000c03894020080e81c0f0520841600e80c06071400303840004005000e4a0200390181c3d07074001c182031642c203c1404a540403d0500500103601100d0141034052006800e5090501d1010414481c1c010648000804204040384c0c41c0103030b00c2c0864000b401d0001d241700210301c009030300034081c03c5107100c00d50000e03d011103c80c00074900303054468000744c410f03802586030034a004c0070300207580c0004124204502846544101040e401c1c803810100954070742980f10214858600900f03c24041007081c000c240c5068204000101c459529242900b0242010090061385c00c0d2150781c245410004400c0b80c500200300310100603000780466054803021202880c15a4 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 222542014 1250 222540764 222540793
    0x60603022403071d060a020318040501030203060109090519030f12060f141f0207061101060e01120204090c0f18050c030121120e03060907050303090f2e02 68
    0x5600c811004074800800c045640b41d03008001400600392002403004510343e01c80006400c1d908840c0d04000075800008211300b0b0820044003014010500f190100a42c0d41181c0201c0c0e42d988050184010303140c0e940b00e9500a0120070040c00c0700103252182c45915502071032600914912000c48080d022680c110520f400741c80b00c034018001611003551034036400e50302d0040c420b080c414042d10b1954016800000300d2000280c42e194103c044903c071740082070318600d41300d0002c05461048445030a1645130690501c1041012220941151078074003141da0402c2840c0005001486010030040011182110014680c1d10400101044813a00b16407a00091056400c3c10144c40d01200e4840b540c910400c014007122440004902104100303c10020615581d035441e0118144640403503008034142121610161a0800c2842c0e07101c1d03102e0b0f01a1103070714540404203036a40a070819071845522200840791968940c1b40d104004c0030150f00540f03680306144d840d004d0122400e000040010b001784042c40418a = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 222543264 1250 222542014 222542059
    0x90c030602040510021c1b05010606020c210c06030c090907020606040e03030f072105250203180411070819020c0904030233180d0e0108190603020d06060302 69
    0x90403d01a40b4144601030304003260103c41a6102c83c0c440103840030394038003090b001d106400c050014cd400514103a540c0004001405401039095a4401414400302141290203c2c2e141140031003134a44544036214403942101030f014694100c0d401569042c1002050f650010b0114050b000542e005c01058800da40f2040c2c581c4400c482c0044865035620110b800c0700d1144002200f1111b011003290f071485d000c1e00c2794000360703401610f0410065501d0150807941c00501d982c020b6160355907000030362a044040203034481d40000e00ca8002d110383d44c0c44815441c400054030403964a5030340071b0b800710740d1040c80074034000044e08001c40500051192003410166420507850050085030103070020300c51120711000145081c0c0c10111820341031102c0340d259486000124000501401b1032004ca02c030301006040c022850b0602c500710041c10031641c052916144d9810404603a000121641d643c148000c0c0180650068500c9a10094100048411907018401d4640c09081942e01c21500d1303051511800c3c3c901d80b0702 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 222544514 1250 222543264 222543283
    0x51c0c06031503080a111006030507050d0b060f03030903010603050105040b06090f0103121b0506040203120307140f040e1305060c031e04110603070f090b040305120a03090c03060204051002 83
    0x71050b01c4035043c0003050310030f005841d69a0f4685007403003202c41070071010b1381042d00955030001000d0316038400744204442404684003801040e512451041141d031030399005124080c0200307009400203804a805a202401107a41c5c0b188050000d01101c2d540c0d00e0024000d000848065880300c1c4c1c410041641c500d000c1210b207000e100040141c40b500d03421034885101c06011048010103100000d040000902c401c244041200340c050000b405592416006250078940c14a00c030021540f001c1080102058014085890204800b0300e41915010700d1030b901260b074400c0d0741050040c8001c031001c100c0c01d0303050220700001e850310410554020ba16800500c0c4250301003900e60070341e10050200780d8080101001119580140500305001a41040d64007184c4a9801507903a02c0028011800311180c03950020b4404004018100d8441d16152031a2146600d407001407203072408140e40000c02424040c8203401c100e49503900410a000d0742c07a6a0714100e03000794454402d643c001c6900b07400d0f481c5100e002160300301e071 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 222545764 1250 222544514 222544541
    0x2090c0a02060a1107120302131214010e1f091401020301080706030504051b1309030f110a05032a011803080610080a111b0606030705060309070605030c04051c0c0603 73
    0x240170059a546030885407401200c4101a400c3c4003242c1c050f0074001030b2000a01c6d918661446090850038904c0384500c00f41c034840d40e580c1c10b20200040c07540c1c000a540c00343c81d09030b05020002506900c8444090039103c0313405003048283e00e4110000c00d106500550480d00d00c003045031110b9960308001d5080e039008840140190f000071480d00030741e400c900c09820041e00f0007030507400f95403200e401401c200c031459941a030010b00f4030f5203401340c80c580016021560b0322020008102c820003540c5c8085e542c0c4203403181103224902c414101004a0180014025603204110080c8420004444c0e44107111035170808c05d03000140070901044e21410185007100b000051556082c500ea900c0c034040102a10012100d44801c10040116000241854400c40c00255010024108078180030301014503040d90341c0c010078480d0030b04100344820079900203044401c90b01d0505103640ca90340e54602100250099520003038100100404841064070300b0a1100c1c540d034850f0600c044850f4a0b01422012220425003002 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 222547014 1250 222545764 222545767
    0x30a05100626100308030708060f24160b010602030304051b100f0e040c0e04050a0b092e060f02120309030909041104110406030c03050c04061b02090c0a02060a11 71
    0x71410482e01007055000301c01900040b64980d980d1303980603460f8400c450351400a81740b441444040d240090592040840407182c0d03c0704000040a09402c0c142e1203402040300c810001240160000c0120f0320150703150700011030243c1e560b074a40d03001e0340f20fa004480440311405207030f0283c04200713241182000c04500150070001e10006200c816200309201e6001003040c44294200354105a90ba409408524802c565840e40384100d280c007032109032200070380540c0300a8100391a0314080d85480b240d00f40e00c80c8524109404a0094040d203403031005200f10450303132020185102003500d80c0c00410551216001d9800c43d403800840c0d4803918103e00059031406c030f40b60410881c140305850030b0168550464021208056507043c02400201115035540007840f13601c101190030450300d5054400c0000941050070180480d18214144034501cbc401c40c050007041c8200740d00c4100401e54074919a20381a41e0141520f5810b00b000074112205810100c0ca02006108110024551000e40e008130708415443d4102107 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 222548264 1250 222547014 222547067
    0x40501290f01030e011e060504060302060703050f0903060f0f0702060417180301020304050a0c0b032203020c040c08012603040605032a070b0f06030705010311070602030a051006 78
    0x74100032003440141019190351000b0000c1c0d0f0300388104211380350140c2000100441c12251407003500c2c02d56200f58403d43c0750200400140e181c1108031071581741d052608594034070800d20500207500605000a4040c841c000070800445941c088680c010012191240e14558400314202c6ea581e070200c6004103880c020030803040520030180302404501c080c0440300d403038040f0366101003407c80c3c0044405683c0b980c400d600203414042140401c402502d2041400c5181d860060100e07503104c00e55060040004682c854041d09040c424841c4103003030740e402441440600303520800201403080030300841086075199400e45415640c500007000424001c48080c5042519090b003e948681004050003a59620120101c00f50000c1c4181c0c030490b060840d0030181c03038400c103007401110342100900d0b0313100d080010301c144910baa400242440c22950b007440c0200301d80011aa01e03140d140100c0c20000e08103800802480b694004030341105100b80007040e00409182d58414049032240d02d40c030b680400784129415003 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 222549514 1250 222548264 222548269
    0x1e0f03010932070c02030f07050a0b250c080a23071a09010e1003020705010b0a06120905030405120601090e030f0406030c0c0209090309031204060210020d09020901030b04050129 78
    0x202c0d03a016059040c400703a245800d802081c05c18440741c099136000c1e040300c041408a40b03000c2c40000c01620400c440030382092200140903020080b40690b501d2034050035401c1e1410800a4000003001c1c0c160030017034906401c881c5c07405a581d40c00802c1c10303100054140d152a00b40507000141d64048400025407100d010344402003d06d080da00000d2030b0b9042104801550b0256103d400b80e2412117170050798010f81e108040d04055003140c0140007501c2c070601b60040c0400640b64030a02100070658100b4000403100c196181c460314520456206980020001c80c0802c40b0710303008203000741200c034101014020710108007000341e100d02c950051208100313420b1205020070f600c25444140c80c006a420000c001802c107800061480e2000c40e0f03203000c5940005a08440d50030140120b590407240c0078890b078281800d02001a4540c000d4264814882d5804111150740d050a40c119800040d0040e01011203941c49080107000d0b075000f2030f02515190b081c00c0c0400700c1c06413105024195800c0441c112800d25220104 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 222550764 1250 222549514 222549611
    0x4050603060a0e010602060a0e0d0f0807020f011a03060604060302090408070c030519050c100503070e040b0607030503060a0f210204090204050a0e0d0801030c05061e0f030109 77
    0xe0b400c9882404041203c00c4414100f0703028000d9a0002c04040c41c0c2031050106039001c03581e1080440c1c0060155203030b070301d40060090b80205d02d2410042107542da030f480200e1034004512002e070940c1d82440c48003100340c1c66546084040c448203806490050380c41500340415190284030080d00400200b00140102c3c00200107080c4c1c5030302c2400c42c0071030943d0b01d0301c925150100400600d80c0010000a909003082030401450310022419036140c01000401400a444c07030200a0102d03050010704924940c00d41d946034400720100c07030000c00d0300392035000e1410000c1440e001203030031034010f8600702408a00b098208a4500407141030031074440e040044900c00d030440a6120108a80048c0c9030030341c6070010380d124016548500591b090010382c1c00940c40e40a07203050340140040c020300c0b490000600201d07180000c04419540c050350000d544200d99811800c552500c2e0300030720701c113480c0490519440000030000b10b049811040e0f0611507004120419110f9003e2800c0303500c80082000c0f010035081c5074025 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 222552014 1250 222550764 222550771
    0x91e1e01020f0709050115020105190218030a08130602030c10091a160f0f170912030108070501030506060f03041502090406080f0d03060305060c0304080d061502011407020304050603 80
    0x41a1802e081103400030502c0c1800030b030402190760307031100018005814000c0002c0b104801910003030100c0d0408004100380c4102c002480001940c000940d401464802c25400d1941e480107000c88503100084d0078034800d2030700308002c3d10169401107000001d107644000309460204801e030010b04003200c041c200c0c035801131004010803038042440040c500442d07212101c5480c8200365800301c0c101003d4519000502e42c90041c1e610302d060105001c0b0000301303da444041c038050307410b042c940c04840361aa403014901d450546161520020342c00000462641400300b00070080f260280c07420b00c060b0700c03600204580c500901d50741c80d070511803e0000401080032111403074018003480a00601c0d08002c1800700d81030f105550011032481c0c0c041ea120341c0c03407503c081110b01c110030309902d420400380e4296034415442d6039000c4c06400c602140400406c0034400b02d00104c80075007517800b13400c1040959901c2050881080705007002c0255182c40044c080c242614030006200d060300360f000c0c500d460700f000100059900044e = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 222553264 1250 222552014 222552017
    0x90a0504150204060e0a050303040612050405030d050405030d2304080a09051c0312111603050d0203070305010e091203011701111206120c090a0c030b090c091e1e01 72
    0xc00c0c58103044252032008101030402540c41401c400301a8062012007521b9078011402940100800c0104031347c0302c2d00d0301d944210342d2000400ea81e01c03142071407455409540651000c00d841c03c001d100c10041c0000c010030140c0582c400c140048010380d0f000094551440f004003018003041400640000c1091009011b60083c90502c01d003130341e40f00c1c03011881c0e1079442d01140c46e02c00d210140210a1541081c0f2a05034400150014031200c244800385d0301d103c1c025094400e000b01c070945104820103001d801919400307250ba030011522864100741c024003800b000e11560801c02c00c8000404d10032840490510484020444041e285900c2d010404000d1a14000098419540c07040002c0f86100b0070380080c0783c8000503c2c1c400555041140c1040607400a1144c01c5106a00085040f01c0a0711007074070141d0b00c281c100c4400100c440483d5405d03009441c805405c15032004d1200100b00c14040d03108003410445406681243d86c60101d1010140b1824110503042d80c04081a00c5101100d04600d03030740035120300103 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 222554514 1250 222553264 222553283
    0x240b07110316090519020702030c01030504080f0313060506030c030a0308070203040906030606050a06021501090b13050709090c090602060103023d020d0c0222060b0a110706020606090a0504 83
    0x51003481d03081030a401000c0f51079116414841d034245d21070000340e00c0c031010003011840d2105550010f980c0d074100e00103007418161110001401c0c444441300b5200c1c1c0f05c0e80a0040756a0303150404048a008480c0b802c116400c07840c080c0030890b98200020f640440c49005401414010300e151401d403240750005218008510040001180071082409500015031242d034003c1507e03401c00c0c04111000c2081e401c0141150f103d4030804024090540d44681142c0d00c3c80c40000c0c1e0080d0b40c1d4003203410441001c2c060740c01e50b401c00d428003199a511550400071500794180c20890000b80300b07001c42e20b041d0071780b02c0c01d0016401000144003501c1c102400380100e6400c2e2076140501810724000c440304950780e030055045a40410300f106007040d018000540103007254680080d1a06190780002c0140090748001040c5d4506105161441030842d0300580140260fc0303082030f221034904200810003040d095265a0a0041200c001545400000c00f02e000361002800316405644400d4120f0041c83e0040c0141c80c01c104 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 222555764 1250 222554514 222554533
    0xa0603060324181a060f060307120b12100b010503060f1309020a030311151611010e0709091b080c060d14011403010e1c1b0c0603240b071103 62
    0x80d19070200c80030600c40c0d445040265034045425142c0000100a180107110706c045080c0140d442804a0f5070055180c140115100d15090b0000001c140d9038850b5074001c2807104121815810026540b43d201c50b40d410244123b000c01e4004540c540810ba5007940c100a18a06101651070040300c1c81e045551035120000c0d82001c90380004c1c048502646c000e80c04900c40c101c050081c0f85050110310500d8480d12030b1840242828000c030191140c07911814810400c08090181c25840290011020030742c9190480700d43c10340366000c1200a000c00d04c421648800c0c580808001d4a6941d94008101e401341c40103030098030784c0d8100303020090340040110f0a51554900c000b074940704615443d58080c01140c000b59500380f003104d040c5400c5800010070078440340c0c80b0f50002501d405001c100919040c01e0780c44d12074001080669902e2111003820b0005041407030224010600340c3e8141d00c06281c8c03d9060541124441100740221031171200341c0074107108148204015004560302c59822030610002408079140c200 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 222557014 1250 222555764 222555791
    0x30a15050a120f06050f1b030403020a020f010e0901030507080d02160915090905030702010813020d030f051e0910050406050a140409050702010518070608040f08040506070804050a0603060324 84
    0x105c04861084000765000f0a01041142400c1d004a1400451070483d20750304040c0c0300a5502c0c07480c080000c0c80740c015008280340301e920408810b10381c0040604526101d50b100e241c02c0b504c40b002c50080300624403840100180303151001954010010030161001c009600306902640a4410501007144607800700000240b80c5407648030b07071200d8a000308040c68a0300381d40e2000601c1c1c0b40018010b52401e4038100006005079603031983c0d040850354103003411040e10f0700d28070003526640a110748482c420b010b0301200101c1c070110400140503641080354401010a41424155201c0c052409000c1c0058001d01280b42c103580107002c40f458909044101c0c0f42066030354580300040d208101c0b842d00041c0d44039014001968801064800302a81c1030028140c0c040c2818001018942c0c028000b034003100003100510180407800044402600001d4441d0b55612128101640160b01c035205050107a01e03e4440016480d210b4440c0106482e4000c01c07504652820f40c45a5203080c3c0300d50428500b241d900c00c00000e000 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 222558264 1250 222557014 222557021
    0x81503011b0809010c0c21180905041103071503050402040b0616211d060706090507060801060215010b07051c031505040207030c080d060e0a02030a15050a120f06 71
    0x495074502ca0b00e40b40004569080d04c1e6510310703d00034080e10840c0c0100040d41210110003007a0384005480d4a0104c0f05021280411100801d807070a80c0340c090003281407001900414403c80c001e1803450b051403a220140765031940f05100c0c103420709188462680d50b40c3c1c0300e900a1a04140001e1000c1390300c1080c1000140203600032a178081a51503082d101804200141112001071001c2d80541480051030b4980500440031362400b40302100104ad0a10013075503543c17015603941075040b94040150005519109507a02030f40d000d10070126040c2800082e904d0710004030b40d0303591040c91700352160a034a044894000e82d080b10108403041d000701821140c00f203100248510034805180d038040303088407001d000001c007200707581c0149004500401c008004650031181200201c0c0d0f108415960312803c0c441020010a02078002e0740344c0000c010b080c4014083c0e039030041d41c003900b1450320810a441c041c1c42c030340842440602c6416008502000c0c00c1105403449400710b24480d00a0180030034400301035941c413046 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 222559514 1250 222558264 222558311
    0x90612030915031812090d1a0106020321061005070201020a050d020d031d0307020d020a03060203040303052226130902070c060c030e04020a11060708090105090d08150301 75
    0x100b101008214001454410050304030021501a01d5207811190110220b4441c20720064081c2e8011070f00030080011152018017240040c911419042d611144c009440790b0180500907411149401c4c02100703186400321843c007490004220f4048007031000001e40d0941c224550070f82c1503010361440040410400e01058020f00b0296001d8062a044103c02908559420081521104000d004c02c0d0403000c00000302c0d02d11a40454102000044038400240004070f5034000521080c00841807100300b6405400040c0a0f020150b178596448c00c000c401b10200014500014000c00b6105004c40704007102d9000420035018142015803918081e075400c209090742951203900d2056001620806000304003800001824862601030300120b4151002004004010652841150f00186010002d40210030303c050b604240e1081d90702514040300040c10203c0119130307481455081100041d203290b00031a000250905a444140c555100c2d4003c600c00403401400564156507180c40c0181d0000c50031070309452 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 222560764 1250 222559514 222559549
    0x405011401060203072d05150403090b07031d0103020d0e03040f080708100e0703020405041103010b0301020918041a0c04030c0605030c07031b060f0c020105090307020906120309 78
    0x1a00460030080c8285100168400310840d0014890800090b58800341c458600c0c140c81d00c00c001e103590407012503415a90203040244503224407444480b4404e00350203110722650081c0c84140d00695140b814540c10710030004024001840ca18040380480c12021200b000d986040c0f6005091400008011044a510442d60b040c0c0d80e001047c20041c68030800f0030704000e0110500a415043d02c1c019420703a84200e02882112902d886140c1c0801e5040100b29410040d030300108280018245810002c4181e26418182d034025401d00d03d1081645c1014002c4801990000d011484800c0301154560803099000e002190800b605400a048543c06d6071030f494054001c1e40203d03030303807103103940380058002c40347e540100c05004080c0100000c0c0c04809007501c80e2240c041c2400d180f0040001c0701c040407034043c403400400c03103407420b1215650a1241c3d444000c084069800821003030b01c80070040d41d80ea000780c04000b540900b8080000d801070800303400f02c00e0361040101c1140c1c1081005400922600a10040c480 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 222562014 1250 222560764 222560771
    0xc0c150204090f06050907080711030a090602010c140306041d0f060601020d0e01050418200406030e07051e0607060212060a060c0c03110307050406090f0510290f03040501 75
    0x100d10103183c030a107200b2000802d801c000320303403501c00400d901d00300003056441030208040014181c0c41c011403a11559100d844140da1703481c0d2a100e0080c06070b0840d805841c1c010340c07802c1e0340c2507100c50103410441900d12960903103500f986d443d107003000081c003842385480c00490101008103020f08020441140444021005040c66113048000246401c4032510f0750010048031003002501030740c018044905440c0c1c5a04d50001141d02401c01e403020300516410780c480e0401040011001c2c80500c00640251441950b00f80220b652944100e9510102405000c0c1d00c40c2c1840041600d0841c1c0110304200d0078005002c060a100307003034440b04102d0304140b6422540e0201c8004003e1585001c05408000c4d0000e8242182c031322280e40c8466007103034010b0100401154040041c503c0c0e81d91708001d480b0082c0001041440b5194a90080101900d084241e080c899400c03d030125a0501200d00824156207008900d2201000d40c90907c090820701806401c0034800100000c1c4522890079000f507109034020380012 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 222563264 1250 222562014 222562019
    0x7020c19031707111e04090201051902150a0605150a031407030603060c111c020c0a0f0e0a0902130209010918050f06060f04050904110402070b01060e010e0d060c0c150204 75
    0x8400f0b00140c80001403084906071105c1e2001c1d10340c0d54408450a100f42c030009806030145c401a10305110f05446007010006003d1009201d0350b000134805001403107100c04110301e40782c0342d40403425a0380e28001c0c01d60181c602076814216071503171b1004d80451100c616000c554120702088104036944191400d2002070303100da5090041c405c50b030007100103011085c50100e103010908403942d80c0310b01348025290388212400c0b088104031803082100e0381e03c52900a0650004a80e10200000b034220248101c004000b01c0100007085801d07248500d1601d00e4001c0c1003541107014003200100298014a8440d040c0b01c401303280410000441c0f4450011041b51031400102400d02e03041c40181141c005100b14802e603010003c6c1c1c1c00607a0204150b400f22401a1104000307500c1da8034010414000c283d001a81291000c100e96050000362807486040364400c0d1101d240100030780004442d4031003c4500c0d0b9801c4003000344603800180199000c2c20400742c00c0d1500403100c05240d43e850444003111400480c8c0d043d00403405 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 222564514 1250 222563264 222563273
    0x6060f0a0507121403010e0a0e030d2c0304120c090c0e09100b0904020a050408030a02010c090b03060603010b0322050c040609020403110123070605010f0501050307020c19031707 78
    0x903c50500342d64184600c49070401403d4004a210501401700103001c2000481d02105568102c03600400b1658103807525600700c0b1076100000c0c50a4000001106511015100307206280d602c40d10034003d05401961030b090611428070380c404805001100c0501c0c060b1030000381e44419200e2521041340c9030b41d422a10710641c00800c408a0006040002c00c0c492102c420844003c0c00d40890780c12900c20740d40541c41e00500d03c001d5445005950090110740000030340d20300e086a065014040c292005c0d100c5000050300c03103240b40d20b203000448000f034104c1d03010401400740c0d1000ca40035641c0034020206084160480c074040d800f14403030755101264554481c0c80c0c940c1c940d140a001d02005085402d40840c1003e245440b200e100e80d8810360326905208070315001e803828503a420300103c142c41003210220b550701e2152034024002e0101f4841c4070803010000c02d010542d0345c460000c90380110030b158000c103031070400341040002881070f1446650b550250320000000180400421094001d24940c40d240ca13940542003 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 222565764 1250 222564514 222564533
    0x280210050315010f02030d11070501060e0f04060f0e1608010612030e06181503071d032a1003050f0109090807080f1204080901020c01030513080306060f0a0507 70
    0x22018140032040c800c11034110680041e45000d07150900c0c01440c0c0c00400300741a402d40c440c480c2048a0749050441441d2041941c40c01002039520402c000c214260340c07203501000460041c0e8040642c0041180458081025500403d180581101c400580220803200c030910349008940100a00ca0404804000300b0030281300740e6008080e4889400c1f545c42c03107540c0c0140041099904d251103100c000c12111403000281c0c0147d20b5075400644003210550076a2031580300780c1c20899840c4001408400e0680071500c8a4100d059208005002000308540c14120ba07a9072002c0b00e0844000d454000456003d1641c0f48808094a0401510700082605060440e20310101d0141c020b0030380c0e1420002c4d0207000a4040d4101c2d040b881d0007050864603916161042c1445201e0709829540c40c1d00c4000900c01401202d500030210100c1c240c00b1a69004407080044d011f848040307404541900410052201051080f17000707550003100206620304e000c915050000c020b81250703018000150000c11240c00300201c0c0d00 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 222567014 1250 222565764 222565789
    0x50703060509070507150b0405131203020a0504140d020907051b03090d0b18010f0b091b040b0c1e060702061e0a0b0319060515120309090402032802 65
    0x141d10b0001c6140889000e00607110b1000c00820203124003010312a46542c0d5802046509401881400a0f040140346800f108841c0d90058a1034170b0702c0c000c1c4030051402882254940c1e41c4179103580f42031030b2030044540740208207400595007100010003440e0050b9150042c40d4480c0c8032585034291100511362038007000300c4642d44445d4841d4410842c00720b40c1c0d80c41c508004101548207404600e00d07030315040d40c0c1c40f4000c4900401090740d0300304a000d01c0f82400940107000381260a0360801c4450351010300d02c0c0d00e45080d0860305506008100070604c2600c092100400307032400580205c0b81828040c0f92402a800320815680e4040d4220708140f09034a1b034144031090300300c4054000049284d0590410544d44400909240c2140e56a09a8180f80740c8003030051002c841d50b0100ca03d40c55401608010010380030440f9131181007a42d81c032240e0b405107061140d091441260320020760600441405000b81c0640140050340c0c10711441440ca8040c0c0220181031381a8044018620508510751040c80300940828 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 222568264 1250 222567014 222567019
    0x10906150221070c0f080102070627020907030605060301030b07090b0a0e1e0d050c010306080a0c0306090f0507030302072c0f10080f061905040b1504140a0507030605 73
    0x40c441124914803640301c000c4142c0c807070ba1a90388024514151011154503449203c402202110010341c1c1c01301940640850782c01210305001224803003000d100360003c034090395140c0400aa846002506088200982c04107031810f00051030b5882d07500145050300240e00441c0c1c1c1204840230031408a074052501001803007105055824503c00c890003070215401010000d00030041111088030810300213103000c00900c805444002c4401135820b00036102c1040030645d602203410700000066156000a8844226410044240c40703681540e0740c40001d400c090000341c030104941c00c400e40200b20f0502c0f00c600210300c65002010114501024a20143c8640440040360243c2c0ca51904c0c0c3e02e9515441d5590010202d84182c009987d002031080c407445580e0421501031003414540752170b070100010998081c5030041450038810301000030a50941d00d003103c004050184075004510701c1074082c030880141003c02407010803031500760407204411000860f008840c2d40d455070306002400b9014420a0701400c0207 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 222569514 1250 222568264 222568273
    0x6060201090c03170d0e0606030111031605090d05010c180b070b0109201603081602030a050c150403090509060d08030705090d1406040b0702010614010f0c0501050109061502 76
    0x440d100d203501c00c1403d110140900f06058494503042455104452030285014000c201003255100c0d42c2e66240811160680658601041710007440d444000780d0380701e81c0b100704050300b41800c43e040403107082d00090745450704801017025071400a0780a00800c0b201614640e692621041c00b0455102258007a52012110304010860035000c240c0510110341500c03000e0401055601d03035441c0603c0d100c9207031040550b503000c020943d400400441c84008500502a90b503410280d1240040100f0000c114106070015920400c8001d03691070103a40a802d480c40043c0948020682c00c07000951f801d4030858080b40002c080d05020321180c40d01c0d02c2c03101e400000555802c0440300c1030703039074003200c07840050b0843d0140080880c0c0b1755403a5950030460500c55601600c0c0c00e0400828171112661010140c03000c0702c035115004000b900b102d2051003848202e980140d0851210b4002034010f4418107507048200c02049080c032000004601e003409402e0083c00c030403c0c001203a40c54a20080c6000d011a060071045410 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 222570764 1250 222569514 222569531
    0x30403021504032006060f19051002030d020a0f030c0309020102071a09030102070807030e0315041203090b09070911090d0605150d03440705040f0b0403020406060201 73
    0x900058079070034200011071001c1e660b169420159002445208030340310400003002015109007020440d40d00074101a600220b0390a800c20800121b48010707405418020301c00721003003201c1c1c5849000482d84480500540b8502603003183c80708243e901100710030f40421042e43c6800420340d03244c402c0c21981c038014502006a04121750000392602603a00c22103c00051629031801c400c070051b01116a1604010004c564419003071500c049240c204002c107802141d82a0300307001da2824046000415810b480040407250340c0c817030b903600030041c1c0c0740000c1c001015500d1809900080d42c00c290140942c00020043c0440d51801c40101d081c2c502103000581480c1080c000c0c9003454445540c6081070036449500415339070740e0072007810300022007885001d62002294445609250304880010301040c00d140005a40002b10312848c0740b8100459522811241d440b0301410440705041c052642105c110304e00305117855a994054030b581d400c00e800c003001a400001e4100210b141c203200381c00040140b030000303200403031 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 222572014 1250 222570764 222570767
    0x1020304030e181f0b0d051504050105090f0919030e130e030406030504140303010b031f0e04020d06141f090b150f0d060608010302040c0c1713050d0b0912030403 71
    0x40c01030f09102c0113100c50320701046003210b403103104409007a2000181d44c96200c5160003901070319042d070710340d000e00440c1c2e0052a26070034a03005141c141c44000d000e0024540310130701002c41d440c0d0000c00307210060007924000c0c600044031a0080200328000e60b12108100c0408007007056103807a264071140010320304000c0c0e40c42c801c80442a6401c031038481c10700180741c0d5a242000c03602c4920040b490040da000010000c140d40c690318025602502504002081c400800001800040d2217170007031070540300c40003001400500c1c0c010702020840d841003038007040860350b00b180b010401405980032a003035011125000705100d43e40501c20014000c0c3e21040c006500460041421074660400c1d101c941d2200086040c0080091411540c0d01d42e5000420821644c5c1c41c2c5004080c15000c0c0012803285050003a003684080c851a0b2a004094000110080105c42c02c0813400030769200070340782a91555810300008a50b9600d9020401050042c0c0700300c2903c1c50200c00c200d0611440380e0206209034018002d000109 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 222573264 1250 222572014 222572059
    0x606010c0c050f01020304092a050f1e09041a01110601050a03030e0117070806040b0405040c05010513030203070305031315080a150e041101301116030201020304030e 73
    0x90b1030548500c00810b8036000100d040d48181c0d040509403034100404124150104030700342c8500811040c3c9503514003038030301b004c64141c89540c040781003000040c0004080c28200c07685546215000c0c03002d0700c0c50a030400300800d06584c2c658280500001034031000c41200e58101064045a21070040944900e6061000040704040d0900024041200503500f0101d1a4056030103601c0c620b142d18548003541c038007810300030482d035000c4035424020317414101e0440c1541024010540a1640300603061007060030400111802e400001c494003a481c968000000503882c14880e18000d18001c8020715655044044507854106a40d8001804000520680300c1d01e0f50f0b10690310741e04510301c4000130078900480c14140900001c0380d00301c003400d0a5040e0a001c00c11091002c0071645401c03c1c4c9480000c00c071a80c80c00c0c101080003080e504103600305514842818041a405074041c284505100f50801048031054484010400c4049015039400814031060641002e00004089400c460002c4005030050354080c10 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 222574514 1250 222573264 222573269
    0x52b0c0306240201090b09060105030c0109140904060209040603050312010b040303080a09020a0e0c0c010e01020301181509020a050c0114150108040203070b1606060b0301080a0b0a06030f060605030606010c0c 91
    0xb500c42ca203010300d154401e41000500c181c1200c0c2082c0c03603041501a040c1c540c0c00a1142c240300384a00c0f030000d41a5406084420101c90b00ca520740611460a41c00703000310b80d203000b00304035460f80c0e081103811065135503407040d00301841c0540011500d80c881115a07985668068101c5100341c01e0a02c42000043c0e800041641e02c002040400f003008a154808107100c2d00340d94010208200c00700b0304000051847c032016050040141c0024055111340203d018201d00c420b0140520388100e103900c0d46107a00b140e41101c1d4443c0180d40300400480da54600510880e0004200c2c030b80050b40025009003011400d0148a8416810503803110041c241281030500c01c810b007200c0d40303050080b5100084d080d5503041c49010028040b852448c0d41c0d403c0035000c080e40400c4600e2085442d41d1400b03c0204001030010180c80c16a000a0000c0c840680140c0341e40c01020802401c0490464030b807440400090440201501920b1094001045590509082606000006104a041080c4098614081222851200d08 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 222575764 1250 222574514 222574559
    0x3022208120d0209060708070203011a0a2c01060c0201111501230325140a09091713090f05040201140309010b0603040b0f0c04060203070b07052b0c0306 67
    0x50302c14a001e42c0c60040d0280155940e031100b004204075040c0300000c0d0041c00c2591088000300400640320700c6d0384010304154010700e50000300f028001d001500f01d17110010800d482281c080c0d100c030b2580c00b44e09100f603802600305000240d4900c0c03288003156000021900072002d24000b0b4030800011102e50030140805104044410380003000124101c0c4952001081801e806420b50700d651146171090400e44e21841c03462102140381943c0080c0004003841881c01e8a04002d000b807100a03c1c280c45e03503026048500080d607403540009014600f00210200902d20b40c045949004645071912001d03504540b4840c183c160f4840c144010400180e81c04041a2404500c181507261240c940b812a54010020807414a40000707000081c08248030004011510440004010800c5640c94107035114041c020341c4141c401691003401080c0000b59548005035115020345001401c0a03402e00085440300019141c0000c04003128680c0601700c0c205010f8062002158181444860302e000080b0080060031141101e = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 222577014 1250 222575764 222575767
    0x13030507060f020d0302031e1005010e030307030c230a0f02090106050313020d03180314060c0c0d0f1812050106140105040512070f1805010503160302040b0315070302220812 76
    0x400c03000000d030001222445000c8d00050b079140014442044100d00d0143c40d010400c7d18900348a585400400c482c03281d58140e5440d540c4590f107544020138131442c46042d8003501c0848010303a1040030200028008130340030b4000a0003034203190040c081810810380000702044010810851000f80c40840c07244d909505840060100740181400c4490807040100441ca035110a4800410f00c08c0020420154040b100151500e40e220a1000034841c0301e601e110300c40030341004940030319aa000d4402e500040c0d245080501c0034031281600e11240040300d4001449a80d040810f590901801b403103044c001d410300c0c2c0d19040710001c2040c000380035802544070380e40c840c3e0507070840a14900f10510050004102601c081d8007015140c2d50300c4286216025440c0585910304000052075181c0021404e1501158004d103000007030558084c44003810003001c080f501841034582503056511000b20880c803815040c0d80061b140d01400e4200001003204240d40c003100040f0b510140f24802c0007190064000c0684038166 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 222578264 1250 222577014 222577021
    0x6030f08090a03080f0a021510210503030f09010b0108070e060c100e1f0228020f0609030a090e0103053a0201020910110c011d03010213030507060f020d030203 70
    0x5280d00b00301c2e410040c1071182c086098290744441e9400303010000c1c0d60341c09036208000d14058001a4160840308080385190380c1d40c040040e000000e141d070000500c01d40b00d0428070032164640a00c0c5074020b82c0c1d80540c2d0301e692010400c02007002e01ca0321408020074a020202070034003840c01490f05017043c1c0b601380b00c0e950004040c1c0440d00d040212903a10760381d5003018010703600f5640c90f00340c980c99008045a082c110f99508401c02c03810610131107180150070884242c1003201d1018402c5c0901000420350198480e0f035034000c0c5031800030086640301e100100c0c01140e5510031114024801c0d03016074440081d0141040051002a4012032503102d90030f8401d030705005503090f58800060a00d01c0142101800c402f880d4814802507045d0000c00f000703102510b19590040700a982180c0c2c4000c10000c000440e003000b030510041d5880b47c1482585226801d110090002d172920010b0700726440421f40710111101070b4408c10402106000502c000c140b0360030402580039107003502940303810b01c40045900301035000000 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 222579514 1250 222578264 222578269
    0xd0e1c050d140c07120204050903040f06030908091c0c060c080d0b15031003030e1002030702010c020f04060b030a0b04020f030412091a0903100c0f200102071a0a06030f0809 76
    0xc3d142d4000d8824119040c195440c407000706060442d903c164082c07402c1800103131901c4000011103088407801c40da94402d05242110807001425860011a0102e4041003001100e540304079040c0c0152101e407000e01030881c030744d24294203200c545902030414440c8035407440b00810700000030f880c80e9500007403000c90508402000203607003080440b00b4446144c0007000f40103e003090b2901803420303280b00c0d4a0369503481000e042006000c064141141d401030340104011801548180c41921400d8400340000c0e441070411070003e025200690001402d9070004010854400d5040c090030304580303020f54007140303020743c115047c90080c800100040d2810410209114183e4455600a002004c042e00034207025904026251000c0e44030741070700d51283c441c2d0328a1100c80c1c0010b01c103102901d919900c800d188180c0c2d1703042c151080c076141a501300400000c0c82c981d12003080c0a00042ca02030740704884074400c101c640e0614a414420241c0900b42007031428100740700044039000d07400c80c925004441d40b80c030341d03d44800 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 222580764 1250 222579514 222579517
    0xd050c0708030406050c0106061707030906060f06030c02060a050402090c07110301052e08030d0c0201020d1406270601030e0313060201051e0c03060603040c080d0e1c050d14 76
    0x8041c1c10700c000140003480070360010180c140d0360110002800610703a614000c807542c0c1c1080c80c1e0a000c451703845000c110454007a40c403034091184941c9011911aa86400178070b040d04c455849107000c20384405150507116414818654001080700e420803a500301600400c401c3c02008214020301c600004062051100710880340d103030404024024031040c513101c031140e21204429032004c003021105034201c00030301158201560541d00000001d600b42400c20041c0c4010346454802c180565508104039010070813079018012140c6180d0501c1402c5041010034004481c0d080c8102d030901817a007c402340d4011301d080180a400c81024600480d100c100f56100600710311400d21105070743c2310042000200c141c1c064105034461140e5840c90703a00030706100c501c40d040e803d040760f6400c1380d0b410030000600365181c80300103590401d0180305281c01e4140c5a0b0340642c0b500d98004484404900c84549a1086140c0240d8158800c1e411000907004880039035035807607a600990660348180b105001d08141d40d0201d020 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 222582014 1250 222580764 222580769
    0x160332191b0b090a05040203250e060d0c1b0309060309060f0e0607020c040902090612030906040b04050f0a030201021903120f02040305010509010c09031202120c010c09050a05030d050c07 82
    0x100007645503585441600140d40007203881e5000e000d074039a000039240381520031f5a10944c50000c43e01c464a0303c000c40c0181e40741e0ba4445840c14001050b842c8106070300e46201400c22492242d90005001200d814007404a600702c3c944440c2c0d420036503182c000001d13070180700101203030464200491803190614012001e8a18031880c4000c040c03030a4030843c1c1e090700003d0540d004070a20340035510b184400f10240421b4a000300b03000ba41144400f0089102070801c280840411081c00d82520700b49070310000024030340d60040c1c0c000d0b181403c012900340f0051600380c00d5800d035004100d44c1d809440303156500103074660802c00203900401d80c40e000b07034000b4540030718203844841c40829010400d100c0d0f002c282d40000c0d0864001981c0790b61800c0300017003541005204503122440141c4600304020701e1680c69803500c2c0ca00c130b90350700214000e032540039410a601c0b402500c13807884c1e018004503030202041c00080021000740d2101c2d200f20f4017800308016588003c5032800242c11103140c82a651810305010601e403038000d5 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 222583264 1250 222582014 222582053
    0x30b07020316081e040b220e0c07110109030f111f020d09091428051005030d030c0509012a0303140a090b06040b010216033219 56
    0x2500381030b007080f0b400710007050800c040000c005a0301c4600c00c0810aa805140174038694901d041048640140b03a0005d000d2a02500040c0199125140c11030281c03503890640b1900d48004000c071312142001000c0760044072816080ca444002545981c0316050003030003240c40a025200304810800f10f503103c098403c0c440c49258085246038240e18200255070705401c0c644100025560f000103da14186402100b08600c0503010209440c1ca0f038040d08240d098070300a0780d61040c140304050200804041c040c0c544104500a0490b01c8180b4150600d070038980003001e602c04061800745c600c540940c206060b00d00e510001e2034200c06206c06640700d40040c01004441c403443e40c041036100401c06030705800108500c00441f0f00381546031034020484098030804c00004001c0c4040d007000880e40e0900e079104001d0140d052040799018a590000444141d606800503202d81040303242880e81024540100146255250307184816004540103541d155440c51580a00307581613800030070309000d04450b54156803541c0 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 222584514 1250 222583264 222583297
    0x120708070318080307020708030403050309010f121505040b2e17010e09010b01050a05030105010e0a0302090a09030e1212030c040b040602010c031104050f090a0f0603111315030b070203 81
    0x303505003002c0c1c44e0001c644e030200520410402260289003c0b00740c90490340d0150055003000e80c101d005542e14074050841d0000c01810404500190f144e0b80100d03050202d603032184da0109400c00701800281d51264aa075400f4042001c1211a000c8812018640c440441c514a2503074403070040301203030004030841104001405001c0045582a02968410b002d01c0c0e8cc480204981003010b40190340ca4021155403502203101407004000d15400340303002007840b074001071600490a4581e400a520020161403100c1207a9958030490201038001009055130201100d4408c1140c10081415a88041c0c1b0280ea010b03664010000c540454020020b80d4058040641d40c81d071950b0300d07500000d000b00480c0e9040c40001703041c0700310178000010301c6044070191030000d00003030110b6000c80c01307112140401034000307210141e5428030660024528410980598424040340990746024802c0003800009240640001882d101c0c00101d60f04c8801c5036030040ba40c0c0804100391903986e0800c00d82c214010344503102d080000 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 222585764 1250 222584514 222584561
    0x5120a0b011b050f160f030b1b0a021501090e19020d0602120702070b030403140304030216060504091103010608070f020a02150a1d060a05090f1503010e0c1207080703 73
    0x404140050303082031a000b140d1080190615070a000081841601440300d86e411041c0045a1030003404e5502c401b24210500000e0054590b44030b4660001520742c005820a0380b8400f400214801c005004040180b000e2200900c1c0c501e4464032422250740c400c03a0321b5035407454a0119202e00d00c003040d5254008904544400000070380b05803050307044a2140041c02000000300307610800200741c0e4081c54040e40c642812208080203244980c8c8040e00c19425803003200c91a43c400390740b003652107001d4403056950a80b5079140c100880d003650100cbc46920081c044c184014000c490380b1a0b22541d20400914010b82c0e42c40e4042d00c00d03801d0815540c4041d400c00c06030744900b0100d1070b030b103c000d000020560741c42e5002d403040285484c1450b807066005981c8503c1c10020f11075060b200e00044c0008240003001814441140b500107a2b084205c05080da5007403e01000400940c640280c015a1080d40d4207240c07480e02103031001441c2090401040401849150030129032004d100760300a1003860144903c6d90503000 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 222587014 1250 222585764 222585773
    0x20a0c0b01090522031218060e031902010207050307020d2a03140d0c110310050a050403020d02070602030403032d030e1b0102030304021002031309090203010b0105120a0b011b 77
    0x1070841d460041c248006181011380b4090b483d285100c0c83c0c160740d030740201440b140410005050244180c80704070b21301c46200303000700e120b07807190701440100f5800a541e581103c501c14025180c1510008043d640305001c1c420200ba008011181c130180e044825000880b641d02c5c01010381c40c510001140c14204a41c0700e040c01301c0480c1d01d0841540c1c0540d6540500000540c170059032640603030390b0000046c01c41606880012a86102c80e000c1140040645256407000c001c10f00c00c41d0021241541c20586800912052640602c040c0058100030301c054a031507400d01c14041e5407403065200060421a0710f0030a5540b1703100440031204400c460504d2007a000c00d020b4401400340001041640103130080e040740429074031031218049070040f8103800bd5401d581d102d808100e01e0000f0420b0503403c0d400304015403010b010340011b0030700160200f20000200e01e0840d0060608560400d4a82414000704001400310b03898181a4681e00084445001c52160b500000407141d80b50030303074640300480b0801c103020000c12 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 222588264 1250 222587014 222587021
    0x9010212041e1a0d050c0c010c0e09060102010203040816060207020a06030b09060609031f1d0f07080d080a0f14011404140127060527150a09020a0c0b0109 68
    0x48850790a8098003e407603100c081600d0b40418040403c41e081048036000100c2c2c19001164803050f184041c6081c0b41e12035900c1c5080d40c0440b452100054801003503032002d89452000384e50414020300c000c60441c64207039a511081c1c070034201c20220201520106034208400d54040307502e402c0e4058120104280d443c880a80a80002030a10748500e014100148150402c0c5c0251000781a006004204074950004400b40d88101103070001c10042c5c55034071400440c0c1c01c40300c82454001d07a0324000c1c81100918144cd900700b03e115001100903400c0340ce1080c1900d540000d040d40c00030000c81c80059030782c0c1c0d550281c100070702c1c1f0f4118a03a08000400d00014010120054407540300700103480030302c481088940390414601d002d004144030480700c2d185103404080820446011072591150018200307031141c1c00202810159050741c0002c10301e040c0004141c203900c03800d046d0001c001c4030300f5108400110b0005400d0352114003408000d140d000c1f4071050a0b0f4814030ba5080f00c0c54100a1101c01544c4070030001c00034 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 222589514 1250 222588264 222588299
    0x71e051e0d030b090115090906080c010f020109031e23030601030c0216030b04080c03180f030c0307270204080d031b0c0204051504020d0510080d0203030406020901021204 75
    0x103800388052030700030603000e40107400f4540001050058981c0c02c040a6002c0e071400034440b00c0810001d8034002c10300c0c000d030f84503441c0682040f41c02401d00c0301c1140b0004001c044034600c04421a4103007012240000d4002c0180c507440208502c4a01041c402000304a80204800c1842503054010110910300c00d5803500003140181300a0743d06101c8200b551109076683e00f050010034164a428100800100780f100384a0fa0f0054131410400d0f24080311040c40c02d24582109044950340601500d440e542454904402c100c4408160094180f43c49004000798036031070140b01da000301c200e41c221001502c2e1080100b030752000b0300790705d0219211925000a41d540f00741d61031503000440e240905400c1d905004006050a90b902656400014103059003400301904015003024860b84a66802c00119074803030010b130079000a00b40300042c1c40d16001c00134000041180d40103403401e80044101c9045568080122079115410103c05682c450700c10004034940b990340d2440901c00b110105000c2041040c2d1104540c9 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 222590764 1250 222589514 222589573
    0x30318030f02070b040e0f06180403020105011d19051518041208010b040308071a0f09010506010809031605120c0f0706051305240c030a02060a11071e05 67
    0xb241e10780c501301107580b085009170078039800c017140002d008a03034400d00180d2001d009040550010700030030a503440600c05440480150751039800520900000c04040c110480da0f13560540242d01b0245c614141c11004030717003484c2c0d805840324002070550a00c001d030002c1c3c051010b00089000041840207260038042641c049405480c0000300710410f41c450580136040e00d03050800c0c00d1406156940304500c0e40d00a070300444070380d14003000340085081d04803031041c0b003030807100212006803400205050031200b0040205040c80340751000d210380d242001045d87c928020a80b484d82030540903050076450708039004061003504400203021440d000010400a205400d44d10854032129100d40080d1000d000c0c0021807051020880320070041403901c1d46072103c0045210a4981c1c1c20128400005456031281481201c01d0b03000252501402c1d0b0304015203540480000410030080b00c0b160400d50b000d210703002015006282009018805150036400c9080f0035901c04116124010140d210910380100c4210245 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 222592014 1250 222590764 222590773
    0x4020a110f0a020405090105060f0d05070801140114010c03080a0f090f030e03070e151e0901090b120312010909050316030e010906021504060c0201090c170c01090b0a0c030318030f02 80
    0x1b403481d40c0500489000c0c5c40e00030509204002c4103001d201203840c080109880f58400c0010000d0b201030f00b8400c0b0050407282d21007511141d81099900100e10300c3e414140341c10040c8902c0180c002c6640408403d411005000340030401c0f41d540b601d00d4010700200e904c0505000c000301e85d000200b5802c034110348070100e826016912500c1d5603030050602503204481d00801213644542d040c660746030101e801c010703030803151101c0c02c0b20002100114138018003d03000114101e1fa109094003861400a101d5030321400d40c040198501a00719501c000d050f1018450040d0080d12010000b040040500980d030070700f8000320321507220400380c0c2030080c68180d090b030226000ca800a2404280c9502c00b00f801c1054451126500900c3d4603659100f5008092950621045550b00e0f00410f00140186501e4401010003200d00340e20640000f100500b444509503005050020340d10081020701181d134151154064a42010903001c100c0b400c094010f0202280b1300c9a81c100e00c100110b04258104001002c1d40c0410390807107 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 222593264 1250 222592014 222592021
    0xa150905011d190b0409120801081204050d17040e040303050a110304081b0111040605120c0304150f060308031602010615091a0d0204030503030a0b030a080904020a110f0a020405 78
    0x902c14400c00341d80c01d400c0d00c00741c0d03103a2001482c9607400c01d400c2c08034003070000240071125446070220000184240000110000d00400c41d070359042103038402456079002d04518003490301c00011540c0340340c10401001d5800c2000644a215170801c1590010507008000303000034a81441d0080c01400700320b038070726034444c54600c801155003900c0c41070740e201d80d521510301ca00d803030000d41140004c00791904101c0010740d207030081855014002d41c040c0c070040c01c13280c481b2038031028200345001c90300b078008042d41801042442008003040307110340601c06203400c1e1080003030040d41076024240500340e070f030300b010344a800c0000500c4160300078041e0080350154654020040c2507224052800d04808201582c00000c003400303030901888402c0030103204440b086011f090f141280f0071111130306a811a50040c1c0d09504080b01b0071411107a280254600110202c01500e0308a10603518140c450080581c19070280d540419041d02d0a4065060340200e4002c000840d984003019541d01e656a6040003030483c003a07420400031 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 222594514 1250 222593264 222593309
    0x5070b03180a0305091e030f1e1603020607060209030105130b2412070302030a03021e0d0f03020a020a02030a0b0603010b0105070506060616061a100f08010902030a15090501 76
    0x400480b254580c0d1141e10f050303610340030072449411a2042a1011285094400d1240c0e4104060100d07040c104019200a5650410007001c0341030072800706000382c0040c00d4003020428000c0e0714005495046030315548458260420000034054071800c0e43d015880c0c01d00f40140c90380d06220301126148107611894040d61482054503030817958100088142c0701c0100c000100f03240c0b42c1014071020400b0400c807000b0035602c1c1c002034039280c0d280b1020f0b40560004090b200742d029002011032078450104004106403400454020100d0038052500d00030180d01060b514452403091183c0503100c0d07001011245404014100100c86080c00d4031814420342c0392010f020030704c1d409501521450f607080800b419495660400788801644843e240d060810041803075640010114800e000c4244110080062060b2400d800d01407c05801c4102c40c0038404101a2200411390024800c0e05441c9845000b41e16070b1654035000b80604010880c0103080701d81c140000c82d20310382550010f4101d503903002100300c204008280d03 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 222595764 1250 222594514 222594523
    0x7030b07050c0a02011b0602030c0919080307030c03030e1c0809010624140706020306010906030b06030a150f090b0a050103110307030507050f0703120e011503110d05070b0318 77
    0xc0b15001034001d82a0400990b01400c40614044800d25821501c0d0215541d502e040382d0040b144038040c000c0c0401d400d01319040031200d0110494420300705030702160900108941d680501c2d000101003011405482c4101446600004440c03000307034040300c90348045865143d142e802410a800001240000000c030180b405001c0c6c1400c485404070b480b130352681180b054054402e03c0d900309505100300a804004c0c2511058020086c42c1d000d0840140c49007007440c0014002202580b1442c00c05003404482001e581d02c000859030007102c07130300300024403800c80300c031400908a1582c80b009141e02d40701000640c00500c1d40150417684002c40b940c0c17417200d407204015002c42d0100f056607400c911081c40001e10140c02984125042a02e904000c1c3c20441c85c101140304036070014078114005001d90300d240e40000440e0140b03118800c01d40f002400502504ca2900320030313080e5840044c0c0b10f8000804416015118500a0341509401a090f140c0c899210500c50b48036a10036200d2a40f00141e60b04081001c10000c035 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 222597014 1250 222595764 222595777
    0xf0515040b03010c0c0305031b0f0406020c09041e111e0f060304030503070f050403081902010f09171804050a0b09010914151c0b15040b0a05010305040c08010e07030b0705 75
    0x1703d54180203180d0b40c0b803c80da5074100400317008230301310520210f04801e180d8801034908003074010a42e56449060181c000d04200e02503003180c0c010400403007400001b8690805c0d40c405d02c2c0003610489000c51880c1051040c0041052600340c10012010400003080c0d0b6150043d81c50079070942c1c80c00d80c0c80c2815402c1c842144411075002e00003c3c0103001241009100351013506040c00070703262042c03c00303489807540c0c2516440101c008100c0361201c18411a010b8081c00744060988007001c007000540d00355110510044050040c80c0c0410b02c0014600b65120b0854002c030349525400b401c200107034500b0025600003414040c45082c4102d04200000500341c5a6000744d40c244c00c000d41c9203d0280d00d54a41c0ea410812110080a0307101c410300c4241e42e01c420032500c00c1d210640c000c650b51440c90504c2b6921904c11034185508a0080341046508a00740e15101c442404a07a4203180004440d81c41c0c2c1401e001000c220380080d001c950038043c89842180002070890300b030f280641401200c076228001e06960506c100d2 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 222598264 1250 222597014 222597017
    0xa020603060108040f050709140f071707031401030501020705121602220207060621240e03190e0103060806060f031e0304090e03090319060f0515040b03010c 69
    0x810000c0c480303500c16150584c001e485101403036126240350362800c0c2041d080c0e1308032010441d0303201e030b49401303c44ca0142e0154008820603003100ea00d0800746401490703a210102e459441e00742c0000414009072103684009a00c80300c4014030591945c403071030940d021754400c00c01901e03940f04a00d1158000c0c05440f003250740300400616070b48443d4046509002820b41611402000d00780039881354003002d0030600042550070302c18040003c8070307400c3c090f200c1e1011030000c051510b540078283e0428000380040321108900348481c418080c0201441807460042d01707954621402d14000807440303072040f0081e0002814940310b1512591910b610f0400110308858042c4115101c07544041d001ca801e60034550410145408040c042d10009c8030b8042c0024465401b42492003079640c4001810005800c1621844c0016200c040c051860103aa210002c0d9880e5007410181018075a4803c1d03113405c002443d8001280d90034404420f101c10b03c9d1911080030511075020840d0b000c2c40c141000c450b014a4184254091030307109 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 222599514 1250 222598264 222598267
    0x110d18110a0e190b0d08030f07080108150c040302030703050d08010608190207050a0203031909080109120f09090903171f0b070515180f010b1e0402120411120a0206 72
    0x903400f0510b40400b40107410310542c0d43d141e61603030417522103419091689029416030341c1c0e282030400d148030454100400407001c22030400b00510030300e00040342100c1d450b003240358103101c0c0352183c0c03402c0c2c0d58138400ca91000354144264000041040710108443c00080b50544842c01b25a0740c80318181c50701402200d0103941030b2411600440c040c4c07125030107801c14600600071144846a990b012900d103030b00ca41d408464003194041c40316540e45d84500904003070300011009020401c05540c0380d8000b40100c1c16504280040d9428081e8641d210781d00b80c00007400103032000e0007100c26906024188245002924043c0c2500d1000151104801c201c80c000110360b17000d42e0000301d07240c0400040c081d017064001312201e009042440d41c503a003060311558040c20b42c18185122a04508001a00c0d107200780c0740f4085036905010740031203180d0382e44251407080c42c41c030081404100c064100184c02441019007d00540b920b4100340310600c20b00ca450b442e911101900c1000441c0c4405140f56540c1c2e82515009610640 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 222600764 1250 222599514 222599521
    0x171002090102120d0b040e0105060f1f0813050d050a0801082118061305030105060a030b011202040905010e0c0a0605070c0b13030206030702030c1501050f04110d18110a0e 75
    0x90383e00201400d40f4403c1c4001828000c48000030f050300ca611031030344903d039101ca003444410b1904000003104404201e800c141800c000078540d1841000c0c1c0e071141414440c500c03001a4000d030b400000f54151583c42816100e428000280150054000400900024a0380c10012610800c00545078812400d14804000340e0717140014a242c02c0d42c0f04030b48500b403071003041141950702d8403800d001c1c0c05d1020811511080881c1070005050840c0c10040c4068030504014000308040389001352040c0c1581d840541448542140d0700214002d44244c0e5001003e0350310b0003030344d400003130404100c01c0c166600c219035012074140d03640000c44550052140140011158000801010000c40c0042c00c40c10010441d0050031950390300000c0154000f15258405a000000c0411450505104101c41e49400c070108480c19410b0034049940e030741070600c4140c010f994440303290265444c80c0b8142d807070040302c200061104107641a0010400207504008072400e00d00845415510f1038140c1c0540141c2c0c004503107000d5a40d4 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 222602014 1250 222600764 222600793
    0xd020712090503031c020c0703030801030624061209020d060902100f140306040624080105030604150207030c020a0609170102181011010c0302030603150121020307050a171002090102 80
    0x104541c0e00c1882086d400c0103d0301241005000c44401180281c456810540c07540c01c212041e1502c075014200c2041210310341002280500c60500e0503504e691034440102ca0782ca102080003452441c401135408030b05041c0c1ccca420081c4a410448605100741c54080c90004040c1c4152040f14140880342c0100b100804c44489081d036100140d5844680104003040540d0340d08540b80c0404002c100c6080c4190802c164003048a400c07014607030051a0640c010003140c5000d482d060314020810300d01c135009030b400081c071005040c4074912217043d83d5002004802c3c86030340c0e1030020f000c038840c6109400c1c84000e1140001d11300c480c10700c01e80e030365941140041d807040c090a00410001100050703c0b5000e0001d129401d0340d40039024424903030070b084991001a680e0408808142ca007140302030030840c80c145031b0780c018440090300074024942061003440510460302d0034400282800700541207070790004105c03440003880140b00024031000390341e618281c902d41c8800c0205030b0f09030300c94000c9581c09680318034065158003 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 222603264 1250 222602014 222602047
    0x180c030905061f24020f0c060406050d0914030a1b050d0c0c0b03090601060306080319200105090604120216061812050a031b1e02150d02071209050303 66
    0x34442c030090750710a80e104d1422044a44c1541450507407100441000a800c680400103d006041144000c00002d0207820006100c5d10450064000304907000c205000007513001c0e0082e4580b158001041040c48205c050760517030b60380200614a00144520103038600401c15039001000c001c3e0060040e10043c0e05001c0c0070340f12102021001c035041d200300a4005a0900c010014500520401020b0052549030030b4000b019129a0b40145c0000c1e0810098540001c841400b003840c4414141011800030030f4a680c040003100d0840f00c01e02403540ac10013040895040403900070b10071403040a04000482e420001280d81c1d00306840120004601b1020900547c0c2c02400740813209020000400c0c000d6858114522a038000000300311516400604d00c0c604044c1c02c80311784003091002ea91117400302000c40e215503001e500280c81000121800320f070190159103c0c004444050002981e0042e03035000400c02e040004d610203801522074040c10600d603a640703440b400040d011100020021410700607207030b00300840d0 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 222604514 1250 222603264 222603301
    0x31014010b0304021206100e0c040b0d0f0b0d0b040b011508010608090a060e0a02030f0d0c0204020d0b03011d060705070807020f040b030708070f08070b04180b0406180c03090506 78
    0x102c2c003107100d100e007035806c01200b4030540c01000d0b400c071458507124061545402c080c00c40d810166051205014079040e0005980c965050a000864070030003a2080e038004020008201c2c0c0c006209290303200c20300050b5009180624801c14459100380c1e0f840014078880e054008183c1c1c00034bc0d0810042004130300c50706d8156001482c000541d404a0500c1ea07035002100e075400343d13200e5150000002c03a01035203028000d000c40042c1c0200030b000f40049011000300a96404840244180e6010501483c040c50759070207100f80c214080c0003000003c0a21041701030108282d504101c180c4990303c000b68946103c1d17815510410383c0b007900281080036950822500b0360300040203540041c0d0341d40c40d096150781c007004680010655100680110350410030980b1801145801c004010360018008010108284049804070341c6130003142e03480b0000000304000500080c51541d6030260070102c010640c1801c200c2c045a0380d0303103426000c0008880c04901501072394040f0802030880e0708a07800207480c4174400b1114298 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 222605764 1250 222604514 222604519
    0x140105090c150c0d180806131101030506010813050111030f04120f12110903010614010e0405041110050f03010f0609060e010801032301020304050106030302070e04080a030c030e0a11031014010b030402 88
    0x2512030725946c041d490030204880e41108000302001c2e000610426103141c0703241c00e0080ca424042031130801300113404401d015080b035882040c605c5446041c442c0039404440001001d00d462a62400d104045d1000307038030207a600b074480441c20035501c0b04160080c020411014400e4a400d1004004650002c0082c0203083c248030070b81d0004c0081b907601703540a102d40f00140100c011601d1140c410800010002c07024201310394052850f10081c0700c041b036000d1001842c2000300312181e00081030306100c2158540208092040b092102000118080568200c0a070554405503200c085082d51050100c4103090783d0851070340031800910050010030b14219840d031702440f42e11000820780b004943d1180c2243c0c4111020b03500b87c0d655400c1802010781c1400a04010420520f50b1401818540c8950b41288039099801d814144d0740c012400d2824000d03000218600880d00070366644000c5800c00001190828802c180300e405003c10140340a1024801d856039004407464089542c2e0811401004580c800b40c402c0e030b07 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 222607014 1250 222605764 222605807
    0x1d0601090e0f2514030c09090c0a0f03140624071a060303030103051209030a0c03120f020102040b181305100906050609010813140105090c150c0d 64
    0x40c0d0768441222a401021140300c4a819450081d44418001d0204803411100c06511040c4094a950100107008240003038a074080d920348608218400303500c10302c800e554100d11540e0402500e01d0050000e4003800c40c40c0d0319140304108501100b02c08884c00700031200c0350a404c03600403440508180c403e026219045482c440311110114100d00030740d0b080210121220440314151013030304203441e80096003044007900110704550450b17660303540b90034034884000c00401000c1764007030301d564080211303609464000c0e01224800c1c2c0c89041c04c46564841d410500c000c620000014000d203441482142d040b0307007807001c403242819420200140403422902441d40d01c5484455604200e6001d485007034004ca0034410101c01c2c031791802c2c10301415180359502051050a0510403008247d8220000541c010307410300601c030340050b480c0351241074200c1a000721303d201d44c03801040100c040b00c0000c20010048040307074018a0f00b0702d072501c1004c661082d4031450302c940c0c00c405010300c02035014605030140314840d516400c = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 222608264 1250 222607014 222607019
    0x160e070e01020a1407030203010e0a0b011e0e15180f28050a0b03060903040b0304020402090301180c1e030c0e061302070303020319090203060402060a170103050d0801060206011d060109 81
    0x2210301c5900134888040d03008003100b00708518091191010069544001c2c0081c48010344942001d0b140500c911803040d001c40004040312666008110041c00d0840c024101c10704000c001d50071141c214405883c010b540058200da0580280c02c101881111149440e004c13035680c02c0491155040740c4416400000b10017840e0880c42e28203030013403a200d81d00180300001c01071040b0003018a4440060010482500200014841c414501086a602c280c0598016a40f40340c0340000ca4010041804d20350907200d040442d9400300041d4020300411501c5102c104c2e00c586240071000242d01403548402400072402800070800101d0b05800b040d4494001008428006480201903059901c0b80c80c007200080d07070010070000c1c22500040c7c4942072111080080004c07140d1540070a0307403944040c202910564010070351621442c410114060441507645045c199542d507494165622070001d155000424000350001c0742242c40025141d04031a4032614481620480481c80c1700e51b2200940818100062803801 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 222609514 1250 222608264 222608273
    0x30623012105011a0306011a03040611041e050901050414040f0c0b03131707020112050613060b040812070c03060e03040510020d021b0d0305090f0d050f160e070e01020a 74
    0x40100d421304103403110020080510405040c440160480003800c03002d010001c2044e4400c00a80740e0181d40303c1000144809c1d044402c00c000e02842c0c0c0404001c070b8154403460546240c005403041118403c2d80d003080d141c1d8a480c02c00060f641c5500c2402c0491998070000f03000300700340400004129005440c01e404081c0c0b00e10ba00205907008603000040703088520f100c50f00b0058450b03610200356440140c1d41d41000700780e1307000a0a150300044078490039a110000700c0c03501e0b80d80c494400004000c007203040083c141d4071501003029400c5480388044a000b4524005400c504480c225401103034860000c0038060705695036600204a00000009144001d10001c00c4d02d4807001000081d4a115400400980b02e40200091400c1442c0908880e47c848500c0e42d184142c03100d1a1800342194541032003a1601c40860100303000c18040f541e015440038a05245030280b2401040031804652810251940b240c14120107090250302481b586211042c00d600149056115915104099005105940c248007090300c4 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 222610764 1250 222609514 222609521
    0x20c0a0510231317030919030503041b0905090a050f030f09061e1303050d02070b030a0c03110708040e0c04030b07270f1508090318120d02030403062301210501 70
    0x104c108140300000388080c1c0ba80c20007072407003000802c0d051081892842d540040550001900041c803002c10040c0e00c1d08011030132010240544070b048020807441c5800700c11305540c0c0300202004d56040c05120604040000044100c44501510203040c078905134a0320240705541c0d020600024208108001041c007001c060001000c0b140d601c1d1612104250031410401d0401c183c200c016019944200801c214000d070400641c1e0b48104039080019400d0100c590a0300600700c00500d190007507800051450400101c080980203403808496002075a983d04c007007241d0180300d1800042d104072020000215418030820060190390400c9040e4040540001440213030300560b60402405000d0030035050044c24070314004140e590b0098540b051240c10a071503155102c0c070034108bc07900c0501e140c071615100381d212020050740000e030100c210b908810084c2d40007074a0b074006000890b4007034101481d5a04101001448070528444200d00000c0380c1d10300b20300e00e0581e04804000b0600400e1442c1940007085080c803 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 222612014 1250 222610764 222610793
    0x141011030715020d0605030a02090c0a0c0203030c0a1e0c0e13020405041a1b040905090a08030c03011e0503060601030f1d07030b07020f150613020c0a05102313 70
    0x120140c0c83d145130410758410341c1c0060b0441c5000c1c2c2d02036000440940d0383da80c0940d42102c42c02d03600b256903424400046031a080a64000b0b07415210000d21051484c1001404000340c50240b01c010900015208641c82c4007000f5410140030006092010300c2a0305003c80c040d42c0280144602c1101c040c151785c003060a841044505031030303904440c404024110459400581d114040d503480001d07901058103c0e000c0c1d03025501034012030503500d034009000c28030200308019446401050040d141c0c0b80c42c21101403140e20034001d18030005e4125116111804218150030103540740107020b4140f0b980d5003070044000700400001c0d040d00e13903100c100340e0150b000064071410400c0c051002406100341035013000701c0c9680c0080c02060440d440320700c1150710303d9008102801d00c0390303050311455100d40b903c01c0042e4070080c81e086900d220320310028928608400c001000241c0c07521400a17180e001c007002504108a034500c460b5100c056203010202c01002200d000007907400344a0b00386108505490741c40718038840c0082d1 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 222613264 1250 222612014 222612053
    0x21b010c0315120f05010209190602150c0f09030a0804061115010f060f030e0d0f0f020604150f06080601060c02130207030509090703021608030a061410110307 70
    0x80d0000080a9450702408a40c2030b039089060b05071500d00b418500681c2c6030002c0c084c2c8101040300c407840030403000390101c5516041c000c101c01c840013140340e0500041511445a24050b01c10945d82040306804403c3c1248150318002c0d550f0b09014103040030704501d5200c0420980e040c010140164001442c041c0a040a0321465852038461302441c040c1d14500310b00400e0419550341c60b14010402c200c0280c0b00417003966020302c0d0521000b40c1c0424164003802c0a0030b0200c0d41070241000c0d01c50b256510451900c3d4110055440b01e134008201e41c026a1904401d40380900203d0459000075440c0e070740d580180d011f940f190100000c2c1c00382c0c0c4000640c03c00500b0307082400040c0780c048400b81540f90605a6001e15409110f04500d42002603078003504034800d51032928007511070040007801d01ca01a60603030f07400032401114448460702e6071400901540c811200c000b100b0f03103041d80204440c0c2c04100c0d2a00701c0c0c40041c02e0b170b0786442c007a12801c6c1c3d0319100342d4422480610041140ca80052450307000700d0b00c5c02c4502e = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 222614514 1250 222613264 222613271
    0xd08061002010905150a0609090c0303140f1c0f0b0904030815150a02011b02030d050406020f0d0b100203040501080105060c1e030903010b0103020c0c09180321060418080a03021b01 79
    0x1b80300c0e07034050b11500c0d481807044504245840002c1010b2a40d0001141d505090880c0321480380300060080e802000c184d617240d09400300d0842e010fa0b580d0361240c0c01c07001d2600c8041020010040d1000c1c103c6070411280e80d0408111b0002500090080d40910b4112100030050800b8401243c00510b130940034204070f09403120080759200949409000d06041e50386100448003c007a040390b8003d60f04d00a0003440101c42d40c413034020800380300e400c0e1304586402d010414a107548162080d4020060a2100c45042c00b4502140924609134804020340b025200141d40e50006c5910380750812000340c00003001e4040c9400b0360b000e50600100203906184050940c40069911912004105801c45250703401e910705050040141c4000c004000c139000b086c0082c100d076801000e84442003440721021180c85080a640320008007071044951800c100801803e03000040719042ea40e1000340300544c3c04010182503800f03168440c5900103001c03a406071081180a190040c1040d66603022940300701c01c9000802c6030381e5035 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 222615764 1250 222614514 222614521
    0x2190311070b090129090702030301080a061113030311070e16030b06090301090b0f01080601030c120c03150204140f0303040308070501021e0901020d0e010e01120207080f0310080d0806100201090515 87
    0x906c60b00d1103900c0b0000c3c0c005181190301d00b03e880d41e251241e18400030940c56139003440340c01000e601c20984404d9aa41301d0402d040075100d1a010f403d100c40307800c81194610400c44000380c80315042d24043d1003180e042c008481c40e00740804050740038040c0000c44a03840b4809000d29007580d1001d00c982c4018034011f00409d00d140c2020150580342c0101038004446582080d0018000f18012015500440d1029003000e000f64255042005000010f50030007410341c1c00c1801c0070003190b05a03402900641ea001107003400ca1a10441c100700d0b4041d00045c0043d0943c005100410100d880c0002030303e00f403806200050700d0301d0100100001d49041000e0541500080072a1440c1d080d641041441112103060030800702c0540d076000041e2640d52107070441e40c1000a00310000b500c14070345405441c0740c41da2204503c0d0300c0d0320941d00c1504c02c5410480742e4180c410050301e40050360300c400248107440080c09844d02442501d0b03840620031905043c08004003507640303a540400018008020301c084042d0b25074142d07182c506 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 222617014 1250 222615764 222615769
    0x3033525020a02090103030e060d11030a0f0213120312050c030106030507050310030809040603061109012d051602030307050d08090a030e09042402190311070b090129 73
    0x1101051004561002c4000c03001030310342c8006207041d6505803d24900071680c41000981d03502c11840441085410603026500001c5828055806089003203018083d110740c1130781d480708038080c001215140f0350090904002401a1a8000800364040d00e4042c004261400e1b2020660f281916203000341a8004010000544d151140c142c20409508c0e04500d035042c02e611002c14510940400f421060000030700b00031580e07a66104800455004806011410a187c02c000c5140c04c03005002d8042044803144044114025550800703100d81c3d041c09e40e0b5018050041114942c02403103e0030703110b4000309000c1c00940c0d01040070b8000288600f00a0510f03110004005026610141c0100c007a50f10001d01e1000007500000700e03481180341503443c40215680c0381022200b0912113080310312074007480090b000001025400604840080d5182a0001c2440920031402c4941e03900400250100c10f102e1440003600840c400340e001910080086081018040340040081050807a0202801420f10208990 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 222618264 1250 222617014 222617071
    0x90b120a030206150f09060f010e04060303090e01050a1a0d02070209010e07140313030810051c03030c0e010c111912061404050c10020a0c030b150307030335 69
    0xc500a945c680644504c038804100020805440c81c1c0c42400c10b07052090b92070f445121601039019000b001442420394905000d0640310b0180510210110220000300381404c002a012044030a4500d0f5010302201514041045170407036090044103540800c03145002d6518040101d010f000040e2807150141403541014041e88844007900007600000d00400410144404004031505c0e01424500c996540b0b01c11b1480382c150007600a0750713204100c1d103401031410071400d101d100e40900c01d85042102a20307404003039503003170a0184c00c5c40c001200c00020100080c43d0041002c500c59000e00b28054000072561104106070b03054000305403840140e00c00740c09000c0d603030007481144500704011440318105034442541710008103400c3c034050402429401c940f12700c2044003000a80c0c0202895201d551245803550b80d610085c2d44441c20059a584480d1031440c0109200c0d088030b6240c1c0300c0120440403103100094060100c014a400c003c5182c080030301c10041030385901c1c0b1074901c4400002a8807160200320114 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 222619514 1250 222618264 222618301
    0x20316030506030705010207050d031202120714090d030c06090c06050309370807140a120305070c06111b150c03040b010509040c030204020d050103120f09090b120a030206 75
    0x2075801031340c04000d240d801241e000b09803041078980f07000030500781c102503405080305804070030400e10000e00403543c03220885009003d02241d40e201c105400034515681d02c10300403240410303448002100d40c031001034003800088888605c121070104040c2040c3d00c03a050611541da2000011820001c01c01281010500c040c081b4100c14202441e0254860390007203141c0a06040a001e51114a895181c14459000c00f5119080d07800320728205440540861180c42e07185011048604105030035a2401e0240207000f070314810900e65541168481d100d40b0380700081c003800100703800207a01c2000050421407044412005100030207004181e02100c43d05806500c840040202d52190f01c28020720000504807419a0704555007210400c0d000c0c2c80701d04056620b044103910096106100051481081203580c01603412240107040540240c07440d400150b4600140c17088980001e66143d00034805094540d01c484041c450240c003641c240c0b400d40f044c0500c0d100c00303220143d002da44613004110b0b100d04019070b16140c = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 222620764 1250 222619514 222619519
    0x180a0f0302120418020c0f07030c0302010e0607050a031d120f0609010b030304090905070b07110f060c120304050f0619060501022805120301120309080307020307230301020316030506 80
    0xf50528040d104000d580c00850003820381a000035070b828520100700801c1c00041510750031b41d8040c590340d29020070300d50654031040f40410244104d03d80185000d80a40f88050b4121005d80400341081e50700700c40030b0300e540b030000e00c0b0403426000b003218949401d1503440401e2681c6005040d4030301688002d51619070011728110f0168180501102141c40c0401a60200e65003041c1c0880e2000203442c00c14201942500445503442002c10781005100086030310004450055848505013012070040c00708610a0076a00c3d405540001c241c4043c4488190055902a009406071041814262001800e01805961038200180040f0f035141d6448920701c80c0c40d0041c842400104001c05034406a407099409d00510141e0484140d22401e0900c2414441074614010444000341e0b6503131070703808855103941811007e41c0042e16441d0081140000001110300050300140101002486e0071f064050440a5484220080c40c000c5482c1c1c003191424009540941c01401d90b0783e524502e10038006040781ca005040e01d1 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 222622014 1250 222620764 222620767
    0x8031e090a0611210a02041d01060e0405070801120609050a05011e050105010e010302030702031b0d0219020904110d05150717040209040b060a03020604030c1e1508180a0f030212 78
    0x203078070440000082a0b600c041c03111004842eaaa1005c080c001e008a611206da03c2d91010300c90142c0580c00001941640c80c141c0390254008116001d201c2117420071940c0303e000c524004014000c64584601c100e00c010b00c00c2c400820898100d40d0f401c0d007890b41401c0100c5481c2c0d100c81c0368814011107014a941e14203180d04040000f50700d4080020804400415250305250b130001c04a03c441d80709004a1311740720030080300c50100240c41280d00d03a40b15008240c0d800140101c50140c10340704c07400358a900c0042c2c5c000b400140d990b203e6446202c07000480300061540000100078030300010302d0904c100506991780b4004030185251556001e050390141b04084104511011b0401c001a40e1301c0e2052608650450060b002ea90740d51030101c1c0c001201c4d038002a52250707010400104024502c0c0120098908070b5141c0d400d00065404100c030f14903403074024103c8101021100d90480d51050b500e03240e00c00780c0c400344041c16604005100f814884201400e60f405040000a1001c0c95010800c2d07a24220302c0e246200d = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 222623264 1250 222622014 222622027
    0x1080117070513020903150603060a060f031b0e10151b0f030320130e070c0b090115090207170a12150e010e0702010c17010308031e090a0611 62
    0x12516881d450007840c0c49501490200e000c610303016810b903030b46044090304a412a10480b6510807001c03034120748491080c42850002514101d1501614003100c004041d0300f00603070300715078940151a00303c500c0c2c0d0080c03426039840028001c4c407929035036000d9907010704881002030920300446030114078208400103100c02d9801c1240200b03507240701501c005801211035004105075180840242c500c0c554007070003007404055402e90f50410b19004040e912004800c0d010016507c546032841c7d54030850300d07000030030b4220400402094110500c15030003804000001540c0c1c3c40c191000e107a000141d00050145540401c80c101085007501d805e000e4a8010b050701d0b42405003514004110f00d69029800c2e00c00341e224960f00f20701c01c07540c018080141403452410030302e0f903840385080f06015004988941c01582841400340c2c9035800744808103c20f001800440c0c146a0030340c0c5400c482640098812160007074200d1291444c443c20840543c0100340100140880c968a0304011003645c00007140d5071512402080b91 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 222624514 1250 222623264 222623309
    0x108070603050c120a0f110d14090a120302041806091505090a1d06090a03081e07030525021b12030403140a06090f020909060702211c0b010801 63
    0x25150b02450041d0040005d80d24141180054007044940d02c0615082050000c100c015a802801c011b0500c94070800072081400e1211841c00c500740c60142c10b50300100da1100100303401d00c00d0310300c0200301030a0251a282d643c4170101820142400f1000c0055a5024140061002400703485041000104407580035400c000004000c5000178110300403940d50340d40c8002040f0b02601251101520043c20b565940c03034a00320031500e404602c44d003200080c410b9000101042005028001c40070ad403201c4c4000e0341d640c0c1c0c10003500180340c060515100a407030498100078142410404800041440d40601020f4000580315441c503143c0804092090707001307a008481494001083c0d03000c61307070401d14180030007603003114540c280b2803a1080078048a060100f00c506200030350310a0070403c0c0c400e80b4080c0065640c003000d2525070310180c07540340050b0010f00c0000c42c2c02c40840001111113140071440380c60b045c04c42c01109151008803000f41034150311501c1c00c07911036030050201d50050040710018104024040b41 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 222625764 1250 222624514 222624517
    0x40b18030310090221040c0306050106140f0a090e070903150e150a020403020a140907030b010e09040302071508010f12050d230708030f10050d020f150a080108070603050c 75
    0x2803c6040e51307012031000a1103410692880c0c0459910000034814141030071704410b005507601050f140c040c1420000101c20344200084581b0710541340038a400c090703000c52403c03016072004540c102040300d000390205520840311303141d0f8011282621805555440c6180402a200880602e4488149040421052807101080c00b141d0000271603401d800c9580c540300070720024041d581010750082d94080c4080b410b07041035074010400a0040317995105995884004900340c88136200c41c54002502c4501c0182c06041810607141c0061003801546c0c001904ca0a1070502c1d114545507203000285907500400c4141d030600030400140c404d400c0c060410b46416243c0641d2031440c200500108115a060900d10030410001c907551a0020a8001d90320141c81c200f100d090b0700252100b1820310345c984003048800c070307106541c0320442c1c2021f0040030402085408100b02c00b88100340007504400d0800c111042184c00100509103001c160b15240c1e620f5050082032842c0c82c0c9544c01a8060514040500100c90721450 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 222627014 1250 222625764 222625769
    0xd0507090503190c1e060e04200a0c021e0117090a08181806031603020a051c0206040f0315090b010e0702100e062e0515070b040b18030310 61
    0x914000c8040442c6020181046142d000265400300c010240c0c00d54800d1031100022070703100781e9404411f00e400e2805c001c00c95201ea044d01c2d243c40c00c561034001080031140f0250911103040c1c10102020001c54011807000c00b20000c0e80d900c40002201c0d0500d0319a0030842c1c1c403419013440c41e2851094036004508980e0703003807261401340600d1000b0460000364801c4445101d08900050100b01c0111014800307407008200c141c550621034090074042c0c00d48030401074008011640c0045ca0401c090340340c64280100111031071554040c45801d051041e0158031200d0086c40282a000b001010041c07660a20288550144043c07203040c5040500d0300002c940086901415581e0200c015441307a01c46101c103a113410b010301d40d0756941d075045c5400051009004078559100c1c0e0900310180e203d01043c400a070b02c07150044d40100c20950403010061203503040c407200a01c141d210903504245020102c1c0c5071002200811582100c418400b00108000f261084070305080c48000c2d03600440c00c50800020b01c1d685a103260 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 222628264 1250 222627014 222627043
    0x3080d2306041d070b0714010207050d03020c1e06041101170604050c07020909070509090c011d0402070510020d110301081507050d0f0f0e0304030209010303051806040b0d0507090503 80
    0x40a407001801c000c848115a502c014204481040b0b917101010007070b80c1c01c054825121071260250301c162440c4180219041168043c01602680c07040d0103080d0000e4101d000030800c0303842403900c050b102990003510b00c400c03030340c03144024105860245880041290510b80960404c00c0307100c5060502c9490810050300b14804440224640d030321401110164010100302950040c07004042c07101200b4003040d1003040d1402515003100030b90761094615901c0b080c2003580f0303000650b1442d0142a0118014060040200041001d031074200d00d40c840d2803074004540318507070006600050a0403a0006440303000c0c41149442c070454119850031022603180c100440c40d2011100b1040c000429680c4a035049075040365050703104000c5c054200304e000c00100262001c001e013451800118242850380003040d64222940106101c0c120b80c01d541c0e00f200e144e0865808000340e0342129003a03140b695600d002401c040c141c20380300c464541350355a910300103854010304484244200e0340e00522072500c0c003042010108010 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 222629514 1250 222628264 222628271
    0xf0f110a081b0706181101080105011d0607060221100e06010509010c050102190215040c0b070309050604060c150e070603020f0c070b030907060302030702030913140103080d230604 79
    0x1070741d18060480c840c0750301c018001e17481c1030202c0641569000d80c000c00300e0301401b1843c1d101c0511800550380100c080c090f19001c1071780120a40c03c0c440780c00114141c0c0380300c06005c4a08110681c4d496406036041103031642d8400e0204210a048a8542e2402940c404048440108510324082071032007540c00107007401c1d0401c2000540300c0c1060740a40c503101030007640b10000315074070402c4003548070700045a102d10702c5c0180a9492241c07094068120382034051a0080000d1828501d4046420401d601803034044062109081002509965402c042d1004050075103075044104294640841c0510030035000d400f1a6252603003081243c000001c42c0000e23207801e070400613907452070b60740c191710309000700d0743c1151451140f090b0206c0c280281e50099030140c0c18003811207260300d85070b010603410382c001103540c0401a407040c06920180c2c60031070410094801c0303525000881c850084030000740312409800c2030710300c454005401c5040328124401c1000c1c0003210040c3e4480c3d00382d00e00c0f42070803030b64000d007000348910349 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 222630764 1250 222629514 222629551
    0x30215030a0207140d02010b060325210b0a090c02070302040209040f05182b080402040608030a080114010512010b07060e0303070309062a0f0908010f0f110a08 70
    0x2026812a103c00b40c12041e6032001d1000e8a442558440244030f56000550909101100b9803c3c1942628080e0001e07107191030b1508041004100041c01208081c01001000c8800e004100115403580ca24101d2203100421024403000c1803100d8082d03280d00c84100c15207482d4086810a50202c3c030071041c3ca0381284c0169031150b00e000060060150501405011468a0140440140500c4500d60308003606002d49019001070000000c00c00485580701060104282d81c0e41e9100b407041c89100c0d84140300030310019029880320741e050b2031900880320610229080d0750042c0320328141c80414101c0540c0901c1c18528012040060905500d8184115130030004046810010003447d900560710300280e20045036100d24000c003000303028020794401a030f515851b08003c5001c00d00c05514010403840c14202180307150002402c11540c000040c0e0800c0c04100d82a48003041100d0f007800741d00c50460007490042440ca1224200c101154a484804440000704010003844141c0040c02c0542c0070701c0402000302001c5 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 222632014 1250 222630764 222630781
    0x13240806030c030d030504020307050103021e0901050715050702070f06051615020307090e0c0405011d0d0605010b091801060e2103040909120207050306160207051003050412020703021503 82
    0x440940b034030740c0c14050b018901d89200e83c19808644128001c40880b9050780d501c40040d4100d2050440c480c0460321036004918803403c00800908141d041898101e140510988480402c40415070000a40d1030b196010311000700e604015040103460f0001040040e180741c12000352082c89810301d400c01e1051740707203420818000000880018035044034002c1d581c80c503001d00d0040902100380181074105840c50042200708507980d083d1401d94606840c3c0c6802a4000c43c0d21104030300e0304040c0b05034030014203540940065000d000307540c001d104100c1c942d500d03882c0308401c110304503072141d4200807005100001007141942c80712020f04111001c0d1000c1816200e10101c01c0390410b285c1000100302e202c0010b0010380307100164045a1120b01803d0703511520f481c0d121041f41c0382c11003031007082d0f89640150003149900c4814085036403000e01c540110f8440ca55140082814040010751207030100c0d698030100424048108186d4640c8040d91014016081c00c1d903000401403522840c4048050030302000041005 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 222633264 1250 222632014 222632023
    0x5062805060c0d0908160902090d120302041d0603070303080408120108060612010917090a0e0405010902010801050d080d05042a09060f030b0c0c211324080603 70
    0x400000d8100c41d52564041d01c2c5641c0c2d0300d0341c8184070002410754035000031601004541d903240c4000f18210340e40b02514000c1441c0294000701140b80e4019003110303107200003c2e0044407a0001d10038640340962104d1800507141b80b4013015114038003d02c0c4105081203490303a404a0f148007a694035090070001c5441d00d081c810414001d00252000d0311030f0f50b0340045900c000c002501d9102e1401100c40c50f4480c103003040481d080e209440350060030b600000035102140d40044005d400c51b0701c0040c107a1100e1943e9482d2000082900b51000c0e40d05965590500c400d41d40d011007051301402c0c0503511024021030035030300e030311440c0700307a2401500440d6190003003801c208800705025260303c0d0300312400500c80300c80845940902280c0c49200383e018504000050302d03040f994929411260042e060682582e101030407000b95501440c08151580218041c000c1481c541550a02901c0007922040d40c0380c110388540e042070040540c100c640c0c82910300e10820158601c80c107641c0c074006801e1510004c1516988046440d0 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 222634514 1250 222633264 222633269
    0x519170c060d1b210f020f0406031e020a090b0702040207120807090806060d0213090203061801060b03060607020f010e03190b100501090506071b0f0513050628 70
    0x700000056400119103a0340000100b242c4412a800c108907010b00c0c03e5072007441902507403d04036240c0c610303c0c2e10300c03807070303030b201500d100180c030f1025182031000348003003000b0b80c001d410500c0803e541d10003051b5442c0a400340c4d0f10b00c594585408520705004498094140000351040c40c450060010740102191640c0e01511044c550021915207800420400540420412224500003e6441600080309280007600034041c40010b0201404510150203001203010300a0f01c144c00c0703d49401101c0016101080a030744205c2503503100030410114000707a00d0039a13100e5030202111640c00e000344085543d4210451f400240e04480c0031012207a200700681d4040345409443d50306028000408099407805e00b00254864400c2500c84001d40d1895540d54510000d0301a8a0004035540300c01d01140c10010300416815000d850380c0c0c0290002e164405040103660703002030485480e04101003000781003458440703218a2901e60240060700d001004039511119002595544415000740b03540c10072250031542c0c01 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 222635764 1250 222634514 222634519
    0x9280803030a050601080a0c080711070b030a020a0207060e0105090f211c2a081308030702040501060302120c0306180c1305010207080d030b0a0504180c0519170c 71
    0x80741e14041484400800044030b078a0f010600800010303005180a1044001052244d220380e0416103850380c0480750b04400604100851245041c0400c1104154018611a803002100580c0d1101303440c000905104607075118101740001c04034901d40c1e070ba03000401d5540c2044140c800d00c0310708041030000f955140120350b404a040e10500320a2004103008140700c10800c402c504041e08e50031020008680d4229941140c06c2802007541318a500640c0020b485c00d41c507030280d29181e041c08040042e201d0b885040b68854503555200080d0343e021404c2c503014060040650b0b040450801a88210040503108020440310006030008000f4009070350351101c104004401a40c140c0e20f07490329110082c080e512015402a010f051481c1c001915840000c4200c15034243d5130141030f1400d02c40714290701a1109030603095002054030b90110f05c0d5103e40c442c0485500480c03111009500c141d00706840c0c2c510300c1c1d400c030038050848040480408036942485174111075070800b42444150204c01c545040c4007104120a5 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 222637014 1250 222635764 222635767
    0x17060a0c030b18070809030a0c08070c150f120e19051603080304051011070f06061703070303110c070314071a04061215060c050715050c011109280803 66
    0x11030890b00c024030f0751103100075449113442c0d40c86d60814540e41e40207855681340010038941d01240010740000160040034401c41091200c01c1e129481d025210124810350302c0021004105285196070288a01d403d101c2c00040820003c514503101d181c403000c038022080e121040c503445034420845c2c104081052403540340d4442c45816103c0c9004c51940d0700580307042c1c0c1e8a10a85440100e0800940f065191007840c124205261524a0340c41018144440b031007a602180e030341200040d5140004402c5030214043c002071507a440c0603140103000c550362403607460041141804102e64020f000030345902901e400c940072082e0300400c02a6030b0315141071608210940c00d4461105040c40380c40c41c0160042e40c3c25525a4104ca00010949a0842e2268030100303007a130032114810003403240a215106601400b9105661100d070f01c400380c0400f070031400e004d40000500006104c2c20743e41400c4c451012a00c07401c81c5810300d0b050300f9100040000c40c0d0f4038401d100103452641d159841a1074104444010701d030302405e03a03 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 222638264 1250 222637014 222637039
    0x3060501080109030e03070b030f0405070815040605090703050304090e120a050715050717070c0b040c1d10090203060d0f03080103031713080901030e1e0717060a0c030b 74
    0x14040d100f0702c2d000b02c0203d14503041c9880f0710310b80411034001761b07610ba00b956030071517403403d0040000450240054849008107070001c2400f040c10b100c1300781841d10340031000c10b5504184c607010b4103e0744024050040307078010340424000500040700300c03411200d64110105050205000791070401500f01c14140304a8800a00ea40045402c240a040040c1c00740c008190b00103003081454099079000c48400c00000c03080d210030000300581c00007031600102d55244c800c0c01700c03029546160440009840680d0f41e405004e10410202e00700f0100200141c100585a003100c2c10030760a0401c80e8200b40c06410204c0d41c000c000184140c9030b9074058908107030046c2c6080c00400850801500300902800180c1c0007491044180b0303a000c600c01c0e6043e0290580e05101c0ca204070180c0c84450680c0c2100d00118105920783c903540f4104841042030310791140d0814000c004000c00140482d00e0008190b20202c010703a0741c0100540004008078082d540b1410303400002c074140480d42400c0b8014004807000d01e82c072502602c0d10703 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 222639514 1250 222638264 222638279
    0x100801180825050c0916090303030c0314070306090c0203070809060d0b1507030914031c140c010e010e0a05250b03010b1305150f070804030605010b03150105030114060a0903060501 79
    0x607161001010b0b6132105c0562616640000300921007050324000c40c402c0c04003000003a210b0b84c8501c41c04010752900003480d5001d20200c0e84100c2c0c0580d10400025110b030814450a801e6108140b580d601c18001980781802d960350303071481c900400410303a10602011440002c441c503c1d4010340d5204d040104203914052030815582d00b1600002ca0039400204541408511440140885421041c0060051030b405200040e55000c1428171040c00003007060038001800101101e1024007641d696102c004110192009141400c48803444401c45681d48810751000100e031000c03072100d0580d0301c0107060318403d0940150341a051810740c3c1c80b100c101c52000000181c500c107104007031f020b00c5009031600d0810664900801c070541400c01e82c17150305075508020030800881240000d081e020b104040d09402d103030703803070b111182151826800301546031400410030851551070380e0001000882402d119045504041c8000c1501c450042d540380100380000303043d90380790701130803c02005581c440c80501c40c80d0b17115905c = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 222640764 1250 222639514 222639523
    0x6021c140405010516080402040f11041211090c040515040503030a081815070e030a0204060920070c14040b0405090c030706141905070b01090510080118082505 70
    0x2030a90b455482c01011074001d00c19040d14400c00d81c1aa60780c030f512a1070340e400308002042c1c10410018104da0701c03004c000e04140008060030040800400c02000902c02d4240381a42d00700100e02c60344140410b03010021107003040130607034081d0b40055030301860008946c110840584501d400040c1d16100105401c0a21640050302c1449032280743c500120340c404070310301c01340d603415201d00c0b020b03003a00c1240000c0d207168400c1890b81240c40c0010304540ca5540585c02103401c8811a40000d8841501c84020740e6501c0040340708081d9002d44d40c4665450410f036034581041401d03003030107a0450750b4106505c010199032a500803284d0071030010020069030405c180500d5950740c0300c00b81c4d0b502034001d020000a60900812000341040290350486143c50795200c05001403144402c00b5a0501005000d00d40200d01035044c489d000c2c2050280c00201824401c80e2003080003100da11180075603040c625400301000198240d1006660710800882d101c0b11841c541c0701c03885d202c20b0b09880000c7c41d5142140e050280000c1d = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 222642014 1250 222640764 222640771
    0x11120102072006030402010c02040e010914060108150106020c0904030903080d06080714030c0409170703050a090f1d0a0e0f0616030504031704080f03010905040302010c030b01020a06021c14 83
    0x446045180148500f40412030000b12006070104080d441e15030098105600003032060140c24000142100c00340e958054030950505406440e5032040c401403046030720800c13500d94600340914800c0225894400005c0d55092566012406044002e01041c10580070710319003005035601c0304029440710412803107000100a14801c200940c4246d010018070500c945115140c4c030803019000d03100c016014001c2c400a041e00c070208945840c8100390740000c00b42d0403000740401c288265121540d5204000d8020044400d540050000b150559000c021400340c05007040c0b03000c4004800f0221b20f030f807060040e00080c208020030303540038000e5000301d4031070101c085100d0b07202c0c43c020801005005031b440170032070481d201120000c000c1040f6084100380013285041c0c1c0b50744a8400c0080710715004031940403007402e81003a4000103106449406000070990203000d07105910440340380c02c1140700c40300340000307545403a203690140107540d00194180304510324189200e908055503e091244200e6400381c02801e08045 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 222643264 1250 222642014 222642053
    0xa051b0c130c1b1b0504152102030a2105090a1806090f0b130e030a0c110406241701180204080a030504180501050a0e07020a020d0c06170906041112010207 68
    0xc003001700e0b05107814032a20300905000c1d00c2c2c15013180d0403c81046101116601c405284d07403032848490006941c100941e2004a1003106003948552032034074100402c060403840c840500109210360400d43d01c54617840c0c0210746c80032a42d00061000c0843c1000148620340080c00a039040c00c40b101d00c0500035801c001082982620a18a20001d0703100c180100c507007092194486810070002c2455540c40b440c99940c0180c0206401000807040400183c11038000e80d100f9441c02c2070140001d8100139907403038840300c1da0590382000d000c01c1001104000300740700c05000d000307060070010105c0c0351021301542c1642c01400200c4111503040c51709081c05031164005110714200c0440340034010320188040d0081030b04076603018040d11805810b24243c101076107002881c4102f144905909040541e0701d800460301e101d0b00900240301d006003000700c001c22000c0c1000c040c804030300300703902444001400010f1482c0d01a07000b0140b8110b00c008040000d620039070301900805030b0360000ca122401d00414100010a246d0710 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 222644514 1250 222643264 222643313
    0x60a03140a06080721170f07060902040c0f08010303110a020303030c0301050925030216050a14010c03181103160e270d08060f060a051b0c130c1b 64
    0x50300170403000b00b620340050000b03401c1d0500c400703030004038005803442042030f00020340b81c1401d803400007652498124101c141ea076240c40390100c0d000d6091900c10360601d04514034106a2021900802800364a41031100404000104261201165090000001241d4002e040e0b039561300340f00701c0005043d0003c0c041c80d0301c034084180204141c0d03042441d00c44051019422640d0051800080c182c00035005a038400c034081004401643c0000c0041c4175110b003041c482c5041403820700040b580d943c2140d030788000307803020301d0324000202c1c0a01c0c1d458a07030039030a04e0307000c00d08803a10304100c00460705001e0340d065130b1038111035121404074071000c0b10840c0c0c92240c50000106500542d810201a0000081400c11802a0000700740000c1c8203120302007a903401240030f001041c0d282e9840780850200d9202c0c00360200064000715412031005007015001d6a02600d22000300710700c05241c0c000940916008170040c042c141e4411001d00038600440300c450000c10208000d010780c08c003d0030f19402001e17403a482000078006 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 222645764 1250 222644514 222644519
    0x15080103210215060109090f02030411040509030412060f06060207060e010207030c05040c09030203030a030609150e010608091501060e01031401080303150105090901030303090c0b1602060a03140a060807 89
    0x10100048400e0030360b0007480c40b50005400344280c0074024000074100150418049075806150041c1000240070207001a62454103040c03520b010300b4221215489541420240b010303004002003524103803043e000c4019403419841c0340503c014840d00340481106802c0200024050340c0100303000003210040d480d002c90140022004a0302c0d40c0e4107000003060129045070520039410700b5400f0541000c00f0341480c02d80c00351250002880c40d0490300d0510300180d11441c3c00c1c40900f66600a265038003448152107441d041c10003054104491050007030404005000340041c0c04188204022003030922040c8400f200d80d40c54100c014020484009603030b02203170400e0f0b0308014034100a541c10f4102c030702c030101071811500c2e548100d0410110900e03045040090620494101e0368505800300e00861198400240c8400c4a18020604140d6680b15a94443c41489020b90f0301a41c01341e1100c2c460750494403140e40b40d20001d420f90040000b07001c4501003003502c000700076983d0070680c08242036490000480d005903a = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 222647014 1250 222645764 222645803
    0x2309090a020a060e060a0f121506020d020a1502031906030305090f01050310050f01050f040f0f0e09030901050310170a0203100e100f0e0a0c03030e06180d0c15080103 73
    0x164550400b030b070081000c10402158038481c00c903d1f00180741c0c17031030180c60724503100c035941c4155418000980c260180e01c81080141d980c040016000d2050140082c0011800071b843d0f04c2003840c035106013a8030071900040090203d01c50711800c104580a80401000500d48909008005402c10801c4c6400380401040707040c115800381c0e040c1c0f4800c0e4060f100b10381c1940c3c1040140f0082038001c0e52005c0c148481440504400340c50742c405070001e42000e6102d00c001d903140060410080d40240d00c1008400380481c2440441000841210094a020308129949441c1c4881024141080e503128044030200c1c042e94011500000c20340901d80d50013182200c04015103500d021044640380d11703080a00e80e003d00b0f1140501c04213900701500f188d030650000941000501c1d066410440c0741201212f210040c3c071001d01c10144c001c0740c2d002e081d2009903a00b50030700d221404518141d0021030036036403055400303a1100c070030861100940d80180450503c5107800c050b5010000d000d44100b80000ca480e0740303142c1c00d4a030104 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 222648264 1250 222647014 222647027
    0x7030b1c050723040c0201020d0f15051012051905040302060f0c04150e0310091407080615010e03210702090108120304140a050a08190903020303042309090a020a06 72
    0x283e40c0390091600312001502004010204481030400b555028400c9240821b171501c40c01d005c0520460380420074070690f00f20750031160190b0308028800c000e030152000740e143d442013504500c06a1200f0014440d2100802c0b10490a00e04c2c03030001c1c0e01c500340300c06c03c0101580850654000c031710b03800c0f01e0400b42d200d584d10800c550007035008842c0072140e01411102540e200300b04000703510001074107580c81095109800c4c0241c9500340310a40d060343d18400040c2c144d1504007d01801092914090100c1e403c20321401c0700502d02c44500c2504100e851054650a0703174080c8108290b010129400030032010300520700b011250410802130344182413501c0001580b500c00b19241180d51060a4903c0c174694450b92606e407012402d03e070f00c801038030560f49200000348040080c004071a016024081e15007146503170890110510754422010005800410001030f2000820b990554181c40b1490346520000e03001c4440c5407011500d686e500c0b0360300c0c100740001c6031000310300c11009500030380320240d40d5030303c600c406e40c0c24 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 222649514 1250 222648264 222648299
    0x30605030d0c0804080a0c03120305070e060307210605010f080103050a080f0d06060c061a100f11030d0f18080d1505030f010b010305090c031507030b1c0507 69
    0x5801814100208500c160207442d02c0c03e10802081c0d080c2a2600015441c3c811414403c45034450240c000380188041000307808500c11440c91305000c149414003004140c4915201d01f580205400300120306210701449003050490100610f2500c010f4810a21001810141c0b041a0118000c170742210071151043e074802d81a26000b900510034099560356510803a44400200c0341c0c1201d0600002003c0ca04a000d008010b00850b51082804016818290216900c8814101d00350086004501550310781501128149a25003001120600c6e918000c4d81d40901503e407002d26800001802c0303c007540c07568000342001201d041f0800144046156105050070351503005003d100301404070f925041c5984d044034000d80c0904da140b460a80d03845010034a072a0300300b9290f55a0f81d4450f20036041d2542c0c0b5224103035114070303100000c0c080e1a15079008203441b144c140d41c00680d0100b2040010324680d00903004031301e17440c0e4058210028001a512800042141824201c030fa90103201d500191480c1400002e000 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 222650764 1250 222649514 222649519
    0x18010509090f0f071d090903070c030602040303030518150907080f030c100c1409040207080d0506190506090405130c06090e09030a090b030712020c0102070c0b0f04030f0c08030310050f01030605 85
    0x1105e00e034504000b2440380003403003001d03944001c0003031070001089260000019449200c015840e5425481c0181c02d5840060210a04461400b1030341c0090800040e840d256012002c5900100c0d2240c0201c40d04159070340e00115480d102d10124201c43c4240000100400482802681d0402c00031220080070b444100c4030980c009000721782c0740062110040020729400400600051a01c06143ea504800d90000c031108040c1c0350792181041003504000291445800d0301544c00c617a001d04000025009008400007507015990b200300080452036801c04828034140c01c10b206044640d51401e00401c1d00000d400360702000b00c180e4020484c50704000080c0c40f00b01c0d043d03445030180d890402d00d8030106908001c0080c1d0400c502441000c0d60040b9520080060850742c00c0056507a01c8141842c1205690729813102e50799100401a0a5a0b0501d00d004c1e50181c0394043c0841210203150706280b000601c09400c180e403103000000901c518101c40d6180c0780110749007501ca20441f0780110005500700c0c1c1700743c801d564 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 222652014 1250 222650764 222650807
    0x106050102120c0304080706120b01030504080a03110918071805030703030507081204030504050a060903020d02100215130201090b0922020c1006030201031103010b18010509090f0f07 80
    0x3841140b800d02a210071400a000c4070b0601d80d6801c48280ba088495210501090044e918061140014010301007030000c03c2c2002d10441c04e140e6150300f8988182551001055a1002c1140003201000c0c00c45100d401c0c01002420501d041c041610521002903412101244000750041e008170801000d480488030014090000103107507450590b217580c41140101c0344200308001c40d481d0480c4491045001d14081c0e80d440d034907641003005101c095001e0740c0000d4107000c4211000c200581c0d034803400f89145681520400c410502c4200181d140a45054010000d21050000c1000b000101000580c0d483d0003660340001240d6282104800c500c030754480243c00c07006060030790304a02d07100300c1070340001c22000c040145440d00c102c912504101701c1d0051440750075114003040003550303414091980f01d100165412403075540360010b5200580f240350400701e8158100c02c00040d0607800b4900380d42e0910b0018040748441d00d016a00d43d030b01c2c008200c4d0760003580481e81022841a5214402400b401400c0c9040c3c170 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 222653264 1250 222652014 222652033
    0x3070c051f05131707020120100e0313090c09050a0605030901050a0e0a0b041e0b01140303030105060409090203030405060417010608030c071a0c01020c1c0318120c08030108070303020606030106050102 88
    0xc40c3e4503441701d003099044c00111030100d003243d0b034042c404202c030b01d9402d405050411504c80c1c80c0c2c400e41c3c0124210100c40c1e48184026502c09980c00c040e4001c079010710030001100d10110405489400059202d540c0c4843c42c040002031244c1c0202c0214882e5000400801c00c1c2e507130380c200940448607000c889000941c0320b041c0040001c0c01485185030458041c480b1100d81790f0440402001c0c00ca070141040b01c141c01d811300100090008550f00502d00b42c801ca01650070f56042201041d445d0050384140d84159444562041c10364805208880143c4006400030395207903110342d08000444400c0b000701c00d081d8a00100001c6904011003660b01c2d87c080d1402070700d0788038a0000c0b100003044d2120546404000100411001e12809100034602c7c1031b440d50150072410018100c6202c03800c54910441d040c03504003600140d10b46c030601c001050169000b1600452a040414100c86c07541c96807400030080741e000000821744010000e82142282e00c01d508988880e40c2d000c003454280e82280c81501d015034400e0904 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 222654514 1250 222653264 222653303
    0x14010311090415050108150a0b030a032307061b0f0e060d1b0305010e1006050f0a110703030e0a060e030a140f010510211703070c051f0513 61
    0x70680082c02440380404060350035500400f2618282d02c203883c0c6610011960007650107011209a111058880c03c00501e1041c10120380c6940e1400c0300142000110350401d00090500f145c10309142094041c20780d200c40c4c40303140030401000b01d120303d507503580304001c984101188100000104051030740c0e900c070880c14007102408059002030309151001c07900c4184030350422000c500c40a214400755940401c00354503040c114600480080c104102c4d50070010301c180061a00082105c525181920a0360303600c400c018802c50380506041d9020030b00d80200316000003410303030000c076080110200703c0c0c04001d450307900c0030255214106a14000d0701604030504920104210a0b0a6484485400107a0748070042d202d000b40d01311007040310410b940c1180608280000c1015a01e2000d9507119015500324070201500c89101070100000b118040b6000040041c584034401d4480c2c4100943c000c0440c4c00c40c10488038007001d542444004584a60300c1d000000303044211140c0c0c48649a44c00c4a26002078984a0300c0c03 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 222655764 1250 222654514 222654529
    0x8010b130b0105040801111801020d0f050306040b030604030306030302010515030a0b0a0213030819030504080d0510050a0f140d120c060908030c120f06010f050705070308130914010311 81
    0x1035180c1800f506000000c0c0d800400c1c01803503100510a201d40d0b0303582d4120010f605221600c07091090456009009a0086941240000c400f0081901781142c4a030703140030025000d060719403011500741c05084180010950941c00180030303248a600244110340d9a03101d03d05122040b8031040303a055000008520104000110341c580001c08098054908501d07240c0345a400145507000b1128150002a400e09030042c0526407007503c03a07149814066402c09464a8840d8025401041c00d529503403070105040d1003001d580742c0020f1001030700c0001c2c941c0c0e4039245401d02c44075502ca10380c00446502d03070404c0c2c41e1500c0c400d84181c0303691043c034030444c00083c00400c9841016042c0215030a0741e413880401c010505002c09075120f0162004869500c1f19210b24801c4c60040c05001d1090030b203003002c00d100d160307a0000ca9032101c00e55145412a115a25030078480d240c41180d03803010b41062400a4440306100340c03403108009540441c3d8060002c60b00714107200c140118244406048034401980400181c54143d030f = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 222657014 1250 222655764 222655781
    0x20d0507150507050a090909150513120c030314060306071107090204030b06011d1c170706090201110a0803010b0912150a0f09110f03070305010e0309010908010b13 72
    0x1c0c00d0108080494200008449041d00c2120100d000442c09100300d0740c0c04200030703001c0c01e030540003801120116510000400880d452881d820354440380040e90b00c07941d040c0c8180326150013056130401c0b4020510041e0226203010fa06030002810700d250004001113001540303000c0c09003c0c0082c607680d81c078280200d61b05210300000346024080d6041c0050000004d00113000036600030410704032581410000544401c40551440c0e1448540031541010380d5035002042201c103030b9a180c480c0110070b681c580b0140c01c503200c40b464480d2180200740003040c050950701011040c0c0c401e0700d035109400b03200c1d428180d442c0400140141079032800c0005020100513200940281e00340034054044182c0100c1d010750800240e20408101504c10008001c110a1180141000e036001101c04201151060705c40e013100c3d41e034108899000e03802100b080c00c09c4d910708014000056802400800940d4504500341e80c4a62222218138000341c051900819032540610804004000003401d004054401160751000b0303116030f0 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 222658264 1250 222657014 222657023
    0x708010b0d06180c060f031b09051207030209010308040602150f010302010e130e010507031506090b0a0c050d030509060a06050306070c03030e1203010306060b030f01090902030a020409141b01020d0507 88
    0x190f545000080000554602425690300c5a4030003a10f22000102295200b03d00450382d55800c4490b1146a030b0030691440545100b13407581c01c001d014420f442403614400c0d0380000c0d00b10803243e0000050180030000381041e603a2550030340301200c0e0a4101d040340c2c08800e03204900c1d002c8104004200540c050b0f01c02e0030001030050a01c02454a800c00c0c0d40040b82c10a2096910340d0f51140c1c100f249003a4507200380340c90030020040c41d040d4981080710081001c2c83c03a0003100c910040008806406500403c044540c00d41d0040454000c508005401400340106582e54502c9200e009c01050b10b10710f0900480d000d0751006001481659514241220f5484a640c01074041c5030303555848146ca000300303000c000720700c003c13600510b50b60b54914078180d421100c140d03001c1c180b1900d0501c1441550281100050304580001001250341041030001034100942140003d502a00c1c04e030f0800108241e0b425a640c00910400aaa00c1d02c0b00b42c06d101054140c07420801801070b00103201044a840c040c4c0301510303105004 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 222659514 1250 222658264 222658301
    0x150c0c0e04060f0e2d0d1409030a0f0620030c0d092001080109090506010b0304030e03100506010806030c030c0103020a121503050601081612060905011d0708010b0d06 73
    0x18000e81c0000c0303400c4600010300e13035048020021000002c240588020300101403513001da0401002a00c1d46520350400c2100400128007074041407030344020251001c80000800350780004181c0e1800c810f2414801c54205c0e201800c1803034407410001030481100522404415003869652012903640182d031104810401d91680e40a00340003151035028240c110350780700502107101c04503d400241503410141d002071000e50a15940310700090001c946541101e20300c03105207440703445a1500303460540c01c10301c00540500c1001c07a01e00c0d4001454010074080e110a8a40f00745588504007415210003d40300f5140d0143e00c0050a54107951207030b0b00606074184940ba00742c4d121040340c1c5d03002003524140140b4511607800d5080034024804113120311401405440c0041428504030394070003400d408141f08034505082c802d0300e031600344625900580711a641c07000c0200702c079201130002000f125001100d000c035503100340200071444070741c14070a000c0550f0004084212002d0a41d560b42d000d056061001c0b400c41c440b = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 222660764 1250 222659514 222659531
    0xc0d14070f0203190804080f0c0f010f021002070305090405060d03080105060a0e0406030605270619090602030f011a041404090204021318051003110103090c0816150c0c0e0406 77
    0x40c40118888085c854854281e4641c0780442461034482818115100e64120139114003441d640d880307111408980030301b0070303809411845109900700418441c0c2e95403d0760001401d4810198020014030b125041140c0070403540d03d0303900501c022029150070040104a0500060000780342c210058002000c052030400e843c124020041020348040b940121703085911841800b4054800d1000603562041c520b907440c040801c0030504a5441001520441180d40089850300720b41589803c80410540c00200039542c80c1029082149401c500b4071a80c2e01c08002035200303040061007a0b00b12002c49480c0010800c80388807601c10000180342d88131040740c1c010303030130403902144c0d00b801f420707140040c42d101160700c0840c0d4040c480d501c19188020103a04500069000900000c0c0a110403c17550180038600082c1d008440e141c0880c001c074ac141c02212051050f40158120800b040d41c00506076030751401c4004400400710801d840c81e13070744114001c03c080c061078400d000c2558400c50540e4050300984c400300e60a103 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 222661870 1106 222660764 222660793
    0x105010e060d140a0804060c110102060c09040e07030f0507060e040b01050d0510031e06060f0608061903150204050915010212070f02060f0c0d14070f0203 68
    0x4580f1241c3c83c0744800200800203005a1150000c1d070384544070a0082c010305d40c034140454100c00543d240050951000c1122400740342c400f14514102100f4404101c00b400c5034840784840d5100d00000000450395804c8030640701030161025059540c24040003c2c4000e840450743d501580c2802e8941719980d9021046482522510100050f261551900001900d003654009400264402c214951070b411408451503098030030031042004641d82c1d08454043c91b03280c4a081e021690900018030715081c005c0d0b5078414150445c002c1072003582c8994407120785500c101c1906d410340c0e50104042c001130034a4400150001c100381c01c404111121500001c0d520f2450b00d0303101c0f818443c081560420002c99103046520140e0041c40c0a0300c85c0e04060540c01d164018501c01c251920425451800300c5000d800400000460304451503c3d0141039159484241b1400004980500c5031100c0445d070358 = true := by decide +kernel

theorem cover : BRFrame.Cov 222482014 222661870 := by
  have h0 := BRFrame.cov_init 222482014
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222482014 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222482014 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222482014 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222482014 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222482014 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222482014 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222482014 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222482014 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222482014 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222482014 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222482014 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222482014 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222482014 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222482014 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222482014 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222482014 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222482014 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222482014 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222482014 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222482014 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222482014 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222482014 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222482014 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222482014 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222482014 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222482014 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222482014 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222482014 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222482014 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222482014 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222482014 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222482014 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222482014 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222482014 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222482014 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222482014 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222482014 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222482014 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222482014 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222482014 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222482014 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222482014 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222482014 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222482014 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222482014 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222482014 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222482014 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222482014 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222482014 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222482014 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222482014 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222482014 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222482014 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222482014 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222482014 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222482014 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222482014 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222482014 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222482014 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222482014 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222482014 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222482014 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222482014 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222482014 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222482014 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222482014 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222482014 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222482014 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222482014 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222482014 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222482014 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222482014 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222482014 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222482014 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222482014 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222482014 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222482014 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222482014 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222482014 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222482014 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222482014 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222482014 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222482014 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222482014 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222482014 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222482014 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222482014 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222482014 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222482014 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222482014 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222482014 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222482014 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222482014 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222482014 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222482014 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222482014 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222482014 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222482014 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222482014 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222482014 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222482014 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222482014 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222482014 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222482014 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222482014 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222482014 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222482014 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222482014 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222482014 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222482014 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222482014 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222482014 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222482014 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222482014 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222482014 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222482014 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222482014 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222482014 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222482014 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222482014 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222482014 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222482014 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222482014 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222482014 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222482014 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222482014 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222482014 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222482014 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222482014 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222482014 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222482014 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222482014 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222482014 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222482014 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222482014 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222482014 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222482014 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222482014 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222482014 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222482014 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222482014 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222482014 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222482014 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 222482014 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 222482014 ≤ n) (h2 : n < 222661870) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
