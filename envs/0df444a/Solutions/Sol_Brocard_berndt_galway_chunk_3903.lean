-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3903
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T11:00:32.899495+00:00
-- url     : https://prove2.me/submissions/c316b7a8-d625-4322-a9e0-7178bf8bf112

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 701798561 ≤ n < 701978417 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 701799811 1250 701798561 701798639
    0x31050708190f0311030d020a02010b01031419020d0b03060f091009020f090703200c0705030123090f0d050c1c081504020708040b0901140f0412050a0606 67
    0x18071401007194403200219000a40203003054400e0054800540b42403445a2400d44100e03004210b1130700060f915485594500e503018400c404143c1c00519401840c1c0c5002c01680030410707581090b0300754080d800200c165000420381c3c010001d20400070b0580350345003070094403903d94040550f0090300074025030100c118074854a00c20b5050f0660302030401c0c05a5100715080001e170a6005010750309060301c3d1050030710072100c1d80100c3c0c040804031030304140d110080707419290300d0030050750401c030b00030307850000100c0b040002c103035813402c0300440f80072002c07119511005410b00f0212081640181480380400601003203410001a212981c00b1008607001c52141401119201c00310303007510302c040350309030000c10315054903104080d4540e00041d10143c070784603641d071791007600b644664008010300b0300100d4840e20b69a4400030382d9218a0b540d818040c1041c15840d50180305108501c02c8111a030b0061202d4070400800788040040e058000c0820054680d83d0550031025001100ca412800d00001e03020b0448880 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 701801061 1250 701799811 701799853
    0x80604030f0f020f0a030818070b0316111902150304021302160f050607080105150f070204181b06020109200312190801060309050631050708 62
    0xa01a0345500445203540c10594444040489000450003456080340c8020000c2205d00d4000c3c2c0b00740d54000e5107141c080c0c40182e45088074504014181c00a071741c01c000c4c4400003030031f498000e1140f400c0c050161811007015190540c40003030308669030103800c07100c80600c03074a204800038150007503e074441200000000003500b484120b4000b0f40c4010001214000d40586a010b003088105040004141440740d440d50008140170420841e400d80c4070f1010000303440e03440000700d80105015203000741c41088800303520700d184c0030b02e1643d10130000f0f01140d040290f54442c0c102001c07070002c100d02104418603d050400300c8a541020072100d4210040c0c000034124814420003c8160f006809420440d10814402c0008661941156458441d0020020000e00c1c56401011004004120f40d1100740103050080c00386041680305405252400ca0300c4808100d0120b107d07984a4918484603001032a45504d030034400c00e02d0741e0b01012810410701c4178000c1190000d00d0300117071366a8500b100c16813041000c0720b2400301 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 701802311 1250 701801061 701801063
    0x221100f050d06050a0e07090504061409120310170c09072303151f0206100b04030b0601030608030c0304051815130209100e0f04110313020102030c01020f040f080604 73
    0x203140c241d060003c00c01c180d10050300130080c0ca00c042a80d0000ca600c651404403241c0001c041aa9a4414002001014410600144040c0001c10098908800b003184ca03504c9424000c4414030002001030f8582081c02c0c4050040c0542102e403010441403400c000b1f5440750030200d0580510a276002003140c0394000c0005188129102c50716140b10a50783e0f030118296080502030900001d90131000c90580e950b29221101302601403d9050355441c1101c40003031421001400700b014000650f08140f080c1d005c01c030100c0c0c05503500a000ca141c151035100c01240201490b81c015981030101080c080048003010004008030b40b01164040c000c044090030000100c00c0c140d03160b401858107181c100e0001e00703080001c1c8507402141c0314014100016240840c44d2940c0011210300090443c0c1d038490968074005e06070039091b50050318100812184440102010f210280020211010301c1c120041168420011903c0c1024540000d54a88501c1c00004000350007900600719080c01c045000b003140040001d04510503 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 701803561 1250 701802311 701802319
    0x40e070809101a04090b09060f0c12090a0c0305030c070b09060a0e0d1a0a181208090c030a060c09061404090b0402091c021005071a0a0221100f05 64
    0x307500050b519100510303a8541004220081212074011580d40d48150000e0900403448003519141400805081c464010503441284840ba401c6c043d00c20200b001390380b031b80100080d03102c02c0c40d01c2c0c0181151804207002001030170361744200000320401401001818120b00c001d0125420706449000c408001d019403a83c1c190441402e101d010700d2540b14201d4541d4000700a400407840c00d80a49078038079031a584001c0d00510714012002d104890b00544180207590320002c1445502c10b03095603500507400c4051018400b00101c4ea008074146c00414090f5588004000301140c5600c25a4a80b6101414428003908013003a40300c0380c00103000e401680d04141c0f072128441b11504d0f043c00c001c01c00e00104004000f07650881da0030701c01d241290b11030308010540d4016401452014141502c10442e0710041e100649042010501184000a95089504185022041014015941e072100d804c00a01903c0e02c180245440c00244c607085801440e1014080c000381150160780c942c8176202803603521028483e441d00 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 701804811 1250 701803561 701803573
    0x71b060e13050a110309010c08070302040320030123040b070f08040b0c0f040321051903020c031207090608010b0f030f0402210102090a05090f0105060c0120040e070809 74
    0x21641c00d503102d25480707002d00030001a00848504900c04a820450b44001c2580d510070300034010300d4020b5031003030b4440394520f0103600c0c060460384e8105514956000002c400303810050112960f64013900958000c00307108a0a07107103862020b400c0c41040d84180d4051380c01e540d2040210742014030500101046600603200c24038103483d156601c1035040c100a103d46034410f010701608030001c02507002000110300035441c05c400300c40240c1040690300c0f00c5103007040c1408030401a1041e41c1a0104034440d100815007001a10b44c800c4800f0130b42144541078100d4100244901000303070300c60300001345c00305941156540703c00c0741c0c3e2114803448880c031958a42807081801480024110807000b1151903009201510703c841d480180c060b08484a042084c40c5c034007694010402d003401742029020318000302001c0390f4020340c41c18a40c0088114004c1801003a0250b680013904041c1100250040103503c295001100311603031070210712016941107401410303800d005400204103041c0c03007080c050307002f845024080d0403 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 701806061 1250 701804811 701804839
    0x609010509070804110a090603060f0b280302060c01062c1b0904050403120e0118030311160506061c02010207060f090306180519050303010506070c0308071b060e 71
    0x403e20b00080040790b42006040c038810058548804a20060020001c04100d0508610b071078000e907000c0c00900070f5400c0c6800d00315441561015804041500860700035604e0591810940403030541d5500065080600050005142601503101c03d00300d424040d80000c61100e001003904241000d000041141c0200e40c0110361840b0030140c0248886ca40e03010190b18244403000410140c4108035015404502400107440540029004d104003143c000702c020800080401e01440d45104202005000c2690369816480245a00070131518a03010440055242140a00d07107140d4511040320303428050205c02c00e5040300c0c10500f003052108594160040e120044c06c001c030403030b440807540c01c07000c003080124000000814110b10070101d4100c1034030005040c0c01c0550500500c0c242d040080f4000000c58000031001240d070200559041d6081107405c0c9a45840c0d6040c07030491055242c00c050f1000b00b00042e032340700704840020361010300841040c5201d415903907031034191031002c2002042d82e0000510105c42e1 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 701807311 1250 701806061 701806067
    0x803070b010b16063902070e060a03020d1202010c0903120e040f0c1d030304150c06020f0406030f060b0a020304210614010611030301050a03020607050f1f05060901050907 75
    0x3d804010804011015035940b1101c0c01d554000d120304a10207901c2614001300c031031951141d00e801440980000d904170790600c000755603288901c65100340032503c001140c41a501d403990714008640041615000304001e08144640c10704103903080e8055881d01c900340151500500524040329042141c00295155036078065510f00c004e007178010360050340d0300c03004508030069218150011000b036036440607620b030780c944080e6840182422280300798001c2c00704008003407d034051429504d0091810003c03512aa14016010707006205076002030030400315012562031341c580c1c8240000310800c50306008040c1d0303c00c5040c001d40301d44c104240040c0c1042200b03124400d2001c014641684c5094110910140a515658115104c00381050f41081b4004010841e8907800206404800c0c1910091851035140c000002d00880301840b0090280d50301240c02c00610000b809045070418803807080c3c4404254410402c0940600b40100d010400c1c40c01c004202941420b0007a1070503240c015201160a4446403000c0e = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 701808561 1250 701807311 701807317
    0xe010c0b0702011d07050a09020f04030f08040803190305070e01080112111804050f0102031e130b01080d03202b060305060a0e010905150c1308160803070b010b 70
    0x100080d59201c04d01460814980e000c8a100d1150a0016043c01420842001000c0b00c584d4004d034002401800b0b48803d08081808031000c0320380c8030340c3c80c4900340610700d010102c5001e540c2c03250403103010104801ca100d03940c0c1c02d060103415403280c0e4100050f80d0703849000d969400c61910724500058460005218a034800c8140302c180600980062100d45010000500343c40e079004c5005a0303811601051000b00441080f0700c0d804680f50900030750551a1805040940c5040d00342d9010007000100041040d82c4440c86c401c0d0482c9420029072070030f568640700c0d10341e40c494620410000003440d041902c1c0e008001450100f002900c20ba0550b0b14080748002041c2c0c40360382c9200d0401ca003a410001211b0000d020344183d900640c0b117080070303000500d00301e88100c0c12291641890041070f4140017200002640208400d00c071440450013458450b00d4006282c0198014820207046110007407401040350b0307800040c0b410703051500f80101d08013244c40e402100d03281d000b0254010b102c0390390080140301c1c4132144006 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 701809811 1250 701808561 701808571
    0x3130906210311011116110a120f02011106040b0118020703051903110a021518060a0c02070510050d1b021e0c0a09050402031002040510031d03070507150e010c0b 71
    0x401c940004017038810580c2e0281d4070764285031b02d01c0381d860000c1219100f4000d0110754106c9103000720724500302120303c5505803501c00030b10107840e200d070714421a8000d69a003c080c0c88100121a5280380078900346c080030000b0f0141462091440303004601c009081e0084034007460741942c4040c10304a100e285e4840c1e0880460340102032603121545032001c006080e001c2d00e0b00e014183d009015004045680c002d08400140045612115403214250718002c0000c0190300a9000040001c0786008140124103204080d00001c1d44655031010000001c2d600174040c0c001c1e01d10600c004c100e002071744002401074455204d03101d000346e00100c40300c2500414603600080d4001ca01030540f05154406000150210030b6034000402e4a581d907414842541010007020000c180300340811032609003403000061428415082c403204064462100401e100786821444c030452440008030303034450105141072900c40c41c55006400440c0c0303400c2100c03011240308000e103030019041a1900880246581c80d001301035030f80201 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 701811061 1250 701809811 701809813
    0x60a12110705240c04061b11090115020606061602130609110415080408180303090a09020a081b0304060e0102160606050a0506071505130503130906210311 68
    0x10298010603420300046480800801043d04030031003c40030b040084402810700c0111280a00c03040c041a900b0404800b511610420140e81c00c440074500082c7d1901d40707a0703c1c5a048407128000155004800c80c0c00d5a4008140c0c09450850799031109011f4140565220088810311480f82040503042c4a005104491820040450b6268403150b0840c182e8000450a03c0c0000000408109440c103200f14403c2000303152030403603180e05181c2c0f6400618040d43e40014191180c0380107801d203580e0104105c5100c448041e041c030900c2d503030703489508009420146803000410740301c100003144c0d40022980c6202c6440c404594078215216512000014080307200c1480c007a41d0f0030016103002280651040c06400c0c480c080101d290750070300e8188140c070243c5510880c06802c0c10b10005000a1800b165003c3d10b0b11b17085e00c0000c2e44d40d28145100d0100c560300201404a010003d500d0011290030001103003680e00051052204036511100068554a2980c1c3d605a2202c41211940040c0c892a41c64508030340d008 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 701812311 1250 701811061 701811067
    0xf0d020406080609061002060f1504150504060e0f010605181801061101020c0303010b071e032c03061314030a0504080106060503010819031205010b03090705060a1211 73
    0x140000040364459000a000310740c8090403c50b8030300c0c1a405443d8803107000e4411b1a005400003d0203551080090400540c885904001510b104600b54072a892804003d100384000c1c003400b81283d10b0040940100c40c004c0d07042c140f01044854a6158080c0106c1c0c0e0f05400f81040da203004411034681c1c02954206003101d805038101c40c03140c1e80302c50100f050012018641166545040710207864944400640b03000b69006004411710801d0120559045900425210b40c2e100c50900d0301b0001140842c01800715200001c900744107160f0303c290b400aa00e03400a0703159a95105000d448002c120301c6548040d072503030024000800c6100681d400b01c0b4100d106505240c103003001c0c40d21841c00d40c2c00103060308002400c085010410f50101b401800000d0116044c0a031565040c517901ea500c440104422400c01402c1c50002001c241c480c51106160f04101c8a08001c0c6503101d07000610143d0040c1d5080035184104000401c1c1072a200048070702411701503c81868120504000101520005d03c0303402ca495018 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 701813561 1250 701812311 701812327
    0x509040507110d020f0c01050309011401150e0105121504090b01060c030e0a03021518060a050a12140117100f020307020610030210031e15081b0d02060f 67
    0xa005030341c05400e040d241c01082039100c1480c9072400c030815a214045501c400c04110f00c4400c0030485000c055820701e8010341d02e03582c3c0d540543c050513417100030b07030f0022050400004031100d050440f00c92420442e920b2150a80156004540d94065030001160080341c240c0401c090440c2c008070080f00c1030003d000400c00d606591034401003504240d1016010038040c040e0002055840800e003110100e04458148641e070458021854107580c0c10002c500c007103c0014032154101c100c640312108440010482c0340d5825481c10000c1850700560104000f152071145030400700d44580c0242002d0f041b5035a0198042e070729121407035200c82203a0308070721024010182c14025800f4a4052419101c141c0740e00983c0c0c2c0d080105d0001c0c500080145010442d43d01180d0620040e07407090340c82140f8112602c1e022440001070ac010404048243c0304481c800c038078100c5035001c1d03000e4007840202120450340586100c3c1032075940030559081c0900009512001c50389510707006241c9400900004170099803058100350794 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 701814811 1250 701813561 701813569
    0xa091505011b050a2301020301030f2a0807030b0a0203090a020f060f0d06030b0106020718052701050108010608120d020705071802040806060f100e01021c0305060f0d0f0b04030509 79
    0x907040107031110317081d25500c40050403000000f80300709003210000f1840c40d0b245441d0f40f440300c01a400002c01c24080c090604800c03107400b040d045031110050101240195072410301c281c7e80d00a901c41101c0004100c000203042c203d551013070b41d10410410014188151041c2d08201a0502c804411070b40804e00b07024207041d482024000d03105110075108009811170550800180d0b004050344034601b10351240505110311810a80f003008005207038203001c9207035260342005c0340c2680c40140c441004810613100300b00803400150442e60403940b10340020810a0313254090140c1b83d4040b0b40c2421100316041092096141041e8010174180f409402902e000fa44c0302c4c44080040101e8821103200c07140c0100b400c0c05404010f205c030640000b0201c0704401ca03a4042404a962854403800900030320042d03c0c0d111080e64024030034000c251143d0501800c1450b01c80001500800055070710702e01a0341d9401d03680c20b041c1025900c080c0707400d400010f41e09000126517119071713002c030b4010021001c0010500902c030060321 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 701816061 1250 701814811 701814823
    0x80709051804051606090906090b0625060221090d0e060c0c06030702031e1c0213050603090d18060801030b1021050d0e0f0d020117150a091505011b05 66
    0x5c03a40e9901c1226140c40c100c01c090b524240c0140c10100e14200ea054240d0340c030481103072001c501481b2014041180c010904060700c01c10203015204a0002660610110b9841d141c420849504c86039580c203500d42541095031590703440d0f103960105480701c600042602d42100a452600f2960044818214101d004035049410a40c0c060300076070700108800705041300c220032142820002026007800c000c130003032000c100c1d1108590b10040c0359a0000c0e038860241601001a0041d10001d80550754074140203072407170303540c0c40c01d07070b0800c000280d005030002070408043e1020011500a40d0712040aa400d60b00d408400c920060b20a00302040c61010000700c2441a00c6500c80c0c0560700030800110756802d0800c5400d1200089405041004924502d03100340d80755200329410620a481400c120b10312440144d4007040d0070042c2080100c14581004451240e03a601511600300544000f00701d5541d030200401a00c0c91707207640b41d4025400d95828000c5520805009099170000040e0210308906a251903040c52 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 701817311 1250 701816061 701816069
    0xc1422061e020105060102060105040b03030c0d090f1a0702040e070810050417090d06180602072d080703030c1407110906120a1e020307090605010807090518040516 72
    0x6101c6038440558104601441d403010035450000340300a280c00e4000035207408050155510960360346150b0505070301c080050f9400064480f080300d42d40340720741c0b1000c1c0c00401d0b40d108100306c0e450701001c0480d0300c3d10540c415004844030801c4080c20040503501b080050f1503546028903007071080c1600003e0f0a03004012442d482100c2c8640050783d420107003402c42554000b000b0402c01040b0403c40548551140181c40c0071058014400162101c000585101c00200ca41405450b10340082508401d003c54a4000784d02d0050b800c0c0144040503410b18486801c207003021024162410a0110300c010900a4003c0d42880d4060300c4c2103807070500072401080740c642182c07106682c520044000b5285c0c60920101d4160015002c5802c0b40c1d400c0081c010441e9140b0f81050001c04400c052000c6455907081c03a07081c44406a4002d0a43d001c01e501c4124440041c4224800c0c02c1c000f500210203e40c2c260300903a001000e6070809054201402c400d0030700000002c00142c02220b080c45200d480c02980c3e503e4443d03040184c = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 701818561 1250 701817311 701817317
    0x402150307050a18030305120411060c15013003030902120607030c08010503072304110a030501090b0d02010e01140c010e061b03010501120b040f06180c142206 70
    0x6684000c80140a0136140c5003881c3c0d04081c1c82d4040c40840e401030240c6507007070b06841003a8010350340ca141c840d020008416510360803aa010468800414005c24101c0e464201204240000e82c2d0303031020320207a51f4200a1103401601c000e07040c020072401c1c02030903005a0340681008a440203031a40804d800308a2800c0859072900908144407040358903018506102503545016a91541801d00103500da419130b100f407a410292f4501720300200c1500520003c0917880040c4200110083c00085112030f903c006052400a4034103400421010300c54451941c90b000c02403c0600920300a900641d81290032084080c14404403000f40075100c12480b00a0421600f1a0000b00e501c0542400d46460030314090700e0b800b00400300c9032840c2401840e0900381e9044603401d1810341000d80c210904180103154028013150410305000341c3c540301400b181c10a100b11045802e030b07108481c844c041c0c4101101c074001030060014009105540e900e08100020b0603100d0070550341d00300480006c0d8846103414116501203804 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 701819811 1250 701818561 701818567
    0xf030c070f0c0902030901050a09050c13060f090203180a0c090c030216050c010f030b06030a110d14060906010c11040b0609040609050915070f1803080c1b03031201090203040215030705 81
    0x1050400b801110f80024049c581442001c1c080c1ea95a03440d442c0d2465514000c82034482e00f140c0400d0b15410450041c01c1801c2c4e0000c000f03071280c0251001e0350044078800c417602c41c48080906160310008020b04820f4100b1118100076080040400140c50720b00114001c02da0203002580d160018802042151f510440040074904034140002d00401000d8101500b41803a2103c92201d0fa120203003220360003100180002500324105181d102c0714000d5004403416585002e5840bc3d410a3b80041180161000c49583c02999140001112155107850004003a5038162580640b80e0425402c10030220600401c02410a007010011400f1a41c582c0d0202d1840d503190800d0100c11281880040555a6040c03030b1210305191403100600200001c081110410103440240c1c0d0001000080440203154080032155030746441c07400c0941d030350307280c5844203080407524031010503070745400412541c10350744840011440380e00e00044040290002842680c210805010b880c145010b107400443c40744003c4d40300d00f61 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 701821061 1250 701819811 701819821
    0x807031d191a1218031902010903020c060a0f08090c030102070c03120315120204151d01050a080705060306120d08070e061c0f0e1914030f030c070f0c090203 69
    0x1450740c0310319041c582c103070010006214071a02040319158000304070f4074900010b52600da4820301c0c1d44100c940c80c00c111031101e00003103500340c0c2c113400034403490307009500300d070350411000f820000309114040c80c10010074054080ca8003200c1c014070070700341e20560b80c50541da84418441c0100382a68072101044404172a1202c00f8820420607082c0441186154a000c01440b080d01c184041004041d004107203405803480da02104655940d00081044012182515103e031b1360390008410b206c1d031030601c000c002d0307401c14004601e070f041c9880250b045070302c4000140103061421091006a6102409007900140b2103650400d904030b0401111444803825a0381d000c031440e0095009140000c483e050500c40c403c01c01000d0b460021341030043c52643d100000010b0001c9000240c072000300040b424040c0a401500300d1024402c1c454121044114002c201d49030340710803042125510381c801d2030b8807030100340350506c0030400e0b02e44408007401001341700711200c42203641680c440901c04000d9074031102003d42c0001c1081 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 701822311 1250 701821061 701821079
    0x403150f020a0c11361f120f0c0b04090b030f03030711030d060e090615010f0311070c0e27060403050a0c0602040f0f090506030a0b1e15010f0c0807031d19 68
    0x40d44846c104c0c0d158410820b090350304001030042881041c0c003086003c2c00e42c0301804400c640c0c0c2946036a2050049000503920404449240c101384242d8176440d2500480480c142404110240344c0084200518616903900109595102c0c500c1002d520341e01c4240405540d2080e0b501c40e02c00a0411200c107100d13145003000c0303d9803030400000c0c021009103042403580081644c20a00c403d1501900781400b144084000e0300e000502d00582da800b6110007450180011800c06200b00d07507008500c00d02c079416040701940d10001040390300c034001c00d8141d0f0141000a002c684102c0c0a0203115210f850b14040c3c2c0700381034407003c00fa42c00903003204201c940704000c01c0158a2110140034000c024140c4240003500c0c11000190302d49a5000c80501410380c0000084c0740840d00e00c0f01401c0a80b12140c020f100b40c2000806055071907002034855022803036441c40003048070b00660004c0e12566104081c149469440e031340031101c1c1d10160150001c4450600c810701e4455a440200198000c41d030b803550342e00c65103408505 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 701823561 1250 701822311 701822419
    0x160212031605100c02031c02030606070501090c08160503061b070813050f01110309090601110f030304021e130c02011b210b03190f05030403150f020a0c11 68
    0x120191b52081100b003d10140c081c01c40c0410118814005860341d56600200d8280e2040801c001c10350351034540d0a0b0200001b41182742c050312a10703012104120311016031080010703142d00a03550315910410001c0c11104140d80201c44491031902e10314105100741c0e94a8101c0c4d0403120031452156000d0109102030300b0229400c0441c510246880280703050920f145a86910425489034015441140000c07100d0b40130b180003400202d280400c464407090b580c2040d6489030820344040303108040c0001222280d100d004001351000c1401811019040e020101e10401030146141c5a000d6549500541640460301301d21003602c09683e488280e1400c094040690501e0034034124801074034940030400205440010b081c000c0c000c51710301199054002c1e8103083e00c64800156000b4035038400060701008120f80c125017543c00d4002c000701030041c10058402c0c0003d1b2300421880344005a0038080f044080ba4064404050381607018004d000402c000d0b403690825030031079515001a0141e1001d059034094000941 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 701824811 1250 701823561 701823581
    0xe370509250e130509070b0a0504051302040506160c241106100b0a0203040f0b0c0d081303080a14010306151205060103080a0203120415050a0216021203160510 70
    0x441911682c2000940580e5070340c05410b070542d0b640c10005210f02d00410594010342000d0080544490720810002c100e40c0c4580074050084403600903030001102d03613000750340c19568010f00e0b00f402d00318074034800400c1614202c002d845121540b207002450420704004500c0460b22141034800070781041d0400350140014429805082d0303c40420010740038103c0c45040244e51100311417966481c000b0400b01c0c514002d50304071800f12000c015000030403611203002045814075110503510016a954000d81e10074100f11503003a61140ca400d04800000c1c42003031011b60040b258040056682501003420b082079400340c2086443c15a108490001c905000c14280014940366412a84c00042540c8160321290103106c02004104049001c0c3c600701d00030310030380e45960b03e01d52260301d140c40d00c0e0416805880d2000c5801a100d03107420003003100d28243d402281e0308560113004107201c0300710907406c0c00001000c04090381d0701c0340020300c42840c1000c07800b8102c801c06801000142000c50548013004115641005 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 701826061 1250 701824811 701824817
    0x290a1514131d1e060d06140930030c190804031b08092b05100609020f180102030405040614120303090a110a170105070e37050925 57
    0x2040018004410803c5500c0c1403262490801c82d840d80404104107000d9224002c00c03582c02d00e401d41825101c0745001c2ca20a030b45140440324150a040c10428154410054494116a140b4500c1d050302200500545e088000314076280c0c6842003924100c2c40700c420060b41c3d0000620004244030074594040545039a0010450740da181c2c100e499aa0154030b403080e00743c6c06002c0c1120b40591514400a4050b001a02002c0410a2620007203840e06a072075048030186095143d1070602c1c08030f0058984d02c01e56950320462502036290901c42d079040902c0449808a16046100c208804901d94445000d00c2000780a04420a031154201d882001210300d58a0002a0300e40e10a0040103004400056291303c510b030003082c0071017081895004104040e4254000b99044001500101c03424141503003da8402c1da600e643b01e02910265104210000c0b0034050170308900a460112100ca003d0b18084000000414071344002c603942d0b40b40c1c08144100b6084620348250300802d180f14854544c06281c41390614884d107 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 701827311 1250 701826061 701826119
    0x17070f080a0b0616020604030804120303050a061d040f170703140f1608121305061305060a020c150403021c0201090305030f090109050a06290a151413 66
    0x80049080c0e030240350b8025044c0e01c42c002c1c129080d9128034046601860300281080e80e0703543c846d010700c207016984200440009150074001800c00345c0074130611050f21040b088000f504600386d0b0614003a507501400548184903e10340d8100044d40401616107581c1034059080e4460b0468140502540041000c0c101d040c44108a9000c51840350403c40301000f03080844c05e00d8040e02801c1040290280000c01d442c41c0e00508184807140c145880c80312007070751181d02200c0b66542c0d0b81c44c8010242d032340480020415032010010910351400d83c0c002c0d00610302c9840864001041c40800c3d10303500203003528240c0260700514800d016a08403411030040105180c0020300403150a540c0007403040c400281040c0c2140740b048003140e245800ac1d04402000340d000021a0344103491410301c40d000b4000190002e4541c1c8001d4444140d03030290711450b818510008081604e56450060030346004580c03004030500b0401f4060f80480318103115000703003880401c0d2190006015042c600300003600d04c0401034030748118000c0 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 701828561 1250 701827311 701827331
    0x100f080304060309050708060f0105090105030114010b18270f07020d0e041b0801050306060337020d0803071b05030d0c0306212108150117070f080a 65
    0x1210201c802d5442d00141049690403c030b820041d16801c030040e0b50003900700b444068200c44000078103817407044400740c42599036801010300301c4401e95000c101c42020307030004001041000000d441a0b00c980421808a25501e6000400c01d41d004000802d0142d2010100c80011108446150340f00c10b4404401c0700c103081884020b9581e59920410b1010891048011400c070386603900100098134404600c601c6144041c00d024144610034041c190286c4510b80001d50140b50004244903480c03088944a44000b240010341d00c40b0701c001184400e00039400661480060b00c4215141c0200303401182550b1316401d050000400e107001850280ea00b01505400401c0407403400b000300c0e5491080030000240d0030888400641c003911466100c0f0b880c3c4c42400f13607848040102000316440c00d51080d030141401ca00c81c00031010702d0b0101c51260400003405c207000115910951601c03552000014140314615001e00e18060740418422201e210000c0c003000202c01e04150000c507035540289015101f40049694 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 701829811 1250 701828561 701828563
    0x103091e06150b09030d0206131b0b030f040b01060804020604290a030c030e0d170403020a080a0908010b09060310110c011b17090601090209041e05100f08 68
    0x3028602035940810415100e0801c0345503403142c02e0b600005072410b4042076540d00114456044088114000c2c010507016403d01440418842d00c2081030320500c0310101c0c2c0c15100ca8080486100c0c12100325001e039a000300341002d24501861265004040c5000d0700c1c500b03442c100311402c00c1039002c3e40510041d04140001a6a4076080e03d065a003818155060039526021802940380142501a0700c82800500c8250140c0c2c1a0080701d03c0d00d0403500c082c030490b42e0391078006a880e03220001e440b0025400c030030f0403041940f4001246800174001c2c8100c0d03030b012605440e030300c9403644104040f8002c5400c1000070010a6001e0040003520041211565a03d1800c1c10200e9200c008040d00c0d107802e140d43e500c038000540c0c01103054030034200d180d100030084505480d0004804450b510154000300d03407400c1c00400090008002d0030320034001e0308040c080756441c0c1041c103400707034119a00f40c0d540580c807031a5400e04500280d0f440100705400030b8001c03540741030801c1c80141542d1700d270700702699400841100b0300c20564 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 701831061 1250 701829811 701829833
    0x1805100c0620130806060604090e030409020a0302030114010309110609030f0f07090b1207120f02090406150902072312030108010e071d07030b011101110711010309 72
    0x15500306040e8440c681c0c03510380020400c03445440c4001003080b1940701c007180900094000341c0420800c0c81449515040441c0c0c0d00e40c41151400d034400001c02c0113100c045001d42081a03806854030860781020703141c1d40404260381103544140c001a0740400104103422062008071034840c42801c0c1000002000e4649039404002c0328062800740ea40010604001d13101040090b41025981040c0c9000c0d0440400c415143d40703051203092181d070f00340400150185403400200e03500040b100000c0c461035103468105148880440003e48604c1300c80d21418004d62141c0485a00c074600c510400554912035201085119202d90820148544107001083c000781d10144510f1001810024250301c141e400c442e03151520202c0d0089071900000840002a060015085400180e0b04402540c00307058844400407581d01100c0b030300513152003aa1020800703c5e4001ea005a0340007006140000c0040c4184a0050a4a140d214107142000c0c00080301c1041c0004000302c202d90a1013460240504007150f03e84030301c250 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 701832311 1250 701831061 701831089
    0x80c10031e0b0f040608100e162306030a150e130b09030408010216050606031504030e0f060c0d0305060409110108070302090d0b010302010f0816050715050108060105011805 76
    0x180e540e25448030b0307aa450640c802045500104107111603900c8040198484800b1031070a2051070402c00807503c002004200c0030780a0100580880b003152810300c484150100c41d40e0351a41013642004010000d8a4240c0207600c604903011020607a44400061a0740d5245154080c1215202131000e000d0340700682c01806540c69084200c0765155180e40c04c10a05511507640921020b40c80026841c810803100017403003c00ca4084d03402d5842554401d0240b6468840b03000c03000d01006408000540042d00441e10000c0340070002d8601d48050503003c0201c0d034113030300030505c007001548243c4580610760703070502507250310000c1610244200e48256880c61080f10b0680482414070201340f00003440c461295065840b0114000c181d415080c40b28180303c261040b081c00306138006652811428056402540706500461039110f000485004003101100c5542040714101d84c4510241b2609040c10030038011315010300b007214050515940f418002500c0300c400380c0d0b111080c1d01c42500080209540c5d01d11703441d00c44 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 701833561 1250 701832311 701832371
    0x3030106050c071d090709060b120a140403030615020309060702100c0605131a1302090709050a03060506270708070e030f0c0f1c0807031107080c1003 66
    0x51440c6600d8241088100c1d04080c44220052900c04200000721040f14015a44003041e503030714035211040c40094071600d0140d2140c004080080030f0000d40c07103c0e2b02c6d60b800702d02e40c80c000442152040203504200000d45003078000075140c207810300090450041c1003c4601c440d00065181100c0040412240d000f9071002a02c1600c05c40c0d915500e10f4010215102c119500c40c0c07041000d45055108040310f18001c1c1820340b540d4140c80f800c0308a50fa40903030500d008011032008820010110340c00c01c41622402810441004604030002409480d4002d89402a40c4101e501241c1c600c0c05405204044100f01403108208042c1e0360031110209083c0700d2245c00c01403030701d09004142d8495405a420f80f02ca1440c441d018801c4202c098051400413070722a00f070142c00c80380c0008000540701000f0044031300d09a032061564050041c8000240700e1002000c0403442400c18100c6c0e03241001c2c100c1e00b0b00401754864685d42c0c111241d178070f041d45000c3c1c0300d900488115003400c00018040c081640c0112170304150b01408 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 701834811 1250 701833561 701833567
    0x609230c01210c140a0c0317010e0a09060216151103010b040e070e1c0b0c03090c0103270506010e0906100522150e060a0302010e0907050d0c050307020f010e0303010605 74
    0x2824420048210034213445100a55103040d0814001c03c1e2952110090700041c5003810f5050781034511110700c0e4100d80c02440c4001c2030340c4a00c0c11400c000c3c1130700300d400c90714541d080045820300b5030130b42c2002c40e01031702603c8006104d420320103200782900d00b407081c41d2520600420041c481a0002c0043d09c2c241d2707042070760700301c000d030f41c2d140041d0760b49051078500c01d500041140b15111202d100c440d1200304240702d0a40a1000d03198565002c0a50000750b80b42c54080e0410344034407019521903440f18180a00c9514008950384d903d041c22400360145510a80e038035040080180000614400d1701038011106800a00340c0c0e1a1561022044694500070f46104000310440340303800c1410449648039481413070350200440ca008415410720f068151141200104004000480500d00b81440b0740450782c06841d60b8141003100420031514030002170901c014404180442030400c1482e11a003c0484000e489840d6603041c540006480e0204034880242c1d103a05003428030107040d00202c00e4a04684660514540f = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 701836061 1250 701834811 701834831
    0x9020a0f12090209011212090b1b0703020603100f0b0901050d2315030f010e0601030b07090e04060f0516090e0606041d15010c030e0d0609230c0121 65
    0x140c20710b20070296000c03011030008500180710103072030400c0ea0f1040400a4103c0318413201954429420b206070b4001c803074140070054818241d07480c3d0581020607941601e548035102c0e40020301d1500251060031140240c49028070124903021031a201412050f956a4100101840020018428509258019510307a0101c0c5ca07107901109580045483c0e20b41030141c03900e4010184071140030a801102d1292081b4026080001c4042c841d00302051600f4001e009076a08640711001c13240000303810b0004000180c0000601c80e2030914442e80200e12074103010500000804102c8160b40780600004c07402c041c2030301c0540c54181c00041500441d000a40da000b9595140f00000300c5a0140b83e01180d0a420b4040203c3d541d81180c00740d044c452891034a544840d42c3c50840111401001840001d0100c0c01d1180210801d150840f81000d503a03104120100d0700c480c240c2d036031b0400b0250207440d1a10810140c1c069044c40c1c034090082180300807081c40c0c11500c000d1000101da0b4801c607460382d0f0a6a141e60384080d40b07 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 701837311 1250 701836061 701836097
    0xc04180c030609050f04020f0a061205060303090d0615050609060316030b061b070806010806070c02130207150b0f0f0d0204150f090f020f1c06030501150f09020a0f 72
    0x1000a001c2c00743d0400045c070b05041305c4411013108803800c901c2104030340100c61340d61030031f400010180c40159aa601035026001428001070001910751940743c40240610b9545594014501584074441c420100b003280c54544200850000303a00014410b020601c0702c07190b20340b100d005481e409003408000e50102074940c241907005200000710690003030000550560031151051020400307130850f604440e03a942e503d2074040c2c1c94103801c0c0583d040c00d4000101007241a44201d0307008503042e000034a941485c00b40741d6013041c126802060112181d070300250054090207440d1052042c071001c15194440c0307101002c400902c00c00801741025226001988840d015500e4950100c440c1e000709110307101860f0349031030024009103171611030044070354103000103130b07440307621134020b4540c819411010f0506000c84108030801030016404004400c9a580c4030000203c1c0c400d0103a8000e0080c42c1101040003030820000729001034250b0803061142d0b00400620900c5580142e8910b43c802241c900b003895018698a41 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 701838561 1250 701837311 701837321
    0x140d02280b0d060302030c0f010509010f120501030b0f071107060302180907020109171608161a1e1b07020d0f120e0301052a120406140c04180c03 64
    0x440c01d10082900300319401c0580c40102660300031012608144800c004204444400680d2680018802d01036100390354011a4146840c5045003440038207030129040c403404451090b0320984103d40034006202003604810b607485c1c0c102405190184848050a41341c0d0303a2510300c0e22911080540c001218001042c41e50200301010000604480c16401c1c845c00081c0031340304c140402d503401203a040c0d0300c414280440c42220b000b148059845c6a01442e07030780f9814220b402401034810402d1109140c03c00159113840b000c02942140200d1000b02c1c00d01c1c1c410008115040741c10a0302500f5500c061240058101c1c0d5444000c541180d800d42d500c0c0000c0c40440c0409043c00d00c0244600030807039800b01084000140350488007140d640303400b91007800008040c2654820f6402040440805000260495201c075030b406440b120311b0340c0b0b1071400d6000701e0840d015500c00c403420303508280c0d200e1840040120203606150400c20440d00c07282081d0801041c400a52801e0020412581d520002d40822601039002 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 701839811 1250 701838561 701838569
    0x81c140402150c1603200d120302091206040c0303090510020606100e060406020102210c0307201902031615050a0e1513060203031306020304050c09010f140d0228 71
    0x112010642c5c4e81d00d000700c03801078017030b035040302c01c03e400e1a4942843c10031850301d685450300400c40c1c000d15548074030700707500943c000d10716260000135050000c07c02d03030b80800601e8061845042d03003849451441c1401040100704d40c01291156012150b1402c2c1c0750790008446410480c00ca64810f00d4060424003916400c50a41c281034020744042400941c554045d8007501303d04041c603411009a086003911940d0078002240d511800180038008213526a119100c44803151030400c1124006a0700180d0f021303e0041e07444522450020740240c50021401c09020f040016190b0500241c01641400560398407121000c008104108000c1460000148102c282d1421604003600105030076200e200d2030401c42d40410380081e403600900000164a6100000302c4e4440c1643d00060f2200003120ba5030b03140658405003007900c0034820022440155680c042002d0300034010f00d825140401e1034080c10600511a82e1030544c81003600d030140101580710007040352101346004021030380386484040e42c10760002441d00 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 701841061 1250 701839811 701839843
    0x9050915010b0a08090a0201080103121403280b0906091e1302030c1e060706110414090106021203041202010e0d02010f0b06090f0402090a03081c140402150c 69
    0x30001070489000310041c41850700560340c0d16410f80d00c1c40e0820303655170300c4070600a0018500c07800410204541500581008510f0316001104034101640405203400c00e40e2007103461540703c009a00440c00385802200200b1031543d00f03200300001c010015558410050a035401102075000084903070180704000c00c2c1d003044117070504031a8240b031900d55450113800b180880c002d00c44c0c030882d50380301d01d0840c0d4002c416882484101448445403018404280c00000089482c0758460407030540c401d8030301001d0400707880c03c0c0d00c1880e401c41900381005040d075010790000d02990010001f4194800804046030fa1080d04004003100c0707020401000c03030041c0b0081103c0309650260783c203907080140d810340108144501d50700c3c00380700d080102000c2100701e02c9a00e00080d44400c40d4600e015480c1003a40240403c410000c01030250b4590b25101d800c2c00e580880c681c00c003c0c0c111003108004411903403140130301030066010454107900c0c4c1035010506070524102000140d041c045161030400c00200b001010329007040d1 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 701842311 1250 701841061 701841103
    0x807051605010809030315040c050903071202040b0a180b01120e06010501090819170906040902041a070f0212390103020a02030a05180d05060a0e06060a090509 70
    0x19254080400e0042900251043d0081101014000142c07030003400074441c26076180c1d800301304100050185100c10801d02000b44500883d9540034800080140381490000d00100c503d841000100c1d804498076a00c40c14044c40709101ea444054900e911100452500080002c0200016a20003800c040c403c181541808001380301800c01041c5c582c101c807401e03260380503210380f951841a144c0e14120100612141078400c40c0000c203407a4032110000ca0340381d22859160a41ca040412510752050304080708083d00000c0801c80c1031030184410b0b0400084448250401013565a84080402c200710702a1117890303140034a68482505000d4180101015a099012802c15550b00ca505110380e4183c4801d469a9801000d01d55009008071545400d240c0d020b5403a00390402000e80700d603080f00070706807000a41884158203640340c50240500c007600400052400745042c44013281a60b4107a8640c000d075400202c01d1100300e0b1681038504041d80c0c1c410700c001c9800d85d55802054038081000c03901c012070340c402e9 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 701843561 1250 701842311 701842333
    0xc0203032d011403011b020d080a020706240807030305030c0705010b091e0604090c05011d222409090501180326010f030b0a0f111903110304030c080705 67
    0x3d84840f01441c2015002404040b010170550401280c000c4507240c00760b01300c031103800c0d4420702c60313405558024465070005080c54034640303806044814000341c1103801242c5101e10507070116000c01600c02482c10302c000780b0102d415958001d04074000500301488031700300455a401088420340000b805a1005020880c040c50405210500865000e5103c2c0e04913840300007040315424203014043c100b641115810f14402d1074500112020004040600010402503003001421b6031607001c003030150285070034a8030b40340030315001c1d1104031591911480f49400d92441841d80840c4142d0140080381e03411100082d803410181081400340206201e00c1c24101c814038415000c15410074014260b500318456207001c05000c0c0a0300454201d4203004080a5902021040001903c5100e0840c5d1080c0c0070180440e41c5140b4030b40c0501602d4450188001000b404a2030100c00c41800c80d2014100c5140d140600c20392840c0c81e2030520610014001800300000d8000000030b03c0083d04c1216170281d80030701128960000 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 701844811 1250 701843561 701843579
    0x50c010c0909110309071e170304030b0a020922180c030c05030718020307031b120b0d0c0b0a090b030a020c0d0503061e0111030a0e040501090c0203032d01 68
    0x950154103622843d103208401c50840e040d00303030b9209001c50f60040c14054104a98160104000070110380c64030700301440407a000704a18104141074510074000c64986055103020b0389000c0c40106154803052050140001c296074080da5280781c00b080c0c0d001080200c00e001d0105c00a440841841c510400c10714000b10200810140500c04681c02400000071054403030040603101c000600c26030054689814035450301491a5000f190815141d00b40001c016008000c4a542e92040c00c3d510408100c10820080044010b4010030031044011901e1a4811003907599880142c0040e020385d1801a00218800c0489801144600d000e000488142c58880ca4840e420602031741c090061050140104200d8040042c01001564040c0c14018140c1004914072440c044400e029000e00c6c9042080c0d8408404075002e003440180501e43c7e00f036403051402041102800240c403810f81c405840c0a141503000f0130001c0e030210989411400c0442d400440c0c2410500111a10142e024088420360111000186a0f26 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 701846061 1250 701844811 701844827
    0x26130e0c0712124101050612060604050913050d0807050a0302031e011707091107140114180601080606101b05010606030509060a06050a06031113030c03170711010503040201050c010c 80
    0x12a2040c13580320b0200d92204926502e1081c0318590b0051018001948180d02d61b028090303100701c0103088141420741d15000103124500644100e00c1d5404081c61031000e00c10184509074080c0704c1400c0c000454249004000c00034460403a8400030140d001c000f1406e2242d070240c00c41c1042c0300300550368030b16503103d02c2201d500c03402e45401c164062240d2800014051011702804101c0c0001085103410000d0a4803184004d0500d8140d610055680d141c40070003811240403e14041c80c0c01c039495808014003810280d00d041d0068110440320350069042201c00c7e5100c0c410414218402d05d425484072044000011025145400041655090040200c0d02540c903500c410300c940c071810110382041d03e60042180480d025802840c1d00416820005e20009000b904240301d04895a0b40543c54428910b1880321207030312903041201c0104040300d0401c1440310f800e2381452203c1844140d6403402c0400d076103459046940d03403503450501102000190946e07024406840000400100a0203c0c070b449940080c5010 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 701847311 1250 701846061 701846141
    0x504050c011706010c12050705070b030105030c010e10110a0b0702100f0902100338010806010215011e030b0a060e01060212040326130e0c071212 64
    0x2520000209070240301c0d480c04a00482c1c0c10317140e078039174241c054446d010000207a503c48001d10004110090018204002640041c0580b101503070316541018101410010590002c504000c511064004c066a6a0510222211035403c101c41162080000142440507190018094080300020800d0040d0003003081c01c20b503450200308004c06414002c1c1d101c101c0303000400281d0401400401000c185000354000591140f0440d03090307148071502401d84440d504400d210b0f005210001e90001050358006001c641c002e00b09001030181a6650301248802110520980c00030f0250420303800081c0109000841c09035400803000d000c90b14100d82c6160150031680b26602070122000000110039101054800c0c60303401e05204146841c2ca50f8860346040b0020510a60b071070540f614401180b1607151006044c200e40542300000c1e8907240180343c1c0800030009041c0ea008040c20002d0200190740791400d800502c01c1800e2540803c400031207190000c060100d11500203a4058500300b018440341c03c0401090f03 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 701848561 1250 701847311 701847317
    0xa08040210030516030c271502030a050d1109040e15101d0a0612290c12130c0f0e0c040b040b0d0e01090b0601080a050705030606160203010504050c01 66
    0x703203980c5800300c00b01c4900f107460980c034a02d0200d901540c9403180d08400390704042441c2c50748190403c010ba44901841500c044003003903007060300400503030240701143c80200312940051410311440c8940070741588100a1454049a500c01c01140800360f807105541c4284805802001000d445001490ba241d040d81c00c68210f080c003407c0052411003511590205552143c00e82030104189003060440b0180050850b100b01030301c0d14000720300540c41100402405010708084900200161041040c2ca0420224076509104507020040c403505100100d0f40280440b00c034030582642e99400264034103000301001000040c6468000401d4103a8101980c02c4d1400d22428071007a442e1a414411284031b076100303100c2000c109000402c51419900c3c0030b40a40c01c4801c0010400900031246242140c144140031595034003100300344095564003c02180d8454140300341040b041c1404100a4403070300004050340d20607640050407442c52410254114003c40d80a0003c0c001400c061900365160f10fa030490351400 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 701849811 1250 701848561 701848579
    0x507030e0105331f050a0906021c052203050601051201020c0d0e010504180f0b120a02100302160b01060e06180f0d15050109060f060e120109080a080402 67
    0x12200a6040d0344030000c500112031000004002081c01c80074490780d60f90f4084c0c0e41d42d10b410300096202ca0700b10400d11aa650341ca5a880c091134016100c801e060300804210341c405051000039440480b003d0400c1005828250303218800001c0004031003126076818841000c514a002082140005071281640c1040390800c403003a0502440900700d008941ca6000c070f0364090b18448045034001c0b41c08000340c1c2c5041c500680b8058861040c0c240b94103403014a4080c55030344186079922900548503060700c0d480c0450305800400c146c0c4c421980c6d940c1942401038400d0058003210302125010b64102c8181411550001200c0c040310f0800444c404001d12505000c46c0c1400d5120785946002c40c21151403030900d50f0b62030710000102c0140288060309074402500440c411040c1c4002c6200f186c4990000c4166140114103581400f21110564800707034458039a0303002404c014013229810072480c80082c6400d0300c0c14101428241500b5016204400002d00220390010380f0045544d40200030500c2240252075143c6 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 701851061 1250 701849811 701849821
    0x9050c030105130c050904020f0d080309060c0405010c060506010909090503091c0c17011d0a02030706480507170303070504120f020306090a0506150a1503020d0507030e0105 76
    0x8069012140000c1c2032603c107410920170f03032030003031000f6802c60f00103011441004512008108400d0300180b0945040001004200507480b04001075948040c4461140c2d090501e0400045d0601140d050000e003901e44400008400b6441544500001c04601c681803180140724103209489a00c0390803018040c8030880e400c04c1402564400d0349607030540c802e044c00c14852810084245d248a0300c0007124095407910140d400041b42d80407804010204034000d00561951441018a081d4582d480134081c000c00c1c1003001405c2041030024104075007404518080301078052860f02e1641041c1014905815a0b071000c0414007000140550560301400d42c0d044c1130300400c130392056490204840d00b000040d4200000d01802510254201080c1c0c0f2800441441d00090360001c0e0800100300e500e04444d612044030300c400d020382089415000810904407201e03031506540442c1c0032050900031150412000640442480d100e076044078000880b20b64108054201810000d01034003c042d0980c04540c01d00340852 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 701852311 1250 701851061 701851081
    0x20d0b1f080a020a0b030406090204060b0406021507080a090206090a091d0a0c1a0d06080102090316080a030f090e010909020a060e0127080106080a1218050108040c050409050c030105 80
    0x41031143c0040c00740090500c2c0c0b405440741c60b44001c02c212070ba5610b40702084016100d60186001914002d0461174599040150003454440111004101ea214400034081680d801000c0f41e508481028070100d9200000c2c0041601b1344140505140c02118019001401e403059a00c0314950040c90400c805542c3c0b8444001c2c2d07510190014003070684c4012070801c010f10076440c050080b105503404d0038541800c00c03002c01d07a01140c2e0301c2ea002076101d94000130305801e0761409208400d01c4e01989030501d501581000c81003591800d1084c001818001c687e442e1181e41c2d40140a154000c01d042e11102e01e03e503844a604001030103210070128007614030240080b586a005032183d20403e00c040c0e40354100100040030090300064551078044008001490204803000c0030b00030314000c0c24599005103140704070b41c50074240109043c0480c0b0200b0900c0c4071000c45520446504104641092a050005450394104507885055550243d40c3c007a10f0030300c20710100200400e45e2041b124049001304480c2d51892610 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 701853561 1250 701852311 701852323
    0x15041d0303150307150e010e0409030305040b0a021c0c0302070b0405010c0215010602061f080d0206010f050f060d27030e01091a04050d05010b1008091902100507020d0b1f08 76
    0x10105c002e5000d01d01c0394040380709800c0c10341c600005140a0f40710018240202e42115120304084e40000e864008000501450100040d0001261401149000328103403900740031120981902d0031450315078405000b1035100760141c0300f1043d0040000c0d151401c1c1850894000d0100080c100b0140c0219090002e10842030079009049400c01d4025103181e986490940015059111071000c1440b803480300810840000c000031810300b289a00204055418000c07804450351b101c1c0e11081c400d9086295625640c0c9522045d210440c41002d0040340f407a0651030b50140003c01c92201c042600100764800d010f042d4041d01a0000036401e072244904203854002d4000608401e200f400b80940080200b004541844030340400581d00a100002d900c0406c01b0000e00030030803a80520300015008810b2001c041c1c018090602e064ac000741102002c03540c00e0740070490261260610005020000c540c52056440f038217100743ca1650f03c80f8513a0321034900385100e0b1005031501da150b1000300c401e00d1408200103c0c00500 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 701854811 1250 701853561 701853569
    0x1e0d061d07060c0f0f020d29010b0702030c130632030a02010206220501020c06160509090106080405010212090318030f030712170c0a03050604050f15041d0303150307 73
    0x213220542010b0f160054180c0c1e40324012030304104c8004412000c12004994428800b5a042615488800781816560412410381080458180c00c11031500180d40020b103184848a00350740c02c0c404002e81851000c002c01c0540d1012980e5040112014a680104131602240500c90a51034a03001c200c42c0a25030303034400926000b40564803050100d6007800c052100d00d02c528514540f550894242665030030b083ea004409107001f260310075011b0003105030046a42c4d001d4891240b410300d0a0582c0d800000e03040e040180f103014140500c170320105003400350a4040303604190160755110010b06180500685e41e90000302c0054034039144090038569803a0100340c650300a10f114004504010785926003d6024400c01c074100c080c44912404042c0c2e8250038841603108859502101c2d4803a00c80d00b2010301901c00050070705201d1450b1104012510751508640c1340c02c40f02d40c00c011046140c581010070001d00c10407441111051800c0c0d201e2a03050000002503200340d0403d246214000620020705651b440c0700c2c06 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 701856061 1250 701854811 701854823
    0xf060f0a24020715090609210b0a0f150608090a0803070503060604080115140607030804080a18060509090a05061e0f0a1e06020c030312070212070803241e0d061d07060c 74
    0x903100101d00c40304012791300901c01e401c000581c0e03141b8090f150200c80c2894940c0ca944103200904200e05604080d089034840b00e1070002e04212501c0355141d0b04548001049201404804400305105840e16401d580240081c08002c000d6040794801508400c0f42520862814070752101211600b41070800036101100c3d8161592a43c82d00e4030369407103846420041e14941007003a0342da952041400d500c404040103006035180c290740c500c03141c414444480401894221881d003001d00f403004585400d0382c1494929144500c0315150810080001c1c01d00c070141207650760002c030300e08010811000d04030342c0e180103150800b0590700c3d01c1d0381d8200580e215803524013103c0d031540040c4a410741a0a91480603070380501e052040d10049070340700c00010000d80100b40c2c2550340c2100402003000c2051445600c0302c25500c07002004c00c10006040c0000c0c140040109840c82c103200800c01111640c81e0401400b04240d4270800034440156141d8042d00405295030342d400b001d10400c0340c005031890281c400401c90321f40180c = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 701857311 1250 701856061 701856119
    0x15150703050d090501050f040506150d0f0c1503060914010302030c12011808070201030e070f060309050f0d020a050601060503040b01050603040201170f060f0a24020715090609 77
    0xa281500d1075080140002c002c540c0390781c0c0c104001a420320560340b08501d0f81d804115a800c2504005183c9100100031500806003d030220351030350780b812107500c1900d0380020124084a02c901c1d04904034101c5a1081850101380c603100d02c2c5442e0550402011784609000400c401a1074411600c00b020007031001a4058000702c03144041800d00c040f00b1703444908c0303030340000c500d40001e4807280e0300d148901c08080e03c105070041060000c560b81401100708030514840207110b19410842e10420001040c4640014540d0b1500c444d402c00a080c00b40c5030780c404186084d07882015015001940300d0a100c1011207950044400200b0325a000c2c0b001c1c2e034003503600721408010382c3c0e08000c244034aaa00190003a810b020310030108a58520034445014401c4507490050070075405c1040502c0909011102c03034920131032940105000d842b05174009480e51410817001e840c074184060070240c0c2419450342041504041c002455040c0c00e030400e2540c0108c40a587e6600e5445070742c1c0060000340420079200d160364031401 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 701858561 1250 701857311 701857313
    0xb0310140a020705031c090204050a020a0815031908040504061a0906130b0a0c060f06030203030910030b0315040507050405011413060b12060405060301050c030f0709030807050303151507 82
    0x90b0b0141111900c64001c036442d01d0030201c62810420440780d2000030194488100e01d086040c5405041d41000140d1002d5041a410b13140203040c2c0107004064002800b040700c00050f40d03560412018481c4104401c000e4545d840a05126500354401e000b1540103600344500020101203001e140f0210103d20510315080c000a4810800035601a10070f4114510b03000c0d501146440200000780004551a101c60201c04410301d40801a202645610b8105a00d04038080016840c0441160b4442030304960025114004260685c010444054410f40600c58510240c01c0070352600000c50143d4000d004407080160341d0b00400c0240c40c02400784030b82d0506080b014102e90700b020303418000b040b01a0f81000c50415103800c0c141946030460b01410407200c07661424001a42410303c240390300000c041e0028401407500c0d214882c5588806014000c40500c0351002509080c032489030b40015603031000ea240e5880900d42802d40e5650070584e0a121b00c0021907101c400d05240c07c2c1040059001c0d20744a00c2d080c0146 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 701859811 1250 701858561 701858581
    0x6053301180602032a191e05030d0506041122050301110d1b2705130507030b010f021e102a17160203130602010b031014 53
    0x5044024144100003100140c004030a40c08207010301a40d43c01561288001d400110395003442401c44091080c401c40c2d49a03160300f0100740b0f4011640c070940510400b9909161103010106031011211290054078032020801c4008002400c5c8903480744c909000503241d050800048886441c4502500c920800010401c10f40e00048010000702e201110358015aa03000807900b501c4021001a100072000244102148603a204d008203d014030550b40000d41031030040540451130081d00d0001074054803c204000d040300c241030501400380039100404018081c19404042c2c03005550f50404241069121061548550075003003448006074010b1031041d41c150554400351140f121103080c140945a00b204101c20607028508804000c0191419441008568500b8101c848080102045950341d0036045104407a01042c2c0c02c88501103d13076400c490352a83c00d9183d0f10400200c050303102072089000a8554042d0b101c580d8450b401d4082d24207424000e81410200c1d488100c01c10610255000441c04c1000 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 701861061 1250 701859811 701859901
    0xc02061e0f13150e10061706010333021b0102211b0705031201060801140103110409180201030509010b010203180604050a08010b030706030902240409090b040605 71
    0x10180b01003110021160301660191303180411010016404842d150140e0011442404010020751043c03400c140140300c2229124107061101500301007101a003049032000103002e148105015100c0c080168060b50211030294108110400011006100b070f48030140d0107000725061b10940384a500b018241340c20745140d03144800384c86070f2002401340b42103440d421882e2000388019406007000f9600c802801c1c003140800c401c160000001c000f00e03407004000d40e0707910394041902c8203001d003800310785032000b41741d5010540900d901c00c422031404d0031034000c07042d01e20915841e152030007030740c05104550355500c40a0903240c1c4581110b0050740200903008021142e07003410514060300603d4580f605541d1400201e40112940141c141c036591054840c220745400c12407030780140442c0c10140080c0016030001740d5060780108200070340759602000d01e22008a85003c6a001d0240700d6801c10804915081c00c8000041c21039048510348d02e40400304445000e0480f4118040e0710103010220100b2405100c80c41d050303 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 701862311 1250 701861061 701861063
    0x9020415080307150e010f05060a14010f080717070c1704050d0b0a021207120c0c03050708030601030b060f090102070b07051c0e0405010e06190305031b0708010c02061e0f13 76
    0x15035590001804905c080c0101c0801460046021459040c20002c0002e4540070342d1104103400f1156144904998003c0c0c4200e01c21250360030f100d980350307071139907000d43d0203410300e070070640b0a1000307081040b601540140038940b0760750250040303107854010300b08450110301c00c0d4014641d0ac814884290b07800929821031285e880114140c000d0300b008080c0400f8503801c82c0503900701c0c0c00700f0140c400000ca541d41c94403442006180178170f00940e040e021518041c2117441500000361034002e000001900c00c1e4040d420400301d841002d8151650361025481718031250f0000d0010500501039020700003030006158068960168004010705050359000d400108100c4e41080c0420601410070500c0300c0365596403142070300074001c9440792125880c06034200b042c00030455003080748414030f2140900c0407940c004292429040d0b44698088202e14500b421727031820181e076100038015030a060340c182c2440e9000ca111405400070a12500812046901c103286441c8101c424841c00f80303100000900c3e49510b000701c503440c0307 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 701863561 1250 701862311 701862353
    0x10e0409080d0507051e180d11030f010e011409191a13031209030f200f0c0f01050414090601090302100306051e09131a07020109020415080307 63
    0x1511103807100b0503a001101e440c0c0200340e001c1440c6003800c0c9038085024400300c1c0480c03400d1038000440b5649007010301c002c1285004010005c0c51034204011030b007107125100700040c215640c19000940300c502a040c40c0700b0380c021950074060341c0700f08203207000c2c402402541d000380034048000c00003040711005a00c0000c291030360b1030104205200d022000003080c6c06441d480044000e031004c9402d0140c1f680c02c0404510700114540f030084404203900c20300000e0540040d140c2600a644540001207001c030090f40410001d001e41c03465011400c0b00050702c40719180d02a206814082e4002d001584d4034000c9101c0d010910744003a030003004030b1820550440d4000b005050190f031003130702c80d00464019440c90071000082030b506c20003400280352248401c14140d40d462402c40d1003480010103d000e050b0701a08a86c0700d1a00d1680c0142001400c01c0022080c0c2e60a0000708914a400900240a0447d46600b07901079440c117080b600a00c5030056843c0e0070380d90304c000110f00d801c1e03080d0307194104040d44443d01146 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 701864811 1250 701863561 701863567
    0x5040e0712030903061a090a2012041106030402130209040906021207180803090906040207080a09140402041d0601090306051005120616050c160e0a0f0506010e040908 73
    0xe0807600c000c81001281c000d0b03580381c14040c2140740c17120480e290158201441c4900b0013483c0c146548054405900c4035001002040c44801c4800058000b05440000c158511011811928052502c03c005120320b0091529940c1c0c0b10100b402c2c01124803060b02e01035000f00c10a4409060300100760000c207541c91020344001117070740c4c1701d0700c6040490700308055400f0040f00d90014040443c0c0d000c1090903081c003440490402540c50000181e58a01c6502c0718980200b00100000c2c050350780729415100d1598001c0e44141d62a05440070050028901e80902c40d610304104200c1c038002d00745882614144c4200000071080801c802c81410382c1d4140040c151030400803a0f17080030001031141d00640307010b4210044110201070404082202415510811804942c0300000b0400c0503803508203001c0d50350545041c89035651240303a22a80c00c01d040710142c880501c02c100000510417000d106c0c03c1c1d224003200042080f28240c0390f4411004d48105036a841c0c0020820803280300310386007903400403002038400c003044c5103 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 701866061 1250 701864811 701864819
    0x708100308030703050406050601090f05040e100f050609151309050a021509030c041503020d170703050d0e0105090706050d0905060108010f0b010f080103081b030c01051501020a020a05040e07 84
    0x4400e0b4012200c4000082d03c460901081201901443e038000409007813540d459400c044013004482d805201d0184903075124451034400c48024131103c0303c1c3d12400c110610800c451a00c10034054078050701d0141c01225440005049107030b050754034041101c001821414610104070303400c1d020b084c10307005c00e842e140200030746500180c0d103904100d83c1a491045403581c0703800010041605014409814500443c10004501849a01c0d0036401054075070464245c01041c0490400c114052444011240006000241c034004e140d0010042c101d50040b180c001d10012100a921901342e131401e0790388009a40c0103c00a00402d40201d015014101803191300188061141d00c9062801d0300070ba0110099035503818918410f4106401000400c1c03000b03003440c035428104940c009011007070502c0007408507040030604039070542034a0980400740c2401805c40e83c40b90a0b943d80b450080c101590030100d1110b01c2e0400507070950020518150180c2c0040071a203480c4c0c0380a0502010b000f4480d0901014007a010001c1 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 701867311 1250 701866061 701866073
    0x18040b03030a09060212090603010308030703060b180307240f03020d0f05060a05180c1608040303030c0e040612030e030f120d2a0f170a0207111002030307081003 71
    0xc05406003da4403442c1d914507244000e410050705102920039030004000d110705030345408088904680e0f2140400d95255184c51048000f414070750820002482d000403140000d0f200140d5460107020100c1c1604d09032642c4250780080c81510140c14000c1c48111340306881c40321b018003a001001103d44c2400340c0f0b03140142a640d01200c0524030080c048a694106110382c40c10608010800380a00f0380c3c40382c400643d4148a40301e0048010001c2d0030901c03002038004100003125440c018034aa00c01302c6203854949034600a4050103181c80c0c8140042c0780703808501c03010b01e420b000362011125a880312506021058408561140780700012507018814144402140e83c0104400480640010ac405840e0080031400348240c2e56007120180311403410003030000e2b0f070040040150081036000d04180060113403d51064405102c0788403000965a0b92408210120340030b9001005150f00c00d940b40d0142c12024410440c0c403503115002000144e0040c000500440d000b61a00d40e00062060b18505800380c0c1d0399250 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 701868561 1250 701867311 701867317
    0xc0503010f03150b041113120308130c0b03011d06012d0c05121216021e01090b01091b110303010e040f0602070807060609050f0412050c0703140c03060c18040b0303 72
    0x5c0254400005a4000c26000c0d051400000d802c00c0c615903230640f0810381f0f0050040078050100c40c440816410754500f0001c00d02d5840005201207040342e612580d648003075503030a0ac403070001c07500014400300018280e0b61003100041300c0306c0d202181d10507280e20444070003409001429004005d003d001d42c4e41c00b011400030052081280f9114000c2c0c0c3d42c40d80010850042030780043e02c2d40501d100c14041402c40e01e030300481c10710101071801100444848000307a02d14003402c039800d8054101050ba00002c51101e829400c80462280902c00000c90342c49002001c8035601000d507019181c982050005010b000e10042855030428001d070b00d120700d408102d0715480102d07131103110112070104001808004000705809444001e00e050b08007001b0506d0034010341a22180001c00003003d1900400150017102c0c003540590705842d04880c00c55090503180d01d80949000c842e007096100a1140c10f0640c03425142c0019501d2040c168002107904026a025554031004075514056500c00e8035982040b03205d440420113 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 701869811 1250 701868561 701868581
    0xb03070512010605180112031b06050f01030224041715090601030b0f01050303120c04080d0e24070311010207121e09140613030f05100c0503010f03150b04 68
    0xe80f4030320b03000c1000560203041040074110810400100007000d411990b40d040d064060030b007128460900b400b403400140d90307107000410070b80c600700520560505c5001c074141030724800d440c103500f0581089620710700300714074451408c0580c000304400c0c8000014850000d00b6140280202e800b0407542500440031a02d084890801303070342c465401001413103450341c0030f1900040b140c00340054950500c00407075202d104100e00315100e403000001240e001d40100007243d00418600c0c00b600c8610940c0040103100e4000800318922404045210800700c262400c1440c00710300030901602c0c0740c692980d4068a117011140d00344501954244203281c0403801ca04200343c220620fa580350185448c03245000e00111040700c80f41010404000c4041c0020600440b198043e40303811183e0a0b214000d20b0303605e450652a03504000d0180c102083d903441045000100a040206150400d102c14100703040d0403507090009210b1035422020441d020404569148503090042e0015000824800d03000d0020600340c59605035 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 701871061 1250 701869811 701869813
    0x909010305031c020a1b02120d11010b0306061f0306080d08061e100e130c020c010f08070c020d03110703200301022a0703050a0b0105040608150a0b03070512 69
    0x6000d11144602c030b40f50350314810344103c21070800315002402031042c07125001082d20400011902c800355501c6417464a958045003041341c3d0f064088003401400c2412440085a080d824074000c05840c0c82c01180a40c403400f0080d1100940821703808103040624407031000402813540e04c03240411000000e0181c911410896120041142000410300004140e10707909000302c65800340e050728540d43d4003080340c5ca8645007460311014400e40d180000310b040304100c41c81840c2030724000540da01e640e004500820510426218196546142034041c0c0c0c0a40d02100e030240081c816007501c0c0018540307500b0f5095054001d142407030035148084145840c10842c0d400941d9846000710411000b02c80041440b104030300c06800942c1041d000314560700700403221812120300800300d02052564054100031940065400504983c0800701c2030810380200303082070050038002c50801c0750114481800064103c45000d6203e500d28243c1d07030f818035090081007070107107255050040c0c21002880380ea45031465034150380c1c600 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 701872311 1250 701871061 701871067
    0x123070308250207090b060405130c1701030507090207151e0c02070501020303510402070f03030c140d05010906050f060d0b010e0d0b16020c0a090908090901030503 72
    0x441580c0d84400c104540a00b00c40065022000e82c5501244450407120036000210700d92a00c1c078001002802990411034012990303005400b22141300350001106052691500c040d03500054001d44078520090002030b000303500c0104100071ba03114540c0100340c0607001d1680d4030180c040501001c0241d640450304000d46862184480004040031311134000840000c0c00100881450940081d40303030300008003100c4c00d0a002d03050072100d4100303980c8211004071000500c441c11194100c0c2c25a113003010b8000d042903c01003030680000a04003442200e00d0b0303d8200b480d420003021a0765007103001d00b003139504403010061558480101e01e2001000b030b1406d04110900840c1540c10011501b0407100e180c0d210038456100f0101c400c00c19220300c4211380f15002507200108402480c440160745500c9c0c0c035070741180c015000d94a1a002d010840c3c50303090054802003107812201c910948101d81d1202c00614560b807106441008200908070340c0c0c400300160b4418503103581401406030000d500440240d00507100b5070000 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 701873561 1250 701872311 701872321
    0x17011b08060d0f0605060111031303020d0f0b13120503010315051e0115081e01030b0907151e020718020706090618020312031b0a1e02030d0c0903020607020123070308 73
    0x8000040d2307040da0a040214113200900c42c0b10180d01d2030500c0040c1c0142c607400800c0081c0301c0e00d040030a44032070f01305005500909240d207400341c564030b08403c00d03075407085400a80341c05140300703d045070f04890300090304014100e03008922500900016181d4105e00285418440501a886407114003c0c8905070001c10302d40d403c00d40281640034024882036080e0403445220350414100d003c1c41341500d81050388000a9a1203079a6585005002e8024140200c02103035042d000030350014004034a890380c41040d565884007072405a907100301030300490b03036102c2c01010121041441c03680582407840c0662030100d00019161a910101e845c04207000500390414030064042d400e04010040040d080721485614600d0170b03000c00b04800310820403000d0000800211031501522800d0790f41411481d280c410a10840072140184da6a405078a250b0589401c001c2d005205a004130f00f1003080300d40141c102807034010315500440b2400c82c0c13000280b034001240d0001909644e880f01c080c2808034442d855803d03040c145 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 701874811 1250 701873561 701873567
    0xb040906020d0b060f0409050c070c1412150414010b13060305061303020604020d1103030307090603060501020d0210111b100b0d05100911030f0102030117011b08060d0f06050601 78
    0x442030f0054050b040412030f88400300e2416040300d046810500c4001002d84500260491510805030050900c0745002c4000c00d40060311951503c00c4841220608000b0002100c1c50742c40e810b8000b0f01840b460404c00c0020046030790b691a81025a00c01c6000260500100000032a00e45000b00800e0310156514418000c00404000e00c68000140705d0310554000d4003642c000395198030041000340220040b0241d0301c03c00c026040c49400115004099949900d01154010000f101a1281000003410007400040360750012030f002d032881c1e045a0182c000f00c5401c1c00004084c0c00504294005d042013006016901007080025000a2100001503c0c42d5820505100160f0383c1e425513984c441d43c403810003040082d40c002510340310703103e00c0c54021512000908107140d0092017030030003c1d098015038140d0140190103500441c1a24034000310a03000344042c610403402c079014000385241e445081065580803d0041c008907601c4403009000500080c903680d43c60381d0410117240200d032a251901e09018017903030 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 701876061 1250 701874811 701874821
    0x190f0e0108011a0d030e03070b0a050a030b0f010507060908040504020301060527130e070b030c04030c0b0a270801110d051b0a0c060b0612040b010603090b190b040906020d 75
    0x203c056052004079140c0000940d1082e0039000003003d01100209004494500307018510041c140b1403102904c1d0030340810050543ea003d4106200000c0c501100c4c136000e4904194280c00c19a41a5111401c042603075407030310700070010003009941410081c000000e299030bda00003140a00205c2d51003944802240d10741041542100429145c50790325044400302640340c0216003c00039184420100d144045500c060b41400116006800245800000c11403520031071802402120300c07444141c03410325900c040408050107000000c40002e40000219056607110903021400c841c0c85143e40322000b980c03240c1c01c0e801c682c0d25000c80b06c071b0307010003042c9004096a40d1040d142d00240060061202004822000d0018454044040148085950224148602030f44408400000601440d41e03c2805181e0a0164541180e003281ea94510000210380b00c4c2c86070052141580e03114102031116160301107203c1c1c5403401c1074034454102e0356075148500c0a81e0f550040c1c00c101800351030010303650044040b403402529 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 701877311 1250 701876061 701876081
    0x1202070203160509150105091c02040920040203040809010e0117071724191a0403020307170703030f141b07090e0309060a03021207050c010507030911190f0e010801 72
    0x42e044040c0c01005d41d07001000c5a048280c22140c3c125210703141d0902000b02c486d92440079410900d840a6541007141d04515507214030800100940c07040c0029040100fa448201d4004242030414400303000c06501034116024800c034141000260400e14082090038404112114400642c01d0107000011b03580c2481020742141508051031000d511482ca0034051100c1c1418043c0106500c415042c0c0300d04480c180400600516030b00401e442d0060198100340c1d4005002c268032074003138504001104a08008403801e800c41c1c6d20007034425546151070030382d00801803100201c184403ca083c2040301e070324150700810310100ca04580340c0384000d05856403031070540c1c83c1c0c0040d40b52500d018004298084004103a0f040e1003800c0350314035540c1c441100c0441c00390080d142d100050702200001d20695541003c00b802c0c50500c182c00820580d5102c1004406403981c40703030701528059028076400b4180c10196180107a000380341c4110380c0c03040d80d075078000155081643e010582050000b03005004560342806606124 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 701878561 1250 701877311 701877331
    0x30f0a1506030b0f101203030e0d021609050603100216030305010524030901110a0f0201200d0c270e0a050c270d0f210806011202070203160509 63
    0x920309558440500f800c001d00001080d400c444000b84d400410020303120058403203880492006401482d0140103000c04030301c1c0e10182d014900095400070b1000980d4900c0a02e01d00b800c1084070f1030800341d040148005410745415000e60125109e641c141da00003455249110503062001820b6424005d04662040c6c10440c4030f50104102d07501e003d12100f007011100054010b017141e072502c50303004041c010a80f00d154511092008a1400450394100c141c0c545010130070b8000780b107001c0701d281c000b60031007400008480040380300780010502021640d00c2042440c0c907034140003c43d0529522344510320030340584e602074424a40309050111140310002c1c80d41140c0400380912141c100b6119a401d035016500400703111070840d041c1082d2040004c0c2d6105800720b40500b00c0351000b5a681050381e40e21003440c2e02560b6111000c4149c80d580110480e00911104150f6200d20184d00c40600450f40580c00300000c0440c1034081c0710103405a50140050b100540a1170100352081e46840e041c48503490b80140f4005107 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 701879811 1250 701878561 701878571
    0xf080c040e030a1d09090d080133030b1809070803070503071205040f1e150e090c07080318011d0c0d060e190c080d051e09030f0a15 58
    0x100c65002090311a40810360400c101945090100d13a0039109101200c00d902031108400d1080e4032002007220764a40c4621b6940308900c0ea2640344400f40c014800d0302140c1203043c0d0f65459075412840e03084666102502e8035000c5640110500001c0040780c944841101c0c0075003450500c4081a8100410001072038030101441c2000d001d501d40c240c680c0502c18019215010100c401c41c4240e12442c200c42c094182c800744508c0d03107511004091054205032810134801c1c5030452000c036621140001012009086640740c2d04d44c04100d03010b01c144600c1c050001028003e081c0516800102643c011718810315a40c2ca00300c40d10082e21140030300b514410b0030004041d03910700c074103041e03880030106104819503801c2c0c0300c41400e10143c3c9401001461240c2c0610f0550062148100201242101e20710007640500c0d0114445505c0d0345045440b04503688225021440c1044041602c094007682c020550480c041c00302d0500c400e00b000710b42072a09010712600c240d00041c0a400c100028030b42c09900080f0201c0d02000 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 701881061 1250 701879811 701879831
    0x905010b030f0a170d090f0311061308180a1d2a0307050c100e0109050d0f170604020d060305071a0403020609210111091219120c0204060f080c04 64
    0xb40030311312850400110100021300e2034881020382c11140c452584104c102035008103e0400400c0048040d103103803114050305002c02c11030350301d00501c908001d82002915180001034161816580754603840170343c000b0240000014618000702c2d41c5072064181c40342d03500c0749103400124070007503d416050710100e1022090440607040074203410740b5404182c508169548001800603945000e00348030881220906001c0141c10700a01074104d101480c1c406c42c11551184003101003035a521800002d54400243e030b42c80b588080500c0c1c503134420380190010300700502e005c01035160740342a6600ca80055569a00032070081041d41040103215211682400c2c01608090440c0d0018505109003074050307110b00d90320b0074407500396403680c61804098046440200030b08044411520560340012100a110785000e42d0400d00f18034000c00c4541082e504a031032503100700540da0b41c009022a0440c2894104a010300903e0300581719849080c003c2d000d1040a0f044152601c0185807414101f18110f41c086c0782400c11401e = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 701882311 1250 701881061 701881073
    0x61e0504030215120c070614070806011b0b071107120b1b0c16080c030106051503480a0e21030f030402030601170c130f0905010b030f0a 60
    0xc0d0a6035411581d03104600402c414604480c004e001550316510f1030307a410b0050012203040200b911600c911410b201c00c984c1e542100100d400700721410000328520b00c000682640c4a007524100d00d06840d0b056604450340ba407035581c81c3c21821503114001c1813400781180d030480d4007044820003d004420b5103901554460b550004280c0d8040c08145280b02c0e20149130500881e0382041c1e03000c0c0103402c030407140c2107200454402080c2c112031040d2200d0740605034040c0b20b2070906001c1c0c0c1e019180f01401d000c0c841305ca0071406d604035038801403060540305200f0034921000c80100120a01c03007000754041040107004a40860410f03070740724910400d40d4404020f0044040e4000c1d0b0000c0026004440b003403100c3d012004036501d6803031078050140c2c540c00006104c03c40c106408010314007860080d000c0b200d841c1e8039020000011407800301d0041c1140d01c2100880300c145084000d4130050804e000c0c000c82c910800503400d505482d8000021207440c0d44545501c007582c1010092408048112002807041d0b00c510b450340 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 701883561 1250 701882311 701882317
    0x60c04060f0e0d030903020f1c081e040603140f01060f0c15231602030f070c1502102a05070606050a270209180406090c0f061e05 57
    0xc0c814001c520140403802400b824000b9000a00341c400f106200d8607005040361418001288240103010350b85605080c80380c03448054059564944410440b01d485054558204004070a4a403108030314210500381440c0241c8010121a200070480c01d900000107055860010110308060794220b00402115034403c00100b02a0300324209040e00c0e0096003400390b865884d0065559516040c0780484003441c01201c043d01400d00e48144200440c0c540d00826018000c0015801d001a801813000c51150003006008007645403003600202403566460032404009a00040404056042040d100f15500d0090081040b5280c041e006c410444009050b44086d05004081800c00c1050100328001040700540c49600601300c01803900107040c5c1d40d030310020700c1c1d4404521140321508850440f04100010b034001c0d81c10305080205108180844040070a22511001700b007039442d69140c17441c91010540341c4900801420b20355015110170703820200c003c0e1800c541c00c6e8180b954411880b1044920075444019 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 701884811 1250 701883561 701883569
    0xc030303130222060b13080d020d0f0e03010903090306150e07271205100504030c0609080d060603050610110606040e03130605040302040b010513090b030703060911090603060c04 78
    0x880700c1c011010300400030f40280440b58100680c60664045642404000904441020051801a520303160710f007180d100c0381640141e4002d40e000401184000340201c05a841c14810351424400d402500130000f802e584001d0010b401040d003140313050003404a24002c550a035592400001646441c0a00c820b9500030b000705110100014400300700f0380c054910b09200b14586070403074026049a10f580d4000c404d486203420031541e600c600d411040b00c42c2958007820b4411500341c1c0f200c441c4082682c6848028008400c802c0320908410005407181c1704591040f1005044190741c001032900d0050300740314001021441c00030500c00350000a0303620710000a00d180d03220700180c4d0089801e90b01034006620758000e03101e81124400d503403030b40421041d5100001c0c204880c0200c4003407100826001c01034800d0710680c8421040b6502c0c105050062150940041d82901c00140883d41c1c520369a0311000101c825100c81200d201c1c5000e04107030010305d41340d07a652790043c0702140640010704010006198074400c600c5 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 701886061 1250 701884811 701884819
    0x5040b07081503060108060105092a090d02060a120e01060b1c021e030a1508030a1404050604120204050c0f07110a03020901080604060e0303100308130302040603140c0303031302 78
    0xc0041c8910706242c000803101480542111081c1d42c40e040059100d2600f40075160244150701c00203000800100c0d4420540354440c00c0e91080c007001e1821000c950b5000414440d00840204400001a1a00801450785040d01c0e030398100e0403406030404200707a440d4100620000d80c18907006002c8006107204540d4010f580c0350f050f803118441c0f0034400d4042c4c003a0040038124410f5a2803400100b02c0400c00851080300c904108110b0080d804882880f01d94803400364100075401031140010031402041807600c0d0309208401c1300d080503595400074582c0d40c096000204064180b0100704210700307150266581103442c422825040c0054a084070b41c1034000c46c14060030341c12207120300c1c8085888603500071002e15005454480d4940c0c41d0070310141d80304001e94044409503d00701824440341070100580e801030489202d04100c041c0355403580b1480d50005108440c00311f0325010b0001c0145e58905ca400d000398404c0001e165180d102c0480349040107542c48000e4040e400400c2000042e1602003154100c03140c0c126 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 701887311 1250 701886061 701886077
    0x2090102031c09081201030b0a140c0a0c08031306060f06080601050f0d0c030b030f161203090906080c01120204060e061605100609060602150708090f1b0a050405040b07 74
    0x740b60030024060469000c1c06040001612900d09061030740e48a050b0390080940f104981c5440fa082c0003203802c0000f0b20049402c244c4040766461f210140101003001080ca004548a035964070340c040564401d40d40143c4130312085051204002c241d00410b0000c1c040380c41216091450b0210251414200524032810014002089a9040b0b152016144102d00f90642000184c40c0c0340b0000e40100b4043d0042403086c850803140c0951301100183c4990f54481c1d6070601d040091500480300c0310a031010b00300b1800d01400d5403011a00c0c2d1401d12501008244900040c5946078070361002500c102d111995179800d8600401c424040300750002c5030070000701c0381501d102d9991341541d0b031141005014150014041e000d95201c0d010040019044141550400401000210366440007030740d40d106601c03045511401e2001c0022003050041442c00d81c840c3c104026124611038140c20f00381810b0a00c2c0c1c07076200c11907c2207442301340740c24940030190140c58240c0301001142000d40b644001e17058002c1400080000071 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 701888561 1250 701887311 701887357
    0x9020102152d1e101a0304212a0615140d03120b031603141c12050702031303060f05090a03051b0304050d05100f0209010203 55
    0x800810150381e16420104001d03007071001c0002038040c64000305240102d100d800071480c440781001024000d60000490000c82d0f01c0c00c40b01e00700c1400c001442c90315441c6003c80c0000d00c4021200301d002c051014003084581d01d00d41842c1074882100c2898004a407000c0c070b240c50b02c00543d00a002d00081035a041e41c0e81c00305503a40c0e840100c0d0b207040300d07000604c45420000c05007100c0d00c00419840a40f24082c40302c0c122000814240151801c03a860701078009088900e2030040003a82d64082481c070180a403c1c2d88c60480c0d000f61420850300513a00803541d0b04200b0480020b061000c0c0020040d01594489001403902901801001e13011150000c405a40e03030388002c141498020400c0741c091291141c0f0fa08151644ea00b0894028200c90312000c540b1403c1c0000a0085100855100003a82d810b440f40c03401e240e6242d0501c05e6084d1141c2918030715100402000c18a0343d100d00340214158451801081c42d803000080600070703181107104c81c1681d80e0040c0840e0030306a8020003507869600150044841a10700 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 701889811 1250 701888561 701888563
    0x20030405121204050c010e01020c131112040c0504151e0e0703020705150432010f0f0b19140102070f0308130b12040303020c010e0714010906030e060a09020102 70
    0x1015007818a28001403410740180780400014481c50080c800c0e40c40c1e283c80800151007215003110102d00680040c030414446140c070035451a02c41450100c0001d189254118000032030380000031402202040d0810081000342c03808100340900016182804031054442c00a0444000c50190143c4070302100400b048103814110400014140c070f2040c40054104110082c0082d40b04081c251198012900030b00700240c00341144901a81d031119900380310b2101c01c208081a0780780c40c1800d080b01300542c1ca220305800c80902034400900c0403507500289400300e03102c01d102120104038141c3c0c0103203030710f082c50648000c10140c4070040714a141c19880c50440340c680102c1c00d0070b0085d00720006041c010711020080c44100300c003034003e0b500d509100840c01303502c0f00701000007401082c41041c40c807050200003800080c0310b07801601401c0941e80007c12520710814030365003488442e8101105a11842680042640c0d01c0204131005080c103060820010700c00f20005c1e034640c40300508030403030309031202d03241030031648 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 701891061 1250 701889811 701889823
    0x7051009110a0b0408071a030c1b0109081b1b040203090a1502130b071e15020d0c02101103060d1406010b031b0a02190816030903120320030405 63
    0x10700910045095846150010301c50304903015030011442141c801240c40c0c0030700d022142c48650910482800c60340d03445603402e001e40c03096008007400e940307c03400f80d40050024003d000445101d450040e4441030040410a14544c0c2c1c0720507084964030070b10615506000209400031844001d83e00175a403070b40d92081d054074210307003500018101040c40c43d049014a2441d8090070030f52600030316404a807950740c0907101c080d009008015080fa240a008085104440c03075406000c40c0c0300c4c0d041c1180302108000000101c0c1c00c2400c60000c056201e44004a000350705101c07150644054080c200201c011052240c80140801080c0303d001d481e080c203406050080352240e000000036481c1c00c481496840301005a42a041a1a00c080942c03d00202c0c000b55000c41c02a14100021a4000d05080300480c0b0002e11004511009403a5504104082c1c1c0101003c803002d240c41f18041c1e120110700b9032071803610f0b4034003543d06480602058a000c1c20b0003550444d000c100a051141c0c003d2881e141e8440b424581d05000c = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 701892311 1250 701891061 701891093
    0x1c060e0f04082506050f0408040b13090603061a0a1a0c010612030914010e18070c140c0a1d010b0d0f0903030b030d020105070203091c020406060203070b090307051009 73
    0xe0030500380742200c00710446010fa032600c500400d012940b02c2e00840c2c2c2c0b003104c0a41d402044542c06000500840800750b015200b01d0003030400000441c3da480154408440707098005803900d9448061b80030100c04104101f4565000a4580095551800003e081d0300306003030300c018a0040b400141924084803d41081c07010b82190b60410003026501c0ca070142c0448803621500161842c442070101080d80079810401c0c0c0c0c81000b0f04640c02c440c03501e162030410548020250f005103c2866104000f003645486040490901e41c002800007c034100204550710484c0d511200f01c0000c071407166012151068400c904403820707025500d44800303200c0540381c040c14085004c680d91910388000c600c01c2c19459004126100307000d0b010f444101c076041004900340c90003144c0b2400546d108001416450030314816030f200302050110701d021400030790360000b000c0d50540d42c41280141e1001c00d5402c00d2044040c58680c0100ca244001d40ca4922103596482e1191802c8101d03a003070315510004a03041c8481c20015900341 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 701893561 1250 701892311 701892337
    0xd1a0112230f010f08030c030f03130c0f0801200a1b081207140304020a05120a0204050c132102040504020105071a071d0a051c05030c01021c060e0f0408 67
    0x5240c1540d8003000c0050900ca0303131944001d140700009201c0004130850340c403075450801440c5000b400d00c1c48100c180e40301410200700c520b1814128008102940c480d040a04405591404c4051070907000509681c0301a1184a00c0303065a40c4c800302150f010811902030f81c9850402d450081c0840489115046629a010300929000100c1c40100300480d42c045200d0441a25005441d082c0c101442e00d403400100d400079008012040140100e00c1c10701c09910140022108890307107503000e030380407605668007601d0443d509440440d00d06c560303c019084a031302a144110b90119a40324010f8a164002613501e00a401660341e100400e0569120740121102160008178006124018004c4400c1100b4121850b4001035141303056407021103c100201045000024440442c160518040005e2207590710240e01c2e03002a40740c040000a0f034140003400f221011800016141c600303116402d01c01c107640010300c0c040c00b071400400340120b02405410f0350b0010311040307042c105507031180340c9070f012446821400c03001 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 701894811 1250 701893561 701893631
    0x60e01170708070602030706110a0503040b10050d0803100803073903032106140f03150f152e0201060305030f130f050f190905010b0d1a0112 62
    0x4e901d0f0000010100240315a5040285800c0e016280d030240c049c5800707450001c1d10400205010a01da0b4503081d8000380e80d40a1350030100e9503600000c881d4140c400c1c0459030f60354080100b0a004403096410801000d001000e54907003410355440c07143c200c1848882407076860070402d050002c090b21810714802880d1079000031031034a4407400c02034105005040c0310303004038111400000f04280d582c041c000031107010075540c0100c1c0d00700c84100404400d0444869800d4070800c28103800d4035180d8a4001c0c040d107100e6252000c10b0a1144820040341c0c003880f0410300480c1d035107a01c0d41c14074600a88840c3c43c3c400790000c0d100200c03468001240500865440542148004540910f8000405000b0144016914030144001d5a01c0f0002100092544210342d40b2034034003020040941000c01c488442c0c0c901c130f0051074a84c40e4030b5200c0b41044403400e1700300c413440d43d5000c9205000303003100e4492000150b00c0710009200400300840000c003130040d01c0200402e07031520382900464400c03c201402a28030400c118140b0 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 701896061 1250 701894811 701894819
    0xa030615030e0d0201150612111204030f2604050f070f091d0304120c0909060f0b0f0907050901030e030301080d02070e0f01050409020d020402210a060e0117070807 72
    0x90241c2444030b0045005604500020600501c16a070960500e504902d1b40d0518040c0140c505403000f02010315079a89a0410404009009004100c0311804400c42d44c074a0426080007843d03984450904024480c8042d0f8150790500c41c04d440c48030014400d03540c141740c0c0d6604d1400c40e003003081c144800d0226114054000c940038030003042d81402e0705c2c00428108080c91300c0c809030425000d006040e000d4507410401081c043c910f51114102003143c000c510303410300780d44c0c0c413405501100c140b0681598140c1e034171000c8100c0031701c40c0e000d215031030141222000c002c03a401074001901500054102001d10000281c0070b00141d00076000300942e0708210b010b40b6241d41e521481c064890f101c2c500004018000c2070008100307064560003c42c09811180b03a2800e07940c1c00d1070b00303007c000d05105c0c2c0140e9110141c03102000c0165502e00040c0006a115210b0060f11801d24491000503d00508070707034543c03420704500340070300544100c1e0141100c4000c14401184000161001d05086642d04004200d00824801003 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 701897311 1250 701896061 701896067
    0x130801061a04142b1a420307080a02010e0402040b0a030e3901090605180a050618010e030c01052704050c04030b1026070801151e05030a080a030615 65
    0x2902c00d0004c0448441e03519801c00c9580401d906036001407422804011345a40300d4262a03070a0714901b03111084491008000000e890442e40d94042001540a424003108659005801e000610820b031001d40c20141450780920f4035000c1c0d940d0010400d6591000c146150030200700c0c0346110360425a52644150702e5012500050500d0028030302e02000f4100c1002c0c140d44212258411500955102c0341071094041c19001c2c1c125000700742681c0102c0155001c122640c4940c0100402c4000700e0310380f0000da4801c40090020502c1300c0716188203800c400c5101c440d50341c00004072010800c04e4003442000e00003110050103094588003030715400034900b0b4100503284965100800540740034110003030050f961900190089005400b4081d250b103003003860008440015443c4010b901459000e4a00890312030b51810b085400328441d5440c400320400c0c042255100740f00180d800203900801c0c00b48810f040502190751112004802800302200040c0f00c0c1a241c881d610040c050705011501a1510316654001 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 701898561 1250 701897311 701897333
    0x306030a232401050111030403120504080f1b150d050f01061803020a0b0c031908150307140d020a090e010f1d0a030305090102130801061a04142b 64
    0x1080707491141c5044480034a540c0b0a482c0c12203609010b0001d1680c0c2050011186250200850a0f00344000e07c00880001d1901050303900c18401a0f940c1501d03180f5041040d4500030184081d42070a800144141c481111380d40041002c2030016500701c83e01c0c9442031000c19140c801c115a94121a2402d0203200540700c948c4803050481d001071341c0d00c4a900c4100b42d01201d0f81c80300c03440000e5102e03452500420822010801920070490707108103403820400804103402c0c03010810203100b00000c01c0c04041003001d018020f020300140c0415802060001d0404c409035116203a06103590340701c3d4407088000f44c2150355011454001d0b005094080c040a0102482940a04100760340e4026180c24859410013150a40c0d017440100549a0004c200f014401d8030140c0c000c00014221f80340d01e54007001911000622751101c500100b81000000501c00c1c5090808004000720250082000c1030401c0f00b00100520600503c4101d4022640c00710402c0380c4c0c4400508000180c0d03c40106d00b41c0c131a402905002c0c0c1440310f = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 701899811 1250 701898561 701898623
    0x501020d0f05101d070e10030c090f060801170313030b040606050f010c0b1515031608060a03150b0409080c0607050418090212071e09110406050306030a 67
    0x1d00264452001c4080030f0512806403c0f0100c0c07030000c0d9400d2150100e0441d0360030601d5801e1080d5070760355000104903000300ca1160307032000c05e841c1d51006103120b60100c96400100501403034032130900d003401001484164103111700c46040070b101006000c0402c09000700c0e4507810405c03055155455480c64200c00111084505031a454900300000440342814500104c00f8841656405880c00880d61813000310b0304054101e4403130b80b000c0303043c1e48000c0c0c03134441c0c4c88240c0017086000c00b0340340d2408000010400c85442404810881c0040a0009548030980240c042d240e01c81e401184203034060010350001c08540320001d60180c1030000030414040e082d0b0041090720010307800d40d0002c0d51417003402c3da0248600c0c411180c003209556905078004107160f00c0440010710040450891241c0689010b24010316504009684891a4440200b5240c403040000007040301038002c0c0700320200c090b0030b11954015440b956061180000009410303035400d101080c4042e5001035203900c040c900802c41031914420b0302c0 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 701901061 1250 701899811 701899841
    0xb010602010c0c1a0a06050406060507051605010207050d0f05010c03050a0e0c0306010b0d060801020703080f16020a08030c0c06041101030e07051e030a0503220e060a061103070501020d 81
    0x742c00c0c1019840b42c1507512907550030060703000760959012042d03003440500518003000d07a5074614021565954030700410000385059511644c0380c1b0303028107045080c0300d00c03802940541c4450283c2040142d801190041c02c880c4121083c640800f05814003218964071414028650752074a808000c407250903502450060003d00d00c00c00c88000292581c699407005074030310030741c19441000100b08018280000345400c408280d808900d2030350700c40c5683e003a60030200c01100426140f00401005004582c05c00e07500c0305002d4203400305082c0c000c6001c0c2d1508a044405080804000700003148604010308803031440c81c0031000c482251070a42001003c883c000191240003c0c1042c01400c1c83c3d960000d10340c0c06564004000000011440c1e01000003500b556402c107406005001541010030030920103001204450a04d000302d0181e04114a902015030350068081c00805405003d8603848215440c420f480c81d40c1058400c2c480600c60952441c0600c800c003c10a41c00001d0810312803006401103d000041c9507 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 701902311 1250 701901061 701901071
    0x20d090504021317100f14100b090d03050408150916050330180a240e150d0212090601031a0402010c0b0408120106030e2d03070b01060201 61
    0x3008243e2041d507071110840e848030002813184a0b030052002c280703850300380b08580200300c925600900b541c201003580032210303a5034840c6154542d058400d25030f00080b892480c1d0042c0381001c404107018000d01040500552043c1001c07000c141c090740864000d0003140d41200e910340050010b1145c00c95007140c0425450080b46070701c1c494220000c00d80c1040d140c0080c060006420300e900300d80402000c003400d1a5a01c001030000045020b602001050001e02c010800020459050300707204c2d00e2501c0f940101105040d02001c640c0d0180c5891518022001601d01101120f110700d0000c0c2c0901d041186110f41d0403400105014040120ba00402c81e107022001c9800c8142e81e001a4030361a22024030000d00401d24100c1d03000003032808070300c0a99102e40b0505200e9003c240ca03480d440041070080340c0894865500140c0d02c5240d000e0090341d140105200c0c0707002e00c0032040b4181e500e0349451001382200c803210303440d5100c915800600302c1c0500c0c8544056007200c1c2c071503080d418005c01e000020b00c2400050351078a = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 701903561 1250 701902311 701902319
    0x609051504020315011404091103010f051c03050711060a020f060108010b060403080a030212130201020615130b0307030209151009121106162f030a060207051c020d09 73
    0x28029644103e002c900d0320344c4580c0903a0019144107440d415201c2c0d14400400000c220700300700b441080c035140c1d00c020409031250b040803032600006003250090b922650060130743c03540c0142c1180480643c1541841d045da12105c480c5009a250700320710813420340c070000108002d141036a0000b101c56604006404882c801d90362032000508982d004031005410100070442400071483d14001424546001d10b401868070000f202d9072440082e00340c88803003481690205801c155a81088079940046444101c0550300b0000c0001403124007504810000040d20788998030104c0d03405005080c011900036080301820714000280500039003002514500c50b040d40310300d50030903d11411091056851001d90701c03445210a40394008155095010760f03620a104224281c40f86070500c000b043c0c0c1d00c1c8560160110f44650386000e0107a001210030200c4200c44550320300c2e030284d90008000c81401e81040006a40b030700142016414400d403c00c4141420103c100b08000c210303030004c0d010441c900c459a90702c49480d25 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 701904811 1250 701903561 701903569
    0x1b0f05132306070f140a050111130b120601260408030405010c05040602060a0f061509080f28060b0604030b01080d0e010c0b06011112090a060c0302071a0d06090515 72
    0x43d0240034203400141100d240001d01036003081c0d420b200002046810707049a5503a41401c1d94003868240c204104042030702000103000d029024040c0404060040c1030884e8036221789507803c1d000300780c0e40c1042085128034405c4034101610300c0e0007103008400c0000e240380c18107140c0c01030750060368200c9442d840e0210303030307600382e0b1151090302d0540e01e8541c09003609498044407000680104100b0000413990744c100002d09100c00e2400301d80c1c13400b240d01d48240507494150010309045211b90044000c0d0071400400003e10401868007201c1c032095011594068054103111000b00b1110285a4000300b00003804000d0292804071907040342c41140459a50109105084407060400b000e0079020682c800b01881c001242d1644003580141c041c5002802079402c0c0d00810700c1d008143d114640c0180c00003170000640c0c00d283e5180e02c05003102d814100130f0b584050342c000356505240d1264004080c0282810002c001c04002101e280c4030101c0300034807149845581402c02480142e80c0c44200c442826400080303410 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 701906061 1250 701904811 701904817
    0x1f06020705190f0e15090a0504020301060f0f0909060213080307050c0109032003280308090a0506010b130302040606030b030634020115120b09011b0f05132306 70
    0x924002e001e0207260900c110708a0a014000f0f0170f01e03d010411408154031544005171140c001008082030301c0c1014014142190440e401070101c90001000600500d940702c01c0c1036080307500d4140300080094080c01c1030340003802528105000f4218980c800a0307085d43c0000030b860918015415201c40060b810010b45964003030b803000034030185002041c0c072443e1a00c10302c0b820000e60301606451510000e4081d040e0031484039000c5c0441c1c42d91190704101410b038005c49482d401a5035900400c4502000d8403483c1d503492052081c0703580b004002400010705507440800d44000d5030302410074401c864842c03d00cd0050314102c6807050180c070450f0001021440009404126520364001c040d020540c5000940d900f407200061a40a40d0740303824981150650300035504004003851800c400e4010014540904404400341c940c0c02168140802400e4003104080d40090002d028205807815610008080d9014002e040380210031440c0001d00084440d941c150050400d0704018211100c21514420084540 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 701907311 1250 701906061 701906069
    0x2011d030a15090b0c030a06060503010e060907020a0b0f042f040e031e0a0305011a040e060a03120216050d15050c040803070f0302060a0501050f091f0602070519 71
    0x2038003144059010954129281e00c003806002c0000c0390a01254032041c0d0035490a644501c80e00703000008001c00801c80d442804041c100510b002459549007040c1e0340d18500015010920409050b0f01290100c1d008101507000350798400444811494800358102003408205c0e42522001580480d11450716a1400700081c0c540043c0380c0302c4039803d03000092100034410484e041032284000c100c09031201c615100000c41d51a40c2020039540c0d4503011100a00362141a070000e00c144900e2803a82d5880c890440507107003690441c101011070303aa645400545040e00344e50001d014400310351801d000c00d9030301090100c405070000d101c203501c1541e200309200981d07800c54000f40c0007c0b01511802180262900b0464101c100070f074246042548901d00941154408102180c0042601c002c40b000c040d0103214456104910020401c10781d89080082110011000032042c0300b900d0401c001600b21b400d0061301880c3c0c1c0c50515a00640d50f40f1001c01a64a0120340a254450fa103400d401071a00103d54858401f55 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 701908561 1250 701907311 701907313
    0x506070f0e0a0518040501060819050106050f130207050307060c0e01030e030903070e1008010c050c0c010306030f060506190f030212030a050a21090c1701110a0c0203030d0e03030402011d03 83
    0x16009101c4043c01e01e81c4c054400c4650b952616400141400100a1500040d29200e5214540009440c0007030031079400e5402540640c4c4d45a10740e018a44d5201601d450b80640d008002d0391720074613490715a045100d00d150040c0300d81e01d040d1170890310982c406001c00750300c182130700c0c1000702c4000c641c0c01e01d540340106c4010301da0640c440750b818810308040d04405030708000804099000700d0f489110503400d49082013200c000080010441c2c6440100400211040c1035080c20100001401c5840f5031548900c6100040c08540d1610042040340d10f8111300c03242003805a04602c1802501d42108140d2480503200c1a0710132003103034005001d00c0340040119940b50880362582461300e803d224081d02c100008101d0017003000a0824000d82150a0740034180d40350b442014980d41c0c96050139071540c0c02101c00701404130540c1c90216034106501c402011600b0351015400d01240007121840040e04e54429124240c410a041c8440d4122521000010327502803803007620f034050442e18803003a0b0003845419502c0240c1c9 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 701909811 1250 701908561 701908579
    0x1617010e030d0c0e1338120a0606030803150303122814010e070315061d1e0f030a0f0201050f0d021b1908030a05060d0506070f0e0a05 59
    0x589545501102919035a428008912a44480082c0000d12490241501c551b198680651003a03040b5034071010102204482d0081d01140221340d10400c840091040c0c0507140083c000c00d00104100810004141e0010081c408191203160602e4243c10035141060117001421019545240100a80c0d032000b488045034155596500804052207501c5104001d10b00080b10160384a00d40078024841001c802001070003c9500d848401143c0b103d00030801001c0510300307a000001d1074065805201201c88a207020031869421400c0e146a9811409800340d0112605469030030119815840e984030500482c7c0440c3ca03188000140340d190003540c84010412803062042d80019801003000c2e140001da01503c00c2d0805042642e81012a4490f49540b03041000ca0601d6007032b001030400c002c11052604500718681d405070760b80d03034040320f00000c2c110514081c1c44000141040d2901a0807800140c6c120003202c1035802e18800c0503207968080500b81002510003601c1c400c050802084490071114054107840d2 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 701911061 1250 701909811 701909827
    0x7020405040201031413020a05010c05100e03090a09151d01060809030d0c170903040f05041a061903050114061b0f0601060e041d0c0607050307051617010e03 69
    0x240802007089040c941c1d0f800300a80e140105c80c140302d1007005203180490000d88030740100846111313a40c0c400c9041216405200b4000f683c08520b540f83c1c02140d800103e66141036411072401d43c000c104489800c41418a00003a9004050b0400003d140c0515102d034505600c5a26a026400c0c065280701c500045500c01081901d02c40c200d0710b0b41c4129001d007540c1c2400580c201d580d00752604010030400003105525480c440300b00d0118110707000030044000358500f501c2c000c0c0ca902c0d60f445a110300c42c0b0543ea074205401c4408040244078aa0401c0106119038070f04c8902c3c400c031015007840c0200c50003c2e01d001c0010854000c1c01c1c001da0000358000f03002d03504010b442d403200103000104030911491070041040700810401c0400c1048d0103402951201c010546038282840101d9003401c0c1405051112101000d07000000841d586858440c10343c1c20540d1713410141845441d602c6074203002041ca109035100409802d03288820b40003518403104120500b02c1c0000395842c01d9a07136040310b80d41c03141c02c208a000 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 701912311 1250 701911061 701911069
    0x9021302131e170124140301090b0105040e0a0c08160f2301032405030f0705100503040f05032205030610180b040f0209010e0d03090e0c160c08010f020f0702 69
    0x42c207820000f800800c2d1501d25001d41003c08803040920071041849400a1241c41e403030b03d2a542285070190002c10044400307440e001030b000018421a40190b036600755038500f4100070b00111030396680280003c4041d9a450391256a0799000100c80c0300c1150b0180c00209415048040e51012030b11620754400640700c44400042c00d208441071035906041d5581c01c2c2904018007056540143d5075a134000e26885882d007420b05041c048411440c84885d004803038144803d40e180080c00c3c0304442c1c1450b042e9280d40d1180380c00d10305140e80b0300b00941070b44404621072180b80c42c1008030340b005400f0040004c0d083e07640c42c420b0544d560001e481001005030344580500c141c1d001c0c03100041d080d000749003010800c00313100b0780814216490070340c0e0a0422a00020800d42d83d58004049004a14054a84107400c05079a140180340604e44e018202c10301a07810085078500c0170000075a80001030034054101c02055038640054a0205445000c07815420041c0c0c0a000c2461442610b82e02400000360303a00d172271358a500708 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 701913561 1250 701912311 701912339
    0x5010c03021f1b031401092705241510170702030904090f061b090e06061b1c050a09170f2e0507120f09021302131e 51
    0x849442d07a20a0850034500e5000b40c14482e83c442602e000a01070620003038410010b10503080810b1042c02d0140c180030f8151240d1100c01c0380d40399604110b0b000b04440c94100e00b0701041d04d07640c16100990052100402040c00c00c0903000c0e282c0c1880420302241400d0a000180c03241901e01c00c0403c801400c480303003401c9010941a401426032054a00d07000c202d0700003900300c641d9150f06a0b00e02030141d001da001c2055510400c0d040007411400302d034401e20b02500c002c200507030a014402070a02c182003c10003540304d19059a5002d420940c2001d0014810070790143e98400c03403403050b0420705c80704960340003490180003155003010090740c0760503040f41401501c94481c040e40000c1d44183c032401c81302d140001414400d2188000100e814040b03c4101d10004180c202919407541d42c03801d02d4403090000880c0c1061403c1460032030982e0100e00c0c540d1061201e00101031125019405c5031034024070401800315540108010f040740e008480c4030540b030343e440b019800b940c542c1c147c0c1903104001003404925102500 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 701914811 1250 701913561 701913613
    0x14010c18090e101a010e04110f16050a120e0108010503070611030c030a020a1a0108031206040902100f1d090a24030515010608130b131407030204050105010c0302 71
    0x71074078840301c14044207007241e0204414a11001c505540071113a581e00c62003030a1140d00448040c041c5000450b5401c0040c4074918802171825070000e0300784451090692000841c0b0341050a642c0311464908000301c0001e1000d809a0010705045ca0007001503002c0e02d10281a03c0b0050002c1654a0420780c06a914982c5a1040c9003144030038000c0841d042820001041e03803218560290103450054035010514200045505105800d050010f01c0303125000001d83e2200703031001c0e00c40d010a4030fa00c0c010078010a0000720194120042201c0d902d540c070f030407056000e030603c420b685410030544800c03601c001c03d085801e00c490b8440a11004250200083e403c60320080c1503e1214070000c014007001101c04c0c2015a200301c80c1c070342000311040c89100106d040a401805036042c02c01851400801c00040901004801055131103100007044c1c00c5282c071070703021182c1139100000380e19040005c1c0c84503584980c1d500c4100d100c4e50078400003241d80c2d4400c0d00ea84041c41d50580042644040d05510902c0c49100186 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 701916061 1250 701914811 701914813
    0x40b06060919050a120b0a0203101d060f04140112030e0d1a010e1312030e1609060b0a02060708130b01090f05070f140313060914010c18090e 62
    0x108070610703650381c0710701c8422002180e00080c0565291105120300c4200d60340c800280d001031010180040b810407900c26500401580005a42796550501c02d40c0701c00458208103d84100c0c5c000140ca403218600f421406241c0459920405512542c10401503c00d0355807400e0800c00c07841c0040205460480703007026090302c60f08180030420032040210f0084031444c2016501c80c0038000401807200c40292145001d4000c0f08001e00705460180c40014214000f00c00c001d10071511070441c80c5106210358080c480044402040d0784507445406000d420b080060f00401801e586442d000041505200b4101c030300003100d58029180302c0d80c07901425524400e006006851410f01107061400090429400b2400382403543c000007204086400900101c500003040d800070302c030104103420070003a0080b0346400c4003503aa41c800365480e0785080080038a8040014000c1c001ea040406600401c82c1c4081c20b40303008524640208080501c03604100c1c1c800c07122030812040300091203810721404400c0e402810810300d03464 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 701917311 1250 701916061 701916067
    0xf0b04060806041d2812082e0302011107030c0e1506041223071503020c01091101020f0d12090201030e0a060f0b19090506120d0509091e040b0606 64
    0x70410011a040d11402881035170800100d84404031062080d0140464140614202101e2242d40306081900c2000203142031006043c00500c0301800743c680308251142d01d07400e094241040540503880080306010490225403000d4107000340490018007030044030b4000c8804111549426032003500c47c48040e00704621340c40f0400e14002151110001040140020701140c1380c0740400782005080900c40d0398a02c0310302d02c1203030000096840005804400e54501448540422244490560003407003800809144e07035003041941e1081c05480071243d0001002a025942501007000704540c4070081c1212210114590065850911205a020700b6049206040c001007032020000b800b40f51070125207003100c1d000d4841404417120300e0113006d51000008281e40000302c985104800d942c560529025681c541075a40740022a580e50b1000c904100103880400c2c0c800084042d0402010780d031280c8903c40c040c5210714042039100c0004800201002d070b445506c00d1007602d8030342c0e8a1900110282138036a2043d418 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 701918561 1250 701917311 701917331
    0xa021b06010609030c171f2007022418041427070e04080705071503020c010c1b0f0201030b1504050a08062203020a080d14010f0b0406080604 62
    0x10848036002e00880e8030b42d988214034520b05101e924132150450b001d40c0504090b00740e460040007c03083d07840303001e4907014003000740302c220a00020620082c02c4490404891400814851000c1c001d1004600030341c0c10400c40c141d000c946084201c1501e0603515112001c00544086400440d41456490001000441e030035010000c0c2480c00c0b507084e500c200c070032a041c120040007200c40c0c40d007203100e0344d081c000548031162601d8034503410807200400160816500203140010410b0074003001000d08600c6030004402c400d4040000c000390044030900d0350329883c0010b84070126005070803218203000084081442c51900e07544030401a1030045003281427684612a00b9000d6a41d01d114803502880c0e00c100588483c900b50801c840d5001941c424040da80122050068060710000d400342c0d8002d4059a5050804d0300c1d20b000c9280044001015004840105840520a11036000b85203200102c0e015480c0382c1c0d8854030382210f210203512484060f0340c020482001803d00801d8410380c00345000700300082e20110 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 701919811 1250 701918561 701918563
    0x18061b050c28061419050105010f1112120a05060f0d080c16141309020108041b0e0c0316111e0c03010f0e060a060305030901120902030a0516060302030f0a021b 70
    0x38140d0404101c01c07444d020004000c5c540d100303041c0701c40861001400554502400078203081405440803040010703c140c103641d412010000d10710340f08190000036544076a0042452054541138800c2e204503070600300032420a00d400c403403001c280513004000018450303040d902d800d9243d00450640d82180944803503010144041c0200c6002841d2003a01c07038400c0592a001c00040004010303485040700d02d84048540940d90042c06260b0103a84034058810382180e000c1c0d03890341c9015650010b50324140207070030444e640003403901560040303030032074603a84950582c0d4105a03080074210711000b906178441001c184102201007100c45000b12420151160100d040000c207094136480b04104000c4c9840307070081c1409841c10408036510056181040111608680c4c42c207889204668207507040000c0c5030740500300d4110310f03803112454582c010121451010180340254649018100345841e0761002540041e00311700038001c0343d10507020350b1000e1201d650340348440c2d0003d41013804d002521030001d2000c00345100c0 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 701921061 1250 701919811 701919821
    0x30a09020a0f06020111041503020c19061a030a03020c04200721050f04090c031d0703170a0c0f03050c0a0b09060a0908090f0418061b050c2806 63
    0x1103502c00c01000606049010b403e558a00324000900c0c901003100300106c00d118190400d440030765240140e502c0c01307010070051505c0110090b919521a4402d620404c200b01c0f41d12101541c00c802c000b00c9000007044042644900b460303036024000d030b08150194030403450107510042e400c3c0002d5181e032040130300c01c4044809503040350008a0340c500d014045556559100a11203102c10020314149103820380d0600e508026004503c07510304919141d0703400b01d00700c41c0a5041200c1d40c04001003a060110321000b0060798036045480295040c40e02c0c07100b603028200300c040c01c5940443c40f98440c042005616a50302e05600011501541001018440c50000c80c80c14000c070004140200c0200d9010304281c6c5045050a50280410a10a150009420000700c0d15000d49480240c2180e6181d1074122040110f0013030b103001a505036907035084220000402013075501c00381040c2c0745d070420344002c0030840c2070548051081ca184c599031903100d2447d1f00c1801000000d603e001140900340400c01100e142c0d18442928 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 701922311 1250 701921061 701921069
    0x60307080f0f011d0a150209040504080a031a0609090a020f0714010c0c120e0f0a15090e01030b040f110603070908190c1a070f05010902120c0a0b030a09020a 69
    0x140050b00d952002010034010903040c26403038007000b54901c902c80c40495552034040002484494801222000010b041c4d0603600e0307a80700a0001d200600c0c00340b0705211a68040c3c08074070b010900d403110504055828000000c10301c81d010746050701e00446d00703003001541c5800810312140c06808201820081420201400015214980003254040040c0c1a17900b13440c1c0c00c691743c0040240302c011070702c0072407100d600d110b0390100c0b281409009a05034401103512041c2d000030b495000041c04000282001103c01090314030318190b038400c441a40c03034136022042000203110180c01110058003060208d48803490300e8641c1407082548807400741d03041c0c000c1903035a04100c8460021a80402040110000900000d6081c03040303410584034010341e07076603501d0a4400900900421030a030f08284441d110580b13081b103807081d40000d200400d44400340f91050207015141c4049018800e0300c142110b0480380002c80e2a13102c080100001e03800c50514603905642e40008069085054940c602100583c44401c0100064 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 701923561 1250 701922311 701922313
    0xc18060a0804021c0f02010e19030506150103150b09060706060b03040311030702030d110a05061006110f0312040807150e06131707020a0f06080126060f060307080f 72
    0x2403400340100f0072007544c103c2c0344c0c084a24128550030006154131800301422a42400d112901042a0380824400011036103201280e01e4800d902001b44207001403001d200b04d21301014a05181c000100440035561400c4941001c1c000840003032160300849800340414020140c52300381090f241c2d48500c420340d000ca074001c2941d0b0f0b10010900040c0b6030300c0241148401c0c215402145458503a902082c1d40d02940d030080c1c41004110424100c5400c001d01881840c0381c0c01104076a801e041548500c1c031580b14a21507000810f8014030140e40388100800c4078600340f4821000b450900c80340700b0303146042560042007140e250400b00040d0300002d10390804c21448401900e40040c0c01003001018625140d005000300d1880f0291529520000e11241007000b0000c61108440380c42e145a88045040c03200a03411030034800340000d00206003035030302011542c100c940c1c040c540003403001018003010200d00c41c090f41242c103800032230004819482902c0d4007604100040d044400c025a5600024181164188681a1 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 701924811 1250 701923561 701923577
    0x91515070302010b010e06120901020d1e2406030b0d020d061a090613110c071d0c0a0e0d031418040605030f150403020c041407030e01140c18060a 64
    0x1d01d9070902c0b50201000003824903c01c40c6a40100260b0307580a14891088000744190010342d49035000c0d0140c85040350390103414041c07807000c41c0c51000056403540341400f1652801045501c840c00601c2042d504030b0380d2105d594402030800b98204c02510710710791030f01d4020505910380c00068032000244a840c41c0619800500c401c180d00c40303410f1403400076540601c114489000c2c0007140e0744002d4502c0e038403a0a0790000528080e450019812230050342c1c46d511050140b07510018000340c0894140c042860b8140851207103551303c460230750041c05a01e00150000398100c106420606215103068009070007801c0c004c9000704903218804855114000c0700c0b200c048051a1800c2da41000e01030200034000440142412100c4204800d070f80740c0c0d0440c00213107132405d200d001c5030038180244845028003002038028080913244980300218444140c8400000a24164503288850818419841070303a018980c100d11580380daa80501c1280c00c9030f061413089444401d00444103964a9004101111860300ca50365 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 701926061 1250 701924811 701924813
    0x30e03150a05100305030406051303020a0b0a120218301605040e0309060f04031b0303110f1e280c05090103030e011202040b0307031413050c09151507 66
    0x1d448001c0c03c00c240303468a5020a00018401100b82c070140c079041c0c9010340d181d0403140c40021408485900280d0041443c10021400320b0300c1400034100150240ca509210b94a0942e2800407845074005ca5a00600130001541c0e003482e0520b05000ea016414603c0d10102001003294075000480020b8440c140d88904511024070051001c800014403040f60301300700354091007040356100c1c030849000c40d100c0c84000a1070040320f401401030350701958125113041d4020070f0400310300c0c603980e483d0f01068000c285440501c4101100004034010607840c0f000140031f007001e00c45070404604d0341c1036240041d03030700540850b540000952840c101c0100001d10151085207050700b04113041250300c1d0441030140090030014070110b03800840e17060402c10280b80110ba00c005228180009028035040000400000028895610780c56006100d91041d00820311300240c40340440c0c50b0301c00c104e802e0300410342c0d0018011500c0d20701e09080d003564031680ea901603940140a80d000680a102400200090407501060440c = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 701927311 1250 701926061 701926081
    0x3010f050f011214180c01090e0612030a09082a0d0326011502030f0f0702130608010b04151505091c0302061e01050609130603020402030a060302041a0d02010c030e0315 74
    0x40c40a29000b001d805105402c06c0001c1044000b4000d10341aa00000041461915500c160428100401041d00c8d180e8000360350041c030440361841140c207a8403a00b180d940003469182c0217000310740d01242c076604040313040c135040c44000c003401003040c1d0230312421040d150000c9100004d0300300b188410040403419981080f400103003e640100000e011135200340b040c0010607031064111414241202c1c4650345450f2079200180d19a1344003002c0e03a00752410040001481e59054003d08000041164140444180d8000304031140300588112072207030388031b01c1009150b14050300003410401c50180040055444803c1c01005160120340f0440051348008100014a2051540d600c0c0011103903041900d25454040040d00300c1c00f850302110322482142c41c0001c08005d0360f61005c03008581c06007096441c3c0c9001007201004011604c13059006604250031842290304c01d42000030035660080070088802184e400450310014011012800d00480180504090303a042124100f02c0d24028040301543c686a1245 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 701928561 1250 701927311 701927341
    0x31e0e01020c12091008090c03150105030c1504050d1e08040602150106020616020a1a1605072003150c07120819050903040b0403140105060603010f050f011214 70
    0x110031451010300107103c0030381d540040031340390130b0b060314000686444911f80700d07040588000d0060380c144585071a50075480301017915641203540c210103880d040d401c1042800340c1c0b907410170000e002c0c403142044184a903151a01187d102c1c2e40c02104400c0c040e1840e50740f00310281090030310548490001007010407030a5410044030002d80003507003c0d00d100394544000a55a0500906951101e00380000e084200303a208000382c0d00d0858216215001d11524044074120b1030005990002c200c5491811003e2064020421514001e51008825004865425202610301125500190300d401117603007442d039203510001014040c2942900159641002d85070003eaa0281d4000c48010300911008004c401c41d05411525031040c825000807480d40e40c0e03216091304503c41e1b50000c00c00405c002c9404014410044440c041c0068154000c01241e00c0350f10030001b07171340400d00c902e98441500901c103101030b0604030079204010700181040301c0d85003654510345041e6010055408040b502040070000c0542d049154 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 701929811 1250 701928561 701928583
    0x105040606061404030201031d031305030712210e06041d06120c1e040e06010f0f050a0b0a0e0a061e05091302180d0b01061404060c0201031e0e01020c 66
    0x10f051902602c80c120301c1140a01d00c00a0305256407601003441c0110503151444103130542d001074030f940e2140c042e0307010303440c00d07050103690700911624501041130240300507444050390308a1a134280c07481086460500000d03192609500700039031300400c2d02240d1143d2000d4406405020524086440345400044108000910591150842c54400c402186001c40c80b803c00c000107988a03520307658010b003800c1c0c010145d40165a009032402c03003645520701c00400d8040c162004400c071820074075900d00c140c140f0300010340129948005e01407001c110785415640101450101030502c80c103c1c105910004112500550240b07001c6169200c400c0740104d600c1e00b801b80780c880395007441030420045001203864412518a6601140ea001486140800c6086004945400003d100b014020720034a0002c041c0740080c40b840303010450050070f8600015443c0c0542d4242c0e085030b901d041035414031760011030103801c201400c02d001c2e02440003002003900c1e081c05509000d41c250f400159513407482c800410300d0403c036060 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 701931061 1250 701929811 701929817
    0x40804090e061f0e16030905062403030406170711010c050714060705160804090906020c0f07060c0303050a020d050c0421080d0506012c0906030a0b16090512010504060606 75
    0x3001d00c21010f410b180180c005c03003ca52400c91a0ba0383d400150010450110003801034800d00b0104042200394103207006c14450741e5010f10003540150400c5c555603014500074580032850246916a4400342c01608503840780e52860b0121070500c1140809086a403601503010009100107070900078001503403410034160b80e12100815442c0740c1300700028414003401d00b01c400c04c1700c1c0e044401414451a501a10060004881c003001005240e291140082d8803003c07803000075002301d810321180c1140225015040384c6007034072030140c0851150390490090034000c00f202c0340c2c02c2c5c0c00d1110205e00381c0705103d818400c9180c500c0940d610781c10600c596a4618655580d01c80f400390902810002403180820b5840a03881d00310049200d0b111140141c403e80c085103100c400d620651490040b02110100e042094070b1410b551040c800e889660070305840d04a55a4068102c0c018000810030040b500031020b0346c590120b1400b201a59250000204200d04000300480341d69140c40901083c006644980ca0042405003 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 701932311 1250 701931061 701931121
    0xb2e03020f220b01020f03210c040e0f0a0608011409100b0310090206040302060310051305071b030905060703080414010b01230409051f060e01090905040804090e06 72
    0x85800404407922071800796090b42c58880e8403d45900030003550292407041826280c50301509a85881d055004180c14400c1c9034200000c5203d100d4004100c1d425501600c3c00690b031030380d428403207030106140500900c850030703500c00d000280da55007841032805030f6a00031031f0014142400f0074000e1404090758a40004141b41071070b074102e66a00055005450f2541c0c103c0401d180e00c1d00c4c0001a00c0303000d142e00c040c1d00407100200308401680d65101d210700b45c3e101210341c1c00c0901013500d030171411500100c0f40ca9010488400c20085416503040550503c40d04c00d140c0801c50985440c082070040c1c01001044000c103901409010821980140030200075810310020800d00070910f0008000c00d07800d12400b87c0302d4004070001c0c110b084a56044401401044800f0300c00e90030050300717240d003080c031140303000300040a070903000b140e054401c08001940b050140c0d111810107081c001e502c00280310207403080341c103003404000c00592034801c0c0c010100030b00240c2d070150407285442440300c4150340085c500200c6d11003040e = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 701933561 1250 701932311 701932339
    0x2010f0e0d11031c05070c060309030509060c21091c0c0303110c1c0501050702010b1f030e0109050102031015050a050a050c07030b0105030c090c070b2e03020f 70
    0x44030103120780e00110b904110201680201c0c1c181342c041a0402c079841c030340f4600c18160541000050803418452400340b40615500c0c00100d084510080b070080000b0070400c40041c280c5441d401608000e482d8209440e6003c2800b001c100c0844d6000040081d110400315a0004a01c1e140c241e2031040300c1c0c0345441d83d04034602035842c1d00b0314426030f000c0141030205e20a40580c14a404011080401c407000d00541c0103120003843c165070401a03190100d8642d07080000042c1124810701400c880e805014100990a00e42e5a24088210400002140405507901c0c03030464051024003e0f440c11034000d6000503500d042040c5402511841d80d00710104501086e9030440d10580e0010845062501600d86076490701c101400460301340c410820900050321a038800802407110089841d4102d8008a0031290f104014030b041c098851000c07500310344066002d000341800728880300c40241d4015601c072800301c14900a101030007000c144506240c3c43c2c00d552a0400d00460820001ea02e02c803500c00c6410f542da0020b1 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 701934811 1250 701933561 701933569
    0x9030c3007153212150108010311010e061206030705090705070204050604090203031c0b030a202b1112060414030f04060206061309020d170d0606080402010f0e 70
    0x2405481d404110110044030ba890000c44620800d840d01d4000c103d940300b802c444042c4807a001070f100402803607420004520042c0f0300c80e0403a1860729068546000a07861911000340351540300806074141320015480c102543c3d140c00040c2261f01d03818003008a81c1c2008001d1528108044d0030541c0a03040702001d00c030140741c0240030388240d00d504960105056840c1c41c04100a40300c100300c000e4151101103000c80305205c44c071302910726502d0b61038010054840a0420943d03200b064010140412040c2e041c200002d0b004c1e81c030030191140010301568a0607002400103240700e035080140e07060181c4000e404804200c003d00002200302070446002002c2c0c404100c049403a0540a000140b0303000110342c811440200c04d00c182d0340740361491455151143d9440310f02944654003200c0d03d601c541c00e0b0103140140c2410300d10510080c0e030340151440d01c0d29034803030b90b03031010b40c822904c1010500c3c00103221002c42d104031801a000500a961f07205501810203200141215400301c0c42c8000f4005c0000701440140c503 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 701936061 1250 701934811 701934839
    0x40803040e190507141e040b0306041514060714190c0509010f091a13090506010f0b03180f1b090f0c16020f090a0c120e0304060509030c3007 62
    0x4174140140d656111501c820501d0f260356196186007001000c0f4000504141c12806544200d80c252010f110075101686c03408010600c500405d041103c1c45500002c403400c10002400075070f407044403205141d44030107400b985031814001800170f042c8049281c0000b04812880c0440003800c0543d014070319035040c04111801a052030046500326a80c407124445d40d180b1001030000c010358040c002c419042c1c50305002a0181402c11020303100d920961000003079054183d0540400c8611007010350342191611080070b41d0090014070307006500d110f40e03413161192480501405000c408203100d0109102c841006000142c030f030040503e036554910780108001c12034170808890a03151800041030f600341e4513200091104040c03a0301260092000307001c01100500ca030b03202882094454890b140d604402e55000c205a0324812440c0d051900180410003216000d9000751201c02401025504181a032030f000c201c01007819203990f8000042c8415000b990384000720b85201c03055440e4081c5c0405420314030002d0b114a = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 701937311 1250 701936061 701936087
    0x50307061706060d0f1104080d020a050d0e0d1203230915070302040902040b0a0318050a0f240b0a0503011103010e0601140f04150c1214040803040e190507 68
    0x1c00000b0003a0030307445545d02003609101190300410203521060300400c01900580a081100d204401c240c10701c2a00005034000103030740c842c004000310600b0389c1e01156061207210450b034100b4245650740d030000b04c4103440b07014940050368001605410034921000b0010081e103070000c00818041c03d110441201050074241401c241ea07403280c098950240450083c403030303a4000d2039028400300d8089500450382000f0030014003995828894000320b60304010f607020b41c002009201b90b010010302400122484013900021303000b12080410499460404d8400e2003e8030400d04800381d031141d81000a203401c00c112000344c40c00b900200200c55503400c0c440c0041c0301c180101c0e1802160703000055050783c41130141042d9040704c5e650081c2c82d405c00d440d84c1c5209410500a140805068001038400d031b5220705101e00216800141a82007011146401c0d5000400700000c000d41c008100004540b80310200000c0005080b0f8400144991805568691580c2c04c070ba8942c1d500d540c2441e045c4100140c0c00580d00000c1 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 701938561 1250 701937311 701937319
    0x1120903050a03240b040f090c09141f0203090114040f06110a120c031b0b011206110c0f0f01020304080f0a0e100c3302090406050a030b01050307061706 67
    0x4038400d1003c14120365120900700f1350944c0318540441d000790014054001c940c080c010903216603440b207038980140c4090f050303403e0025454040c2008540080e400d12004220050190300388403222081c29141c454000d1003042c0944d100181840c030700c0d41d101d5a041e400311301407001c0310f00b061309000c2c0502c00480d4502c83c1c0b03001c00820600c3c4c1da4903e841800a4002d0030317409160001c0b1800ba0718030180902c40b89200940210f00c42c20640b96055403404612002c0c2940030904090fa40e00f0620724104902c484c80c0143e072040c1e524080814284010001480d101c24003100506600c00d8080e506441d000e0312010200e010b074014001d100008074810281d80c8480e0300c00554030703105c80046800315008000401c8043e44111410251b207822500311031003540c031a00401101003e10018090850f0074401401c4001d514000998049034480c41d50303020744802d43c8014008240903640d20005250b040700340d00141d40110601004010030314040203020b000384840e0405442e101d008111002034564024441402 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 701939811 1250 701938561 701938571
    0x30b031608100f0e190309080106121707060f05190b092a03011d06120a11060d02030a0b01030510141504080102181311180a03150b01120903050a03 65
    0xe141d4544c00120f070302c903440c0c0201d9000e4905022030290700582c0c003105030b010072a11b4101186040040c05003009031804801e5040440c2029a10b40b50b100728907d0020801440c14092a40015102d00890720130480300d42000c1384a0504800034014650a4003000308a189004801c0c103483d240c0240c00e41c0d100c4003070800c00145110301800c0c05c088501c1c1c0030201e265018000700108a9004004002d01d417212240101c1c1e0440d940d8a0612600e0100382000348000c0d070248042100054481d40305034410240075203500c3c00c0040c542e2012003640c009581215110f5150a600032aa5a0512a00340c1c0450b9101c4024440c1c2d00d410412a082c2c2c001c41a00c50051000003913a000d00300d100030440f0b00030318140000319035858074040000c580c1d070750010a071841804862444200041d0500030260b0041c4425852403070041ca083c0250250032034551620342024184c034000001c54104804648070188078900810042d100c40d0004280084540c2c0120402d45001c0b203110104c0d42c00416503440004604000034 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 701941061 1250 701939811 701939831
    0x30c03081305090a1410030839070e0618040b0c090a030302010e100606020c09130f0b100e1006050d0f05130203070b0306031f0b060703030b03160810 66
    0x10614841d801a9070440038600c01e2050070f90003540070210b081701402e8150b80c2074841c010260079610035448090102d4400f840302507480284248006080c1484142901151020145280442e0401e0740910380c99009140304100d100e09440c2c1c0b0a50240c03048540c0040a4010070704001c0800c809070010f020040e0400020303680d588002c0480b10b00750002004400c2d41e540c0ca1074020f003c2c1c03840c00c44400341409144803c4020948078082d1354160b034050307006020f00200c420f042c0711f48041d00a01c1340c41c1302c0d4030000349070b00404c01300c0d00c0c11400d1501400788910308d8603040c1e2164806550075880b480990020004101552030003566260548581d454411b548040200d651000741c1405500413805603c0e0001740304d45420ba080c40740d03a000d07100b5030584040d2580d030021030001d17000854006402da0410480c6000310111031144040c6001c81c040d00003030043e0900c0200726190860941200030981d079411441141c035003004490701c1d0400d0302c59001049420040540e45452080340001681512255415 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 701942311 1250 701941061 701941087
    0x1506030d051e04030f030e0f01050301170a0f08030f090304030302030d0903170a0c02011104050306010b0c03120702010501052e030e010b04021204020103180506040b0c0d0c030f0c0306030c0308 85
    0x804040c2c08240e0036495548a04103140c440080e5441140811000324451140e8146008500c0c42400141c4400d42140e1800c40b01c6010b0000c0c05c132209045000c1c8980550018900e805d070001a14003845c0020307100c1c5000001e500c1464009458800d4a62040c001080000d50000488000c581410004281c0c0074803072500b81c1d12a43c030700b000004445040b80401443e548298880701d44800309a0003031050035011542058148101d004040d00341e000a0018054a080d010084c03601b81007900441c1d1500f070101c00503d015100568120005035100c0d00100654a04079454002d8001c00841481c0d4103141c207103c1c0120504054400020316403034008200c0b4498080d404812040c0c2c018006655401210388002d00070070303003114101c2c0824030703000b100e51003820301041c1c400b21558020300034021074a458503034000065000340885041c5000b04400c0782560000d004080e404034880e100850108011441d5030240d03200c03018440201860a01e0400c04520540c0701b800450350002d007469590040f14402e0 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 701943561 1250 701942311 701942347
    0x31f0c0c061e0f0908040b1819030b060907050a12020904090b060406090b0d0609020a0f08150a1509090203011404030c0c0f050603040303050603070314010204081506030d05 76
    0x1510140c50300d1074128150403844070710820711420710b40812880005070103c0086811001015009032028081401907100f48401014400105010313009141c0c800c0b00007620039155013096440080100740c1c104100032050000680040c001c0b224080c8900d842c030070007801c034001c1d617091000304100350b0038601004500b41c0c1103401c0c0e030344050b0041c80040503e090601003840c055540c1409503141900001c1c0016261041c0040c0c4107000340703e00440e5200b5112080900651f50007070f6800680d0711000680d58040030390b89130080c00114094540c071840c501c0040d8504030003d148101450924a48006c140c0c80d030a80003041d20417203c400959a40140046401003150111384005400410706110038182c00c03101c04401644116000b8400f0340d120011a5035003c0f0381d10500d5006242400071400290085d0442a4001d1000d41107851244d0b407600d448070440401c0600c80340603540000c090180130014010309000500301108094503041c0f034404659102c00347e0f8000410480c0210b8104c03500a001404 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 701944811 1250 701943561 701943563
    0xd0203340210050c1605010e0603041b14030115060f1803050316230303060609060c06041401060501030605090c0307020709090305280804120207030b040b070e031f0c0c 74
    0x151804035010b00c1c00c054070903484000841400d00c43d01d000f03c01c02e034601c0b0f82c1d01010703680181d403045606900c4000b400304a4001401c11605421003e03402b2504000f985103d6008060a403480c81ea660001406e06003100e0081030701122845601c10b00f4080d09130400e100d00d0342110640761101c0c0c01c0b102c0c492803088a100940005055000c0001d0020303030034100303460700d50302030b030280c1c1100010083d0207107460a003a091851001058006000181b034134075120019110403030b005442e541c5800c401030070403420580112022130308400310f4180361051007000d04c280c8029080c00c0c01d0401a8905000001c1c10150004040481c8280008002490184240304407402810b800c141484091014a4040d0041e0440703105207000000d05040091440c500480301132000c012a168562261681e4550000c00340503004800c055100704400040000c1000340014401e40c0503071001c100d50306003c200200903500f680c990320312a1384051080542000d02d030307607805164640208001580131032046c003501d004c004190 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 701946061 1250 701944811 701944819
    0x51611010f021930050c0c06070c0b0604020c0c04050901020702031b03010c09050607120203090a06081b04030302340303120b060f0f0319020712020d02033402 70
    0x350400712030f80304641d0008440f0b541e1311101d511301601c640c2210a0445061103442c03040c20f0100200a018643c2d00035078200484040007464800c110200500d410020b4441c100011486409030b03040c4146000c2c05501328500715019458210300642595407020700d425054841c2d43d880340401d050000c00d6040341d1000c0c0d4040c00b038070243d464070104480d2500700a25814025400d0110001a4034400c00040c41a10b80c0141018100b0116481e44400d65418440850540c4400c210160466403a041940000c0945994500031441d0a41d604060714925a4940d0074451040c4070904c0001d030040340f02c202c50000d90801c40d45003004405031100004003a07c100080d4901038102001b450340c000c901c0c141c50321401000380f003280070300c0c0140300c0603110b00301d0110b91400c0300b40300c03004c12400890010358100c007440c0c0a0480481d54508140304a80c01100d003110414910a00603590f21340600c05070b01241c0c1113001841c21b0a880d2340071041040c0d0385420740c40906039182ca250b0659140c190581410f00d402074 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 701947311 1250 701946061 701946067
    0xf11072a120303050a0b0a0b090d05120d1a0303120a090b010e240108070311041716060e0f0d051e010606020c06030603030403170c100b0a09051611010f02 68
    0x2107400c0700120381222040c0d002a06242c001180319695000307510159101070800d04000346080c1c240c0c81e49410a18000303a00903003600b6120013040c410001e401b040c0c9007000b01140e44031000c0704c03500c088030075a0750145c4807008008148050380d50048140da44c0e540c84040840d11596a46076500d00901c1c0e03014004004244034000454585210b402180c400c1d51500d0700c4018408050300480c1c05191541007882c00142c0030000204401c0c8a0b070410a000401c01c81d002c0e08060304d5080604c840712030702504503244e50055a0a0800b81000101c2c0070041c1030504040c24000080000308205ea4400660a1b0081c0556203502c42080b408100c402903040b600d01c10440c0d0700a01c41c07a202d011703154900c240d00041c46508038507880da26000085a0141400500031440c261440e40c0d1628140b503101c828040c1c0c010305004040000009204084c1e08884031013001030301364010b8040207000021500458441c0d49414100130038106803c82117154031442e42044001e0029601c071a03800360140046941100b8004 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 701948561 1250 701947311 701947319
    0x903030403060905070501091d0601030b270603120406020309150412030801170d050910021c02010e06071119050c0d0b0f07031404030804020a0506031503010f11072a 73
    0x45141800d4406c01d07607400b0b042d16034509840d40c103103038070b081c501800c290940d0100303003103600030780c428601400042d01104403400d139000e0031410b4040c51210a00000e080a0410405140a0048a1100384941007450030b080c02c001000b503880c010113200f1809800340c520403160603040201900c000301005203441d07844900030b2800802d80d14003072140d0b100c281d18042c40020045800705000e80c0303c40307245da10796003000300d085c080081d100352125410341940035440b0380620105288061820b030071040c0d00081440c641d2201c0440c5000c030300512401c02c0003150082d0450401000c40c1c03070341051a06c0c0d48048403045d000e041c0242001a0424150f070321003856800c1e5801c001e103084805201350144000f12103241d440d5030b003e0701900d01580000b9400c1c000580054000381c040d9101582250000e03080208080d290004139603140e000743c030f0208501c11500c980341c00c1454240a0032150b003240800034032103643e05080019a07409141740003059881e074001c1c54001c40c00d005d00c0c0c0074000c1d5000040d14485641e1 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 701949811 1250 701948561 701948563
    0x3112101062c101503060b1b010c081608100f06170a05010605192106180c051c02190903061a150a0216090c021203010807050d02040e061815010308040b0903030403060905 75
    0x340c00d2311b1f40c90725424804c9201c4143d001300380452040c4800c1e8511141e00c401d0b130748100c800307800051950340310b89480000414081c08200c0700c100130300319030307200c112040300c0c0391040c4152804010300303c0491509000050150340c1c0d000701958101c545a071010542011119400d80b100c101c040e80011500010305856460880e0b41c1e0441c9088808010034401c00d800d6400320b84041d1508407071000d01256081104540d080030b094080c00c0c074201c1c0750328014240840804100e052a48001c22900041c0b10144184144402882040e4400c10075004100b03900c511100030984c61038070310210b078808810100340b554a40c0d00030300c03004410007003401180082540325441c81008040c1759034140e005215261440da41900a5411241071310b100800805946260104100d0420740c1d480e422600035868880c02d4801c4a010010140030703074500f10700c500f0081b0604a0b035078a07205241e00d100304d4070602c0b0001080403400d010121000d5545c400f107410b5641401c9000700e0700d5480349610003040d41c6d152880c40c0b0f0600070 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 701951061 1250 701949811 701949847
    0xc210a0506180106050306010b0a090b1c0e0f151f0306020d1808040902070f020613170d08041e0c080c04110403112101062c101503060b 60
    0x1441403010491000c050a43e00700d41003401443d405a008200505c14200c442000e00b001442c180344c54503605d904c840003e14150800303107081c4015420b0001c0079841c4001070160711040825400140303101e010b40f01603503584142c8055030030740c030034081000700303048441000b10111104040e02c11011070558038a0040000d41c030110b42948400e2516014203011503014003884030180d0058030890030702d4200340700d10009511a00044031042803540c11140141c8a8001801803800c00c0c92032000c44c00c0c40d01054425000e14010b141000c1d0300503a41d0101c1260300714244503003280e0004010030b10507040444400302e07200300160140964662660008164000280c482d103241000d84080c020005040c1803180c060046010040c800c4641610f46402c0c3d04203134080325100c400354211440c4040010880500710303015030708408814582102c5d080e950013281c1e51b4504a903844d00c13075105503902e0040d030301c12034031040b40c09200e400715005c002e07075558207110741c0001c1c0c00307004000307072050362400000c0b03118800e29 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 701952311 1250 701951061 701951071
    0x30201031d0a0f211d0d1205031009090302100c081306020c0c0d080d0b030d080415060504110c12090a030305210112030210050405030a0309020303160c051e030c210a0506 75
    0x140c005ca05500b0900340103944103c130325032102030380c0d0321a9039030032040d2000e41004000c2c0c915003030f80340d1002449ca05c45010310b6001c0e50098000d421200c242d403100009540341c42000d0743c2480003000174400010f0780b90704101c410542001e4010b031500b0b03441c00207900b03054030b041038241e000103169004010320081200170002e004010404002c03640d103000c05d164680c1d07107011000000c40c04901c00500440d0410112104010072245d001580c0d945550004003200c01240654540541c0828440305590003008110408080301051908000c17881d80011000807407400011b0401201103100000e5400341202c1101c80315004600061568440141243d400d187d500203a0052054150351309014060340f0825000da0303040006585040310400f025400740c41120703c03c98161000300007012138481c00e560880c0d00c80e44111440000785103440d0402503110f8120344001c804c42e0001d030301c0481c2d55900048025042c00181c40c10200401208004072603224542200d2502d03000d480da03460100600401c04521032 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 701953561 1250 701952311 701952347
    0x70c030210180603090506071b0b090f0114040c1a0d050915071e0305100506030405010c140a020304090c03110a030f0510050d170408030a0306030201031d0a0f21 71
    0x60f0b6541000300c00f130b90189031000c0d00c244c1188010a04d917501c1a03055034881d05464444142c000002c4c0d5540644620484608005410443c3c1c50820182c082c010101003e5081c03240392107030b04103501c908200d1086403199203040580c0a80444a64100009490486000b039504114034038207640807507140da4040d2006036920b4642c000141c0f4580c0580d1041e010502d9506d80f100c11119840800e030001c01000d080c80603220707035001c400a00c45c0e962030000c2d4811845080007090b00c541107072001c0d1403885810000242c154061019200d616400400e80342102c0313000d900131031807080c1418182d006051101c50030b040c0c0c1c400040c040e007050b41c01d50090000c2c05402d0708208059690707110307420f03035068840c020168085030441240d004903440400c07040401304980e01c5546000da40d1441149180d104c0f07081d000119490304000c000f0741da01442086902d051b042c90320409450380c40d5520751550a121001425001040c518505010441003003c80c000d0010305904070040c00424060201c8a00c81d202800d5 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 701954811 1250 701953561 701953607
    0x60108160b070b421c02061804150b0c161226041e0911040501110a0605070e0a050616080309030909010308040312180b070c030210 58
    0x1821401c0c1084480d542e4104440090a489000e0380500105544003a507040e0140c19544c60395580c90b03150540702c0f211070381c9442d42001c814801840120354030a156840c0b056804a810030158841004845950111000002071441138400103002054041500885420b0010000c80c0110144008280f03129040c01110661441c13123602c80e540c005e071801130102442d0068100e4001401c042c2ca88000640d0030104680e1b843c401c0090060241c020307074040c02119403c40c3e400c180f404810a20319015001300c42092104000346070704460284100e22905040001086000880f09011b100b803c81903940000306008500740081c0080204403803188041c4074113a44540001e0501c3d040003114401100c90480c1e180032922034550002a8000030000b050501040141000c0d03507a8070003265020f544207040032600d9900f9800c0c000ca52a2072038201c0d1081c0300c14900d8254900381665a40c204550b00a0242c994401041c41c09200320725450344003d4100c44405c1c00f0302d00b4941c212a82084245905c0e40080c0 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 701956061 1250 701954811 701954819
    0x1806072a0c0b0922060f0e040b060904030e030d0f090b071203050621011406040b0a0b0c03040b0d1a1c021309080c01140106020a08040510020f06010816 67
    0xa40c04000400200049007100c02000900741c1040540f000c200014003c900710104000c4c8010640c100011012881d5a00c410a100c00035101400c240500814564150945415614040e00034070107401c0c01d2040460800040c109442120b8808100101074165100709205540c0580403c5245150b80040f503904400824100d95075000e41e0304051300160004800c0718480300940080c0009010701f50408550944400003100040c84c92401180480000a0200c0403c0c2003007048070001d0122846a81004480c1e007036a511410201c0a5505070304091740c2d50a500307400709156110703640c403118100c0004130380c1208014140d0300400050016156080131044128108100301c90401c56111070350b040408071101504101221040300a01b0b201c000807440c80035144d44040b81c201000341d419980d1030b43c511ba03125002c8245074030f005080d1400141481c0c0003554072180203005a014141c0a03200026036070071184d10800c10f881e44074204c1810f444080d6150401a03440d040803015000c0c04001c010f000203 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 701957311 1250 701956061 701956127
    0xc050414040308011a1803070305190506100803120a0b03010c200703050d050a090f03050a1a07020307171207020d0311030c0a050d0908030a0e07090b0612180607 71
    0x291400070142c25052410501c0384d94081c0d81001d250b2007e40503c034654021000903070400c400e003c008822101d46c0c0810000d071034000d182520007488a02c40c44141241040140300c00800c1d241c62812180e1107250360341d41c403014075008080280030154190b00302550034102c06c1c2c00001c0200300e022000d58501800c003601c40078a60304e46c440e2200a02d998011401c031010188220003809241c0203515007514903940d90290030b40807024581064407250002c2c0c18880030800c030b104400801c1008003000404c8e503e0311003400f80d1680a081809010300248841c0b0100761009101198688600200c4030141810013200007551601c859200c0c00c0400d2401307414070f003146002000c0c4c0b80f0440c400081c040c90000100422281a000010002d03a00f42d00e030805800051001c0780910b1141400e5140000c0c1c80c2040700403203240984070f90114148601c1c000da07212040d2030741d4040382d4119642ca040f848150300c1c1d00701400c0100510140300d5029009010070701c1080c0e036001400c2c80313902d4500140140c0b00c6030200406 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 701958561 1250 701957311 701957339
    0x27050c10080115210515010c0201020c0f060906030106050406020d030501140127230a030c0b071704030302011a030c0a150201151202030607020a0f0803040c05041404030801 76
    0x2010802034001000128443c0344800c035000414a814144426202040308038691510001c45031240c84804000030754050a1008103003c0003440e001803a8005c68002035281c90b0030010b0140030300b48030694016981c5959048072101070300a481c50b90389694885004120f0382090103860018010490140c20141c441e02840303040c0c400c80d111204a0000950040d200b510580c00c0c03003000160040040b10080c280385840000034a03110515031001600705520080c01d07082c510b1032600c1400f00407000d20109803240242d000313562102c074181e651403080741802c040702c0c038100e8803030a800600000c008c42015410b4005c20300b030100c4001036146401a200825031903a4240200b1504007a4000003000708a114010340c421000d2240000207150300032a1810002003100e40190001d1040b000c406e404505041203c2c82e8020040e201510b00c07038800b903580604844019101800000000c070100d021320103002000c1c8002e1000500401032030854519619156004031801c0d00480c0780f02000081d580340354214 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 701959811 1250 701958561 701958589
    0x612200108090c09042901061103042103021903030c080c04050607020d02190b0403050d030c02070303030b06271e0319050c150d15060e090a27050c 65
    0xd00030104043d024001e030400c00034001d5440a080c102c09440c00c0754811400b02018003800b080d0704280d810303c10042c0c00107200b00c024200580c01080108249840300c0241035003030140300c0c0315024924560504a142c007208800c5600c240e254403080c0001c040d0590322140e100c0e40181c5902c60982c1d00d4180b208120b007e030f845469000b001c104041c200502c0c24428003c03480d84000c0c84c0c1c80212406000004403001d0355004003642c101c00003400d10030700c6810092005100b900f850203100110038491700a4888009100045c240340c0c6490102940382d07501d0003643d80b02c40c504001d0344c4c0415000d00c4102107600d20410100d008054042801243d285125046040102c01500526041100c0307000c0c4464902000d5003501c040c010944907280071740d81c11040c5d456084c404200c250300d62080d104010103c508000d0b580b0f0030303036822031410000660089401c8410304021664415207545030381ca548048c1800310000307070804800c0b1180300a564500010044e02030301400c00c03114102240d9081c005034540d1140 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 701961061 1250 701959811 701959813
    0x1030603020d02010e01090e011d0a050403090303050c07211208070504050d110d061b02010b030601060c03020f100c091e030f0f080a02070302090606070312020d061220010809 77
    0xd07082c015500503080c2022012041c50b1840110f44c1d00c08140ca510300d0282c010700d1500c109040c0d640d950303900769407810b50800c0328010704006a04041e038001d401d2030a0347c030000302401f07000304602c403c00d80c05120010080c0f0344103216260601e0540d140e406c1c020005a801c0714040c80003048000d074107205444052042c072003a1910303490541404204405e501500100300c450401680386148185c81d4050f0100d076586c482c0c1c90204469213000000301c1c15a007283ca1301c0d02160314142c0010190745d40055000e0466500c0d05045000406d581822400c2446141c101c1d120352040031800e000c4031005a012140411065556050460311361354080ca151203149141285991207000034404035949482c0180418421035904000d01ca2aa40f4404250040d40c0b4840140c1c000300700800c02e6041c403070b10280e44140100c0d212450821103540281898040c2000b01403071640c0411a401da803411640310501a2003d10411218010380b0719286102d2071180c0511303884035003030f804a80003079400707840d20708e01481034a0 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 701962311 1250 701961061 701961079
    0x201110f100209060d02070602040f0e04030e010e1f0e1e01020c1e0306010308090a0b0412030f021f02070c0503120f0d06180c090b030c16050f0105180c0103060302 72
    0x4614100030f0342015090b6980060308000b400d0b1507180c14401444424450700000d600c0d41d241c41c0f50b00e15002059031218840180303060400001a030320021a4a1030b00090030590703003e1284801086d0981040b002c8446400075505958249130303003100c011000762a04854007802d07078110308210341a20b843d00740b17100d015900160b204942460311007100c50500a116184040c5030030300e040000d1602c042079009807818000016412094140010800040c2107120152450146000d480d4242d00c0d106150240420042d00441c070003961003404060004058140c001c151041900d51032070003948582c5c02119010502e030300c001894240804c0c055890f0101c4e00000b800c202c0745004001160748101000c00f00c5603a10840825004a042144090054400000540d000c04100082c1c45031103a900310b08648401803041180e1100308004a4100c540c108003005000b002030716244c2d24084e0f80c590220440d50030704080080d0701d4003e00e90680e000080108503a90410a20015000c4a206000180d08100e4003 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 701963561 1250 701962311 701962333
    0x3070c120320070f05030f030916140d0606080607020c010e101407150903050a021005040c051306030206160b071103030a02030601110a051b0f1e0d060906090201110f 73
    0xd4000340c4605030252504c0309564240b681d5a13801c1da4484600d44000641c040103200d04083c0412941c00000c030b82216140c2c010b8108800c0d41420780c80300090ba03109604c1c43c003a02c2c0411201f84c120300002e20409040303070101e0400c1c4030044d40312409600d48a0028002070900300b4a0f150040311601c007960310f41c5460040c46824030085d2196800b90784159602c00035603400803611395180c818044218029a149a11440e2080000303040c807615511400549041105200104404034048411038108840d030740680c160805039213015295607030020f540710502040c004241c291003c0707192205841000200710359556420165400c402070f0043c82c0241d0f00138000180041540c1d40150f4000c2d90504000050318403035180540351010202c41211190030030383c10441800350004c0344c00c0c030079032040700d1111031038500d500420707012203281c1c03c0750b09600042d0f09411031640300c0b02e100d0b01e81e90303400010a02c440192410150080c00604100301e0000300c072012443c6c00c0100c045118407600802c00054581240c40c = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 701964811 1250 701963561 701963621
    0x13140a0b06030f070302031312090f150210020a020c0a0905041703280b060d0c0f0507110d29060f0f03100c020c040618150602060c180603070c1203 65
    0x2000d00d4080e0881850300030100b160003110a0340d200d910f2b0745140717200e400d148601411640366441507100005217920540c80940108445400c5081c54800607220f4201c00400ca02e0074406208090308455001c0002c10010359941016126a014072045c220012100101c6281d42c801200c05149207000f42d183c0100344102d0802d0601c1e91502c503600482c02c2e82800000807501e500031382000f81183c0da84e41032074111641041c03102203103109a00b009400c001c11925542c1c13221490000141c8100c0a8030221800c00c400c01c07501c1560b140010411a0f01e294080340c0410643d107040d41c04520500d082126a1417925020280945580c4050003a01403074001c40101406407040b00100401c0d4080d0744c480c000d80d51981d100380001049441e00d04160754502c00048022035190079201110180182814031203541c0004004d038000f05010280340d40c0d082c11030380781d0440c03001118510758801c0002040c0701019900c81e2030345000c1c600452810451480c2e00e00240d003107403204aa100c80000005282c00c0c10058 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 701966061 1250 701964811 701964817
    0x1020c2b060e1501050a0632030108070e09160e1b0a0302072001050f0c030403150204090c09080c1c05030a1809061d0613140a0b06030f070302 63
    0x180c40d60494801040c180e8a80301929107180781640c4540c0049843c551500c0441c10703041c01080107a80b02c140160601d44000e050b481024100c424040090a07003013051a0040e40740016a0003510095440b540c40d50b4802e0f490304120b1140110302c488010100e12942e0010403c00c99070284001c610506504d018544000418000e1503039805100d510346030700c41c0d03c2080340100b0340e00081c1d640060b900e041501c0d009129048640d00c1c25196540050800043e0341c01c14101c07103d030948240710b03d840700d07202a2481d2840c40755400c0100584070904031006015030079000340050310b080540511050b0b411103001c8915458620400d01250301001200303882c1c4c00c0003402c000d41460030b00200d814000c11030316614550b80c00b884001c80081c0403a940440714640300d881020203000311f020305201091034244910102032022003e000c0d8030b1650000701e0b00c03541d110390500303040d007010103010f11500075042c281200c080000c1b6a060784050900030301120519250007200c0c0b182100d0311116659031903245003100250 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 701967311 1250 701966061 701966119
    0x123213060b1c11030118020315100f0e0f07020a11040b040204050d0f170a0206240301050406050601080c09010801300f0512031509101e05030c01020c 66
    0xc80301081c50000c1e42c40c6100c0c804069400707242c401c4030003c0304100b89401c5408062144d0700080c409490240141d074049203c1c00d8518000c0d210100d0758441d9801e201f0440724941c05105900d442485c0021031801c03015000b84a0244c20030144440c0d40d07004001e0362507609100c1d00410300c0341c100b5440341442c030f400d503c461101103000c0c0005003004c2c0c855020a68a8040310029519414520120010000d000306482c40416507281114140b00100d03001a41d02d0741d024285007024070281d124801409403c040015036410300030024003c508090501c2300043c08141d41903070018140c40002158021503004070b61140c14180c0d2130840981c0b8103031054800c203112004118a090500d80150101e500c500c1d41d820308a406450f81c19500c030700354500f070340c41c287d600340c00c00b624000c090040100107001c44050031f02012041d1400e8005035200300c200c00d6010082c0c0c2040030743d06206441c0b45c001e60b058641c418260b41064084500b07400b170090040e40d44901c00a8100e07484000c64003c00402e000280f0854415 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 701968561 1250 701967311 701967319
    0xd03080f0a0209060403050a110103060b19030f14040201090e0c18030102131d0f0103110f150a02070807120c0612060302030d050d05100b030109020a123213060b 71
    0x80c0340344000540170b030302540c01942c1c99800303c41e03004241300e400e11038400201000d081c104010791800b43d11f44a203003e4940704032080c09901c100651624080d401034452144d6000c2c1c00c0102030110329901d1074245040e0303001c3e40000c0c004400414050303240c244260044082c04c0c6ca1a00b0820103440044005d1101c946054255400b0300840041c45203103041c0303001034170340042c4404148503419105d40c05010010b101032a1000701030b00402c04501c81d064180c002080075244102c10045030000308010100416140000940010f08021060740c0455600240e64810082d201001e5660020541c0807545140c040c0840070803410401c4214010030904251350100000801e0a690380d07000a410038000500107000328800180c8442440703a18841c0944c4480420024002c0ca0306100039801a400305008114005a000840d42d00c014091300c1109806003001105104802190540911109000700303242009680d070714401c1305081c0204a214803c4586c024140d952000d40d80350740d406803c100c415140c05c = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 701969811 1250 701968561 701968567
    0x3090415120515150d02060702030a241d031801180602072d0605090109030204150e0f04030c03080720071502071406091206040f030e0d03080f0a02 65
    0x410190020022081c1c1d00030005002986540c48200069402c0107050401c1144019054507559540c0c40380c1a18154040c1e51a60316120030380b001c00d1508900e44005020703c00c881501a04c1d89412001403c3c1e40300b01c0501c240000c0b03498890400380c600c0913001e034440301d81003403100410369200316200d030112000c1450501c20100c00450401e4410082e40c0000c00141c202c7c1e1024070408200c044000d4951119020340c2e101070f8640c0580300403900813130040d1410403a0014040c4042c2e8803400e04040038580040c07040207a00c03000381d1b10180c801c2d41c600c02ca41328442c9920025008404401d4050b2040d5055210003510300b8541c2c0c1d00b2141e1100040c55101031000d1840800300100040c50700348104c00c141e1008202c5d072420710422a1000340810713202411544402ca06016890901040041c0f0310000c2d1221500c4003040c6001500c1d20100e00031441440c0300d000108800d0008403402c031600c1c60301945803051000c0241d02404030b1144c55000107404200d114000ca0066080416503650207038200500500f = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 701971061 1250 701969811 701969819
    0x605090408041d0105030d030506013c030b090112030216060e0109091b18210b01050306010f0501050313050708030a080916150509030109032f03090415 67
    0x981604262400d40c1d00000c0814180300741e00d4844445030300754181c4078440e0110b41c54040040e1b07454001e02411420140c40d079011809a0740140802107250705082d9600414402d158488281114040d054096000d02c49400c840480e00920460700403003400340c002c0010340e00f00b40aa906039807080108400b14455102269980c500c07540c0c03280c01a04055230340c1c503c0848014001000c0424a800c900d807242d16024050349080c40450030318001b007019003024007210b00d61401d103001c070b041540d000c4019144620070402200c0042c0030541c1c0080e120361b46d00703032650341c0b900145942c0e41001d004003403507806449418401980580095a449481d003500400b120440da607515080c00202c1c2e1142c84142c2c00811288040c1e500f02e18016803295410008003d810640d01c0b40000e002400c3c4a084c40c50001e1202070850f140c450001c0341d08848010700280804a4640740041a8001c4d204a0b058410390703001080144410700540700040d41c00c550001d5041c44050004c1000400750250000030712039440740009 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 701972311 1250 701971061 701971069
    0xd120506212a040c08090601050411070f0305090a08070b03011a0706060b0a110c0d02091807240309020306011a041a0a081b030a111c0c0e03010b0d06050a0605 70
    0x740255007914a0740702d1040303030070080c0420780e50540145002c0c49800020803403010000500a070440300122804254012a03501a00700b500c1003000c00780c000303410342908005154000c1c00511207a102a5068803e080e61901d20320f031524203034000c41b50358541c104010000068600f0005071400c2c4548400c1c0d152044903542d001c00c9441d030b54400320f001100410700d0b0300340d03581003001411007181c83d4014020f14035085001464542050300d00905c104180404120324444000d501034005200c0c03030844150301d03180c0000382100300407242404420013102c40d6a03c01503119000d011600c5902130000e08240c0d0a20580c00c00aa0034850400d4018905002c00200d0020300d89488920607284003400d40c0c0e6066002c0010544d50005044090407444400b0f11054917035220300304ea5008503c1c610014075400d01101201c40da100b1030b0400c441110907a203000c00b6000c801e44c414103410b50b80d61190900001c0c048103043c240c0d03a50004a0340e101d54404c0120f00400c0390394000940c4640c62001c0080d415455500007 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 701973561 1250 701972311 701972353
    0xc120b0c09041d060f180a02060c1c0e2106060d02031006030602070c12120e0d06061410030e070308250f061406100c0f050d020d12050621 61
    0x601c2c00d03808001031105c002201c0541c580c00115a10848403418a42c0c0c50440e601c12481000900940b000102800001d0040c4196600081150310012501080c08801007a07100d4800106201d220b040d01425480414000300c0361790445420f0180c4040ea844104108900a8000003a070300f60152400e85647d02c54103208000103903219010050f201c0c2d8003818910000729443d04000283c0085030b070080041030401c0e800d4a66120203280510313000e0b101c2d0b0041243c92080c2040103042a0400c4000314140204070035280c0c110780152024907a02400c82c40840c00d0711069482c110254000fa42c1c14000324880400030000021403070020b1550342e008254161034110310040964110140112080400c5124094038000c100346244218890401d03100059456442800405c00e10070650200001c020140f4401c94a4a0b003000c1610045d9480ca240a519040010314040006505191510807110244a51409610090031058003000b08040301070890802e14521003c61146182c488a094684126 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 701974811 1250 701973561 701973611
    0x12c130c05031218030a0503040e0411100e0f0405010e15010c0b0a0608070b0307051611040f0c030c09031109041a01030302150c03070c061d0a0507030c120b0c0904 72
    0x890743e035107842c130b00000d0b00c21295180491180d0043c0b1803c41c041900007050b241528042441c2c59000e8495282c40030711400d40740501e581040c01a0018806160081d107503600040040c1c40c01d49860980e11b003000300b10344003401414004500c1001040f0080c045440f181c55505c010304062060307030281d440c0c205401d041201c401401c6c94032948144043e031000d112034401001c00c808220b085013400100680030307004162135003070f80c40300c150145014864041410112103034003910401c190803400345641c002c0c20310040040c000c6810b1601a1028600c06c0412000b140e40080c8602d140b944294104031034114007038004d454a00071480403443c0e1040f12640c0c54001c41c465001441d0360044007242d00e8203540c000786810211f200134400c10509a82026246411603030000f00000d030103004e82100000020398402c5009940304030100c0f0000c02a0006020054034041c80000358a07640d64807929020803402c0800400100c04000890301018654019000d9844000e0010405901c101c0840d00e0104507041c0d = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 701976061 1250 701974811 701974843
    0x1080c1002070b040510030b040c0f091401020604170712050403020102240a150b16060605030d050a030c090b2a030c0a1b05060c06012c130c0503 64
    0x6404266403511510a580914040c000361208074070b00700302d24400d4062445964000c1d0307401510510998425841400740c41c1d0014410004684511070013000752101d0003005002c41c0d850440442c058804001694020105900524080d42e03107580d00720364000b50034050b8503800300c140f1442000030307150b01944000704446e60307419840314074600009151909102c01259001046008468120100380700283d102c4c00d0b550700801c4114044d9151240310060380d000642a200202d4403112001d00503400052072805100705100050b01c072010991140443e00030200828020403070308c0000c030700a422140d0102214100342074010750b01c4680c00c42ca98418640c0d0040c030130803503100d0b11400071080c1c1900c14400188000b14200f003023107445565101480c000143c0204c3c0408054031100700c00555090140c80082c040380d0719002d402c0f034060750ba91028060b00242105020400b4442c0501c41c0d204451a212130124008503140d0810305c1c00350500c1008142d034030705411f240105203620b080000e0310403140916 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 701977311 1250 701976061 701976073
    0xa151808070515010f0303051b01060602030c0f03181c0506040f0510050f0105010327031806020307020f0f01053f09120a09090e0a0623010e0c0708030108 68
    0x842d0083c200311030183c54030561000d010040c86545480001001030b0707981400c00315078a1829014210031240d5800c030885c110760800002082d000e60110251000e15603410484084501c2c40c40c00340e0310380c0a20301d0100d503100c6c03688000c0d5603e8600050058103240c902c1c40524590802504e03490304011045a06503114417840c4482030030484108203030380007800040020490ba05020729551010300703040c030805040544030400003501020b40d9402e84000103c04030074200c0054640fa0180291410203440c000550017903400045c00343c004421100c185a00805c51070302c01102000300004c1020300825641000410311040001e110504081c040819891460700d5038011130548040201c0380d0407064400d071200881c240406800009603184103000407519441e02d5500c0e5a004403081c0c25194008008141014003c3d80c0310240815140400ac0c00f0b4007080c004c1024000198800007030403024014014654401040745000700b0b081a46c0006208100c14540615a240c07170020380c201380c01040c2c09400803 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 701978417 1106 701977311 701977313
    0xa050906010207091401060f3603020402031003050709060602061306271509080a031109150c0105060f0604060c03020717010e010510080a15180807 65
    0x1060701080804245110750b1117901080c402d15001c078a40304201c0d08154071801500011400e403140704441080c0c04402a48c0c0300c00d000c2800b03c1143e26255000c070040e40c07070340002c50280d10821403550410b400c40c00e00341d003450030a9206851041c0340c404108021900410066444080307032000300881091814020060100d601148142c8259030700c2c81d0200c40c15400c0c150004a00660070241c1071940e8960100499403261005840000d040c803031042d07094401e420406075130102c101c5050415030400013040381848100326000d035441004c81c0620841200f48180d56000754100c900d0b0a43d0b504c0500420658441c0e4001c100800402d034031581d003458001c005010003450000311000d1401f1251448038024203882080380095401c000106000408504c055010340b060342000d40b0220740b843c3d9991600f280300a80c2440450b0b1240604c2e0100c0c001101c0d804a128002c40030b01d80d0b20039035 = true := by decide +kernel

theorem cover : BRFrame.Cov 701798561 701978417 := by
  have h0 := BRFrame.cov_init 701798561
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701798561 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701798561 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701798561 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701798561 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701798561 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701798561 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701798561 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701798561 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701798561 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701798561 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701798561 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701798561 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701798561 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701798561 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701798561 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701798561 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701798561 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701798561 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701798561 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701798561 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701798561 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701798561 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701798561 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701798561 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701798561 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701798561 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701798561 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701798561 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701798561 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701798561 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701798561 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701798561 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701798561 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701798561 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701798561 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701798561 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701798561 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701798561 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701798561 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701798561 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701798561 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701798561 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701798561 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701798561 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701798561 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701798561 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701798561 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701798561 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701798561 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701798561 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701798561 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701798561 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701798561 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701798561 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701798561 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701798561 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701798561 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701798561 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701798561 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701798561 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701798561 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701798561 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701798561 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701798561 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701798561 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701798561 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701798561 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701798561 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701798561 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701798561 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701798561 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701798561 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701798561 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701798561 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701798561 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701798561 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701798561 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701798561 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701798561 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701798561 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701798561 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701798561 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701798561 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701798561 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701798561 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701798561 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701798561 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701798561 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701798561 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701798561 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701798561 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701798561 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701798561 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701798561 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701798561 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701798561 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701798561 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701798561 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701798561 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701798561 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701798561 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701798561 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701798561 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701798561 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701798561 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701798561 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701798561 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701798561 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701798561 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701798561 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701798561 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701798561 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701798561 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701798561 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701798561 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701798561 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701798561 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701798561 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701798561 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701798561 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701798561 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701798561 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701798561 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701798561 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701798561 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701798561 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701798561 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701798561 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701798561 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701798561 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701798561 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701798561 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701798561 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701798561 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701798561 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701798561 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701798561 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701798561 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701798561 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701798561 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701798561 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701798561 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701798561 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701798561 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 701798561 ≤ n) (h2 : n < 701978417) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
