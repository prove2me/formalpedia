-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1748
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T04:32:07.857909+00:00
-- url     : https://prove2.me/submissions/48843e70-4c28-42cf-a972-8540a5557fb5

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 314208633 ≤ n < 314388489 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 314209883 1250 314208633 314208641
    0x40b060301090c030b06010807050309032d0a08060307050303040b030c0a18080a0309081c05070515040c0602070806253b06090619030608030a0f080f04020a09 70
    0x1940380d00d5580c520b03001c0d000400020765000118401c00032880f2514001001400c0e9400040130390061250400405c101500302100715000402c7e05902c4440b9802c000b82c04036811902d51000511001001840800098002191074030582c411003c40c1c90300c07030301e50301403549a02841c4954100c41000780301107000860248090110041e091621115505110000c20014141c80c3d0180c407a60f08003014400a140e40103221002130280300e0020502001c00c000400c1004407901d60301e00400202241500070054244a6240c100c801111100307100d042030b003000341504060780704081c094810a07100142c2c0c0000414403a100c0d5004044140d41040b10340391100707000b203461441c0c804100003840322120220091401c25112002c500307a61003401c002c0060203e80c0e81c10703a03090a01c10141031000b4071240d655031080302c1080c5108940048103250300101940038099640020740720380804948461103561101f541c07007411000340d0303a8011b42d0300c840c20109031005040d503000e03401004202040c4480c41ea2500 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 314211133 1250 314209883 314209891
    0x30c0c091509050108032805130f080f010b010e041d070b040602060907060905010c081e030105010e18060411071a04120f120c09080708011515080402130605132c06040b 74
    0xa20700e1030540f042707921103480038464100b260403594518040c040303400e00700028080c2c0b050010003088540410000030782005c008090f50b03481a500c0701d8046001582c0501441030013540081140c0c2960f40390f181c3c17a0342c10303007140c02003c006104203c00642c900c400054240700312206902c80310481c0b4144401100d41d400302440030303151007c041008404101e0640e001d40400307000c84100c00e4681d4186000180354140285005124400051081c0e03110b055010070075400070380454002884030341c01e09020241d030242101c0a0711f45618042700e440c050001074001e070b00c282d100344c1c0c0044240d4030752507080c0c5041c00c0420b000800110900034141c100960341d80440f8a40760309003000700c0400d03580e0b200149041003d4200c998265141c0e0030b4280007007a002100c0c005088140807a404200a0720402402d1140081c8007030700c10940410304161040895204c00090500074085215000703259800c1d40c042c1940090703540e10164031a0407400c0000c113185010640182c800068011916551500c100e8500050 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 314212383 1250 314211133 314211137
    0x9030b06150c030c010c0905030d08130c0b0c0102120c071e0203070801090804030c060813060f06030f060e060603061e0603070f0314010b150403030c0c0915090501080328 75
    0xc4042c014120030405040f42d10348510001c9901c00c03030048003c0103980c065005c0340c025444002c41501c0c10340c001c021258407240c0443c00702840c0c001402c02d807110b0712843e440002d40e00000100c080e00004190000c00c18041aa030b110801d41d01c1d61031009115202ea010054418000250040c0c001d40c25080084292800101141c402c80e4407038520038211810b4036001c07a00b048001404204120054644000500440c1401c5080740b403d40c008000691036401e005148944d20b550780e8820000710390000c00956004015003811801601d86200101050b261001051040e000000e0551500103102441850024403c0140c00b03080342c1c0500b40a440a0821907050288100200f00030401e858170100645c0202c2401200032006800142110400c007620307405595450100c2c038004000e04203c40450340d041c50001c03d1825181081081044282c2042d01c0e0a4142282d240c4100c03810302c10001070b0755001c4010880750361b82e103c0080c0e49101e8001660720700000d141050f00007030442c628905080c103040c = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 314213633 1250 314212383 314212387
    0x30601081e15190e040b04050102070803010e0105040f0c020d180b0d0c080112030e0603250207050f0609150313080c100506032a040e010e0a0b060109030b0615 70
    0x5012506000a003151030144034001c0780b204405603c1c000c2140410400100402892542000c00f0b0345034404009001070425404a004102046400d42c102c1d41865000050b054480d611040a104510020b108282c0f06505005240011010b0f5200b020701078409500102130040080005031070b010364220f01c15400f4082410006404640103006180300d20402d0f000044104034503030083c2c8161010f820041c040d40c11150b400380002e0708a401c215050340c00702c0e0541d45a9803108213034801c0f8010400c2c5c3e4400b0194000b00c030407095400050f03202c103803603040322020803c1a0031814411076018004d0f00d2584520b685e400444543d000d84000c41d0007280c410780c089a01501916240441c2c0d200107200303200c0e0b5000c1300316101c804560303111b5683c0110080b400761442111b03140d051181141d00c4504408036100110300544956240e03400030b4090130000c2c000b40008000314141340d442e4210b8150940741c00002d41c0000f106503100e400b1002c20341c0e030300c8660080e03e6118081400092214280c030f002100d40c003 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 314214883 1250 314213633 314213671
    0x11031c0f18080927010b0f0735090a12020a120807111005090f0a180501030b0a05011a0304080405130e07091a27090312090a030503060108 61
    0x44001c0c100007040c000e20455540d00c0840c020701c03004e58903a10500b00b1096003208100740003a500104107045540c141c3c0002d0b00c031012801043ca0701d103e40c403002003046000c1a00c444040695031101c580044000ca00303142d0200c160400c0c1c14551190011042d4440621103090001c400c09012040400c1d00240c000013005131a409004030801d0000c00c00d0b1a0020046403150802c1035000703038442c846033305581c060100c1611030310160240c0501c0c00078511400018030121070b0740e191030388404000d002c6c1c407090703009416204184000803c02030009680e6001010001101d0340300030700030107040b640d06500071580c0c21415141000b071a000540100c0e5084000c0000050540d00c03130010340c4290f041403500094105070228000d1030250b060b402144500e0400e03980c9042d41e100400724403440e07076040d512020002c040c0d101e45800e40c1c01820342081d140c042201880b0000a0000c050030743d1240210503180c1a40300c1d9503c0980d214424580200011b00400008401c0e510031444160000300300c5080c0000f09d11 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 314216133 1250 314214883 314214911
    0x30c0604050319150e101104050112020c010e031b0705150301030f030207180f0f0603151503060c03090209070203040e04060c0c0c0303020c03010b060306060a0c020118030b010611031c0f 82
    0x803510b250f00080758440c1c5564030781c01045204141000240f2840c0c10301d8236180c41c1c00a042d0a003040142d0700426030114000e14031500a401101142c1c0703068041e80d46c1c500f40d002d08a0100c405814040901d403040d4040072449082001c3c4c4e0404043c0640e154508681ca183d0b9008850618000100e0460282150000d29048010103140c02c480784c0080100b000707148880880c044a01c481c0302c5048140c1401e400304041140b281d5564440c100c40400405c1c42004203084500c5000e080c1d00041c42e407490086100c4010303038141e008201c0035201700c6411042c3d484562013244d80c0c0c0070350302810100d070320b00c03001080008105070300102c410145402c2c408a6010251100d04051302a94010b41c0560003040c450380d10b51a0a00c55110b84100031036a5504500349000480c4d40e070700412029006012100409105681c0104141d800d007240ca021415142c941b603103411804100d0a1040384080341e901000010b44020201c281c0d0030404400c505640800982001c00001d49031801030186580e580e400b1204c1400 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 314217383 1250 314216133 314216141
    0x3030d0509030403140c011d01020118080403050705090702121e0304060f150b041403070b07060b011e0e040504030e03070f170705010816031b0c02030c060405031915 73
    0x404544055030302c0780c0c650309044005c80c80c540a15a01c0b60005070742086940c0c0c012104048080841d00d540c0300722441140141e0041c4102444580740f0070b018aa80410080007800030020b0740d03c6203041d140c955581e03070284505244240d8600b805600414041d000d6261f00c000a8031028076814219503190201d130002e211030b940b0544080d031b072054072410075204d83d550354050b4000f600c220160700010680345c4451245c2070b0080d0b0083c0540e1421107151403e2559080000300080e141450301e40c0c2e5200040e00e030001c014040b0a410a01003000582c10a910308a0744191804460442d160088a43c0e9448100801010300510440030b10658400240c003640f8100424405098400340c1c4109090401d101809000004000345215600990003408142da00040c41900282c400520a8498515041c19000780502507407004440c000b1038843e02c0100c2d80905844407881c000d03800d03281da0f0141c0d0344c1400840e10a500803503030540e2152100240c20412484966152030203408080402921268650151 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 314218633 1250 314217383 314217391
    0x1020f0304080a020601060e0a0501050f0417030d0b01020c09190908031602070506130b0f04030203011506080a090803151c0317090105010f1a12010b030106030f0e070e0603030d05 79
    0x801004181c2443c025010441213000d82090b00b44492401c01200c00a030070f0207514020141004404185d514050307080200380c0703002d40440760a492020f950940100c0c0e90341c204d00303440302080b414a4032094280d400804d441e641d812010f0680d01c441d40d41e106c940380910103a948800d4190744d0740d41c00c1d40c0225890310701030750141f0690740203c2132580a04000900d40800c2e030f086144240810030509020f14100d440b00400ca030260207050f40c48041600c0524114055a40087d42550800700c203100d458a00c5d00000080e80c0068035135030313143e45031401d44004a9003c2d2000501d07140040000c6041141510201010301340c0080c5101c0100c590703c01c01c0e07480c00c0b400c00d00803004a292401c001100d110707850440795120040100070051585001c03a081954440c1e84a182402811000420a01c81e6000200c0b00d060b515404009050b595034201c04007103600c02d110b880002440d14103a04110041c030300500060402c540c0040035100d00b030020001c51000b010b48070a034184410003010b075411080d8041c407803207 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 314219883 1250 314218633 314218643
    0x828050a080d0606080c0910020f070b031b071511040b040902031b030c070f151a041a030c1912050102270108042307081f05130305070501020f0304 65
    0xb5006001d80c1641a03885542040040c02820820005051810b1081d01c012202c2200c0c11102c81046c1e48041c0c0c2460000c1c0c0d019071b0710340544100130558031400c100850141912088000c1109581e0b0b4100c640c90080400040103000c100c47d080f444c00380c0703d41081030103004800340d80c2c0c40c00d0f0703507080c4050303481d80303d603000445e0a07801000b0400e64090000c1030320020b80050302424510f150400c035118051140100003001c01e84081c60010500001701940c80e4520200c1c0c0040003522000001d80500b008030300740a5201d1410100d030a81d4000c240303e881c1d090f0640140040c0111040348081000200c181d40c038260112440d460700003422440c0010040c2d40c02c0c0a1000180c3d1440c0354001d2440601c06407a80b00c900c2c920802d040035160b60301c0541030307a00c603030404909032106c405801c100548031210100f031060b03485400305c0841c20381070103d030007801100c64204019108041c0745142c016180100c400c0a12014030b81da900010038000e9004040031485070000500d80080610000d06507001a6002c0d21 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 314221133 1250 314219883 314219887
    0xb041a030706020d080424091406100605040b0f070503121603060e0a0513021f0215010311010c150203011203030b151903060e040b1006030203010828050a08 69
    0x426040620032030700504401d102400030304404101c0900303030000c054001000c0030030343e03100a05080001c614402c00600c400c0c0003440b0a460300c1c00c001540080d64081d85116014100100300354650112542045030395035107880c2c0c1001e01d02a08076066801081d40c1d9501c1c001d0030800c8800040091004040c3c3c1040d105c095000d6003402505900c110707251075440c1e024540307050310a010340c10711001807560041c020080407600795200c100580f00d0340340d1050001d402c1140c2101440e10101390560f050314100080d42194400000100c907103103842800c1c400039100305000391440740c0c15449220f9604a2500800268801d9003141d004070080364002d9002e04c048c00c03503a10b1120101989030107004c40804040b20011145461080320441500c0b0306440e403824030741003886000b4098083d800c172000401d8244020141c48c41c040c20240000c1a00300c60341014001d40c080003054417030007072013624180c41200f00140342030000f1002000000c000d088015179030150f41441d03d40081d80400600d584188a0b900443e = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 314222383 1250 314221133 314221181
    0xa0c020c0d1b0806060105040905040201030b0a0f050127060c0515150916090608070e04110d0b1906080705041707170316020f0f03100e15010303170a0b04 68
    0x82c18401c0260805a1030f40c101380c3c1801502d0b0b034824250b41c1500c00d82900095292138501c016070003426400348154201d0f00300040010042624040b42080720307070130f8039012411042034200c2c04802c6000300080710700840d100414003a81f40308010901e43c040c4180104d8408240348850301c8080c10044030404500e01698040b907046003091040301d5000b5104a00c0407450849840010f041220b03036000d00010044403600140c5054030980398030b4003044000e042001201c254642480081c0e0000028118060030b021034100035080c1000e641514500c1400f00340565030501d2011241c0140140260007000020310003c90103001241903044842e41000040c03028030319000300700c1180c2c5011852550320b50420f0021141a01040c0118181c3c0340c0d041301c80700d1800e035032180082ca0b9000440401605441003900454007000c0035800207075a1610a41242c108107000510000060424000200000c0c41c1c4000c21b0b011858805440d81c0009401401003010609040440d0496040042202c12006e0018981e = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 314223633 1250 314222383 314222423
    0x71b0c0f050105120a0e071d040501140108060411030a0212060601110f0d05070c090c0c060b0d020d030e01110d0e011d0f011d03070b0415030b03060a0c020c0d 70
    0x840c004000030309206041035100c8070a2504d062009200b0345440d9141c02160285010600c15103010344400202d44001034091001c0804c40300080340c04035010341c80e04460712410201c20312181e04950f401e0000300819a03c0c1d41d52100c0c0e80950500c4281c062080510b01c80c0103a80304500c4940c4210390000402d01032030020001020a90856018481078001c00c0540030040c038007281c005803840712130419584c0c415447c80c10000d84181d6501c134004a40c5801500590035038402d00984c02c0601034282440101c6181c410410f48480c01d403002540141e05030900400217000c2d550000301c164050400001100c02c4040300c1d402d02030300056800020f05c0b01680840c40790f8002e80c1d1600040d544020a0554582e01e8000c41d00c07126521500324107221403160000c3d800ba20f040c20b80100e1003000740c00d45100b507540f0040009180c2090141480e412a0101c485404a2007845070782160040200100000d0700d4082840000700100380c3e10204500420000c0495610382d440e010780f0103485650708804e003001070104 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 314224883 1250 314223633 314223659
    0x1409010506040b0a05012303010303031d011e0b06070b091c1b0b091006080105060f10020c0418020904080309070e0403020307021912050c01020f0106050d0803071b0c 73
    0x25205500d031403c0c0c44990f0302d4202c0d840b000d980c001e0074a080c000b6050b4281c0305060244c0b0410502e420710000c004010164103400c1030f8112642500c00040c0100d03a0116a42070795550122045000d0340c0e40c1d1207002000c05904422071920001e007860f0721b0010552142201c0c2c0c00203d03842e40f00b650280b0f40402c407003104c4441348000f44906103414111207400a203559601c4070100c0f400307007140c208030010484c034a1040c40061024004a0002c000055071420020302a0000701c0d00c0fa407081c10041009900da00f042040c0c03c158002c140e024092206041e000c1200070003004480b91441c1811500c51401a200d10140f140118091005247c5a02e000c0205610300940c0c0d801428408440c00300380400260000266040158121000c241510141c01071210b031070020303484801814851500303203050110220315580f9100c82a403e48120b5400b03811824240c0b2818400e5941224003000d10300049421741024507003140721440c0250303003401e078417201001b22108404d0584600c002450100321031f50440003 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 314226133 1250 314224883 314224891
    0x6020c16050a0b0d050912130609090e0c040905100207061409070f0b0a030216030507020102011a0a0302210d050309011b0537050c06010b03162114090105 68
    0x640a0140d0341000107418071405800340040e0710302c1e00c41c8041040210144150301c01d41f90b0101400d030711406000b016001644580c0704680106031900800308002e03030503005034654032075060020504450014141b00c010419440b00342d450303018940c6003801602d40c0e80000c1c1000c42c0182c4020803802e00e00b403540d40c000c18000e4400c154070f510142d0304104a46200003c00103c410700000700340c44545807481603003c0e124904504003090b041150712010550043c2c01307840350300e001303034020000583d1b80c1c1c010001560700c10f150b650388110140340810042c42e0240c910303007040100031030988075042c22100080c03070086c100c544100031450101c03c12111050074443c00d032a0f0f1580c10407103021950302c501c002d4258444c050100780508006451800c1c400903880f45520440c041e003040c2080f14184e550000e220f50001e0303160040368004c10300002501440d04003501c4c010b0600340c80d15160b40941c508142d485480943c10402c141d200712a5400c207a2a06124580c00e001d080c080c29441c0d032072300c0c080d42c5086845c020 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 314227383 1250 314226133 314226139
    0x4030f1707110c030703021c030c1506080f0105040b010b070606081603021c0305030c07020d020a0e0a0c03050108060606071401021303120f080f0a0f05093a0f0c06020c1605 76
    0x41c5d81000540d80c0d83e421a1544290040441d000240760304045801404440340602541b514910640200150b0361000084030801c8054a200c01c5d19461054241d90080e2809058440c2c605e005000307000c5204010400e1600c25240000c9041d6a0b10b03401d828415400d00d0386c0034006a100c030030800c1d0304211903000481c03200b1a6540c1082078082e40c02412a00000d403804101c001d0203d140350854641110800d0415002800c503680c00e503480c1758100307080a00311401404281084040c03003000f8060300925058a0351034014280c16914001401004e41201400350b401089a40f02561464801c3c4014900c9020651400d14004d0560825145242207513640300100802c43d581903182a0340840c00c940c04c10300c28a001081d64940309042c00260400780e403c00480b500e84824031451450009401200741802500f41c401aa82441c09440c0041c0048101c061071541d09082e50f24103102e5105251440341604000170038034000d031140c100300d80000d843c85c40583c2c00f80c0c0d00d1400d01d1583c051503400170a012 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 314228633 1250 314227383 314227393
    0x10506090c21070905130911030a0206070204050c0403141c0e012f031204050712050607110106030b0103150b100207090b030c04110d0f02090904030f1707110c03 71
    0x10204681c02c41e1940100031482c604010045007845104204080051600800042c40034030215202d00040c81c1d141411211940d000344281000d0802007074103c4615001484203052000716020b00c40542001008c03900300340b800304404000140d00c00180095411444000c1109555a40c145142014882e0b2203900340503400c191451143c1e441445014689000461090300203020403018040e1142800d54409602002c203241e442c60009401c928800e90161003190380c43c0c1c1e03640c8020400c00e04c5482028119400480015801c1e50142d03104100046084000103106036403500d40745c012071003e070801ca40e0b182c0d60800d05a903108050084080020742124001201020242d01035622569403141ea811142c44000d14201550b051000c0030f00400c010308180034550705040c007110185e002101400f410307460030704030444010b0036200340c03401c01101a04c20380154481cac0c0c40540f5424100a0000304205001c021011842c8103040b046004007420345408040c4411078aa01e801c0c0889800e8590003030b402 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 314229883 1250 314228633 314228647
    0x1c080304150c1818090503270402090109170a08071a0f15040c021204060309021e011d03100e01050604060b03040f170714071406070c0905060102010e0f010506090c 72
    0x903c0c000388048400005203c10741e114815040c00240495040140c503a001c08111200781d90442110719132605c160102010745803070303514100800c0703000e4601d416000404180050009034140d48140c440d620280c4121030000845955980c0c8a40c4800c07011281d803c064204290755104a05150381c0000981e06114580d00d008001c0310700e19142407504030701c1591102c41501c00a40240440c10a071103c11044540d01e075103a4102402515407807200701d0062644100d03d44180000c0034103003003107400c140d440c9902c040301540b007409040b41c3c407807886a060092000405002c41c1c0ca05c580c44182e4140000481c0514281c01003004961040c1d0014a4000041041000040c035203000155800d0340810014001c2107007005a22040c01074080040128800150003950b841d0f0014520045076040200c442807104d0010501400e4050000d00034039100c03400d103041c407031000d55401031030b03207c541803000180c3e030b044043c01d6178580000c0440c400300740e035501c005003c50740c1014080035038000165100c0d1458414 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 314231133 1250 314229883 314229917
    0x11107080115091802060d0e0106030f12020f0709230708040c080c0315070c0b010f03170a05310b12010506070c090e0a02060408011a040b010507021c080304150c 71
    0x1101d0b0802441607000050403030540b5888d40c82048150601e2008000094581c40d0601c0c10360381900c03095410100794803400d0181c07480000c15503908000c0c40c1c09405000c0c980344004000c1c108490001822040c440d1407450300602c0c800509210700c18582d070b444503904280c2810040b4501e00c0e081030f021504440c1600312107480000d8004c1c1014416520881703103070744103502200e0400c0072960041c10200003200020b40f001138a50141c1c01d4a001d0315010030714041d241c2100e0018440c4210394404100284070215005001c49140070740b06151258410075802501420b2205c0000d503040000504030201e001c82d62001200302c140e01501050799002c0c0b0346646a00e038920803810500c694035102e611440d00d429604000c1c403d01c2c080e9907001d0b0246894548030500c06000c1d20b0001c000810190580002d500c00e17243c5070245010313002c0d0603140c0d503241c0b8020340c00380400881080c1c64040c0840748036200000203001c3c0c07c001e40c8528020f2070071001102c04040c0c08401c5d038045075062010880b0813088900d040c0 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 314232383 1250 314231133 314231171
    0x60509011e27050612060f0604120c2319170d03050c0304030507020d1e03050304050607020a0b150d0f030324050a060813020a060801050f040207170901110708011509 73
    0xd507808102c50481e500c3d06d000400c0f11403071032056604120045400981507121844080381c852040c0388074290140c035a003000c1e0f9401c6000c076288051700065011a940f82c10000c80355005884040c0648090342e07154591001c000111060b4100103a1100218654180e41486610341200c1611750203851400c0c6511300511718010b080307001c2c1c490601b40710759400304078000345240006405881e0041251030141000b41c040c0d0800c80f41a900d901543c40061405407010442101c1603501130f0314042e8a4a40c0794110701c1c0b00f0406600c8980200315401900041840d4100e91007a0314843c1e40d000c2020340101c003504142d00b80c0d400150342003912040062143e5610144c1c3d0702d09488451030406401d903524040382c8503120b41c2440294100700c84000100f0742c1c0e5440109107050710001d4a11603075643d0104103110403403050a002404c01405103140c0400301c05040000d00c401401403400300c4128035204134581c00d11000343d00c0300070569503a03c120148900c0e83d444800061113170403c100060008941000144 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 314233633 1250 314232383 314232397
    0x70f020705031c11242d070c0507080106080106061b1704050612011719120203040e1f060306050d020405061513050f0603040c060509011e270506 64
    0x220104a00c031400d0b8424040d0781182504c40d401c0b241d41c2c04044a25000c48039029254800440d0b030b41000400505110010303105003502c0034401d00e4076064a241c014480b01c2e002d0b00480820651601040c0811000c02110000d80244000007468030b1808841c4ca0858030a03a210b4000d121140c00341c1d072000310540b2511054180c11410310700c21410000f2110f100c030f2285030000c0c0e0384510b01284402d40f602100c190320b81030795004041c07000c1842d09280d4160703450329145800c00402400000340d50001e100f0b048022126081c900440c0e003840e84402c0162074680e0212142085103003181580354000604440c040024090b5003001c0000d03a04100110714115009003010380141e84071408030b8080d458603c0c0a000782ca80d400803094603848034402c0c441190780188651803050074160103810076460030750110382c096075200440c0000340345084002d0741c07584c0284080c541405038015000f51a82907179001841d408441d69103001541240c40110302c0c1c44041c65440350381003139450300103200d01e407214401c403864 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 314234883 1250 314233633 314233663
    0x6061503011208040f030503090a09110405130b09161b15020313021e040b0a050616031107030b06100809030d0906020405030a06090b13080702011b0203070e070f02070503 75
    0x2d40d040d14144800e03144525070043d062800d4040700001401404400791401e010100c0d400f060303a40e0b0340c8245500381d0300090898204002c00300004c020320b14159074694004100000003060b0011b8005c00142c030039104607070310f400c4102d204804c801001e2384840c103612030103064240070440a4030b80d101d4400c01c0302d8024030005200d90000104038844411300501900c1e40e4024004440220301c0d248821a05200c108840e0140781001c0d02000c540c60310392400030607524050419030a080c195204c1440d109900c600650a00000d900c24042200c020b024401c05180180309201460914a080c8070200304010202d4080003103d20901001200210413207107040c80c05400858080e6a0307080401c021710590b40419498480c0c0c0c0d405404010203a00140c1d040c9005c2c26101c03c041d076070f9917aa0b045240820200130301c45d9000700074000040d170040e17100100e0b03884807502d501d442040c598003007464510640c009110f00c250203010480d1045e40b00310005010401071001c1c1c00a10b00d0400070a0365202d840c0c641d080 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 314236133 1250 314234883 314234909
    0x1030209040e0d11100216120c060212040b0a0e061807180606020606010512040b1003020915041a01081b07050303070c1109090d030b060d0f0506030606150301 70
    0x40769140e4024400111031070096415032140c5240c003402500060000d04d07020300503650b51400c001d1807442038032484844501140401401540e80740c009a2084060f03000b808149a162004035050b0320240414420309000a0414140fa0a0207e0203200c02803011082c0e40c24019154440a400b007803590304080c5049a80b08106040703009a400d0610903040703c8040e81d0400503200c801005600981d0468540b50240d680f82e807103420045580d40700313155249802041c8100440c0001c0ca540c1c0c84190b003c0e84034004148100e44950004903044400d803244200c2003044405652207103818820310880c0803980a07803000000c40400040c200800061000030134488030f20008201840280883e110a60301c03005890b507e151201d406010107541040c180c0d48503003001d8201b0000e08114100c9801030a1070f90044c4070b44603c440b000c8001c0d04016005c140c0200080c0140031072840d860192000c206241140406e01d0318003a01030514242c80140000c1c0b0038041c0d04100700500e0444030440b410340d049040c80d02 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 314237383 1250 314236133 314236147
    0xf0d0f0b2101020c010c090e0609090604110f04090503030402030c1e090402030a06020406260c1206010e1f080a020304020904150e0a080d150b0405060a020c0a030303150b030f06010302 81
    0x1d030081c0601400c80c8595420144400e20301d0303501002c010700b6200000712814090b29032109001e04885c049403078110b00e61017040881d005c01d00b21740856041d542c009041c1c0c42142c1d01600402c060b6811400100c482d90b0000c001d00045150511019545034020790340b51992580307056a8154012507240c0785801130791041d0100301035407012700144d1000c1e5045101595216a2840d00400188035002c10300f02e840090031000b0081c07689010142e0241c2050050b15080c5400d5070414100b000d0046c0225051200004001e41030707480b001000e90500c4042c0c0c10125130561002400b42408800402c9039444a104008110060356401d0741c241d0001d0700650000d43e4000f006640030020581138044840c24841c0428000801c02058010940c00805107002e0250825034681124132803124020448040018001800707141407090242141c1002d5104031029280441c1c0070500c11100c07600140d0009441c1c00d0318800240a50304e0329130080c060486410320310f10300384a0002031103a01519132410103030001240 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 314238633 1250 314237383 314237449
    0x150509120d0617210703022e091202010f092d06020301082a090f060d0c09020a0906020706051c0905061f06020a0213090c0b0f0d0f0b 59
    0x240010300302603d80f00000c903c01465495498a08100c05201c0503558210482c418a5a00076a0308007a8150000e01c0d0400030703c5840800400001c1da00320301d1000d541c8040c1031950090041142e664000c000c00c0541194400000b0300b902c0c8240c02059045003048410f000041e1071401c8203428070b003092402015000011b000c2c90704403150320000303081d450001c400403072600030101d094001030744035640c4020100b0328070401d00100290a4502540244a000040d0f001d441c0511000d500c0880101072a0b207941246d51801c141e000c103501311740d1442d50b0224038807040d5904000701034082d00440c002801b1007440c01100419902c5007034801042c1151244200d01300c00c4caa9040026450381c003070b05445207890300e100c101d000745140c40c8400e0801c010f0520001035031400410401492a00078041d14405220740c1d811001402c02003404546611000c0000a0030b2040d40c0050003d0301080c0d45082e80c0e400b40240500285d0b4292a0764001c0585000701d54541c17540c507440141b107000000300d80031050321088061 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 314239883 1250 314238633 314238641
    0x507020313140a1202030a2a0f0f05030303010e0a0f0603020411070c150f0810030f05060a050a020f0a030902190b040807080307030804030810081504150509120d 71
    0x5084880909110301140e450307500011903240b9507040d00d082e04074580d20090302c1d030460844003019405030002c100c04000f04a01c0200c1110641684184440b1954090f0300e0b801100307100c0c3e00030300080714424800d106013215008041c0c001c0004a00660641d410100d40704500240900301d40000740d0384402d080c6035190300e9080303e03000b1500180100080b065070601c00c2095445a501164111021000880d030140504d502140912a0355030b50301103a94900016103504001614440546010003c0000003801c9040e42c0c01005210f84050005410520040c100351440a844010f00a00600600900010b070105031101600180340129918019002080100502424a000d00520700d007012440d102070400510440d003040381103450840c0c0d2941072a84074090729070000c000405a001003408207108246580d000044401080012607079008420f2515119110301c01c060f00d1814100030074800c01203007080400d49110000c0c069403a02003c4030b80c42d040090250408047d01041804030600c0070b40c0 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 314241133 1250 314239883 314239897
    0xa0f020a0803040b070f020a08030106051803102c0d0807050c151905010b0a030209060c0a050a0c060f020d050c011104080a17120c030402040b03010c1106060d031205070203 76
    0x20349030b035034180303070801c8003a00604951200100d200b8407256110344e480018540c030a250044000342c11039003030400c00c031401d0380300045041d8808210318595246642c2440007100020010400141040c00740701417460860340d007001c1041c0fa00000c0713015907200802242c500014505441c000c90103075070b10a01030704da030f000c2d0201140151040301c044080d50100f50301000d0003040342011400d03441804a2068080d10310034014580c030404103002502d4468002d030003400d0724510040140e8106250440d440e2320300940c54000392a144d100714003080074012000c04207409045685000340300e50120001c080d43d12141e10901030204200061810880042948020000f004012034036030303030b00d645202113a41c03100c50300d0f0151070100c103c80e220349251078074a00320303032541160210368400c2d542c81030a200000d4000600c183e07005a01da0103030101555082c4580301b407684494903035080c000403c1c05400e04d800d00092015010f80b503001e40c3d240200c0e4101014405046410202107502d0f5a840303000c07425130140781c2c = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 314242383 1250 314241133 314241143
    0xb0d050a091202010b01020c0d11040e0a050d0e090105041407140c011a0301060906060804030c0203010b09010306021305030c0132030408030411040614061e040f060201140c0a0f020a 80
    0x10008503080d43e06402c0b1200c02e40342603003200c600c81441420010754600c040c20041c21a4002111945a17013000d0704041e4000e0591415a08114180e407151400c0481c444040030009080c0c0c40184402e14080c00818007614054074104101e11041e8643c6200600141040060040800303028000910002c201c0d04d200120000901954004185d05090742040c2e001042c405e500340500842d0105851040e60212040c81d51a1691f0341c84e0350b1002e9544088120f41681c02d5501c7d086400f11603190f0700103030340c02548282e00050340c0d501c0203014903410354000c0d00a03034880e030041c2c0010003881c1c1e4400340011341b060304c0220000704e034180741c40e605c4402d04a41c805185c0481c004020481441000000f540c0300e00d0007541c1030002c0d0083da50800c012581e060003030040c00e080c505442d80705c500740f82c00a01041303101c40d0460000c2d0b60b070f00d0034000d4403504a83c2c42070000e010303202d00a0001c16428084c0230780a8440454160301e03400c215102010501950115104028284e803501c1c031854401c00c0014003858100c = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 314243633 1250 314242383 314242403
    0x6130504150509090c010e1201200a0e010206160318020d050d080a050103080403031d040e0106080727150e100302120c03100f0f1b0e0a0b0d050a09 65
    0x10524403001c0c85a6100790343c0f1850400300007542c0c915010880907900201692011408a100c40400c504120250f2030000341e5966100d5a41b0103849001c0c03d10f404c08840d128841d1203042d0032000070032400c440842070b41150403190034000041003808945014546a09002c1101524841000103c440002c0e020754882d5014100200b03000000c1120b4001a0b6180d50b03104080d904c220850080d600c0c284001800c0400420040010a10822010042c901d003a662803031060310110018040d14407125080907030b81d545e5001004121005c00c05a001000100d1000c02d000040403e50003a00c03800225250a2544801c5118030364808002805c000c1c1000314501c0c0001e00703061048880900050104034000c2241d90391008040300b0009517900440b070001d000b01f01ca440080d0b80d00019042503029400025240c4400405040d6180031342180c54043d41c0e000300001e2000307040142180340200405000d58909103083c06510005011200300b04c08100c00030805032140f148031401001d85000161401d404 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 314244883 1250 314243633 314243651
    0x1602030f030c0310083007061a01030510080303011a19030e0606010e030c0d0302010b0d0303200c03041202030c0904080901030605060c0a0b18031c050108010b010504030206130504 79
    0x8030201844c018074071351000b00c0c81c2c0c9448002d01d551355807000d81021882c22800f1100b00c101000c2c25024030000c10000140380c02c0c444190780e6001625050303251220780c1a450154a1010f580c94400c0580c081584944040441d142c101010b86a200c180940101170004aa201700b2954600045407001700d45002e00c1c419150301030f00020700405084814240b00d00822020070940d40c401c04c002c010581e00180500391401401e01081406046182d0031001d554039524034054507524404e010640358085e88011a21240e00c0c0d000403141c5d003030803111001e141c800307001e83c4840c20700000c1524280d42600d094403004c1505400041d280c500e8811455900000040400c000c01507288007070666880d081e01d06009842e01c9000304031041c00307070f030860241d281c0c481c42c034807004034440f00c10305504520040c007603103203400d40d0204040c00c503841001c6c41e000060203102020f050381d81c42e10480340148050b5000300003003800c0c000020264410f81c84040d00c1031001103208400030701c1000d00b100c02810300910800c03044603 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 314246133 1250 314244883 314244901
    0x1e04060b030f04050d020312060108090a0605090a05100e070303120e0109081206040606050904020a200106060f0212040608151002010509070504060806161b03030510050d03081602030f03 82
    0x508030b90882d4140038841c1c00181e144d00010035923815222205200070165910401121414401011000a403244018400c045480c1d0b00c996400350101c580504400300480c00d000c1e00c1d0140d00500c00290314a00301d000c91146001184500a80742d0501d4802e8079a05c0c00c0c04a040a400915801040c551a00d0201020020040c00030000d401e2645803c40496a4035010403081399458400e1402040c801c102d0b01010780342990007820141400d08050050081c1103a0518403960400007101040e0340d108800d001103030300408a010201641e1000700715074404170300d10700481d015030710410080c403a0900205124020840300d4140d1a03502030801d048910070401c00038041c290a90340c00f03001e4051a5001f15050510317000300003d8803000402800c8a032640c02d0303880c41d980442203442040101994074060b54284540d00380102501030359001c200382c144100034039100c00e8554001c621541c408005140000d820050039903002a25680390741104084500980c150311968003590401c410000400400b25 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 314247383 1250 314246133 314246161
    0xa170c2b020c010804060c090315051b030103150f0b030f0105040b070c050a08070611030108030405150702010c030311160813060201140f070c020d03030212060f1e04060b03 76
    0x505940100e0a03000c0504040c1e880c0da91082c500c1c1d0002d40c80b14002008200700707401c80803805095107424145d0700da90303440750716540e480641b500c22865122810f000c0c80700020071385804501d003c00516403071945141c0d91110000e004003030041513603840c1c039100c80006003a41d206d054410310240542d5102584a0003c078001e00013100c040303921240540100f51030900c20841201e003240c1c01401403016100c90380b1401c00f06e410030b01084407581c0e2640c0c409815241c0a0000c1d60080040c04011900e59050504202c22404013448601c4154424400840903030780c8001d040341010b805003000030361602810030041492180b6203681c105a074110f0b1000040280c841d0081c00407490f01c6504901c03403a11074030101c0c2aa0101030700392154000c80d40200e109000c0800000d44c200c0f00c1420401040c3c1d48039404a4400d4a40034070a402003540030030401c0002d140341c20308a80c882000c40c0c811440c200d21800041926600c08058041403044040100d51a1190783c8244054160507401c1c03034a0349813038050a4119 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 314248633 1250 314247383 314247433
    0x1503020a0e0a0e0c061605030408010608030a080c030606030a0e0c03030c033106120603021906180f270203040f030f0503010b04050f130f0204260a170c 67
    0x25490800310f614840004210b80e110110010700c02e0b8070784a400000700d0500c0d100104181e40c540003c201c0060403c000b40b00340c2d0004c060740e138081c43d141e5005980c007920b00d0b41c0040c84050519010401c1102c81d81da00021241e00806055001400010b600301e0b05181c1f29407030b58200e4161100087c11a840b410000240c00c920500540940c00e0a10f071074210940e08019500b081800303a41c4410034000c0c54003030101d01c800c08016540000d9100d80c0c90b000581009002e400805140c00001403d024459004048248200d0b910108843d49442d100450200702650b102e8186025580341828030300c1c00c051041003250b480f9001042d512070526060500600c000d80038114049190310f480c2000003801f4405680c103c8160503131581c2880d103890140a940c00380303483c0c0c03241e100488240007111007515202c0c4401607018414010703140e07403c00241c80e041d025203000b411415001071030021441c000001e00d0580282e40401c211a600000d103074880310074041d52500c0c41d60341c00b440c501041c040c40d41c05205522 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 314249883 1250 314248633 314248651
    0x1506030c0810110706200d05070306060201020a0c02040e070b07060615020f030d1503060f0b1309020f040b150a170f090a030e0109080d030b12010605131503020a0e 72
    0x300d0500c40d07001004030f4608842030034040b01e080c0402404156554003080100c0200000b51148070022290050f241d80607074403c2c1e5483c0d0f170350b00910443c654144150030140c030305400218036001800760050a1000b1044000384216290f43c80e40c441c01c08148040001002001d42d101d4444000340781c00e50240407a40540e0861082060f003c100481c40085c1807a002c0e444000510f01d4401500b28a5018248480b10216004588100000010344504c40d0300116000300000282c403150603010801024004400b03004d02c2ca042c45002c81c00b60b5241c1c00d091f030f80314104480005600106602041c120703014540d00a94100c40031035240304458000b668440030b10350024101085990b00b132902c0c000182d00340d401c901c296005054040000f1f00422210380d0080050403e502841e07601c0302018a08500b1310110300009407542c03034032070050400050b04081180004000e00801d42410b0204035401d1010006000725902c921100460130341003140d0402540d00030340450049512580080e65084d01070701c0403a0 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 314251133 1250 314249883 314249893
    0x6071a06040b1e270601030605010e010f050904060503160305070603110702010c061d0106082a01140712030207140d05030c07061b020604050d1706010c1506030c08 72
    0x1141c940741c0308503020444024400e00f0300000c450088035400441c0c9594070b03008402c840265150400c90700414060385940b41c1d82c1580c0e484e000e000101a01d80300d40c000c070f051000c4c15100c2240380e80c20441c2e0096180301890100d407201c140b000081c000c0d002940c00150540106170101c0040b204042c80300c001d590280f8111440b0981c0d520b01142201d4941606076201c48081c0a002d006600c10120012424060580494040c8010481000301144208040411384d0768107130422000310305004001030360305a600c9880340c034810100a0000560800680e5040080c04001c0b000140e5401c0c00751215245c100440c11130030894400040c0003548031700340c25520111100c0424280010010744540c00003480c1c0d8441d030940c2c40c0e031440c003038040d0050b1008688040d19030540940c1c59130b03000c001990300d410b25401425541001e0400508128403a003400c02040b44541e81da0300e5020390a100103400600030f03e881d01c201d00d6a4144001d10f4910403a5462650341040c030004103103c41c0148550a964130641659 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 314252383 1250 314251133 314251141
    0x12090a0510050318030406020703023f010b120601050103090c090e03120112021005090d080c030702150c0613020a090c081b0903072603030c0a080a06030b0a0e070506071a 75
    0x545d0b0b805944102030050b4006074050005042c0b00010342c0164680008031788218400540c40d404403454155100c11460b444900300401e81000d02901c030100d0f200399249180801c001030039a48502c03050007914141500d0340c40c3c41042010002c000790040c50340e142c007007001240b003165182c0c407a03000d0b1890081800842001042e01280c41c0308203101182e0003807141d440c43c61200c000f030303803541c000c0000154070800211407200440c1c03502d0010a07884101202466030341d059441004a0f0000c00741c06496480b030300303010413004002d00082040e00f082080c60f030780910a15901c0080d62124071074016800311418085201941c1da00701200d5401207034042c03400900c00c1180043d200c0c0c1d600451a0349a03255104040400066448945612440807031f680868a00f0f481e0780601455a0b005555500000030006002c800e10795000e07510030f812610840052003c06d2035a120345120440180400d10a540d4030303011140e21000030440e040080c48041d008a4442c10541008458007481041c40350426044000003 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 314253633 1250 314252383 314252431
    0xb04020906010c150c2a12020f0f010203040506130218040510020a180801110a2601030f031106010308090105031905070207050301140108210702061c1b0212090a05100503 75
    0x48000445800d00c0307082c100150784501c4003014040c6500e005502641a25100e80e0408ac0544900708800c200050b031f40b030a00e460708070f01c0c04000030012002c450050218900584d100c0d20700c0150308464011182d15520356042c40c40c186620800b82d400d09610000c7d0440d900f64101c5c1d060748110195814811401e0750383c4203170380e00340e80d004000b40080d0346c0104070780711546000b5020401120744072080385450b1440e0030720f004210b003020b0b002981d0f945603454a0404165011011003c0c003104100585100e502d03568610b9280e00410440a0500c2800301c002504246800d8690180f04090141800f8030b081c15503000e91511080e000303c0b0302039401d203205801d000880e000c540c1e048071181402011444444082407240a8000d681d00c0ca460104101c0d0002680d074a0015107000318080c0811045090b0038003501c002c40c2c556441350840b482c0304400400d405600400c1d014002074450b5102e960710841c140c0096040c6002c0e80200b079010041c803084d085d910303a201000d98441c0140301910b00c0075001f4100c003 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 314254883 1250 314253633 314253677
    0x14070b04030f084302031903020901020d30060512160506072f040b030a17031b030f07020607081b0f0d05070c1e0b04020906010c150c 59
    0x1a4480826282c2c2440c2c0c0e00c102c2c80e071000440c2495113800b40310002c45640c04180c00720740302c5031380300c016840420a5156840c04c000880c1150460381000c518144824002030f441b025140c05110900041101100a0840a420aa140d0000d10f03421248410032100c0f0000109010301a4501402c04188000c540c04400554051001484c00c00e620a180c81c00040007103542c804041142c91104008051100010300039020b01e414044001e5002d900c0c20b00e600b0b00c8219020100d03414841d501805006022681001404006941c4444013554940d1444a01c4a240d9822405428521400820005880e912044c018011245a801d644003502d031101300311f40b40301d006d03140000a02003c4a030341b4078400d407100080c18020502d81c0d00303d041c40203609401d07084910071039055010902d110070a008206100e4400389091074142d4426088a000740c90301c4544d804000c000030302403480d000220b0310680c05104d030314140540c400c80c2d045028503051401ca010b044581010030103da41c48030016800021001 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 314256133 1250 314254883 314254891
    0x190503193e0304080c010e030711150307120504032303150402090a0e1306060e06100801120201030b04110f1207020d0c0807020a08030301062a2114070b04030f08 71
    0x1d4003030641e29503854110345170740038084024096503515952001044203002034040030740101102c03100d40b0009801d000241c0000c61944c60000d0007001080b81460700400040840641414006000d40d1149400d4034040001c1341c180e01914070401a042800071800021845195041009040005040203020590090000c0b9590000045100b07101041544c0c0d10b041c0e110040500302281d8034426103411084030900e400c814541d840c50030800460b42003510780d10810b00c0c0b00b8604030049614111402103103034440c2100904154039209c5031aa55076a6420595504404040c0240c0e00d0319024803030f46907980801011b881c8083c0a000103a00070f130000c5014440340c01c84c6e480b80c40041065642d50945507004603012640f1502c42030001c20019410806075028003856240c10902d102404442c89103c0000c52a508068180c14070103070004040c40002c0d030110171074151540c5a0100144140d501c1c00c03405148860806001c1051000d00c1a580e000c0c500031790290701c5030707403070071210410440300414119 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 314257383 1250 314256133 314256251
    0x303010803040807290307090b0a0504050f010215060d020105120a06080f03071109130b0108160906080c151209070e06010201050421050c010207050a06060b19050319 73
    0x50b030008040b4517802c0c01103034030606034034004203229150305144501c1e401914000c400524081000c0c007040c189000c0d4004010002d0004009940402c2191441c0c0c8000034030a0740101c0b600301c0c008085900803c140c800c0a0b070722201c29006440d01f0350806004000a02c982d00a034420180800c40c0c2c80008030407203c6542e044442014005210410b1100d5008080c080d54620956010080e002c80d0000c00b860b800382006001a0000400d8000f8050f4035201c541c024800182c80c100302004004000184201d1081040d44c84815082ca9401e98400a0080615070482810107600304103206001285080c02d8903034a814010320340d12a80012404ca410403034004000940800392400d1803901344454800c402554a4080e152a64180340036081e40c10030034044895501884c2c401c81085a640542c0c4041e024495200b400c1000c40841e2080004980d50b210b01404000004140d40c024210410703400004040d07010300504014560f0343c8030041d030f00349909180c00c0400c02612743c810014550720307070594044 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 314258633 1250 314257383 314257439
    0x1509170304060f20010507090b090913061d0c03121c0b04110a03050103020a1a0a030917070f05010b09100905060301020d060e041119060c030c050303010803040807 72
    0x2122094911841d212a20f60500200c0b4010396204045198000825940b5200200703c2e420680e0016003107603100d030410780c5160400d1021030440d0b2121000c81c1c0d03102130014030811100815040980007800810051001810b6000d0401442e800000302d65545901c254125203507451181603c140500814403042c410800c00580750030503000c190042c4440c040020030010305440304c45001100c1d58401180d00010a0f00c4c1c0e0010025883c05c43c00402c000c002c0d1196001c200301c40d1051821061041b202510300745941d4892000500c40a038070b80144c40f50f003450310715582d12190f0a00703803181840790740221407641c01c0102c45400d5003002100503000f4041002c69100d01c0b400c04040350f019041c02440150503660a104509105141c0d0003880010308903160701c01c80b41c0c00e00e801c00d00003440f40041864003610003d0750784e200c0c4c200175461030b008503981c0b85002c603100c82c1d044c5070442d40356041020140183c8008000840d1200c0c0110040c0101c03803a0714100d0747c030950749000407c08840200d0440c2014000 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 314259883 1250 314258633 314258639
    0x50c10020414060c15070e01110a080313050c030318030606010c020f0d11030d030b01260c0c030d050c030604060e090a03230c2d0706051e041509170304 67
    0x100f000c4e10100c11a041510700c5078420f1315009400f81d03c102ca04500150742d0507070080e03407540c01c10800302000b080b520140180c03e6860f1144809032202808450300c6500a0402806100c800c0c4106444140d00506480e030381e0b50051060b010240448400d40d103e8050900820700c10360044002c2003525a020340411004590a820040022101102035034404034107900050195000d214102480f801501c0000f901d01001000400d5100d014441e0107880c100090340c01700b9030b0820320281d54000006c800c0d4654407104054800d01b180240001c841d1000d080c034050140504149010b14851003081e6401c0010654031040b0843c207071030a032848240c1e504081e2030080807a102300c0c0050741418001c41c0f20340381c010148100e568240e201101c158102d4000c4100b5030380c50508070055010008560312103440f00800468180d032681200e00c034000600c4400501c002d080010480382007284025103003000c0d02c07540d4bd450740c0c1405a8041d0400c4000810f0a1004107084c142c10902d40c0e10300c03240400460420782 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 314261133 1250 314259883 314259889
    0x1050a180201120c27060809030a0503060607020f031f050603071a03100503060106030507140712030e010b06040b0301080c031c03050603070e010b180a08030f07020a0312050c10020414 81
    0x88011388010890650503034520161608030750003440c5e20440360620b0a51600600914015000d005080d058008025890b140c80e40b0006480c1c2150086802658030122440051440c28807250201e8160103243c9050004018107200d007102c040e60644188480e581c0d140405403030b1000b80c0030380b090f00010005034000038080c0c4409982d000e40c49003800000b4546440001e403030128260b00100000b03803120b08000076158410300780c800032524459940d080980950341c00c24404940d0091608140d0380d10740150100b242500081d03c03000000d407800e540e8075154030346689542d01c2402410b8841c4250010030406080019100700001d001840112159a00040c214007900e400341010794944100c0d0004607100705a60206402424001141a0f40d0a4550036500c3c8ca40616402036119115018040109402c00700850312240010516280d46440c18400140c591174241c1000e0320107401480041641e54200c0d0003001908034030b400b140c0c09083e8101802c130603849a03002d14074484401080740c22240c1 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 314262383 1250 314261133 314261141
    0x1020405031207080c1c1d060d150e16020c060403020901031403091009060e010f050316020a15140a020319050a093008090c010c0c0e0901050a18020112 67
    0xa2042a4062400d84012486443c2244640320340c01e2035038030720090308801c1e500210190001c4481887e8003020440680000700d090060b500c080800f40d803074212102c0035901592070315000e400d2040d0204164284008010301031404250000050301c82c2045081203450700d90140c0e0101c0781e0080040041f60300b5a5101c080e02d01a1010003401480706100c04179155480903485840c030840380d42d440800528242c001044149400d08040c14409164480c0c2c0b0060360040c102ca1b448410650403c0e003121044508920f412036003680503104002082200000407950780014260030041481000f46880b009410740403071009468111030011100c0745000d4000998021950152800700c0016102e00103407145260680702010000645681201c80c1140b2110203401042c002d010345403405d51481c2c460122560303811426000c90500a220069a08210001c511040a0701211108802074241024541c3c0a080e05460400d603050130f011340380c4036149032403c1d0405c2c3c2c641c050f0340c3c00c1559070843e81c0ca40010 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 314263633 1250 314262383 314262397
    0x7080d020c033004060e0a0b070201081503150f091e030a08040c090e0607030608010b0904022407050708070501030c05090d110406030f0b0901090f140304090e0a14010204050312 78
    0x1000056103855004603d0b80540000c18080d115150719001c0760003000411009a00403c040807020301c49100980d82c4030064070350226103174040e69580c01c1d140000a1601401090347d0580181c0300303007000002d070307184202540550b100c00c08075004551015000e400400c00c0e5121000ca5900030b1204603401403042203c0ca800501036240f00040c1512140340c4015521070341d0141500c0d03440340b0184200558036210700e40051400000070031080880c800040c64041001c1c0010307204030140b0400c070500d40d01140080340306126007c185030b5550500e252803034448405110741c8100d8002c540700003c007035000c0d00031107400320a16520b251421522004002106110040035030348002c20800c2603420381c49511554015500690242a446502c2e14012114003001003090040780d0526619000195180f480c07201880d500805180b0345c03a10f00038540f403940c0500d0f4000455a8140701d980300020301c000c60480d03c014015220070011184411540c0c0c240d108500c80c00d82c0507840268400d02114100d0094550 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 314264883 1250 314263633 314263693
    0xb01290a0e04181208072c03031204050f0a020120073212030a05030916090509101505240309010c18060e0105030a180507080d020c03 59
    0x7854007540224086458410784000d0002004841c3c10501c110301d03602c011032808504e0035030403515060038010900040d4000080052004d000c100000c240c081140001845000c0d0480c1e807240104101c45081c1c0e007058505a5841c00b0701c0c240e407000c1c91070101e110502980c041c1c4420f08400e2141c1154100e6400c1d60503025412701800801182d20010301030200101c90502d2003080016108101500c80b00701d61a0342c3c14424404a1941d0007074400c04400c0d0740300010a03040560b102da581c000c003d0705040020302c1c4100e10380e80703540700801d26001550121b805102504112410b1059049100b0203d032080f4901e01d9200899440c00c1010b450000c050030f0f1044c0c681d54250b0180350b0401401070300c41e0815620407007565165404040e109501844810600f0346030110303400d06516000d40500229040392419040000000000e81078401e5500002100c0b050344207003111201180c1003450b1180381d10702903240075000d400516059244002011625082c000340503050418507241c40c0d081d184134410201d91 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 314266133 1250 314264883 314264897
    0xf0304020103090f1211030301030c030314040f12060515010c060c26011401090e0402040f060816080c01090e0c0304060905060a09060f0c050a030f0605040204060c0b01290a 76
    0x6040008240d20035101705080c402d100d04d462400f505601e4403001c2c3c00303c56401400104045a400403901040f20740505008151fa204100d00301040d10403a005a69400c145030000a03070321455284108c1c0c290302811040100b80c40c1c90460104860302c01710600d00080d440c0e0244408074490354071a1284c08041e0038030310b0091210b02168448082c0c0b001031030381982108801040441c002c501061401c0000340307040300142d0b01b4000710400c40340c0b001e0406801241c1d5030180040500c4c0980c00303107000d0b005a104030b4050000c01c5640d0740b0700e04550f004200444c090460003d40c01d501880b241c400795402140c100d85a9902c0f2024a1010341006201395030346074a941042c00803030341c1800118002c2c69180700c0441c1d00b400a043c880e054400b10041c40b00306034540351014100e00c1e844015258440c80e01d10340441e0006580413607034080c050540146600034800100010312640203109001014031a030540300030343c0c1c0c1c0c3c1c5404450b50707810203419a2501d210a0481c01520b80c1100040048407000c2c10560 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 314267383 1250 314266133 314266151
    0x1003020415080618040308010603110f0f031b0412030302090316031a01060f0503010b072102030a03180b010302101b300e010c05030c061317040303050f0304020103 72
    0x15070701d00400164900410490001d10029050840f801e841e1031148146215050030b155500030103078003051045800300340d030b1a1245000d081d1004d0440360041c1035890825218205940d0500e000c0e03206440b0000051402c00110070301010000580d001c90300f10000c6a0a140c03180d40b0168080c0d13001c140041d80c18015103086451007404240a03101460041c10600030304121034901d440c3c60a01a003261050107812440320341c1241c1e00400700c9041d10100060b06407514902c4c03030400c0030040681c2084040114140e15090003503400805481d1180b1590f905204020746800307181c0b426480c052014020254a500500c050b00304080301c0703c001c2a0301e140a802d8003031032145016000018690444400f46844050b490007080c90400e21500b0300c2c2408050305540c00380e0000351103030306110842e9040c000c41000c4802031000510903078012030b400c202070318950300e8081d90344146020a001d080701e2400c1010480c0d0b6052100781300780d0302079039815200e0b00c0c50900c0240b20540d5540008004a04050300e0340014 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 314268633 1250 314267383 314267399
    0x92d1505070b0f09060a050c0702011d0a03030f0e06040e041e060504030233010e130501020d0506030d0903050a0f1e050a0506060102010e0a14160f050102010c090302010e10030204 79
    0x16201d89031564000d80f040c200401c865040103000b83c28400418100424888988102e20407039115942c2401e0004540350b01ca10304207609421075130110707800f51a0044c00030900d41c2080c1030b58174112499903070821030342d1480304001d224012401807003101010000000e000071440c25081e550065805050000c030250366136814242c5030121412001070300f1940c000e414250303a00c0d004615082044422800060b120307400c0c2d01300303504140310302803410301503001158152082c0b061004607980c00000a646e02e5492500c18006000c054618500920585203524001c40c8515004801c2d264048007404e032841c5240c4900d00d0b80350f0b22030016121340c81d80b981c01007010300114000240081c419000340100700d00c0784c28024200f11008180070b05590400192510310500401c0118065906c503d4101400010111a40c9050034503000c90010105448020900424100201c3d0403034809034028021005001c0d01200c481c0420303c8000d0104402c08120019417411865400000707a00c0c3c5401420b1548c0e0300c0d00 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 314269883 1250 314268633 314268653
    0x3030a0206181c0c020f04090506060d0204020904150f080f07060309293304050406091704090f06140f032e05010b032503110307092d150507 62
    0x291402048030300c21848111b08003075048109403030341240c0402c002985529800d440328402429544500e80403192882159a56419690601e40107802000241c600842000c00b041c0140a204900c5503103460014100f04005861443c135011803000d400301e13600d0100250050281800120b94980c904c0d180305000200000d00c41c10780c41f60641c0088203d0071300c910010004840c683d64040703000301070140319401028110030000c04040c2500c000400b6525814880020401c210009001d8020b5940150f42d0200581c003900a580c141d1004002c1500c040d0a400308440c0325228126500c0c90f034001d0301065180c07c0c03030420729040c009030503191145020030410013182401004680d40c2282001012405515841030303601500f0419285407840c00c03d240305008072280c901c100102e6982a01c0900da0940c82908605281c64074040c0e80c075160b060040c0c018114110a008203e03603c551000c0c003007030007580882d50300300075800d0180c00c410048c2010351170310450b480c00d259401404420010140018401d880c = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 314271133 1250 314269883 314269933
    0x1c150203040c210206040501200708071d090a0308040f05070b031b090a030807020607050703080d05070f0906260a0b0405010b03040c0e0a09050109030f090503030a020618 75
    0x42c6102c0440d050040c100c2c02403036903480e4403150015001c400f00c01a00c6142c121001c1d90300c00d0a03e001c405d01900200c6d91a1148030a903807800e801942d00c005811030b0001140c00541d0441013030f13481208106000d0784040c050403514290242d11456040307001c2802482d07040d41160040c04442e0207445c26885041c6014403941c00303500b00c004008200003002c5215100190300d4004c0c0300c01d503864003401c0d8000402d83c044500010f000c00f600090020210365561086611983d0b00c0700945654658a0030155815000121056141410140010701e843d01c178800e046083c88550b2031742c01c0d2503400e0402c220703149120020300768000951407104404941c80040700a1084040080116046500f1418002525410b0340f140040b40030034401d1000189103c1051419100e1860203203000c2d96440c0100000fa00014202070320719403800720f01c0d00505602070290070000c500c0d602d03800c801e203503a207051590340e00c20483d01d140144c010b038001c00c0b8100c503114a00404004550210750000c0b80b03081c0780010090a080c = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 314272383 1250 314271133 314271143
    0x807080c06091e031c020405030d08040303141618120804090c0f0c03110a062c1f0905010902060f030f0108010203012d211a04021c15020304 62
    0x40708015008104100600040f8807494070018220303d489900c03a40da0040864050002502510000b03c480c2c1c2d0303a059400401004044514103028800090701d9203000361030980001c1e0600c200259514481207110380200103c1210f4041c0c40100d110440b0035809a21031455000540240050f690001001d11000c813800381101543d507030304c2c2c458100121014030740803200380b01c4c44110101c0030716001101030411300c0d050f0626403501c124040c06c003800d10021400060141e850140740c444180d0b505c644610307400301c40f46003443e00b011100c0c030b800e0b82c1c410b083c0c0070000e0f155403820a0401d500c06590440300b044e910490001c40e1042641d40000d107240c108020f58004407070040304110002102001e03081c010441036000314555410500101c0103110354119540c83c60706072a18101460785007035000c07001800d0500c400c40390255420b0a0040301540c0900941e00c0706450309040740d5049000350003900565000f000c41e40300e2025000350346c80141ca150380640c0c06010b4112180c500e22a2030000394170462082d = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 314273633 1250 314272383 314272393
    0x10914040b1009090b0405040c050603180607050702030d020c060a110703050f0a03080a1404201012060603050c1605030d020a080f010803030402151b010e01090201030c180905040807080c 82
    0x250484c01103da4041c5114416030038007083c0070105102c1d403404419070b000bc2c0e074095569076803150302d65041c001c0b0404140f81071249004000358170380d025000e40000fa1003101903071400481d42d00300700d0745d400c41020394aa00c10b004203c000c0f4190300494050002c0d8100ba8181c0e1601560398590500745010000b9000d6540c00080f840c0c4109035212758100c0d40200b425200300078580108a86030541c82000340009c026400300300800030340e0b80110101d0441c0035001400401c0700580c07018020114520181080304842c102000415500d029000b05442050880c040c541002c802001d078080172001c003007040d520b0b40001c2200f0b10b8a02c0c0c683c0014030500996444a51190a094180c1d03019180c05034854612500140305002c01a0f440002c124404003249100300e0711901f00008042c007001540904210725840d000c164100010190403442c0058000d1302c1c100080e0a1002040d2584825080307040c1144480c42010300c00185103a121035005802800520704101442c0d543e40a142c1c03059040e22055071007 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 314274883 1250 314273633 314273639
    0x6180d05070e0c07080a1202040527090c060910050408060a0902091021061503060e011505150a09030b0117060106030c02070302240a1205060102010209010914040b1009 74
    0x1050b080143c00c0a4512216498800700f521858101d02481c18294100304156044498142454040c0c41c00740200401c4040c80c9a10003d01400031101480500ca00324681d02c00a205400041000e201c28940540414504881c0504000512400304180006d01c1402d21011480210802940784503440300e5000040d40c0180c0d00400c00b1440c0010544400300c0c40c507000c14452400b00c0c03004c030348404802d00a40d40240407246485005411003039000c900010740c8660000601086401c145120024100200846046c0c4038a002283d1084e024042c0c0101004888ad480a0140001030103094000d24060503002c1d183d0383c909010440c02c0c0e10100c4840c1c010040d03c005c0c08800c0c40204e00505c9a41010048404407110180d01d4140fa484042e200d481440c2e0b008600050048000e06201c1600c1402c0c0da031240110070250070170402c0f0240e003181d18a8000022041c1d4014422507e201a05845001b030319860728480f0b8407100c03c1c0155160300581c0b121282e100a441c0c10810910f00805506c40408180c2 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 314276133 1250 314274883 314274899
    0x9140f070506090607060f090510140a0b0a03080f0d05070c03020613240f0f0e06152101020d0f050a0b22020903280201080906040302070506180d0507 66
    0x440341e00618401c5400304920030003503840c8400c81d400244e100070042451b0046060380c03030007001401c0340a491401103038002d0039981c0d07103580040c0100e80801541f0285454030f0002c9800c84507440c2e503268002c445044180003080c0003001920a2110345201246040c1c0822209001e9172425a410400303c1d81060b0320604140c0c0511060f0392260214058600c002c80540301c0803907030f284400c2000c510380d0b4042c500c661080c0c000d40000c02000320f01413052101c00051520f00b030007004003807802c00c41c038001e18010840c04952001c110f584400c0052062105150b04072040704a90301074003402151750340c20045941440e0460243c00d5152000450020703907850440e215800b030f070f4803101e030303031441100d58582c101054182402d10400c049101000142c8031008040444d1a01300c0000d11a4244419070090307842a22100b41140c0b0414401c0e0f030740c0d8944d03464016161307030381d0138040c1c40003005600301040a200c0c9081aa001d07101e1071075403000300354034621041d000c070700303081804003040c2c880c0e0700401c0003032000503 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 314277383 1250 314276133 314276143
    0xc0f0f0d09170705190e0c0306180403210603120f09060516150b0d080409060506090105090f0f100908010c0507030207140105070b0903030406050924040609140f 71
    0xc245048582c05501002520a480b0601030003100e1150f04108402150071201c40e4541c005000ca80050940310708200303000c18501d40080751105d1191000f0000307540c9401c062002c2c00c0c00b450b8140c03226021805101c8180c0925a841c10070ba258190b40c510000000c074200031a043c01040309500d0b504040d8480c410010580c1060b50030403401e1080410420303070005d661948420106402c8141c1e00752802240d0031050180445030b11155000e04980003060621240c40020300481d081d80a0801440c0d558030180300c01400781d0b6a081e400304500703000c0c40c0198140303c042e446e41140002c240001d21003d0328001401c0c43c40c00070140000800010090010001c24800d28001c00c00794103026061480390b9400030b6440c5034034091445000c68001313001e0f0b440e03401801a9060f10381c1c013035001085850720b60031665aa0b0000c0790706944460424011030039000700070580801000c42075030071400d03810014005c002c0d0120b003e44110382c010396904d24040461311030345001d602c1a40312800f0b04101801802485c0c500 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 314278633 1250 314277383 314277389
    0xd110712020607020c0d23030a02011b09050d0c0e0c0d05010b070804170a06020f0304050d030912230406030615051c09020607060507020c0a0905010e07050c0f0f0d09 73
    0x990701c98002d1001058001880d00d1100d54101c0786006d0203c05480c107405030340101b500100300e00000c001840310103000400a4030075a20f05070300030000d110b081460a120128080b0b9180040303000c165061086041410b080410035000d0404484070964460340307030703a00701c00032252405010350100c1c0e8040349983e54081e860041c91640d8035241080c0c00358549442e1413040744250540da034030710a406d201d03c03003042c005500000d0b00003004549801c2c9a56461416900407a4111440d004100c15190468000e00c619500079800490940301003a80500a03250b40314400b400401d2804801c6401c1d4219a003000103001a100ca0768010902d42d00c0c0042c0060101c143c41c0e500020300000740440d0b882c3d40c00b4021000b400300080c3d200840d94080900228655100b002c44c084c01c2130b801c1c0340130441e856400144140c0790b00411b07150b4500381580d40f03600c44100c990078080c03001c0b002d801d980403991003482040513001010321038041d030701d410300038156652502b035080c412102540c01c103240e003004031a040541503000f = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 314279883 1250 314278633 314278637
    0x80c0901080606100216120b060306091b0f0d11270f040f052a010203130902030c1b0601031703042102031b01050103021c0c1404020d110712 62
    0x1055041c040565100c801c0108180e0003070300191440c040c1c452080042802208417040203041d40da440d1901d24a03200b00c0c1030f4003602d0103410900414924100011001c1c0300380310748005480880405107044000302091240355038444845041c1c03e00310768a05428070035135071041c403944030f40300b105409100d0362483c1000c28200d5038248200a64a0801000c129a0302003224540c0481c543d0381e0f40f900d08c084002d0b0f80e0000d805480341602d1807460440d02d841c1041141002c111480c4407060074001260343e0f22841200500040031448c0402241c183c0e50061600419010981030505912082c2680c808032034100510403503002e0300040040c401c00c0030726840a0316111010914601c0d241d26a083d800340d150301042d1420300003c0403a86a58824070550784808007100c40c0c0d003845144000420b01901c0c0a000991060f402001d44951101d2105444105540d00041c030a10403442d1900d031294100d21500c04e2508076400304202003a4500501c0b4000740c090703900c55540d4035100d140c1801009802410a8a01 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 314281133 1250 314279883 314279899
    0x20406022b140c01110316020105011a070b1302120703170918090f010216150614010f0509090a0504142b05040305010507050c101107060b010215070801080c 69
    0x300032680160040789400c00d2500841c1d9843e102040c0e2801048402e144085040c804030501140c0090081da6054030070182e07001b444280d890b4500d441014810100c50b9101903810010607000404164210f03074440c615075902e042d4242c454021518040c0405d951540c5500712103c00d20400082e0b00100280b005a450040e0a100c0301c1c0b404202141d4103403c0380303641001d41030700250b0301c0c40c0d08020500300d1142e03c01c00be5440785103110700d65030039610076002103400d00306103542000012103600c514400c43d0455004680000342130b100540300544c00c08000401c0005c20045000c40b611046401c034050250554000b644c0c0c9801e08110035100c82c08d010114044e04201d21041600345410722740005100c20810107070b210b000c00d92099905118030f90009007136509203001c02c454030b50820050004080c12601352001d400d42880c410045428400c101510000d0078024103010403400d610407000e40c203060041301c4580785100d44440d14100c003143c804000070f01910042c000030700c0030b0040306503010050310814 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 314282383 1250 314281133 314281213
    0x30c080a021305040503092121030106110f01050106092c0604020f0d0612110607050715170901060519061209050109080a020a060b0a0b07030305150402040602 70
    0x6142e020b080d40584811521200810280241801100d100382401001e01020500e81802d04110111142e81c84a80f800369403c04841d041030141c040b020359109200706440c585c2809003e4401100000300d07216a440b078041d100400e500c09106441c040c0507191101d45003513141812651050416850810303981e4210081d9241c5800c0d03030b11b89250081002c980150302c440c100043c40d100c500030500f0541da05420108001000d00040c5200000c042c040c0061484c074401000505c0034078400c6d46002420781d0b0101c181040250100e491200800c041c61070003e00c1c500110f1f014030400e01060314103650603507485004020614140c200800c6c080c0e100c0e09040100c034a4208050400c0702d62200544105440740d24090800900f0743c010418254040c3c00e0540316451050001e603076074031b180001c945040c90070403ca0b0b134510700300361610110303070098a0343ea20b4550290303403c4001d004090f0146140f051100042a04e550700ca00240000d07005943c001c050841c0061600e8501031203c41c50403926640c001528 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 314283633 1250 314282383 314282389
    0x3120906050318010f140105130501030f24020406030e060f160513051c03092304020a0207080706051216020a24050705071406150d02030109020613030c080a02 70
    0x40c2e64005205050085140020f0640c2d50140603282e101c00d0420389071405041400038a5101c0f42c0c16030380e055403100d45000001c080841103070020301000d4604540d001c0e803400021426540c03011582c40311007800d4000888200780034181d0300b040c1c10001c0440d0300d40341150644542004000d6101041c10310f51062424550b00451910880e021804104180040d00c1003440414081c1c034802008043c0c00c000c02008403d01130f84140020410403400a83d60907000158820302e00c10385a094080c03981c045407d08103280801c0000d600021070a81940105c200009030604140a81c2c80144926140d06a90300303505081c2061080c00100303181d040b100304480c459980740d0700003140403a041c2d0108048462200e5414007030366240f0101214202c1c00e01b1b0008020409500402030211144560407411880c0041c3c612281c4404c000c451050034202d104404011500d040502444050300241c0001140d2505401007640c030307481580d4400074a00c1c0d00c17004104008100703107540014102100500700c01c19aa03400 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 314284883 1250 314283633 314283637
    0x1080f01060c02030705030a1115040305070501080a0b0405040b15011d0d210210060b090112110d09050a020307050109060509060a1407050706030b0d080403140102040b0f040312090605 81
    0x520820004002c00c024210b44003040000040c040050403141c40100601d020f6007460a02c0c804e41e40120225102e00c2c030882c218000359029207900202a021143c01c207401140c01c04402403160404680b1621480c041d5140c5219260243e40603528144142c80c240403007a114011129000d03040061000d4006002038008a520001e998104c2d180040c1c01800d08110224150030700d0040704404d580403281007010380000e100081402090000c1c045280d403007062086c5401165441030100307290b5031049200f94004d60003034546065183c041c50406030300e041140e0803544a003404403800d0780403040c450b003035203020010000149800d291441c0c91609044c2d00804c80c6c003d400c000303400f4401c08506121403d000303491009442c140c003ca490388501d62800c1c4150707500f0240c480c3c1c0307002c01e140c80e207040e109043c403100d240ea9071600032940030f18103403450741c682da140284000d894035074ad503081c0f0011031840342080060507141c800701c0c1c40584450440c00c20600610000380c0b02c0c0c0502039500802c01c5682d80100c1 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 314286133 1250 314284883 314284889
    0x60403020d0807061509090c05090705090405040804152003030106120e150403050901110106050105040506160f0b1914061c1203020c0f0c0616030e06030a0504020f01080f01 76
    0x2210030b80301e060f68a00380c03010b40890a080358480c0c034042001700345195658003290a403406810a140001c0e5580706021003000c0507904840007503000c0104180e1420315801c00c5401034401c025076890030360b56100e10300400c1804240900003030f02007402e8800f611440380f401e10741042d009010750302d15450140040d03d115100245103a56644818031503240c02001e012030441c01c02c2085082d0341915181c0380c020241c0d405110250701040d481004400880720510804065070410307141c8a143c6414101044081c0d00401c0c0140c0610410703490000016041300b0742010054462100901d10f41481d8a804c1c0403414000c006940e55864060504803402805e09039030381000c415115511a101480410410f000301000b01601c01c1d05447c040c40310444d8980d00610b5010000010795a003941070424103070f1602c664200361940f0a50900546420f802841c4440350b200748282007543d0084881c1c0007142040e08222941000c80796104108020350070300400210025a00b4a801c407410310b0507107072030002030310180 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 314287383 1250 314286133 314286143
    0x1a0402190c0c030506010f090f0603030927020a030617011506031a0a03110f090609010e07110d030f06061704060b030307080d0b0102010c02030a09140105040909150605060403020d 79
    0x181d050210076621640a9600030091320308540e1280300d41051101035101c0c20103101d00d0450a6007803080d180c890601900e61559440c003402e03103400312166030454203205407080300715042822503440143d0310040c402600c3c2e07030301d0102d4030614110315000b4445181d00300200b103034104024040211840c412000a5030558200001c40c405028603801c01c0c1c1c1c448200454021104070002700c00c0c080c035002030b01d103019000c84407801440c80402c140482e04806581180c2c2145400780113008903040b41507040ea2240713152400c54a031040c0318424500c0c01c0580d11856001c01d81c2d03401510000e52003801818003134400c0342400c40744041082401150090001c00203040141c0c0ca40c66040c0076a420f0048403001600030740b0281d02c0d00c161524640c010080125034501641c600031f45890054004025074040d00313110745034143c050f4580400c041c8150700622106041040401c0040703800d01591245080403030141980d44c900c18018101a01118210740049105150a001c01c02c0140c1e0380c02ea900007155405 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 314288633 1250 314287383 314287397
    0xa0501230f0702061602091501020a0803070203070f080a03061401020c0d0c08010606080603070e0601080f1012030f032d09080d061d0708060f1002120d1a040219 71
    0x21001c0d4114500030190002c0d440000041c28115203c001c030015401e41c2e00807100e03100c19481b40050b03c0e040007141d220242c0583c019800000126198101542e40311046006076454038229a03502012900022022075108a01040001c103181d0b041c428800030705403104051406822150000c5d540303400842d1014030503001c040900e020807040c1c0c908071004064120091066580300c000180c01840101c030014028480c04100003101500d074003901d03000c0c8406841e416815110004401d12610004209540120b804900001e04d40b42803100111a24001e42d07501e114100300030001400c2d034191902c0c4031403a0014a51b01c0000980042d80030584071510900040e0010862034805040d02a1080c450b0310107150250003c2c0c03616144540c103090841450750714a5541d44c011054400302e80640d955500b000c10140c0c1610303607050146c00134007100c0250048800782201403184840c260700c582c2004c040603441d45c10601043e102d00d4456455402c04440960510f5840d54110400009001300c3c11300700100 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 314289883 1250 314288633 314288647
    0x210050103200a090617120a0801030b1305060c07031d10180f0b0403050d020102030f01030803060f030d050405010e0306090a0303180602040f05012a03080718030609020a050123 78
    0xe000361100c004c000e40407081c810946c0d9486126040380720010003984501406100c0d200c0d00000d00c08654120320151151030386a400d41d00c40c0e1128410080071082c41000340c01c0c000c800f00744200f200d0307842481070501d107aa0700d80c500e242c01001207400742403005500c10f0041590100e69900290000d03848020f24008504054075001c41451148913482a0000e10f5141004a420a60000100140c0340510111080c01052420032401c0380f208940c0f0a4000c1040d030018400100108004e54208400a000c5203140d000003002906120544c940480440c000040230021540c000106040310719044020f480c0c14988054142d44812040000500705665a0300c2d0200c404002c04489122503000388045480b184c940d000c0005500c0c0900400740850038100b4800304190088001d0a04800820700f902130421003950251200113001d080d81080c401c0619a4605480405d0b6500c2c00450140602041d10340c100e005020101c05c0c581c11440c1000502c1e01403843c001d207081d5240b401e080744c001d9820758400e4 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 314291133 1250 314289883 314289889
    0x200c0a020405010803070c08060f06010f0311120a0501080d020606130e030304030206071d100809031e04030b061522050904060506010801051e1519050703021005010320 74
    0x1904a5000394000d181c40004900c0500000107804090304c208404441551100089660389004842d07420322890000d00241c20341d445034811090903200b5050101d0409034228111070150800f42e401ca04264209080058103c0703d40125070040c100d0501501d201c2c4040b55000f5242c040c010301c901d015a801501d00744c00746030f00b94405240e821441040e03948a04080c076001b92900740503145240007071445144140c000360b054000c42805800205013103c0d0310412907003035540c80b900074229682030006000e031141c0e03504000f40f42d1040c14400c502c0d00340e0755410740c42c181c030036084082c190303030b0007450315444908030281200100e80940c54110301d801d0b5111000c0c060440f449902c0c1c0c114030b401604001c00c0c00104080d5400c15801041c098a58244a0f07072200305001e040801c00c0d580780b15144e80c082c250318a50915840140380d03142104039291416a103001402000c044c0803d00c2800501c00203000b005040d4188440030002e8403410003031095500d9600c850001507101042150f1020f41c21001d000700366 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 314292383 1250 314291133 314291143
    0xc060c0c060c030705070e0f070e36070201060f09050106090e0405190605060102150907150309050118020a09060506030a0b0415030302010b0f030f0d0311040306050c0a12200c 77
    0x164170030100c514403911401d900004c100b054410822803e00d50021800050003105410141c9001030a9810f081b6101c10621b1400201d803000002d4560041e0783e0183d1060200043d10700c40d80e455000443c41c603283c405060060300b01e40c0c3c8460040b40c90070b801030001551006207201107450507645020103813101d080c45401d1004a020300b032482040c61008070200440c5400c042d00c82c807004d800b036035025010714001d501000e4040791204904d41050005011881c54158441ca161110340b900007a4491540d139071030b00312907140c3c1e121a03914914240c46001c5162070700d8184058526800180009440c0c203000c5000303400040c014201c2d09458200c104010340701c83c1d102c039411200c030070310f1420340c9036503030130701a00070301135810018000d54880c0d445035540d0900142403884100407d00034860b1018510040f00100090303025540d42c0171040000101150b15401240d020340003d10f4503603500c84000d20094091502181a10b13480b5051440e81805a24100d40300305070840c07500341082d501c60b0847c1c00c0d00d00f06 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 314293633 1250 314292383 314292397
    0x1020f150114010507050d1817070e07050711090a09021801210b0f0403051309050702070f08030a0c020112090b1909240f02030a0e0c060c0c060c03 65
    0x80c0c42980034404a00061010860403100164001c400303980c10180115040d00c120003010b40142d1240480d00300961094500030450701034813100d4aa442e4039400124540300c00b21703010b00100e5020fa4402d000d075040041035940c03c07800070309001e4540042d540d510b50001410b403040034407444400c0001954855190401121554018080a481c0840018504840ca000e0203000e410010100300079150340c000364010401c864001c500a5005c2e40e4486080096020081c4218200030050241c200d02428442e07820001c1c010b490404146845c00840083c0340544a03440090303980f400541c10040c0940110032104404501d1602203000107140c00180ca0031007d0b02819851079242c00b141d202400340d080c42c5640904a10005403d0490b04501039005490902c04c003d001c0404a0b8600d08a0503004020310300b1481d4548808280c12040c1c03d948000c0340c10172101040c45641740d00b1074041c89403040c814041e8007207084500505090000c1c1c1d450f0754403400c0321081801040300040c42905a0400c0044e02c0385 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 314294883 1250 314293633 314293663
    0x7180c050d060810050a05150409020a09020309060a0c0903020105030103030f020f0f01020d0506060f03010501120f0c0f0e010305250e03030301080c1f0c080708072001260601030b0102 81
    0x10b09a500e406031a5110400103032a480d6030700d00004250110600c0c0074040c041e0200d041c100460030100b07401c0000034520040100d0740464507000010325240721340061031240c40e0101c003604843c50001d1401e01a02e101c0303110b510409c0352514003440143c1c3c0110540b41969010b14141c52044401202a480c1030740380c03030600176540f0508110990001e0150010144500c000300140400d44418085c00958002d6040740d080d40f036424001070000d541714100304002043d104001040303020b02020140200c40d808080f101c001a040c0120400c2c89401c0b40c40c01c03810034001c2c601001b0620303050408184d9500b00030002c0c85d22600996064240318811490394104200c0102035030b030303a560f6580c00703965164400c84a19009400740c02e0300608001d9200c5103001074501548416402000c6940d51582c5980700980c12950350b81c041c401000401d940b03040204058130140201814005541d0000d003a0b807150b8031600d01030021041c0300c59a05218000c119400010a00300482c00a00c10700060342040e911120400c8 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 314296133 1250 314294883 314294891
    0x915051806060f060910091d0c310f09060501050f0a030b0d08070821060d02091306060b090a060c0507050f04021b01060501030f0903020a0b06042310090501060c0b060f030d03020c0f07180c050d 85
    0x17903011052f40d6418221400100c0410070300c1e035640c005442c5806521220401103800340640b50b8601d020781c00c11151404018803090079441e01d903a84a5640d00100c00689580e54046141400c40c00c0c9607000290702c0c0041000f001461030b115001440c040e021640080c0200704c0321011a10709150020760000c800c0d80200e061004545a001d110340981142c40b40d41e103e003000600000f0451b008400e0701c4003c3d50024060143c1900300028000c1a074103145c0c02982195007080708001c080380c0301e880c01c450b51070140004540a840c01000605444540c82c2c2c4882d20742c9030154620029800041d810b2583c1d500c480099509d0b5103240010380103000044601c5503500da0451030080d81c1c4001c26005124185030381c1e0712a030007602c0e445d03c03000310f92003400b900d804a1a440030010210f0300c9050129840380004100c240825030300000f0030b081844507000304020a40114201c118030340f09000c03541855881000408881d0324284142420314540d4030900314403540d44501700000ca10a5080703c0c0c80c2d442c4050240 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 314297383 1250 314296133 314296139
    0x41b05060a0201141807290f0a02010b2b02130e0d080f041a1503030c0a060b04090201050a080702030d0915051806060f060910091d0c31 60
    0x1c0d01a01850301200132090710407000450008481d0a000001c00c440002001410304045509080e500700c481060f5039403044500001c80da80f0140020240b004e14445e04649034103078020f019003900c048010340c900c5050191108241001a4040c645520800c8101d51442e200980007080e800e901c54180806000c0c200340c4007410030200000c0201101030315503540300c0c4640e54503403071208078003065800038141011a02460801140e103141075800440a07081a103241d440b0303000080c9140d1040e0b60502007a0044030307501c002d0101e180b0034640441c81c10340d020300c0062050340c0000c14600c209000c04050208000c0443c110385c0c820010b9840a03220007030100300001060401e03201448841d182c00301d1250901c80041c1c2069065190f401000407100010505074480c4410402d418062080154000c2028011032013140d64450910b121881a51128070b442414006004100c7c0090f600d010741c400308071000d0014202c00e0f40c0444034200880444c03c01c0200c1c0081520f24014129000070300003420b090004 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 314298633 1250 314297383 314297387
    0x90406090f0c11060415091e0b06041d0c06030408070506190f02270117010b0a0e0102030f04050d150c030f0b0a08062d07020c130501050603041b05060a 67
    0x1e0024664035150b840940880c001d480765582c030308540040140c45103486d02590b02c1400e4218100741c074030900c180c0e29102039003021188882000a000c0d6003003801001800340d50705151040341c125540202e00070407062556151290707a4166051010700541000000500723210440d420790341406d6012040c0e0340340e1306210b1303c0300840300400c0800b0042c00e450403c030b500b5425998401c84a81c03060441103180c1d00440020300c49501d54103070f803c813418041c0c0e80a122084002044016001e800780115460b12004851401040c683c01c1c104940d044d540200304610402d500001501c0840d00d041340c040a00d05102c0c941880100740c1095801026810000002d01c2e040c2c141e000b103603400380d4100c010480051024204002029203201d00040d6811041c040341d01c0004001c1540d00c8440d101c150614041494103030f40082000445030080103030800790745040f1501e0501c1301440c4000d81c54a0910855040ca0000380042c0f1000c0c0005058a4403010411451b14003016640c0003420014641038441c00c15a0300 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 314299883 1250 314298633 314298641
    0x150608160303180e0114030f3003010510030b030111070b0907060302040806011811040e06011806090302060309031218061513090515150405010909080702190509070c030807031e02090406090f 84
    0x202c549d12892014000e8a64101401500c4c12103100420380000711601010907070080c009190b845806548404040a40d581103000500c4014800d108506d0203103044030702c036414084c09401000426004200c100109500007074000d05507006c04400302940090002e10100901000301080706802001c100040c5010300400e54610449003a00c880061400000c0d10340e9055043d80602d10100c0d94064061000d41007150103542c0c0910042c0c1241d15120014409400d840000c0302c403900707011500d107071034941c07140d050040c190013055004002c1503181da98800540003105a00f0428903d41d55074040e01c00b030240412007050004600308103804c0030306002101c443c1c07035610780c40150b0085083c8000014030582c98442d89201315004a00c490030210103070b0801855028101103400c03840f21051000c610740d501c664502d8010103040d2980d0403080d0191401901891005056506151920041d0580c40d900e20964400d910280c22005070740d240c001000070300503d41a00302848d018a40348106001c201e517070384 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 314301133 1250 314299883 314299933
    0x302090a0525210e010c022b0504180605120303070801050603060414250203071520180405060108040b01031203150801020705010b03060112150608160303180e0114030f 74
    0x4028440030007980000d88c2e896502800030f070040540101003510b40340054a4148000030309160541c40c09980c0e5210f09850203800c010800c2c0a42d85000801440c640080c55a81220350305000d54107614202d0f101502c45a4140700c4d250207a8000000a109980c2e158010444040c000c41c1c2000941031442d41214800d208000c800d44149883c0711803002140004182d03501e0981c005c00c00c04195004501000241032004890f190840d00070748121045502040942400195841401401403801041000f600c03070150519040c00f60b008140800b00e208000241d0560740c01402002040100c00ca00310020595016030b40c5025407406400f04040f40107400409101d40107030003e00811070b524003015201d05007841801c9145000c4c8101c0741c002204403607030000c8218041c03400540300d595000014140455880c1280312405841001e208068004200fa218601c060030308901c07450910115032090a410300540c059400086040c0c08a950104440d24140c40c0c1c00041d00c0c40e01c8400207402d02c06907020701c = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 314302383 1250 314301133 314301161
    0x290331020a061112160b01030308040215040b090103050c0c120309060702030306010c0f0807082a03030c0702040f23160206060f1306030206130302090a052521 70
    0x60700050110b2107041c007441142c0c00400601860400803a2845007a40a844c41400d51407901c1c2c0d080c40415417241400b402940039454800c1c0300c0c900707403041240710b098079a40d03481d071018180000e10422600c481641c501d41c200782030009181c0c80d00000c0d200240189100241584074032040c0903503110ba91406540200c00d40750840d8003507100c0c0c400031380c0c880c0001c0300da080c0054031292810010582010916014501400c242490004141c42e0305010b0b83c1700364190000d0346940650f210546c4c401040c100c890071030a801a45c154205019407440e03912406002a00c60f644504603401c0f01c074071517800150710180d6801440504850450340031280c2c1c40481e05071070031005220407100c0090000c0341403441110b00520442018000c4020072031064155011040c0507603540c1408801a161100100b2009000c0040040f69030706d0341c41040840040104149074607070a00042c850740c1ca602c42090300541144440c081216502c510302141c210010207207048045001024441200071280d10504d044004c0f1 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 314303633 1250 314302383 314302399
    0x20d0e09071b15060e060111060411010c1104090605070801150c081b0703061a1801050f0102030c0607230a0c03030203070507020307030503040e0129033102 69
    0x50000c004803440c0464080002c40c0c00b240c8903031051820034401c2c0c0c091901c101c1c4075008140140c0050350850780e00750030801008200d503007440300540e0820201000165000d004142600d050354a04d910034055008030b0741400410f0000c5410021901d040d80110407000d4810092901306040120181c00180c910001095030280003203040ba0503520b4091036000c6a40310082401c5c0e0321340d41c14507181c1c000385001c0301c0b1851220050002640030b009010080d80a608089160034680c1c0308440070603450a1f00320b208680b880031104540c0c0700c041841307045803001c0f540c0c40014201e60740141e0562040030000c0501d40225000c000f00b40b500714860403d000401000800352001614207014140700f03180701040400d00b001d000e031002034400c2d00150703400203041ca80b85040c841c41c0d5000c039103400384641080300c0350380000c503050140c000f810342003d0042c860520040d04060461017416142c081c015414400300c80000006501807040b000003580b450135203c0048070011800010310070014031240d04070701c11181 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 314304883 1250 314303633 314303657
    0x41b080907080607050a1b0c03061d120f070804030b0f070302090d0212011e09060b10051b010b060706051b090307051e03030307051222030e040e030a020d 68
    0x10015001c01581d201e41c2c001c0c5040d44035610b00b40d0f49500300006090802503680b0108503980c0e80910040d88482c80740e10007420990562802c1400d460700040300c4c081141c450032002d000072038001140d283d03180210f6882e554540ca030717520015040c8a1503401405002d4000350000401c040040c11030b102d029841840d010503201ca250403002d906c144110700b40d0107040c0031022005880d0000c400034181c1702c460300000c2d07030b050904c01d038a110b42c0c420300011040070340e14000d0805009603401a1260958110749811060b2181d81d00907242c0c1c0a006070003c01001803482881031000254814400c890313005042c5074441c40c1d10b18144000d4403003240c1c6081a203c0400c050340c0d4403805c2d24140ca604039001406809058200b600380141101c0030907101311080d000c04a4100d86031000d100460142000b030307542c183e9503218440308000e90f8001820503400070414242002c07881c0300064410000c0f0740e052401c2110740c00c2c2c244c0020003500b40f59180440a010006140d450b550700002c40c0c403c110401d03141e82c000d00134 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 314306133 1250 314304883 314304901
    0x2030a02010f060b03220203011113050d0305042303060a0606020c03010b09061c0206161a01030b19150b030610030501030506012706060201140f160f0e041b08 70
    0x522445807884c000c4007840030545044040300d400d50105480d42e102003100b103035900000d0a440d04180e01d01c00500f03000a100d005103500c40d6604014100684190010000c15034000340315200394440c0212140790091890482ca40c05031010b88250402022034181d401c01c041c044008041034800d10340036224003001d00289040c10300440035500300c02071034910389560b100c090008142030310030244960031003100e02ca40140e882402410403502501100d640c0c05200e86041c0301200c01444102c01032802810040001952400744140c1c0101080b04031074080311118048009844018400015150a01808101100c001010310700c110400c440d0441e00c2c0001c0d0009900b04d5100b804058400e1300000e0042c40301c282d603a0b22500e03004c8400d00c411507010030104d14240c02c03a0921340081c00141d4540c03080c240445e503681203054004032207488100030b40c1404560500c500c01d00b418400103101e00504481030440c0100c655506820b1b02400c00d0010301c12a00b18914401d084903040e41c08582e442d4003288044c4 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 314307383 1250 314306133 314306141
    0xa1202070e0f0f18191b0512250302030a0b1b070f020d02031e03030603060109021207030c11070f080d030b090406020d18080910050901021504061b02030a02010f 71
    0x3a180b80c56011030340c441143c201c40c035041d04d05130888284282c86201d0070308a110202c1e0000b141c056040164843c41035075030126030b5a4160321503840381c0c03908190044101004602e8004a804051405e100301400c0c4800440440c01c1d68000b0b9030502410251806028404a1a0b84650881c0c0e6804085007040000c090b460300440d04041d108983d9006a0303001400c0061600d05c5590000701141c0355840c0081e08030303810101040a2107803541020007130125a05040201e5409481c81c440e0940c204110020660381c6144010402420182c0700c5190503c814044c10380d000100d11807209441280340c8a1045e25095031842c400c1c0324040c451a985191514840c0c8550441c0c6500101007d079680c0722a110f11000e5040a02c0210b02c05039903000c0500640480e19044030043d05c01c00b045030301e81c0109801c004401d145810440140039080040c0d00c0c8507a0f0110341100000030710507250101380c59905004009040600510400c94008222401c1c155000006811030203490760003030122040d1240c200b4156 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 314308633 1250 314307383 314307391
    0x605010e0c220b070f03030b0303030103020d08033105070b09061207020708031306020d080f0115020c18011a13090504080d060608070e0607021509030a1202070e0f 72
    0x2401e01403140900c191002032201e40c8180081620400c000e80700c900b10340342c41d4841c000c11620b20b89071410312000c154042c007a1400300c0100318041c1d03041d5851a000300c0c40329101040000c001800020008155010719018030742070110100b441c035180307a14010803149121550006940e14803405400103024038a000c11102e408030003070400e508180030702804544200019000f01d05501418038040340c1d0800410181ca40d06c029110403516803440c007a4040c0c200008548400d040015030780800a691112080c0b0034110350402c00c50881d4003002e800101d003003640360045150f000303040c403041459800b00c0c100810b060b2056940c0c00b008a100680f050f280a2083c00380135000c0b0310070040104101103890748203a50090185120902d409048005101221525003003500402c83c0d01d0140b102e640d602c00c0307405440c0d40342600c4051400c84190006596542081c60050740880001801c8259031802d00140e000039030701c0741c6c0c8082d8188a26001945441d054016443c0c0a03c2104c0068001e003041d030303880f0303000d = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 314309883 1250 314308633 314308651
    0x6040c1d16030504231f051005012303160e030303150904030e09090d0905031501260706090305060a090b1911040f03020a06051905090a210605010e 65
    0x8480100705041d805003200030b000352100c500900c810441911040001904070203890040c100d44000708041c80e40c0a80300410b403017002c503e0700701007001d6601111200000e540b001d081820100e111044140c005111490000074811008401c1c820400e1140c001d0b00d14940c020340b2080d040356481c90605a80e40070880d007003480c884d24080500c1039414012890780e0032034024038040d4800340c14071012885d940c506440d8407403a584166a0a04480d40c48260320004d000c0450180614580c40304451a510303c041c01201034803800170400400d1802c4610021051400700810b0300c5031159525000b610044c0b151000346c0b050f0090300001480d00400c1e01c1818090340e489401810103459800820802e100140d10294005070b8600c4814903066031b000c098401130400d6454500c2d0a0700f18410310482541c0d980c03040b01803103c00d102140c0304800500305044061141d1820079103e010180015011480941c00341d108040d6042c1c0d00004584045001c1804901075901446141d07642e0b002028252000c58031004 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 314311133 1250 314309883 314309911
    0xc02130207020102120f0706051f03080c0c03010c0929040608061810030228171005010909031d0102030d0b0a09050f090f0606060403030302070201050c06040c1d 71
    0x802420580e015101d4240184102c4042801709070320410b05a101c22000e980d40c04000c9906d104000c3c9602640340d2009040c0799034180c3e80001380b165000c114003030000030050500030607410078001c81000400115000100240490303c0310513809483d1542034080e0220017590482c02c5c1c3c5280011519401480c00c833102c520303182c50300d0001d0441d805000908051390010103444003540f01c0c9030f09040d45004148d0001805c22261451040010401282c80c01074040403c00c0c051443c1800c40100c18012940e81304501c03450300c0c00c2c8120f041d041c0000040c1111140346000008183c0324a6544034210181c072a441e407108003485d03010185118620400744500590040003459000f000c26085681a800c02401140907146c80340c08110654074201c803540d0980d0801d070200312950300c081052500f0040d00780090046030414402290543c07049000103018075070001250b008692040c0c0c12202103180400a0352400d00b05841c106104031818414004d103c0300582425881041840f4801d0041c00c004c41459 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 314312383 1250 314311133 314311159
    0x30305040909030309021503010f05031204030b04050321060f03010b090109020a0e09130317010f0e040c080303090a110609010512060d020d080c0d0c02030c121c11010c0c02 76
    0x1c8050b100301801182050788402e948401601c590411400d41201c031000d503030f201d6045c03c8140e005114030307901840c440d030302030510503c401d40c105040380c1c16a0b4002c440e0406581d41e5060052840c41f400103002d8012030300c00030304076001a200207110f02401c3d04803800101c40420380201804c0e68644038442c0c3c1d201c0d04090041002d90825070090844007a103090a10b9103000c04000152a400e04680a03000101200f80e00820503602a100c00e07450030325524090003035410300004111800482c00b0329100c0108002c082420302c2020401c0c0e10051030300c03504803560382c64440e09980e00c400d01c40c6012a610340c5410700e07214a616100b416240a0a01a52200d040840800c0354014540c005041507402c400065940f20250f110220800e1003a4040e1041503501c45507116801d1501080741038080030058145114401a50081054141d965084a1682d0319101c01c200c0181482c3c0c00c4500c0103610802e00410420040e040350f8110403014542d4001c0101040c440e1007910114030458000358046560300d07100c = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 314313633 1250 314312383 314312399
    0x20c01090609380c0a0b0105090c03070c051207060c11031905070204060506030108060f09011103150103060906060e010210020408030a11030d06060903120201090210030c030b030a06091b03030504 86
    0x5800d950f0701d55030030100154128000c1200d44d03c0345400340402d80107101014180403500000600400c82a9241c0e0721a00d065030400700c040c00050401004c1007595801041406810000064004a4082e0f410b548c0c2002707140c040000d010407444500400e107450fa60040720040030090f110301d006480c0000790a41c01228040b105580003c03001c0380d02542c0c0d1500441c082d02e50f000514045c1032440c0040120b401c00000300404184010003040301c5030b04103010621300040360021740b9000f550386110400c00230301d00340050300505000d81101503c7da250403030001341e1660000b0b1030785100c1d000f0b030291001159480390400030f80c0f28501580d10075520400001c106584203c00d881c6221910700266402c00c450000030409a4620354440320016101c0b003000c4c001d0025007040e000c0e4802060000b000300206030760204103c2d0480301c440300281a0b42e815000d514901070b4101d000b1000c00181500c011746030510b0004020600380c1401e41d240404d101071240c411109984110940ba090303150303141003c3c608050 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 314314883 1250 314313633 314313689
    0x603010e0717070e220e030a022a06030a09050109030f031503110d050708070e1005010f0206011e090612140d0507020d081b0a050d14030a150e07020c01090609 70
    0x3110000c6480003001e081000070702c0c070400142035402d2001d5980d94441840c00ad1620720b100b1074000c080485000da515060750543c00e0040740603010780d4500d2716a6a28a95440140200d44c0d024202e5400c24115104042c1d102d0b11707040320a1050b880c10092001c0440c0b071a8003945d6140402407030010072042140b5503140603158003181601c41c004407207440d0f0303d070445941828810383c0a5024082d600302070000076908031210901400d001c1c41e0a0100507259200299030392018420085407207080320f220b503010002d005244020b003903900d5040c45902d5071014451820034070340c1019500c112440305466504500440d00c0300445000742d41d460f00b0f15060340c08106c0e031a50514021541d00c801004401300750360020b801e012003201c00303e002d44215100303400c01e581840d542080b100100451304440c0c401d10045403081c0c98010fa06080c00003188001400c4000b4880c80541041080700c44150801030b896a0010380a450904280d95602c0c0450399888180c7c0c103030f900350080840c030941c00c3e85030260301e540b0215 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 314316133 1250 314314883 314314909
    0x80901111e071106070c031101080c030610030605060a020a0b0c0c1b0604120f030809070807260307081308010209090a09170a0906020f0a120c030e0603010e0717070e 73
    0x58103448500001c006125540201006c540514500c0b40c00c100744240d0201000c03820b0307801e0a10420601d8a402c170000a4440203140e00c0c40f800e40500048207030b5100750f0144025003400782405950b0458020081d50f1418809021220203c400e000100181070040c19101c095413803c0042100c1411141c10700070a502c5655040d402804c00c2c80002500705040500100e02400b0b81d052001c0d40b5418240204004001064001c0b1540325040c10043c030b4000082280c11101d0407200d00e0040b801420014400d0618021f95141910000c1404024003126030010031342d2408000e00001c02d80c2c4d40d50003040c02d0380540390500c0c0d4002c0e8500000b030700c2c841035030b005994464401c1078a40c1007450200038a03c90b85d0006458040003980c621002e00c50141c041008940c443e0219004202046007592540d00419928100204004441040300c04060140706001c3c254100144100e40325030b180c4000400202c8200c0f03030440051140000c142803221813480e500c2c0280c60b595a184100c2000d082441000b6035050 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 314317383 1250 314316133 314316143
    0x70b0703090b18101a10030212090f0d030b01050307081909080306040c0201090f03260c190302070c0b0306010908060f01030302120a02210c010903080901111e07 71
    0xc03041c00008000926451044105812844040300511552440c1502a4a800a080d8a4580040c5020b00d032500c0300d942d04881200c14190b00800484103d0290280902d140d00680441d07050107481c1d140840c4100c41e00f070034441100e10b405000c140442c00d44488040d8180410020004104890700c940302d142e41c042c2d00004020a40d020404032a4100c1d040e541c8180d594007030110501840b4034043c06aa140800ca80c4002c0c01100b04980b0744543c240b88411008041c00407010040f039940c01010410400204030003d00c4640e45028418048141c1c4030309c06e140c966020303401e9200b1003940684207417003810b03400c40a8240202c0c1403001300b101603803002d0304050500c2000301c40040e01c100c0821441d0300c511078500e040c0c8015451450080d192244600d202c440e1203806000401320326030700141d19400401c5e0340480190101d03c14090000c00d200701040e002155080032444030515170010f41d1103014000c00e50003044078010054880301c0a00035009000003084001100304244a0f8040140020038055 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 314318633 1250 314317383 314317391
    0xc01170c030a020418050f0a02070c0b300105010201060b25050102090312090f0405010b0a03050601091205010903120e0d0e0f090108071d060d0b130c0815060411070b0703 75
    0x40d10820744140c1a0314000741c5c2071500d0303c00b04500105800e0201d9003040f06c0a0095042003001c1c0d403400580903050049104810001c60341455003c107641450100f4280c4418003981c0300d100000d40d04d121a0309000b540e002d5800c240713001514442c044100c5210809286031001442c41c48168411a0350105600342c1d0959000d110b01d1300c150b83d00f88035010680741d000404658852110050240594848424070302c550316010040004070340c1c440448500c441940342c00904d50740d0b2440180c074581040e40041103c010b003014154200901580f00d907804074080d494001d504640700b25080c003039688402801001d50400c0b00000c1d041d5020740041d00015000401c00d000f034030186d40100c0c0c1c403c0c0c2c090744403940c0e95000ca14100071000d1444c0c10300031000707211454102a441e0810200c0c480c078813100030040904840c10000307600b0f5058007400e0510300360b0003d000f2042a50360f428465540c503041c041100341c00511000b20303d0728076003840f41c0030b034491801118900b848155202e44081d890010200400c2c5512 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 314319883 1250 314318633 314318639
    0x60e01080405120307020a0318062109081603121a1e1005041a030105011706030a02040c08100b0301080a060e030f0f07031d1509060909090f0c01170c030a0204 70
    0x8030809544031700e1080d4003c095141080c24000c0062040e070705034510784481a1014442e4692241082c1040302400d11903540f00c00540c0c0001c0020121030314050862003012039078101e2004050310303410b9824080d66800411030440030500089492404034601c040014440c1980c150070046802d40d0700b001b00d100d0080031110300d000401d10324051200c84000042c0f001a00744183e40c0085010f010110581c0f180604660421002a01f4484160b46c01d44c1c0308943d01000540c1c40d0f404004c8403a505602820034811000141ca000e03141d640d0075283c0320624140c5100c0400c5110030042030f80cbc1280c14442c000c01c8001050384501004105100f20791507140802c0110b621a0b540a078000d100042c1c07003141030384c4e90f1a02c42c1002000d03100108000d002d50240015403d84540c2c50301c0c4014180e58100c00d03610356400c48080002e4540c410100f00c503401100840802c101041c02007042c50307000741e4100075200f600101c43c0044401f242c0301da4076824240c0401010031072200740100034590100030f80000611b0503407 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 314321133 1250 314319883 314319913
    0xc0a05011805150d05011530140115020d140a020a0506010807030507050a0b0a031a0409061d0d02031204020a0b0409021b0d050d0f06050406030f060e030301060e01080405 75
    0x15880b42404440018410190749283d200b01401021300e00d00c42c8190040010380245241006514540205a031001100c1035414089150300c503e15417403010000100100300d41d00041000342f042d084103800c000c1c008809a40085204420494035584525a03030041400c4140e083e0004c4a440d400c504c9031858980028030100b100e00c0c060300c0080020400c00d4514940030303240001a800c81c0e4003520021004001003520304c000d84050111505000c1041a83da04146440918904861f58481c2c1482a0341044c000b0360750043c5040207440d650030300070460800c140b681d581c0c0c0c2c1c2403251005a0003000038144603e51240c030705410a10052580b030302d4a68449a4001e180c02680110340d40c2a40082c1000721b440306490346038030b0083d6010140080e440e0500c006001ca003d030002c00c00c00c00d80c4814609180110303d91110010b402c00030b00402201e9183c1c18005c550010501080350300c10310b4070303003a403d01001c00030a690484655544030806080d10380011100c40b81c004e08100c405105800f501d000943c = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 314322383 1250 314321133 314321149
    0x60e0102040e0928031e030b031b010e0307060905060a032405090711120d0b03030c070602070b0301031101140705010e06060a0506030426070506011202010305090c0a05011805 77
    0x403100c04001e00281d690401c052044c00c44513103003c942803c1000034100066040000030070090042c85564090320401e01066000e400071400141d03250080861380d070340800e0b070036100030f100b0902030760340c03001144c1840c060641c1e80506016110128103001410401860008028020756103549000326010381c00c01c1240c1c04200e0340038040c0b41201d00c1b2810601c22401d11410080c0e100c00d45142c0303c00350040e8190429110340484009070340b14840095048501c0015400c080880c1c280502265510481c0e62104c58503100280180710040c021400c0c0000c030b10844009807070503240c118030141d500d0b16104005441c003a1a13800c840e542c0e04000e0051001250080c401e02e0a083d81103030203019649800010012488a95080070740316500034000d000114514210328202441d54403140d050303200341304c98080c1884c02211001030440c41240700101d21030510002c0c810034640b003a01d043c0110f44885030300c0c2e80c8031001c50455680040c0310302d10810440d8820030702c0012002c84c0e400250199912a00410504c0c = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 314323633 1250 314322383 314322391
    0xf0c0f070c061d061c05100f0e09010b240703091d073b150a090e0a09030516020a15030203090c06091509040f020d0e0106140d060e0102040e 62
    0x3280f1038404100f02419445200d010040c01102d480d40703043c44008020f840c05c0695021840b0b01596040060410f0496420303440c007030400000c00c048502d0341c428820752440340c121214030700d550921906440f50305100b07041ca291007030390002d07003001101009144084c0f900619403c0d810800c0e24800000c0100c0d58111510f1000941642c1c06103c0ca400c90001d0030f0b000d01500041c82170811440c1f54004002d41800d085151a918a566001040d010b40014640f4903041d1070805100000914140c015412030000c4048401400c8140300315901c1c2160182241d851490140101d41f04000c103513400800034420310105480241500d00040e2074260383c1072452414108500420b80c0003052149880c020000013440140442d074081ca03003140074000c20b0440c548503075604601030740401d0100d072a983e0341c0c0000303030202010070045440d1104c0521007000780c1080c00410748254a802c1d4003081640899103c0310340860040c00118403000150f9414006003006241001555801d000204149450700090303401 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 314324883 1250 314323633 314323637
    0x71206150806101d041b05070c080a080a1b080a170f040507060804050c030a2001080f150f030f03031b03060d08070203010f050f0910050f0c0f070c06 66
    0x8039021180003400502019041a124512000a24800d103034400d840c04c4040c80034100d81100b9580440100b4003400c0c18028001a0742c008410501032035900201402c00caa0058800c04642c0b5900ca82994540c2071038440500000d0080010113001e50160710041c0f03080c000c4000040303e510480c0c403118100d400c180202c0000072002e90347c5648040c03090240e2508101d0715003440f0b00b1420301d555030a03925400361141100f07002445d0000b500b801002c0c481008803010203010f85a221110b0318051150012402003010113502c0802c900c840c9512401c0401e115000c3ca02c8104500e4031900c51114103c803080002c103910003484039003040d0b203840901000c000703810744800443d04c9061159100009000000744589070100c140704110007903582c024103520058101003007955582140c000b01e80034150400d20340700200c4c180001c1c00140da403a40c403110720401140050300d1209404060f907000f81d880a680c40d070000c1c201c403808550500b10200c001d00c43c850007220082e2170211180d8a078500c0700000d51007540 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 314326133 1250 314324883 314324909
    0x210f051002131a0d050402010203160f020108010626130c0b0c010b0d051c030f020304031d030a21020f151005090c0a0305100807083f03071206 63
    0x4400c0ea070418a000d88625050300b0116803000540e060f071802144209050320752610041b0b17040d64001d00c00c485584041e902c080708548640d08146c1030b1059645e0040340003a4101c0c0002032024425030301c00309027204071580c800d51600c00b01c0094140400140801012100042c0407400003600020700500800303141c0c440383d032101500c440385800c44903c8101140920310742106000061000b1a100110500100b07a01c18070380c2003044110014490061601c07030302840042480107154001401e038405107080c520450803003d18105054440c111300000814516410703614440e08a0049a00c00450081d44120380415081c40e0500380b50070031404a03200c002d01001e050040c1d285041090340d01501d0f054446100d01c0c20449804038180c0b1800b00352030201071ba038a01080b0f5140c130b500182002000090102c03010283ca0f030301250b4070396034584ca800d9840620300e03101c40e00420504c00044040c041503041e503204410230304a0440d82c0d501c000d0130302082003052050001c0d08181441403002030007198003082 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 314327383 1250 314326133 314326147
    0x1d1c021f0314010602060105090f0703060b041410050c03120916150e0402070b06040b0f030601090b0111062203030204050a0f0e0a060803041701060b030c09090709210f051002 77
    0x650001c4103030020005c64000381c006100c03903224002016000b405160380c0705419541c41400b1001007115811690700790400040c00604018000741c58400d0000481e2200003224003d40180c4041c8641c034049180c0e40c01c140902d000240068807000ea02800c04003ea4444040d20004006030706550380288040c04404200b1150700742d07010b01210a00f0380d00f07039421454640070f901c980308880300040c2180c0c41030392110305003105511f40245007150150701070101c90865842e4003040c8042e04a441006001801070002455501c2c00002c13464056220511140c2c40c882c0300800281c01e5940e8524103809158081000140d580c440782c928100034002c003806403105500300005007100754806801011641d0030031b40107100302c0750040100d4040380c1108824070070070384003501014058541c65001300640340300802003011030a00e000042c0010727681114015103983c0e400030203480e00c85d154000d007072a002c2686a034281403070300303414482d07000c90281c0c3c42c40c902800d075541c5082c5803c0300c4412655409802040071 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 314328633 1250 314327383 314327411
    0xa1514190e0f0106030216020405060d0501050a0516090f0b210106020303070f020a02030706080603010e0f0c0f03060106020a0f06140702010902031b01020309091008030301080c011d1c021f03 84
    0x180f8050441403030b00b0341c54640025510303818046501d901a100b40e0799100440c2c1d0310364444c8950740b40c940e403040084c441e5150424490b002001d045400c1c0304603a44001c5c80c1c07407840d4400c001c0354055840845010703040604151031842c454101400c1000d000450550751110341840410f40c40c000c0c0403075801185d03245800704d4010f2001044a01681c195400100a2001a5400f08514041d1021850010725583d600b900107405003401c0220304540d40159a0500c803a01000304900780d40c180156500f10120f049a0f083c1959601c09200b40c00042c0c0040c00034200007100030800d002c0c903900680e00800c1105e0082d4030f130201000140c81000151b9900d00e081c8046040c240300340414140314030400c601c0100018000b030f44a02c11181c050740306030000380000328010a10003000001d0086001203945942e12108407903641d400150a2a020990000500e01c1084d0000101201c10b000541208541000700c110106016040802283d00c40701aa000720384074054040c8282c000e40b500d41e000709051894102c4 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 314329883 1250 314328633 314328661
    0x50d0605042d030e030c060c16060827120307030f050117031213050d08191a0d0501060801050c072001020606010c030c1b0305060a1514190e 62
    0x852280c2d01c00007000080061032034244800c180c0c240c10480074040c0500d0010782010580300400d580b200002c136800d20001c0d000101804280101d07048264500d840b840280c440303080840b4042c28080f2109103004818487d103019078000c0480b1300445003000c10682c12850705401c01c6850703100180da110111301800340a80101c0b801020180700c0b8200c0b0fa01e00002464480c414020b2503442e03d28800041501080135180003c00240c201080d0340e48058034140041c070042d0306980d1056240704c1c41002d200543c41a224403400ba801484400c0803040782501480565032684000359580e540e110400950584280509403107101e013148110360b00d403500d00e042d124000501d80c84030002902082d644d42c5a98000401d16008482400d011030f18031401d10701203601066050001303104107030108100310352201c00314039502a24811404c1e14216a0703444801c5040710f01403e8242c03040241040d040100380d016200b0b4281e144009012800802490000710300030085d81e512240d008980744042164020b802c040f = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 314331133 1250 314329883 314329913
    0x11211060a1e0f08130f080c030901020609010b0901141f050910110303060d080c01021206041413120207050301051006030501080703032a1401050403020c0105070b0a0b0a050d060504 80
    0x2040390b02c040b0340f403e00604403000103001c00750200c41884144e09100d501000181d2580c0d002e400c4555840b03000c00e8050326034201010044c050b00c5103c0200c2c105110600604287ca80094500d60392681fa215680c0c40d40e08038120659000302e00c0340f980100c409402d002001c040c62031034884035a80d0340164180b04001e200c01206e50b040180301c00707910740b64403400b2045070f400c4241281ca2243d8504d10b07041240d031f41c0c801c0c8403d00409600c005049010120441c102510412046038100311388040110300c0ba804000441d03000417a001c5e02e0300d8580000e01050048401410039104444805407513102103800c6139410b4a258001110030b80c0708200ca15494065140500f1303084e409001c1c4140707190380152080d0b1007100c1000b1000001034592507840000040c256000340c0040c0c4610300714902c2c214207402000181c80a4005001e12094425154054003c41e0740c600d078003201b80001c9503100d20788140108964010780703901003440e041c001026610340c4684600386e80100000509424189440100662a41c1c = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 314332383 1250 314331133 314331137
    0xd090f140102070804300c030b10080307030f0207080106060e120f0304060c020d060c0c02030c010e0303120a0e030307050310060c020a0915090f020c0709050f011211060a1e 76
    0x1055200080301c030426941140d00c1605920302400702c1101d0541c3c101e101b540d8a9102c3c40848100c0410701c07005c048101c5c101c901a1401040549130513051419070865400303000907e500030009400002c2c42191550840509441500c5403e071311401d2450070341e000740e4818000250045d003a01070030f240071803610040040b5000107102c82620071301c9480d164001c500c103010500403c11840010754881010b0b050689612070010041c2040010026202404440307099000b0b11517015881d507554002d545044448100600843c240002e00103015100c0741d001340090500d503180c5005143c0320704100081d5000e103071140c0742c150b05d82c034110758200414034942d0320560405c400e8040400140c1c50320b00389001618040003001c40e04a8240080511100c4030f0f9000310a10391a007030201000c0e4a00794040c1403110802420b071058265144080c5040c0c80c03050340c04c030034481424401000107210b40d00d52544450700c43e50200c0090554040001c4450304901124408a041391490800ca803840c0140b1143c246418 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 314333633 1250 314332383 314332387
    0x1090c0311091f020319030501090b0d0203190501060b0c24060604060804030216080106090c0e18100308070c030303060803210a0b0a09090b07051c0b01050d090f140102 74
    0x109001036900e504442801d4400014480194810f610a0084540300703800000ca04401d880b0a400c01001031109200d00300f00d241c50200444d006150030703c81104200c0e0010004c0070702599180044180c1440400e08549540d69807100007010901d50f0044d100c8804400c01038003c40c203d2000aa594182c00074205500e01220780130051a039564070300381c42c1903800a00d80408103548520301603143c144004440c240c0c0c500e07100380000e40c40c0d1054026000b0748640c41024010a403031540c042d19400c0c41146040e901c4003022030603281c9050f403042c80aa0200600c040700356143d17600d031500716603503102c03083c00c2c3c841544000c41031080c1030300341c01010001c08101e001036107010540c4542401c00c9000c0c1c002aa1141e031100c000c60180b0090b60042c903060400100702c8009155110380243c006d0038040c1c4101c880192080c002141c1502810a80715944c000c0b000910030104103035a19030080c007514040e18103100b801d12204410049074452030380218400e00b0700221041140c108441c15100d15500c0850a03801 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 314334883 1250 314333633 314333647
    0x1031b060813020604080114090708030c03070f030c170304170405061c0b060d0608010b010c02150d180b0a1109010c020409020d0503220503010903080c1602060301090c0311 76
    0x300c00c440a90048024001e4110842c8920014884d8825548182c03a40c1d800c0080c1004503202c8000024000d164140072101c01e1a655000a91030380240780c6d1400194005100070300110300102c0e18034030b04610074a004041400541c1c2c4070901710f20740c410000450a008001c0008000340400102d81c1206090f010501f0180391900003801d038440c1110090f0a1450380583d0703081c059040e0409012010000c040c149c403035504041c15002046907100741506907023005900d0b2000d50040c00704a0460b0340241200c03190f4007210355001c6072a4844030321042100c0d91100716a40020040403c241070520422240700d9500b4a4110320041d0f0b4040341004641318001c1201d412280e03040807030b040d04581d05a4011981012600001315001c054140240c003e001c0002d00100c040d104081d00c1040c0141807078068081503c40301810308959003a4001000b103009600416500455203000c0e10a1641128440d0b040900c00c0d030115419410a901c100901e54a13161040d003255098010299940c00381c524540c03c00700d0f = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 314336133 1250 314334883 314334887
    0x301030b04020607020310050106120f061a2b06060206340207091505120c01020307060b0316080f0106140d1707080a0903020907030c0207090c12050406020301031b06 73
    0x4007400081c0300300c07000240750085403414001c40e1040480040c00b00255030f0744a074098080700b200b604508910b03140c0394080c85000c9462040704d084c3e071a94807206001c1c1503805840c4c0c04640c403101e4021010300d600c000300000030b618003414128000781c01c180402d001d40b034604080c0c6003102c0548405c02c01603001041e00ea0b0649592640041501079160314000041c090906074280701140d009041880e05140703001200c8107062240b1812a401528a0100e07900200b07100380e100e1007403800150068008204000103c1c019030480d4144c25030003010ba403951021849880c215000e50381c461032581d04005845081822300b031103144001c204995050004181500019404088101004002401302101621070b003211900355046c65522001240d40d602c880c11019100c9c07040d030f100c200e2291401d1000100072038401d0007456440c4803260014030f41d20781408001809804c94400c01c0c8100301c80001c02c0640c2500a00455018501175400180d036541141131040305545002c0c0c0300700c804090b03443c00300310b41a = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 314337383 1250 314336133 314336153
    0xc051201030809120d1e0c0503041211010c12031d0313080f0f1906090b10050301061a03070c1e03030b0a081c050d0b090a0f050f0603120c100c05071106030103 70
    0x25141000d000d20860186c94140d840c0d042607000504079110225010440c490507410701d0041a0184000b410298a0034004441591410200401c140d00720100845414084d4101c0300744031000039029090a004802d141d80303140c02102110100c80541c4104008981040c40101c101c0d00810018140003141001c0e02c0b40d5894500611942c000392400455040c03003141c0d4400c80610b9441030800e07100d824501c82c140701c4030265000b014405c2d42303031030380002d01c810340c089087c1c00e88078540c180d0300d04541ea100c00c280da0600c0c040c84241e40d15034000c80c045140c00c03000101c44500d14460b03200007400102d0340342405100e41094001601d65401700200d0880341c0b5084100102d121035a1422a541d520040070380b802a04203260456001552a014000da440040d0011203c031083c40b03104110940e200352501e1007010082d903035203415401860101c41048100340040040c0d115240859030541000e0307241c9022101348000c0d040c001640403e40d40100721030802143c1b485001103880038115411500d0f404145 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 314338633 1250 314337383 314337407
    0x150601081509041403161e0201091404060305060a02040905011403120c070f0b0d0f09020a05040b061309200309120c0a0c08070f0e010e06040c051201030809120d 71
    0x2900c400b0000904000c0c0c131281400e181074074482625110244044500c44520b5505000c5078000700d01c003038000c070381c0c1e00d00d00c41c070951543c05a6440c220b05140c500d00c5040010880b4006800545031758000c40450402c101d507034081d10b071a600040c0d64070714040003030307048500603044560156900062081c495070002240180a07a10b4a0340b181e6580261140034a002c002c1d6000e15000d48001d803000070881d00010140500c0c8414100612030380d00c9011041044400400c0f00030344c00300c101c07141400641020303480391101d0200500700328640510408135080f07619040c0c0c0032000690f00c2c0c100603881502e0f0007030359407a08841141690b04608000800c2030316003812005500100c0c2002c078402042c01010804241119041b08100c04501e894071a10354680ca5139001c0c516000c02c0c0c1110008059140000c550304880c942e000308070590301c3d12820040540101895601002028003000e0014610742c11410f000b5846441171135038942945080c4103402c04045020244ca8111441286016422503003510403 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 314339883 1250 314338633 314338639
    0x9010503100c021f200901090303110102070602070506090705090f0a11040320030705060a0903021e1c060c0306031211030d0612051606020d0e061204051506010815 72
    0x100b2420366000303e2601031002c0c0c001c0186000750f00c05503961140743d484100703d4044074000c003a426480300a900103900c6100c454500050104a04102003481966407500c0c403050340c0c0000d80781c040d050f02c4e0380d03050343c0141c1d0081e203482c0c01010900610343c10412401004101c152400156071520400808041d1002050304150303944501d1701d40c0c000c0c0640d400b120007031580101511504a100e0000c10055802d07c5071950083c0324640f00416030345003107015075281c200c0c542c0c0c402c213110303040d43c1c00c2c880540803082500b00b05c865580c074400c0d5980d03114112460300c1c1400300150210103d050500c0001e60310b0044005041c1444d115007800841c001141c1d104030b03601c081c204880086d40007a0300340e2452003101542c00b40c2c3c0d03107000400b01d50080c0742402d8081050180c000c850101e010b601c441c1c1c001c00b000d4821200507034400915800c285001d040d2a001e4600000d000c4e03810a218051b0036244040102d900304c8007500000c2c1034451240c2c8001d00940c01c181c0070300e04103003a443c084440200d6240607180b2188 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 314341133 1250 314339883 314339891
    0x815040605070c06050c070b0601211107061d010507050301300206130e0f010b040509150d120818030d0f0e0708150903030c0a0c051606080a0b0901050310 68
    0x1d2540200f2107000c016a0008042007545082e9400301410780140504442c1a0580e801040d1650311031041180010701e200855110054040188001041c0c880401180100188401e6021949074824600a04001c00300101c8001800ca0b105084480c0100203c00740041070006002160307481c42008000142c01190740707211601d03a01603001001c00c5441c000c0d40084005040d901900103014484200e0349407550305906030b102d510f5000d170600c40c24050501841030901003001245450007006402a4001b0b400c1d5041400c628040f411442e6698401d8440044072030b0541c10701c5610481d10f607030140180301c84488510203420240c1d103901c01c071010307458042e80758200d507840f40301c0c0c641c0001507850b160380444200d42c2d5a58481508d07650008000e05088101d80d000890749500030048901c01c204030242145800c040e400207860200c07000c00c0c10741e02071103601d10246103101c00c010007070041c0070300f601c0d0364145150900c1042d064034a00880d071800780c0503d00041007217880000303003041800d9000402007 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 314342383 1250 314341133 314341141
    0x50a0e0402090d14010c0207121115040801050109051603090b0103080d1e140c120708131401090c0503070311040506040905030a08150d0201050901080406020c030c030c06010815040605 81
    0x64854480e003d000340c000100c468205090340015440000c1c0d03c14035400f0b4580c901c0d5180c042d8100070036010b001801c0b040b102204144a440c0290150304004544841340d414039032103018007401c55000f40c110201d0255648180f000c44548000d42402030001444c0600c4903510a5552a0f03e8100612000707080c524007080c039440040003071300000b001007000b15016004400308d200d40c001030505a44005006034806c0d0209042e4507010088804e800349207410b090484d200c400d801c50710000020280055000c1140900000035000300b12503c41c0d403400b40002c1141e00c12030030200a0110b940d801280b289e80400000c1000a00c1600d1050500700b08443c006180c0d910000454060140b9041c000c050b4000024103200b41c0e074004c0d09250145640e049800c0282c0c09100500401c0d8020080190105e40103100c0c84e01c540d882115180d61240c450303030015062466102860307245030008402c2c0d41c8030790004200495a10380806c0981c0c01491000001e000c0c004104800c0f425402e800741c00900080e84940000d = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 314343633 1250 314342383 314342389
    0xa051509030a0f120c0509040b060f0f030c28140301140405040204090f0c03030905040618180203010c121104140607080910030b0f0301050f19060e01030308090d050a0e040209 77
    0x44c0040d205800c06001ea2100603200914590055100c64070a610b81543c0800a045c0501514454001d41d902c0500c4c0883c00d51600041d5000280f800078000d41c02c1050801400840060301d2945d803020030303405041f01c00c141024011850b82f000345031840700305000400c414142030302030102d01c49081e05e001070180c07554008a8050320155901800c564070607005034081101c60306804048900a07074421641e90707210820041600c400e8801d014000141c003008000000480c0d2000b00c0c056038003490384140f40707038a0b404203094848214180021845207144030980740104c2c0074051142c0d51103440c1a00e800d060613504044013020580300d901849000c26154208074010080f1029084010603402050000c1c02c0014060010350500e41c0c043d6448411068150905001d003c0c0103e000909083c0c0c00c2e9a04040d002002740399685080e01c0c1c644500c00000c00c0074192903118041c4d802a951101940b900c41c05403480c10115111500411604114010402d0b9000d2590218001c0c212070142e5522558400 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 314344883 1250 314343633 314343647
    0x403120c05040510020303090706030204080a0215070215091915110f06010f1a07050d0809070902070602030709120c030303020f09040e0a021009180207020315090a051509030a0f 78
    0x402d40041003944c94605160b00003010307602ca0b050b124200d480706511188210300b40d024904c0f070507866510a600c8000145001c140c04d91007420400a400e04140302500083c0307000d102e9040c0c1c5540d0000000b030301856414a00c1c10383c080814130781d200c0b4420038a4282d084031580407415012003003148038814021541001e010046104220100301c84055846402a0741556080e00c02d100901e104a80301c180411510001c0c0c842032030300100907000300021410107031414500106401c106010b034100106c0e01c1940781c07015000c200d0041c0c01c0181c0780d01c1c1c62580031303202c0e00c4281c2140141c1d1450307440d030307000013a02d4090381d105036541031902580362006038604034a40d0240c10742042d481030803d40452404100000e20040726402241d1607403500700c03000c5068908202c10301071501d0030500101c9141c224103460b001043c0b03c40c40517088807a400220389801e1100300f01651200c2a58015071020030520000b084400d0180040740350fa00c401c1c0c1002064140d0741e1103680c1c50902400f4201d500300080e24020341d2 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 314346133 1250 314344883 314344889
    0xe03030f0c011401031a010f15030b06040f030602030105090603160306020c0307020d1a0a020c070314030d14010f0902120708070e03120d06090203040c0b030c130902210403120c0504 80
    0x818200f580d6164030304110181001d81241c46245070342c80000179500050b02a8070300300c4003a00000c49100f07015407411406010301407115604076008100006491240510040080d400703002c1c016240d504100421006400280100d403283e4400c00f0706a03a848445609501160fa00002c01a5035001030070025085009029000e03500c130580d40407043c18007541c404034101000e0f9524003900c5a0b0b9070140c19508078003817082a615140d00c600002d0000038424201984221844801c982c1090801c810031003d4a50341c0d0962100c1c010480010494000b0f0800d4030350103000d40c07030410b5060a601c070548504142000700040b042066000c00b044110740190603030601c1e10700242c140c07803682043d10021340440d03104144850400c0d28040000030b90310f5840c401d0324000c0b90b10120748401c952602d0166500c80c0c1018050020040c01081140354900c808503c4800030843d004000d07032100b4402040c1182190074042d05501110900e041000180d031018015817241c3c4082000100303183d80351012140c1e405103070 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 314347383 1250 314346133 314346161
    0x2a0503070308010806070c030801150c0602040902190507050a170c060703020a0e180601140d02030703060e24040c05090d0b011e080d080c071505160e03030f0c01 71
    0x58004241070344410b019042c0e9008500f00e4180382c0380c000045032060113034600070700043c100c1e000611a1b810701240c0060030140714a42842003611546a01c012680168050301c2e8055000071444c80540c02003d071102403c0701da05041303081520a8440f9078070b40d010000010302d032141d0180030030000c0302d41c08190352064400e942207544624103d000603009601a120350808240310640c40300e0f291070805030002c0010a400740380f6005031100b00042d96203904882480c10110b1050007203c9282203184051403140401d81d40c04100b907494000245004071003d082c11200040d051911100704802034000c40110a0940d00040c05901540b07085510740100650380d60311810450059060010000b8054103a40c40c007810f00c840502100a40e141e80c1d80b003031040703648641007203d042d1101f0307000c0c5925640c0040200c2c0d1807842c055071541e480d5031000410038040b40c655070390801d000030700c200c00c2c0070b0f200594540e05000c611741013100c00203552406032800340405000001000a130b085029084003c00e041d0317a0b = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 314348633 1250 314347383 314347387
    0x30405190c09022704110d020a031404030c03030c03110a0e120703061a06040302090705090301230a0e06010803070213060e0408030708060f1806120607050901020105090106062a0503 80
    0x2600c040c0010300003404130207a40d0341c10a40c001d5403901e807144844040240c00000d16041c00302200c800690044a45c0700180343d43c0e19044580c0c1d1a0818190307115034883c1c1d54000040f2507034500036088070081d40b1140c04162030400101440c1181104a13030b290352140c10a8220850540009188001a81d503144032a010303d5038000204845a004582e42404407100000078103660000d11104c1d005074403005e98007800000105064500500040021050180002c541c0c05414203540004a18085030680301d58404010005450344510491076142079250141c02c442d450004026aa40241c480c043e02c12041d51610806d10740d9654019001455611403620b43c51405081010842e041202c044011a2410001840519180d0075007400c0000040200700807400786000003162580090075290015050707a107800e04864104130583c4102d50a940f91076540d6a440c000a007174540180803d0b10301d84c1400001e100803a0000c0a603085103a02d04e064070b80012580c5c2c1c0449041300c030000c01130001d000c0 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 314349883 1250 314348633 314348647
    0xf0a0810020a1e02120f0d110c0c03070b09010f17070509010f02011107060c02010e060405010b0307051c080f041d0f012120040608160b030405190c0902 67
    0x8281c000c2e0000c50001c2d1282d21086004844055061100c0456500141c00884008216005460140807000c51701200c0d42d00b061046034000049a181c40303007400311040c0106100304142c00c10810b9151029003500a810b05074034001d072100d1507000b007413000fa040c000041514076030b0600c01c07260102e5980c2e115401c2c0c02682060a40602543c0c009420f6030f000030108c845c80d03450350340140a16080348000d503200703e02d0550030351500d000038400c8560410855485030141412801d0030810715018500030400029262244420103180030096880507006104102d1005030707902d1044440c01a075500700510750f640b502d19654090052040381c0203d405d00c101c0800d241ca020038201840c500c160040c0c0310300c0c40c5030390300c074090b0810420320510420040d00c20090702000250032030303068000d007240703030400011032841ea400080c007912070540012003540d03c42d414901038005598080310003040c200c03002d60300c3c0d41002d440f003d0b202c2c246d807000b000c003050f12860000c04003c0001c4408004003180c0c64115100c40c0 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 314351133 1250 314349883 314349913
    0x9020d0e0a0f0c0b030f1506121005030601090b0102030711010216090608060c030c0d0c140c0a0b13033e012018040b1207030807050105090d0903020f0a08 68
    0x6030184042c0d48050035502c0c00710b04c08034075004680c001c0c150750160a80c1e542d640007000e9106104582c1e480d400150520500020005529042d4091044604184019030500040c9460610164040c0301072505104c000003859801108981ea00354111550407414190880140e2402074540309082085095110000d145040342e0b200406031010300c020b84280d41c80300c0686461030702042e11401400e034000c1050340b0149031150f1050200107020b0070103034043d014244045180b904500d9100c6895000344110b9410000d900300540d5200360341903062040d003295611700600b420004460401c4894001404064210200f182e00c428140301c02030800520541c040200e02a1440b40d06003800312184243c07101d902030922080e1064494519400d00040d000c001c20000071301070034101c16411008440e9482d420700d030184101006507024072015540d031456032030181d0071103000400000058108a104070581c2e50710000c00000c0f02d80441c0c5a0040b080d14100182c0461101d07485803402d0b01c5405c01c25840b03a4 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 314352383 1250 314351133 314351153
    0xf03032401080f0a050406060b040b0408010e070303170403030e0a0309080d080708071206170102031e01050901031401020d291905040507050c01090302150105040207050709020d0e0a 80
    0x54103840346510459684015075220900f070301e601140407003070300018291964641c8a554800d00842c40416840d548014a60155015401070031407103030000b40034402075101b4001d04030714407010001001c3c50f0f480d5440050403030b9042c59181d103090b409040806c2c1450300c640c00c03207402a0f50200644110034000d10700504081c0c178500c101400d0b4001c19801d2840e8500451105100300100d445500042d6034040044881940122143d84019550070011484039074185018151040340c0000682d03034104095030035499211940041000000000107010540305d400000e811a507100d050612141e80b0900c6260184c040d01c015040f245180c4585c001c0520380d010b400000e0104100309103c50a44030105000c80c5281202140c4440301d01510100300a0810360301280d406015407501c5402e280d490b01c0e200d425141206000c2d0300580c803011444031a4011490380d2801444100c8085181007034a030754103038540700c2a00c600e40041c2c1e80403442e040202c101e600b1100f40b580101054402804542c5001000c2c6 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 314353633 1250 314352383 314352421
    0x403060c03140c0a020a0624030804060e030604120311040e250201090b04022e0201050105010e0a080a030c02040204051003270c0e0c0d050c27060702120f0303 70
    0x15081000110319a02282404c4034125042d40e405081c244101c2d0b02d890001e441d20000c03c0d481440c8200e40f0f2041c1c2088501100040c500c0394104650301c078601751005001d8140e640c040c1d4404e0b0003810078000042c18420722100c860040d8180810a12a4200c018807140160f912180210301400c040080b4218008411030000000d1000107401c1840800d01703d08031840254020003c001000108000d480d01d0680c050070289003100e180019010038212294032140504d848004d0307910b0700014409503812108100126105450489819160900f400ea903a035120b840a020b10001904140c20340d00c5a030112000b9007005404010318451008000300202041910045001031f1009030071070803842e03a81c01902c050741001700d50f0901e42c1010350444009001034440302c42440100404101502d071402514851130768211043d0311a076400000315801402000f54020003207041a22941a40e039100076034285503010f0f02d08a4052030b01c5440503250022814903882a480003000b080464610f0841072403070 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 314354883 1250 314353633 314353661
    0x8071b06020c06330a08030f040e070e0607030f1e09080712050a0b13051c020c030109080a0c0206120a0903090807050a0302010c1a0108061b0f040b0f0403060c03 71
    0x105603180043d0904400c0e802c00313103a10813400081c1e1a0f40c0401c0900b060030344120000c02041e0a0341e40c0782d910714134560108608485044002c2410403024003600c10096000c0d0007818041c0d41000b0307610006007a80f081040043c0dc0c80a03010300348550911404281c2c401a61411402d030038101b80800c00b030301030a1755124104940c0b16900300841c0d07500d1040030703224266078818014030441d0a268dc8031404042c0c024100030700d032126240c01c9004200f0030482440c0780b905204400300100c124a100a05042e0030f00c40450098ac1000d80210014204004940c1050410714000691118901c001040e51095a9110740da41401c4001d08c000e140c2c0c2035105d060018401c5d140c01c4031075542c0701c02c0a40c8030926442040e0307000ca01d800301000954050040305406921815608110200c00c070030070f25502c542070308120718541c424001c100c000040306600c900881c011114650400980c90100740c603500c11805806042c04001c2000a10350b110074082d81e01455100134140420840f1a070000c006181e8200e0b0401 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 314356133 1250 314354883 314354893
    0x207050c0a0e090d020f030708070218010b190e0102060a0c090306050f01091506080106031d030310031202070305060c0c01021c021e0304050a0f0219170c09010503070608071b06020c 80
    0x600d0b000003405041d06d000c07a4040c0d0704052980d15128000d4106900c140d800c95018858901421421501d643c080c2c052151a151124030140341d80080044101c0301c00c05020b503120550300a0b07a000500d00c0e50006500d4404501206810011103110186600080c030003401c2a040c00798075880b1409c8507050b41c0824500700b011000301c0403141d480c105148510b00100703105000511043e4400c0e00400a03410040a400e07030070a4480c01902d195500403550025800c858010a000300260601019902499840200001415030300c070540c65000150961011110000700078106000c2034066a80501c900c0c450030204140c4c0c2040400a58444085180400503913448241c00b583d80c401a64003e50308200213011a5800e950b4074101c0e40d4203e0f1007a42d002a020240c1640c407800070140c1c4028051891030222000c800c942d0b407628000504401078402c403000401400680c40002d5003000704d580074076064003035448600342a00c442c010304104940403c60780200b80d060081c01e40080002c1c482d1081254 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 314357383 1250 314356133 314356153
    0xd0b0705190c06050610050307051305101206270e0c210c010801060e0904060603080a020a140a1a101a03090610080304060e03030f030a05011d01030f02040207050c0a0e09 75
    0x10406c10001c0c0c513200814070910208040c54480d5010b007040d01d0503c8810040f0503105c000140380e80003034030341080025400c41c81422407c03401e4000c080082c2400052015181c145030385540041e60580c42c9034013a1b558940d86480201001c1002186a07100940a49030f80003904080c0b0031440541450a800c6110b281e9141c4015403003546103034120b4030300e541d80007106ea50b60000c00030100c01c0034105480481c5c40700340104c00f10306070000130b0401001c1e03a00100b80c0651a8074100d0514502607810140390b030401070000e800304072400d405003100700c3c214107100d4040c0d0320302c04031030000e039130030340008070351103060101041c00240c013100440c003c500d4041150200d03515003004852900b824041c0c0b28168000b0303c420070070f00b0f00a561035a08071900406036030624800800c001203540045410401c0c1544500c0100902c8078a42d0760004c090641005480351581562190140c0842c08034009000d03d03400038940046c030200344001040890010a0384da0f00c82c0d6100070081805005848462441c002e4000003 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 314358633 1250 314357383 314357389
    0x103050615130504031e05030601031a0a090506150c0102041703190809012304021f091e0509040f051605010210050a021603050d05010e01050d0b0705190c060506 71
    0x2001d4840320040400c0c00b810044001c8401070f10010f401141802000d480c1c08003006951117400e000341d0401e40e6040d483c2c0c0f900320001825100c1c2c0c10003821000e040c000c0c000d042d0b83c695070908010b40307200400111f0b003030300c9100228a0304425500c41160140001c03031011a540c4040d00107004407900c040002d40270300d0020a00710b07124481c0d04041a40c0b1040710800313003003880c0241e0034142c1c0032032500c000003510002908a10041d44100300210040e24250303003000214580f1040f141402c461401040196002501014081c0c4800340521000c09024890b98041030b84505040d0300a4100544140b01c1401c0c5450004483d01c80c03c00102c400d8000c4542620100030078007003035012110142c0c0241014400307000300350002e240107413902029039000c2001598400540f0444074810344030380d0b2907135560080751044a00301e0300f06821107403031a403480380104082d40d29645030000d40c0350000d1513500f83e0b484041d41510140b0600010200c041030001c01c44400d240c100c1610700c1540d0064000b4407640e0351b90f1f020 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 314359883 1250 314358633 314358661
    0x90b09090a02040902130c081012031b020301090f0b0402010e090705161b03030801150f080105041d011a091b12070e0616031803030f05070602090405010e01030506 72
    0x4000c1241e100312036481c0540360a8009803141400584075134810190f17030061105031303210307864020003050280090240c0c0340d588503401002806000210003440761140e400415805c8100102d007420b80b00a480b81041d5036085d0712582485a200204110040062034148840038040750280e0101c0d2010201e203c2d1820020007691098402d940c07618500703111180041c000c80801c40c800d0303c001c4640f402d0007508490128900001c1d60281e2590700d0305600d00015035490b66442c0300f00303030b0410008801700001e60750440000c0c0d0560303030f08480210f00103015079036094001a020050500c135600301201da801002d21400b03480d00d44a002c1d9640d036080c1ea030f20684012901c6035401c000900c81810404101a0b6404040070360300300085203041d6003540e841c280000e40315004031141c0c0441c06034050b0101c0416410018541400c1500c2902c200400c6c9140c402400c40800702c82e40400344800024004104003195040b10340e0900000c00400955031151150f41c0301ca0313800d00089502e0711550010900c3c9600d6140 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 314361133 1250 314359883 314359891
    0xc2406060e01110c01050a050d1a12010c080c0a05130b0405030c0102030c0627120d0b01030b030c040e0c12070501030c020712320a0b0106090f0e070905060a02030301090b09 76
    0x410000c01c61354011501984031f102d10000708007040c050400003410602800f86281108e81100726082d0001d010014090800842d91400360b2414102c8090982c0140c28030303600103c4012110707119800c000d816995849011031042011101500c04641e1810710b401804c1914410360449441c0000b020040e40d80348620139000004e0741c0802c0002c1d01500346103240b401c08803e480e000d10003a00c0c241821600d80b101c0c2e0303150015008004030b540603024516210703607100e8001c05d19050040c0c040d400040b983381c0c103d011015004581b00c1e80340341ca42c0a002c002441408401614400c420a400b0280540f1902a40a014006410000c0f60f108203031001461038207543d0143c440d4400e400c06c03651035095070310294181c00950070a4a1941c10340000d440b081e04907256090020f0f0242e900c0618015400c0b00050300243c040c042003480510024014107003900544401c8130503103180e51150fa6080e242c6c070038561f0001c2d5020400140c2011500d90100241d4100c81d080041070000d807002d04108680114101c0b = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 314362383 1250 314361133 314361167
    0x14070212030c0904020f0f0a03051b0a1812050604050105010605040b0301090e010b04020f07021005030108030f1b0d021b151215090a09030e03120403030c2406060e01 73
    0x44045280d00503408003d1024110003440140783c0103042007100f41a0300700b042c6800d40400c002c180c130446d2a1300750081d20750080c10340c2c06d81c1c0000b0512120f0241030307000e103003c01000c102480e04031a089101072002c090103824a01c42e0a6140c15584c40c060341e45000440d001c951550901d800011030074043d00c10b44040c2d500c481030190450782003150600091102e8000c801a0307648803084600e044d11544010400c088400300b06c545c0e05c90490040c0020003800001320030400408000410944a0110540301009690710780255600c2c00071803150710300007210000d502c007400b40c05004e400d031540000304280e0a0b0b60351001048c0d4070150302c00300400b4400683e0300c1c420040003040300b1000c00d034260980690000001603241c0304410b40350040b880c1038804a40000006642c0d4141c001803541181441c10b086200324018101268038482e0401240905c0c0320040034020140c003070808010310a001100b1030100d4440c00701d611000803c0520180600e0722500c00490010131043d0040d520850400307401c48424 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 314363633 1250 314362383 314362387
    0x601030f0e0d17060108040f03050f0307052d09060c03130e07120c020c06070317041b050303090a0306180f0b060a1e0b0a0207050a0e0402090c07122f0114070212 71
    0x25482311515210f000604404001041004040034950140998011031040c0c3e200b41d100d000a0000f0041c1c409800120385c8103c04131b035040c40b145200358007100c000ca0800d035000c5841d002c00c000322924500501c000e442c0000b104000100b507146000b403c1d079210b00d0442d80c2c1d0112400308420204c00b140c07003854501c030041e04005d00c1230b092420900b000b404064071a2a1004030605020b5501c8801030060780c040b240c1c00c003a02d0700302204803203da64480250000710051485c04c0041d00000e03519044034440100460b4440700c07141000c18154491410550704140c0101002c6401d103080724030820304071652031080d242034601065090380d59040440ea100d15140200c0842e08106116500d03810402c0320707800310301c04c4e200042580e442e5101d08000602898192000c5c80c203152040003248640285070745050041480704c40302140c002d22003d41910071030700705442440010800c0707101b004900e90000d180c42c82450303400508030740c05500201c441c3c001441089659103c0010403612135100b251030341e00003034003 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 314364883 1250 314363633 314363641
    0x804090c030b0a152d0f110f1b0105090a030602070605010b1c0b040e0706020105180609071401091a070b070824060706050f0912040f030305030601030f0e0d17060108 73
    0x140c120590080c06240e0b504801c850034a80c5c500300305c3e8003075a0200014203406000242d41d0740004245e8203602c12030010b03060203040d08000541e01c40745805d80c81c80d100145440704000f0b03402481211124070703025150f028890303224142480a913000b80070898a1a261900001e141c52600043d107964100520710082d2129020340030001a0054002e0194030079620420310680c030104021b007000500c0c0c15000403d42d480c1c0b000703500001071345940309011690007010411801801c00702c0c0440075140c030352200c0040701d041140101c035148031030b80105441d508100b640d495601d100034054020300e4031032104400c296960490441300e20800b0303159045806801e00d405500f41d8010f510102516030301034411030428030343c6e456a100b520010785490010b040c0b881c0c00d01c0499001840030034071086031000d04524203840c0c01d000d01c1b0120900d00c800741c05c0000110114110381c0c03003904218249210500140240309800d1007040d260321481c1c040f5000b16444410008d0010141e456017842110305071110303005591 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 314366133 1250 314364883 314364887
    0x6121101091404050a0f0e010b011106010302061615060603021c0b0f120f1b01020d05040b03070813020a0306020a0f11060c1b0f010603020a050415051203070804090c030b0a15 77
    0x10000e02560900b648070b1b8414840c050146c86581e0007141040001304d0340340c18080c00074059600d4248203410301d801a000520160b00c5010031600100c091650804030010710307041c00600c00305441728401c1e03501c1c10010b001480c81c1e41a00900301284401040088000240d03e500c012201104030080e0403107518804a980d510300105080340450324003003a61060150408981e0500000f02e0455450051441000d0b0703081d641000340702e12208090170190b00e02800c00803030060f107010080280003081480400526a0040346031811080f5a010703000e076900948900e4608041c2d008501420001015070403200e690749c6c0310345000b034101c0c110a0003400c01c1b80c035201d218948a600001c1e1068400b14001441c003c075504c2048890500380ca4500005139007415481008200d040e03d5000c1da10a40c240050300400c0e0300144049012901e003220604c185201d98886281580503881d0060111800440c0000f80c1129a4100c81c0000c146641d0401840b00d60104229059009e40140c0e4881428001c060641d24 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 314367383 1250 314366133 314366141
    0x9050a080c090406270b0f01230405072f1b0612060303072003010f02072f0d03050c210d0b0d060504050109060c020309030d080c070606121101091404 66
    0x42512500b07145c06060040111000804113403c565000100c0304010340070600c83c90b118050011100407032542c2e10940351001c1c88039151500507100e26600c00118000c180201d646446e1100203510146101041046203440f100490002d44503d02a03010b040300580d00304901404e58250042049051840600d441c03e138040300101140e805100400c0b45001040300e50115401200d190807601041c00100c0081c142981c143e0310040685500600040c000141524004c010603909a0034103000c85195240e28070040070108201c0d0740251076010072609042e40030008003000c00d002411074800d8016014003081c10005000382c44040ea10502c40e28044582030b42112440d110010200512841280c0b1010200c3c1c13010b503000c9900380c1d5681011404c0040714010b038529044e03c0c3c00510f040180c1f0b000402d84540c1d6001102007000180030000c2c1201400c0b00940b646d0f00e804c02010000b240e00d542512103851494a070a0390816554a00c00c003181d8400d40c1c2c50303001d07190080400c0c48680c88030300c2804050 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 314368633 1250 314367383 314367401
    0x2815030b04080903010203010b0706060906261e10050c03070206160309020303130303031401030809010c080d020c0109020a0b130501050304050c12010501060314060a05060304051c09050a080c090406 87
    0x1640c01c202201013a074003400a180038080d1040c00b1652401141382070806c484036079002c0402a81851010404842d0382400c0c1d00003119141c0304c09009003241007038541002100d0704410042000e54060040c08100000e9000c101265014100f140d92218403201001c0c1c00211265401a0b002e5000a07281e00444170011005840c03904000c1400744003513000038119004900c0000381c80f03804080c200141035040c01480e1082c00761041c2e035041541103840f000154400c80b80d009062008803010341c42000802c20403513800070146e00045440302e280e510000d010340900e40050344910380118004c00c0c003203900001c481080301380800c2da0031b1452904005407400d07000100240c59030701808215602d16242d100c40c8000380300d1003400004803581400c0005d411070b00c030310f01a030041004003c1045450344616110350b003030313410843e441c3d9181c1d61603240c0645405031004001b441c0004042007203084a4000c4010412f941d400c8030785441c40d0f1b4407031004950f41c1c1610132410b45d026155901280109242da4000601 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 314369883 1250 314368633 314368643
    0x6060703020f0f0303070905040b010210020c120403051506030303070c23010e01060905130b040209040f080a0302091c021e03070906060518040c120b030a0b2815030b04 74
    0x64901412401d00b010070b4005900303c9a00000200b240c280d83c05222000a400c003185d0804c040042c20000075601c8014a080014090340081c403100c0000c07040100d2001a1f0741403e02c10b958540340d1900544603407145001c0440c0c0d10807400424002c0c6404000c2e01e102d001d0035510480105200d4030394000f60000841d1220080c01c80e400b180104140a00507800340718084000440c00d00c1c9014802000c455001344080da10700f4071440d0030000101181c00c41038005070100c550b070700746da15030b81405460003120900003000c4000000b00502d510b41c1640203048002011156084100205100da4000f184000002540611502c00703084030003081c07503882d244042c000303070440d1881510b601078001242d0081c1c016102040740440c22018001300717000c12900e48041a81c0074001861140d00c00703040c0c11040390b101c10368070b81c8500c0c4905007034404108524040e0b401c409100020304100484800382103818802088850801c001ca20b0b51a500d809031a03110a80e1440700085a8a1502ea201c03c640010f0400c81d4 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 314371133 1250 314369883 314369893
    0x7020604031e050c0604060504030803090f0d08010311090112060c030b060309210a05030c0d0f020d020a080906060a1701060302031c02060123041d1f060e010e0606070302 75
    0x404a04000940050303410303800050b60030500300781005450040c3e8800c03035510500c4100b00c1480b0203507110090340c040b250b01041c0103071282c80d050681401e00d110700c1b41e000702c1c81c072507180c10f0504135074880c400904032400340008541c1a5012802d111703c4080c01d0045185c1c1d001030341c03210f00000d651588070b40c000182d24900080c10070502c3d000903000c4e03841941c4070304442c0e03c11200110300c030001000b40400c1c0a80b072003100380341c5211500f0141c254000203200096040c0080b0f00040ca1030724503002001000c83c801011951a802a40000029041780300600c002031500c0d0700103041c02100040c401e0040c000282910309840c941510050522a03403042008955243c05000006860070080361461540e0003c092200b40508000240f41c044143d20044144507400d554101808030060b40001040b41900d010542d000240303060003048855000b502070324441d0720504221424084a80c00d010b40d0344038818000c955448264500c052828018104040c40d6035002c03d1292a02c0802400030510a005079a = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 314372383 1250 314371133 314371139
    0x150309010b120607110102070b011208120103080301090b030a020a030204110c06010b0705120a0e10031112010501090504020f0d0203220f050709050103210915030f1a090a0207020604 80
    0x22480940502e84440d107501c00000d004007035030819000060b20708070307038021410001262612600c04006200341c7c1500010191010140404901110306101c0c5180c2d41c030300156964603004038103038424410100310324684412940285808944482c120760024240c0b00c3c03a40c210340800c001410201200911010700b005594180441400303418000c09450301d41c40e0300c0d0201803c0c858101142d4a48440d0254801c0001124035600504880030030300003515400c10111305140158000e24401387d076900040e00118036200481c9103406c1160503140c0c02e0340c0f03180360707a030741c6405000583c0154a004400c03820207002c0d552685c02d11f03038091503101400c43c0158030700494825803a6400081c40806a4105503210715040604c14100841c20007040c00380010800e03589542c454840007008500b400c60ba042d041007141007614841c0e840b14001d07103419a901d2104d08181100a4020941041d01d030004034104020180f044034080b2051000c60005030601c0a16512040b0b40d10095004410490380f00805101c04 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 314373633 1250 314372383 314372389
    0xc0611090307030309050a060503061f0203090d0b060109080d0f05220816141302090a0905010602030d06080c09060d0c030b041430090d020607210201020306150309010b 74
    0x180b00158000e88074010300c2401c10041c403400b095560440c4003440000c106025803900d451098804400185000c0780022158417800c03801e500c2006822075019010300000d006001030140f00c180903000c241c0b9400d12440d900c1800903218070b141c0d00a000811801404564014004c40090407003000480c0f00348011180e0700303d24010880d06400c88089a840708212044180b01c0c88003600c007510750b080f08650501c108100042294501c108001c10786900800c02010a803140c3c180d24000d00201c0784280710541c0c4614000350340b500488040a1200d041c00300000e50204082480b034640d20700940003151580c1c4460a00c0342580480c04102c9240400c200e0000108e468140158010f40c41210318510700201b01e005146401441c911009012038006440d204038901c0500c11042c0c110303e51416522050240300107a200e0304200c0029402100001e2281c0810501039030680c01d40d603103006050302c3e810300d8100c101d00304d001c203c03a0641c0101c8201d40304402d080840024540c442d1001001240c4100d401001c = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 314374883 1250 314373633 314373643
    0x15030a02040905010507120207201306031202010b0d0b0403050a09080106091d0d0e010305060f030303150a170613080d1e0c0309030e09040303060503030c2b0c06110903 74
    0x420b58044e55200e042c07040703060b4480e13505041c01c2e4001d14190306200f855103440c0780d20001c9404007846203040e8500d00e800ca40b113940558070111180c410401c50345550381400d802c6058009007074801540b030300240c082d01d03181060030102041d4110000501994079940c1c00d0301e00f54000d603240801e1040700100000c110109004103800f41000d860080380c0518a2040c0340941181c010412859400c00d0b1031014005601c07040d0040418402d1902040c01c0e1115008503100400360380c3d9043e0540000401c01500d802009100c0c0986c000564006004030f981e01e0300c540100d0f40030401c00c12181c012074081480d041030482c02e40700759405141c0c403902c0c0407001031080044800064203441c010052400303aa145001d5882941e41d1800c40b8141403013120040c2d0390080034409000c0c034952142d04000c01103000c0c140719074041c20141030040d017101e9503028090140c65548001b080340c103013500103200094012031403e69900700d01c0320590f202d42c1210351460380c0384406450314040d040107140e02800388110340e580400c2 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 314376133 1250 314374883 314374901
    0x1020c0604082409101109031501050f090906130204062610020901050406050d06080601030b090106080d080604020a021c20032b061a0c06070f0815030a0204 69
    0x40102442d01e608100030104004222190454880e9542040703011080030810701d10745c42483d0000115001e101103001c104d405503c0e0181d0f0035110f10590340010502c036984541c141c07042115402030340041e400800c02e00c0c01d02280c03601d026800a00115010001c810030b440c1e6203520042c400304203240c50302c4944084240810f070851410704070340310309601f410080c0122413546c1c01100d415490301d010200041c15511840c85a202001800070300f03062441416071241e4080c2c0b401c001603900300d59490400c0c0015040588460500b0352070124001003400e000107003501031000b40d403102001035640d0800c01c0001e412081c805019801001034405502c1d280b0665074007000c110351a0460a103410320801d1206c030050301d807099400d90080000d46e9285080040041c0600d5804c58000501404154280003503c2c09500c154080c0c0d40000c050000e440a41c00a001800e12640403a84150b03900d40c1c0460720f00640c0034242e40401d10400101e500c81010000c010038030000502207070301960850380820304550542c4 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 314377383 1250 314376133 314376149
    0x60b04050a2105060a090b18070b070303020705120c0d080105030c0607050a0204050c0d0606110303040813210614040308240909060406051810050709150c030f030e030d020901020c0604 81
    0x52018001c010031820740c0740c0c1260301c0d0f02314040f000071003616807907507582c680c02002e60604004c140c1d40c007098071a030106d550107070344034081d0392013050301c41294806030304070100341003c6000700b0b2407803030b40b6a01c1498510304a882c001d00901144802c03005000301c5034001081070740c1c240100d0021102580322406128040d454110005a80746030700c952410840c0c001d604541e0820509155111011200100f50394006400110003992000a508205045c0c80c440d80000c469064001000c0d920022030925030840d14090700007406070a03004d020440d007046003110000c0200d400580441d8020305001081e145000c0161141030803c200031002074520102140e01121941c0030000b00020441607020340c0d5000421118848a0a049001140d488407400d070100b918240c0d81c0d2000840c4648514170000042200c000b40038480c86040030700070000202d00001740c004c030703c0107003801c40c10340c0c4030344a00342d48100700101660400200710b590740040d44c0300040b060b04501c19111428126941d840040c40101590 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 314378633 1250 314377383 314377391
    0x80a03020d0f0e06010603110739030503090301050705090904060e010b1305010f060e0315130c0617310602070b0c0301030c0b090d030804020a090c050904060b04050a2105060a 77
    0x1c005056816040000414023000c0c40303d400000c00700e5420941d2804005030907050b14614100402442c1850032442441c020203400c00401d02c0350120081920607420f8009100d960384200068400348500c10907540c00078449400540403a18503885901c01c50360440011410f2050603000508501140b100103400d03e40d00c50041080d1001d01c038058005040500344401c0c040740c420006034031a00729250700e003141000d1000154081d804085401c0495501031850030649132a032400074000800b61710b180b444d0000e100c000c100c2e842e0310000055940c2c034031032054071440301003005001024038000d4411609960203100c0d12001800f07112125110b0024012180d0720b07580b65080c2018103d2003076201e524503800030491000380d500d40b411344800081d010b040c1841c16032154800f00300c406003c1d13031081c0085c0707207002041d5004070b911000130700c020203007114240036580d210801c9900a1145203d0194042c11140040024006520300203a6444000e421201c01040c07a40320b0030300300001120072080803955 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 314379883 1250 314378633 314378639
    0xf08030a0c03060503150106080a0e0607031b030e030301120309080601031a010b13030f11030a1103010e161703040f090605090c03061e031905010b01020c0d080a03020d0f0e0601 78
    0x2c94807aa030b000b003030214028040e0300610100711158940600611080110040000341075801c1a000345070703000c1918084800c07501d40b0290007001400c444003002c0110703030b071503c2c03a002052090244000c588596000780d45942d10308a00d01b43e080500321030480038400d000500086281d03040c04654002d40c0608610881034003134554500d50200c0c141c2003440b0b1803505000c0b004c903944184136640d0035aa03014070742d4106005141408a800101400b81aa240c4500c10f40e00c030412501c5165441d040e81e064009000d090244051207484849005501e80391710415802001307004032082009500b04d000000b624a01a1901d807941c040280c5a0809408552034803070404c06428a100c805a101c281201643c2c21414540002071809001c4849821414001c000911850750140014490401032404540000c0014502103000e04240c4e4280f501500036030013038000c5810b05032000784105502001141c540303620301c9130030303802900310000c031a02035a0795080090400c142480341001e01d40e01c82008001540c5 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 314381133 1250 314379883 314379887
    0xe06011410090f05010c030e2101050123091b03070504081606050901080c0f0c0a0506060d02010f27180c14180d0605010b0414010203040f120f08030a0c 67
    0x90700311001010801a440700300152403029507040151002480c200b0500c5000741400c0342d9002c3c00e010195800070088160041c200e16140c042c180c041c6858000b809260703600c0c404113001c4141001c0140d88400ca1100340c00b07083c0760005459502c41a591024214401c0307000c2c21310507a802c210340328404a0300005061050603006c104400d2a0000508004c0704141868030007172580c0140c01c142c074107110702034000c0b80c58a40a00c080d2410f66403004420340d22000038040c596516007a030314080c0c80314080d80004c50883d0405000000720b4980684403c60704c00c1213248111080103c14034501c4080501c0665503042141151085008040c02101e00103101c40e80c0002c00201d95140040006004010103411700305050351017078404140306042124040b103814000301d0b07940c00c440a00141094600b500120b0304d102c02c1c41c0a00305807094203802d1142248080010b9030359100700c1c007801c000d011042c442000004010349200d860f1610510f0150f0b080d029903a6084801d03001540d030304c40466218003400d65699 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 314382383 1250 314381133 314381149
    0x607210e071203110a0c1502010f0f0603020901050301090c0e3c060901050915060d0e010c020d030207050a0b1e071e261e0a0203060a09140117010e060114 68
    0x8181038010781170480440d070741e40f001d00d1300c00d100c0d040c60350307194210344000a4000c0d8441c0c0700326402c1560600c0001da81e4060b880040019000803417050b07207444d0000c00d050030144510030300103034415070449802e824031820788480c0700700030002001d00307950000ca408241d8441c0c3c04e5000c4004000b03503074108074070700740340890149400501103800340ca4800300400070b81e940c40035429040440789031422481120500418054459011000c5080e4140300c140d00702d0300300561091010b160315a00f9110080a48503085003a480b41800190155020103612f1002c6201041540d8200710484007130b2007000300304c08a000100703004641010126401d201c0c001030005d40d03429074440f070b00207a01c0c0407441916a0115a0784010700840444090294480054003101040110007820190024030b030410346051740341240658000c4450a001d280d141800048448150180c610300c13602d01d640180d40caa0030500ca40c10900d0048010004540d20340b001c00000140611088d400782c04441c1d10700b40c0403002001400b00c50 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 314383633 1250 314382383 314382407
    0x30a05071112100e01200703030b0105160b0a06050409060c03050c1c0b01140d05090c010c020321090618180106020a0f0215040902030402030d020607210e071203 71
    0x500e0405165004000000c1001e03c050406460009001c001c190300207801460810349548a480c8485025a00142443c0103020324034802c5d40c1c01d1001c0c11154004442e140580c04a42a960604208010010b04000c403003583c820f4001e48002950b0f60341e4000101a188410000d8401d030f5510032415405503418040c850340404480c107110b19280042100e819101e117062950150259200c0c13034400542c8c8070b0355552245441d54080c80b900c4510025409005041c103075540c40031441000a4a00e040d40980148900c082d001800b6098a009044043d02040481604542c0c265010044c090303880e51004003922020f42407d246019a609500900548031700700c0f207040030940c0d803a000400184c1e81c0003030b140103520f6000f61480c0a480c942d00c049001c01e042403101100e14440400d003c540b80d00c0b0381e8069807042d4000c404964030303281c42c000e06903120942901ea4000050698442e5050101008014070035001003120010300d42005985140c20701784580c1120300310014041c400340a040d0301144020300 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 314384883 1250 314383633 314383639
    0x3090204060509190b04181a01080d09030b06030109060606020a0506010f0305120f0c0706030e1006030b0a09030210060b03180309060304020d0602071b15020318040902030a05030a050711 82
    0x1960030415a50641c920b05030400d83c070490703122025001a42c40b01c1c7c2106e141d40380d000251200c94815880c007490201d2980a403148000e8000d00005803645000400f540f0300300d100e86500c1041070458039841d00391345006000980543d211581c0e0760016000b0301ca15001031245074081c1c802940c443c6041414030b401a8050300011407540c20a102151700400e203901035070540460247c0c2c400140d8131f854801c0c000c000017182940500b03440020130580540142100301440f070241c8451129001101d4102c0394180130241000306c071540010741103443c0f41c1c40920703114024012510b030112505005010755402e0b800691080d2004024091131a100c800348a200c0842d200156040c140890f011401a00000707101911920711403035894203003d00c0ea4111107540390000750b0b4043c2101c951048105982c59886412201d042c3c1c0c1c081140031f14808401d80e02c40c04a5030109190030780301102040b0141c240000203a9040c00380c00503101c0064002c000400ca0340d005500d420b900c404060034003400c403508600c0080c0c0 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 314386133 1250 314384883 314384899
    0x1140901020c0d09031a07183b0a0509030d0911030d050418271a06100215041a01090501180209010f120e03040b0310090b030601060807021c030902040605 68
    0x80003c5040640c010306c0055502e082d02e095558000032a0004c5143d00c1c1c071030007045160400310380d22001c64000c40f00280b5850240d8202c1c13512520b030008034080403030344002611055000c10301c00036541c0c00094004141070112820000c0107030030305007117172040082166500d5158240d45c10b0303801c0604c0118610501801c2403400c00349056420714214800c0b0f1a0100c0c0140c1e100399040d001107000780c0c111010003032540c12600702c054034030f0007201c0310102280d1400d80c040410009103043c640714651500300442540904410f40c10380c40c80c000d041c100540222080454051070315031240c0e014060078024a41000c0200b8035500d0450013146280002e055203d40c00d004114180460b40c010081c4c05141c1c00600e094000888211a01e0300204801019000103001c0060005030100c0c0b5000514010081c3c05005243d950b6994424000c4600856005030960003900041040074080c851890b40003065005070b44490307100308a00d0b8140c1c0d003100c0a0901081c0c0c0d0700d04038425401c082c8607803c003900c0c0c2556824 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 314387383 1250 314386133 314386139
    0x180f01080705041701060b0406020607120b1c0204091e0c060207030b0c07020f0303040815010512210c0a030f1205061e040f0c050717090607020105030901140901020c0d09 75
    0x703006120f58080c801c0d00104004000007200001d610800003805601407003911203031507010003912110b040d00c411b4005201172800b0318400303925105d108155a002420800b00c210840e56002210540e504140e038810f5690344540c02040c290b0801c040b1680414010014035485480d118000101a070419001c540c0140410300010b41e00645150b040070341c003402c980d1141c46a1000a08200c1c08103a0350750980404035000074041000940c541320609042d200044136030301c4100f40b2104030704500141d10150321010701910450500940d124010b902d1040741c2d45040000b060003450450074000480c00511f01d40343e00c805003680207c0000d400c2007003060601407403c2c40c0c0001410719100050900c1c2081d02c02907200d1190f55254001036060003818130620003040e40400107000b940160a081d0f071781c2010701540010184030ba20031204031440041c0024202074503600116041e030401440611159a5000d9403d400c0301101c0803903108046402c00540e64089070117481d801c01e09411411014050456028 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 314388489 1106 314387383 314387387
    0x90a0614161103040302040c050c031c0c03020a080402010834021c02070b03130b0f0709090c20010617030a0806011d040b03030f180f010807 62
    0x8520030620054064504100c1d034108550b041e002004113100514091740b10f0040303040c291610f20b04001040410603d9076002001507904022416111000d0b515503000c1e91145480c20715055081c0031441502624a00000d0030007814840030701e000407102014503000d4041041441c442d00368940100c103e504030120a940c040005000710b0f6038000f035000b42003c6210404c2d100740e0081c0032240c50242100c407550800b9003003464100052042c1e402040345503200300c0c0100d403100841c003a9070a1540c8041e002075615404207060504028140aa2a820a03401801c150b0f01102d120000c0000c108014010800703900200d11008100c0d140c02c01411000001c4c0049524540380c800c0700f030316124010344900070071000140f0301c443c1220621b445400c06800007420460040c0c00c176420140480089140e5800641c4000c034481c4c45419048414900f00800344d40002c400c1c00d042019041800d00 = true := by decide +kernel

theorem cover : BRFrame.Cov 314208633 314388489 := by
  have h0 := BRFrame.cov_init 314208633
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314208633 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314208633 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314208633 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314208633 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314208633 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314208633 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314208633 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314208633 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314208633 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314208633 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314208633 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314208633 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314208633 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314208633 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314208633 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314208633 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314208633 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314208633 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314208633 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314208633 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314208633 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314208633 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314208633 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314208633 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314208633 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314208633 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314208633 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314208633 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314208633 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314208633 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314208633 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314208633 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314208633 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314208633 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314208633 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314208633 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314208633 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314208633 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314208633 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314208633 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314208633 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314208633 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314208633 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314208633 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314208633 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314208633 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314208633 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314208633 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314208633 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314208633 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314208633 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314208633 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314208633 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314208633 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314208633 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314208633 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314208633 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314208633 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314208633 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314208633 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314208633 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314208633 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314208633 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314208633 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314208633 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314208633 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314208633 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314208633 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314208633 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314208633 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314208633 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314208633 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314208633 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314208633 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314208633 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314208633 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314208633 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314208633 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314208633 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314208633 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314208633 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314208633 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314208633 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314208633 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314208633 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314208633 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314208633 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314208633 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314208633 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314208633 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314208633 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314208633 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314208633 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314208633 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314208633 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314208633 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314208633 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314208633 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314208633 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314208633 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314208633 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314208633 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314208633 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314208633 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314208633 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314208633 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314208633 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314208633 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314208633 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314208633 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314208633 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314208633 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314208633 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314208633 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314208633 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314208633 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314208633 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314208633 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314208633 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314208633 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314208633 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314208633 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314208633 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314208633 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314208633 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314208633 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314208633 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314208633 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314208633 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314208633 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314208633 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314208633 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314208633 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314208633 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314208633 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314208633 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314208633 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314208633 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314208633 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314208633 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314208633 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314208633 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314208633 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314208633 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 314208633 ≤ n) (h2 : n < 314388489) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
