-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1644
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T04:01:32.07914+00:00
-- url     : https://prove2.me/submissions/bd0c8e88-11f1-4198-b34f-9d24b5552380

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 295503597 ≤ n < 295683453 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 295504847 1250 295503597 295503619
    0x150201050a091a18191e02030309040e011e0c09210308070201020c060115180b0d092108040605070c050601031e02030a0818010527131a 60
    0x20200380681801c02e508541c500a1206040d011031030400c100034102ca08103168441d907041348007000d204510300303040540703049619a000c0341441003855110600403400c1002005004005071400700603191281c2c4126800103c0d04c06000d080c45c09094034020318a100d880c0780020b042e40d07081035032000340800b0540d61030389103068866900d12085185c12101460444900156030700080c41b61801680c091020f1001506001c10658406d10703001081c2c01080505507049460007502d0b03440800403902d1900007509496441c85c00050a61500c204051001c0003500da041080600601c2044041c4980f520340c8092540030310080c0040c1103400035101200c420f401c04001c9290984960300b0850ba080c1c1003005049140d10790750303505c042e40c80e940c0038060221f00410b40700005070b074080c0004a042c0d801040c02e02c0d07450308890100c02d44c1072014018203041c0030301800f418420107440002c4c0340d4a541400c1070b007134002d10000d002441c091449030f0040700460900d2110260140000c400c0342d01500203581c041e24003 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 295506097 1250 295504847 295504861
    0x6090e0103110402070305090d03020c0102100b0904020f1c0b01030213020901020d0e032814030f041205010f0509030d0f0209130504021201020301060f0e0a2102041515020105 77
    0x18410a1001038101141d01035011801d1400da4014611319100e424410311b04443c00020a07401f0062200036030160300045000c89071560148007280700114414010080301203000000f6080c80340150020b402424400b80c60180381c1c41f00e541284c12012040d4106402121603e045203130b241090208034080c41d11403200c1c404140c0c00f8000c1d5010307014140c010302041003031004c089820400e0503020540c58468082e03107054105400a0426020300001380c40030140300b1070f0030000c481c0362001003030005c19441040750342c00e000c071900191001e1303540c14401d48040080c41e050183c0900b40204500b00364619110a010003480008010005d05520100600000001c9840f25049002d090300039900310707500c01081c9410b100554409688a44028003a00303042590f02e00d8942281c000b6041880454462000c0d0504150030035007a4002c6102218445c0c115400e10001d11a0a500c01c5541c44404968035900011907950750002640c554000f00311750b8074151f60b56154034030200080d0414015510f0580442e0f18 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 295507347 1250 295506097 295506119
    0x304120f051206030703020901180e150105061c05070905100825030f02031008071a1e0712050316170609180105010e06010e030a052503020a0803040609 67
    0x5031031215140c8500784440c00c1c65050380d5a070020403090b07240c041c50a0100060f075480ca07542d4003810f105000c0c0d84d02d46990507541011540080790401c1c0990100070003030804180e0300078030b9041d00d0003920b40c147c41d000b500b071282c03a44c0d0303884071320b40c05805041c5810018229800710204040301e10454560400c01c4510b202036070240e41c160744050383c8210b4901c0c1c41004894074021244c4c502d000c3d180000f07650f0020a00d0b0b80407030300300b07640c03030000030070b03803907410405000c0400242003d441030500d07803085004580803450a51082c00c0800c1d41c8940303c801c1c5110b92268100c1581c2180380c1007549100000c020410040180d4000c4459402038544200d400d51328a21480c030818130f42140d01070a50181d02ca9400300041508001d160320f12038086454150107424003030152034000c00341d1244610060802000240a107544201d619001754000300146000c1100001c41040b0709450641402d100104401c0c03840c8056226000650010461030b00050900f60000c014412a0650b035220b41c2a03645401030500c0c = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 295508597 1250 295507347 295507367
    0xc06110307020d05130803040f05040b01020312070f030e030a0305070f021902300c0a0b18220207050312011202010c1203090c030b04050c0901060c35030412 69
    0x10ba0101d811008644c4c0200000e18003401503107607544c011590b5032103075450b42c0d000d0781210403040408481080641414040c000303080320240090740c180300f09014604283c1000801540c204807034802070040250090744082e001d0609481500e650b1881c0ba000900034040a0347c511000503035044145400c944041a0011490100c844107500b1550980800c010300c41034100003c450321030007411f050380b50036804145007401480404bc00c00000c0701010010300c0f01255118034000d441c10003541c00400b00440490010181c12202e04030307950407140c800c0c14031600300c1105618035480090b0190a00c00008040c3c8070712a800c014507a050382c0c90318030b541c541d5440800006d020500280115001481815003041c10186900d0005801e124a8444c0101d03414a41e00c00c0d58044000c0741880103101e81800145507880056814040c6035152280003080c0000110b03002d0076101d20300d80c0710071900141300600098286800348140050118296076021070348280d40840e501180900c15070f26280c02120008 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 295509847 1250 295508597 295508611
    0x603070c1a071710090203010303020d09060513090207030c051212010b1216050702040f02120a05190b04112b051005090c0702030604051018050303010311130c0c061103 74
    0xa0f580c0301520000e0340103030020b450303a10b200c1004000801d4812280c405540290b0107a4010003008003083d602400d201a03a4018004104e010000014400f0902c0000d004071026440c00607914400303400d04a880c2d01078000010210b000d0711a58111511660024200140c0407219030405a40e070789540c1c00440c4210a61290204102c100090f02007640c0c540c8038080d40a00e04105284c0142a40000d04490000302c1400301d1650106010b040c007240b0000380c951100d100c1d00d042000341441d0440b010703040e000ca0312141c60a034840611141c2610b540e00120009a105415030f038481204400ca216000c6201c1100205080d00e86180ba10070a81c0340111401000150380110742c5c282410248280403200920b00080e0348003c03c203110050300d01308070303040c070980c080c401500741840040c1410059880068080f1510b00d005a50100854004401c507411240d0107101201e101c03000c040441d2404c644254620710140ca81400f84000f08d07040382c030301005180701c1c04040110b00180750305050381d4001079846c2 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 295511097 1250 295509847 295509857
    0x1e060e070e010207031202060411040b0a0e060612010b0408010506010c0f0b070903150509070501020d020606040b010311030408070203100204060221040801020c10060801110a0507110603070c1a07 86
    0x8100080e00541c11000d0340380040c03040d03681c801d40341e40b07405c00c42c0c84071407140e500180d0044d4100f00600010b11038081745164212400e01c1101e40e101c00007403418899010300000c003400381d0007003a01c6680c0c0c0d034116030046240c01400746996a403404185079980161152040c19401c0c600001c18070b40c45124100c0301c1c6a40100303000c04c019407035164500700c0f41000b07107041e0610a1a40d008000309040d80c0805104c040c039401c0101e280c3c43c2100360b203400e04020350b00c154150b6020200289505c0c0e004a1026031160050310700068092a0800483c040e00c0c1210a001400e90000309200034429400010b005c3c0c07038000d80840d6124070180410070f003244243d200b9800140c01264060402040304420480c050b8500403c49051a48a20070b03203003241e04c030704800d400d203501114215992440b0380c000d000051403d41f000b000034592000d00d20b4150f1003191041c070208000000c1c1d413010018401080c003001c80002c1c10755516494040c2c0d01401104804400b07843c10440480d6000c1c480741c90036000d40c0301d40c000340d0354 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 295512347 1250 295511097 295511101
    0x301050a021c020309150a020a020d1e03020d020702060c0a050c0105070809060903010905240a020c0d1809020406030f05060f0f0402070809090f072705010e03010207050d031e060e 79
    0x3401c8020340000d00041d03018000c05410401b07540c02031030f90354041c07800040016910404510040e24042510ba101130a00201071540e66030503a1000c06106200b915040142e61205003600100080c80344d110000d40c01000891b80300c0f160000050b0500d1117074072590444202060040040d59140504040149008410007a0701c51504086001e0700020901a002041001c01d07640e4060800c404040084081c446910701000c49000c844203440c0c02100c8100304604e4045420f000c1c40e10743d00200251014000d46000003e41190320b95100720040c21030301421034071740e601c41c7ca004016003550011034041900f044042201490b15034080071114400804240c0072010403030501019411902042d60b0b42c040a200003505d94807880d0a851040224100401d40c0d807510400c0501100420807095001164000211111501d43c0b142101038980234206030b2400c2480000103806841500c5d4020814098500422869600740d006440307110030650301500115410250b1000305c4060f80304041d200346c03020300 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 295513597 1250 295512347 295512397
    0x501030c03150b0a0320010c020f090c07050f1623011809110403121b3201060f0b0903030304060e0a020306010b070b0a0e0604021306050d0c03020301050a02 69
    0x40e02c449460719501001c10440740c4880000c071002410360059404c4036044010a40b20060100d8903180104242444114035041b50003062008440d0701101b8003400900c00801c490414480c280d030122680300301190000100c0c0602951a0f8807600401303103800e11000c0c004203004800c0b00c03d0303040c031020301c0c10346040c0680c45038011038a20f00090031202d00014014030224800c540740c06841002d0032600c049543c0c41c0e20b113144c410b0b1307460b200407000c2c4208516200099450b80140315032403001364006400303410340ca495245c4400c0b0403030718418806c92100003079144103842006402100881d92600b4031964501d645041105452080440107a45034108200280014945902c00b0741c80044d100c040750741010711907010900c1d00e4000e8012901d54000880c10f20100800c0c2d07a0369aa0240d00c20109000414030a410b82d80e0701c031000351009201e010101840083c075040d55000c0c0005101c0148081404002418105090a4130f808160301a50070400001d190f0340c814004c4401c00e00646009002c0320b48821 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 295514847 1250 295513597 295513613
    0x7060c03021e07021026060316080615010801081908070b0708010e060f01080403030c021005010f05120606030c0d0510090803010e0601110309040b120a05030a0908010501030c03 78
    0x40210400c0c50381c244030030b01c0142c1042e91040800d0700803a101070741d5032a5030b004004e20760f40034882100403c1500100d52810503209a480b03412010407010402850302c8040029040ca070b11000e60310704442a6038800106203200060081c0240190196000e0400600004440551007401008134642c86881150103007280c0314603000c0712034061a840c6003408480e030b0301c004001030b090300c0450004262000500c901810a001030f0b4201400f1525880314807841400a8011100140f0241c14550b50782c5003241007500a0180442d11102e1000801c901e40e1103c0742c503070b800704583c080c1ca40500e40b0102100c0d994040081c40d02d01880340100200080010b9108000c00c808085808444501903050021000304060040583da0303407059401ca85c50b1360400c00f08500c00c10008100c6410800c1365402040441d1011089031201301003503402240e4501850301081c0b80f0421500684180d21900950000b44000400a0000200d165a580c034900742d55441140c2610780a000103080c1c0d810408003000094840307 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 295516097 1250 295514847 295514861
    0xc09070c0507120302010b010906111f02090907051902060105031e0f070909031106040309090209030a080313030305060a03030e2704030c05160f0302041a060a020709050105150706 79
    0x200100c072402903d40281800c0758001c64021000b5030b440312211500342d030700100b0040c09800b0a1800116004e000342c10f160f942d071240d002e000b110f8440f04648901a1905804842000d0310203070005205050152004101c2d611001880e000c0141408012580b5440420518100c840c002d0003070403200014152500e491159004004c0d07988991010b14070076500501118008103896000021000403034100a401707242e10340040c0d40c076904524104000240c2021801c82038036164400140c039801c40902007890460342140140103558080300b00080c000301c2001c281c1d01180f1a64091100361a41c00a008038000c082c0402004200c0e40b64260f540c604103c01e081d5034143c02c00080c06018200f5105e803407686c280a91742039002500c01a0f040091060070030100b0480f100419100000c00c1c81c1030700d0251aa080790000a21543d20b81c4092180340e51691800021081300034234040da2a506803030040d40c0c0f00c010788500d158107414100002402c0c0752040c030b4072564900c02c900803480d2040d280d4810008081c1 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 295517347 1250 295516097 295516103
    0x905120c0c0306011403101b0e03070504020d0207140706020709110706110c1b03102a050d0b040513060917030901090b0c2505010b060f0a0806030c09070c 68
    0x40780e207110032640e800c0100c42e00074010681c00d01456010030f014541805c4049034420140741c140350310710302124002c101c205000705070381c68075442c0b40302e0301070001e13003400b000d40e010b603a000d40082a40031b10210a54001c0400a02c156403001c204542c0396a41a00c9035054407071240981c0064500300100240d5410243c00403100c000150b141c010f440e80c0314403c07100b0018880b11445000305001c4129142088840021102c48810072480c681100c0000d58401e803541142c10101d07200c01c8040c2c8402140052880c02410481c026100d41c0304d5108000c006421000b2920300c5d0324200240c0320f455041a201e00d600605000a40c0030800c8000c2e11014058200803400315036003225102d80c1c4188488013030207940115191000419030f007a4904103030000303000203031012480c8502000700185010050f10364401310340b14100080743c10b480c507082c41401442002d1030641c00c4040000c40c40211940400140030728042c0307403110365250300c90340203042d1707140415400e054106d000000800c17400c500484042c0302182c4 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 295518597 1250 295517347 295517353
    0x3030c0b1801060e090c04090c1202060c1005090d05040f0e060f0904062310050126090106090c0e010c240f0203161b03120f1e050105040905120c 64
    0x700c100031807421070f142c0ea4803401a0610000502000b10018055416000411641400b02503415200c0c00192121031040c03160310255101c08208640792401518900d1420200b070700c00076994102800f01030030049542c0f0b89a0300500000c25903040c0154166002d0302c0726051610300c20f0303080c581031070386400004c1c004170b40c811070982410600c1d40d900640240300e103129500200c0d01024101198900280001c0d024904445400800c418103e140020301d04940091810050015041007460303103540f03521503a451146511800c001304034105411000c01c0ba07104030304c2008982c01c400421120301d400c0440c07050008a0704859100810861824602100c0001c840e01203260101d650403000c643e00f800110408503004020003190065200c02d002525820b41001e40750500350078000140c0d0407461500400b1b1120780c2c20341400d0301406500c03000c40c5510401c01001f156001000c20850b0804501d0420300460805001240c0c9040ca4000c444646511034010845d01c2280042e81000342c000001d040340130700c = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 295519847 1250 295518597 295518631
    0x60f090305030a021e0706051c06050319020915091506040824160507060c03060b0301170f0c060a03021e0714010c0503070903020909100c0f08010f03030c0b 69
    0x26400b40300400c01803d0300d8008141002c03181c103402d0011400c81e007140c0c1090308005010041e2940110489410500ca181d101c4008940071041c140205080e8210369010300c01e90b03442889000f0701010014600f8006c545025031940c0305800c6100d4680c50750550b07900074010300d0201d40000d520040f11242003c00030b00e81420207445100c03051416082c1c0c000610303001903860070304001c1c501c183c00040d00b0140003042a41d40c0886008080e20502c542c01c4002e000c16950705c07042001318032079440240545000181f1541d2035030340e4210600074081059034030103940114a581c804050000a030281d01040c003500080c1404440141940250881000304186d000c041c440d400c03503240907074001c06040d40300b0300c007500d40080341240d62421210001a508240700c8100305100c4465044900758080342d904450411282e6142050f17942010800021041c407681080da441c011240c00c02004c501440c03455440c1145a80e031001b0500781c0704a00e10000d0b01103144098502c0210703252040f101e5200078501c40e80d010702 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 295521097 1250 295519847 295519853
    0x3050904110a1d0409080301180209040c050c010e0d080601120b030304030515010e04031b03031b110f0307080406111e030a091710020309160806040b01050604060504060f0903 77
    0x1a440b001d00300000481c50b00c1e0510b500c401d003051000144505880c200100c1205507180d805906c0180600701031318204803400b8807070a805404480e00080d01510a01c0f0b1003c03907000191603904051040000d030350a140c0c0b00201c2090004440120501c0c55031503200700d4540c4001035840e49034a03c0c11091482c1c5811003e0f0f2141c9003000240002c510480c010031820140c00010b9140e4031060b048208401d0400b414000841c1d840640d140c014030100f1801d110a05d103603e0164020149900d4559524481210b0441566041401903040021070000e51340002e6610300c5054492041c40c000500307089041c4028020302d44103076122684100e9174801c40d00038001e00280342c9a881030f80b0020120aa0000070700f0f49006621500b801c000300031030f081c000042c09080c00501e81f02d40141d0012a021540400003c40403803013041480b80d0071000c0360a100c2c41d6600d0750005901c034031040701d040e104015003c000141c1804c21001300d40840307180360342d20b07030070030382411800c6400e0900b1040e11020800091404008 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 295522347 1250 295521097 295521131
    0x1e05040e040b0402030d11100b22060f0f0b220b0c0307050717030a0c1b030b1e040510110702040509010e06010506180112090c080321060d03050904 65
    0x299010b140044650703d4640b041515000c0f42c019030104201034901d1440041c0c0c40002c01040404c0300880100d4140c1c0b55a0105101010744601500c00c1e900c0b40103000030300c0b0410b90003003080d5004014544103440c2c40340051140e1511600c0703901000b100070041a4802d1194085c800c080980a40180c20640d40d5200e4041c2d99400c110340c0b0f42e1480e04002020000c00c02d04028120043c45480304885011058044d030316240c2c05003108010500c41e4841505041142c0b4501c103080c00d48104c10070a079a29203e040800340c0c07410846414a28041460f12840c1c404070030800c181c4920f52100c002c00312441008141d40c0900351507600540f07680b6040c030a50340141d480b4043e00303100702001800068a18544040c1603e07000045e844076008520070042d80344401e501c80c1c04108407040a007443c40c0c60140d404032540050100f44805400c030f807003c0c8030120342041c01100030a0034401442030b00303903421202d15854002e0715044d60f1090348804100301510000c1d0003980506100d000003840000c0c0d00c07648118180c4 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 295523597 1250 295522347 295522351
    0x3031109090f160905060405220c02010f1104052b081206190807061b0204090c030c27050403051210060909140c0306030a0501060b041d071e05040e 65
    0x820b040035810084800c1488544080140035458a00c030303a240340c1030204081d0720850060a01540441d001d881c50514061200c00d040b1711003210801101d08601030013802803400c000041e140b642820400050700c90321000396410746d24014108540443c01e1140e03803110b054100320700e64071000017100d0140890b00c000080d020310114480800d103545444001c111100b0451344400402118045061008200010342002a00c0590a080e070310f5940500c86150b2403046200000d5000303003480c20301c10801040613084822a807041c2e680c1e40c0c54035151201c802c1c2a4a641c404000c1d0401101080041003255030811380d01f040c041c0c00c05506e018031200510012540854010680d5560303010200503041d80a809c0c00b0044c03c480200700400100014143c420300000703411036a19441c04400300f500c0f5501401030b2044690f0210003080002d68952200c904ca411a01c41c4084400340194103684205400090b184224042e1742c410050003d200c10b040050b0b50001e00074420020140804140c421000600c54 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 295524847 1250 295523597 295523611
    0x50912030c07140a0f0b0414030f0a0b060d0f080409050c1603051318060f080c090420031507020c040605061c060f0602010501050f0102010e070e091006060e04060b04120303110909 79
    0x41d91740341010000500d0081644c01e150003980315400405030858086190704155a020a3340c00307081d10b4000010f04001e10859000c1c1950002581c2c130340c2004440c10041c000c407040c0c504180965920008207002502a0089200c4c0b800182000b007070009120300d00802010700501c2407202190b80b81d81052415030164202900ca0a5032540c2c1030009403140070380c3c403009240220080039501d400340302141c00034101400050414500340c07040031f401b0f0349410040080c01e40280131a0303040700b004580c00c0382e0184140c403014054040c0061503c03190030b041c0030301029694040c100030b242c040320002440404100c541c5403101301d640d4080201e842d030380c24015400100000c5d400420654142820446881e03c0308003044d06583c58261440141030300403803008129101003070703c0c819503a0303007804081c10920700882c60700a41e0701e0400c0210312281c110101d11308220090340c04000d5583c4868030454988504d00910201410a042c0300001a100390018003a200d48907104c1410125504080382c1c508074141c0e020 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 295526097 1250 295524847 295524869
    0xa060e0a060507080f0d1e020a051c060519060801060206070c080a0311040906052d090417070b040b060102010e06130c032012030f04060c0609020907050912030c07140a0f 75
    0x503582d22207845401f926660b00c15400b1450800c956001514510076940103126074843c829100400c1001a4007500040c20040c0c050b580341e4614502c01c070200c240a000b014049020f85c00003142c8a803000030410b206150750703100e80303851804030740b26800c0c00d03001462070004150701c079003542400f40058809000204001d58000c038015050408000111984a10501c1d106502c010341074040c7e00010540c40301c2c4c80c010b0b01c00b40c20a40342ca08168001d03100c1c5401c44100c16034001411400c024044084500c1240280c5021005d80c8948c0012801e0b20183e0524111648c408404265901040b4980800d80d5229000d8403a09954981d5540340d911054814240800405032440d22541000104940703456030b2140598680702d0860101c41990145020300d07020040c60900000030050301d5405890000d03001001041d0b945400c003c018002e51294810b180600c07111301540e201d0890001c160b032005510000a00034031410b2840b01d6008071044583e66500c00041c030b034001000f80d140042480509644405 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 295527347 1250 295526097 295526111
    0xf0210050c010b010c350403050d0e06030907052101050f01080c10020d0e060408010e0a0201030f0204030b040b0402031c030605100806100c2f0a060e0a060507080f0d 73
    0x101c07803c6509680403581840511070f90b1100113509500015148181d031412151043c5190403d10700c50b001d141c09626818000003401b1061200000720340011060036a24541407032804401d00100b40016102c811a66001000502052521090f8801d01b59034070701150348810b8400440c1801c1d07807410f0b500340c0f00d4a00d5040040c0310324030040c000041c10b2102512018030450040b08000d688510f01d0340710301d040100380d100000700f03661040e04860080910200900194090388845900c8540e0035004034003003480c1000c1c03000b11500e18006d54007143e40109082100e41d407543c80341020944018001c03681800380410103400790700135203040d510302422540c002070380c10704150a124980b142005880180710301203040005035902c0c0c4001d039100e42064a45030103524000e01d0200c40010ba440443c803807031220703003004070075140380444451545003003181d4984e00230366a628142c494a4407043c500340c001d00813040c2031142d01e0003440207209880c0300d00361240c41d004800c0c40d101e255400800d80d074150309031680a = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 295528597 1250 295527347 295527367
    0x140d0618060b120d09030305032802031e160e190e041a0c09060c15090c011b0804051905090403050309150705042606010923010e0a05040f021005 64
    0x5000c118820004004c00490440060907601c3d0301d1100400700840000010f00983d491f07001c1c1002072200d054214612840c055a01001e90002c82c1c031101a8007030300b00c60000340d111241c903442c0035400710740140d4070b0300755105412900c89404002c0c164015800d4005c8044035400407000030000d0940c0144520141030610b04131301404503c2a0020200344181c0602c411886900210381d9585811111190b8824001e65418206520022000c5170022104200103a45001150072501c0c503100341c0c0c0f003180300c806070202031810403480385000c0c0100070140414802424a1610700740b14900183c0d414002d26078500010b0352401040304c04400042001c814810380e010304001042120000359080c500502e0710340350050050043c0c2c0b080c41c034030041c03445502d0103100070010680c40041c4421b050744c00a40e101c8140001810f40080343c00d070341c825554148820500164981c90603108031689401c0d641e154810741e14080e00019109a0741080d048a4000041e507411640c035000c1240d40d1a00d5880e500d841c1 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 295529847 1250 295528597 295528609
    0x1202120901050601090e04080d1a09010b0c0d050c0c210601080a031b0b0c03060103020706050f04052a0f0f0402160b010906030b0a0908160501020c010b040204140d0618060b 76
    0x250006c1122408481070100042128041c0e40d54410340170800650301da0080c00031524103040c179540e650000715a60010404250080050552095101c01c4540f50588114101c48900c03425400c81c60036009200504902d00d400880814000b0f001c089014942a000105908042e03007a030214500d50710411803d0300b01900314090480d0881ca02280b20b0b04844143c4400c24040270051141c800c020300000090030680c0a80d05441d00c26070040002c04c803030320b0702c00b0800940c0001a5400d981030700c5504440c020003665030512010240f144401c1e1340c0d034007090300d09011072550f072400d0403903110814800205281d10f540c406008002e05684850f0760801e142e0401c10b9103030f001a0441c0a64604102041c000f0035100e069494200850440005414595082209807070007094180208090114081780070310105401038442441414002c01c0500c1050f000c0100301d10980c03080c46298a11440400d0303041c900300704c2080b0a240902c4012805800540340f29030404501002201c005d999211b040720b0f00c0c10b0103 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 295531097 1250 295529847 295529849
    0x1060e01050306192705060604111207090e27030309030f0f0d110a0216060c060911040c050706060509010b0712090e0103060603200a06120212090105060109 69
    0x204461000650520700481d4031500c0c001c10300f2000034a00021100030080660100030a02d04070f09119200032062035020b07180440040c400c3d03d1600c244004902680707020303c5441441c0d8584241640f52458080181c98100d1b0020050300901856120000b031260010018502c00c80740c0c0c0710588040701207840d20343c90340c03132483c241c0e410b40d64018010403000710700000442c4ea010301c001103543c2d2913084022170030000d4030031103141e0b800c96402c009001c6003500c81d08000d04810074250f0240c8405504075846101614010710500c40005c0b40303400f28201051550380007006442c01054041048456040032906903082d517003091001070800280c99061002038401c1d800035150441d003c9030207500d4a12039a40a00034000003400d69000c899000799424000d800e200018010340880034065a9079090210090019100640e07903101c40503c0305505109140101d1014200102859a02401c01604031030b25607007112044d80c03035582080310b1501425450610b910682d80795001064600d400f6000500390045 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 295532347 1250 295531097 295531109
    0x40807171209010605030705040f020d02040b09030d0c0f03111606020f2808030618010b03060f0d0201090e07120f060911030c030606090406090507020a050705010509091b071709030106 81
    0x2403c04c00b400396650101e80502110000c6802040b80d8150b01541d01c000e00c00c008070704a07460320005000440901641c09040c1e110b400720300741e03000d022074844161810004c1050003000e101154402c0c0c8000307801501a61140c0713001d5400c851080341300d0351049506c00e211344c1241001d6440f82c1e02941441104000e11030012200301d40c0100c01840b103021500402c501680010a41d0a003c40020b107651903081801d104412407506082155a5a0280122039030080d114940501000110403400d41000e55070109420790603907401078028906520040b0303600303000c4c0003041006000015410b04204034052a52200b4049200141c0ba03403400300450101e4040c4210700c848500140100070307a0022410030380c0e80c00344060340e03607954a4134600009002040c0a8110301c521f207162100340149282c0c0080da074499180300d01c0443d0400e039212001036902d40141954241d10041640004030741d030210702ca0082d503c50b400101d0b00c0c1030031000d503504448250b000e03110700c0709100085805501e07407809000382c03001009 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 295533597 1250 295532347 295532351
    0x19050f011509020a03020c061509060607021305070216030b0906070f05040314070902032a03090a03110109020a03050a0506010905040305040312120e010c11030a051204080717120901 80
    0x304415454250030041d02c296801940c1c041800321186010b030301156104a042d030181d490510389100c1c80016100501c1109001d41c40b2900001d10b0740c1050300442e000301c0d40042031490501024412030014020003007161045005040d48058001009802d07030020314400c81d00d1704541e1500601e01454411b004040300b00300301c01e5101500c8840d4002086405981e04840858005001c0002c9285001e10716440502c0103407000041103140e01205900c0403540703034031504a0384500300e03201882e02c3c940020703241d1210b01d40100722007c2c002405a85c4480c2c040480000118150040b82c0004000e032065600c00d5815400c0524103000b0401c050000d5030150404400810040c00c05440013031840c0218003000b007224458a00c610101030003140f00c42c2c00c400071720105020394004040503074040d03c035100713081d0007242d40720481d80e02a89004c400d881710fa2035180d4a060400300340907402c45170b070a00540b003030302e030b40e034040007000f000c54034103002000440a6503610729614403005040950848004204040c036074 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 295534847 1250 295533597 295533611
    0x21210050904080706090507060903120306050f240705030a0908010c020a030f050c07091505060337020307090e01050d030807030b0103060815010f05010810050d110319050f01 77
    0x5900c40340c081ea0082c0d0000d00460b1900c0f400d01c0e10700700030184c60f10090280e1055a02c009180c80e40f00c00c0d20002e4a205960084201c0d2200d282030f000d540280c095035620141107040100b46051580702c01a0400401b21041d001c682c203402d2104a1394040d440540f125000020b5285055801448070b900030000342000b0400c00e0030ba800025110452020010100410101040000741c402c000b52044d0348407400079181c001e03a0b65000b003c02018000c0c00340414030380c907800026907486d10f0010307244903030010a407201364180140014200d00012514900c4565800c60000d04024000d2019500c0b85900b0707201ca400e45030800200095880059001e148074008440c620303c0002d03880a145904034240382001b08205040340e0059010308001d400200161155000701c41150780f0100410303048440604d40c1c2c038616515840111142007007150740300c0080b045400b00f0082818180d41c120341690007040403200c1c6000520021703050503a8600c042046000d400303441402e11500b40100114059460020071400c = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 295536097 1250 295534847 295534849
    0x60e04061b1b0227010303080c0f070f051f02040f0923071407051f2a0201060b0c0a06051f0e0c16031110020f0711040f020d02121005 59
    0x714181c20000d0b408690003010070401c5440380e40100da03040c50700250220b5403880b031400d4221209400d02c81580025a81d4003c41da0f8044036504544195107030100d030501e064000d40310300c420b4140d0040111760512542c07c0303280360311520603101c1511040c0c03135002580d181e24140241c0f80d140c0d003035044070076194074000e038040d1000c04080c00542c0d4406c0e04103004c00156182102a81d44000e401d0783c82e000d090000a03070a00f040360100f2190f114483c141c40384040c0c40c08110110003113800201d800e8202c00500900d91a844501480d1517034440d400b84004a405070700c450224400360412201e070b6a003503200c64260005c21005004e03580d401450000301c80c000d888100700c50442000f5600c121004401203001060301c60042c00102d5415014158001d8441403032032030300501f0204464003001240c0170364030b6641150186802146d5040f10a02011424542c03691200704119100c4800700341c0c801e540b000400b002400760700190108041801e001a120040700494290240c0e008240c6e455001d0700310424442 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 295537347 1250 295536097 295536107
    0x141608010b01090b04090b0409050f0a020a0e0f071206150309031704020105040b180d030c0507080303070c060b010203360109050d0b0c0c1501031a1608090c04060e04061b 75
    0x44400c40140407c0303a58412006c14001e0031040360182c07140c010f409480c03000c200c00007401c40c2d4180c8250344c03081401d6581c000080341030390151028000f040b100d201203000d492003008a0a9103001d060000107070749541d1241039031010350001107a004a526140380c00d0a150300300f403c01d02000b00001d0542d40310f2400e5400248544a54000d0074911017002c912059110f1403004c286219920141c51114640c809050140a180c4d410720110340e00e00c5201004200c0d0b20340031094901868041c0c4403440440300ca603403190068040220194118801400389100d10660506810380c0b44603000e249642c00441d82146807107030111800c0d982d041c400c0390101004191115000c114520740c10000920180c0c0b12103074190302c20710441002800610460303104040c44041c0015490480b8450012103810307000e0188a01000b04e030444102c2101e0780244100d064140c002c4084903030201120f0152070301c0e0301c0c00d43c0000b0115203079a0044040b0078200420030007041f2207449070440440d0241c815a4810000f0800280 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 295538597 1250 295537347 295537349
    0xd1b1d0a0b0c01090f081e0a02060604021806190201150b040902180d0804091a1c03020709020f0d050108030702060d02130b0d200c0712141608010b01090b04 69
    0x20786001500d040550002c2d070012411541c800c01d8010740070a503050081d09178000120f290301096044e84000300f4034040000702e529520298000c0c100302c0e6100d10800000b5009242d20004402014540f103856544010061001c0984076007074a6010340007802c004c0c02c580e07501d03061003881c20780e400d41840800402e02c192400c841e944500541c2d00c6031840c50410440000d03504031034110007040d8880c02000300181c050000c0d5032041e4000c226240c00000c400b6540c41c00c1d90320140c1c12480f85ca074210708a0092100c50000300f03010740100e07820140c1e41c01001c0c040360b0040d01c5052400202244000100e10350b400741600400b0207000541c10002a9000502e083c4603400360751038120f0703000810350f000342d0325009120700a0140d507502945030b010000020016010140d502c00034081a1a0720a00c0c40e80200c0a85c0c0400706500014403206040102d224a40340c1c1e01581641d12008000600308003c1d010006030070b0100c52070f1048450646400b003114207442d18901d02e2410b10041c05c00034000a20080207582c = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 295539847 1250 295538597 295538609
    0x207050f1b060c010e07120b070206010f050907091e050114030f0c0c010f0c030c200628020a0306170d0509040b040f090c050a0b0c0d140d1b1d0a 64
    0x95031040f01c641150b004041c41da04100e0140510080000c030711b940d282c9441601402001c4410035076480b010200d8442600b40a009440d9603075050078021130519084040d4040350905110041980711000c404041d00e1180c9010200310181384248025680440040c0c4080104c50b800c6080d0b042c042100303c084c44004194900c0f4000208180c0c0f94035000750403200c00303040010300c2080035a00c0307030b00028007401304016080b000c0351001d49800e290b140c041c00343d0b03846000c0c1d41000d41080c2c2c869888070030328400682403120421060308283d2802454610040002241c00c1d00d00094180c604000340850b002c1d9041e01d888a0381102c196481041e801000f11103d41008071000a500d8410720002001040500c1c0c01c03250051420804104001c00581080142c44048400344801641c42a0304602481030f02c0208903240c001c1201424040d0003009214501d5019004060916104943c02c4044400c60124000d03c8440c1d452104d40850b00308035114080d50801e41c1c0280c004d0b840d03c0c0880e021500b184940 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 295541097 1250 295539847 295539859
    0x921010c0507080d05091c091401051305090a060e010807080d11030d180516180b011403040c05190501030507050405180c0c03040608040c0509271f0207050f1b 70
    0x5086c08906105151120044000312040201128002401e0500d103000e1b469080c281c1944504841d03000c0d109880d00a840402020100ca0400f000e00c0081d0300080d1107100715a031500e40115040d40c82d141c04501810080c0700800c0030070310304000189804404041030301400490340300310000000c0441102d1a004629201180280407903107a1203020800140180c01d03409038081e5410b003190805180c00c101d4410317211013090b44802801c414110b525085c100c81c082a213840d0f401010310700000c0038642c014050f541c4410300954440c08500140f00c04103e601151103c1e510600c0301e9070705403141507001001d9107005810182804003217114070403010a1041c0200541c00014042008942110003011100c001d80362500c2d0350394070181c1003060a907400c8030402004c002c0411750313041840d0340c90711402c0c1e86105100c5110f00345c6019044c01c5544260781c0741900a6080e1641110349501058403505120100143e0394500ca01701582031900300b05003103101d034200282e2150760000006040111310b0049a107 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 295542347 1250 295541097 295541101
    0xd1a13090827030f0f2505060a020d0311070b060d061e06030c05030105090601060810120b06091e0a110705011419020a050a11030921010c0507080d05 66
    0x1042c0201181044107881100c410b02d1680703140c0c1521000e0358010b4045410041014166549a0800300d80c805082d5224007994070044407104550407410091039400e210550700c500101d1030680c400c52050300075903c0503006500047d410b01c41d06801103001807496051003207983c1c0e01c8000b0007004e03240c944210320108070001401001c0d4804100c0c1800f5100d42c004118003903400d03401030300081c4002c0d500740341080702c0019181818010305210f5590800a02026070901c08240c1e911040a40000b580d89030f0b2150114600c0580b2040c0020b0600a0490207407901e080c00401c0b80e20b000c001c03c01035a0002100c1d12800107a100007003160011311500c404603c41a000a8246190141c0a00503250f5801c000100080801040c6180d0180c17240310070248007485402c000c081a84074048407040012001c02001010f43d1007041c01e501811007400550703117030002d4000043407140641003031540e65510800003210709119007403103900c030340400c141002400e154568840c05594001c6240c1a2500307615000 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 295543597 1250 295542347 295542353
    0x5060106110714030c0901081b0301050609040308040f0c0b0d05010b07030e011d0409060203040501240612060306050703151a0315060f0a02030307020c090108100903140705030d1a1309 81
    0x801e42c103005c0c3c03000c4d21841e6550f230358000c26550707800e103c4007940c410720b00b03401e1700b000c0c0d0b0606000703980c41090040c00d410310a4640f03640464038220700070802d40e00c070020b19584000049929803c0300041044a403010740310b1150481140132248180d100469044003009170600203508581907400f82482403c0c62201600d4042d16003080b00311500c4600d0b1b0140c03a00d0442c02c200700695002e140a0360140317008000c0d43ca422142030350141a086e840b5040c54202c070200f000498031600300c054a0380d800980110b01590780f5911002940c030259291070109884401030a142480b00046038002c140304111000c10114070700c081c00c200e04c0060465041004042c0072000c030707a01c541342140c51048511100b641c1c0e4054501000b03403290800c1e02d03110010301801b0609917162421203425810b03500a003000e8466900a800e0400040c502c2c0701d4218140320140084080d4010b007000a044c1541c02080071f5582e0784480042002101c4012595100385151103605500d0750701c45440d11701c480c0000b040c00280000342c0342 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 295544847 1250 295543597 295543603
    0x1b04020409060b0c060606040e01090b3d020102040b090111120c0d080a0203010b0d0203131e020102070e09060c0d06030c170c0306011a0711030d0302070506010611071403 75
    0x2421480d0710a081640000311024100300401c3c90340c070002e041e50444d88039a0304200942c802c40c4500fa514005103001400096115031101c800464020208001d02609000410409140780c041c680003401000b80034400701051042141c81c8080c503c02146841d04041d24038010f80a220b20150400c07080c882c0d03900c00040100185040300e002030034807540301c0c0448000180d0b1070f600c000c0c0e1080001c00b1500802c2982e46903000b0799059442e62841c080c01c1c41007040c4040c0c029000102944007203500900c0e130305c3c0891504511510084e19403640a103040c5013500029190049035072204042950503410008481d82c04200981c2203034121440a540d1440da0036407201801e641e400141c403140300e01e000061140152014610555141000e40c0c0c46041d01004250326514244651602c51240b22550140311074a80b00808040d40b140c0c5400c0e64400705140481e10b008854540c200100b507000a4003005d110f800c104c0d20303004110504e005644a40085800c540b6241140701d80080390781c90200d01c0b51a80e4040c = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 295546097 1250 295544847 295544849
    0x903081305031e090a120f080f0d06060f1b02030a0f030921021302090a03060b0a080609160807060905040c030624110a020105120606070f12080f091b040204 69
    0x40c800c0700410256100788802c0303030743c03240004070310800c5c0500c00024140e00b808080014990001b900305126603d91f19801d20360f520204d03490700f00c11002c00061240c0f5800f40308410103850140d90785c2e91520480203002c1c100000b1841113280201107542140c1c0142c1d03000a40007011688000318115440042c9805c3d20b0315031b42c40d04401d480790104a04034011020108465400750f000301c0e120f5480c1030101411b0300486c07003604011500001d14407018030200350741341c000741d03401c00b4003030880c01109540b1402141094800d44604245401c0030b5283e0000484000d0004080c12408001e40035070303440d2113805400034050348034103805240c880640e100e40b507000307030300c0304004104100c805010b084004442c62585468615400045581c0c1d6a0105680b4400102840e0140e4107071202d030310f40350380080201d000d410002d0009510407003c2000c4800110159150580c0f1481881010204c504a000142c02c441000b00b50148207042c2d0300c1001036110000a410b04d010040315139585102c440c050200740603110f6 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 295547347 1250 295546097 295546117
    0x402090102030f0706090506070906120b011808073006090201030b040e030a0f0906020a062708040e070e01050d0207020321040905090115032916080703090308130503 73
    0x800700d540424081150440071b4110321031803d03103c81d0b940c0d00505a41d440158014540001d00459483c00e400b181075001d01a803003014101003618088030385014480050b203800441c416002107008204d4081c00da030203080010200d604908203148200c4010420300c16048024090b01d03103400302002964001d40c41031100e200c000d0f10074044414410b54240c1c0d0b0b40c0c8a0456140010500004c0a0b1030034030600001003550907660151444e4041c0342c8a400180290901d201c601002c03517090009030704001c0c9140e04042d440383e400c0c15100d40c94501500000c20f0010002418080441c900d0055a0307400002c48500d9100d00c40016210000c41c001b0a1502d2000100e0000ca150104041c590305034403c80544201e03122440d09000a5842c86421401e03181d0140fa0300c088410b1141c401d01c000b401d00aa80c10034460b550b001034482140c100d55685964130145c03418601e02440d0046403031625407140c48a81d00010a0070144000d51041c4d0780146004002801c9071010b040d19000401000000d00c112022411 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 295548597 1250 295547347 295547377
    0xd02010818030d02030115030b030601060f1709010c09061e080c09120309030c010201060e1305031c063011040905030304060b0301051b0a0e1c120212090a05040209010203 75
    0x81d2083e5000003076000307015901006104400c02d5050030b01c00e000b04006010050082e01381a4601201030304d24812480c080f5092013120a03141c414034405041440c41a042800045090a205940a4250550380c2c0041d0304000c0c0305a034004900c41c81c030317460714030700c003043e15004805540d20780329501d4034025002c0c0705a00120901c0c6640410750000003030100041c080b03065542c5c42054900680c202c0b01c1c1132151140010303c86000409042049800c15440d60091080e2413511403005003a40f4845001600c85c0c1a6668888090103220000340101c011446112a0104aa019001ca580030303180610b82c020445a2803000140c5581c0b90364000d0702d410750b841000c1325101c3c00c242c60404041e0002c4c101d007038069881c000005040a0356141d00d04550b24603121428640350645108a41c0d48040c1440d568101a5141c441c0c01b409107a010b28800c918020b6807200d41c45400303040e0003800c05d03d000c14050800c0c6001c0c89840d10b1503880407441d1781100c908460060766840c6500050781140101403c0e020084 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 295549847 1250 295548597 295548607
    0x5040b1e0c07180c1202093120030402120c0a0f090c0c0b072a0b09010506041104090f0b060f040311040903090603050912270409020d0201081803 64
    0x400001c0401c2543d0040c0e07100c08090071610311080854540d803403004000362440040425821680d40109441e10000c1c01032075004014a0502e00240140d07003450403182c0aa0a86400307000030b51060850f15290200086141c1d010801661901e000250011303201e070246c0340349210050300400211a850102418401c4159500d50b00c050706915030740325122034541801c003c0c100e80f40c40b41e5003581d20b441d4000580841500c903a04102c860301403188046035000e0b08072000300b000310f100320071411415124031108556440c051668500351070011340000e0103281840c0c8140c48092108042d50241c4200710310004000c900700f0784000c007402c0803813016034121030001341ca104c050304044010030641c0c1c0200384240c0b842010605000885806000c05400103c04440a010a500c00e402c4a070300081c4000403134000b81c515159004041d4403e01d0130085241c40f00d081942c84414903079044e106240129404c0101d15000d402040b400c0b200214000d0411180100181c0221488140403250741c4603842142c1e160 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 295551097 1250 295549847 295549867
    0x42001020a02210f060a020d0f02040b0a0c0519060504050c0a211e1a0906010b0403120201021902011b08041709030343020a14031005100614070305040b1e 68
    0x235440345110214460908401d1590f01c00540201d0381103e4000a18516000203000211030880c500b490032501c0d4041c02d80d1349010703185000e00d130749041d50040e02e00050504051501c949040050250540144003980c010000d010040c07041c484000340590424491644520b4500c1880307030440300c008420f0b0f0400d40301e2018864503144415010000100301140b940701c000186590701c50900c100100044108805d000081c903140403145d07445510700001d401c126400b0720501403080d03090708400040c0c1d501d5070b00791201848640120303104589410403003c1820319440d000048100c0901d1003c55040c006001c4000380c804004031503003050748068482021005c202d43c42050413100c80e5038a8a110b20801030131030100c1550b80c10070b83c103034020416110645030450802c00b000c43d8660855160042045051904100e800341c02c2c441e0008503001a031407800c092024002503440d420380c00703070150144440d0700040c1e000401c80c1c01342c0c0d482514207611016207804600c0d400d45214606c0c00b01d4400400d2031504 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 295552347 1250 295551097 295551101
    0x1081f17070e09070803031f0b0d09020915060304060e0c0a0b030a0b0913020d060f110c070b0708070b1506071a06060c0d050906070b042001020a02210f060a 69
    0x1555004042d00744280c6400c400e0590380c090074081c000c1560410004a40c007844208003030b0369810030640a000d82240e848500200c03540001c6401010315441c0d007041d00440c54840c442c10362210f15081c513604030380e0b0700d02c0100c2e141d404000c00040c051a52080705258145040280024140c4010001e0036030f1625040380d100d030364200350741242000d07040030980385035032511f040c6261040180804551844181e43c0801814440c5a541543d5180d910741003c0084c074a00d0080f1f012440d0700a80301c90352032600000b000d14003000e40d0b0000080030010b000c80d1000400b13880c01c071141700760048003405042d20b91142a521490b01d4030700072a8812400982d03c0100500081080c1e0380039060100301070170ba6518020b00c052842007804081c170b1030700286a01e0400c0c1d40141c000e8290084041c0c080c6080120640d1a40c520400942c2c0a449001c0c241c0c07950207101d01c0210b80c003a1014400c0c03025140000c43c5601040801e8012f018960702d04011000c1d4080032041040300141c08107542d0121b500300e007012515040 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 295553597 1250 295552347 295552349
    0x1e0b040f050106021f0c050706020a3b0a0501091502011803030b180c1e1e0319020412030806030a0506160f1404050913080403030201020310080c01081f1707 69
    0x304161040c0c5c17010f0320b440303064031070110000320355210580703071007042da55110007035100000d21402e0005000840c400f012609a48043c50031845240e9030b000300712103a1406071010389495003403003078824070000d018990744400500216030054000441da01c41c143c0d42070740500011304c807031140c51041002c801c0505900d600100e40c0d15130151105032481d2911740f02c00451000454030549074140811065403c21401d1252000709080c400c0c103a030030030030400805202c15070111407010f908c05002c400e00c9501d100011625990321092103045181904d000040c00e00080a400b0142c24050030100150082e2014003019085644c00001e862003071400404140d1000f5002e0042400240c2d49003540c0300c2c860158442c80b075501e940300300c9242032526013030410822240040ca0006482081d0103403000003601100500003462180c0c00141e103070302e0448403070001950284d1043d074403980200080a05a40c0180c00c4a8010040c2c080c1d4003089910394080d842282000d5010401c40c04014030420300840c0f000c15100 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 295554847 1250 295553597 295553623
    0x3090e010e07020c0112270507121106070204020d091a01060e0307050d03020a0b01142b06050c0906040b04090b040c09060c020109090c1d01031e0b040f05010602 71
    0x50016601c0d00d0101c15040340440744440541e0055121880b15070055043e40800100304001090b031113009110081c541c1402d016039a02c21405914030010401f05000c2c0c0b10245c08030b82d0626804400d1502c601031300709410081a40075000c00925003065495170380481c2e010388480748003072200c10300910b44444140e07038162010310b0600d070042c00030412510481c0341e0f514003040103006000d02c86c200410406520040e030380443c2944202d11501001518403002c090003003114a01041c29140600184000c00303107400e5800000e080070140e50300d07401ca8000d0620702c0d500e8120714000b549680d000b40c042c00901c9a1284194081008980000c04a24900090007a505203e0f428006a5003030000d100964090604400205a00e20360a0040500c100c0b1040c0c00c09005141c40c407030302f50344c0d0966030007141c40000400000a49000850031072299a5201070500c0000f880e081007416002048517191400c0a0b42c0c038258141ca50b54260300079580c0d5041091002c1421008124a5a441c4400b079603800300c0d44216 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 295556097 1250 295554847 295554869
    0x14030d020c060d050c07020907320a08100512070504060b030603030405100509040204060903030e031204180b12010c09080c060d02030604151401030e01050c0d0c0c08070309 76
    0x10150903803011500894980002c0c150505100b000100c50010302401400c07804034440622818000d80d5584440c0c5000301c4e40c03520313610300d0301007035404c01c08100c043c0d00d5618034403280c2051440c070240c04090407991044020300c2d2115042d101c070050100d241d05181e0000707501246030010ba17442000081a14000c0300d07401c81d41004038681c1e41d00d030341180d03003c116401a0300d034005002c1040141083d02d48030403040c80c7d51806038038042450000500321f80040d0080000200030f640b003031041640000d070135840c401c000c400030041c011030917440d200c3c24812801190000310340039090750352890300c47d0010342e4074000003020100ba1403890801ca0303001700095190080002c491040c0011206804034099006c0500a008546421081c00444010b544007400b0700742c03c0fa41c1c0310090024107250000d103c01a0184290a40703082c182000010140d460103640000c55902d010103100301590b2002c202c441590003400045024044580e003543c1d07410400702c000d0100040081d40d00308050b4410750700002d8441c00c101d0 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 295557347 1250 295556097 295556113
    0x306050a0e07081b0a1a13080309100e0315090f0d1704020103090206040503030d1e0c20150108030d150302030a030804060b1002030c0d02010506130203070e0a1403 72
    0x840e507120407500c41d10001c1d0300248451075200030040d60448480201500e1602e0a91b950070f41203001c0c0551030f0965240b8500807400d4038000698900d07880080000350015814003d520000591340c000c20100e80c0300b44140c580d0346099540301800030b4400f1184001c0108840d151105007551500c042c2c0803418a1401001d4030041a1409030500071103071110030100003960b503a164010b5000302400c40c4243e910007410301c80083d05940030002006080350100d00420010038807800f440d10b01e80184c0c1d140302007a0030104070b071040c981d02501600c100407070f03880708103003031204804103500b410480c4018441680292001040c190f030000000c00d030b1100603120400c10190b112082c01d60801603800300a5068102030700c0440442d1080d000b1a4009004031400152040740c400001c2c550594400720f24056000800d640000d44828401900d41000da070000744003030f1501000085442c089007825415495020001c40c68135403241810b2440080c0103000f0140164a8088540301d0000341c006c0c06200b4810001 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 295558597 1250 295557347 295557371
    0xd0504091506020709020d060302060408010b0102060612120d0209040203011706281a060a020109020103150305060103080c0f06070806311e02040905010e0a051506030618010306050a 80
    0x7262404940d0642d014280303903030501d040c502c040d510021281c80095158000440503a48800040000b4a201000099601864400682441002031405204245034007010381d000c400401da82070205154080180d9510382c2c806088024024050390f05c1d0410b101100100b10a2155203441003a0064542210345507030ba0701600c280940c221500c007c680410030510308025a02c1c0303170020855403c1055014030420000c00201e141c541006503003c0050703460720f04410555070144242241d000d40443c0c441e9040307003540c843c0b540e00c0701d06110051020b680003480a02e00c003c180102c008850a042c140c0d51103061500000305580d40a50303007640b1031685503611800d039044052402c0414406a043d9009182d10a1a15402041c80717148002c3c580200b0a502c001c0b11510b440200003402c0090400902541811400c00300e0010040c1000081442c0400740040406500c00040341c00e03034212401b039a25601c1c08080b480b001c5e0b00c40314100c140e03000d0708001f1040010540046210b10307490401044080c80717030a = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 295559847 1250 295558597 295558631
    0x11b0b04020916090521010c0e040c0306050609150c06040c030204110702010e1c0c0b030412050c0a0f020406030b070f030b03011e051015170a1e09140d050409 70
    0x14003c0c01082da244010045c908201c0262500c1d140018540350a420a089015081d994002480c50000d400d41d0701002840c40c141c071522542116610342000b0300b5040070302040c01c91203040206d80c464120300001c1004100030030304480e0b910302c561082d1113090a1600d00400c03024890300080340f00314241100030030990484000c3e122816016900d034440b2409920034405000c240068074a100c1811598610100b11840001e01c01000c903a1710442d80d034902400c00b80c00c807900c06010712013046000c000e20550040c002600000090300514852150080c9200003801041c9940c4000c2c40748482c007041002c04d1ba00070298018413026510b0500c401c060000402d8222010350310750017415072400851111030000c9070312490f44000c894001c104925141c0d0410203012401d070542c0c8001485200c10041280c1648441c1c03038100344c0b05502400309401d184104840040c2081c2c200300081d90f1070000c1000c0c00307103c6030000c2403080c040007913400b60043c0750310051007944603005401e5440d08140381400510081 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 295561097 1250 295559847 295559881
    0x2030702010506061c0b0f03070f05032415061c0f060b040510030f021605070314010513021e090109020c060f040803070c0303060803030a060e0703050420011b0b040209 74
    0x246401d504900d00c05c1c0d15400034280b103e00c1c2034228044000254003a02e0801900740038108588969280605c0c00082500c1d11448118410300480e41140303064100d00240d1000b600040030807800c2070744015940c0454401c1c0202150b0500050410000701c204003c2a408103100d00e002840501c00300703881e4040c0c0180341c401c500ca21a004501c0c15002c2148910a611a81390040c0250b005464002d801102c0d40c0d03d4103d030b0405581075001071004008011201c0e5000598000c00c1c002403000d0b1070b0401480c1225020340c1e9000c7d0050146903141240140c00449144507240300520704109942c468808200075000740402c261107116100c00718414500c547c400360b10030f55104072042e10b1540d4044007204d5241c0c882200720141a1030f00e1010882900500245119512501001400514144111816400c0030b00784605062500c03041c40042001980f2100c03030040c40b05601d071594000c400048a41040880c801d441450008480c2c20410a80c404036034000c034001c0b6105480e035101d69006000c2c149038 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 295562347 1250 295561097 295561117
    0x8010f090b130215030403050406020f19030e0d050607030b18190b1306140906040506131d01020c0d020607051c0b060702120709050112020a09050c09130203070201050606 75
    0x20440015151455804103514180d1010308404e070b091500d2281000942c02c1910118003081d00450240a030300c2d070402842890301c03200c4004190403401401c41942581c4441c0d07001e020024202c200381c038551240d220312286290f110f0700702c60540c5400140107004002c0c526000b0b20035031094450b480554284a2950300410009200302d4610701c007962000c00410007003810303980200301c20302e05c001855528881d940080485a40c507100540c00034081051100c00248814031139480e0209000c9644c50f03c400300c0c1400c1041041c005038800014020101904013038a010f0360360f60001a11546140c004511820308a142c0e40881e0142d85070341005035883e000b08902011144071055100004042540041c890740320013030f10041c80c04010703802090b0f06c814040e01c40d180ca5805240d04204003011403041da4010324105128128903883c560004d42a20400c0c444c206415407610003007400d0220480072965081001042c015000041000d503501079081121514095482d00d40050442d0514500719042408 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 295563597 1250 295562347 295562363
    0xd0b0117121c0603120c06050a050c0d091103070b070611090924040203011e0b04120803091203101a0f070201030c090b16111c1e060f02030108010f09 66
    0x5900b1420a00051050180c40055458100010100d4010040c060703507502d20340ea550381400e11318101402620300c082c11624a6501d090100305442103008140c507416038682d84080380d03004181c00c002684144c0310042d1a40360180c4580010030304421001844501e2192900380000c5018894541e103038080e0046a07074002d003040b00041c8000348100000d54116502020a0b511410706101082c226003090300100c0e80614030800341c4007103c0c00c031000640140480c1410f0342c6041d00308a9586103045801c41c2c002c009100c04000724051403000c5c02550000c0c0b500c2031181d0303168a4440c030550b02c084054455201d10742ca00607410141000400c01301d80d0400036007074101d441c1c0001c5a004600500400408404202e5100c00124264048000074000300c44403911415868a03d03007014091204900380051240803018950007007042601840c02d03010703400a92103031000e002103540d0034005c4200c00300181418980f401d01038079007074164041d60580f070002c0d00070840052076592000440c6e0050001400d011 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 295564847 1250 295563597 295563607
    0x80f010e0c03044701031214070203100b100804170c010213080706030c0e0904021903080c0607110609060f0606070f08040812040f05010f0507020d0b011712 69
    0x580705401980c0162040700200c280c003001000030103031291000d240c0841d00410f01c0d642c240d0f03400402d2030081101007210303845409516540d105521041e14051071800e0214460101681042302c3c010340380e02d107030003400b0f480c0781011904418008012510001d8400d1901001c00c810f42881380310428401c55200308c0e480b2078001c0c0110580c00130b4000802202e03040d034007041707205410000459207a004011400007481e0711820640c02400b5101c044444c50704006420800445550360400110f4001d501aa11003a1a107151034000e9100500c0348c1000e091002e000070b4a5a14090004080d48592565a1401c485810300c811040d1110025501c0301810b5001c1c1c0d022034614503074416641d03003200000785981c2c64601680e8072011103800201042c0e500103004076042000010130b00010540013412940c00d03142c6400c02c03c102081100394002c1604100710030411740502c0e40240304441b4602c0c0c0050a5600715100e40c0341c5045600c0c0300b406544103907c0c44d02c01c5046400c83c002541d00c0c00c143d000c11010700308 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 295566097 1250 295564847 295564861
    0x20f04030b010b030717180d21020906030a0c020106050603191a0102151018150b0a020312040303091e0c08010b0102150603030405040903050a03050903090d030807030e030309030a080f010e 83
    0x5000050105142c010b0340b031f115006081d404106440540c030380341e115101d5038101c4a01e4040c803207400c05074a00c181d43c0100811407403039584404807513105000d144002410390020200300d005020ba50030203038120000100b1b00c4007500094212401c0007044010a212480c410500c0103080540b4500c290301603400f140c0c1040b8081602100b0907803110030a0811075080d0342d030384542580c40d080d01441601c0e4503a580740c01125400390482d82000b802c000b50710145040807900000355240308035180444044154130214041603c00e40003003844540055640101e040740900c8082e11404030700e801c0b5496543c8030b00000390004180108000030720141c0280040c034031044070401e48224002c18041d0700d4002044081070680e107a2088080c03d0b402555115100e829002000c1d046a0028020402d16401881006110795400312811811903251a2460460b25454410703805040744000b41c103102e00012041050201c00007000e80420700b816965080780792079207050445c1555082c0139500d46c03c0011400a410 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 295567347 1250 295566097 295566137
    0x10c030c0c03052d0d05100602070303080405070801050c09130c05190309020603040f120c05030409020d090507080f010b01112e092001080f01091806020f04030b010b0307 75
    0x752118005110091a407483c0c03d02031360000d000300070061011a8100b00945240315240c0c2c40b84201c1181016035080c80380107580c03460544001410010000002010018203001a40003000b26000901c0300f0709080002604d1030308a0340741640501100c4280c5941394146000d0a01090070a440b010315050341c00b2450945480315203454818103031181540c00c0141c441c50f0040d07104901911044100007018a400038588000c4801e0008001c90162040007082c0044111b13011203130403010051351130005403000c5016003010040503209010b038031b000150110010600240c282c10356802002844070141c015200000b1084944d01d640d88810311004031209140307541d202c44040350314802c98881c0c4100920081d01c3d6148003c43d03100002c0c821402d41400d40c40c2c43c0e002103200c00d00f00703542d20703207445c0c5020491020141300700820141c980c09010301003907409917010440b940048042d59124500038031124681e000b031000301c070000244400001c0d612044800d60303004034031564650451441c001083c03d0 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 295568597 1250 295567347 295567357
    0xd0c060e01090219090b0907080703020d1b0809060106020304080712030c0b13020f04050405030304022e020615040905060705091309050f06160207050112090b1305010c030c0c0305 79
    0x9aa50b607240604005a0b840c411034101d90740c09844141001c5040407941d6096407840c2034040d0040c1107810900011542118071294000014540146c03204c19503015a0050400100000b8144103030341da81c5030201c0c3e400010790344640e084400319034031a40e0b1240102c0c0d692145209030b03030998204d120117000c0c1c14013440c0140003650182c640380c07060903210b4031071100021050b980547c05998414443c030131410400444190494120340c20000e41c075168840d1030302e0788001031000307228401010308030f00602d803038650303000004216a020a0f89442c12000103940d901054901529032000039181c04110315160003031030000e5501001621940e158000705580c55080390b956242d000140f0024400c0c00ca90f64441c0c0329080b80558020100700e0f160a1801c0c0c201000504441c3c030350000c1d1411151000e0300090010200d84080ca01940c42c642108a604014a00e040c0003c10012000742405904418404074406542c041c8000300320007c103082054045840556032480850b481881c94404a03000c1c2000d06 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 295569847 1250 295568597 295568621
    0x2712060608010c1e080403120b13050a090204060b042d080a0c03030e04111605160e090708010504030e010c03020a050a060c090902070f1112010c0e040c020d0c06 71
    0x10a4654807501c2032030039200d80100c00800140c84d4100319459004182a450701c5949900340201c0a00b407980b0014141d2a074003042012803901c5d015005110303181e01d43c20000d0b83c4650401080350741003c00e01d0304064401114168800e6003080d60202c1c02504501c211170840c0c2d8440e85c0290580c070b01c1c2800fa072144c41c0f00031614050318811440040d00160902c21081700703910a40c440c62025042d8030700501145400e80c400e900880c0380101c5007002105007001c49100400001041c0001c0381286805480c0c81010720035107020042c098000621000300e004032902450b13a14080d9000c5545a044071422100c0072900075000543d01c95080400f94060103084540307500070b205171080c5080315141e03240303007a0f0070000840303485940b00d81c130594150b403000049003d800004019494510039840360360400c8506000a80a040310203080e510a9813501d00f04803003140110001d110120010f4405400d55000799040303402030b03050000300c21026201140001c4404503e840e2900c0c000ba590f110500102000e82200d = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 295571097 1250 295569847 295569851
    0x901140405040f08070b1905160e0406030212010b091f05210105090c0306060f0105030a02030c040302130204150c050d180803120109230c030606090d12271206 70
    0x2a0340401c00c114010000745004141b0350045007001c4800e07079004005140006240c6152000780305034066040c5011100a91514080d0101821100061b0080969500003075005a41c055150200303141908074440705e20f02140c5030b5100d96a004142083c00858070229005d13054000c0c000e014524001462102c1a0151030500d4001030355000301c1400c40c0c80035614204568042e440e103da00d031404200295100e44141c40b86003c1141820000e0f03c94000038020040c96600071000900b2207460074151801560018003001200d40180070b518002d5000d07001e54810140d1125140c08139602902080d161280d000005020790000d001c1c08940020400c8121419200c0700540010302c039030200701030011060140c06804140d450400920100c803000a043c0300c00c108035440000c40b00c01c10200e0380e948102050b08076540c07940c0c2c0c0000651188903c0c010a0343c088112200403040c0114440d024088580684038010180c070b482a2030b1401d020000a000b000107046441031014044507118404c002e0310400380 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 295572347 1250 295571097 295571123
    0xf0c010216051501060e1809010e070b03040b010f0e060105030601030b0a080708060105030706020d140408070603020403020f0f03100f02160b070f031a010f2714090114040504 77
    0x40c504186070808816140380d884074824400d0403050f010464010112030500c1d440618001c804600f0b041e0038205001c09110aa02c00190100c5080d001050140a244c0135111010344918401c16160411303601911000800b1001041608588803880c0c140c503c0360f820313072507180c0c1d9003001180e0a0b172008210504164645510458a444440e51080a0900c41c1c01a21007281000f00f010302c1c3c114140d1286210ba80040c02c104aa25008640b103400e2003007602d003681000c004a48110000c0c0314560282d03c0c144149040050042d9041d8060002da030310031580185050300c2001000482d11084860750b0380b640150f511501c004c102035114101c42e80b100700001d420211036a541050284403400184c07a030750841c0081200c00f5600c05401101c00f851420200a400c4418500d8800c130140d07440550b0501c103201c610f032221140190f1512551030b0519025003400c1584905001701c0540078451120401c04181e5030341d096245c400c821701e068580c4198100c3d8018085010403001e0400540260b0700c0c40380b5455 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 295573597 1250 295572347 295572367
    0x9030507201201090b1f0305070f0e010b0705060a0b010c150b030f060f0c0901030f020a0e10030605030325020d111807020c0907030b040906060509060a0b0f0c0102 72
    0x31050008881c560358908003074101440041c01c84a60316806991404c8045000601c01028107074002080340c900c114030b034102910b00e41410300150030150061140701000500c1c511400b240900392000c40700304042d5030740d9500c150500ca024401c00104a50132800c009503940c0b01552005214510501d01891f140c40a62036600c4040c2c03101c0043e42d003003611001019800d0404001c008003102404005080901d030401c505100341c900a011f01015003000903500400703a2203078218800e40304624038210340d1190318140142c52420407081681c09510f844a8410203d8002d11512040301c0d0080c0145242030f509640f541c55030510360804144a003c3e800440e00940c40b2038140b021114415400000045250401c2010f01001141580c6800c0c13100c4041091f6140c0c081074088108905540c640d8040d2100c030820f81c06400384c0b00e005504186010780d21014040c060308640b044400036104031166480d0b01003800355601f00c60141c141282c41c00c1024251894494000701036110783d8100040c10026110 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 295574847 1250 295573597 295573613
    0x8040323070b16180e1f1410140919080f0d111617070509130b010803131a09060d0501050f09070807050c0c060403080403030215060607020409030507 66
    0xd8416200081280e0801c007030703203030f1030001c0c8210540c85040a2500314440900116000b445000c0c84449010107000300707812645600981050444401c00c0c1e440564460783c034800b010140c0107002d8481c410a01c050f001c071034014581100d9018501d01c5c0c9134139044515007880b1442000d800e01c0007a40c0c800540c00181c02c1c00510030310f155102082c0150440e07000c400e4000705101c048184ca46e10540061030316517445042c4480c0030088070a54a161000c0c9100051100d0400e4495402541c0044000040142000c3c2c00600c18540c54840c1e03078100b915913250305016070303617000350444d00380040c40c58001070041a488020180c0180c02002e549490501c50b60f0200300c164100300f481070000764031100144030381d1a080d5443c0d82502801e562043c0c1510344048020030703c600c041c2011050001c0028640740482040c082c0d5582100080c1c20141e0302c540d030b840c20500030741c41848290011f0141441040e441000d0001ca01e00484004081c1d9040c8000c1d5020030004190540b01181030020400050000400710 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 295576097 1250 295574847 295574857
    0xa050f01140102030c1605011d030a122d1419050c0f070602061005041a01030e0106030f2d03020d141b010603030807020d050403260705060403021c08040323 69
    0x3500440c406c3e689800005414500b0403241c40d508580f00d08010305c3e0603100000d14440054221901c1000711403142c00907640d40d00c64050301c0300c1841800782c1c0c84014042e40c1200780040b8480baa03580030400d4034000d40e240d4a0243c501110300108030f503080b03104980d05c185d001d0866200c20105803296410410642403620309680c1c480c0303025070040d80802100744400340960b401810240e074240700b0b00307100550140d0b4403540c1b142024149580c03043c0010282d2400d40c8450702039030340044040c6480f056030801444422290001d01402c203e03a0760074581c00c001c40b1104810f103a42c141c004040d414030345201a18440800340d0001403014007400040c0c1e070440603240c400300c10f03400300c00001a29070450500414880c2c008000c00d06560140c0318405819601504032402c581d0000059031400c040003910001d17601d000c0c001c154065001084032028002e0200b60306004d14800d13002c41e040c01113100c40302541622815200c00102c0e1504001401007400f0303214030450560b00000c0c94202500e0140100055000 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 295577347 1250 295576097 295576123
    0xe0901091a1206070806010309110d1104181b05010801150512011d0702010204050f0120030703090e011208120402030a02030607020a06060b16031202120a140a050f01140102030c 78
    0x50f400c0c03250b0a50007140305030300002c0038079040c881480180ca03055098001e00010f0b90023a00c00c481c103141800142520540c40c1c9000a2050003005c000c000e584062a20812086c1c400d500d00d007850f141107211181c204012100c0c180c54640c00d076883c200f142d1400c0400003551030203010003040744218103114a45003038081d00120643c94604e40e840303803013080b100900070460780c10340e0f20421040c05140d503083c40341c1003698000d00e0311b0014182c06200320106002104403070510ba100109040003015005030180c41500e614002d280c4071aa6204bd404040900f0751304040c00220702000181482080c045159900a0026049500c10908ae1b800f0929080003100c000340160080e002360f408218081c01018000c10300020414248050f000704038405c49107a0300b0003010f06c503030380d080701032400c2894058030070b0340080d4061506a460b2210426000d41580900045e91001c1800010721a00580c0f1800340112159590b08440703078201500620b0350104c813001541035200c00d02c00310840200400c0161080702c8 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 295578597 1250 295577347 295577353
    0x2091c0c03060c0c1101031406060c03040b0d1d01060f06080c07020d03120b04060b0a0c0c120c170102070b0612120d0b0405010608040302030708090103020415020a02010207060e0901091a12 83
    0x200350a001e0703017100002030702504250510700d0350108501c0ca4810342e0341200c4210380480c1e07122b280a420a01e1441664094820f020000c41c4441c4403440c2c682c441c40103c0c0740c0b5503405c051149801d40c510308071f0300c403409441054600392609101e40b034862002c466110500c8545a03107040c449400013504000d011504800140e041d5280304410a2140075488070504169000c3c045d107070074206800014081c0055060810030b150040c0c20600a6810911000f41120000703141c0f0003060742810300050410380580444403500b1541d20003040341c14070031076651507000000c2c100c06032179200400034030800c0514a001a445007149400c0044102c1d00149242c42245400160b84007446c000e2005442050b1702050501a09130b0800006c0b85d008811110f405500100c819502c1c2210300040e0001d0045401040070341004e41408400190001961075032030b4000d800315043d4550300c10048451500e81035040c0d400060b1400100b2010f481d60f0042d41c4510311009040e12008004800700d41c521895800c01c0450358 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 295579847 1250 295578597 295578617
    0x708070e0924040c0c020d020d0b15191203030b060903030a08041704060f0c0f0804080312060a050f1201090f0b1518041b0306150602060a02091c0c03060c 68
    0x404000b03a6140400c002d9900b40300d04a6900d00c06400180d0f045030203405074102c1c04c000402c40da2280b1035a880f1551003031030300c0c2c003508100d8401741c80420320514441c0103c1d02c4030b01254404202c1c0307540703104845100051001c40041a50220003401829000d6904040f0611041c08903540c01d2001c1c00e44800c166549825a2805090150200e0500e0710300080c0385804010510900707070703c88042c0b56108601e06007050041030b0340c541840004807246002e4901c0c60302090102d41b0a002100901c0f4140304d6000341c1d0710b29111a810064800e200744140c541c001680301482a00381000703039400042841c082e00000b45029135459220030b118030281c0880d0b2216171201009500c0075110a080001c83c002d444030125a10702e4601c0b840d40e80d0011740b000c1d15920806410740078510541070160042d662041090102c1c010b00741c2204040300d01402080007500801000400b0f10a5034401e07200c10140c000d015091a0034100d45908144078800b400340c0342c0e00100900840490620702071000b11040585e41e0040322 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 295581097 1250 295579847 295579891
    0x150e062b0e0609010902040f06060906110309091501121e0e1f090c0602031305040f09050d05040609050f0303040303111e030301030605060d0b010b0d0902030f0a0b090607080708070e09 81
    0x71011040c540c1c80143c0b500205106032baa11201290a495090801104000b4032112180c503501030109142d501001240801021760b0841940d028224000e80340c2c02c6400d2500e25885054818500c0301c0111250072001e06031012559070030140a0f5602c140075203691082008081071121640780204003142d0720b800e0f125003005a054140001404070703202442c00c104441d100c0000c072160503c9a40c1c422901c1c1c030300883c00d5000e81e601240500e60300c482141c2807910f007020045d11340d82240c820200403e031080c80001d5a4200704c1424036150034024083c52504d800c0d99803d981100d000400d0000b94880c3c0d00c0301440841424691381680000f0178000c6480b589103142c004280d440040507240140c1c880c01c00c3d0800114144000c17130541d02040880b80e2211440c45400e4020801100040d500d44120b9251520000d404211086410300507503c8981ea940c03a444c8003581e81a081d2404d0000594410000300c5c1305204103466a0003480b645410b140c20740ba003900191400a00396040c420085080c0314030100 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 295582347 1250 295581097 295581101
    0xc061b1106100302010c0c09020a17070c030c0602030907080d02030705100905100c140409091a0601020a1205070b0c0319360c150e062b0e060901090204 67
    0x40d0044140140120301c0c0c038038007007010540301d480000e040c443c220401c6010040c05158403001790084c1c04045440d00301714a40202a183c070740d00703400d01d0b0500310310100d050b0501c2503000c40340c07040d09038603a640740d54103541c0c454009504c0200104840c0c00b07404808141914280301340007500500754021078543c0041c1c01c06038141018001001c1c101850f1940100c001600170460074134081a40c10300042496022000399140c603001080e01607d1100003801080104803640100c84190103103040704c6142414020384c10000b01d0644002e405640001702000c0042c05001600030b901c6110300e8440d040603125540c0c420500019a0314914840003c020040303881e8540c00c501c0c3c5440b451039810301c460707040a204d45c010345215403240c0c03100081822203800e0406101940f105195800303c29410200e51742c005203e0b0030000e500340c210014284241841481c90b000e8203480800c0748503004c502d01c104100f90100103040c81202548109500da03046800c0c0c0039003c0c420307503202d4040c190001c505403865104200c2 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 295583597 1250 295582347 295582367
    0x30807050705031c030e120301080f0105090303040c0e040f0f061407210b010504120620040e060d050a060504060b01090f0e06010f051306090302090a050403080c0a0c061b 75
    0x8041e41c403158006003404a09550b00752628540d040014080b486c0744600781c100444000b1300c240c40711000000254900c00020000d900d400f400c0300800054480301007003501da1000b41c1e0043c0807150360721010300c5081034440359903401c2441003006400038902a40c13422801200c070841991001c2e51442c0f800b114402c4009059031102c800c3c6007a54141d0303161880110078081091460030160f07074802e455541640944211000792058806040c001c01d11884e00d8000382207500100344401101c807480b0404048007005540c1902e20f2640004116955801404401544c824041d00c5034411604080f01040c0c1605c1218003844c0102ea000c00d84e21400c0c030000d00030785030650050000c032030079240402042110045581d0003040c00d191410a002c0302c0a0121039501555150704019241e100000554a80202040302101d00c20707126541283d0300c075502c50045460440d800380c04614010001b0341d00e12024401445116101d0a20314000038454580c0b00481d000601283c1c107190089034000c2d01d05401c8143d400c = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 295584847 1250 295583597 295583599
    0x1e0f0e0402090903160809310c110d0f0e061c1107020918150a050601090b04140d02040e1203011403010b031903090b030f040606170304030b1906030807050705 70
    0x5845c00b00341d5071540148100580000c1c2607400082030803102950380606406001c01088502000800c21400703401e00202d20400800100b8a403e04820035140100d01b0591030f9500000600b480210702001501d44850b5041440200011150001c401d561201c0c00303855100c182021955455000060341001c54404c1c0c6504282d1003024480d900c0140e40e4040010313480000200c01010100c2e04110301803500b803590154000759088501003001c107001035400540714038026a240340d241555040414114402d43c040d003241c104200000750800d08204085100080c4080c0002680e44180300e566400c1a141007040e01c40407a000004020b040e0340c403000b481420302c04070001c00c00081d40c4000241d4a101141590b100311071a403001d0340071315016036012001001301c00030681d81d0b0700c2d015166400d00401200d040301c3c443c1c6030900103e4103944e201b40b01e0554a6091000f03620305821600c400c0b003540001844400f814071202444001c81259010b082c004500c140c2440e070301e80001c2d04c0c2103800d0a0403030f0001 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 295586097 1250 295584847 295584853
    0xa0f1811012c0d12050703080610081f0510030209011d030312071e090501080f0405030406031509060305150109200d0e0f030d0608070f1e0f0e04020909 67
    0x2d0140007451604004640800101c0c2521403800301d008980210101c07440603110b0032441420b2048150080020101181310b80d491840343d64801080056241200701854005140540020402c1c4007441c040006004074800e241459030781c0f41c0008103001c03070751034070040004d0f00400c0101d1759580003801000200440c4060b0f40741c0c010383c640803030740e20300135540c82d0803405801c0750100301354a0003000c0d80d0b683c0400740c0c08901141f0302d00001c064200743c0f40b0301c50540090100c80004a58680c0d20b00c0d100d0003a40c4c803201940c90140340800480140030a143c040d04002002e420000d561310f02c07480740e1002584100d02a00d14904181030711980c480e0140c0c400c0d050141170260600c1c0c401424070103901c104290341700b0b1a80310209010f03542c0050080c1c07074a04c403941c4500c6844040c0d1280c00001340007034400c10a000c0c0035543c2c1741c108075621101f00348a0711800c0d0074480c000384070104d19110340c4211640b151303c0d11501d2964628200e042c455560344080e50004420f0144402d40c00c000b80032583c808501001 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 295587347 1250 295586097 295586117
    0x1506060212030c070605071403010b04240801030311070b0d32010e100306090609061a010c080903010e03031003031d0913150c03050609010519030b0a0f181101 70
    0x103d50b520b02c2039400040030542c3e07401c00100000c2c003d62502114010303281a490f100c1d038440201041641c014010461024019004041c1c01403a850202c60b0441403641d4001069113996002d41d0001521040fa07441c601503030001203810707544030015015010b0400008611081c140464070701d0800315808100050303000c3c00b81152015410ba003e51304555601d1b20420140e601c00100154422680c1c0009001a050039043c4044c840560401c0c0b801a0003540d081250384a26800c50800550b900102808140c1030268a008510001d010300b0272200302400110301e01881058150442c0d00c111080c00701d07040c081d5000e000f030652020307400024800d034010070a00d0341540000545844002010316042d400c9203125201000001ca159160f000100c4005120781000c0700e802a026202c103d510f18081c5803010000100c6180200e944120b04810350103184013541551500f0f00c07a80307401891300401544841c00390b984a616441282a00c00002d124000d4403151468000f62014603100c0c001c1c104955541 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 295588597 1250 295587347 295587361
    0x20a02090103030f120c050306010906030b0d0206030a020c0307120e06030c0d150504051303030506090606190504030b01032114031f050307170706020318120a150606021203 76
    0x400c1505603501428403d4030280354050494190b03100d9031405495506107405038800a4114002d94042e840988407616082c4c4c6611044049806015215500001d455034207805400e110009540201c5440805450880850340c614615888610103c13050f000c020a440c0f10b0560061208080510803505585982403e80b09d054907030003113004500e40301d5a1a648800c10301082e0310840002c041c00f03001030140345000c0720410820a8414000c1c3d010038180000986a490004082482500014115414030002c01d40b0b0740524901424410705020702000048042202c1504442c0258820104202c0e021015a80d1400c0b104011a101c0140303c181000b500800c44610284c0c4c0d0b1080c025040380c0d0900606060b0070314002c2c40e55020b180c144c001c092020401d6040c503034490101c05a00c070112151140d0790402281e480c07089a50705106800c0c142d40c2a81030317142960400402021480071164228000c3d00d0300951101da810302d403181141e0b1104200807071030701844400d10892503d0031907411890999 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 295589847 1250 295588597 295588609
    0x40e0901020f1b0f0703060b04060b0c060a1e05010b040302150901020706050c07030c1205012a03020904091401050402100f12020d0e0a06090b24090402150a120c020a02 74
    0x52440032294681040040c801d00400624130700700c070040c0c00c4035061507603410200c4c010081540300b42d009504011021442015060440f40607000d41030041403d5503070084503000500000c8643c001004440902c01c3e2030401c03034001c89000c0d02100d00207540d01c81c55481081001c0058070110840c0800600071480540e801283c40c03402c5611f5814016500c0150039030f094104111904000d1011407101700116402540c172503a0103036148140020001003102561a00b145210809c1030240e134440407030fa03c1842442072300545031540010704082424191642c1d500800c10380010424035070b80d900d00c00c010540c68042c00f02c5900f00d0700c0341000b03c0d806241c400020002200e00c0d59170101c2940004070740380c2e41231440e07000c030f0044c440c00c0090314890b03401841c0a60181404100c1560003c3c2024040740c028a01a03900c00140d5180311543c03045911400c0900540000c002c01c1070b03911a0109242da4100e00600004142c0702c2c10030b81d0350301078031140c0c0480701c0700311107415040c5000c56000c4444070006803102 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 295591097 1250 295589847 295589857
    0xc06011d0f070807110a030905030c04060f0b1303022227031404030c081e03090109090e0f1e071401021f060b0d1a010c1205090112050c040e0901020f 66
    0x1071500b0f03869a62103403025200c0b600c01c02a400060b100c1d040c900f5052681c02400c040a4a800b101901c400790400810401a03c00c2402005940d1959a504005428840000300303540710b6608580e600072a500d0b000150018024500e4181c500800c00e20f000c02401503102d1880030510300351404004c501144a004200341660030020140320303810007240510511403003138400a6a0107801340705195242c0780d174a6141d0302000542d90381c0d0411801014800e420200984020540c181d489001c0c4614117040c11000c1d040040500c0d2441c010b50040d41ea68400501ca10305247c4004100248090306c01440c203845d1000b60ba004034681c4056144100540c0e0b030110b1141c2246500354001503008a08500c000700408555101c2c60a4400000310100444c0081c1c220550b00c0d1009609664418203440064445659948d001880c1c1440242076584031401440036081c0d502040c50140345046420510700c0454a0644a082444101080800015100801e000da20507241c6c0c00070b500300004101c0324026170250b = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 295592347 1250 295591097 295591111
    0xc041e0b09041107080408010c1805152a0309010f02061e100f181409060c13050405010b07020f060708070b0c07061a0f010c170f0903030c06011d0f 65
    0xc80e0125083c051a01065819440d0442c43c01a030b16541d40006600030f040110080c004500e02c0c2c400444078142ca188404210791008d4a121100000d20310807031480e0380400b404811700302515100351022041c1142d00c00458a4100056030303903119442c0050890390b4000740182c01c561050041001d01c003406441c800d070003031501300c82d681d060b2502183c44440f2140350b0007a40c492002c074180000e0740780000800c28290b201e0044200030089d020f070816540e009013141c45120540c8004085806c0611080080030712802c0783c24900321160301c2e040001d007070326070a9000500781d201c08100b5105619200c4901c03d44141e041718980e18041c500c0d504ea035900d015030500a00f2165020f00040d00c422158000ca80003039030301540400c145803142414030004440c0582103401511850b8039196154050180e40c0f00c0386800c40188125103c0303039060101c069020a1030445a4941400500c07980d4030304101610380310001d030000c4d15056040c020048140084071701000742d80314050083c45403e4041031010f90b0040c1d0 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 295593597 1250 295592347 295592351
    0x1090c05031f0513080f0306011701050603060919090b09010c0207180b01051204030309051b0127030c120302060702010c09092c1605271b030c041e0b0904 68
    0x140b0a440721a20728000480500010303000103006c403116040c40000d51103a2001d0302c4209088207111810203080070240660b9405c0403080011642d94a000c0c40741a1344126a40c120000355a20140f03403c0684500c9207080786d05041c40428041124420b00801e820075000e4401000200e1401c0c141c403c1002c180fa5990302c1a940d5580c035040300d80d1040c0120b0303d17107900c0354106c10003608082c0703402001130040d25001e403203a024140d00c121448248504070368081005a442442c0381514000121a0801010408401100d141000000109480c4018008107803402d20380e00040c07441c0c00d0290824800030410003c5900d000c1180c0c42054100401c0003e07102c4080d030009007011040d62841100240042d05242c1d02e980b401440500000055806100c9a031009250380c0310340c0d03810510420384501900790070601c14145403401c0360003c5005480d0b00440c9031070103007c0d0311024a00b030980ca50041d00c250386415000603051109484400b03520741c2544628030f6500509150110203002400740c410017602c039a03 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 295594847 1250 295593597 295593601
    0x110c011413032f0f0121020403051b1306031e050c0d080901020c0a0509010b070f0b0f10080c0109091505060f090306060913031416030201090c05031f05 67
    0x4400181c1220146038024a00181d16040c103801d41d07010156500d1907200b611252054482c28180f29030b18595440301a160140e0130302c1124240e180640101005c0043d45900740400004142c04100d180322000e80b402c54a4402c80900b414003c0060000f4810801c560a00400308002080c103d00140c40107840c0f5050000025589422810700104403800c551280ca0380c5903990900640c00000c1620a4098007110044003060041c0010f9061903c903007540801120010403005950000074285144100680400120300e0758800441c41c1c01560100304401501c0304016540700000305180c050a0010002d1480e8602d0100091004005000b84011181c88280d29251000054688806410000c180d41d40303030103000710400c0064100705001071107440f4074408540c59003007a0503c1c1d070040403000344980c0414640e4038140c91100100138482c21209042005e070760003034400a28002124442e43c004507401405080101c47c02000350840d5101e81c1007040403594428006891001e081c6c60791a010600da = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 295596097 1250 295594847 295594867
    0x201080c070515010810140a090303020f0f09130e190c08030409140a02030402030a081c06180e06060604050103090c08070303090e09070b070b06130e0706110c0114 72
    0x50300030290002c1c074910400003241ca43d850304641d014140d9543d042100ca4102c12507014200340c40c0f841981d441120700b4500800c413046125000582500d000342000340c0f0704003030400702d942d40c4e90119040780e00c0d010012455a040303190110381d0108600c0c8080c0e0a001106c2d020101b242c407883c4240100140305c1c14030001e807040082c070a402100600031801a00d40380c556480003040074102c0c0b1180701108005010005510306c081c0d1003a24056500a002002e0b041903995032140b082d0b01108a0406041c203241c5940d002c80700034010035025180450023601c0a07070303036111075500b61040e43c41ca40740c1c247c1080e0200304040d2500c50546080351002d02c0d0100d000c4503142030007040d040294024241a0082410101c141504640e80343c0c1115100b00180c0b00342d5544810f0f25171154094000c0140742ca008228001c00320711000c40140c3c2140740104600241030100d40344404443c50846104d500760092081001a030750032a19940900759a2800382200c900d015000070500d4081c0c2ca141008180003050b04040 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 295597347 1250 295596097 295596121
    0xb0f0f0c010b03030c0a05070f140904030e0307061710032402070f05030415020a0503270a14010e040219030504170705060f0601020a150f181101090e090a020108 71
    0x1000a015040e03170f690313190a000f070607250280c0d128140d0f00c501c2500000103900800000280803243e4182c5107124242e000c038100208104090002d80410400c0380650a1541d030600c0290014880c58489005140707000d040900c1c034407002040c103070020750660020070100300c0306800c4043c56150008500c0c44c0105007000300b80240507220703000d0443e401c8485902c0c00c000d8000028010f690710f814081e0906d0381c907154126a5011141401040ca80007401054100a9505800d40001120102c0f40701d9803003130712000c1070700da44d00c50b40140001030840504800558101c043c2c40d50008050b107003985003510781c00d014240c04c4c2c003140c800c07801c050740c4d07000040900c01444200105031864401c6560b603608503081c8543e82d800151061401c4010540100d08907600001341c2e074030040d9102019414014031003d0010082140d05d07540107a840c0c480309440c494500c480781100141d84103000b10300f00c200c8001c000418840041d0031007100e9910800a00c94000400142400000d5091034a1206a9540d60302c540c5 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 295598597 1250 295597347 295597361
    0x20a0501051009060503060403020c0f041b03050a0e030c071202060909040f0b0c030f04030804020a051909050a0e030313030e0a0602012019080604020c0d090603060b0f0f0c01 77
    0x1145510700014002c0352458806210704840b5107043c24041c950b121004c050f1251800e0b40e00030096070012100385041d061621003400008402080003402e9280d03000c0f03081d4020381e038003100380010303a4400411002c18528410b003002d040c000c1004504203003030101c400b0760f56800350141420035919524000219a100401c6611354203020380003540c64140b07490700124035286488115170503469040060365122800c0305492003010342124010480e02d80b030310141d61074000980140c0c0c0191100c1d401262a8460b00324010802c0c005004003c0d1407440c040c132280c11a03101400c1400f41500309000807031b602e01d0001c107403a040010141c00500c1611185401e5402000800c0740346d4100c00d0114000a52603019401603841c0c42c0c4005a0710006001c043e00c40516200e810701000109929601400082d407040303d8469200750054001031500050030f10f06803800400b030a04c500001c45004090090941c5402190018210000b855041c050f1042c02d0000a0103a070355104880d050104002c4050602501710130 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 295599847 1250 295598597 295598603
    0x70803190903020708190803150d020603090c0306010506030c070803070516141504020306190e1518030c030405060a0513061214090303060d030207091103040c150c080901020a 77
    0x1c40c4851602940b1820389109400d081d0160b9806000540c0000386028120740d84544214510f5807402c402c901c0b100c038980c0c41c03170b500301a061801c0740050f21000000c1d0700519084005194101409080600e81141600614080e0b9000c0c401d21800c003e008080d18200c036070000d0301e141c80f640c47c81c0c0100d40c0c6000d4104c1d02401100003566201c244440b05007242006a10041911210490074020460782c00e415500203405521000000b040051003003003403c0640c00c607440c045800796824900b145400c0052a55042e10300c1000103011000b441454405030b10343d10013000c4d5090104a60003071307840380110312500e40940c000245194046205100b12085035101403000f103031240d1241d200030300d4801500491401e0601e46118aa640410902d0301d81c400c0d6400c3d0011032943d83c2e00350601940c0444d04a044041d44545140480e40e81c0c498000e07681411400c103001900c9160600341036440101ca83d01c00424410184005003c00f03174030510035031a164100c14a42d0780d9280781c00040346000d600035000303 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 295601097 1250 295599847 295599851
    0x1802090303032d01120317040201090501050c0c0402040308030106020601120f0618081902010f06300f121209031e022418031318020403020a120506010f05030307080319 74
    0x103d14121680c141008803070103580c843c00fa881e0440317281f10380c202003968064045540351000300040e40c4194001e050044200003514a8031a141c000b29040e80c2140e041203e03512408401800000c5d0b0401180d4010000b428042e1f80301d0900747c45590010381042d102500c03094517081c8514501051450f811501c661003c0d586666181d101c06d002400d03030010720100015403e01c510b05188200038040d5106440c001d0041d14600b5041c010040f82c0008602030140011070980081c40104148603c517164460142d82802003501407038034000c1000c0000c41542413843d141500d500c010036440380240343c0d045005140e2204541e075000040c1d18082c002108501440c46690544400c01d80a07000f40d030055030131088007001541c401c0c20054407401552201d4400c1e001200c004c110b500c1001040d91940309105000601d002d4aa401040141074681c02c116070700d109850000041280c00c010440c01020080e212407440340c1401d000907200e2040807009000c0120100200701890041841c00aa01d2040801 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 295602347 1250 295601097 295601099
    0x302060a0203090301050105060a121e060f06030501090203010f1202031023011a030631141f05040218030d020a030914030303130302150a05011802090303032d01 71
    0x2000b9076a034048040c80e03010754200000015141018003d40700c050304951111094061100d200d000104425660500704600442c020f10b2515105d1080101400e02204d0420503142818000340544e48107078800b000c62407040004109103a030b10010607003034420107441c2d8110306043d400000c1c58001c0400d6a02d00440c5000340a444102181c0340d001c00018200c02d00ca4140d80c0e80b09404650100b03401000d441d107850800018460f8503000364110712800c201060720541d0710b528a103144030940e6511b0f03006405940d80f201003000f5040c00822561008040c11340c10392100c1c0d90001c005981000e845a40e000300e40120b000c003007105d00450500d0050802404480f8034102c1c0c160000d58030f580300141540485c0140d40081450156894440040701c0058000e40c9036845400c3c02030411510003030282c1c00c50041403800060740c0c401301e81700c178021520b40c2000309040d41455888004401d4070240d213101144104801e40303807074038013005590388451042d050f16040f000301492040382c0800040340b0a5540c9001d00 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 295603597 1250 295602347 295602367
    0x405011d0c0307060e0d0318080604060501050f030c01020a02060a051c0501090c05030907060513030602030906010f0807120f050c181e0c07060c1236150203070207030206 75
    0x10880c10390102101210f49140e0740380000c0e218141d01e154000e8202c4d107601c0707004c000700c3e000d541d002d80b8100c14903d101c0c19041d5101600740c09d000b001e44003123440c69140c10042045142c458104606410110040c0610382d60241c00070303580345100c0704024000c00c1c011840c80200f034040c0b0306403071040408050340c0b41402c4400d07031500010182402405684e62410b10760b43c008034814410f82e445407000c103000b446da10f42005029207068000440c0800001c280e4103005c00011100c2c000313580140c410b14000c0c00f41b5410209020b640c0d5005800807035199000460401c5009400d17443d0042040c0c001012407680c80c5c0d136003025030400d100d41a80c0e5420152002d40d2200c61040035038000d2051002030782034a400c100280c0c0c0c08951800c160760701c001c0d9039000d0240c000800c2a56000f0f8900183c9410001e0071a0001c400d0142030741c0706245680611522002083d500c910402c070030220811000c0644004a4400d545034054210708160484031a5404400154001e000700701180145400070300082d11403080c05 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 295604847 1250 295603597 295603603
    0x180f0307060603231509030706020403030c0c0b0f1c0e1603060506060304030e040c020a140c01080a1416050c1b0310110a0c030e12030705060f040c0b030405011d 71
    0x48801c03070b015003140d40d4108440c2601c11a074a16900c4c140d000e4a84109444241401140050500d9516020411070320b40040d689100400065101e41c4480a00342581e08200d03252041135404459011404c000301c1104c6d00b20301e401c03516100e41003d0070300910b00c04413410030000c01d43c002d4404207034401c0d080d03419200784a074103020302141d103d038005110035070f245000e100c0e05010554006000c43e000000003801c514080c2c1020040121b50301c102da94801c0c49451301d0003141102400300d2020b801944150841c3c1d41d02007400f5500261a80c01800400c1c09009886510f040c010310506c040a8400081101a8030650031140140e8019044840da0001c09908500c3c0d0300d80994030340c0c400d11030700d41103160126590041991820700d4807005c46c10084111003e0b200300b090b00d0021010170105003c104501e6031640d140000700ca4100c0000c54690000e85006480c0a001a0500158510901c20000081e2520595200fa900005001500c3c0d448034a000c901501583c080d044048483d0740b22203050144c00 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 295606097 1250 295604847 295604849
    0x2101060b0415020c030d0302031e16140304110d230c0a080105040c0311060705061312110703060c031d0d08010b0906040b2d0d05010506090603180f03070606 69
    0x840c8407098400e90b90606a913142c080c1e00159815400c04c40304006003600035400307107612191442a5016098901d0341443c4c2c40740d4100c40941c03411207140c4242c044103511800b40d0a11280c1a4010303407030b40c2055103407103801c0d03200e00d40c1c118400d005440d8140100120080b105040d02ca0f03034001d043d001c880d100c2c615503c907415941650300482e01118000380d0003905016850143d50495900c0d0806800c686626084401c00c0d00d582e90070100c1005400002002003011512070500d03103464001c1ba41041c40d00300041d03400c1c0d9401c103080040d81d507a0b09414150204208040303d9105800040300c2c41c1d0044254041c102d011040350701207003555400781c0810004145080b00c25031a5448036401c1c4c0c0c95220045842c01504842a040003041c80301384081c0b80420014031210b040c0c0e0a00002084221841c0c125200c520724a0700f0480d0004220f42240b450f81d4001c15000d001c1c00c441483c10004440045405d40c0001405074491036036031400c200003c1004c1c40004580c54890046e680e41e0140c5060810150a407 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 295607347 1250 295606097 295606109
    0x20a0801050106120219030906110c06040b060d03050a0509010318050328020c040e0709091401060902161b0b0f131505090607052409010b0f010e2101060b04 69
    0x90703500004d1100c14800c0364a030030b041c0d01d03003c0312020174138034101c00801c0302d130100311100c1d55140c04060310101060083c00f110700d8024001c081c64603151605400c1c08101a0509000e00b5407a80301c1d00001f0303000380640f011a00c42e45040303a02d840e58040103d01410308a9145400a2403252220083c004080014000e4031046003031040403c040e0604116181c40034602d4800581092414800500c4d040d001520100000e030100c0301c549840310030800c2118000b001c2114803440110688504540a004800040100380d10841c203010544082112102000600600c40f59010081041031220f21490a01818040400039110303071011002e1070090380244508401d01c200d0440000740701410b0114208003c50550704e542c24a6086c10612886801c0614100c2c1d142c06107510000311a0f00c1c03c640043c403182600d911b00254282040007030300b1074007104a0b40d8001d80c4021021222039801c030341c07880704450069801410303480b130620030700e4400c05181c01544c40c50750034404001000d04070407011300240c484c = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 295608597 1250 295607347 295607357
    0x915020d05060a0806010623040806010501090e0c040308030c070b04030e01030b0a03080415050f0307050a031407172205070503160f210501020c01060306150311090c07020a0801050106 81
    0x540300300b0440943c22601c20200c0c20b07805840140010703446621150740b200c9400b401040780441c40e05e5a11180d400c00e4125201550190004128541e8411070b0140103040325070300054a400c143c0021180d40c450360201420070000000410942c4a001040350f801580040c0c0d01d030010704180c40d00a0039510f036040f201c0e0010f81460704500e62458504031400c11a42c0c80b1140511341071a00c082140c02900c40604402841020301042c1c2c2d00d40f107070743c0080d44a02080e80e100e60b90742d120244c001c0d007111030b0794440c05212195041001030503500490810360b8024011060089655213061040701d0039036801100c5640451320504200b0003c00281d0303202a12422800c0d280b0110701c000f80c0f0458084103220f141005110f10408001001d00300e002d103003d0700340c00c1c81d10145c000b9007030300c510703081e030340320f0f9007060b40c5a07556100820a00180d0711540400e181c0861001000ea0700c0c58481e400c10102d81c4c0d854500c07502228010501400000048814259021381580040ba607a040c4540c0200701c05d1146a020074 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 295609847 1250 295608597 295608601
    0x10b090a0c0504030f020616150c05120a0933180203030712030605060301030f03030e03090121020702120a050136030e060d02130b07020907050d0915020d05 69
    0x600a0144a110369080c2da40e0600349403a40d00c4d0000c80071205030301030780c101008206943c145003501000100c2c82e40107001c3e20b400258403002c6e000c2281c840d10703c0c2004001d41032026607240095901c115401030241140811002ca86050011110301c01c0c2c0320000e0244500840c0d2201420040202c00d2154492601048220100c00100740f04010604001b58950010040c1350001841c1d54100c1d801e203c4c1710300c3e00052883d00c40001c201c2a80c801c0c0c100781ca0b0303140d0083e40482016418055000b503101c00300c000e941055220000178003420306001c3e03505080a03038503030160f0250607207a050782c0c1d03240d40040c050b5140c059481ea80d1500d4a8202100351941c1d405c0500400100039142c01d488c007211110004c168002808500c000c95015901c04100c04100c188550b14070300d40d450102604614004480069507107045074840c1180400c40d0740b01101d9030302d0610051016030740c1c2060442d4040228100300e5928100c03901520000c1100d050024040c00b40300b601c03c80540a658060810300c2d0588800700020303 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 295611097 1250 295609847 295609861
    0x20114130609080d020d050304050c0904030e040b0102070501093c15090308030105060c15100f0f0e0a110706060b120a0b030717010209132a0215070903050f010b09 72
    0x21310b07000d80d400702c0582d1010700c00d4140d580c8610700540c2e005005105446003101e4403000610a440203841c1900010110b0b50764064a1400d84140c1b906510b003400200002890800080e19502c5d440c13003401140301d07600c40511400705a4200400c52940c261b0f801c1111440c0c040460080070920b40500c3d01604021101e16030905d0088076810151fa4019440c80c1c2180e181204203c0c41e5803103403071810039600800e103010f000b000000d00d044d80540704140d00b040070a410079200034054421a8041d0700204c0c0c0201c1c0400250308404e25844c0c000006038000300710103031200c0101c00b00c0e00c51070100400441c64075800141002d500c1001c2e090520480340480565215601c4800a032442580540e9142e000010b081200c040c2092981c0c15030101640003600382100039001400c2c1550302c0181d003ca09403112500b12102901c1a00980c0902554003155016100542d00a6a95900782013901c0f20707400150116906e14010424a401507610000700c8440890000c0002d02034071074045c00b940a0350f01280400c0c46 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 295612347 1250 295611097 295611103
    0xa0b0f100b040806010315020f030411030c011b0b0a061d01030c060c1e0618060203040212030a0c0b06010e06070503090a08190206030c0c160e090a02011b02011413060908 75
    0xf21092940242200e909640310130340000303120200d803400c80354200301e0326540800e020003461145000c0c02c044180039090750706160a1001c11281c050402c1590805800a00c0c00719115494103034000101e0308441e5180440c0700c1c0288a260420742c42d00700c0380041e00b4043c41408134243d058a1242e18044249595101c099035840c24561008120f04424060303002d41115000103c2c40050088a000c5001d00800c40c584070145184030342a1006074000080106500f00906003001b0903d2078070065141003007480c0c005000d8282c40000600d82101000030841036845030a11070701400c4010021703552003046140c80c0742d4aa20101e41c850080a00c40c0c00001d20120100b040b0448074060300f00c8003c084d80d03d50800200d03920007401d4035440359060100c2d50f1420f0341007044008025412201c464014100320101540000c018007008069208814950050340c0c48980c81650350f008071006082042d440c801602c4400c14125804024076000c12440c03649080010240d04491403601c86029040c0c403240c02c81e032 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 295613597 1250 295612347 295612349
    0x6030b0604231002010b090f040b01122d1407080303070315080d02061014060a050a030e061501110f0601050d1406100f0509090601030201110a0b0f100b04 68
    0x1600c44000d10080200d0242c07031481c40d68045441c860032034180400c00000b08009900000800140e40d200000041e50070802d04860b04103006110b60303141441c20f981e070182070400500a82c0340350034410300c02d00700b00640540700000003003100400042c13113217002d112088907182c090b0007520000b03c00d01100c1c80811f0041404d5082d44c207100081c40ca9596400020b801900031120403124031505440009140281482481c40c3d0341402e41c0030b01500d042041d0184903840c0c9541104100091640001c4202d903a10f10407074010020508285071a50f02c505800d80080004540542003801756008100703d0340c2c8000500ca800070026200c080c0c000b5078100b1140ea403441c0480324203459034041c1e00140070514048200710300140c490103000c000c1030303e62800142000001c0d0b842030ba090024081c140603c42103600c501020700801c1d9841c1109241c05007889540d01c4c418030010341401021000b604c001c140a2107202645034200340315075000e003805100140e004400701d0300903141600312200030a405035507200b120 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 295614847 1250 295613597 295613599
    0xb0f070f0b04060b0402031b090f030307050f06010510090302040902280503010c031406090907180209030105160c02040507090815040b060315070f0c060f1a0f1e0411070b070906030b 80
    0xc0c801034404090448c00d64001d640a41c3e1000c82101e2525880e5020801049402e11481c050948071014a41c954a03015061300118494400c4200e102c0342e0a41c070141c604100c940440d8003060f055198000b084080403800740e414039016605007c03a10344054003008100b2550290001c0000300e1490004404482102c2494907910540c0300c00701d400740c50718007401e0790440c241e14141d03119180c0c0d407051803142e0b00e00ca5040000c0030342c021582d6040c919081c0b0540341d1018552100304102c0c40d00b0140103210350544003000341308603611400300305003910a000d03400250060404540001280c0c600b1a01e9800040302c080f21481d64030341c00a210b03030902054400e80c00d44901c40c050000e86480e0000e640c03103201c2ca0644810080400b090b440405c01078060303105d044480c92400900058402c444180003200f02350414003807401c14600c1046a103a41d9040c070400e01706c2c41103041c108000329000070080e000035164800001c2c0089000d209114404544074019141c5880e4602d9042d9100b9007513041d079006038901 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 295616097 1250 295614847 295614871
    0x17073209150906030f010306060f0e040b070e0a06230c031c09051b131509020f04050907080601081302030705010c021807050408070b03100b0f070f0b04060b040203 72
    0x8045582015000795500484590300d05007001105404a440c5800407602c41c40080b000c10010010f0000740d01c50900901004680d01c0192420440d200c10300100c090b0004140310400d100040915110340c02000c4400c0c00146003103030b11544e80400600c000c200000070300282284000340b26031042038000301c480600700d00300030310304200040981600007486000031000e1141c5a03030340c400001c6c0d81440585030001429803001036441442c03042c405603500703164110b40200e01d818a5441c40780354100f1a402202c041d00c2015a0b90301c000460582035005960005800c0800b020601400640107021984a00d0b030a982d01e94465880d41095654160301010203034058004150501840d449030f6100ca8005001807d01c3c11104411014108100c004542400000b1804a402e210703c1c1e4003070000400038800b0a060604504142c0c01c0d0b0038008040d0f00c150f0070b2081d4009180c081100a134015515005d0308040c60300f104804500304900c20502c2250100c81d107519014404035286410720a0380d020714015418 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 295617347 1250 295616097 295616107
    0xf17101d15060304081b06070807020102070b0f061206010e061f05070807031407060902030c0307030b0105060721020307020315070c0201030905100623030a080a0f170732 75
    0x501c0326540c07002d08160386184007007045003001c00c0740011b041c1c100d0800200030a203a1520940c0289000e1004d02800110f90040000303001041112413450b4100600244a203050703201c10001034442d94001c011404540906000001c5025014400c1031092406880204100b0b8030303100d2990754a8121070640380410030078001e40380414401000b51085502c00d00b0311581c1112070799030300c442c2600805002c4500544404812003103040c207100c410060441500104585415981c981011a0050007074038002d00c00440d0b01400c0c0114403091010780204103400c1d030480700303003040000e4032507001d40000d0380241318191034591204e0903804100e02c00d80b4640d03109003006107075600440261044050548845c403441241951680c03483c494040207000e9142080300c11001702d60034040d041d00301404148030350045c005000111b0840d008450342e200701450080c07400d0003560000d4803203140c0e04c50650321804c070f020708102c0410b4009040c03100445051303c8504008a12540c2c0310a6610700b504a05603400d400c5c00 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 295618597 1250 295617347 295617349
    0x2090c0702090406270b0a15050a171006060f1701180c1e032304080a181208030601110d0e04020901092102090a0903020d0f17101d15 59
    0x2c0200c20301401e01d43c1c3c0f00c2c07545144102d050345e121010103041d1945080f20050101241c00d61050041c40341d441030251a041d4500000140154154441c0610000680c284001d520708148040d40780010801402c00c4000e80300e00b0010410b04192410501088040310341d88280103400880d98100c80c003400d05100058a001d0008014203c40c00c40e030803d0004102e83c01c40b4112404403a01d403590130555000940340301d181000e00c80b208000b02c0e003a1407400b2480030301c80800c2e0001c0485003042c0c0d840c14040c40d03a00300c50314107442c0e400075588109001070131404800300b0012000001e600a04099841c5020f01480e810255201c42e04422a00007240f0100c081004c41e0030700340c01504075030344141048450113a07103510901140c001503880d0000e000000543c4411454072000c2c440e00541a454200a03900aa94005e07540d003000d41d0000c030520882b580c40700c942c544110840d100040351076034100e10740d00b8110b032090f143c3c1c0100d0094001000b00e490007806451100341c9400e10a103200181c0607803942c1000c0c = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 295619847 1250 295618597 295618601
    0x604080d11120702030a09051801140a08060403020304031109061e06040308030901090311030c07090f06030f030c060605100e13020c03040312020106060f120c0306080f030702090c0702090406 84
    0x1030300503090034007801200e20480d850b2255a01c103070030640141d9910041628010310b9100c0c541c2196220b45850344c01c004a40f8500600305e41541d651108007441641d42c60f0002c4e6450b02a41d0000764a413040404000805a000c0094400c40b41300f440f011680c1079040301000b850704d2040300e2240d0049074070301102c21142c00b00e00581880704c20103001c003446c1c6500c0b51580c1030554000c8600400e0350b916181c0500405521075070751000b0700400030240d401d10445003c555241c111500c0395144c1c094446100100241e00f9500a00040d81d00001101200541d441e02032308a1200c20410b5907214504040042c69080112110240e4812642c44680c0710b8440402c015221050b041186d1189d5420300076103c0b0724104100a102442c02200180550303110103600900355810742d0020001c00c55411f000d0059160043c40c1c0d03408028800e100480c4803440c0000450042009920007805807040c10450102050084014840c0320300a8072001d500c2d0b900c07840700c041240b1031540b009401509040029000c100c0907 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 295621097 1250 295619847 295619861
    0x7050d0e0603070c031e02011b05040308030c0304050304051f1808070608090c0307290a0519232101050603130303061e15030b03030d02070c0e0903090907020604080d 73
    0x2d040280c1c054680c1707011b0302d4140c9103e07480341015039501d540091040000681141003040d29140c0a03282c83d00f10356428940c0d020140100100356008000b007000c00000740240c9010301001f51030070401c402000e070f102c0c04814600aa41c000718012868405507114480414030640304000c00801e0b50514002084510000c000d101064a02801d0080600d9035001d000c808010000310504000308890b03c4190341c0e03045103080d4a0280602c080000c42c45560700102905d4000142d8441c800c88044c1215040e00c958041030061380425280c003135200c0310f000c00c800190006005e00e00031010143e9141c5019013110ba802e006044d4071020030b10005225080318500104900c0c802c0c0340208106a66141c252040714000c0c0b4445210042c51505002d100d000b0b07540e80150014900d01404904285008241c50744540d01952088540005075103003448550304182e8020600346103041d1043c60400301c0103407640c200c003414030721a4040201003020300344001031031802143c200307100f01d103010900e51101c4014010 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 295622347 1250 295621097 295621103
    0xb1e06010924110d11060f060a0b0d140703020408070b040b0301030605181212060334080f070306140705030a02031005040f0507083303030412060207050d0e0603070c 73
    0x6141104550036000740903a041c95803840d242c920000301581941703070402d1401442400e42d1004881003210655071801041d04450814003001da46030403004441020b089004c500481160114042c065401d90590003401140d0a41c004e42d80019110709029090344503e220751070541d8410710060001c20007030b0b4802904000d550b07003502404a007408240c3c2c1032158030451200145400706a0211020f81151070aa2248045010340840b10030100d02800101503040c20101002c02ea603040d001c0e5001c01c0d01400c01402642c2e04844d204c0c80032044946ea9419540000c4420b2400e2050380c24240810209150041c403060b1222810341c0d40e6068034038001e40000704140d56500c04914000384d6030310340c1c2c8640c420b00c0020010100d4289030011010b0720200c0081d0484410958030710f28150070345403070719010740700380700810061700b029148200191460145821513602c21030211171032010464554014801c90384074a00340c400342550400181c032a0607080300c20b5034100008100141c074880c800c003440c1603050300c = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 295623597 1250 295622347 295622357
    0xa0b0a0c080615090307030c0e010b04030503070312020d060807080f010606120e0109020d0f050106080304080d030b0307030b01061806031806020306210709050f04120f0c0b1e06010924 81
    0x24200b000924100b042c0e41f05070b0b02100c40071020300c42e09140c3c0c480303640074010717001c4440c3ca4246036a681d540c0d244601600941004902e800c0c041c40340e400b0760103e03082c1102d002c00c280041505e403403016885440c2880356801030b04c41c0340340c040f8211030107000341e9081702c9190315041c114001d400e09100240000840103500b5560360f9040d40c00603564902c028802e94041c40710141011003e150503400c5800c190014a1079500c02c2c442000708100000e1000b20704400d618000c9490102e00e404240b0701944c41d080141b144400300000710329141d20440c0580d140d0000c51b4800b01e0701d6615102074003294103070544080c81d0f901501012020600340c1e0011500951302030003005001c600c01008500030507202007150615000314400704215038a5000300303900305520029090160506988031180d0040d441c1c49003041c8030840b0759510340385004042c3d1484042d0020026051403030040f0071045041200140c2c00700f01c90b884804039516500c2036003808147d648503044051040503280041090294160390082003003 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 295624847 1250 295623597 295623607
    0xb01060813060c0c02100816030e011103070201090c06031505100e0306010807050a09060b03041202210a0f1701091505061201060923010503040f02120a0b0a0c080615 73
    0xb40302c0b0b2050106580603940c0390402c8400910400c01080403c203800790401c1811810b028a03010341280303000c02c0c400d02c1e00740016404001c0352a17501404804482d2000b050000c401c00c04407507019040055200e210f008080100e6403901c00540c1107604440d2854180ba00300c0c0811301c00360410a150020303180c00c030705205101314a590001380c41c00e14240c00005480c1c01c029020040c07420503040d04d002070322007a242407000d9410600401111b000040c80507000c82460000f0346540c13030080c8071042c4075641c00724504603112150085c018403540a6001200005c40d0360810a04503485080078880201c0030b46c1007100e080e46001070050191060140d00e4218500c5418005540d40d11540100091003840c8040b00c1300350703d445405040d6062990040103034402503681003c42c60701032107c56208040c02d00b400d9860341c42d6400c04c1140c0380045000203405c0380d44071224400340c000005a108542c1e22036001e825140d691000401e05851013443c15401240e0400c0108071240b4050b070002580d8100891828100 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 295626097 1250 295624847 295624853
    0x120c071104090c060f031116110607080414100e010e030c060d1a040c050a08190908120a020a020c0405040813030b01090b01020114061e12030c010b0d0b01060813 71
    0x2100541012a0383d020f620800300000c03a000180784d01100081c1c141045211040c1c3c514000b148141000175500c580c0140b00b050401001c01e00c00d541c0100041d010f00d4854480d841c2c030030444d501900a100c16030090411120f040e02d03200414040c2854142e0b83c0d030302c003003140c280151a41902d840f941c550501500c3c150607015141d0101038210040c007400c01203010800e00c0036641c400070030341c86454025420100400500758000045400c4241c8614088075035a0f212451103240601e20600c03a08140e081c04002814490340c90082c001003141c0f94000140c3e5141c07600c40500304e2080000403405a04101060800d0745043c0d40b05c01c3c0c2c414002c4031010310708081174003800c00031030f06500b0499070014044c00500c540309030b52041034220507007800200007044a504280746640c0000706071510604444e88500100200b403401100c8070310018008998503241206626103c2d045078240491941c6015000d145501e40003141180c125002041c0c050300d0b03400c02d1411034141a00501d240655502c0401c00400 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 295627347 1250 295626097 295626101
    0xc03032a0715020a060e07150f02010608060a09060e0a11040b030102070b0f100f0803030126010e1c0305040804050607080712090302270c090102120c0d0e06120c071104 74
    0x501c0700b1a03400307440d112a03546021011220541d20750b10140e41f011000740031072501c5007030b00c0007011300c0703802c1c01610080d0f00c43c0c1c12405059140c03c84003a034041c080c1807228021031900407441e03a621442050141811400c14039030740d81c24051014040e40c0c1000030f404000d0a00d03500034140180050009841c00400b82c881215150058520341001c00b5200c0401501880ca4103c0300081d010421850f520645090401a601d000600908290380c3c40d0800720111402401e0741e8502c00032401000b8403101e54910086902e541e0070003210508005d0b041d41a0504034460321947e40306640c0548401d0030a41840180310081d08941d00032512414104150f001007400178070003405035845651014011410361040c00040d81810300040c601e224402a80d0300100d02d003018003a413000300080a1603c80e40f030311300100c0c034107941c10043c0c51000070002020405950081245610080701c6c1c0c41f290021a009024400b4900c10b0440503100000c001e0003064040402d98001e00107030b8000d100d041d10040e441c000180c1 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 295628597 1250 295627347 295627379
    0x209040f090812060102120904181505180c03030f13030c09061d090303070e03071701020405040510050108220210030c022802060f0d0c110c03032a07 66
    0x2030b5421002c1000d9a1002c1000d07100c503444038007031002d811405407100030050940522400d0a00c100d44500d040d80841500030810301200b9000030300283d080c60344106510084c4020343d03126050701c00b945a20b200580d00000c00210030390024000f5894182c4808403448641c010388446002c08000031000404181142e01a0002c2d0156110014110746809031890440c00100d48420761640564100030311000c02106603030344480035007001c3c00b5a0101030300080c206540768111091010a00118043c2044154081c0c01602e10a43c3e00300125202d8195800c0645018400c880c00141400c0010b141c0154400e01c00301c0030341c0000900320480c030590340012140d42c80760315a4400250f0721000718a03901e03810000040751403110303035910380c0041e410550072495640e08440603006007000200c49600000d0303402120031241a04070700b00301c0601805001428400040c000b69500e100e007118250340c519000c400c0321080b46c000c1148a80d2800b104504820400d000c414800d070501445a00140600004031561 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 295629847 1250 295628597 295628603
    0x15120c0807180f0b010903062a090617041713050307060509010315050a15140417211204080c010606032007080f07050a1a040b2401030209040f09 64
    0x1c030720b032000c50039600855500000c0508118280620500350740d8000000b08142d0341c010f00085025100c001008410690300020001e10a095040042d20164041051810340303641c0e030b5802d41e25030b192800c10f56002c40103442c05420440e815200145000b08100100ba82c0d00d01c14103000c8200340e4a100083c10b104031a80003001088001a00d40c0443d0ba15104611030740501d1141d6003492401c1c00d020170102c10107800b41400d25000000c074a40441c1c05a01c8101c0316900b08030040b41c2d91902c4150380c0d0315500310504800203074401c040407403540c904905542e00c000c404040d90f841c01d000d040b01c050105610042c1040e40c4001040003c40d006038003c0c0154406030005807404610340c0100040100d40c40d41050b080340d20719000380001400560500c0c00c95120207c180801c41c0c4507161800e05508061460300024400481c100240f4042c0f0001000b091045004000001503542ca1164048110ba00d800380e4140f44110307440030490540c0a40d01410f24500090070001d420081156050708440740d41b1015 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 295631097 1250 295629847 295629869
    0x10180b0702031306050a20030708030405070306060b0c030910120e060106090504090803010b0912030313110103140f0c0415030b0310020c0706030b030a02090408090901050415120c0807 81
    0x203810008240380b90303c0c0144540c2c07402c1450901d981e0b03402003079040040c18503114451401d00084c6c40e101d0800c207a841c0550801d03801c40d030707038101840d00b207a0b42d85040c84101d40e000d0800600060608001e0261445141401c01852a0a0f507140401084602c031244050512060410415401ca9984a400f0708400030f0002080c0302c0d4101003029001e00820740c0014800c1e4104044900040c500c617003036074115920a030310681c81d402104002241111034502c042120302c000300800600410005078451803600031442000d440015034011002d1725200311210018400000101f081014240107482e417014500301d00f942070030b461309a40b091100d650251400007a80b5401d24082e03e00c1d042c4205040300b540b04c5011898914091611510340d20b881c03203860b061550b0313410000c8168030244a414805030740184586424079081c43c140c41290440300c0054042c40c5a40c001003000c1c103107445882c54102012021094561420700340b11603a580ca100e0807140b52891140000340e01c02e0403c000f0018207009445 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 295632347 1250 295631097 295631107
    0x150905010203180607140c03070f080406030c0c0c29031e0105030601032a0f030803041e08090d08070501061d090c010e12010e07030308090d08040510180b070203 71
    0xf102406501c14600002150000e8043c00039140d0880707100c8080030300190506803900040c40903142540034001c0040c01280034807004404025400c4010000d51320700d0345080000e149c010000f01c804501e20840101401c0061a05200c40c07011a140807a0040340c489880440004801200d8581e80041d03030619500d035016000030f0326180d0130003003050140501354018143d56240d83c4401d0700c41d002c2c50124503081c001d010100000f0398200107003c0060040d81051180003562450308040aa008071000d851509c0c60480051840f8880203c4604041d00316980508180c9001c080180d81c0c070502d082240c80440130028000020005e000e51801000d03003c4030104010f0040f08039200d11b0500811004a60700401c045c245d42d680c1011020103c6801600c0c1481c140d0004210780d4018040460107030101c0c407900e50700100301980601014400c508003000d80340d4500f10b40c80107a034001810b8030010710a4018210901e1940d40b29030100140c900114010701c0f01c0020340e11010603625040c0c032600010307040064 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 295633597 1250 295632347 295632361
    0x90b010e04150608060a0b0a02161d010312030f05010b070302010b010203190f03020d05090a02012c0906040b130212060a0e07030e07050307060c0209060108040f0b04150905010203 79
    0x1005852240060300c092001402d0984090b031070b503801d40103403018040780c1000700f201364407203081100142100c1c2440c5503039420700c100060340c1e4164045118503a450300ba50040303881c002040c08101e820241029501945c0d00f160750340d404803400062078a0805a90308142e0310b00b15140d029080c0280a812000345c1e8400050030000d0030744070f89002081c1558800c0040001070800c00000001d4920b0324030380101b4168080301c08401034422050031865803070811007409210745010403102d07013440c800d07201c43c1c5d03007a068030440b070800c040320035490100282c2000c0010058101005c1e440e82c01701004000007114000000011800004451070a98695000c00e00382c0320007003001c070019000f6900325514a8a1454248070454901006107100201903c420075480400f40070001c1e1009040010b06031501c194480c00b00401c0301e41065016407040070b5240114030310b5400b9000d0140210381000c40d490100b860754594150142c4003601c12142c1401d00d1815505080c21845908407840c854000940e0342d0500714 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 295634847 1250 295633597 295633607
    0xa1202040c03050105030327130b010f1404090f060e040b150303030103020625141501140907050703020a08030712150e150109080604050f0f060105060a050c010f06090b01 75
    0x3819400034180f0b000b005119a90f00042030707812545124a2200348180200b141d40841c0040302074481d00000212210160010b25400004142c4002c1ea0750780c01403140446c085421041d90454650341c3c140400c0203000500c4541c01c0340035070400d04040880c07040d82e00e020b41c40c25503400300d805940c010144014003040008503c00100c214504900541c21941150005030203807141401560846200c0851441040081c8115240d5143c002c814400c07000000c0305842d03116101e001030b5070100f01c414000401c00e01a0014118800000580041c41e0341c0e0720428282c0700c80c0d002140540642c803c43c2d51110010b203034140103601c542080d036503504030603001403010000d42e0100030303540b400d1440108043c041c65034003416041d403040c43d00f50551500c103401001a6046805600103450038000d06c020082840400100c01440295130011a10801240034620351294802e014656020004200400790740e44200301a000810044000142d40552054000125a01540030380741181d21442804255a005 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 295636097 1250 295634847 295634861
    0x140c03070602040515180f01110f010203010612140708060a15031505010201090b152103030f06010c05070b0a0e10170c09010804080711090910050705070b150f0a120204 74
    0x2400c1b0709103031142c40d000ea2800582d22842d405000802404940e030b078800e280062605450380181c2c2e8811103401502c4c0d010f94800d0040790b0100b980401440d9400722035104030140011100e030b80052544400b9001ca50240029210941c4606500408030702d115a20346e41d0410005a03850000b6590070002c48090106d810744d10447c150b906d409155404a200300038100d500202816003170800003101000640070200301c0303800160310300000c540315203481c500000650003503800d000d824102c2e40c0c5040c0110780c644800381005020313070480b000800c1603519610107803030713050090306000300a0703030008003c03d5500c1542c409000000e00c00501c00c803040585600388582108110750030901d0b0418490018100b28400b40c001803282a001800740240400c82c5e000000c070010080c404505030520403010b071b44d00c10014912400d011700c3d0501107071200b0702520864000a03401031010707106544400d1460f03944000746003c550400c500c410f40f0b40d41030b03507030861030b00c05404034030280101a980e45c01404115401 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 295637347 1250 295636097 295636129
    0x712030903020d0c3302071a010503030406120504111f030f1a120f01020f1e090d06020306040e0f10060503030a0c1410050c0307080a0c0f140c030706020405 69
    0x103460104004242c0c190301032505282c9501c20601001c141c041c00c0074a03800e8174079054101307a2001c0b03907a030f0030441507550b0401c0c407035489800300b2016600c59082540701d204601c030744d402013010074042100300803181c7c00040d4441c1c040c100b00064500d80c40c01007000940d2040a10030010850344694044035018800d1064900d40300c401000322884c06a00c0340394840701540400d118409855403190074003000c00c6214014807001000b951194002e00811400341c000345800c1d031500e218214030b030b40b12103450000e4889501001340a001409803640b80c610003588090300c0940c129898070181c5040301c0703080110f82150910300004000d500c8825415074121950b50b001603109800811031400c0c182d81c41666207002c150403940d0340d0300b1112542c2c42580350511807140000b00e2420a410072001d02030800280d40f28070060b44650354540d60f0000e440c4201c60010030305101007009103a400410920965035500c009404d1055280303000d807510401491500662412201e4a80004080c07040d4289207540310300c9944 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 295638597 1250 295637347 295637357
    0x21509031b0a1412030a08070908010c050403080f0c0d080604180c05010818060103110f030c18060607050604060501090e0303010308070611190306060801050d08040e07050712030903020d 82
    0x341540000d0640e400c103100d4048410f0700d80e201082d1a5032500c84d6006850300e06405c90b03941360549070024180b0130003118040086103c0d00e034006180101030141e6403110310b403903450901d0316055640300d0542c2d8122180d400c170f5045d4140a0008941420042c13180075030855159910185801d0f0100070550351007403107103140b400c15543c0345030006040500d4442640c1c0b00342400d42081c2c1d07562112440c0380880345c52800752882183c00010900c0140010000900b90555410140500903400d2560715010025101d820150041d0744580a402c02c0803115000900142541d1500c6415140d4615160303007924280c600c959100010001c6800d14031800881454900203141151305d142c840c1c1d0303000c2c002c0c0c00c0080c10071500c034030082c40c0b180b00f400100d44503044803043d0f441c50503142030802002084103014200201d04060004540c0d413070718a1070b0b1052141d10a11851805d07080c1640c6440c0b9070710160008d41407003024001c2c200060b846151046880c909a50009000304450800a10b44171140c500c1c001400 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 295639847 1250 295638597 295638643
    0x6031b060813030c120c02010f1b14071e08010f050c07060213150206090c060f0702060c0a0807080304031d0604030f0212070603060503100b0907180302150903 70
    0xd508260340c240d1000103208440c0740e00d159402c0c15900d488506034000c0c05800c082034200900d1713130880c0d0086080c074002c6c2d8500d40c6401d00011305441c001e0200da0300714440d100048580c1c00144000201c200b03040c8000040d120840d6880c44400124101c5400d00400d1112520003401008401d10400c80c500c2c01310340040c0068140f00c180c070b036001e2240381c2000d0102c1d600081d140c01a4030a040701800180100803040c0405007110340020740301c450698101c40e25000d000d400d140989000c0342a1040c2d0702c440580145005915401c1100e16880106010368900401280b907012981301c1c03018000d0980202c610560720b00c1c0602d00104407080c42e600035408011005442c6c4804d031140d41c251810b0303c2c3c0c00500005400c29038000507084050440110b0814032990318046040e5605810500484000754111a03003070f81c14120035020342e2182c10140303400942000001e16041e10a84103610b50300540a0044400d0380c99070003165403600c0720000303440041000104060641010080c4040d40341040301c0d008001 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 295641097 1250 295639847 295639859
    0x102070803070c0c0302130506011b020906220c020a120201050118020309010212070e030d080402030d1b080f03010e0114150c120c0606010e0307030c0b0703030209040f06031b 77
    0x41c00050494810001106803c208204801c03040b83c000d07540061104040c0010f0300c007400d014100c1140e000e800a403442980ba564940101c24008071300781e0041c4082400c2d41c5007820b01055407890b00d50070840c41048079011f14020114403545071f00305c01c40d9010700317955056818031514515007607c00404581c135020040103088070a00c81c3e40180c1c000c4200c0565a074542184190190050360b2000501c094003c0c240325009401841a106100c6c00f5002e4400282c032580381038686010844010b9051342140142c101803078400e06000030081d03010700c0c00141c4804c0984030441650821a03036903001c980004014010382088030402801440319400070300f40f0300340c0c840100d003e002405410440e2040003060418080b1070501141d540001c07008070080e2a04203c4210340d64072441a110342d1301040b2070135a040c40c20704000c0b5050080e6034000040441c0f240c90540c14203100c0e0f01c100b074140e0825600380140051541c1d6405030920b184560440450850b046082c8404d01c2a0140050604d04000d17070010000 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 295642347 1250 295641097 295641113
    0x50408030306040b2701080d09031a0a09051c031107050a0605060a053319110319051305030d171005120607030c020a0b01030206070203010e010f020c0f010207 70
    0x201060644011a56032056000315001d0041255662034001c1a501c00c241784142001c034107812920306070115401034429546c00d440f5103a0a00026103d95500840003080300d240891560b00038000311800503014103180c480d20b00341010703800c1031008907100d4545103c078558140140000a4240c00106240001c150783d160394400000d000103044030b4035007002800729070b29031426400619002e031032a000e1030b54029140305182884414402d42d071001a068840d25001380c01a1100154140380c400078140c603600d000c2e0f8140624a802d05110310003004070343c0c40140101c4103000700e0b41e442c0d12280d0b2500d061100d08940c0e680130750800b80c005d0380105100300005078040101102110308200c00f1145460b11f00140c0b010080a801486c0c21089064122400b0440055450311884255030100142000101c00301d844410746032010303008440d11401070000d8500030004100d81da200900003c6e4021914001c0f5081d2074916512800171a80495a9071074a80140b0007450030290800085140130210703030750205 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 295643597 1250 295642347 295642351
    0x100e010608180c04020301060c0606090207020105040506130803070b01081905100213120b091509060a0e1906060f093308060c0406120e060f0a060e1302030106060504080303 76
    0x851562440e10030182c201c09001030002c070b02e0040c3c015541d039a16890082d040403140b54040360040d01c1c102c2c00013240002c80c425910030f29416590a03141c117140c003040240680109041d687d282c840c1c1000001e0004c3d00b0001012083e1065819030300648c23506024605090788049800b40340f00960304150b0000e200400d180040d0740c0c0c41c05005032500346102404000c800c41c0c0e00013240d0801d46010b40c40610400da405640710380c40c0c2030100e614054a4421002220101f0b0300ca8002d06c4d400180800e0141440e50480c010700c5204c2400c5494010203031582c02c0301a91204c42c2941c45a40d1418180444203044851002030001c2c500288005901e101d400900e40304607034407811540b243c580c0305841480702807800c43c1c0105a800204c8101d820302c000034041540c0a07200c0c2c2404152811200d00c5c0b01c6100d800b810700c41a00180c080c0005981c3e840c03c220300013500520440e2550f0341c818000c00d03503103d110150ba01420015090320703251f170704510505003190517980240050020602c802c0040c44c1d800400c0781c0d = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 295644847 1250 295643597 295643611
    0x1806050c0a080a0c11030409050f13080d0b1503100303090b1201050405060102030f040306061401030608190602090d0b160827010204180f060e0c1b030d0207050303100e010608 77
    0x20700200700743c0040f1021940d00c0511179460100040014401c0700c15008580922034101884940351a0b4802d109d07200742840c88004c200120900850400281c21390000040400103080c510044056040010f902d500403034100134410402c0b0300600506500903032030400340004805552078800784203a4410040014465180710f240c1300c10002d41d01e64403c1c010707103081c1c250009400340c40c0e640300d01d00302000e84424011614140032020603012103620900a00d02129084006001800c441c070348166100880e0030801da0f0a1902049407202544440c00396586090090b00d1300d410030b0920b460100b0140402c1100101000940000e0180d54054028114071805240315060714000c1c1e500805406401360f5804101c0101c9540c18080b8071103e940c1141e543c404038103800304a0503442d80060b00c440041a920305107003810501c14040c2c00744070320b11100c1700080000d007102d080050309450802685c0c4a0b480881c3c058002006114010318030f1201d49001d4512551080480e6040000c000d0003030100034015 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 295646097 1250 295644847 295644851
    0x70207050a051903050111180906010804030302030612030a020c010206100308040b070501111206030606040504050309060f07051603031101020405010509060307050c010614030d051804090507091806050c0a080a 92
    0x52407110200180f5800465104009002601c0c5821a00c0026041007018a181c00000c030001c00d0f031842c1941c01144901c005842d100e030719407a10f0b28100c009420042802d504050240b81d40d02031410200044c040c00c07141c942c01020743c130942800080c10518003038600c1084104c1090b040c40052100c4061701d040c1c075007290505480303180034200782c1d01402910701e2081e6005400150b40c0320140000c8141d80c0b041e1010360440e103003511000e040c0000c650044034050581d0b00180072480d01490524000c1910f141110002810101031342c581d036042441c0c07811140b01c910b15601080080680260203488c080c0319039002182094600000a80300d0b1080d010410712401c8000005000769004505550307640306200020040540c588141c0c005211007851864441d101c0c0d181d9060b080c2d8859400c45100d071070003448040008900c101404007402c0410011150350180c0400802c1079200c0d441029009081e2000c0070740d80c4429400c00c0011500050404040008100301c00e4180b180c001106581011442c000 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 295647347 1250 295646097 295646119
    0xa030510170604060b220e0c04020d1a0a180c0507051605040e1908030402030a050f010204090b0621041b1409010801060303091710020d14070207050a05 67
    0x60600c92052074200070215000e403400004540380000340d080c403452049004000c0083c000e000c220082d00b03545241c03c4d04041c85400502001159003222150303403840e100701d6028014080018080e41c01003800b44800c1039036600b128140802080d40040e10315416950009041e060181079034110301d04010204e02d442c0c031520300d844e80c0c81c4198101c98205070007100360307100510b1820042c3c0c0802140d02c034151181d03042c14404140c0c1c00b00405c100000c0e8448040400c1990029943c1e110143c01c0240141d03414020200ca140105000f4494003908108000c00180c0d103d0814403148100c40c18504094002c100901002205220000120b07040d40f19207829030110350b94034a4070030700d280310214481301c2d01050000c2c0000c0c0c00590141e01c410f8080c2c1110f070f40d1000d0381c8442c0058200d8416100c0500000d907035503810042c0607401c140c080c140358200010303904941030520120b4103a0b440300d064040362a81e6038562864409406401c190051058400f902056140000007440600e0500030b143c45910b96034a = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 295648597 1250 295647347 295647361
    0x140c010c0b0c1303020a032f0d0f02040207020613030308010608070807030504050a1403070308010e09030702090405070f15030e010c02060a0b0619030501080d030e15060103090203060118060e0c0a0305 88
    0x40b403c01598001c0203150034507143d190102030400090b00c000b40c0da5540a0490f40460740c0c2c00301c890b074032000c081e0040c0c616000c41e4440201c0c1b0700312901c090b6041a4208003920141c0c0f2418020070750607400c0c41c2d258000c10f255203001401d0600580c48541007044d60406c1c048074940c451229500003c9502c0c010601d51a642849410310310f4040008201c503100941b00440b000c1d01001812610740a6280e19007140e0742c030300915048a41c00c50700078080d42c01c1084084018a48502c903281c0050103142201c2e025900c0b4252041c0b01c8656400c10041c03c88058411040f0f0340e8540100c1d82045882c030000c0c04040781480000e075584002a0024050a07112404511700351a804c0c19902c5100c81141e00c0710544000140140051800b8012404030b4010034802c0710320180203000b040381a01e8520300030682e105030762030140f8035800c0140c1540c1c10540c40d010b6030b402690382004014080c2c500b132401221401e100e04446001c641056202c40d69101218081244101001055955815040c203000c06c0640c3c88030 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 295649847 1250 295648597 295648627
    0x70b01090e0f011406030f0f060705071a0703050f06010e0306070f03110f0a090807030302060c0d06031a09010507181503150303020a0302010f14270109140c010c0b0c 73
    0x15500b0003641c80d0030462480f01000d07004e02030042c601541036440a0004043c81c0d0f4454101079441800c9506c900045000c4501c500000c1605038020241e110165144402c000c16400054481c400001d40761018024024041c040c0c281e08070b0b8003403c11101501300000400e894080041c4a40184440c0d001014035550190700300540f18810140500d54680100c0801441c60f041244e030440054040500440c0c00ca200245003001e82e600b40c0c0091a150380c803000e80b207002e54011480040c0c03140e212003000000400c20000d40459010703070000c50b800c80c079180101908403500203000e10100000d10407503034503503400c90b0503020541d03080d14420101081d6130141580030b400700d600003125400500c84008140340d03000c14402d80c102e102e64024450240d840820710700369240c0c4400400c07100c3c0c0601c080782c45000031800c00b440c1c40c4410f0800403458504440c082c4d0842d0b081080a9034070480c64101203005160500910307002220034200107122000da51241c482c0190001e080441ca5200024248410000c407 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 295651097 1250 295649847 295649863
    0xb100c02130c0c0506070203250515010603051509010501090302090603011b0903060f020f0901110a0c0b0c060a11071b031718010815130b060d090201080a02070b01090e 74
    0x10750140030390a4034a0004000071240c0e1420b60301030060801103503090384040308450b0134a11010703282c08504040c1e0f0000c0301c01e200756a011030315441070b070a0100f18070240e108414020303c5607440005040c50464801c0014401c095031091040c10410300520180e0f130400d81d5032050329016202030b11550b9900001c240142509040e10720800105845112500da1008225003070700e00c146018800000f410721460140d004504406405980500400800354801d80485a65100c080201e03440c3c0c0b0356548640e8081d8881d5007201b1000c9100051195214004012007a04003203440320401440d5400811030b005401410001000c2405400c5501501c1180c000c0c200003442d0464801c16104404c40480f00042c1d01840000c55040301c0c4080b02ca10940c080c0540d1403040d420310580217103ca030f0140801c0107454142c00000c0380d0540d00c04841c24a6181c900c0a000c80c5100c00000007015040c600025004160080c0804501c1e401000b18800042e120450141100d400c048041110707100282024101928 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 295652347 1250 295651097 295651129
    0x15051201080d140c060f0c0738041101050903100606021f0c08070f02011d0c0906030a0c030f0606030506090106050a0f05180601020712030806130b100c02 68
    0x42002241606012485004040098481d00c086506035156040035025034400403040b50032003070018903103074980d16140d54031a4401c0072145c60428180d85111503541c2e070005200d65103c2404034501b490050151691101c4c803000d50408083c40c0541d070320030485100380001c9042003400300c4c038629151000c01028008484880c01880456207030f06001b550307412107620320303030040e01e00004d41c2200c0c1708184202c8820005640d1040e465940b04001034030b8400d0200301d280210340d41c907290b503040d500b140c810520310202c2c0000500a1008448200400803802814451003608080340b2800054116102081141d9020001002050890414000030412131b0302c080c0141c001d072810000b21600660060f02940c00454020f09040e0f250300101d4003514950042c15001540d0b0000034400303c1703e12600076130280051046488032038480c0343c02e511510600800300e02045944041c802c141c50003240f880c459a5184004104141c11600050801e486055142090101188055055440d81d117201041a00 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 295653597 1250 295652347 295652377
    0x172a1e0720060906072a060c1b06080411060403061e05010b040b0d09053a08040201090b070f02040e0313080303070e1504030605070f02101103011505 66
    0x10500308003500340a24180604642812000d0700114580031081e5904440050301c05400c0210642e16140c0d800a89030301030010524903100c02049592141000024280c255280007100c0b801d0300c0c1c1803105e120162403207103a00240f89014042154055030441e0312a400800250b035042e40c0e000030900921490b0001b0389028104040e103441d449904048510600d107900c81000580e03070341c00d4082e00c079001e140030308001240304000102010f04183c109104a600071420b03502c0e286030400720440070704070303e030307040303040300c940d00c0c1d08080110407000c10795602c51000d062490041c5880d43c0008c00403011409030001c0c1e0040440c115003406052065459001e40c041d10410860502d045912360341d1308407002866900c1c85030074003c03e4010020081d2402900076444005402103100104251403062140100c0b09400034400000407401d0b901640f800780f0810f4559451000c0103100003400e00f01c0825a840e070141c02c140e00c11f036000c0780050031a0304694424400030000c034103c40f004c0319103106031700103025220703 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 295654847 1250 295653597 295653607
    0x3050a18060c11010e090601051b0a0308041506060c020108090319020313060e0a0902090111010f0b0424060f1404090204050103062408040819172a1e 66
    0x42e0030540700d020702400340d2403000a140c16800115185c452001e45550000c0080d00402c800703501500148c8070b140c4041c14039004841403401c41c0c6141140740c000640c00078031941c1c28002030200b0807500b02442c600074030003400742a0070090f0203410300c21600030090400000c5000507031080c405105a82518404e620701f000c0342031a00c24005c4d035030341000700c149481d00e805200002e0114002d0091142c4441c1c0a130030000340d40d02d09840040290020070140703060240c01e00c00420301d00c900788a04000000d00d8540060143c0240d004d02003259001c1c0c2d1042400000700b00e05010600b4a00c51540c03c0350b0052404840082c0700b00d80494407044110905040860041804103000c49550041d0058944c01c3c1c2e404c014056558400365021b03500405140d482c501e281d4074005c881403052143c164814000c205031f51411590080c1040700c141000390f00c0c0d001944684800210000c00c0b0080c54000400540c440ca8010b4030f4103418801c0720480b01d200c3c032152000580100c03142294180510b6248c140ea03000c40c0c4036 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 295656097 1250 295654847 295654859
    0x7110a03020d03150503100f02040f0b22060e10090b1303060e03031b0901020111030c030a0e160927030f020d0314061e040e0a03022803050a18 63
    0x2e091401102c001007818090f00303200e00915403103c032088410080013494101d03103c0c2070000050603001c0001107002d17000c0101040c0d12542910030782c02000d280a031280c2c0e844034030500070001142024600b00c02900c42070300b0858198090390394950810100c5600c0c0784201000c00903200d07201c89034081040740c0340115144112004118040c01200d004100c00c0c41600c1142c07640680760b00c400ca0706081c12160444906484540c2d45024040b00403042c000055035035030441e200036030380d0022654000d02c0c80c00002086403c8101c0d015064840f0703002c0c00203014000344118002000180ba019010505507a0f1a000a8038a412034195440c2c80040700d06e003d1942007824000c0c00180d8414032080544a40544600044d2180c4914041c2c08000e00256020b41c4130ad000b081540e501c0b100745037001940c26071900c9095501ca115581c00310390000e00070050951941f501a0811800c4e024501c0c0c001c14401ca410001c803401c03101c41500c181c1c1880c0c66540c610340200103884802c160a024100c000c00c1d00c42c04542 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 295657347 1250 295656097 295656103
    0x10c030209010810030c0b0711041107021903020a1502151501081e0408030901150806010f0b0f18030a05010207030917030304030f110a050a0f0b1e060907110a0302 72
    0x15501080c0d0b030300d0050b0703510b40d44d2000c43d800c05480300900c07001040e0010003010340301d4005403007038030f1048201010401040c0c0000c0d09032452442e0002e030540700018140d0843c0b601507000c1c0da02a00d2a03d4890085242d5000180041c1442c41014078036100c1d1503a07084554420f00003200c1e41d0715015008200c6051940d8003980c0d03110140103440c0801c41903400700e440d0881c2c00842c15035071002c0650011065450f07981d6103846070000780400000d0340d2607110364071451400e99007001c060718a41c001002c081d8902580d0910780d2680f503102c60340700502004001054200300b01125403100404240f0a103818034a0013080c41c0ac008075034007030720035403020402c0b0b01003681c00946102104c1016030043d03c00010a02040c0d100d2000343c030b0080c0412010b203039608540780682c3e505402201464251140191151074a5042038000042202c030384944242a00c10040c00c1a0141c0d08059a01d22030b40c0031031000e29450150300809029288514080800210b005100d004010404004a42500d84003141460040d503 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 295658597 1250 295657347 295657357
    0xa0609020405060a150c0c0e0f07020c0105180607020d0f1110030506032d0307061b02030a0804170715050405010b04150b0723031b15010302040b12010c0302 69
    0x100c66400c19003c50729514107805550181c41c2080e2130b4401444a888003520942182c107003c5070301d010344a80c0050451071181c0308070302c500240039044045107001e41d002030400080004c110705100007442600c50b0074070041d0716010760080503030314995645e041d4000140040319200f0b00400e8072140111490410045201395404000700303944c5401015000542601510b00071289540c00d60b00440c5540000f041141c0c00032010340c440f40200f0f540c00102200182160300c41041a10345580b90402001c0241844001145808980c07001c8c50816005080003414040e0180015100c80030580203160040d41040c00c81302d80c5503014400101007601e0860032000340204a6068a030b5520b0007414511500702401151803421035440d180345c0e5941005460740d156000751505075030031000310160400125900d020221070801c41001503894804503520703805040c030200400482904001c1550461425000b0740da41901e41c103d40210b013038010040442c100e0f40c0000a190010360030a40c003044880c2d09940100 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 295659847 1250 295658597 295658599
    0x4080d02060601020c2b080f07020102070b070305031915030c08151611011509060302090a0c0207060509010e03010c120b0307080303010e06030f060f070f0809060121050a060902 78
    0x2400641d2110010f984a8840341c261507041b0065500c130241e1814101401c0c200d84045290307240115005841c7d42807503400c0070204854062000403a403003550303010850759004100c0ca2082501d425186e0394010141d0101400600300c03140d2051140f071070681d00c1c1c7c00c0008050014000000103a60300d0905201c0146180300703070314250045a100644103204405414422041c0540a00c40b22910305000c4a00d905208281c02e0f4039541c410b043d040d940c002040200042100410102d030480c10f43c010081b908401900c1c00c181b9502c1c0c00e01c5808101d0300411080d08840315400c1040e11401070f4401642c014900e454800e0303155184c8076081314042e8001100c8124499440e03001c11210300f140052640c0c0729105c0c000c44005900034001084400c510400b0140d1011029080e9118070000f499090710b1301c00c0aa0315542611790b0142002038140c0c0c01441101400e00c545041080360a0425540783ca610060140e1111000b490424150106190b000540c00c0790b4804119662002581000c1d002010b400b5022 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 295661097 1250 295659847 295659853
    0xb01030c05040c020c01081e0a02030906090a0b0a050c07060e01050702070b07020109090b15030702030403050c0d0308060904082101051305040209010b131203050c0706030501081203040c05030304080d02 89
    0x4102410988900c6240355620740017403800c4010400103441c40c2c0340041000c5d0b1040320240d900060b40c92410000e50041d01c40e60005600c038200034440a04244e070042440d25141d208401503030105050b4520f19400450b00100050261202110075185d403140440203401d0504040d500011001c0541c88544140210350039925a180c5030a4200014880c0e0340d030180c0050048a400d2000c0b0806a00004c400d040082c010400420f4156005a96400840f015801340c2c2002c54100705100c424010340020440c12038074200072500c00d58000e8001c00010340203a02491380300e0000307002c20035140100c85145207040010780301c02c024801c1c00681d0240034020180100f54401c01d40591507298000e0a0049a0041c031483d00b580c205600c0c0c1002c2d401034402d01c00401049040020941c1103a841201d00c1400f0f6500d542d0b0312445000c08918101c40c1e54451004c01d881d02e8010040780c0e80120f48040d0383c10154665542d07907129424101000c3c20581c000d242d040c000000c0020b4400c40000b403800c040721407502a = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 295662347 1250 295661097 295661099
    0x2010b0114180307050a15090501210e0f0715020717030417100609050708180706050703020114090a050f03031003120302070f14011815021b0a0b01030c 67
    0x1140c400c818181c480003191014480c40070b00140d110304007240003201030100e40c55180d64034001880400e141e4030981400e03555210b00401300d50321040d4000580380070309046905140b07101403041c42440d1070300410709031035480940c005812024041d400005030490100ca01c915280e5246d6418a18031800030409482440c0b4003340c1842e9541c00a001d80e03c0c0603018508080c9051040030f14250404c0015070903004503030300211511510300c41e080240c02011400200d6160003103011b00505409070a14080030b2501d5130200000c030000468005661130340c50f0068032207034145400d0f4090101c1c80340c021061480306040240302c040000e07030410b005008204486215031180c40094030b0344030a80f400c40280d01c600400703002043e900c440c41807480c00c0600d001450000140c43e035414044014a04450b420140315034168003000c05d00811034080701401101640c0200c580e9504141c0f41e5059202001ca5000f2520701d040010800110820361410340580b606c0d10342514107005800024042200e501e042410 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 295663597 1250 295662347 295662349
    0x3060801050c0a0f140c060a0e0307020a0306020a09030501181a01080705150c010507080a0c1b06050a090f06022205011233080114100312020307140d02010b 69
    0x603181c000c000002c5200d1070040f80560455102c403c0c4d03040744082c0401e90340348541ca50340320310080c09618500e0001d00310500300100180245c0d4000c008034405540b09200c00000b580d24840c140007100d90105005907030708000f05060b61224583d9001401a500c0c16048526101c883c0840342103040c400c040715030000b010445095000301007030042c0462603200031824081403d106a030060000e2450421a08140c940040142540c90845058001036010313024420541047d014031101800b41e42004440b1360b4455003c10b981142156000d0482a120b82c0481c0700714100b43d1028220980224101c00881e20500f008400b035889907900c46040300404140800034a9404840c03130079228140d44010849803082d1401010b481c00401103490140350380d9903900925a050027100c291444500c05020310742c9003200003400c550f903103094000d03a50300c81c0023008903c40e11100d00a050f603030b0018159100e081502030480c80c50080da6802820420004640f10501d0f00014040e110b10340da070360003404050b0f82d1034 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 295664847 1250 295663597 295663601
    0x5030f0c03040f0807020411040602010e0c0907020316020607023007030b040f1505190f0b010504150c0503120108060a0e0c1002150c0c1509030702010f02031c0c03060801 75
    0x21000382002d00c241010600140d04d031402410070a000138400f00d01c000e0b001c0c180040c0307030740954052801f5030344da419044410b060620801400303910032035640a00d4a000d85001c0e48a1144102d00c05c51900b100600700c0865072408261601d050700945201012030340c081b21111020071200c00c0c9545007404200f9030003008800110001035950208500040f83c45a03550384a00600382c1100300c0d00e200d08010504103c00d11841800d10600309041c3c17160307984011000c0c9104541c1640d0034002c8031410282d20807141c0e60404210b030110703031810390742d000020008c0d102280e0706140e104008101c1c1c0400600454419005000c2c04c1c1642e0303012054030400d44070000300d013040315803501c1c4004e41504906c80c0d10322940303402c1c10303460004115401510314041c070031140e94002540842e8100d50b501c001060b82c0440007010000003441082c980a030202e1130600340354040d034a0040b00300003410420101503525280f4030074001e5a624800c0c000c030752805034200503010b001400c1c2070600307400000d280ca000017070000814 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 295666097 1250 295664847 295664851
    0x121020c06220210030207170a270b070201090b1314030c0d140106050d0501050a0501050316090c0e03030307030e060a06030c03141905030c1b2d030106030305030f0c03 74
    0x2000b04111110055800d02043d40c400c25805014180c0c2408100d000c030754000c0e031a10080c00c40c4c0f5412580d0300f55240e4041c00202ca4031008028034160004030f01d082d8054a1100f07002d0301c00e000d2031140c0391708252004071002c154540041c0360644011900c1103038115850780c1070342640c1c04a00c551a000c0584001d1680d10341d000c0410031741c88201408000041035180d4540f04a1003200000420155101c0c000701d014090000001c507140d030351d900f0400c01c46e82d507544900e41c05420114064103c801010300c1e485110400b82c014001003960303075020303c00810701076007490812400c0a41525105e280c145005401040341c0c45000381c80c2d008002c00110220400d209280949520003481416a821611950140b052041e00704100340301e10f01e18228106050f590400c2c1061283c0010360f41e42d400090326a0034262051038034422407901e200200055a95118907003440ca15103c6049210500f81083c0185071481460880e00340d480d001c0088240f42e8000e00031846100c1c072600708a100e0726102c140130254803003 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 295667347 1250 295666097 295666141
    0x3060106032d24090e010501050607030810090e0f1c0516020f030601030f060c0f08060108040f1403041a03071b0512031e0f060306150121020c06 64
    0x410340c81001078441040000212201c2d1200001e000162060030760420694200e541c2030a400342008005400140c00f17491803643d482002071186503d0309000c20054001c1d000010b0078403400c0b2002880030058260881c0082078680410b0107000528004913450340e200205612290141c0745e61600c1d150451040001c030890103503503a928003541c0c40f02409440140c540101e03401940d5409521259400301b20751406103024640b01d031103a10311440c140c412034001000ca1824051840d402c403400030b03009000583c0c000c20030300705509195224a440d2091000d01d4000506c2e045400b103151400c0540000580140c1d0f20b11001108440c140b418080610702084a10400089600090f080396100208600611501c1b801c03c544010402d4416400c05400490301c80d005801002c01604003420312100a40c0c0140111200d15040e04241c1c0120303859580042808100540c41d0881021603403040c1c00a04914060543c4030090b6030340c030184400650f0165028440910400c008260440140381d10f00d4008a8 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 295668597 1250 295667347 295667381
    0x30c09040201140f13060306080f0c010c03080c0c0d080601091205030f1b06070c12170105120a0618020102010e0f03070312021b0d0801060309052a0d0b060306010603 73
    0x301285500703000b5030001c40a040c0110f0244501280303460040c0d20344d0064446907c1c041862810031140624005641105401c2544110700c1c10a02d660000c428080d5150035151807900f550700d1003502c107040e00c0b940d03070000071381d12036107440d404040d6000402500420742666540c01250b55004060088501c145024005400401c100750b56601580300500680844100c1156401c6002c240784d4105501110326801158044461004104a08250207914007217420018203040c9071140040c0d201505002e00c0f030058a1410781c82403080002c2280081b81a44407500307109190840c9000d0500c41c494400c12400b40d8200792588001c49008282c021102c01840011b6083c2007031a1001c03680701c00d031850054a0700c3e9080101c1d041c80390b0b80844400c4500074030401000c140c401c018000740039001c1680200304152401800600203000070519001c10900c03000301d00e000002d18490700c0c0381d6240b40f01c2c1055100c0001d0991000700020840c032584601c1c022410783e0300c260b0740d444080d000e850841010303601c840 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 295669847 1250 295668597 295668617
    0x406050106080c131e0e07020601090f0c020303060d02040b100e040c0c05100203150604030f0b0708010f06080c2b06053718140a0213030b0705210105030c09040201 72
    0x103594002c64442c00c1029100405d083d69903074007840342940207460000050300580014030048505010384803c40c1c070003440401000c00340ca14002d4907800081c1c2f04901c10807600c01c1c000c05641e02c1e9002500e40e10001010040e840c40410000f500200500d450340f4000c5040036590341c001800b5480703505102e40c110b8090108e068071566150b000303500081100005045402a494079615000d003d0809507102d100780a0603450300b81400c0c3d0820b0b6008100c0300412031080010b00c00040610b410a04444a605010415464034034025400d4040c00c0900309010403000000c1403554440784030000903460409040220540310340c01e01c2030340c0404103480c84500790454448000380d140480d40c4100d43c4900d41003c80215107505c0c01d00150030142000058a5803242042c0c111062004112600070204003821032030000b02d20049050041c8030301c406440084a0301c0080c4c1c219004e86c04a988004a4428150308010210070b810149602030080c14001d1107040705100c25030910901082c002d9030161581c010803 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 295671097 1250 295669847 295669859
    0xc120905031b070f030f0b100501020309010f03020c030d320123040504030f020c090105091501110f16121a180106140909071409070c02090406050106080c13 69
    0x8020003081c20290b501c182000050000c81d8052418003440c80307441851690185824800542c2c0005020320030b602e126020204944c1c0e0f000401c42c1d0200c00700b82010030424a009400750004d002c0e44c818000580000a13410b55025880e03403111002d800703011032040c6040407d080c03920704403408a04088407109000014001d0441e542140300440304901c02030030070800c554002c07800703903002514100d001c10084484050707855010301c1030744184202655604165827606c40082c004400c0a00300001030310301c01d6180c94040c0d1140107141103484044d01140c0c840509000400da8801512500700d00180c078840010a00001140c6089199500010f0740104a4030755580c071086040042c0400c41c2044035004040d075240000c0c06404000c20780c4654880e00c0c0c051200601c10540c1c001000c2c1d14003504003a905120846843c801c61444890940b825001c6503128881511300c0300d011140a98010107a0302000104211a0402c5040c0c0b11207503105400e0362100f4041c46c4103401013041d0b040f058484480d09000b9 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 295672347 1250 295671097 295671127
    0xd0c054b040906050604052212020109050a120e09011d0709051909060608090327040e060a0b04150605090d06020c070e091b0616150c12090503 63
    0x2100c410014000510855500081c0c111405884210384603070303c58003042040e144ca8481d0395400155401d081031642680d0403422600c9601e030303100420b046000003400c49403d00c00d51202c7c030000d602c541151951509800d16802001070343c02c00300001480040d022100f0b0a000649504803440c024984810b202c0c00d501540714160f000300700e00700300710350420001211358444030403180c029440011100c0346818002c2103000e44609030840c1e0309200c1e601040c080c140c80300000701c4101c01d40309001003001c1c8990705240840c09200032401351340241041c0b001c3d0350284001c65041c1c011408804200001083c25013800280d808440015114103a010010054180114003d00e8205402008680c01407040c2e5900c1c412a0454090b40250340e10075442444113080b544002ca82000c0880014150410041034100c0304800070028903000c1d03040030483c400c4d401d190b44c000da202c2561111000c4036401100d03401000400316480103000092480b07a050b00d4081441c4103084200741c0002c0550310b0143e40d0481409 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 295673597 1250 295672347 295672459
    0x105030c1f2a150c05030c07080f030a0c0f0e21070803120709060302120a0c1b05010e1002190f0c080307030b0a0914040308090c0d0c05 60
    0x8248525211440c0b00098a00c24241c2d189107035400c104030b805030500700300c0450488400d00820312407512002150300740d00319059940c000b1201240f80d54aa0305803400d40d10501a20415821100000c810b001d0f210055401c200c200402c0381d80d80c0c00c1120062603080b10003c150403405030b0070654000b45004c041c00340e80c801e0100c80c40000c003200c0d0102c0e51050a180340d03601c011000f4006c01d05c030006101a00341e1003d23a00005044500d01581010700d203000454540c20094014000d8a90700d552042040d07004d0903035841c5000041c1c10400001085040050107010480802d80c03080c06810184100038a80344291159188450140494000c80000640b5000d5217000342d401881003444407a00026801e0700214400e0035039580101c1d44034003603130074003021080d207400450b0098100740d20441c8104400603071a41c000e41520701860070fa1a01d00308c80b130424082c1804103410580c00c42800c000e008142241008a0710103a4180c0106d08165020400d6440c0c030700d0b0300320384a00000a11310318040f07502c1d4a03c2 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 295674847 1250 295673597 295673659
    0x31b06090a0f171606020c04050403030b06070c030507051503010e130b04110103180b1302040b1818030903060f040206041d0601140903210405090f0405060105030c 72
    0x220809441e5182d1107603500071580540000c1c40b5448070a01d41c89410700084240030008400b00521074213004019440d81817141090340120f0307580f0001818144650019450303400d004e00784036501c0c5d15609052211b0301e92800240caa620a200000485042604910904d40c100d0141c56065234281041d00e08011800b030415240003981e803007404c2c0440e50103110f080c01103100c0c15624481d4104900054152802c10707405140c040c411a29110100b81c01d0302140f0750003401e500070100035030618800540200030030303030715036801042e540c0c00c02e0341909400c100980280b40602d0000d040c2c1925954040d1f80c3d00c0b659034a180c060300070705e0104010610f5140c1c034541040c801410340703081a4403020300c0000309413069421002100710100744201560003000f079141341c48141ea001e0380b42c0340301c1001083c2e80302c404074000014035805000380302e001c14048096501802000b00100381c4c0e403c0540359015800b0003a14280d45600900000058500e00007038500c9050b5405042181c0b00020407403681d001d0140b0362500 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 295676097 1250 295674847 295674859
    0x3040507030803070f0e06040f06030e011104090905011a210c1f0e1504050d0302120c0304031a04050c01030203060102190b070f0305010806060415030f0303020711031b0609 76
    0xc4005582503010350f00c250103a54682c0c1000010100c000c041502e100246c6004a03c100010300c441401c15060000352005400c0c045980f90114407003d0050142e04039403c2120320218000ca102241034011481d218007402c0240600305401c59034107003540c82d420f1055803164410301c0003039492a01503d1000604170600644507582c08000c0460340300488240b403182c21f4106c40728075440d460717040102c601800605450144d8002e0800d21440200d208500401d441380c0360802c030203010913200300a0440846490440707240c840c2c0c03014200c2079070383d045804100c50281034080703002070706044001c0e00c42c46650008000c09203000c104d00150001d5001501041c118080c1e2005000d903c0c0720900503490162040c20000c050345880800280b6924003d1980d10425081000400810200081719a00b0040480300002c05245c1d0f50540d61100704030380d00050800d082041c04609043d00341d0b020305101da01950208844010341c0040507203914180713166114074541200f03001801d0401e200505080d05014080c = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 295677347 1250 295676097 295676099
    0x60604090908071e021017040605061207140103110a21060504140a0b0301180b06012304050f0604030203031b07080318030708060708191401140103060b03130803040507 74
    0x35044c00b0b82120440d00c01c2011100c80d064210308052511541c80b00c0d044c5070001c00700000f0208000340302c6c1c001d40068400e6484002042c0316a6640d084c09011b11113460880e001c081c0c0d210501c6101c11401148607000c6840d28080066101c51030080351a04059a62041114420119245880d040d40c008582c40035a60b01400306454850f03100700c41a80148003288202c1d894991080d20580d900c1282e501e0081e4181075400c0c2440e020a04414805c3d82e22154005445e17581e040121aa14100310030a1050202201448a882c84076401001038031410398503d51094100414008144182d00c0025010341c8104903038045001d40b180035461f40c81d0003000740c41246507520203652031508401415039005403007202c04131007403808014240c020220040500710314a060540038000600041c02d440f9505c0d090200142000b4090740880209014141d07200c260b075854191504241042d1300e00a4080f0b4540b00000c200741c83d23644c0c1500e100e41c001d07541010305a5816941c3c85aa908042c0013160a807080d210 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 295678597 1250 295677347 295677353
    0x1905014103060405070e0f12030c0d0f0207060305100504020315040c170604060501090608070e0315011d16180b0d09020a0e040512180a0e090c010806060409090807 72
    0xc000c80302a400041041c0e101c2c207101c010001150800303001c030800c0c40035064404405440340c0e04446805001184e0b10403008004003041d40c11481164000b0480d4000d0240c4a8506500044220300b8078100780d0855030720035121507054046510648908500e2150003408009520b0150020340d8400031074660111106060740200e401c0e584011128000b090b1114045510405041c2a1592040c02140d05015030741ca030100280509810340684010003507080005a4058080c60b0217001010000d01205c00101c1640804450703031500380122000410091001c190307148443d0f24541c000d5424410780d50720603851500c20b64031040b035840e00348a246a4110006038508940b00903160084c251540407507425824070400501e1044e5812001c0c203042c5d030300c0601c80440e400103948a1042980e00c21507940e2041c1503100c0f007030307001210400703548502034100204010310381d020360601492040040b940c00c5c80384440152080b4104075003180d040300082c03104101142d9240c100301050343c05030780e080d403038003201e51 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 295679847 1250 295678597 295678697
    0x1b070203070e0702010b1e010c032a021f1409011101020d050103060b030304080d140f1c0f0605090a090c0f23010912060c020705040c090302190501 65
    0x10b4008107001a60800f04010182c083c01094501501150307111890104200c542d108882c26910190420040c01010010180112111110000d00c1070b02400804510890100d0040c0105012802840003454080d14107000600884800d040d81d156458054900010f080b55504181705081c1004015074984410401c00c3c8000d186108000e1000f041c0e0350f0541c1844025610840050340c0258800c000c200b01050780421b6a0788039080303074138164944614001c880c06403030003040d420070b6550700000751030600c100342e558601d008240ca1207424410b691610003030008551852060030340141c44403000a0044550707a108800a91180d40da4025664070b481041400060384d41060300c580b40c4480500c01d2004610901d080000401d2801810302d41c11300519801d401085000100300355103c840c41c1d40f40c0c60081c002c0d0009441d01420412011170480001844480a8070050f40256001003d106100004281490540c0c4040c1c441c510020035002d030011460072104000d0b00052000004003142007900 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 295681097 1250 295679847 295679849
    0x40b040222080c03030f0a1b0c0605031b0301120f020a173009060d11270405010501020a0f060902090a0f0f2c031b01020a080c121b07020307 62
    0x501040d03403803030510b111240f524030019242c9100e0742c01484164404010342048603240746251a00b02c0340b01c421403000c40502c0d10000b00040000c1d500d020701003a6030b80d010010310f104000c01c10612803040d40c2e014440e00703035110a0007424080556840300c80302040e44a041c0b1700c440b42c405010707110030b07940d5034401140c1028501e007483c65a42044003015184000041c0031130b1041001c120510034003010a00c84426842050703c0c050081030003003107951038803440381c1c016000e8210000c0d6407a0780783d500110511400580d82114001c8600c0704044102c1402c10380701e40340c103071070040e001410080d1460f00d840c640305091100440f0b0f100d88405440006803135032030381c6074016510100089030b1034503401c10f0031050b2541c20005407082403070308603080c1d44500c000802d160f03030302045580700340310b10f50710b0b641c0c50705611a0800d00300c1c10000d0200042052501503008090020300396a0b10b2000d511500104000ea1248180303404001c1025000706103c030301c002021b145420006c420491a24403540d01003401c060003 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 295682347 1250 295681097 295681147
    0xb0105071202060415150311060d0f0203010602010f021201030611042102090a050727050d050c04050c0403030903060c030e1c03060b1e09010c0f06050a060603050c09040b0402 77
    0x750240302c2000080c81603500c1e109402c0c4000e0080750000740143c0c410302013501c0090901c01d010844078442752101c108840c0c0030610a4800d1050740c458512102c00382d4020320074000190300c0d2400138000d0509602c2614650440e1118183c00b6920750380700d080190050b000b0701c3c48208410400098440d944c4000e145243c604d1070340a215201180c0100810395030002c180000b5941000100909070794000705050944d540024006100c1050582030f00d070050950708420f81041c4001503030010b10000140501040a0481c1c0c103101c1030b41c0e8400725003e1405103100060100e4024541400041c0d103d40103038a44210b540380c0040c44440b48e0f10000e190061a8110b03d020710aa050464209d56150181102400000c0c4c410b624080c80d4a104040400c40c04800040201c0040380e08c1c42642e124101e01a19582c0050480040809a003051001000191110303803a0b01e00e49100000c003280a40a01c600c10007500740914103140c038070001d10024280133085d107588203901300404011201814114244444 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 295683453 1106 295682347 295682353
    0x5011a071515030516090e03041a0d060306090b0601020d05070201080a060f060f0810050a09091505190b030127030e06181c0302060a0b0105071202 65
    0x20b05880660000b03401290004240000081d480215019240521185a544440110450b81c0c02c071410500c5400a100400c003806110740305084800e4500c94040c0351142446558003101d007581c1048074840da43d070a04006010159680030352114080c00108155028003401030800d0207400030003410400140c0010340c0a4000b600004003d04007601120342441d1100c00140c070301101c002d079281c00200d90200103034541c80a000c0b01002c581e009015015294108940c45014058559007a141d81c03010b20007000d000d0143e40700d098410300e100c004008901d8040300750441134804c06001188aa8100704c0c0f5101003070080250412511084038025040315414074003680c64040c0d46003456406240410b10400486c181400140c040008849402402c607002c02002513801c0f58040c09001a0301c2807002400742042588600d0209405050080c00d2504560b507100d50041821207a40050b0 = true := by decide +kernel

theorem cover : BRFrame.Cov 295503597 295683453 := by
  have h0 := BRFrame.cov_init 295503597
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295503597 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295503597 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295503597 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295503597 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295503597 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295503597 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295503597 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295503597 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295503597 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295503597 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295503597 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295503597 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295503597 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295503597 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295503597 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295503597 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295503597 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295503597 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295503597 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295503597 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295503597 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295503597 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295503597 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295503597 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295503597 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295503597 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295503597 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295503597 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295503597 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295503597 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295503597 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295503597 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295503597 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295503597 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295503597 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295503597 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295503597 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295503597 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295503597 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295503597 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295503597 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295503597 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295503597 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295503597 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295503597 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295503597 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295503597 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295503597 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295503597 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295503597 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295503597 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295503597 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295503597 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295503597 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295503597 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295503597 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295503597 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295503597 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295503597 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295503597 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295503597 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295503597 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295503597 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295503597 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295503597 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295503597 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295503597 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295503597 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295503597 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295503597 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295503597 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295503597 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295503597 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295503597 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295503597 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295503597 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295503597 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295503597 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295503597 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295503597 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295503597 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295503597 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295503597 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295503597 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295503597 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295503597 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295503597 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295503597 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295503597 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295503597 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295503597 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295503597 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295503597 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295503597 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295503597 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295503597 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295503597 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295503597 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295503597 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295503597 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295503597 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295503597 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295503597 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295503597 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295503597 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295503597 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295503597 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295503597 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295503597 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295503597 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295503597 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295503597 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295503597 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295503597 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295503597 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295503597 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295503597 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295503597 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295503597 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295503597 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295503597 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295503597 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295503597 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295503597 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295503597 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295503597 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295503597 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295503597 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295503597 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295503597 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295503597 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295503597 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295503597 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295503597 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295503597 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295503597 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295503597 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295503597 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295503597 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295503597 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295503597 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295503597 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295503597 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295503597 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 295503597 ≤ n) (h2 : n < 295683453) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
