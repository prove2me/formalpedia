-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0810
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T22:55:56.142096+00:00
-- url     : https://prove2.me/submissions/e44b37f3-da25-4f32-8c3a-43ef263b6101

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 145503597 ≤ n < 145683453 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 145504847 1250 145503597 145503599
    0x15010e12120d09240f0b0609130906051f1a04030201030f0e071e0902040b0d0c020a050f01090606051c120c0c1719052109030604030315080703030212090f0307 70
    0x81d1644190140c0394800105020030005e41c02880205e13405801e02d00d4001d51b080041c883c0301d00d094901d007a96142707441c10018406079180c031290102d480440d403001a06032054210b110f010100240c502c01003001102d03400d00041000c0380c590450095101c024140b548030700c2e00003242030f2550440910b030380c1200c0480d62115541c80e12005000e060002d00383c50702082c0786c03000c5080183ca000700d07010307152411182c5203089983c00140b4010800140303c1c20441c019109840d0016000703000e542c004080c4a00041032807200c2e400c0400442d00c8a90007076214104c80300d0000c595003240d105044145c0c0d0002e01c42a00000004020395507165a050020310501c0c0240010815202610388215a10600f208891500700d10f00590012500300b803070080c01c030394805102271a0480040d50031000d00d400448001d07040890000c0841c0c40e2503015242100401c0c2c4134214a9940c015407000c2d40f004140c0c0200070081c0d1443d6841c041d49442d001d500c0030180c25400126180c40b034580c0079603117040040103400c0710561 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 145506097 1250 145504847 145504883
    0xa0504090302330402131404080301090606080411010f09180504061401210602070204050108060601020c060f04050d050304080a080d050705040302010503060906120615010e12120d09 80
    0xe003400078440300641030303521121040384900000384200e507180d2100d500283d04c0329020821401c010200c1c0b0190706807500701800030b80c04010302580c000c1e48039400715a00c0754100280117082d1500c0c0e40100e810880044200030200e00000c13039080080ea400c1c01c01d0b083e5104401003c0b950521140c12003412264412000c1070282051340c00141b040e40546802c01030404119881c8980c07003002c2c810a001d810050201c0d4400a001034040c0300100d11540303005140c41150f501080c10b86009a10180031b54000d0703c100030540d601800003515071101203407000c1c07808404504080087c0914090720340140c00c8800100100b0404004540182c00310ba4100c0e04140420f15200d8ac039648084d00c03240516082002140c0c00d50f00500949007034960503115541503075541c030144080b8110040440b81d003c0d14801a0136a1080107101c118060480d04442c071841c2c41c401400034040b0000280224002e03142c45110030725070707540480c40c920704030101c2c032404d944c07401c003400e8030405050340d0f92000e0900001c44c0100066 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 145507347 1250 145506097 145506103
    0xa05070f051513060b030c1008091501090218032116050f07081507051803160602030306041424130c08010f080f280602070c030b010509070903110a0504090302 70
    0xd0f0a01c07960702032003241c0300101403540703400018400fa5000840c804212401a00409415134025021001ca40c00d0814000c40b07154038010a03071100642545c0060b400380440301b0319800180821069004042c03000d0b5a203d03074442c0d4a1403060901241c0300214043c08141004041c0301c1c030141d00082117440e0a5420020b01c2d859103000c3c401c0f00305510a007440780c111024144a4148030f1801c5840e118100080d1803840c1c0b051021510307441d945030240359030401140b1032108404000d40074903801140c90b0318028051000720340311a0580c140280c203020400070400c003940d0f030500701c2c1c00300d4190b0701c1c0e460004000403d00e046200c0e154200d5103410070070720480c09035000d09450704841038512190080d990342c0d2445030303c40c4607241468180c0e420440500001c60350b2107800d00600e1488200034090001142c4422040340c0011104440c020300c9420100188102050001e01401d000c845002c05820300b240003501907496840002d1040c804030038010b10581e110718211b8002d05000d4001d00c0f281382c030341c640251 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 145508597 1250 145507347 145507381
    0xe011b140c0102030109052211060a03060305191202030f09040f060b0f03040c0509090307061a04060914070207080a0b1b0406022a031b03030c0319020d050a05070f0515 74
    0x21811511031986603404d141c83d18004500e40027a405034601001400b40070076584001000c10901d61903020020028004015980c1002d51040d030f2441c2c00c44007440c003d80510103284034942158012704c044040507001d8011550381070002c64000a0000d06034007200e014080d00ea00c40e03c154940820340860102480005600c103e1280d4904503100b078654040155580d400d48078409150300502c07072840024065800440202aa401420410314043c80010140c4103d508244130443c1c80b5400c03039007034034a00030042c4c0e004103050002d84003490800040c01d903240000d000c0906010041c0000c07034100341003041030348005071404900350b681d030b5102c030401303035031011561030010700c5004141c04580c6500d03229036210070a940003006030082103000b100890300044440d0700c02d51305000411050307000d00e0381040140036007140340d4070400031082c07040b0700a418498400c10240074400100408180603900c40100c1d145641c0c083c0c20291032014605006d0702d44162101110769050124046c00800303020840743e14 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 145509847 1250 145508597 145508611
    0x15020f190f1101090302030d020120280c020409080406080a0b030706050c0c030a05010b13050f0604090618030e0f0a03170309032206030e011b140c010203010905 71
    0x505a21210035414000a00d444405454107070030281c41800900050500a00c0d4081450710b072032415240e400190501b01200e08210243c1e55605c50315114005c2864054010600e200c22a030401c0018a010818003001485520404603040100810300d406188029003150f00503104003c082882c0c540040668418021000030420010009070b529402c1c0c061a0710480000c3e0203058501e14040d010341350b50700043c000d45098020b5000c5001203440c01c000c0d04d5a414064000850200d150070240700190340b10310030140c0c2712070411041000414001c00403503089002503900144c0890a4100303400204204940800788501c44809074040c51780c0a0010707980800212409001c04503440d0030050082a1884000c280400c160340b208602041c1314051503003c01d0742c105481c036156513518500905840194280303c034150306101403101c04d6042c413407127412402034002008401900201900070034040c0e80d450040100907020046010056015140a804040001d45d01c82d42c4940d02100548000c135524 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 145511097 1250 145509847 145509853
    0x20304060f020a020a0201050a091d060414040b0112021503100503070f030c09110714070e0610020a12020304090f0204051008010506030a020c03070b01090c030e0c010f120615020f 79
    0x108004207110b10807141440d103c3d4005200d0001c8540c0156420b800c080324083c28003135183c0001031602c80c4954541c0007424820a105c0035458420100002c50f80b50340082d0150781d002d00d00f080006445000f0041c1902d0018403011140e41d09440055081d04000700340f4a4821804001c1c07101ca5805656041d066034070450980345042e496040b40340d103407a03080c88003070586540d5010400000c14503a2102500b40c0c60209164030b080c0480c7c481d24030126461121a0705903001d26010850f40b40001e0210b50402e00c2250030007104070f01080025a200f48155002d004050200300e8060784600801c100d4000781807103802030104034010190b61000b5000791140714090500445d4000282d846610218180d50008180f1802c68440e1103a02000b50429854116188030401020020070340030303900305000f081c480c2c0c0c010610310901c0304001c00386d91104605500d075074481200d42006a8208004d010702c42c410385080f10b0070b09582c0b245d44024109582c444030f00b294070101c810f8011680424484c01c204020421 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 145512347 1250 145511097 145511111
    0x10110601060503090a060e010e07120b07080c090402181002070315060b031609050405040f061802030304090b030c09010305070501081f0308310801060e0411060702011403010902030406 81
    0x70a440611048440d6000c9800101300b1100040361680010354440d2a0f2000041e0310441a0280b450115507410045004800c2d48a000c01c002003048090340c402040d1a005d411810700c1c2004000d43c0c080c500da01742c0b0440c1c01148006c07140c200281c0080c00300c0c80080801d04000f240303c001079100c50079404141da500c40c4010100008201d6402100221900001c00343c0ca1640c489182c251100101d150040c00c024031000000f4650303885020320b0b4003035401040b01c00c1c90b05807140750140881d00d400035030b43d9a400f031000046000d642c004c02900c044074800840841c007041c0c2040024240503107140101c1c1d0200381c5400210600c000040d458041d10f0b02a01c85200c81d8881c110304c2c130b40402c0d8206080380021040d00081c400960b6000180801c40c501000098489a103045050b501070704036404003171680340c180c4c0104a0f102090007450000c007040c40400525082c1a26545810b542d2800305034058100050f000e421a4801e42c4040b00c5254078488160710707543c5030b00207803010b0341c406d807000c1d0744103410022 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 145513597 1250 145512347 145512359
    0x60c02180a05161b120203040e04050303190b01080a0f230a0b0a0f060c060207060f290303180a03080412030f08060d061d01090804030c060207032604030210110601 72
    0x13008980f2081c01d5401001194440c2d0341c1c8545030004000900c00f140801d2200041360401445000c0c065031042c00690b41340e02d86400d0806800c1e10300504041d116040152010650360010f081a8105003500d0000c2000705e60001c031a00544065401c165041c400304000caa1844000b0302c4003402104250f03010310203000400c041010100c0b2a0040221440c0f0041c0200601b0f030040900c1030002d07200f1032001d4105481911410304581f24189040400764494146640303000c050070740c2c00d40b40f6000c82071940726030201001080ea04d0080000a509064040804032030342da4800310040d005590003807000d580d5544071402288800c082050487c040b66681c80141241801284818802c81c0050003c802d402d5590b2a04c10142800712080c0342c540c0c000c40440e400c98042805009007840c01108225a070740c0c0795140c801290704aa5200b05d0031504024424000650845004c0103c00c1c45c0340c20a4890b80c11020075607080f0b104650000b9404084400b19201d07050304031030841a68035001041e103130aa0b80e02d40c = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 145514847 1250 145513597 145513607
    0x3020a050705061306231204020907022802030c04060b120112030806100c0506070e01090902030c07080703050d060e010302030c1002061303110d210c09060c02180a0516 74
    0x10340d0203110304c5800d5040c00320074800c00801c1080a44c806090300e03406458a202d82440d07110020f02ca14640034181088150300f040d51205410404134070050010200e02c108090180715607d88018284050400403001c0d994100003407050010700030420060346035a203d0072140350380002004003c1254541c000100012001105603655070141c48812440d0340c0c3c80104208241da4041e0f035814080589e1042e03021541c00c115040c49030702d0b180c540302e6064801e0000505102c81d1680840d203c5401001003081c169412010f0346ca03c2984200d01c1c9881305954a402d4615020303180078000201d181110000303141117001c0403c0e0480740281d09440449051100340308403860307034202010250f4400c001152080d070029500d111414080c0c82c01c00e045c0300c9440c1c100c509111000003504001461810480040240b6504120003582032040402a0300380c0410f01802c501154881d950910509440110564071920004165010f08610f125514a004440400206000d03108000e02482c92422005c019000f0 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 145516097 1250 145514847 145514857
    0x1503060302010e0405190c020c040f020c21040308030a02070204060b03060a0618080303091c180e07120e0703050c01050405090a051005100f031506050a0e0102120703020a05070506 79
    0x696030343c4400311a030800d100107003401401019404015121944030080700d40b04900c07580c0550b0303010b8100341025500308016103401c0300801c41407a104100701c40041c040014010b411003403102e005100c10300012043c4060740200c4e400901400d40000c100118180e6503401402c1e00341c401c41c2d0422600b5101d545504050000316441c0303400000c10327002801100d0150500100d42e45071b84924140081d111000682560403d86211f519584404e21101c090780324a60f0813074820940e85400b099109240350440c241c0a000d2250b0b05c4074410000100380010700c95903c090040c40b641d50184242d5081c04034159440c145c078442608e103401a0555003d0940c4520308542c119400200b041e00aa00c403a0500d40040c94050b190b840d0005c03000301d000506850303d28107005120231a460b2116080003442c8050280c030081070001002030301d62002030000641000603160b84184620b41000c40fa10b0307810040c0d25180d0700805c0c440383c843d40810b14008041c4c1c000782c1441058401ca06031840c040d81c42e010f121482c016 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 145517347 1250 145516097 145516099
    0xc090d1a0a0204270f060902030402091506040b0d0f0e1e0f0c040e0c101707090509040b040203010b030303192007031101091a040201021b090105040b01120c091503060302 75
    0xc43c04c1480c00002c0a80303034030303040010018005031007036a000c626400c5440580c48801c90300d80200410080d4501414902da100c170308407604c1d0076031703002420020348144964000c1c80c8040c80301142a1540d00001d6021603c017032061792082025001d00300b640e968071451a440400512440003c1c00c920380400f003400d6801041401c01071028000b40320800010341a40000905284201c0e44904c50030307503907080300d044400030b583c58030f000340b069511401ca0032000c010400c2060081c15102006070780c8400c8030155200b604641c154903103482c0d82c40013170301401182144a9241c4400300c240110500e104c00000295002040308102d4200c103141d2041a955074040c400b00003200070f0000702c01003806510050342c0010707124000640100c07a41d46806008000701c4211b113090090354200710455130100600811a035080354034030a144080783c000b607011281405210300031600c400d40c40500b64000c1c0618800400180701c00d10006000c070f10024040c11152041002c03100b0684024107589000b403150300d06403a0 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 145518597 1250 145517347 145517369
    0xd0201060819210e0a06080609070804050109020301050f09070602060103050d110f01020d0204090501140d021203160807020a0506030412080711010903210618050c090d1a0a0204 78
    0xd40c4038041c002c07440410162511a80302c0c428200c44105916040c4120200d41c407603290741e019007001d102c1c80091942045043c010f000043c04029520003a005602035400c2c030304030740603a4452811602605c2d10703000c002d41541c201018030280b03903a0248043e00c00c1400c50112800d243d5166012681c581c030030b11025180303810013180710f40e480348107000440200e550a41181c00ca00180d03c5d01d142244c1c082c1074103e20450780030800b88810209406072174018401003842d140c01c5001d000c00900350404100c00244504100d841081c0b1245062060300d0340d10150a40d808007a03511820814100d90080d40124800d070040000402c2c0d500e40f90056a0055400041c030081d50b181c4c0d40d00c1503411820280400090040c04100340d550944240180c0180d50301c20b1351030110001d42d200d916107100502980384c40c00117040c9041440201140c6a00c448480900c2001207441d40340d4404d0880980b041080141e00a0404100c032820300001d507004003181300055402c0340c01551036843d154100d005034095204814 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 145519847 1250 145518597 145518613
    0x50405010c1112180a03020901080f1506030319030f060e270a03030221010909140c0f010e0d0602161101050310090902150a09060806060909160504090207080c0d02010608 75
    0x54940d0081141d420f026281d080e17081c0c1c681d0002501550700b64400c90040d40412290040d031032050002c0c101e0070003049110102c0d81000c0001a03228040c0c02d1742c0c00c0c44100c3c1300d6920f41405200f504400354601150300300b0444651910540d0700b4040c4115005020400c1c241d80002c89000031070003c18080c0001c10140040c01c1507035030300310f000e540440c603011400000103442d40100301190b1200340c000c12064500180c00c5800c1e00c3d010000c29400c0d0090f82081d0003e041540729519001c80e0649a0321091901c01203802a003000581d222420440241141d1b2012404d05041c030040c04242e04038034001c2e440329013081900c0f00111110322045034000c00100101d18100015041c940060042a200034105d4015186500e0b02c101190459490360b400164204020000c4540058456800600507501c46240c4455000800d0807a0009040341040c4002180b048440394030900c1960003500341d084080d50340d1344281c02d040009810404000c7c129004900c0e240e40c51900510407a01225265000f0305440 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 145521097 1250 145519847 145519867
    0x3080402090c070c06080906060301090803070309051005040503090306090c060702040509010905060a1505121c020a0c061e0c0b0109020906090405011e0608010806160909050405010c1112 82
    0x2005015000c2103240000344402400202c410302003c028040654070141c8900d8a03070103181c032380302005d410540240d02d013019100c0402c82c04011245d2100303160a003c210000c0d81c5c50700501e4450984001a4068540340a0004208000c40181600340040b801c4980b01c1d2225800070707448848401125a02c11002c10040005003450340009501039811000020309881589546090000454201540e070760b80f4000c0040f00220710380880060501950098038003091485401d5840f010b13030716070000106d085502820002c3c401c01003254180d80c0451001e01607560341c003010b050aa070300035140702d100400c403042c1c3c20030900c212000c0c0d41c1c0750f8106403515640c3c1d00e8051554001c1d40b2174080141c010750200b04403580d940b51801140d000b001d40d034900c80490500da412142903c4512342140d0104000a001040120b01c001480c9820001a003039402c006203420300f040d02e40d0040c0794003051110307045c00c08000900106512120190440b0741f550001c4600e44081203884183c08000012042020f0116100d0307 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 145522347 1250 145521097 145521109
    0x2010e06130326041a07110a11030f0d020703150b0d02012703230307020102070905070e210105010b0a1d0d0206072003012007020a15030f0b0306010303080402 70
    0x4001600b43c000e00000022200708404181c100d40503101c08a000191500c030030b0003c07800c1c1d40e0004451612118070355000e0300e03190304c44040c242c0240404403440c1640074240e0f403d00c144100c22060100f2500560246600a0349500c1c484c0b005407107420008944d445070007620300940c074041e0b40c0285510348240031a401501c05802030040c40801c0c0150b8007210098080b0000c404d400380d400b500036840401643e029242402603131204d194031300c0d00144903000041c2d800007150002d80760035290116203695425000c8816034405070005601c2a4880709080200d03610368980a000c00b00e00c3d000780616070321b503076046001d40320340440c1d8000650111142c80024289404000c20030600610b02d1180d6845500080e00541203282d094540070504003211240c040384000140300c01000390024810945240380c801d0014100c0800d811205c0000501c9030304540c0c0d21002032015111620744084840d40e000350040007001000340c0c1405040c84c0001c8100246000501380303040300d6150703581c841203650301d50034055 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 145523597 1250 145522347 145522367
    0x40b0d0b03030301080a0203010f020403020a0e1518070f08010302090a020a030209280e01050603060103180203010f0c0e01082502030c0102161e051c0203091203040602010e061303 79
    0x541958500c150001a581880254020910607000705600200c9004040c00c603403845c00f50541d03580c410230007000140c9a000011f402c031040c0304840c000f140e4540107000c110a910024896125900a20107001c2e40740718441d9600800180e40c68000c5103801110565549800303000c065409404200001c0403000240c008140301c82d598070700035041c540e01030041100400d45600d5003055100040d0b45050055205010500400d00102008441e52401011548610029054504040e2502007610210241007000155150701600820030b040f003c1407030200602d010b251500019141c038030711514a600c00d502c0d042c02058202000420f0700304120304201425801441d07401980001d00540c1c000140a10250000e00311030f002c204003c00030351070211018403c6d05c0c0805046021881564080b84000403207032a0f140c020050200030031800841645140919607280e5400410441c06056480380070024108a4156030024442909588080ca032a8882110201501e0011905800201e440740c03221a13 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 145524847 1250 145523597 145523617
    0x4210c081305060f0403030206090304060e0f061b1c0509031e0a150e0705040e0a030e04060801020408011406010807140f0d0e031810020a0311070f0e09160308040b 72
    0x10169030b40e44003003015904a08481100da00c0040350070003d01d9018005180d226814101a610349402e00c60003800004450300154002c0100c20503407101a01c402e4200d84d24000c04003200407441500c100141d136140b014000000d44101642d800510b002d008000b5502400402809005401b00c60882551007640c03207480d074074003489442d1000f004034060f00301004084916010204880c00c2141d100f074a42495a40310074080c0d4500031428a02c5880454941d01300b9906241c514880900100010b01511140d000340c0c0c0702e54400940041c0d038800c158003e038810380001801c47c0c0d540d60760300011b5600b1130044a440340030a1212440405601c04103005000340c0070002901400c001c2c0c0b1075614070480f85004020600703540f0010b1281045402e1400307041c41d5420882d01c032002581c0c0c20500941743d010b090802814403a07000300350f090283c428481d600240510008162540da80d5024031504110140ca22808900406500c02003100f0690241c40c00d50790003900c1c82e46058a084850a400c1c0c1c00544a0 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 145526097 1250 145524847 145524877
    0xc1602060d0504080a02010b06130b0915040803090102100209100c061118031905071203020a050a060209130902060412060b04050115020706081902091f0804210c08 72
    0x200c1d20700700502caa01e000c0c5004402c0c03180ca0380240c240103801c45103880591445003c003070102e40010382144c2c0b42c000944054040a07a100c8000305c0100d00c0600c038000b4080000c28000c103010511010000c094560040260f00701d030012041c0310804d40881c03044011550304140404075854015008040c1c01180c540700e4000022510308203082c00301250816441c06412100505030344085181c108502014100100405011000700381e40380c0d03541c1c0d5858494071400200c02ca200c1d40526009003c2054200c1e00102907403424a8580380c240b0081d842164200c0c42554842c90341c0500b00721310711403441d0080c1c0c054072251130035051489228220082c2141220420b448190000150300c0b94041d00c0c0c001c1c01d082122a44030340000030040d09200050f0460b404200c104070030420f24400540c0405034000c103c1d14016580d44c03444020440c0600e030b009603480704141440800c81403a03440104944a14018009544c0d441803004400f100e10440740710795030008652a02140c003060b1100014074038114203141c2 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 145527347 1250 145526097 145526107
    0x306060d02030103050d140a020c010f0c0204050a0506030f030c1906091401060311041505060313050303070f020c0a030209040219090f1b02072405040f0b070c0e0c160206 75
    0xd04050740e200b600211000c0d042900000d00c4582c01c56018604005c10031109400e005003a1f40c02036035807000405d084d0401c1000c4001d1189103006017030202d550368010740300b030000d4070f410707034604001d4902556080e019100744041541e1078031011050b640350b5006031010b070514040740044412051075466040d204940d54000c4600003591892030200c6090300740c0e002180451850030600310240350402424010b40c1003407a107017110000c0c824110103440086840a480e600c94007052200d02201401c01001403100006110940f41c0101c0e60109120850b030071204400c4e840010700c510b080d01d07444000d401550b454042801072601d4091003000340da44000448800390b1b1802c428043d1307520001d4401300c0d59a503440045000c01026940c085041b01400148400c03450801000508074140318800c800020b55090160604e21850459000701003c10b07503003240903103403c000b803a03a5101030412a0308032a00603001610800102c120b512031b10660803c1400c4c0020311284003501c0140b10340c101d80c403190401c6 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 145528597 1250 145527347 145527367
    0x70513090b0108010f1d0903131e061e0302030601111b120601030218040c0e010f06180b180105040e0a0e060702060103080f0a020f0d031e090c030305030606 69
    0x210400a05a9400101d0720740ca000c800508141c5068008004135480480306200c0b903034000d00d440c2c0108640e210441040c0c0d8403c8140ca0541c003458440e2109151405000104850824105000c100082c1300401c208d035911501900c00140d1103088072800003242c0a1900894003990245520a2060508402801812180d9405c0105040c442d00b082501c6000071a0310742030420149207d082c0d1000102200c0d415a00081c8817070340790210b407402866164000400300a808446c9600902c8007140280e000e5841c1d01a66000c4040c900902c00000c0403c0e44003141c00c1031083c208000c40d001c0c05d00c014503200600080740c040082d4000c1c5641400030030400003a04244101c0243e11541c1e007640005680c1c0f020036040d904084011300341000310740c820401403001c03a0411040b981c01d400c1d10010b603a512011a03006030308180401030418014028250710b818015056004408a40c02c44034019515880350014402203d00321030000d0b0506624040610009004100075608804000e10550800030f040c1 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 145529847 1250 145528597 145528627
    0x1c0b0303120f180a0b0f0606040803070809010f0c0b0114041e0903030c11120304060b030d032f0d0f060b030703060e0c0313060504061d01020403020901050901030506040b0705 77
    0x5039040d121000c54100b000010f40898012a08031503511002e0041c4d0320564171290b401c901e0182c075000303600303c01a0200d80c696440000b11002008548107680e00d5400ca8149040c041e0048072605001c51040f041c03404056201d0024030610a500c4490a101c9908103004191410b04034900960850782c0d62031095440302000d4400780d68800002e6020403240c07024035005040e5568041c0c0d00050000c540c182a80e8000049280300c140d04906020988a035101d0800d54090031300d00e2a000d800d4080c615110f005d541c0d16820089240c406a400c0f00760f801a4940c19039040807140d0701096460344148030240c021180b94105804042e04000c0114015840d41304209072680292148408255204020814503e584421647c882030104090342585007041d000340c02c02141200c010480d0356988002820050164012840c4542d200c041c0303e50304080c1012103000398424081a407040d403000d000028141744c001d002a068a5100014040d2070f00c507596003440d08040505207200b84070741440315000c546020 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 145531097 1250 145529847 145529851
    0x70e1f02010e16080c01030c022509091a010b0412140f0105070206040501050a050c0403061d0d18121a07031404080d05100305030a0c0314130f0b1c0b030312 69
    0x643d050100e468482a0303840c0600340500b41d8149824032110111040c0c011030b44074440c80c00d00e041c0c0d000d0090810488141810b45800c1320f05c03481e29102400e4280001c2d80041400d4113184160490180d8854010b03502031b02a42c41451080c020016452000501110903031a486801c44103c404254030421440d0a48404454820043c4c0c0940108400e0202c2409555017100d0455400c011303a0400c0d900c540c12034807071400090015900c4076288904403500a8010b5448140b400075030360b40d0b8103205402054a00303e580b070070708568039a04000c42c0011070300705400341580d400155550b00c1103210040d5915414028580d0007070503600e40003000c5003407025030000d1140e80300f201030342d51798102c50446004848010f410070b00c041914039420300c00200008121038a10b45a428921081c81c800e10703084031460500c61000c009950701041a8603581a00b4615005440e41c1c0e20701240f5803509c2d000801e00600424480601621040c2580a006a41030384681515072000d03050780c0c9004201c0c401d031002844c00b = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 145532347 1250 145531097 145531123
    0x90b0a0507120e090402060a020a061401090b180a09080412081b011506140409060801090b0610050702061e070b061c08040b030907030510020304030206070e1f02010e 73
    0x40001c400d001c201d003030303103030420206643d042205000010b0307000f0039501400200b0003401031500240101041c0c3c000c02100420b00c1d4072080c02e00407510503183d40800c10b4001c0c46500111030415281103806d01d0b042a030700d802404200000085540c8850601010300620748041d50340b0402000702041d5041c0c02600301e2441401003c0e6150340382c04645581d0704840048c440560540d16041c00608105003083c4813008890480c900107803918900c180b04051889213070b00510b000341c585480080c04a2040d0040010103004e41000b64480c3d8442e014400190345e000310740c90010b07504002c20801441e264000d04050042140840f0b200c40805d410071900d0790001c40d064503441340c0001044160f1a182400c2819404813440b110b8551059035103281c0035008a0040740d0b000e034008030024828490802000b80119000030032212448103110340c080081d40260390903030060040b140000c0d92140261007010f000328000e04141c0032030206041000005401c850410119501c4945803d1007140c104039020030305003 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 145533597 1250 145532347 145532357
    0x7021809030a1404150c05010b030f061801020a0801060f020c04050c030916050f09041e03110c01050405011407020301140118051605040312020a0507060807081015050703090b0a 78
    0x222400003500c078081240c00f02090810400040c051020501d002c400e44414074240902598440c0c03034403d02412803504055050301c154110325460764000a070040c090650000800c90540622070790600b41d104038020b90b00480d0680e00104050b501c12216965900030510668280d02201c2000400349c840960303681110301c102105100c1e01c510184800d90341684c402c2c0d81c1140442c94a00414081400c0405d0540308121030b43c002401d000c3d42d02495041c1c5005c001b8443e008100b985000341050401d01c64194691013640484100d95018608075400e0722070507106d2041070b400000d0054810351001204903019501c0d039040004060143d000d290180203440300040304440803858400c03c0302d100034002d002922103000b0400300e0311f800004a4058a81008100d0104100700b801a441c085030f40c24000c000c0d20031020000f415992010802c0c2c001e4941e40d0381c10255854658039428011402c0c0540f0104021b1255461000340c001c8004242480c400c2c107112130300d50741d5040c012440780c1120340b922012070 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 145534847 1250 145533597 145533607
    0x30604031b06050c07120309050c010309050304030b070203130f0803030105040203190c0207060f030504021f17070c11030604030207090b01090503070b030603071a04091109120c01020d050715020702180903 90
    0x14403086246e051001619040001203d9a2100f55541d029402e020b0305041c0c0d0b44020300b083c030405000311005545c014401e11514140014001d40d070b03038402007107035003c101c000d5800706010400440d40301c22588100700070741c1540d08120410009500280c00b00b10b08281810925810008a018550b0040c0c05a00500b94052070800003419283c03400900340c040610304000c0100503628545d4005036040d850900002d43c02c80718100b0384500040301c0e41700308075105400400650380c0d40003000711850f0340b08046c0c40340c0750b5801e0000e0603a100310585008025800c180800c2c060182c09a020351400d0405140114030f256651012038213000d141d0704145d000711030020800c14075017403c0000d400113005030843c0126159262403112500e0046000e0030700c4c20360f07d07042091076420700902581d0383d00100410520702c066074540c0c03059468a0b0340c422140540640602d01c40c0b40d174018004d803403000340c201d03200c500b07140d043c1141840203510814080380c0c82050381d40240d0742c1200201d8114414444d0200440e568 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 145536097 1250 145534847 145534853
    0x10c080106110c030a140c13091a041a220602030a050907031a0a0f0e0c03010f0507050a080903070c081005090304060c0807020411031501031505030604031b06050c07 73
    0xb0002c0d00c0185120340c40080d04500c1600c001540405550f0041840c1a001c0c6c1c4444070303603045c50701e80c002044d40070400010b6400d80b0021031380401c45107072040035542c00441c0c11110301c2300701c4102202d0147c550640042c208203001c0b2107200c61640920090001ca00d0100c3ca0141c07a03207403a2407550143c4156602000308001000c903032180395000091038000b416201e03e07540e160004600107a01c620200eaa264012500010701900481c0003030178504010310510320314148a0b0b0751169030f682264480c0d03091030f1001c00e102c8128415203006001540c0d84134501080e1180a4918580203800c1001c0c0d48010480600841d0300420048094181070002d42264a0217020404c1915800350905180d40c20412041100c01d0f00310401078502503100341d100313407248601d0000400400c0c81680d0305e501d2082c00803c002082101c1907411280807000d890400040588243c403041041480c007031260103501c56404100400d001e0900d0310600302e80c04400d201c2030505591240141e41040d5126400340c0408180e030b80030 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 145537347 1250 145536097 145536107
    0xc02060606030606130f0b0702010801120809060f1606021c0504080316120e03190503060a14030102070609110307060c020d02010e0319060c0e01081603021b0615150f030406020906070203010c080106 87
    0x140940c50b400c1c42c98100b00d0312210b540b44a141cfc0f180344141800560101c00c214440150781058004e040c080c0d40d20049418054041d622400000c190204580a001d444101e180304440c0204c0c0c000c42c0b01425960799003038020720048901e00e64000d000c0303182050401310b12980207000000d50b00300041c44d1103025a600c00210b04008100d00000d200051013000385989a00410b07104641d040c100d0000c2d524070401c0840d00920400034080d1440b070404500c0c009108030300e01e401345100d8064040300c800c03680c0c4690444a07900b01c610000e50044405400304059841140c02c0800f90038010259074407689100c1d545220041802001c858094131142c03c40700080d00101e5020b004502800c0000d030318588107583e1000b2003880640031060513408940f04110f170306981d1542c4003203041042240c01d1401c1a031a0ba03645904502c40301807081c007261030750010030440380b0290b64003440b021a207141540c44036903c03600a0f411105406401c043e0621141c07002d43e03000d0007030b480c0304c000d1a2582d10f2207504222000344 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 145538597 1250 145537347 145537349
    0xf050307050303070b0c0a0c05030a090608060a060909111c05010801060902192a0302010e10020403050a030e041b030e060603010c02151b030108030d0c02060606030606130f0b0702010801 82
    0x102c81e41051100c1404200d074076000d590b02180d002c91a5a88010400c0d0944640c1114070004e001440003081440d84d164201d080f040580706a0345500b50301d41d598008201e600c900134068500090360b035240410181403103401c0164003004100b40d150615564583c0440c0844583d07100c09051070310748004101e4200284510390142c039044800354a0900b283d11502030103081e0038000d07001c000021a05441c0c5540d0540c014000d047e54400e42c207051075a604009020b01041644060280070ba1603a08222070703918401c030b900b01d903413100261407003035080e84055810441c10a51190081d445080c0e00da49240c12008052010a0b00c0c0c9001038031480e020300041c50440700505e410f000c0e82c03500600b45003040d00000c5614841706240c0d12903a003999a440c681018004034210211140408000800e000f8000701c064a1220191541041981e0100800300c0e500c3d0070070303100c10303400803810408039029080030001002910640e50b84413645599032410f4090780c6907560700c0051000c1000c91500110b6134800941c41c = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 145539847 1250 145538597 145538599
    0xb0304120905100914030f030f25020a0b0a03020c01060e070e0d1e15142a1c0b1003020409060806011a09010c06090321150b0918010f05030705 63
    0x600c10740f000700035101944a010b00c0d00d03041c961002401c0c00d40c0d0200966003000c03c42000703898481c04140c0782004242c00c04600305030f00c12404c42012024003c105491500c0c5c98005001c142c405140138020941d6611a0003403404060b000c009650412400b406804000d10803402c09603810314001500a0401c0900c408280c865030b9000f07a030001207015061941542c01240d400c076200345a40c3e181c03807698030084442e04500c507802c2519655201c0124804a841241040c03261400d0098241c0080783c19141004035a1041c4024041042c031032107200c83c041007035480e00340c002400c00c80d85000900464141c03450200000e030000f400340000c94460241000800d1003030020311079941011190b41c140c0429080f202e80c686c8001c0b60321182a03106842d64400c040d0030403403c11100c82c40d420000e0034000781c0041c00061890100220282205a1103280e10f422088003004412a08200014200c3da010140c5181e024181d02104070b07034281c0c904c1c0d8144c000c141d6400021012807502d010315041c148154009 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 145541097 1250 145539847 145539859
    0x9060d270308250f0513030b180c0d050303150a0308131a040b040504091a070302121006020c0114041809020301060b0903060a0b04020706060602030703170105030d050c0102040b0304120905 83
    0x1040d03c182c0c00104004d580c0d01d6505105407039220546000a406046a00c080c203000c2500b8140001a800c1500d0303c0c00c000c5005060700c000c148001c0900c031500f160b2020040003079000f040050401424400003214000004180701603650b92a2a11500f50300441003001c0780c00c401180030020b1100d222448100084e6100c00c03503040510b840c0c0380803060701543c03080034091922101d4a10070000c2003c04040b640110742034a10072401e0610009000b90030031000900e412240340b0118007042400c018810898002d40d008014000106004544100004c107603121040418000071405040351404440c5840707001100050034041c0780101400c1d80c09542c44820000010064296191004a8030b96845212a400891441c50160100e00244900b11001e402585880313800f288039a404002010420b009940742c1d90281c0d031701d000c40c04042c0000e20030746605034846081001040e016001030b10541404000043c00c040c1c0d40c01f00882c0550003150708039030015224403e154000d80201910000d084107944c6 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 145542347 1250 145541097 145541161
    0x281706030d0f08060307030f030f1d130e1005010602162918090a020d050a141311030a0b070f020105090601060e042306040b030309060d270308 63
    0x29010365242580c0c00d04020f280700006880341c0702008031100442c2e2201521404c207929040083c0301c150040a040c00040851980d0080b0312640d400d0296403183c001c00c0001044458143c0c0c00041080520451040c080c035582600303401000c1c8200d034000c0889802500e002d043c004120110880c1c07580008503c15103118084e0042695800e03000070801050215035038821032910305070f000401502c01d280d071282c02c40042003c005582d801401003260284000c0c4595140d07008100b05940c810804800080011000a554403002d0540d082015000ea00e0498440810034003107030070100003078806e680555110091182d0305500c6590780c1d4800304a44001c0141382805140c007070311440c062050f001005011a0944550390b43c640c040800004a404942c0303038112000320214446c00c2c101c603014460351405c1289801400e012040710f24400000708120b20b4030750b0082c900b074020318a20001c8050100780f0304828506522092110340610b0180e03d620505203003a451858800c0e05c2c5416401e5801c881c0d8031 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 145543597 1250 145542347 145542373
    0xa2a06050f070308060d080703120c050c060a0f020405030a06200a09050f01050f0309010f0606231b030c0303041b1404050a020f0f04031104090f060228170603 70
    0x205a80c0e220f545803421001c10344604c000203440f401400c902810503080041c01d03004040d080807588007032007440c14062240c4a01048152401c2c000d10015040382e070460700000c0d480b910582d0001e1940d0503503810060819490340046841e20b0082d4600f29691552000a403d003000000388400c055001c008410346458904c980040c00001a481885d020720401014074207142e00942c20b031030f440349100c034240e900c92a009019030f010700080c109d40c8038290720f001d20208940d40725042d850601e4030341d24001d03220503da40310070905a5011007c81da40b005002400803d402e141032000b0101d0200c14002540c480c20942002951007001c070a440404c0c800ea5101001601b510303040300c03110480d080740c00207142ea40b107805860191050300466206003500045a860000c5000c0107001900d01401d100c0044d1444441880308607422030f040a0400e507402e0002400107403058009040400c1c1021070700ca6000d000c00350082d07403052200840008150541c1d810382442c040340d01179075842305003200101440301600d2 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 145544847 1250 145543597 145543627
    0x23031615020403052a062a03030c0a0804050307060915050a02030601080402191e06030e03030603060c0c0f07090608010506010e010509100c0210030608070e0903120403020a2a0605 79
    0x3c8258545e031034007246411440004005c01170304800d40036040350b41e07641076200c40089225042094041c4448103101c00e481245001060340e20070388500c0c00315481c00032298001c0d40e0131b00000b0011502c0348070400c204c8000804074000c0c80c4420b480390f00402800811000c2d0390341a14802800311907036502c1402040a1a130380400c1d4681c0003a0191040c2902c0322070a480045070041e540c104030440c0000c0f203008046a4150030140701161129901041641c90f036800b229200e12050710003e50507480080440c04e640c10813801002c00008803021541d0020401540a04120403a442418042da642d001007018000c00c2c0601c0e44d0100091808500000800e00080d08078007071103030341901606910500350000c9016118000303501e50020101000400502001806420b0a000300300300c0c1c3c000d400001803903083c5c07403107840d0040c04090065030900680c4d042c0b00300003240003042501140702c1e6040d03180c0465001085c030a031503101d5a003128100c80146084500010480c2e1200d400c014041003500c80b5000c000d = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 145546097 1250 145544847 145544863
    0x3060913150c1e0906030e19020613091401090c03020901080109050c07060906240e07120f05240f06040e040c0512060603010c08040f2303161502040305 67
    0x5050700107070780810070000b03c400c4028a640c110401100042c2950141d802003440e0302185c0c2d03d0344c1c01b07116280c1018000e40c0c607103004c0451000e805210a401c41c006241200c090402e108400780303445941c580c1c41c0c114601752400725003401d4600304c040b001844078005902032155440b1460800703618052032140000c0003100d0512800900c55650000315483c02141c9044609403508104144400002420060000c1200f030340621029160002034406001080484004036840d007051580c45540d0720105662541490003840c1c42107545424004640c002842081c0c0100d8400b62041d504a0440c8140c20002c94040d0300e181c0310390740000701d0022560701c00046a0999081500440c416210b82ca8031080c1c00100c2c0c1c1000340e0000c000018035058600007d4250b2241004800034020f4103080042a2400b1f030040d1005441e090105001c0d6020030940f0540f1800384048684141906051011482c11a0804000300d2804014500c0402c103102040b2100c02d00003184103411850030340307169038031030340c034244 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 145547347 1250 145546097 145546133
    0x11b0c03020613120804170403082206020a0609050106170a0221120705010908030f09010f02030103080f0304031e09060801080f1c18090605011b02010e040b0a050a030803060913 78
    0xc0440024100905d114180203000711800d68184ca61727032030386010305158000d60420040034201d1700000346181480b20381c1d24101c4101d500a09001c107841c0c0c890401801846c80c040d41d5030340d25100c0000f0100343d22980240794a0408001d400040c42500c10820244041040d01c0500100c142028250f05008542c1c5101401c4050100f035403001c1d64035045001d07002088c40540354079808404c0015418601d03045078460b0000710000c00074050703200c640d0f5003240020f00015021300700c14404010f02d065442c0056401501030300781000e100201c0300040c40305104002e88800010b00c0070343d003000310941002d0450301400202d400380001001103800250388081e040030b00911018110780c10052180665848480014440e070001040c80d150080c08018082a1003400d0001e4900c40310740c0e00302c0744180149100194144e441004c0e828440b0108409024010b00103540040d4601e80080c1a80d50302c0314041c0114855540701d5203d00e000710401c4811040144030010800e41c284560380014101111848913600c = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 145548597 1250 145547347 145547357
    0x20c030c010f0c0c09020a091a07080304261b01051504091b0f0e0f04150203090102040b1201050a06020a030f0f0e060a080f010f0506091002011b0c0302061312 70
    0x1102c101c00c0711000014807028241e540c841c10042001c10545e002400c0c070b401f140c2c5598800d05e5480d11440c44502c0d13038a42200c1c00507001d0003a0300010b040c04009581180c000c00340401c80008080c0b240c00ca80c4145c580c13010107010000b0b01c1c0e102014178050303040900075503840200004d1404c0c442e580040b04944e41c0d2140700b1503491001c101003103510120036801c0c1c05d510f0340030a03846407910309621441c6180d003e224284240e51000078a4401034450341440b40740e0020200401c00350640c00345002c1d42003c0d0070942075540a110104111092030042c10b08510b100c56804101d5152505001054445030003007021904096144400300390032006100ca0a5241d182c00310000990100882d400100c444841307900150004080d12023a51220071070780141600704040c400d6903664108032842460078030403203810250600004195141036044000b01040900010900250080408000c187c0700403144011401c00100070081c107504100d2240c0c04800d40000980441c01510340b00202a42d446000d02000 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 145549847 1250 145548597 145548617
    0x801090b0109080f0706030615020a02151917100501020d080604060b0f0a080106030209030c060f04030b0103051b010206130f051203010611252306070c090c020c030c01 74
    0x192141500d400101074010a4a52440300b2003030464032805c0310310031000042d080c101c01007170100c0d206500303147d80e000d01e800402c1000b4040c0d0074007800c08008100d0b043c0e82d90040c4403202d42845c18100c000d8072002d042e40c4038a5900b0741c1a48100c0e074008041e14140c0d141052074010302c1240d030000313204c08802c081820135000581e10b0030300040140500750001c082c2271001188805072803d21401821200364a40c44158590780c03610720840490181c0e106850340b5030301c11000d6400d2810481e0003442104110200b03545007540313907103d0490a503c02e0f8801c5941d584012011017201c03481c80c0c00700701e4409091004e0300c400d00340070103102200ba0011801501c1d135500841100b0400504021594815080f041c1c450344075030b511b260203828603281c0d11503180c050040c4c2c1c1f0044c0e0351600510241010348400c00c41820040e040c0382511407080c840102c0402401100c599035403165841501411226105d00760840c0c0301e600300702c8502c0035500c0745101c000641d40030b03400e42044c0755004901c0b00e060240c00e01c2c04031981 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 145551097 1250 145549847 145549849
    0xe12040e090f0d0806040c18060f1403040302030702090c0a090b3714030c04140102070f03080d0b0609030a03030b130501090605030610180b0105220303031802010801090b 75
    0x3009007038007084524480d410f00c50030101e80000d10a0700c0b4100c200e80803c526481000140d03118650000d15500c0c20030b40c05010700241c0c0c00741c02e000840409038070b40440801c108031401c80060b0b1050381c05502503803001c40d84508514003140f0103a4040241641c8500340640404003030030302120342c001c0314000880400d64202820a4108950003075405140c1d0090b6000c18550b406595118624007100103050b1103a2030401404940850f80601602e402051900c2d10700301030107101c0c03204400c0d0141107004000c0001a44092400480c0c086c5016003031156681c000f00302c0403001c40b03202d0b004007405800240000011a90b001c60000c092542500340403c841e00040001001558126001d82c2d60718600710001c580d05510303a1105064480590480d84151200c0310744408044d02e03445204c5070506001d01c11109440d2076040405019418145217013030000e05880d00b14040b5001644e04074090300c5490030014107501d4084c840008108039807004c0641c107a81c00007843e5140501800c020b20352608805500c03 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 145552347 1250 145551097 145551103
    0x60e10030e0a1506080106080a0f030c020a0602030a020610080c040506060919030c0503030309061617150f01050c0307082113031404150c032307060e12040e09 70
    0x14401e6030100740c40003a40d0b0b0746404051070440442141a1134503103c004100700c6030520405003541c4a02d00108127541c01540e45c00f8010301c1c1010200c08028180c000c020060b1100180100946a1600074548032491894000c0c03404000800300080000c01c044100082080030442542800060780d01240b01c0e600c03000454058420003007855000f2044403e01d8014900140581054a1155030400c0019503a90201a940e00041d5a130800d6900040701080c200e803082c2c00908949950341c2011040c0d10b03403102c0c0000d00d80c0001c0340d40880507124504802c2091400d44080341d0201001d082c003604000710044059500c0c018250020858a030024003480082138880c1074200d2802e000460301101d180440100a211307220031030860100f1903501400340e5000d411003c1e0340c15560102400081140b6048044031a803220100c16800c0c48a00b900c04141106003c40400161a00c02a1241e5a012514000d41101d00c002078103c00ca8001610702000c03200c000d4111401c030703582c580c0350b41c13070300e807211049181 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 145553597 1250 145552347 145552361
    0x91c0905010f18090905061003080f03070903020d06020306010e030a0309140a0801180b0c04270f050114010207081506090c0c06070216050306070903120c0c180c0504060e1003 77
    0x4003010f02d42c0070020b5680c00a4004503100c03031051080d50144c1d00c91400140595405001c0184010824000641054208030185612282c507103410864261317a5000304403034910500301642c1050f00002000f000b960403240665614000f5001442d150140f910000c02d0403003e801818514445c0d071810341e0495803001094406028100020012200c01810240c0b0031119040122401004200020002da1a04003a101240c0d206400480d80441202c030066900c6440c0c0c01040006540d0b07040c40080350000d101d0240641007841000c02140280030019144c00443d61000040d903100d000b201d508503072000030740d941018007641e092050380c803500c003810554056841d0010f540c1c0b00e0301080203c0a603002650b03842421503100d521130060b4503281410740b00c1b1001c45009010600b9004200005125070102c6400784070a81f4080c603562107290b444000400c0c180e440080140403400c00c1e650741c1c03100d6104007401001c3c80d060592074186058000f511180b6014500c0d482401d144004650035402600150 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 145554847 1250 145553597 145553627
    0xa0c081c1a10180e1008070f0305030405040b0109030803041b0b09030a02040c020c100509190e04030e01030216030309120512010e06181306060b030c0d09050f010212091c0905010f 79
    0x120146441c254103420f5015500c02d0006c039109051001403a024400050700607a90000d0145103454180800e000c0a003480070b21090401442c90341c0040812103141c05140950322491401d40507680085038400009016040b42040d00d40400c203130740403964006640c143c0d02c0e6040d600480c900f07140c584e050b03007400d1540c1c80b513682020940e07402d401940c0e400310003000380030030841c0d400c100000b000002da07864060500035842240d03191b10108002c240030380140343c0c00d494145230251405601d910140740012080c0c8049000c61340340c01ca039208201c0101c11403d03a039507103442c000c1d05000c00b2004000e004041849018452904100803985544542000075132f00c8400a51522507401d020300c000c0e04403a100f400a8a09500e003c4000c2415605102182e00951030001c2c80740c200945c052146004041310f207402c89031740c0f044941a50020400f800600740010340d91200c83c21310b1a04a402c142000d44041c0044030103242e0154045040d070b001800d880a13030f9800c0c60003200606044c00c054901e100054015 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 145556097 1250 145554847 145554869
    0xa090b060d020c030403050105130f140109020a0605040e01090509070b0705010e06130b09062806030203010603030806130b0a06110a060e030301060228080a0c081c1a1018 75
    0x10503201c43c0300000030802c881c810070080001741d03588040160002c0040c00000c01c255250749121000c115a02c26800020780860000601c400d01540003030305d010000c0d481030005c900041020000255040442d038014400c03810b0074006894900180c030f4440030203008002d2403100101c0c512082c410b00354460070388010f1340001c40d04a0304249040280c20841e4030800c0314000d590500051600070081001801289120b008052421406060040c00d44660144004180d80c030880000581e40900940c00254041e8840c10301905141e0700b4807000d82c0300745209241c42400c2040d42c0b00c0545454012504a405508c4d0152400c00d007908400c0c1403010221000e01400c2c101808600c0005000c00158105d4104d5001c0f03030ba243c0810b240c1200d548180030104101448103400d00d001080c803040003030204180c185052035050529907694a0749800201c0c40040c108140100c2e080311803003034401d4001c00394540c581c00c1180040341000031000e56000da001000c100010240c1405e2032042035550001d00000041707 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 145557347 1250 145556097 145556107
    0x70e0a06030605060102030c06070e0d0609080c01050c07080f07060204090e0c0f01020114062107090902130203040503181507050c100306060c06110412030521060a090b060d02 77
    0x25800240c6000d01080d40c410340b03040701280b00d942c000012174140d000c1c0c20b40681881d0340d80d9801512880e06c1149100e800c4032100d0131400000da20b610501c3e030058418040c840d10f0300f040340c1d055400c40700b0040c143d03040008200085c1001ca001c500a440e000c0f440b855000d030381d5031041d10340302010303000d16441581e00b5810985e081d44100d1000ca40c80b1200a01504c20320442000103004a0036125400c14490181c0c0718640411110f0401000315183c4044002c0c140c2403100a4864692514007030340d0000b00b0081c1c2d03403c071210441ca0a1241207108801d4031070250b0039418180c49071505c17403080c1d2a60303013030051030000c4003d070344d407a125101e40b4981070100c0304585038045070a2a5889160340c00c901441107244000d4440c1c12170080c8a12000d507041b5640c0c410240082d550b402c0001d145841070701140705014400003d4949142d522140504c1c801e070749803619080480c69030088041d814404c405d04a01c28420003c076520341c0d000f40c03011605800c00104a10300380ea004034441e8402c40c01900152800051 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 145558597 1250 145557347 145557361
    0x9010204090e03180402031003020d06020f0c0601060207050612011e0305030d06090e0712030507050309030604030e130c02030a030c030b030d0314090303163005070f030204030f080705070e 83
    0x40609142e1070b01219413a030943c01c020402040b0300c82100e0200241504035418030140c00c00085030100c05100310f0300149040c44c200c83d140f449822071107411616610443c014441d095042c05040000c10050b103442e030600200140786042000e05000e20040c245071203286403800843c1300e01003801550000141c2c1d0b503072823094003840041c0c00180600d402050401c203846d50b000b8400a10402215545044580311341041d030f0702180d26900c500d00c140c9861009200405080d40e0134885c1c0c500443c40303601c0e41d088880700101401080584004012030080c90070945c0f050180d000700450301003030401d15001580f80390012054009040034611141c15200c0c1980500c0c0e5550990300c5290040c266011404c40d958503908095601e00c001c440010703103503088641235500740b409442c4544442c40030310080d20f040d90105000300c020941806d41c1281140d12401480145500083d000d488000e0924042d0318113821903e406424050290700209100d07400681075041c003000b8032031900901444100802c032424801 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 145559847 1250 145558597 145558603
    0x9060118061805010215060108040c03050114011a16030e041119020f0d05040e1003050604060f0605180c03070e0307090912030c0e0d050c0d0807110604050105030a0509010204090e 79
    0x524030b4540800700740c00101c0ca560000866020f07040c22036981d00707030300c2d41c68000454140303001400440341c94500d4040032000450a0182080c980360b035590312050703076240c09030114403090034016506e41c00100300141c00801d150a2901d420301505402c10000030b030340c0307c40842d00620460f6001c040300e910115051140041400c4a840d61030029806c4620b8140254902a2192a06084c81011403030800c410400c0c8070180381003e502840100301805029625154a410000d08803003c4510b650398180a402caa0414820031000d84400d0391500b40f0a8204420a140d0030f401820564100d940480080c012921515814044401c064141c03840310360360300ba500340501078100b022200d0310800f02c1170700b00307191103481118400040b0b95118001c1c1480e0a05002e9666402501590140039007002e08110b61075007800c10140b984a002000e945500e2801c0c01d02c28401c030010120b11600c1d04010401440c0e90280a9a400078400040080e098a5103143c1034024801c0380c0c084541c25003080703103007041540b000c = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 145561097 1250 145559847 145559867
    0x30e182e061d0402041d190e0105040b090d0909020f0d110703140a051602011202210c070b220f0303090b0714041205011e05071d030303060906011806 66
    0x1819201d003000b10a14200002c4c0d0040e0700070243c0303c030042c181e44111401c0240d6843d400405003098000100304405d12001030710320015407454580e446400b40700030080200841d55000710440007a001c3c071b0f038803100000c010280e03a00c0b900c1c00b02900440ca03080310300604012076419200c0c000c42084940040c42c19081d0b550054002030300820884416002c210800340c0440700c888100756a42460000c040c490781d4410903448006a04100009a0f07000d00100540300820300c4603107040d680e04140300821005203145400406200c08400b06204c032400280c40100c24540051100882124542d00841c041006401c5120040c1c200c0c12416505414150580d1000700d009002e0f03165030420755103140707060b2403c0c03050311510603160800308401c1200e490302d041e208074842d2294001107160204484000c00c40c003042c0207000031140d920741c00d10814075000012007201c00702110b80c14402002003000652a400300804650050380c0000003d0394a070b100762483c00700103036440f08a142e4241c490f5401080802c40b = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 145562347 1250 145561097 145561127
    0x408070612020a0c0b07030e01111306020106030b0103111203160c14010804142505011115010b03040201030207061d010e030f220819030e182e06 64
    0x2600380c00800c0c039005000300c41541090b511082c062508170340d2601c0103035100030300c1da00400d0303074035550492031540170301030040c2680ca001c0c80540c9483c56880f200c00c48003030550007203040d60300d000340400008105120060440340c002600c0125940303488007040f00396251804082032400009550f0503942c6035851000c400724000ea201100c441d480d414846129208500214007151006002600240b604a1041107190025064612110b071090300350440310807814501c001000d07008810300007941d102c004501c07161300c0700b0300500040324031030402c13280c860060041c440d00e5000000010156402034040f5440e850b0302610401926000643c0340a041a02c1402258a075003480c280600c07040c0e0002c1628001c1c5501240030b032400c80c0f5603000302409100451051400ca00c01c001c002003500c401d0000c076800d104410308200c0701c1200c1c0e24004081000c640c0b903841c0306802c0c03d03540b08910f602d01521f050340445000350418406c1003103a540100c0310100342d45041c20040b0040040381c07242e4401e0707840300d039031324 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 145563597 1250 145562347 145562357
    0x1915030f05180c150409180506090d140717070605090106051f080a06050a03080d060e150907021515090c18151611030d0207050102060c0d0608010204080706 69
    0xd401c940d0034441520510855079550108042d003d092a0400c10814032191038142280b81c5a502c1c00c201c816038925445100c64030069a0042017442410310100d5801005400682800d0518400107002501e00300e0b1070800d2a000401c680c81002070006850124000e0068080d450f22074034501000a00011600321b0355030f500f04600000e003800c1c411050300707000082041c040109000003004840e0507900070040d180c26600c4003c005140e840e819406405140603412090340c660090840c441038520581c8000381c0110ba100804c03007201e48124442c0e4807003004450001103901c54000492407c0da10f2b1060342c00100c2e681e0180101c500ca41031049480f98015038450781d4aa441e420815454005d00309107138554003001d051000540b5200401101170b0300c1c004851418044014240d003003218802c0030850707100403c00380c00301071450304110b0b008080c00244000d104550030400001d4607074101400044000c1e00208110140034800e4002c14054504d080c000c40d115551110a1035031000d1030f1240f40c011403 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 145564847 1250 145563597 145563601
    0x12090b1005120a030e0d150f14090a050c01030c030e10020a09050f1c031403040b010609120c0e150418030e1203120c0910020703110307030309051915030f05 69
    0x400100303e028815800d92199046102244244000c180c1c042d0703411110303400700c5404600076400501c500364080130400c20003d50201c6c4c00701310680d80f03175010b0401e1200d9031003000300a0006138000b0710340e504c1503028a000b040b0101c0f000720503400f804441c4000c09140c014400c00e02e4501c1015400752080a840e035403091404c40d03440d41480160405a61510b81103d06015500d0031540d4024244d02424801d10b0010140d01e2892804400d07a0016601190160541c030010481c60389e1080b501c0e40035000300b080b0015120540d58400000001700d206035240d1090100002e28840e13640e4200500b01c400103002070064455054802c0d60080001034208d000c070300c40703400d1005d241c2820340000444149100c0254a0b140900060b80464a4001c0035000d606100304580b45e0161a4125150201c2c4007170f40007031103801d007581b4010521808221032a030203544090010000310b5440804c11049460136102c2d90482221070541b482c54042580214101040d080d0061018582c154800d20b84401c01d420100704507 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 145566097 1250 145564847 145564879
    0x90106090b011b050c030304140310020f0d1508031309050a09030203040b0d0f020f21090c0d2306010906050114030a020a090302031b040e01050709030312090b1005 72
    0x4a04207100c980c006546251080182c41d80740140a415034018401c4a1201c1c4030702001a1865000f60441c9202c01c0020002c021a0309041041c80480900da19065040000703071290282240a2501840282ea88404074141d940d40c0307032420840a01250026170b0f0707a45031030640400c0d0130075081c81104540ca1410000442850031481500c0e400c503031580c084c1d03142915041401d48a90040b8400c2049950758a0110980040704e1008103154103001c86c0f115140d044030034000c1c101002885882c500034a001c4100840480049000303010804c08450380449160203041014041d6600141d48c0580e41c81410b0940b2800000201075040721000c00b414420203460708011683d82c080841d8070703c6030030400e0020400f54420790300504070300300b240e04c0c081344101c1d52600041d00d0048241f401104c61048c0d9801c0101c1400c040c02004407000911009000a04140b20000c24100840c0300c05800c2003d0640201e401c200c86810904507075404c40813220007800c000c4402d002154152007150700c00e03140329000d1420 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 145567347 1250 145566097 145566101
    0x204061401020c1f050f090439050417010204170723060403080912010c050d14090d03020a0203121f060309050c090601020703080403080a18030b041101050705060f09010609 76
    0xc00b2180ca16011013100300050260b446411141183d81081c01c14003114117203031640d200b41c011010f50f04440a01814002843d9220100410340f0881c0400444030703031000244d000000c40d030450700701480300d010200301100c00600902490b001040004e01c522039440a40c500040c4c40c006550341a440218480d003581d03044a41001d01511460300608144401c2020511483c040c00d44408040d0000c1d54140407813020301e08407170795031010781d0106101041d000b0700c801076803080010300404000710340d240d802c00c07190503580e8050b00c103c0d120030941c002446404291007481510151884c0308000042424140c1c2d01583d5413407210880740417882d000307100050151080c018104401e03004800b0346281800c81c1d06100d000100106810306500c903018000000901c190014402036004603551900c0305034015004041005031a01c2e91117064555000f0f001141661000f250429400350721548220441401651a40548107010344213024110410500c078141040c0b0341d100c1c80420000708807050f1941d2040c41 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 145568597 1250 145567347 145567369
    0x1050c07060b0108091506011b0f060e120708030a020403020a03060b0306070c02180903091002031209070e190f02040902070203010e070f0e0405160f03050d0507030c030e0a030204061401020c 84
    0xa0b940c84451141b110000407650360390440010f151400074003191a03030319280340c0010302d0201c50b040c0840e00c1002c1401094480c52001c003003890041c140b2401b22001c00d244c2805543c5003c0c000a50010101e4030341c01d000e0741110000e42d40030f8201c00302540da0381045c078014200c2000807400780c00f9000001e440903202d4085c140c1c0d866401850b00300003e041813aa218003c00081c040819444200060a020f40e103040e520500110654021580d62501481c010400300015241507255403140000b0f2001d0320010380b1042c0d00c4020394917440121480c030140742d00078000c2c440715515010307c00a00881d1b0f0302142e4004040c6075009070000c0c84215240c44c0001d0756860684141c0c0c0e5030500c01c01040c050b5801840340150898040e00446110300b00040201c1445a41d69000e940da42440c10410000c00005000300c1000003014103002c0e08011007910301510300c0f140c500004082080c0126002055503900c42d010010b503070090b00800130681c40302030b0440030042c00d1031024098810420084c040d844c003003850817 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 145569847 1250 145568597 145568611
    0x305010f05061c1103090f0c030604020303031f090c08041a0f06040c0309080315130615030c0507050105160e03060c04210b0c03040309090216140f01050c07060b0108 73
    0x140f030031a042200782c1c1c050180100a5000a40711200d030582c0c00312810146016402c1c00c0003414003803021b02420391a01c003a6010060103034006e041004050307a008010350b9031080c482403640e03c620b61402510a4000703072039000310003201d1901842c078031f019070f02282d030034801e500c210b0300549200b803014014010b03d00b0450300703c410031940341c00184007810035402075244001d0340d08010807050300703941d107541c02a04110760029541c6203496034049030785401d800c011000b0701a52002c1005a04008141006400042060003030580b03c444481000d032140c0f00b103035005504280200070904161020507040320849c20448000303021620b001c03121f8a40401c0c6107001d200811191407406180054148100561f8058103501103601f0000030049001d00d1030341880b1706040011545e907882c0500e8044c100080c2c94010386401391051004001c080340401c900a80300b03070001038501940300c04400252608030307840c420390580d500303000c1800340d45460040540000b038450312083c0140b00303e01c0c004403112241101c8103 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 145571097 1250 145569847 145569859
    0x80a0b06010513050402090f131a0105031e04110409050d030b0406060c1106070b0c040302090a050108210f040602070f06031503060504171b0106061b1b0e07020a030305010f05 77
    0x82055145c181c3c020814041d024007400d0b80490700787c1c00103000201c511614001c85460307054011300703030b2484138000001603002d007000303425418403003a040410690859800c0501030300001003800e00110400701101c1040080c0140a51003591074143e8540070b030303800080b021904116401d0306603e020301911065410780e5903284801440340d00d034503508079912071403140c020904006030b5000c2040d40c031030303e4130420320300310710955403499032050020051005080901851403c001800040d0300072455031150408188000a494222000c100440c8aa42c01460206100181c005412600413664100b00c0701e00711000a00195545416001e4921008596460005003003060000a1465105a0300302303010758032070203229401040740351035580700fa201e1034000c0b81c0c0700c0c0e0681600340c0d01740940300161400d8581039044c012007104d04084801c052100400780e903000d41c0030380d03400b21040b0710707440007049481560781545c1048100a9103650f01c0350401d0380080c1c2050004540d4903c200800c804844011b050 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 145572347 1250 145571097 145571099
    0x130503070510230f120a060e0412031d070807050301141308040306090305042402120a180303081b0a090501050c0c0a091a0d080702040203040f0804080a0b06010513 72
    0x21952415070003c1608012080e0001c040201030f104003501c2d808403565081d0750781c1c0e00302072032090380300c00010310b9050382500341482481240d41c1c0c401e8040e0000e5000180326000000540c044d8043c0003805411908009001100d240c00d600015243c01144d071460103031280161500b00345800c1c4c40100f41d0441007452810045200c1c03100700304103121030900504070700b820262240d80750710960b580406c0690000d01c012409002c59841c040030018000e503c1c0c140c0c3c40c001c2d0125400039444106c040c9100c24a01c6001c50b0015600d40186408201c6181a0040c00d42440e2a841c7c0500390720000da4080100c062540d03509803d1706918803c98400c90346503100c0c42d0856140030011a01d03a0f010a220120314001c4140d80125a200c122000c8050050214041250040101c0d841c0350360724580d0110784a0007081000070045003a000c22190900c0e0180d40241c1c0c1c1e035036a4107048030504204c2200425001000800140134070010601c000154803c0c500c50031151100801142c5500800c01c0e4040b80c20041c1c20 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 145573597 1250 145572347 145572379
    0x10020c06160212010c0f03240308031005030304030804083a1119120302040509040204110c070e040209070801211401020d020408060105011416030e04050a021305030705 74
    0x306061060b100400302042e003400074000c2400c0d25904800790740442ca5807500000b016815000c0c070a89000314078a0340300081c0248003200c000e003016100140422000102040c0c61412035503c20010f4000941100e503070356540d140400340d90b0300910a440d130358041c0303182401110150020449901d9059070785c039000d82000c254204081d1001c90714031028010088134204040c44103001010000c40d00e160b41005403403d505002d840800c80c22959002c05104000030301c82e42c0d03108a0001e800c540c050350b001890107680d03400e100300c622440800010a10800d2400612a110041414032a9100f5581c02d881d9458443c0d06484400c02801480d05207508a00326810802240c0c0003085003034015490b54010301c400415013400c80e8000f001c1189140d400142c01d00441d8420004140180428a859105001e29001c11308040c000c08540382d68202404440400b494444e182c4240902d400503c100064101032070b01100a41c011010008240701c600000142e0f8a40400e0003411520003170308850001040d00 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 145574847 1250 145573597 145573627
    0x61d010e09011803020a0201120203090d05210f011703030c070206073815010f0f0201060e071706090702190c0b030901090b0c0903030904020921010b10020c06 70
    0x500e066007035036072221071002003240000c12034031980c002d4024295601d01c43c00010000d11001c504444014010001e10245000015100f900b0040a00e80162900c40c80c44401840c0c00107100c500d2131103002c0c042030080d02c06445006604032190085140d1100860802d07240d224001140c48602c010720502949000d820710000030485036105d907540c1c0401031101c5403201c0700019941000c0c1c41d0360b0003030004c10b201514801c030b15542000d8000c01307543c401d5480200013000111840e0b00340c2d0070000c0b602e01e0031811038002d41242c0b003c1c3c240080022031602d01401d0003845a07030800003000710082c2e00c501007043c9040940d030a40c000c9000750301801d2004180503c1c50142109034038104c0310507500000004030100c001002d9400b070310008001284168090814541a1401401c2000450000c0001481c3c0d940c001048505400342a60050380300c0709580e00184a4082c04000041d103247c0308502c0c0f40300148194000180328200f25081928104042402ca0380c1d00706002d0480e400000802c01c40c0307400300340360b = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 145576097 1250 145574847 145574851
    0x51c110409050703230601020f07050f010c021f020321100b0f0f04090e0607020613021005040509070c03020f0a0c030204050406110a02060406060b070308041112011e061d010e 77
    0x94200403600014220340f00c401c402042e0005c54030700402405100c05581d041c0100300700c4280e000000d11400703041000040707032400310000041c1440719501c2d02d0380464681164019064452a40548540300c0d07440d4082d44a9101135080b07100c80100c06c8444129007441d1406900410318510361901d07640c00e2014034a0190f01130035654007c05000e02200c6000300d8400c0c003e00141c847c83c1c01c00700f0000e04401d41c00d0b16141c0007819402c01e42d04400308001a00c0c0000311001002038040f20b044403100c1c4d05070001d682c2e52182e034001d41d421200c0703042040626900300c0f101c15090340c4240e080724004003c04404503110282e580b40141405011001040507144ca030308080e40141c00f0303240004141c9688d05411445038080e0340440c0142e0409000c010038000d039482031070010010070b4051450031504d41e034003c124980040c8001c00c2e031400c0c02c00003202c988450740b41401442021000f041150750001c4038040c85280ca0248030034040c1805004290f950051408650b040c5080901e0315440e42820402c801c51000 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 145577347 1250 145576097 145576111
    0x150304051009051f06090e030a080f041b0b0c060f010b040b0d060e07091a041a130302030303090f061510110a0206040b0904050702010b060d0903090312051c11040905 73
    0x70b0802d00440041c481201030a00c0c030420800000c14600d000d51b40c00a80340d044001200a810500c2642c100d1a0070889042d032003080c090184049650724505840200260500305140902c0400d01082800c5850020404240032408aa00b580d82e03040b5544c00800d024040c0d010806400e01c020406011800b02038101c007542500003241c80d944414008400d00e5044812000107118044100034190554440240d1100040b561030b14180c1000b200140c502c4841215442c0004005042640d5100c0d28140340c019650003025a030f07403400d100d0440c079965000701d008001d4501a40010464218002405003540e000c041d140d801c220248070010f0b910f480380d90035000300c1802400c0c220320041e80c1300402040500030b940302d119240d08814052004076503008100c60190fa240203000303451580c07103105480c1d15058414010510001794542268220384035070000f0140850588403249940d00f150281c028051302d002001141011203240a090310101c50254946450811003404091803030b070070156000174 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 145578597 1250 145577347 145577353
    0xc261605011b140d020a03090b0a08180118050c0a0602010e0606190f0303031a090601080103140a1a0f090a0b041506080a06060e1305030301050f0d020603070305040215030405100905 80
    0x8184102d404e10010451400060304042801410950007804410150111480d958107040c1c805002400d11400a002c41103c8041150b03403549030982500401d00a100c00014850309002e1454001d60740c0c1c840100180c03040b080d10401285491052040781c8010b072401004051948514007400b40d80094124140400301c200c030000315a0368103803180940103521075030b00050280f0300450174400d0392215401d42440b5510740000d005140ea80013944a0641b600000032a80302c6550000e95850546011001024003d64039088410041d00c100424410b505a0062078510764541d080c9540b10f001c1010005c04841900f008940403848480f2028204842c041d4002001502c0f421602e01c4d00d038180c00b044800b82d413104001c0c0034000c1040c4c4200d410071f44490103919140300c0b030b40c1c2d51034032400140600c034080c952400070480a07984010300188010f40291856540742090034004000d00700807034040e401003840c51503400d0f0b03005105003140e1099800501412021122402c2c55001d4019142c09031a244 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 145579847 1250 145578597 145578623
    0xd02010201230108011103090d0e0a12080403050705010c0f0305090102010612210905060d0207080f19090e0c07140a05070b0c010b040209060f070c261605011b 70
    0x380305124000d6400e6050b00c1c280b80507614018559003541e0071181245558038092043c0309243c6c200040382000c0381d180303092110030304c6191400700d10004090f5210780740b04188140c1c0301c0b040c441c81e40e0082044d03901130300c103407500b00d5117900c011349041c0c000c07503802040f420340c0308524800310f8441c402a040303d1105100202c0e0441d030324100d140ca0140381c2d010544040110350302d021407501d84c01c030714068100c00504051007000d00c0c5c00001402c40c010307901c041802e81d40024a40c41002003910031504081000f414030f0b919681c03048044040700012180200c00b0400e40d5030041a128181180f091043c080e142c0d260b45072280e16680c0b05490030301c2c1000e07101144100100c000001c0e009001c0320010b80205a242c42d210300d00a01400d0079a00000d0707202d801544100031003655074503400d045507485a0b404103403e43c6c80f0031a1070081c1e404a100d501c01042c011b5510b0f4030128008000c800c46c0000201c00040f1100d0482d15801d02d00d01d5012031043c180401c0482c0e980c0b0142d040342d07581c0300549900400c2400815 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 145581097 1250 145579847 145579871
    0x17120d0c12060e0c28030b04050a0501030b01050613090509010b01080c090a0b090319062301050d1e06020c030a03240515090a1401090e0405060604020313060e100b0409050303060d02010201 83
    0x104031062101e0012a44982400b101230400d0300c40e03680d20282c5441c084c0a55451600c956000210602a10340031703a40000301454803548058001c401040c03141010800c3d843e111803071070b000b132000110460000d0345000114400d90201c81c207991108400409150442c0d01e0a001071130b10350310500c0300399098040d50541c40101070007000c12a40742c1e8000c0001140c007810550740c9004250307141c0c2a840750105031100500c519103030021a2241554024031480906000d45205c1103141400031000b000d083c00000c0f1681500d0010000d420baa007925182400342040c88166041032002042c854507a161a901081005107052046000000074646600340780a00820100c1e95203100d9800ca04622003144000940381e5034041c90540050200720003c181504080c0d83c2c4d203454020192146114540200119072072009a451a590003507000008018504080c00c550341c5500424001304200343c9441d4205501381401d0003810411a03122001d54510740e2000104065000310400590440d96608012811 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 145582347 1250 145581097 145581157
    0x4091110030509070501111002030601030e030301090c0909020a050a0e06160807050601080609060414100501030308060f120d030f0f02072301021317120d0c12060e0c 73
    0x641c0ea40803440f441c0009809181a0031580114104184001d0b8070852000c0452441b1641000318405641e0b621810012005840c50728066401404000f0000408080303647c001c0e11040241c3e102c0b016050b0707848644008a00900d000c036000300d002000020010351180790011480d030b10003030000342000c0001030b40c0d1142540b0707800100d0313a41c04005104c0c010b000040012a005001980090803a03140101c1c0c155202e0320b01910080c41d20781c3e002005401441c052080843c4d00c0e1418504000703070740c7c1d2802c0080c0554421307100d282c00b581603100005424181498211801500100201120602d413102107006294031400084000c1c1e0701c030842d54521207203000400903107019103081e0191400084842c0320241d03d88816404036803041001072826a0303480d04100840ba4120340405840c210800e40d1401c0080000c00006d00050004440c0305840c01d83d401158241c00542d14007160700c0f210900f080888505005910500355140002200591950001d00030800764810410300213101c00036181d8 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 145583597 1250 145582347 145582369
    0x50d0e030412020f040603030c080c1f05070318200303071401090b0c030402030d0c020d060c020f070803041a0304020a030b10090506040504030f0305060402070f0804050108010602070f05040911 85
    0x88500000c82c4909514080307400b03402d401400c603820000e00349503550240048075091402400d81e070000c12401d2443c041403250300082108482c0765042c40314074081c418000d200480e06080442d1500c003443c6804600c0c0c00c01038005a9100503015141000ca101446148501d9604954035100420004000441040400400c2c00300c2500200d62240d03a072070701d40000704000b80f4000242109008200140c2d80006144070214070741c0c281195583c03010f00200703995071058500500801c2c10801d1089030300380d0001e205c200d0206290300b980d8142d52202201922441180b2640c02d0805000350b038280310700001c41c0155080b1b4401040107800316680e5031900d00050040728602c84526100174200090103450290960004c422182001140b030701f070342d000d012200c1505610080546e07540000b0741030780f9a64101c9889981103040b51700118070915050516602c00d011b00c5000610f1030000040b11030000505e0010b44601500880e42c1905000c1480014540e0301c8081d5050b51841484070810384960079192 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 145584847 1250 145583597 145583609
    0x303080a0c1b03031d1009050d08090304030303051905042411071202150a1b030b030a0b070e120a1205070b160507060c050304030215070e0103020d140108060717010e07050d0e0304 79
    0x30416603008d042c143e003040c02c0a00c170401440300110401600d5200801103806076913140c2170001e11034075021803103016410200340c4800315074500760078441072101d041e060b55841090601c004d5605000e1070550410b4135440000c4c00d0080106101540003e4a02c3c010081c90406a204a4442c400d40c0c01d141c0707010040a81d5219485640c46a810b814901e0f88098180704280e075060512203010301d0030200f981e829403000040e240e82406c1c004180300a21400c1c1003140c00c24000c0132860f00c0060410443d894084007581103550040c1544034110241c000c0c41555402c94001075182c6d0341ea038460002d4a0400310703200c18401049410052440002d48500c214004070034a559a5600d030700e40ba26000e80b903d1510a00c0c0810072000d00304000c502c90b0300805c801c0c1061002c2c42c000d601d0320307420b211010142501030109121002124004694070500040040c46000d55640d040400001e80d500142131150a0140c1c10444421b140040c2885000c2e10007400c0103070031680c000403c0d1461000c01d90841c0c100b90402 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 145586097 1250 145584847 145584851
    0x30507030f0e011d010905120f240105060708090307120201020f0a1e0804050303040b0702090a1404060e0a02030a080301230a050f03070f0303080a0c1b03031d10 71
    0x94245035101404032205026400c00e00c901c54003281c006070943e4003105806609400720340728000240d10802d01c05005110180204050140100f0740d80e846040d40b5941d142c0600c107102c80d50800401407005114a50150300c4608c403070fa401c140600c8810b502031a4203075001c5004000043c190303281001500000d1100d0040801c04d291503100080c1050744401c046c0071194403291943c404220803840046400101281ca4108010546440c00f46c1d80150740c0708640c14000400c2c00101003103880010041a482112a021035076240001101240c103000414042c0481420000d00020070315403104c80d100c020340c01100c500300d0340390b4000b17454100240030864420402000410a00300145141c071095141c4a4440c507404008a0108d44408000d200300c5110740c40021604080b0744052014001412040400d08055501c03400c000e04001c1c1f0a5a8202075603103040e6540d030f14a481010b10170a21450340002c1c1c030700c00303006807401c034040c00e540e40030311040c02040300c580d1060f420100301e94044d0711148040 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 145587347 1250 145586097 145586107
    0xa050105160b1311010206060108060405071b0c150507051209010903080a1101231f08060a0c12050103050d0e04020c01021c0606030618090302070f031110020c0f1203070f0305 77
    0x2050004c032100303030411815944030409100003071380c00200d60360b8070980a980c0085c0a5680250071034522801030106c0340d030814000c1042042c400d01d012004159140b0790242c10420b11074a1045480340f00b40311014100f0341141480c3c0da0000d98542c02801d41c040140b40991401d40c176910b410b01130340c0c4016078140100341484141000c58400b070280700303050841160003140d114070410030b203007510b0001407804082801001c0d03110900c880425540f001345c18030404403001d610304840203d0090810012070710105032030a0310b4440310405c0703000d11816a6070180c00307400c03080c1c0065001e64451701c0724548940d22503020f0044605200c024809042034284000c032a510b41c910650107442124100d80062040505186e403e02c0490b407003810f1280340740c10300074000403440501d040403801c2040b0780c0c2200c0f0118107601d20000a1100200300201d204504a4110211407403c84085c1d90300d22403444c07500d80052510b52120010310300500c409079541d0501003070f280381020999590403580f825403011000b051003c64 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 145588597 1250 145587347 145587353
    0x201020d05062d0301090503070516082b0306080d0201091709060307050f120f011701050609070c030918021b152403100e0d030603020a050105160b13 66
    0x40d10ba0411803d07625075982104a50700201c442808410468100c0d220351080e144a0b00e00754011910190404207481d02d81c800d9103006921713001c0c0c0d503080f127550b10010100402e0310100459021048140040c00c4201d1000125050240642d25180c04090590328200060900b03002c1c410741c240210560b00008401b007084c5003641d200c95051311070420706a028040844c01e911000102d0707410030b500c0c0c281142c50b0688440b02c484613220340000050b8018494042c404c05503250b0054906a0b6030a4003844001c022800b501401c9400481d0238907480b890603000304164a000d407100c070f1001c5000703251100b02c541c0c0f115030100800840e450340844050b40001c10031034001100d5510000f5982410140c00030600328000c00a0500d0040c011001c40691084c80c2c40000c080502ca000340c1c45009000d40d455070440c50141d80060000700e80002c5180a1000c00c1c40f0100e21a100d00c50503640d00424002d486810040111500d400c10990104080f119444500c04550b005260f1403092100600d400220b20a5103 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 145589847 1250 145588597 145588601
    0x9040320030f0307031d0a03030207020906010203070c060807140f070606120c0b0904020d05190e010915091b08030901020c090f0f0408091002061b09010c0305030a0f0c0201020d 78
    0x3940340080380c0c00600c01d8803400c4a00d802201d0b0007011520700824000c200344100540000c00f85425400ea1080d10104410560036801a10030305000b00e444409595030000160b0316441030361002450140d12150920220340241d5001d6084901894050700560220205039030750b40c098003822a0086010034074008001d01d40c01410080c02c4000f140c001000e00342e43d00d0110500c00ca00030340d072106078003090610b09920b0319410f55070345a2004000748610b0030a045088503c6c0e50130340c0c1071307000746090119451080340305004011a4580c410390385d040884281640e0001010f050b001101c0e40786028480c0c145c940200c071107050140103420040c40d0358082c02000689803006400302d082c05804801c0801241d2002c0d03101041d840301c600510508265a42d160442e624403c440c122a0b000094150290000d580022903500c100c403002c0031280c030a0619061100e80f402102c070910300040f80541103a000910941c081d42d00490a0800480c1c0d12086082c10801d1b02e581081080050394082030b128140c072424 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 145591097 1250 145589847 145589897
    0xb0a0e010227030a12030f02070209040b10150f080406091b0608250c030c080f040801050c03060904022419030b09010807140a1e0303020607030c05120411090403 71
    0x480003040b210101795508070031031855010840c18195140708203001d1505a030104d401d420303402801e0300c016140c6031411051840099980313100d41100e413800852200307440003940d01115072a0300c400d8582c1503118400c9450307000c020000c0710540c1d03c8603815000640309404101c1d040d240c2d8202aa40d0380d052580c001d00d203040003441c01600501101c811a201d02d407040d001c820a0312146840001e4060b20b040070743d900d000c2c0300c600030b000c01c03000200240d1100041d000360040d2942c5200034001921482010500d900066841951001c00d5401280052030401a40070785000e02d0510349080718040d04880780d003034001030302850540450b403031120f60fa6a850710680d60651803c841c141c003d94108081d4030303500c0c10203000d6001c00c58030f4000d402e1443d40c1d801c0c903190024404400754041c145c4200c01b80c581d601030140702c120094815070300402c83c41402400341c103c00410560341e480c1402113006084458076005841987e00c0c04980c402c0c5200ca031541030350f0610580c042e455405245544030080b090322800 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 145592347 1250 145591097 145591099
    0xf07030903091802071a06030708030702090a18060f090309050405040f021504121a060a031a0a0b060a270302150306031e060910020906070b0a0e010227 67
    0x80d00c0c0036500020703004036600c81503800100a0030340d80c2c000c042d26240244544038004d044001522401c400300303602c0b803460038403c202c294140c0e60700c0307a03840a100f0782d2801040d10081d845000880003c078036444a52000003201101d290700555401140c5880e411501b0803402606202c1e111200305003030607005007008008120540303040180d840c0686035100b40c0105405d00a101ea6100768220328881280402d60f8007074103034039034035201040e80c51421581a00940309203503080d00c4880002402480d2440202c0704480d004103150440c030b80440304500c840340b001042030310305030799844002005454100184c46c1503030305512816130318138103000380031100c1130a825500c0099030108024401611065010440c0c80c5800810a40340d8030f941001070b040510408548041248454651100507800aa06d6010b00006401d546c0c100000840720b805034440c1d04103c940000f01000401c000601c842c66290b80308454086c001481131440481c9400d9900145101d803609050700300003403002e040a0050198010 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 145593597 1250 145592347 145592351
    0x81804021608070c21060f0b0316080607021603030e0a030b0a020d06080f030f030907080f030d0606020c0a0b0702011215060806030610030212030904090602040905060109081b0f030a06050f0703 85
    0x1d140924002905402c9100906c2d80b0f40b540381c0880b114000d40c001a0540c01c0003400d6074100c500481c00f0f2408944684500701940c031408010400d001d00210b111011300741c50140d4060001c1c10349c0c40a46400c0740c0394000c0358203d4050480000422540d2400c81d000e000d45a8001d607654400c145500141e820301d401008880c0c01244030a111100008101c0d408101a421081c3d02c035038650b8010344c1000100e0f071206074140a40414942e031032078048024400c144450b542044082d840c0e4000304e0f5120f40f286270f92904554055814041c03450341802400c2c00d940305160914000204206840540b824500042111200d450052220a03001500b4a60100094006161900c1d00f503055540510136031002030b00402001d503081044120600c106c44541c03601400a2101845034900003000750b01a00c2950b914502d0540810080e41c40b4600703140484030700b0740090401424000740d04160618240c0c1d2158010103001c410074407601c00b13000300d003502e0f400b41400203450325095800d0343c0c0189006281c101018 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 145594847 1250 145593597 145593629
    0x903080f1c0e1f0b030109081c05040201020304050607060e01090507050a061706060c100207110103110a20071d0a050606040b070308070c1e150207081804021608070c 73
    0x1040c0000c583c0900402110000c61414034502c20300010161203012540550a10100340c0620001100404820704801c03107154881365440c000d0400ca81040e100240141c0041200300f00c01d01d0110003510382d040c0580c40004900b0031f1210100e00f1118190300031035080d081b40740104180d14080b0040001007040e42407800852520051941c10b180e0001c100912507440450006050002004100002c02100900319552205418000c20003440804517600090800010021060601080c0c440085042d01c80c0d04050340c50008074064501d00220f64581441544000110f11040000c03901032648000444080ba00300600703100203654009166601032a41080b081041c0c185280880c0c2500c0d4162802c1c20050700d405404980c1c04241c040051300a001d501140c1c0c02000c02d070b00031720005500c2001440c09260010145030140d008201c000b0b8001ca10038002c11008444c00d00600e2072000c0300520040ca4510000580d104070814100151000c2e1000300d91141040200e00050300940381e00a1903070144 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 145596097 1250 145594847 145594871
    0x309080f0304090c0c05150103060513021e031906020301080601080106060207031e060203012705060102070501030506031c0207090b0d0c05100e04050c0c120304050705100903080f1c 80
    0x1e00c11032151292244c2c1d00d0010070b021502c2020284411a80101556058800400484800e0100380002e5540c3c0b8540300100f18044001198500d0955016295030210303031418003030701c0c6001495260140c050084640e8050640d03403000c02445014400c1000584a5040204d59440e189058000c980c441c1e1503c0c00510813950002003a108a03688903400c1502181d90103d05440e110800c58010305d420700205c00416040c00551810078054210507816054000c3e19946900380c9206440003409a0040303072082c0159440381d048990700c42d60290480b217507a01c040e850b500b8100703100240d40005800082c01482085958007500c2e0348088202c502c10107029294a5420852080d84501c51284200d42e0301d0011060103401071440d880300c020401c02a62410113081a9940e201c0081400f542c016068080515030580c429280104c0d009030007428214208014406845602c803022418003406a00010028581343c0040241100300440a80c40340e071070b82218402418003c1107100f00f80e062020349602 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 145597347 1250 145596097 145596103
    0x506010302120c090406060501020d030c081803120403030524010f03050a0f090b0105010e0405040f061d030403060b090705070b160e0405090606010e03030406090605070c1e030309080f 81
    0x6407a0122540380b0649000c0d40010715000421a0668000e04801d0030401802050b81c09542103541c2a020384040c601102c204908a030180c20352003000c500c200b0701181c90030805610074543c03490042c040f2441c190aa0001e0050290221000c40000351103c0400c8100c20f0410251000e441a0154140c00300c1400b100291140c40507164840800d0f9868001945507a6181c121460310903024408011010303040c101290400824041d06010600c01c15490400781014420340d880343d5044042d01921440c01e03501d90700500303040710041e44186600407074560151010310003400154490480000c00d0011039040c00040e2070000d0a000c1441814001400840c2001d1403080e44500c0200901c80320070107220065401340100d003d00d5400500d40f0007006804e080004542c1d010340026200c0c1011507580104040d964840d6000f07140020307240841c104103140c05003000e0b0000c1442410001c042c1d54441011540340c010784903200d1a0380b07001540400905821030450720190895401030308090283c5403c180c0c0e = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 145598597 1250 145597347 145597349
    0x150c080a0e010c0f0f030807020a17070f020a090204050a050409030e010305040312150512011803030c050405150d0506040501060c030c022404140603040c061d0907020a0b09010603050601 82
    0x340074000922100e680c0c8901003040d04958456081840d160f0141000440f40a03a154100c012584045c00716120310f0001078018052a80080182d1303884100c0400e1090755003180c00c040740d0441c80b00150b000103a071022084000744ca0103400058840c0e18020070070040300c5455100900452030101000086907001d03045001e070f8842801e01103041d4803545001c0701c4c948148030000ca4160701d4400900d40003591491010111401241e90240c02c0c0c001d402000c2c200d5050400c9600060748800321080000d009411003d50b248640c1000740c145030343d0300081240d201c1e105070489c400c0700c0000380725403015409100f80d980120065404010b158148040a05000594039026041c0003140034410219510341c03e62040f0940c0320354000400400c05070500303815030410b01900d0450007404101148908241003564401c9410039034107244907141030820f40302101c103012041010320201c422007106403034082050380560410790003001c0b0203102e410412002c1c0c101800d45090f03a41001c00030030105900065140c = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 145599847 1250 145598597 145598617
    0x10e0d020120190207090f0c090b0c0607110c030a080309010513120e060d0f0c0206130c0b030903070f0b101e05010809030403050f0c040c230c07081501150c08 70
    0x40c0d003d0300c1c0350340c141d141c405241c2c0080d200e14280054000b0140c002e81098807100e2541d12859845a2250750400090003401940740c0140d00403000078410b0b42c4191b80c0c1e0002401c4c0e02c416182c03c0c210810120342041e60841c0141d40c3c0f01d4001082c014220700c248510307907001c0031340d045441c0c1c03403051651400911612450040c00f0040720310000d410540d02e9004a60140000b41010003143e130344605184080c2c520b000106000d4010000080d4410103503a0b145803845910506070440f05061049000440e00041c010500a12080c40201d00148894081c400340d54015a070210a901c0c0c0041400781c00041b80d00b1040086100c0011a4800c559454175001503030800d0078090300070384d606000540342d4000d030b52003d40315100707405990040300d0780802c45203842042130741c042c00716030050b0400f60351001045180d03600006508400c1c040d02041ea202801e00704080e2410f8410050341c9411031440c00202820348007010800400400442c507034030500b014414000c0c00c2c10600052645c0f980d4049001e200486 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 145601097 1250 145599847 145599877
    0x70201120506010e0d0501151e091d0d030b0f030312040803060d0b07030c0e040c1e110115053a05030f0406020d0f0206091914010e0d020120 62
    0x210301c02d070b80100102c181081000d45485281072203810300901800383d6000240303104090420110302540c10850852100310712604950500303142125060092103c401a0081301c03120146401441105021104546281e030740c02086c40640c45c81084a004600c080140c031a5004001303680c80c01d0120340c0010751040c0c000c151103899035908004609004202030380200071003d41400c12244c0340c2c0580c840c0d02e2500d0103503070303448001091800b40030440300f81002c9100456491034040030301002c01d090342d80c0c1c10602483c02c80049260a02c40c6802d540d1800e4900c0c010f8595400b0600250800481010524500044d61a002c080080341e20b9450a00c0c4009c0c80c031158004c55000c004e00408204480e80032000c402000d50711590741c80000d46035000440301c5000250b41c031081006461000034224000e05800c0302910700105112309403182105060411202c12100b400c62400c172000a10074000d0039488000a13144100c120b0390002e08444a4502600310841514150540241c520080e0741e1015044992 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 145602347 1250 145601097 145601101
    0x501020714040608120408010c0503010f0e180712030e060a1e050c0d0c150507020309130b03010c05070b0108010528020c0a150c03020717070221010507090b0702011205 74
    0x480c01404040d0800d44e40761081c1ca49403060003058034014803c5400d00070080150356440b01086460340b00038401c000320030164807024844520100b2a40381c203c04035444121261503440079184c00e0090340c1c2d019022005175090850280f42d0014400b8049000490b8000d1416050b504d014101c2e5182c03018140c01070a2036464440c1060160b000c49220b41084022540000c0035460300800e000c01d1a50100c0c1c600c03560000490880096008080c01035196801850503e6100d00c00d024003141400032a070000c1e92034816440d4161001e21450808a00c50741d00c0300d0340c401d0541882d122080c01030b882611030707a14020070480d12181040318580802c0f03004500100c45030690384000040e0207100700c0002c1600070010b9210420815200388660054401001d110580901006400724003078503401410324481400b6009040d072003c0010400548011304011001200c5820103030146100004081140c0d966000d128080c1c0d081a4000000c1040f03000c1da0703280c4802079000a0030081300352100e4200c15100e0340 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 145603597 1250 145602347 145602349
    0x11a1303030e060705100f1b1e05041e030201020127021c05060a20040308120402060f070f020102070f05060a11010609020f042409030b060307170f160501020714 71
    0x115100c4c2038104c4122128481d2400d82c3c040141482c0c10340e02d07a40d40c90404c03414031242d0a48a002c1c0f01e4011515000300302c0d50f02d03046291107148041d90b0749080003020440440c01c48444000c0d0f120b2035924880d2124100d083d40b001900f103800c04240b14030901e01d181c207096aa5503810b036050303400c91b5054401280082010f66600c500403c0a00d0003805030082004001013000c0e241d105988800c038100340001c4a6021840400e450b21030b0f80000b0300701103c100050442d80c000c080805404c144040e00f49490708501c014401c1003038104101c115880d00c0d0a40750b500c295a41041840c010380001d8120322001458000054050b1181d611104e0511040a500141540c0300794000310050109100565407050100c150350314580c454040c10301d100d1b0150310490981000c1da03203410701d19101074841600c03450030350300c0f40e000940c0c0060820782e040c811481c001c00c949e00c1c10b04000300101e0f4090300500c071004c4a844480c2c1000c4074040359020321251aa020040c0da039000034010b04450325180a99100c40007a0 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 145604847 1250 145603597 145603609
    0x3060d0303021c02040e0f01170705090c0403080703020307030306050402121801140106090509011e0b0c01020c160e0612030a050a02120a05030907290307020114040b011a1303030e 79
    0x80d184003d40f011800140340100c000480d4803645c5590440d00160b80c1f43c035803941d0340d100d099001c1110f40d844040180010304040011640004107203074580d060690329901e40c000f55001d09002c8006800200342501050f815024003006803800315410750030032140582d14541060020502005064801c001555070304c400c1d0b0100500043c405040e41c0950b03101c56010744031074414810b82d805540e2440c0006110300f0018800b8110300b540d120b422410301c0c50b011003031b81aa042802202c90300d542c20030560b504000b042110319450301c15414040c039803030f00e031000c01521860020181401410380348489800001c0102c00c0341c02d684c0302d0f418041d8445950400032841d0500ea1881050368100000e61030080580200280d0701c90712801080700d41050f03e80740c1240040c001e180303003440141170000c407941c0200706034005183e200403148000902d0020740c001816207030700240d41c1520184070320401031052540304e6903040d20111040010f90720b03103052521034070504000d5120142c200321094a0349001c030390700c0b1 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 145606097 1250 145604847 145604887
    0x2030105012903060306010608060315070e0a120b01031401060f0815011514030403051603030903030c030c08010918080f09040614091504020c0106090506090c03060d030302 76
    0x54000c00c040d40e103030041c45000103101e40780c81c2c2003400741c80340700504040c064003100d01c03442d80540a40b2459182c408142c44410020b0403655150080c01e60002d504030140b5140c611950380c542d2060b0081400206102e170301c2c00650480c54682c48803020720070209000302440b41c1103d0b07200d0038511046d40003048507401000389810004650010340c1d8001010031001440c030404c1c0c2840184d03045039982e500d00c884100c814068820002c1003400082d01400c8000c00003443d4813900909001745405a03452080b0030041c00c0b00001c4020a607500b041070b00f810350600c2511504c0415050400040c9214000505800f0741403040d042042e45581810588011801442001325031001e001c030703201c440c0c801c000c21950301b1401242d800f4034a0030f5000144403a214072007030100766001d40205030a4842c44110095078694400c004d4020b9000c05c561a054402446400b00901c070881d030004007800e000c002c00041c1c46018208c3c4a40d50020f20901038655202c06001400b47e606050042e070b20343d0f034260048000080 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 145607347 1250 145606097 145606099
    0x302031c0f0c091a030403020703060216060c080f01080304060504030f0501020708070c1404050c0307080403020715022109100503090a0615180e061501020307061109090117060a1802 80
    0x104038071141c20a411114500a450121500c98a400d0030b413031074014540800c03900900142d200c40810004185c140d070080003209050f84400509040b2501c2c0c00d03013582d80d04444800000c0410007000f00d0601900d03249805840307508040c51502d8500540180940a9400302516041c111001001000825811900b1540d4880400368640b070450030b10403c90403162107203c0b56280418801112461720303100b80c1d40701d8080c0e41d040c2ea0840d1900602200c0c07a0702d00820480562080400200d03a005c22011507081c60103203980100110058114045500301c0c00040401c58118188201c620a5940c0010040032401c141340c52070301c03955240200c81c5400e003032000140080d0301c1d0045104144e083c8080e05010303190401124010b840490a540d422550701d801030800c0354200c01c003c41c4412800902c85a160743c4144101d03420500340d0b480315000c88917800004220101c00007041d001a050507403826004200d441b2055940e502d03030140054440900070701d800c0c040c9507a0b40d01101c414498a41d44031401350 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 145608597 1250 145607347 145607351
    0x30b1906172107050a03030b0609130c09060c020a03030807021203040501020703030c0e0d06050a0608061f0e07120c050714010f11070519020102010e0d03060e010e040302031c0f 78
    0x403015411920307032207455003940c4240c1540d9440c03604542d9a0b01101c0303400d54044000c0480583e60b8600303c1c0206411501f09a101104012004040d540c00700302c0c090050840d500041c0c9000556400b034201c2c20700398003480070b024502204d43c3c0965501c58024040301e416080c914825660700f41e08034100080027120314260074002c0180400d114055005d4806244691420044402501c00c10b507060354000603125403010b000e4068100146a40c0c01054002407602c01c0450040e03220300400c0c1c01c04400702c8100c4c00643c04031007845030748064459031400600e2102d5001e41181071464000b0148240e0f6900c1c40f002795183d41d40c042c9283e215004a038006030308101030f501116408415540030380507040a0080d424100340b004070000410f2000c80300442e034041e004200d51400b046c00c2e440021a0004180c2c195540c410010881040c1404002d5a400c0c060ba40050074ad41002502c05440314180c2286141e18040c404020019800100f1105614590032009501f80801c100d00c6018040f2904510f4281d8 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 145609847 1250 145608597 145608629
    0x102031306020f060f01150c1704090203160309030807051e0304081b0102032205010605120a140a150b130e0d091a03010e0a060317030f0f01030b1906 66
    0x20b5030100c1c00403200041581518502c2c0c60383d1255121910b806e00411081044402c071124666024108507109a842035140755496070104500d400c15801690141d8403040c0c0000411000c11500d404880c206003031340c1010040c00400d901c0051120000500d18018400d00094103c035402881c1c10380d480129522524a699143c00e207880e005540100c901051559079511005540a6041c003d1b82c1c407818444034890781c112a65480100c007004100c50564895603505004038041d10f9038901c01d90010000d0008080b00b40c11850840c10107035010100e20402d80040c8105400680703049044804109031420100b50f48003104009221141400c41085a01e40740050b040d032500000f0409610801e640c0c1c542507603199981503162141c010304690401110010801403240500031162207400150314040000c0b0300e42c8903611200c0350600c0c160100b6080c4404010408901032102183d60310401c4000072040551440d03032001380c102400f0306010301007501c1144080e20f00c221a4020030003051f0b4941d00e070040d1 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 145611097 1250 145609847 145609859
    0xc060301031202190302030a051305030f0123060a05060705010e0a06061d010e07080c041e05091f050f01020f01150608060328020a03060c030f05090703170901020313 73
    0x1182d2070240403000b600501e010413040c205441d64040c0303503036090340155140c4881850111030684c010310401c940d981030200c4c04071302c1c1c0d101049460400209400009001c5030795104c0059070890300103842582c803c0b40300070400300d601e51000700c600312403082e900c283d04d904061810070301400c500045541c0f144074520303054052101d507030003000454520081c807204000010010880300e003001d01070362401403110300104214611524081c0d074800d031031205140c03c040d10754090200c8100340c0f05000b8a102c40541040c4030078a41303118101d401075801001003020303c0e030341c0359005481c8495102e082d00c50407440c200c040c243c3c3d00078802c2200d0060080000c1100c5810782d03103000c03c1d46049002e024001111000082d200f802d002034802c0c0c44141c401c0680c82840c03030351040c510f200200600200c3e00719035180d6001000620300d0042c01545882034401240c10401543c2d0001180c0700109119801d40c01003400b000802d403103100c41c103030410400400c103544000320350040c0d1540c81080c0c0f00102d419902e107400600 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 145612347 1250 145611097 145611113
    0x80c1507020418020f0307032102010603050609160f05100e010504051203070c060201090503070b090c06030c0306042f0315060f070501050907050109140d081803101406010804050c06030103 83
    0xf07500e20031586080d0781c044107070034140d8402e00c1d030000a010381d46000d810240301c002040c00305e8910820b8400411a142c5075560142091816540f0030b2850740146000d00e1754203940003004018150348007250381d13843d16120000d2401c40014035640e00384098100c01041d41d0744140100c80c09007001500c907000903101c400b0504d65a030311252054481c10000200451840d00c103000d08416140c1140041d0309041c00d81d21011401c81018040400d144546c1e10f80d00c94548807070020714800c41c6072466591302d9250000920042e80d69440c03810041102d980c1020b400c040401c0402040c24400c044a9603c960321100d01c06c05100000d044144d10210205096000740040c4000f40020781c4204000d00c042c5e103800c88215a40d0b0840d01646000c68003c08051140c07403440d404d913105184005003640e0310307520306d40c450f0071240c1e220200b6441c0124a503c8000341605041080190038203401d03070b0030000000e4001d4900e5042c0000f42100b41008040b4011505001c0108000607125a0007000d01c0d0b076950350f82c541811 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 145613597 1250 145612347 145612391
    0x50705010b04110a0e03030909010308030a020409050412081003050706050a05040f030f0c0f080d0507060902100e030708031e090a030b0a02070201140702091f0306090507030318080c15070204 84
    0x3c100403044109401c011007603600e00301012788901c805909580d103c10b0560801400d50075026401d01c40041c00384030074001c803030065020b00c50040d040b84003c803004010200050080c440c00e000507104000003100050480c1c21103983c1d107481d036203c0e0744c09a400c94480c0b1450f440380104111200020062014942c0c070b00700300d00c0c41000d080c918595281e010411003006c501c10300c0b00c0341d0000d54514a2083c0504028030446101d1400010030f50b200340d00040d41418071001400000e011480764135180d044c00c10409010340300c030300c00840c101125004400a8140a699032003925107000c113030744045440c0c07111080091a88000782d290b06207014040d1000a401c10803003640007981e00c02110102c105054100c819403500074200404540d2544070f004080304501c04810000101c0040000108440703100e840412803046000e40309291550400070a80030001491800d00240d00100308118000010692400b1748140c0c4c08900f41c100e8511346154902440d48040d401c00c0c10315202c40114001c03c28008 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 145614847 1250 145613597 145613617
    0x17060a0305100c0f140d020a030b1305011a09060d0c020712080309010c0e0924040608060a0b03062401020102040f090506040c0918051321020c030a0b010501050705010b0411 76
    0x51300461102411184144084090b010841c010868030034948295001020300c04110b00700803900305161404585900046030f0b44441227642c550040c0801d4100305101d542409031b401c5160300b0000c00000046581c400c4c0c108401d006507881c22121050b500074402c10340203111108084e03040b104141400002a4011138070000f46d035282ca0800d8144070f01a0303d4110449101611181195507000e49800c0103c00044003580b41c800d005169107030130390b524043c00015001e210301401040c00c200d80303980242c412074001e141c400d40028007003122200c40c01245816a440686603148000360040040c0e00a10550700300c0c4078030001071000866004c10315041140605415170f02040441c0b06958101c83d041000d003d8400f07100d007860350f100300394501c58000a420810751030307046d0340050b1540e071008100b55480308000e0446404070080254244c060004601d001000e40182003408200d5841075107040050251505210002c6955018040254401502c10002a00400141ca504400243c2d65040800c40c1 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 145616097 1250 145614847 145614857
    0x30406060b3a020f090307380f041203080a05040b010b0c010b030f01150f120308070c060c090801110c030304062f04030c060f17060a0305100c 63
    0x301c92109800b262401030b010301401c0d2200700154800c1141070001081080c500d115060301039000900c80c802002e003400040003c40d40d90170080185818043c03031790b001000c0c0d41d09040c3c0704e0300320b079907684007144141001c00b0040312514480001ea00480c015a10040b8407810042004900f041040c54184c07100e60098403064a82d5551101e9038060340c030200c0d8000d10411510004001141800c03028201c142e00c09030010884285034070100c0c1c90001404190b83e4669102d040b18461014481c0c84030000c1c110543d00d94445606050741d204684c00302c020000c0806c8070660000e640c44c0d108010ba854900c0c1d100100f84001201e403103004040000c1401040b01035440c014442c03005107045c1048402520b0401c01442c29940c0340e072200d000401540e030404401c003681008003564880d0320748202402440813001c080e151821420070701110082d03a0803401c240108854607029a9801088645803030360360703480804c110340d1004042080c40381203500051091180c2c1035070000c0c0c007006030410320b20f8402690362 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 145617347 1250 145616097 145616099
    0x305010606031d0a02090606040e10050910060512281d010605090103020f0409150203221e02060c0a030201021207090b12070e100302090a15050d021602030604050303040606 76
    0x190b80c120f41002008980540c0102058030041c2001c10764107910020003820700307050680d01c000482c00702c1e008032140d01007103d040b0170078405840c4c0494032030f422407504409619030b942011005000e40c40743ea0a908050f03649200056207201c1040c543c0d035003810031000050718540d180123503907002c1c000e2204005455080340181190b900d0052141d68111040184820b0241e441c513028800c29100c10305455421a0300c03518608040754140300510003003943c10f440142e40e854100d8144004050ad0314600440c001da2101341d401007005c010055400103250102540340b81507074400035212f03102d07000403000340d0701031800980b041c1078040d4050010b4680740c594040c01c03980c41e4102203d50000c540903601d5070340740034440e081035410740864035544001c06040c08402c0016030400941600620a101000207400048a0314a41840f169881c01020200a000c205551004018100d80186a010302c2e4990740402d80c1c2c188004104440300e1003a4010b03080c1c0d095030605040080e140d078000c503016903182c3d06001d4 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 145618597 1250 145617347 145617371
    0x60b0907030b0a03110d0b040515070201051e090c1504050103050c130b0a1b080304021e09070e01050904060f050a0e0606030c1b100509010b060313060b19030501060603 74
    0x10310b28061400038a4100b845045980d07580001009004c404d40010000780f105001904101c14540214092001031804481800941b4182c0400414000440e4100b800303210702c06455400c1040144041c0140d01c68540d2007641c071510b040702210391294486000d8180d0800c08034082c0003041512001e0340c00740b20942d250b007604c00c6684071384000c0300160710841d08100614682440039041c00031040c500300300f003044444008800306200501c2030b950b03d10000140f004616004000c4e805d1a00000c140502605200c0300140e40e6107030090108051041c0303410103d903030781c1c800d008440107103000400401c11241c50340303245945001d40c2c0c0035250042580c40c2c0b02003078000401c04001e00c9400002c050500d10b54070748a401082c1e8020b02d144c2d0f10542141c00c0d04010120050204200c482004040041e041c50400e6800e8255080d9002d03180c0107400400c14092800c8044003009040c0350030a9001c1400818500400c500750020082200140b100301d00200400406420100c02c8500554091001140281c = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 145619847 1250 145618597 145618601
    0x7020106060309050a080304081611012012030a0e19020a05010c11060904090501020304060920061608040506040b0c1501050f150d181a0603100b030c0d060b090703 72
    0xf070b002504652181c80390400043c625801141d01510510030b140c1860044141d8640144042c1c2040340c2e03c03c0713800079000d500d59100c421500f804c0050545280360710f0880604c4e540302c01040b213840d42045000400221144455080614203060100441d140180601c8415641c5d2100c80740483c1718001c2080002000c0d032244020700400d58009150f00320346000c0c2010044a03a110124441d00182c07101c9047e0f010540a02c040d6100302d00818000c62041c040d45050031419030002c05003410b80d021000008000d4440300300366152400301003841d222800c01c1d4204443c01c0c4c00f0780e620040c1d00a10001e4042100c44194014203042c02321501110300c10442000d1501c0040b909004607034000d00750f05244412454031480c4c201d6400300d41d10b034030740c03502142c6000b00d030644100707007000d0340700040c131003280400c00c40c07603482940106200441c4070126051403070009480d500818106010a0303204c0c413000d55580c0e03042c40b80712810704008194209190582c80d1500103450326030580c034414901d000c005403401c0c0c064 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 145621097 1250 145619847 145619861
    0xc080706080109150905010b030714130504050c090907090608010918150906020a0306050a050f010c0b0a0b060d05010e100b040603150b04031a01080f0304050108131703070201060603 80
    0x65250518141e00b4403c18100400d18440040c08a030402d04002543c40900e2003090f0283c10764410a59403842d00c2c1d01d018241808004101040002c200086003803640d003641024107603001201d020595441e0b03201c084609000310706030a41d100004a0034416034981050303982c4116442030b10355281683e610880c007822220090303100c10181401c5298040003d0b003a10406040306003001000442031803e40354a0200d81102a0100109541e07a405000c0c40c64441c0c900c20003480c04544161400081c2c1000030b0003001000c100410304602000402d200614039004102c0030b00f405040c06494409002820010708401c0c0b19022200d821080403801007621400060107035642d0800c0c552406140000417001805240c4501807065a200c0000c101c180000001740300650180d020745d40010740c031784040f030500c4c60182d1195480ea40700700021220404040282c400325807017424902800c3d41c80c00001c90391007001020062009000741c02d0008941281d2001e103000301503d82c003c120f483e0b2144410b500310b54034 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 145622347 1250 145621097 145621109
    0xa0609060c1415090f1614030a0507270b030d05070804210201030c030902010c0b071403100e01050904200103021612140a080a110c03040603060303020115050d030e061b0601030c0807 80
    0x8201c6d001e1242007240c0081c000480f0b00982251800383c0c87d91507035418080315400000c282181a001c140700300c4104e590300002c00030090020040d015000c800a6603c0e440e900e080400c1c03041c04254035060024100558000b00244461002311014046141c0015404604200d0210380741126400380c0512a120b40c0710283e40c107031501c50441050f6221950420001050708080101f4800f010100c50078035406113000780195007041d200f1a00b80080d00c401d804050b00440d0103604020100b0000c25030f0240300a403840030f0321000400c4010110012000380c8136190700131091544101581041141c0d403610722010301c0207a40c40c4015180c1904018140b403041c43c82d010002034000011030f00740300c0581c0c02a0785a074043c0000c5840c01186c44069030070340c0c2043d445500860350780d400410038544c0a008404003803508076520441d00e41404001003140540083c0541009105c0c0004909503c4100440ba0704c0c507055200c0075144080307000ca07183c1d030f0b41c0e0074001119007206550000510490005118040c0c0f21 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 145623597 1250 145622347 145622383
    0x5130c020c12100c02031e0310090c09030f0b061e01051c0b09090a0c0602060c0708030619080a020a080f0304121110050a030b0a0609060c1415090f 65
    0x2c00414807006414414180140529540d10358214403800070310000c140c02a645500062640b5048490103540141c1502000c00070402c9200210003204140d03502480300154129100c13000702c07020040740c0c02c0100b41c40d249952000c02d10080c035900603c0342b5000c07036484040e10042e070100c21018041441c883d000c64820304c15820340c41c42d00c1001e140c69601c0041d00188a0715410001b41e08580b05030380e42d0041c2d07042301321031106102500c40048040d1400340010611400d00383d455003000c2c03003a0380010703144620100105680756110b0102003070030041411960704041d222171074903449a4100c8012441a44007035000520048007040e018400c2042c0400345040a260070841d80240d002743e881280c0f07503036079000304441030b6988281c841d032900d03480d40e034690312618141006030482e10316607003440c8100c81040301001815805828030050700c140707107880340c104811490408103502000854410301d01614200e460b209031482c120501c5958403604a0764600a0180d000351500544e81201c10100 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 145624847 1250 145623597 145623613
    0x22406120106140402070f0515180f37030509030d0903020f0d150203100311010c0c09020c030c07090b0f010c080a08040213050708040506071d04090f0f08030105130c02 74
    0x441c4c59405040000d019010f040e50603c1d50307035626410a042d16000381da44c9e0500e04140112001951100e48e600700d00745000701080c4a070754441030b5507012a4040324401c0300701b461400324401030080c00d4489003024202c210010103640c1c60045d01c1600a440c025000b03220300c08800c50001e215078802c20881c5e8010340728041c04810781e41442550880008240e4a801e070030203002c40050a503100540c0305a4a018094420324118070f0858019020188141c0c100612440c0401c0400c9078101c6280458405410050b580d0b00c07600740050640c01400000301090040600008040901c1c0d003122010341c50441da40035242c1123010064800c3e040040b0090500034041c4904c0d00d03128004c5990a82043c0001e00c4001202e0300003400c501503c81c00c44000002800c00317405e1000f0400c0405c0640d81008403801c01c0801d104940c1d603c808603150b11441e00380b06640303410080c0306000d90150403180c082d0300139561210000660a24041a900c2072143d18000d444421032505d040c0260300c07640c1608821507029003000 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 145626097 1250 145624847 145624849
    0x8011a280c02090709050f040b030303070c140304030503040314030307050a03361401110904051005030313060207080d053a0b01030510080c090702240612010614 71
    0x9014100100500c09240641c1c00035a80303141075148100c07a02e6540c24640c0d4249028844580c2d110f107192802103050401400310303aa00403082d070354003010916040b2101607150070004929004400045270b2804002000320500c85c000c0000c00030b0740d003d480034001552150213000d5483c07004039024800a04c0c1888000b000620075003088252124021381c00b0031200900c7c2c1000840e51180d100507070002045201901000309185071102560704400003045000d02c0456040e00502c10000f4080c4580d90360000140d082d4075044511001c1c00c0c02500301d0ba02da00c410140044500c40d81c0c00b030315002d441440f500007103802d40003500c0c04030403925960b00d5090180300480050319542040303001106c03007486e0560085010704e08040400c072003042d400210b00420f400c0005802c07298040c0981801441205050105260024925000a100741c0c1d1025043e502c54800300d04000c0181681b102d5440e207400704044002c03a18003101d01030481120300c00e6032140c0d04201a803c807400d17071080040c00c4210440303006c05 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 145627347 1250 145626097 145626157
    0x100303020307230d09051206040b0c070c0e04050d0801080303040c0315020903100c230910120e0c011e0e0108091005270a03020601120f02030d08011a 66
    0x10b4500a10f5618011111240341d0074035007003414100008a49910070010380c070b401900c00d10070501d0341001d000c4609191b112221140c80c000c00b00510200009015810800051030f1400181600480483d090405260141e2558200308002000030315000002c14412008411280256403222985d0400b600d590342e100114080051000102503080c002001c0c9610140090402070f40340110002e034030b82413444054201d00a4810341018070201c110803903009945e041c00c94004200c1150760507040f05030044101e0344022002c03410301c010342c00c01c004a050300c0c0d80020074201e10702c02601d070f140c50144040140501c49001c0d1030f01d0750000e410030000e010315500681c410b0740c01c50200c84c10341d03c1400258002c9000e40740b0075100c42402d240600304851120300d100f000da038200d0000c0c1780a00a0001d064400a5941c04180105685c00c500310104104101040000c1030106a000c1e0603503001c000c0d075200c0603100c0282407107030001a130f118414003040c644007481195900c40307201c4200c9030405828a00102 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 145628597 1250 145627347 145627373
    0x108040204140403090e010b0a0c110301150801060306110a080604091b060801050405100b0301061d0405070201141006020a03120f020309030304050c030105070c030e030c0405010815100303020307 86
    0x1e0019512884403445580420300c85200d28080d0701c03519446490310011030003800301648108003401061095101140c4c3c030074541800fa80d003110500e03007100d002c00d00080c01080c03061505826505805400541641c0c10340040c0205ca001c0e04c010442c1c240c170350700b040f4428442e21b1750b02c5002030780d1540001d03810f2070184d0011400300c2c001c40c0001c24064446c8103c00b0390100c5078003c3c4001c5840803004011501d41401000d07406001c4000124119192800b4482d860106015450030f115420808501500420b80f25486400000b00203100b02e040500020303000385188589900765060907000584601070899802e421140264004d2182d0202c903141100d94069501c40c000059450f801e90060100d070741c0c001395000b02900e0001e5075590a092500c60301d0103001d07010142c0607034100002c10524607009803152446a401d4241240c0080c0e03a100000c1c2041000024542e015284c480003007000380d80003a00c16980c02c900c01d04c20400c1c2e1142c00b04a1040056440010016072003000100b00251100366031803 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 145629847 1250 145628597 145628599
    0x12030605011215030b0a020c010501151e120c0804300f0e0301020a030e0f0f0304090e010902030615010306090b06040b13030f03050d06090b010e0f150708070c1d0601080402 76
    0x2482c6980365510054001c100b62100a201c87d00454141c801e020280b155a0046c0414042820341d10fa1408018091800822141d1340303c0c1c6d640f403050a1002c0c01403074507100c0250403100800c94144288000fa1007441c041e01d041d43e10556901d000808040543c01c0c140020011000ca4050b018116a04075031800010700c0400400c0115661000e0300e440c2400034051000f41c0342c0300031841645000d0414a000b8104214034402d502401200d09440400310450f020b1f14900d040119020702102d24113400f400d00e10303800075014407800e41080742e9281d9089100f41c00c444266001d08c1340329500c030b0307084040d241c0e4000801c0d401041040200144080d600003080b84004404e000400070b0b07640e484515100c04114004d9000c1400014015540d90302c5100c2c1201410070030004114600356900000e0040341c060034030a004030403035482c1c003090760365005e000c031441450910841c0d41d9001c1c0d07140156068008440840700c000c20b162000c42c601006408000110354407480e103580c3e82c0d41d51401154107040260040e = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 145631097 1250 145629847 145629881
    0x4200604030206030f01031716061505130608100b030303010e0a060b030903030a0c0801080a0b040c08030a0c020f010e0102030f0f072916020c0105031b03010f03120306050112 77
    0x40c3c039030f000075512803403202140c2a031561450503c482c141e240d13840204030940c4108290020382c411812040a0310307030028030005d02c8901150042154429641141c1e42c0070000310074142d95003160350004400e031803c0b0030a507910215003c02d8481500c80c00c0c17102c40c0e41074105000601c008181201007a40c004040c0e0350109403599181c40051041c0d0080d038030380c0301c10340000003000b001c0002d40c040c82c5c0c800407e601c4c1400056142c0750710251260619a402840f0908080214081c48070080700d41024144072402e5179603582d0500b07000380100024940403030150703e4403410380741c6541c060401902c500301c040e0050351a0129080980e10554441381d620a5202da09200a80120b81c3c03052440c0040c094928940c0c0410500a0308643c46a20050282141c00c2e0006070181ca5a640412424211035003070801e81c0c0c42e40c0343e07515030300780c030390b00250f03909090b51404000042c000c2c448200d281c01b128051041e4200c10380c2150022000c1e1407417030144ca03010a00c80422170030b80f8161a072102540030612004 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 145632347 1250 145631097 145631099
    0xb01020705220b0406030b041209150c03020a050f150f1006050c0f03041203110703080a0c050307020d03020a03080705030c1c0207240605030a1709011404082404200604 74
    0x4c084031055041642c0701d000741e5041100b0000c11281811301d4260700e04068013440c4c5005018064040e0010390071f010042d079140980c08140c000c10010894a038041c0035100100420450140d03981c61880c1c0059081c1c8804d8049203442010005484c091118000128042400d0240a440781d91242c5030300c1d09644582d240c1014403c0c3c00348060030181041c0703660414580c02c2410010039010301118941410340100000300001103402080710911140360401814035030507400d007203055000305d0401035007101d000e222030010194041383e25090b03244aa2124400e81e250101c0481c1c0600080b0f5003e04007190400c40f08030b4041030503104000c3e04120040240c030713010b0550f9481500d0a580c1c46000c020150020078012200940d0103510040c03d0190000c28002e0f100b030f1107145003400150b1408074aa00006845191a40306403203a2024500c2e0b10341480d034079642e809045075180b10080d440040c042a40f8481c1c14040046190716000ba40c00c14060003002c00c1c0349200c0e100000c0b440b802d00ea0b01c0300742004 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 145633597 1250 145632347 145632349
    0x30409020d0b090a020a0914010e03010204080706021213030209040807080c01060801061a030a050c0408120909060405010b0d0c030e160e06030303130f0f0b1305010b01020705220b 79
    0x1c2000104004010481c10000b005009600d00042c10081c2e4890050010806095102c2c0d01e65003100e18180d07480c504600d808005940c40300030841e6054041d400001d000c20f200400003840e50482e0610303070031916031a685800d55001d60085000c508901900803408102510307007400c01c2ea4019000740409480c003607407541d82d48a20b5110740429034999445400c104010303082885020003d0000903440c0c030601c4a0000080140d01c0020143e00d07031a65280040780500c0c0302d0b08155400717001003200722030700050358800325001500034004040c17150f404030b40018003904142c00f0b514122100b00c1c1840742481040b0303820b40060700401c0c50700d00402d0341c0c0341421200c8001c00c2110380ba120340c1c0884420402824508440030008000f030217140a80d01c10000e000c05171403580081200540c011542c0c0d10080391501e000c0c642c499080300050042c0070700d032003840b102c054141e403400c140c244541c000300300b5641608010782e1a06264071540e58046a00c0c10707e500300707041113868001804200800056a4101d800c = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 145634847 1250 145633597 145633601
    0x60315130216020a0806010803040519030203061e060607111002010e010519050a06060207030f060e0102040e150d020108240603040309060906110325060608101109060702010e03030409 81
    0x1c0c296502e107400031154109600780207000c2c130040d102c0580900103030360401045c80d0f92031240740b141038081d100c1e141c00045400340b11a080006558001c0940f007031030602103206c1484010200b40c0f00460015440450760519004046440d21640314aa8441031402001004480843d0311120420f6540300d070195138580e0020b2040798031801c81050b140405200c59280302c400c0714070050400c0c104078034000c818420940c00045d01d8040742c3d40003000d555168180d00c0c10314050400c070241e01c0c01d00d600100e0041080c000c0c0d2018580b103040342d0300b906070a840c5044100000d40341541c00c0a1b0200c0c08800214410300103003030000548a091030104512603c81c403001c240680d0080302c06800062040c0802e00007164032900000c018140c9140c9200850615045039850744102c400300c00044003005145081034004d1000300c1e046030342002e000c004856a5403030203600e5201441d8008034140c41d0006500307a5920340700a0355a014405081d090130151304c3d9005644a2011082c1c482d418802480002030039003030344c = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 145636097 1250 145634847 145634857
    0x8060621191d0a020d0804080105010e06101d040209061b0d09051801050618210c0402070f020609030705031b0906010e01020a060f02090a0306061a090603151302 71
    0x190340c1410210181919001c55103480150480907584030128000c00c80c2c0011698901da4040712040c603000120719100b40b5611895000ca01c0c0b650904000154848409030f102d03114070011b0300c2c1004a0b16030840112482607210700c400e070290450140c0c5600b9030178564080c10f103003440039001c03610380401059503c07400008076034104400d500c00f650400d0015880100c20300100416210f20803a200c804070401076001d4140a1540a03c1700410030114440307840304140f0050350040d09400d40a010415000074005201c03107800405d12a0b842500b015060520856075800c0e001241c41c50f002105070700300300d1694403411a890b494446c207000410280c0c2e00340030860000c01d042c2000c10680442c00180800340c07400800d03282c1400315145c0b03c0f4042e40d80105800001c036902944c0000e490340c03000b1001000b4002d16510580018000380040308100c0e440d030092007a180650801d032810048c0007910b21840c41340d071004642259052020400710030034214261021680180080300d404440c0c7da0241c100d8100e = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 145637347 1250 145636097 145636111
    0x40b070315120b0105120604120c0204091703101a0a1202040807060c0c0603050c07030c02010215090312060405060f12070b0d0b010806040506010206131410050609011508060621 78
    0x1d0003004008514250036040034216080000c1c03c0f2526003901d0303208034600c3d031027216002d0004080e0000115500ca500c00440c0b160b0064011429080826104c59030750412512182c50070618113010418922128544649d1468802d000f80b500841c0d000440710b4098000358055881c1d000c1c000820612170a1007140080c041c541e64144000119081403c000c03005030b07003c04149403501c0d041c484901c03880700407030b44025010308000c1d41c22449840104e00e40720040303540c1e4105084c1c030824400d002760088002c00c00024000035140b500e0b11080e01300300845000b0f44496904c51040352010000d810300c0c101c0c41044078005019a40000e50356080207404d5800001406600c0365241c0740001c6a40c0c008540b240c004c2025030b0200800d141080000c1d41d25400a400d075280d4800d20f0744160304101030340c0841aa0100803005881e5021381180b00f80000c0c080c1583c40034814804c810010800a201200c10442c119165403101c0d0300b511280203010940e8402d4086c10283c000d001002d07181500a603900c03034001c0030 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 145638597 1250 145637347 145637363
    0x2070f170109062a09030b06060f191e11071a1905090406150c1509200306010e090303070813050f0606010e061612030b09040b0105031203040b07031512 67
    0x80444c0c8142141c50201025030034004084400d0000c00d900e036520f90307070118040d141590b913a584c540346000c07a0b010308104050050b681d480c65903800740d413007800c54079560803201c07082481c0002d8050541d82041007103500c00d00d55000500030005284201c0030300c040382c146080a5840c00080c4040d0f0780902162040c0b80c008142d00041401e040d013401e200d40d1000308040c4130000c1000b980c0010082c854191460050180c8007000c6888201c50345a62101210780e6100d400c00d035100300b281140201a43c14185154030a009040c0002415820017620034820816003000e9851a5a00303141660840d2001e0032104000a0300242140000c4041251003100380450004089514041000519081d042894140540c00a208203940c3c400b42204462404d5032050300ea80301000003810840051400840c0700342d0003071512041c0024070040b03100d024140e075002e509484000c28254004a00c0d440250b400070410000280043e603540d00c00d5002146007003100004170342c400e507250420010000200001e8071111 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 145639847 1250 145638597 145638641
    0x402091c021003051312121a03060612190309050a03060218010f0c0305030603010b06120a050a050601090608060109090f06080f0708030a210c0c03020d02070f17010906 74
    0x1141941c10030300b0800c494030b070030301a07881c000c03041007206540e09100501036400c441c2d020092130b000d01c0b0002d2004c818010100400400c518490080d031081989050003405a080804c05c00d04206021149820b450f600a0070356008401104081c0d080c030710420703420010400b201240e26a180c5000c1c5000310301584000d42c503008883d020180c0340003040c61240c1030088400d5080105600200e0503900385c2d0301800c202e0340369519403000c41d01400e64514141d40c40034001030700850400180b00841d0052061040c200650313620510480111201940d0160104d000303603a04111051040301c034036600c10410326085860503918031101c002c1e0f41840ca60351200c107403100700c24481548104901181007264000405420f450b1810b065101e1090312070306000c008090305001182940e4103400a80da1f000c3c85001c03c00360280e44001080d0082650040340103000b048560a80c5620000d69001910010020052020b1401c0b003206001d2000c041e04c4003842d5203611614011420a100301002da4095512403084a = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 145641097 1250 145639847 145639849
    0x1020c21120d0f091128060c1709130b03010f05040809240403060e0a120309031d49030e06131a090d03021005010f180b0402091c02 58
    0x154080f080301c0701510307141c1301c012404140c0c0241026028107041d10f009010007401c924404880d80c4040b5000340e04008820005001d42d03000800518070b5016442590007140c0c80513070414144154200c0c281d00c005503c2e9070b07100043d001c1e0f01500034002c000740000b0b0704010a030001b20071f850044800799001d41000c288c030400d41c18804c0034150f0b610340301c00700c40140400c1c2d001513002c00d008600000e001e550786c0e000a02c480703010030405d181220760803800c00403403102c00000c014050700c00000100e001030010b5055030514290030782c03450840c20b4010903009076205005000340e400204c44041c41751251141116507140c0c848117401c4d510040380c0f0001101c40b071402d414060001e2100c2d030b40c0d84d4040c42c410083c840340001b042010304151941e0400a5107080310480d065801802004030041c2c4c4011044e07001d8042540000d00400840202c84060103260380c0c501100c05c40d6003851041212092000c0352152141e403d070343c8103101200000304014213280d2000701045421040421040d102a0700c00031880035 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 145642347 1250 145641097 145641101
    0xe0f09010b010507030c150b12060a0635241005010f0203030f040213050108011e18110a0b070b0711031303030c0204090501020a120e070501020c21120d 67
    0x551007080c208075180c151540c0e0300400c004044440601584120a034440e1a5040c41d04413102d10b1000610310200c0e104007a040c80d85503102510328042d000d144c210001207103d02c00d4500403444581101c044585c1100c0c2080f042e030204180c02552082c05252140269401641080c011801c0035584c00007aa18080d43e919440c0039298000c18140048580400350950b030000480b80c0c0070350312078601840c640780c51000c01d1850352980c00024500381000b0020843d164154064101243c1c42d4418880c0c0070000c04104040310000360507925041c001c801d040740414906201c0d09500b050140a4469641c0d0700e200030130f01a040b280084505030307000d0f000d10027141c1e80b00c20300c106d0200c0d1410196260190020400d018a01c403848020300340060b07405654155a40c55210076101c0360031000956903010000c1d0010180c030000324a4000d07807494101c580b045e0712400601304d130030b842c410f800403c0905210000c0002d40c2849403140300000b400f065868169813402c3c0117810082d407442c1c0c55a82c031240304c4220041 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 145643597 1250 145642347 145642361
    0x30a060609050301061208070f201011030d0209010507050a030309021504050a030210052217060f0705030402030a0c060e0a050613031e1b0602010501060f0e0f06040e0f0901 76
    0x103c260704081d0280120a0180340202ca8984d1050740310303030b840503076151101031201d04030000b620341001003104a103101d84035903003480c001d07204131043d03114803071170341d00954058850781350310f2419910038042c180411034164000c0080341c1050401030309042d955a0313428600700001c10202c00103038803010351030214280b03850310005071400340140900340384c108000300381d00602c6c0d844041e21402c607601040340c1d034a016600f1140030618414040e1400d41603803d100588030018401c0d00b21001e035080c0c0504c101c102c0403403824062110300c81440065281d07000b084030680c00150045e40c4c54040d08401100054a11481c0d4006010903101d05586040c401c080000748905a8000e03401201d00300051360035120a0032103841680c0c0d21030401500f00001c0d411b02c0b1107400e030b0118000d11002d13100200f50401d140320407006048401300e500030b101c0d0b6a2104004c0700c04040340c041070700200e920044080790728036090942c858010b802509032410103a032210103c0b458a02a120916240b8111081c04500316003805456 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 145644847 1250 145643597 145643599
    0x1101021209060d06050409050d0f0e030304051203040e04031205070903030e0d1b0807030b130302070b0a02030712050c010f0204050607020910081c03050106170601050717030a06060905 81
    0x2805000d9400505040d01c40d40ca1980d100e00000165840c0d1207a0f2644104041e0401800801503100b10740780c03445d640c400b201d80000229203d004140d0606102e0041840040c5001c0c028506080c50203003071142d2000345522200342e5010a01c4003207000111100348030f201e10300036542c104480c112028044116034014100c5d40030890b49132030500c0443c1d00101d07240f81c00c400075180448101440d0030014401241c2c1500001c8030819010001115080040c2d0741c002e803406950040401c0d00c2c2d00c0c01c000b8010005000080150308170352420812102d2810203420000c0041c01030320314042603a9515103041c48606900b20108402045940c6031a10034464101c503400d480c8421890304d81400006882c5004a1000a100703420000000340424003504081e0020281070341111000c98010f135140b07404001220f0283c000034504000081e00c1881032600a140740e8800074200c42030303147c0500444859100d03181c1610000e00c04520300389807a00180c025032096400450000f0900d00340300f00107105c61202d9101d5 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 145646097 1250 145644847 145644853
    0xa050d080a0801050d170310050432011a03040f02060a1106180606040b011107060f0809010902011202030c070b010e09010c08010506180102070f03230a0b0f090106080a0f110102 78
    0x20310001409521410001d41011b13180341c2d140d5455682040840100c0d4201680203030514500342d05d01050822101c1650000a01e15036601d0303c10464025a68000d2245000e100c0340d410388a6415040c4100954100d8007a02c000018031081c3e80200d4069030002e050380c400201c8420013228017040900ca4103070806183c0340c104d80c4a01124118036910380c2e001d09442d1099650b214021101d82c091a000d012190210007940c0d920340e6100d1001e09003000e0620004080358040001554440043c810603200a9058682214520311141c0e00300003504003c0003840301c3d020400c40400850311580140d8020010549040841e2030f001c4146400d445450640e42c0500803140014081981d42000f615019005000c89052000d04080100d01d080c0d09580524241c05500c0b10100a2100b80154204810790b149048180154840e0b00c00b44d84022561000e00030340c941c003001c00c0d4ac5802120700c46800101c504008078402c2d4031014100c3c24817890003000c480719000080c043c800c1244208240440c0c123424005 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 145647347 1250 145646097 145646119
    0xc030f010801051005090606070c24050a0807030f0b03030c010509010e0c031203040501110406080601031103092e020c1612050a151506020307060b0603060d0609020a050d080a080105 80
    0x310b40d00e80256000341c078030a1b03946100044281d00c860080d141d0245e0001c5181d8166691040d14515150f05000550403005480041450342e60264089401d007655030707034441d40300c0d0b40c1d040d008070000c2524030036510803140c0f5052109600d5804101505000f04014000aa9801d004134140d00312401d03a03241c804941c00500f0441c01c0ca5801240007601c004200e041d460b81c9550b10720f002801040e00902c0354001120200e40410000ea10840c2d55110f000207881c200900001480306566030f020444240b00c036580004e40c041c030140681c8040d89007002c0d800c1c500c024500d4466143c1c0342139800941301b00d42c4961140c03a070500c9110344010440010280d0780000c40c24040c0984a96484e041d000301e015120006410445940941a510541c107150140381f801d419252101c40013500c0354417400c41a1040c0c1e0410380040c015103003071402c50f40600d50050264084014658502015249030501640e0001e1000c0c4001100c0d00c42d4102c0c0c0c4a6180700705561981c66401c20009000043c060b001a800b0301c40c1380d07407 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 145648597 1250 145647347 145647361
    0xb06180c070201051b010603121103120105040903030b0306190b1f05070807021e0310060503060a0b01020106350c0f010507020d020a0e070f020109050c100c06050c030f01080105 78
    0xc40703003880c1d020f1804a0f90703a10020302040c0d40740240308501509601c4c1410001c14440007000030480703240140e03189590341c5210075441c0e640b4010030b41401c46080109004024074501544080c4403d4400e04000c1090144a00000d083c040c0444114030042e11020442c0c40b201d8440c8640003011000721410501186596000c01d204404d04010310700788079001a815043c40b004a01703542089500600700058841c42c1d019440d4140b9256500500a10812040240c28480e0b80180307002d84002800528143e0b403031481e008080d2001074600c9042d55603d16012a40501640780300610200e450100810901c20344003040d001c00024030200001d8200d023a00841994070100e06080c580824070340161211114000103980328001e80b4001d41c0704000d4103000881031082e9070501d1084600c0c2d01c880c0d1100780304103070a90a0310420303000141190030800e06a01e80b480c0c85642000d1302e074420b2500f5a820111035458034115036056030524400c400100411143d02e4041070710a014001c610021f00082c18400 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 145649847 1250 145648597 145648621
    0x308010f1a070305030402011110020901030b04020c0a030f09260f030a02060705030415050403020607021608100c0504170f070f03030818030904091a070503010f03080c0307020d0b0618 81
    0x114000c0404c88000042010b6a00c02c3c0c9940c44d42440d140b0940d01061409030482c0029448a0300c400e011034200f0440115a18103442030365901410b03140680502d002690b41106c0e0415440290001e01c501c080e4041412200c3c82140c08180e481c1007221045c01c20f58211346032401645250140a9900c1000307090211130b80132400e076800044030704180d0780f00d4482c0c5ca000c4411085414013200310903d0441000107040d400200c060140c3e902c3d8085d04d0154290110034603021031640070b250f0071903100e12080c404232022a4480d01c025003d500c0e000b81031030703211040301004000d50440e440c4180e1080111030114442030204500a11001d140c100009185a401820002005010f00d904102d50488010807100a00855031200c00040080110440d10300e0000c5510700d110820403c4003940a00241410b070180c401c40381a0782050480b0a495842c60380c50b04200c1c0d1002c2c1c4038584070f0100b40150310040c0c55241440102501c1203c604140b45001c005200a148110040461000c1190b05202d41c0180c04 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 145651097 1250 145649847 145649857
    0x1080c03010e100c1202070323090d150b03060115140a0f0c0f0209100e0109020a170723030403030f050103030509040b030c0613050a120b0f13060501030308010f1a 72
    0x8010040f1341c4288101096841001841400e01d540740005450000c1540c0804c21424400081d8810b0035403000501400807240035450060341c102d086410b0030030108281242c1c084c1c0b0440e2403a00400c0301a1071502003424900b080c0d04c246000345a100a0400c06604140b4000c0c0502291050310b00303021a0600060011030300614030018411003e40113020700120505003854250040d021800604000c0403a2949030024814a1100c40184002290144c05802160385040d41540d445c00c1541c01180214540c110180145046c0613540c180450388a0181c40c0c4414151802c10400b40c89143c6808c02a0903900b540c003014644034600001400080d41100030345549400c01d80d0b001460b0030081c0080303464600981c14aa51203980850f507032402e41d0003a5082019581d05507a000784456503640300d002c000307111030402800c400707a01d0006015071813020700c03040d4460b0600030a1004006c460300c420040310002c1c0c00680015102500621403000d021030400c0041412903503000101c0701351446d01643c1d000d0 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 145652347 1250 145651097 145651123
    0xc060106080c1902030301061107030506042a06052a060c03190203090705010e0102060f130606050409050d02211c11041d010b04050d03032a020601080c03010e 70
    0x20040420000000a41070b40d8a0068042607181c980b00c410f080a503494000344902c400090a03001542c00c0144c000c81c006003181d03440710080003207440b035544600c400303c2c1c0c1c007000300680346002800351a10241c9a08070310041249403603455950a540020401441d00385450040300c0a048000c051780d1a07000400b15401062280710b40c0c0c49480d45994400050701c400e01000645001005000c0090000702c1c4160481b4000d880780d00140040c0c40042e0b0700c6407421654000400700c103d00003104041c1c4031171581c2c0100d10600002940c140c55900160031a0707005c9809450950010f0750401e032098040290711914204075140030115900540080342610070040c03138110100341d0702c940903c2c0415a41160741c80c071000150490b21682c0710070003c040e00400180d09803842d140ea1000003100003a1004441c00e41c1c4000d01101d1440c92203403801d40241040141400c2c481c10f81d0f188010700c00c803902c50081003040c0f01d5405024254503104d0f0891402c1c00c0c015005200743d161401c012440c180008503894035840c = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 145653597 1250 145652347 145652357
    0xb0f010e10020102160c08010501090c140f0f0a0e0a06030204080a0602071e140c0d08040504020702131b11030909070f0c0501050a06181e090602070501021b060c0c060106 75
    0x1030004a002e400794081c440310308403660170b0342d40800c481c1e0825081660b10001c001c01c0582c0c8c1e80e010042c25107800d01200c83c00300d00100002d00e42c0c0d00039003001b40000c01030b0780312892600c4250f414020759075101a4034807000070b501d007141c8030051400310710a20041c0344901d401d600f4142484031b030300e4035401c0382c08004102c654000744a0080040d10031059007581c50380e80142c210140c150400c000a40000d00d410ba06034002c100c0d81d00c0092a041185144050b0400142414141400d0070b20000398413085040e03138012505640b02c401c5030f185028504502e00208081581c840009001500c0304001180040c0030380c00c1070040d0034407504c511211a41c4020b861400d140c130310700c101c2001d4682c082d4610024040e54200300030044000040d030000c50032545464020500840742040c440e0440340707040304240010b0810940c0303c00511458010b5481c050051800621300180703a1356450890344040640c09004126502000740c9845c14001d20303521081b02c2e009645410301480071941c03140310501071901444 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 145654847 1250 145653597 145653619
    0x40b06011b060219170702030d051503011a030106142b050303070504030209010b0a090905370c0c0f0209041403070f021201022104030e0a030809040b0f010e 69
    0x421071610965094100320119035849481141c0d0f140407000c81c0b0042c0c046180b000d10131004240000c080e41c444c03070503036028501b0414401c0105004d4200a0070789401001c3d1000e9100540d5020301c56958242d2500110040400c0c03100c0901d8203680e81c43e4003045d40e885107039090390348a480315061000410134180070482d010045102c0e4080401103081f000d0031521001c010840c1c041d40003002001a60700840c1c40814581e030b210790890542c85100011300029030f003042c0400c0449400d40140741c12203075440c07030200c244400c2040d2140c07015003070941400000c104400f04d1421401481880e48070071182c500740c04910f05030744809040d0504010028010140b0f0340008083c4000c880c128003030074444c80162a500d040c4c50030f20810180b203451081e4451650000c04c240d251005108480d0f07400b50209004039211095200700d0340c040e80c010b1080e001e20070064045000c039651010b842001d0f40c81150056140c1c3c8414090001f101c03081b2261a0244107080e840c501c280c1e8200700c05c40524541220408601c07 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 145656097 1250 145654847 145654877
    0xc020106031203150e0103080702010815060c100f050103030c1104060b1c06090c020705220203090304080d033602060c0c03010b0603070c020114041a030103030314040b0601 76
    0x149081c0e4406088007003180040c48580381d042d042002c44052400441504548071242ea1854400c28400240140c10800c10000194001d1b241c6036444258031445200320591280440e0581c2c1c0205103040d400d8103e440d10752030b00c01040c0300c0c000798120f0901c020012581142d8010344407842d05d4201800c04450000009440d03500c980001c0050004840c0302038959210034250040c140780c4218032110141420404501c150242c441c8012210031640280042460403040c40043c60352190001c800a01d00200d011048051340001d48c0108405001503580300e24003041d20b400d0076000d084c030104140c1021000310700341400604954035030100e602a01085078400c3c3e082d8485a600b03510094100d107000c1022098481c021600d0019840154000e010342d040c02c0e42006100d10007202d044012403075450502026510903118040c2400b50a41c0310780c81d064a4401200030a0694455114150302c00030050080545c94002c8a080703c4200b2804192814030350f9174100180790082941e410001c074040d200c050303 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 145657347 1250 145656097 145656101
    0x5130809150c0304060e1c0c1503021b030721200a140c04060515040605030601021006030606030215270d020a081e030a05041a0d0c0207170c03060a0c0201 68
    0xb41d4005001200d6a49a41c0d1101500041040107114840d007140008101d4201d055510f14071515405400e100310b681c203040d00692060448400b1108140e42400080c084442d02c4459a18a010340d0005648944e451301c0e100206108a403881503100c07020b1541c0f580c5079604082901c2c0761001c0d003001c083c0000c0c15040128500f1aa906000d4003000d140b21245141c908042611018918161414401d0f01d4654041c081d5024444105e035080c22401c00003008000d1150b400b940d0014814410350300d10344d103600202c0055583c540c0003540d88030f50303500c01041140b50020228684d22103c90f416070614402070700342c401c50052805407805400041c5060002503407021030702e211127940184112030b4613403140030030359544c0c180100e05030004c11803880344218604004150303603403011265940d0345082e041009240820000e06102403060005002c4142808a01d004202200040b40d0003090860b18220610160950f11081e40c18180c0144031540001d440104860340e0055000d900400c0c9054030380000c0740 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 145658597 1250 145657347 145657357
    0x12040609032a060506060903030706020903070f08060108071202090f090708030c070e010602151f030c0909030806060a0903170408151905071b0501111c0513080915 72
    0x2102d114024110308803860501441c507140107460030843c6542c0e01c1c081c07111a101c0c6280d02981a8010300004002901c690000c0804060150923214250783d6054032901c280825040b0081c99000100140414001040070744018180c140701100d1801954012400503000a03180c41800c10031480065044101005558000e24118003200c0c2c0d1480e0a00c0301588031991401010710040c00540001180b0b440080c072403c0d020f50050090400b900e030b142c03045081c1d0320001d68400c01510700c02c20000128503000f41c0308004210307002010841c203100d80341c000c000c0a4014401c40c81200c003404502c40042e4000e20342c80550707034441e041110b00d51200602205a004582c070140f00c520600c00e01d6007080c9902c4a01d14043c1215103d207440c4040a03992510035510219400c43c0040da50640000203041040491101d41c3c1c0986c000250f102009403425203e035005030309071000c1c03c0d0030007001c820f08000b5100b4a680000015075680100c2e03140c1d900c0c124144103807084e141c070a480f2030017100107800d1000100c071 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 145659847 1250 145658597 145658627
    0x3030509011505040b0a03050d02010b01080906010518090106032f011e050903030f070606210809011b020a0303030506011d06040b07080408010516032306040f02040302030a0b0610051204060903 85
    0x1e0400b1809c108000d028000aa418500240f11140490040800014514183d68004004100c4910b940080c0b0482920060800d48950340b42d03100000480c4041301d1012441c400e141c0c1d44141b164120f410a800c1d03807a02001c4c42d0400c00c00c86800411101e00ca5040c942807039162070910b6440d480701d40080c1c51400340f0545003801000010f108030030400c071603000c5c80888100105440c903030b0041c0841e0341e20142000700094000c42040020071201d41c4036103484c58000d864050308544000c1d403070300405c28450f2190012800310703603120284640d9607000710b024642c00102044d0100c41080c0a008114140254429404066000f2848d10700f04940c4000307850280114000803c075501d01554203a810344180f404940202e440c0002e480d5100640000044010b040000381c6211a1104000e000007000c00d0344150360940d5090201100694041c046070440c01d000d01d1051082e82004002c00501d1181d130354090003880801c012503051041c80b0f07246168025048100002c80102034101581c8081d0140120 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 145661097 1250 145659847 145659853
    0x40f0c08070e0106111e03040e13050624010f11060711010608031602040f0b060703021506060702090f06040f0c0309050706030e07030f020315071d09011409091c0c03030509011505040b0a0305 84
    0x51031294164141100c92f00800c100c4490b07449100c080900c90401e62154800e404024441620550190411800021251078403070340007a10b5030794440c2004030595031000014001c914041802000f4000e04014214800155190003441c1591704041c5107a02c000034096500c0c1c80d88901d607420558480c030310f03507140034114540c2c1e01141e00d0003d4036207609024000f903075008040424901e0800009903071441c1d07801f0b0504540f9480b481101081c501c030003071149922580307a60085000075001d01441440800341c0c0c07070124070300f0002e290040c01e01602d03401400c10035240003544c0e10003400016030300c0c085a4100361039680420490005c0703070502601c81c0e46035124400c080b00b449101e80d400544040c1c122940c800285801c2180320801022800a114040d50045412501c01da82e24001300d440d60040c03007103800c44081c514007400c00c05184848124940100e01c10486850501d605401a075910403903440c02002104041c21003800c000e08980100d500803030f610002d004560315030541140c00755401c8422 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 145662347 1250 145661097 145661101
    0x9141305130c0602030a14070f14010e010e071a030f1303091a070605060306010602061b0417150c030105030615060d050c0d060602010b0904060203040f0c08070e0106111e03040e 78
    0x380d500e9215000103c00103550003031000120001d40150384107254081c512081241052b2580f411125407030b61408210355031921083d10480c4240300300d2502c6d101c9080504015894416000310a000380d10149085840803c10003034200282071000e903020291600c0f541211900b82400c0740e85215580100001302103080d03000007901111406231001505ca081d06000c83d9984005141d00d98a00384144030142c0d00c0540030408201120a0420710f441c0b03000303251800c156a03102c1c0036817071f00510b025415260700109030796041c114640d04180d0f80032105203070312817070341d4901000700780d8a060080240c0c1c041000180d10041640e960030459201444c00803041c002c42c241503225145960225843c88107141c42c0c510300241d42801030094a28010000703102c05016621a00e03a880603600040c4103c0750b8030a41042200018003a01d0090b0203001141d004040d440e080a000001c1e00d401a000032060180c40301c6010300507080010b603e000c4141c585214040e5422400a00b49103020b40c3e00000031007298141 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 145663597 1250 145662347 145662359
    0xc04030b0405060a1803090308030601140301090603021002070609050108060105041d0a0b01030b01020309040b0a030503030403030c03140603060601200304140301060e0112080a0e040c020307020109141305130c 92
    0x2c3d11402410881c004003c0000740940d8603600644142000300400e142000400c08a100c2c400034651002042c113210b41c0c02244400408545d030700981018512641d6004e0500079420481403110303040707030680000d003810340c01c1400c054165182445010304012075540080d0b03140e40300b041960024080401702e03828103003650329403003104042100c030b6000d468a0101030310b800c0d620a0190014040d01a0059071410b10800c0510014061544515401ca28400301c00000290104015841107019070780000b07031900341d03090081c16900c4951b41c020b101c0d06090140025a900440d62a404c440309007460381400c482282d0b00c0c0105d1184d00c2030016240000700e8006403950090220f191102170840080004c1a1503c1107019058802c1c001c0304025854407102d800000c031504020849503a90307040c118065049200080c00351079035000c0920040c1c0020456004558110801c00050042c1c030302c0c0135402107020300100e00e01003821f002140c40745480d600441c0c03c404001c50507120940d001000700786181c0c0c03180 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 145664847 1250 145663597 145663603
    0x9060f0d090210020f101b08060303092706041b0509030708010c05070c0807060816050d09030c02040b04050601121505030a050609100603120c0302101a0f030c06030703050c04030b0405 81
    0x900c26040e0291007040c46c0444294498081e00c41c1000000e01d52003003c4100c1119942d40c01040390f0f41501c0304000d40c0529a07286441c141e48442c81d006c2d05001e165007181c08005106001d01010700803070030105d0412186609103e01c10790154641361050b00e462849000034030b00802c035840550709502e00340c0603840065101008280b52800341e03c01c401d01c950303203070700c000da43d0651840b40f640051142c01c04241e580d44491900030303140009203030160810710072003d82d06c01ca4025050403008580703e1428a004c5007070500031080d440c50100c404104614121002900c01302c8a4600d0f048081e66071120f62003840c28042c6050301130280030702110308001251504035680e02e001d452984e103a00c640000216030580038018681500e40c801031500310030700c41c00400d9801d405c000e0012000c0d801100c01c004200c1480e841490180f0103815032541603182c00c80305021465036040e9903a4001d401a94412055071a0103007240d400802c40d203000506a40c544d083d8045900540d04002c0140c03241e0014002480300c00 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 145666097 1250 145664847 145664863
    0x418060516021b09130615060f03021903020c030d02120a0b0a0609030210050c060a060e0901020a08060d0609150605010f080f0f070504170304150509060f0d09021002 73
    0x801480001c50030004020303640c4a51500481c403004600040d40c940604000d204541c005030494403485603000a07a4440050f1174001441205a5800d03010400c071180e40100c4000285200d401c0840c5810000d6a021070181c45030740e404418540c000032005800001001240e505040c1128219110340541c1440c85504000380c41d41000d480c205840b0327640c0c0d0f203010550303441240d82c0d0392190b10340c56195909005812040810f05814480140b1000b00d0400e02844002c1c483c0f50140f000082940c14001524035898000d411004568818060403005641100301641c0009003110000c1020700c5504d40f4070050001030800030900044891000400c40b101e4210106aa009803515a403080000d50304482c40a8101c6090001082440104224500c041b950680011407464401c2c40c10382c90341544840e01e8001c2d000082c2d15840045c041001c4112000c1c402e21116541c60a9880d00d051a000178004d4000d284285500c0c00002179841450401644001903103580035260424003052503202070740350610 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 145667347 1250 145666097 145666111
    0x18190e01170105060102150c0706050711100b0303090411040803040e090f0a02010509011b022809020c0c060309011e0507020607111c1403010312090609030302030909040204180605 79
    0x1c0c1110111848418040e1921558069004017070403042004003400000c401f0701104c00444080081c0b070701180060040e103204d6003d0b41c4800942c6a00807007250b00c0c00501c00c015602691415117922196035020085458052084802203007684101c014180c0303601c40c540c00103010703200c0018001241c0051281c114418500102035801031000002130325250341c64440003d00190003044081015805100784001c2244000340032413050300c190b40801d128900d0700044080c00710844840c042c034081e5440448001d4a00c3d0b11080d41404034007143e255488602d400200d01c580c0c0e002c8001402442d00f540040c815405c5c0043e50340c0703502c05012418004000c103480650040c0141c03c0061101e900540351000340030500001007940c034000421f42d102d8052070902020400101c41820000f10394200c000d54061401113414100c0e001c0060006001840564400340038008603400800100f500401600c00c04841076440c0a019501c5100203001001045000040d03400035952600c20b21482c3e40c0000c0c07288075 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 145668597 1250 145667347 145667369
    0x806070906110c030a06020309010b090403180501110d141303080a120504030c08180d05010614090f01150c080a110106050f0607060f29031e0318190e01 67
    0xc20560180d032200104145184c00d03600c10b10031400061040c0d8011540188100000100f0742e40c042d001525606041d1000d5001031190550041c00607001628130380145000d080040c00b0080900c201521160441000b106104036400983d03000c080c07001c100c0704420555080310b03044a0300c9241c820401c2d0840003802c000a40601102d1422685600c107403401690941c803105949009941c49400c243e015800e04c0940041c0042007406545907071584c00c40300352145002045217402c0880d00c401c0b42c034008004501c6041c411080c0107500000c008030038156400c0c1031003039115100005003079a10b9000703034030001e200c0d101c002600350445034000088018080d0719070007032000030740c1d4070200728500d0001c203011a0300c51000c02c03080000443e02d50000c101205200740126903044c1860845041e60700940d4038800900303c02d0110300032460300307221503c0c441c0800a25842241c404030943d550780d0103020341c0354414441100d0f030740285030fa41c0091082601c443c18200300c68591140c040181000c000e11802d81030311 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 145669847 1250 145668597 145668617
    0x506130b0f0609040f08040f120213020403021302070611040605030a0506040219050904061208070b0906040f0303181403040806060604030525030b040b041a04110d020105040806070906 81
    0x410715200c0706015441c0103240384410f855a499040d1403003441710701180c019800700400142d080c50392400b08014582d44101d201e2545031401800f103101c0490b18110320b281c1c130411081c40103955282020300e140325130120068039144a498500001c24580c01200c6118034049400949c42d5031107002503100c1c40307048c0810704c840c0e11020144401c1c1e010b00c1800d0746003012041c5030004124450405003540000082c00401c40c140d6422001001002082e0140c9072001c0010b1000d0500c80f0310b000007900301d81481c006010314035181c0c485c1c2c03858021140e001801c2581758503015400e6403e40e0b4042300c1d040c3e0401c0b0024000900742c0345055036540300740304040744d902411000580914061081c2d82c2126080b01c050701340615141210740d040f0302c0030f07202c04480010224002c40840c3d00d11044600ca41d11070881180641403500740741c2807510016824000e0099200300b00310000e00e10822000c1d2850b801d4610810444c03a80c1700690710b600075604213861603c600c00800482503840301008084075000e4540c04406 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 145671097 1250 145669847 145669861
    0xd0e0d080f06040e1603030306030b0f24040b120601090b01050c0304090209010c0525050d0f1101050f16020a050907051e0405040207030906110123090a0506130b 71
    0x151000c440c922105801c1500060680c103054100c00714034500e290a46000e12a450000520b01019400035400650703200801c0c030811880c8001d2300d400c42d2041d00d10005902c0c003103103c80c212040f214400e859060a40c1eaa070b00d61502c598000c80074cc235074004c0c400c0310a032030910016a60b0300e10074031403951524100f10031440305500800840303140c00c045c6000b84d4900350410007440040d40c04a0f09180c1045403100745500030a200f8405c0c6c10b000c0c0003003100000020346040b40000001200d411061089280810801c00200c2c903400c0801c0e1541d0115910070314a4510300181c825019064401c1c00d007803000140c600311281451010010036208844008256480344203110403080100d8525000c00c1013084201d0a01a0800240000d900240030062a207902c403000f1034184d80140c80c0803400710748071140501c2426000074414066400c200003c00000c0c1251041c24142c4003110740140507044107002242402a00303010811046400c542203543c07a05000c81d42a200240f07000042d2007526015004c510303a = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 145672347 1250 145671097 145671107
    0x3041e02060a0c0209100308070b06030a0506070f0806040c020a060c0e0604030b041709130504020312041706010503010c0c0b0c041508041101050414060d15090b0301060906030305040e09070b0d0e0d 87
    0x4c0c7c9402030342e2941007007400d80c2ca010151030f010300340c40c0d4144948603401000940820129115481903940d280c500d854130701015109000c0649414403590138605180f01003540050358410541d041040032036420080c0e0015100000a0400c2c0c0e50003960006001c401d10400e882090700843c4247c0740ba079858071000080c4d058501a003ca0b480c0e004240100c111268542c6030031141c1c1050004080d10420294119030003010f034080e900ca0844489140d544200c10a001e2180d04d0062000760000c0c004852001002031103140071070001880c816401011a01500880050702c000d440080ca80d45e290051044002d4410308044904075045014000880d0882d441003040ea01110f04607103252120201c80400c1104a8106103042a00c040d81d4140b01a1402d400800704001000170060000c0c00c2d08508040c1402d45281d40c111a40391303030801c001000020b6000040341c0480f030300454042c1058a404105a003055059401401103602c041812104511715030700c040700b1070310640300711511078000803c1610 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 145673597 1250 145672347 145672349
    0x1503070f060516060609090b0610230d150f18110307030203091005160908120f09011b0501020a0905190506130504060806041406090303041e02060a0c020910 69
    0x1450a22a1076a018241010256550304c903050100d4515140ca10140483d40c0408082c1d41101061080c000c960912006070310710584645000c18103080100400e0483c4901407900d1144c080d00000c2d2070102c00b5250780b010001403a0340036010004d947e81d04111506c1080e60040084804118103000b03010400c0344034007501e02465000841c216a90908160025007000f400b10605000740184581842d04a10659100d400c1d10000c00d40c3c0c082d50403400078000130442d0440d54041c0c1c44902d40c1e0701028403c03426210402c085e40308456076400c10700c004942c0038012032094251090b440c285c0700100001900600761030714240e9140030b25965034070100903013030580d0344105d004120300714001d1000d418910000c04428102d0310300340400d65034a00c0401c1c1125000d0388412120b400c01c809001c104040c48042c5180e100405005000b9400c042d2080350f228030010f44001c00c00e805000410400c0310480501e00002900200955100c0e00c01c2e50001c0e203001502c00d4124442c0e1500380000d1219840009540 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 145674847 1250 145673597 145673609
    0x8010204031a1006030902061b0d030605010f020303152829070f06060f0308071101030905070e07210e2b120e0a1a011a070b07090803031503070f 64
    0x22600f1441c000c0c0035001007807440f20603a0001420410191210000c00341c0348070000343c0310010186207010307803801400c4680d944c1100b810040d408502160300e503800400e80c0d41200c0745110301d074500c400710030000d1807542c140a801e22040d100500000040030841c050101102c1c4920480082e1441d40001e01c00c840e401c5400d1100c446109000010120f484041c100074000e20500f000900340b926820524a0180c1d6603004941c040800214501048400700c0002c580c600282003e10032010240c0e41d185d110005401804104169600015021403107203003407034442c00c4258051a001903a5000c400007829a04403240650301c50180318541300e1208074030359180941c01c0740c2040c0d2009107600707045500f4240311001484072600d5070594110542d00b817042115084c40780700c8100c0c00c01c0c40030035018404030050b4880e1852200c00c1683c100403225100844030b4080d4001890130142d500d040d81526901a150440f10040c0f1002c000c010784500c1d00c1580d2034035900c044045400b40c0c0c1c0c0e907000500c02c03600b10380111 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 145676097 1250 145674847 145674871
    0xe060403020907081302060f090112200c010b0910051206011a0a05121303140c070302090901091208010801060801020c030d0e0f01090b1b03060907120b090108010204031a 75
    0x3207140b40301d400a42c0d0010f100740300d5041c0301045d540008019411041e60380c0c0707844c60000303400d190079a0801102a011100c84105005440d6a8112503280c224411110010201c1c0020001031006003940899080400113100c100b060400700914001c003d114050b5a02507901e00000001c81900001c5070f40c102c400c504000d06c1000c1d200c007080c0060b5044030f03018030180706040c0034000d00148940c078042d101e0710105052200303100e1603003001011080c41004e0b1a00c1c421080081200142c4045a202c0650345c042e60080b41030b894010b2a0384c01085251f40181000360000720402c0040d41c00301c44c42d81202d0001c0700920000d91280119802c078030407004a440309600401a271554282a600a880880c0085050b151400c0d0341c45012801e6804050080322090010400c110901c498102c00c40303075100910610703608520b0708602080c1c9515004c9c011006000b03c014081c0483e411980103200305000141607520a075035200540c6010b50011f01040b44c842281d03810030445101c480e4034043c454503490b009 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 145677347 1250 145676097 145676101
    0xb19080603060a0b0f0301050103050616050a0e061b0102030a0518010c080f0408040e180d03091214040801060803120f0408030406151a0d0e010501271d0d0e0604030209 74
    0x61801401903c84d036a80010032407003001c2c034681d020310a03203000b14091700241c08903160603020382d00070980d042034400c1840414000e81201c0da51000004042c0031054600744d03600c40c00d25100d48401c085c9a0105206503000004001416001d900318074000c00b98040d0040310040968030840c02d0303484800300030000032074140000e58104101c1c05400c0d005070048040070300d002c4c0c44401c0350003071410884440101c0c000101c01a80d1805040125181c015a50724040200a580e036856501c0702040e40c00410400c14680034080030030b070000c0121402090b03d2002008007694400b9200c0d1250081030107003000380c05080000724100e5005015a00c46c50780714076050302e141c0e134075904c13400246002001d21817401038806010404409030340c142240004c034003030000e44441c820f54000064030920303819000d281c2d042400400001544007402c500268400c448299070407042c5000600904d6224400d103024480703584901d00000002c034401480054556580000c41446014028988500e02c0002c0d0000b2400f00 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 145678597 1250 145677347 145677361
    0x60b13060e450f13080909060a0b0c0c090603010203072c0d030e03011d0c0409020d0807080405030609070302031b03150106030c0e0307050d03111005010b1908060306 73
    0x1030740d505100e0140d820010104220030000603828806038103040441c00c07480500c043c070a02e4502c52540500c80004035480092a6500c840d001e0050304050360180240e0000300b007982c1d40740000c95003e4103491352041d8480070540802651a00007512841c090542900800c0b40c07400c0600880344114015104d00c440c0c20300740103402d070000d9600005076921603034440044555640342031084003100e020b56079402d28942068101401c444801044003581c40710a115071b031100e1808141d051280108a070300050720201d500100c0c000c0c00c5180d900409600f4001400d40070030840c1d4002c1d000b654003e17400c41d080d40d61030f140d0322031b942c050300e01000c3d50550203e84124aa600c003041403000150020f400e07035074075800350866140142e0080e00980046a00c55107005400303980306940c1d02c06107008400510b441c0e8030700b5002c0742c000b40c841000034040007681480b03600030400803c40c104603c652083c00700925a50307030b01109101d400609256100040030000d482d842031148200718092070307004021b040e05403900741e = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 145679847 1250 145678597 145678639
    0x91201020306042009010c0212030a0306031a0609150301060b030f0405010e030304050a02090406110a1d0a240203040806070903051506060d0b0307081f0c05070c0e060105040504060b13060e 83
    0x40b90489e4080310858000900c0e210600181403600342175100410f06e07508601c2c0c06000d0654644400e501e030980c00040180e00e64940b42c1c915044103281c2e448460a084403030103c0e015044c03a030000005240000301b40014602c170f02d21590700c81c90041008000300040300c1c5005444e4801510060040d502040410001d85131403015035401c14440d00300001e00b111000d5900b074454010f5082d030f4010031020b8582c000660b058070f1000001d031004561540701603046ca03812203540140c0381c0300c042c008940c0283c1c4810090023001118007410003030f0100c2d102890280e8000b0b24051160100300c40078000e511081e9402c684404900b401942c2c0208aa402d0103000e02207100140310340117046a040c0b10b25140000c1c411424480103190712080320240080c0d201c3c000d002d00a4990202410b000c0180420020021a0b441000341c1c040c2c601d45a101c03212034680d14012526030069030000703940989010380000d40c200c1600000d0482c003036080b2042c580a070351140f05880880d0501295a040681c868040705109809 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 145681097 1250 145679847 145679867
    0xc03010e09012706050c040b0d0905010b040e100606020c09061002150a1d0a0506130c031b090e0628020f12060111190605070509120102030604200901 66
    0x200d80001680002000080603038034003284228503502507103683c0014455903004240e170145403540d0f0345241ca071621500090900c03811054001a9980307003900402c002c0290410b86e0201c000510600406441e03110007521098944281661540352a80010f6414001314518003400c0b001000303268161303100c0c814045082100da818101b1070040092440948545a441901420310044009614000c1900e01010960703401d1080049600ca1003150000910000d00b040d4001c4640c058090201c40902d041001011284c0000b000a000a01c0444013903d245060404403107111006020710103540741d20b591140011b58083d2540da00300c8500c44a9001c00880c00f00810280c0c090040c642841c0c0c440b00305070341d00284504501da42159040c0942903034000041c1c15a409020054626890f6502e84c0512105047c0d200034041a1100002a0a1070240040c0c1da406000503180500c03020000d03480ca4000c0d44110b83c3e45224605c1e001200180041200b2501d4400003402c40261421548800640e000080 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 145682347 1250 145681097 145681111
    0x504081006080a0b1f060906031104080703020411071a060109051807030e160306020c0607020d0503010312091e03051204050a17010b120606090a021602012102070b0610080c03010e 79
    0x584101c404115540c140c00d10081c480e0355078084101d23040c003000030103451300c00ba1400400d60007071000380113100c3c000c40c203c0d040380e50445c1d000418414010304031060740100b00c07000e13182e807240e003000b49151a05034040d24400d010903a29280116111000c110082d1441c0810700858103c2da4002480c1500036441a081002c035101102e044098902c2d06442d0402c8680080303034256004a0400309201040103103907002811400a440c500400d040010031a002c144000380c0041d01c1c0d882e40b007003040c0c05824aa0b002e00079684003003040210614071070040c4642d44c0320859240c826809142601d1f0120300a54080c0c1e24000c105502041c5031a80350710200c0c00e845400c80c03165507a0740190b80e9555841c0d40ca140b1008550b0080c007014900f071002c104184200402640003a4010000320f10b03074000d00d103134010780d0b030340c2c2420040b4481500300032102ca10b00c001e8010109480c400a04842403007480c0070b01a220f000c0c100c030694100410180c4c00c0340d002d00e041d034101c00014001e100500c1050061080c40d548011 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 145683453 1106 145682347 145682371
    0x3010b03071b060609021207030c1d04060503060907030b0709030c05100e060324150301060804110a090c023a031b0504081006080a0b 59
    0x840100000208030759007154650140b02c103000140d942d40c0100c41005620784403c9018020362000034559a0007540c0070019151034441d000360340c0c1c8a001903480108070103a00e45101a030300482d888855200741c8070300000c00d1980342000418030034048000100fa480307145040491080a021b000d440800803aa44e041c400700d00641d400404490007030743d201c1e0b58480b4035801210303103120240c20244d018000205003e951903085000103584924a005086211070113410003546038801040f00c0e0b2119018001044501d003c0d00b0015803150245a8503080b5041580005a2040054014a100703a660326442d080c1c50743e040042a18144840114070845a2603604503501c0c4009131f0341c060f0403484440300140c0d4003846a00404006030b032032104460448000700c030281064001d40550f0b5281d00c5103000000c40c0078881d0080700d00700c0e6440c1000d440a050301c2c1d250000304010041511201c0c1d0 = true := by decide +kernel

theorem cover : BRFrame.Cov 145503597 145683453 := by
  have h0 := BRFrame.cov_init 145503597
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145503597 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145503597 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145503597 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145503597 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145503597 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145503597 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145503597 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145503597 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145503597 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145503597 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145503597 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145503597 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145503597 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145503597 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145503597 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145503597 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145503597 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145503597 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145503597 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145503597 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145503597 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145503597 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145503597 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145503597 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145503597 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145503597 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145503597 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145503597 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145503597 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145503597 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145503597 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145503597 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145503597 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145503597 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145503597 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145503597 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145503597 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145503597 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145503597 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145503597 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145503597 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145503597 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145503597 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145503597 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145503597 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145503597 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145503597 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145503597 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145503597 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145503597 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145503597 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145503597 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145503597 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145503597 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145503597 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145503597 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145503597 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145503597 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145503597 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145503597 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145503597 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145503597 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145503597 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145503597 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145503597 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145503597 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145503597 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145503597 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145503597 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145503597 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145503597 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145503597 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145503597 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145503597 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145503597 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145503597 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145503597 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145503597 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145503597 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145503597 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145503597 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145503597 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145503597 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145503597 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145503597 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145503597 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145503597 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145503597 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145503597 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145503597 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145503597 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145503597 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145503597 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145503597 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145503597 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145503597 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145503597 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145503597 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145503597 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145503597 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145503597 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145503597 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145503597 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145503597 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145503597 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145503597 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145503597 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145503597 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145503597 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145503597 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145503597 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145503597 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145503597 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145503597 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145503597 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145503597 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145503597 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145503597 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145503597 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145503597 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145503597 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145503597 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145503597 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145503597 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145503597 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145503597 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145503597 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145503597 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145503597 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145503597 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145503597 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145503597 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145503597 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145503597 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145503597 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145503597 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145503597 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145503597 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145503597 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145503597 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145503597 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145503597 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145503597 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145503597 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 145503597 ≤ n) (h2 : n < 145683453) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
