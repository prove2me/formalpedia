-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3439
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T09:40:05.779782+00:00
-- url     : https://prove2.me/submissions/7b62afe4-edd5-47bb-b1f9-c0eb4568b909

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 618345323 ≤ n < 618525179 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 618346573 1250 618345323 618345353
    0x50f180705090a0603050603010e16031515060201050739050f0105090a0312050613020d0605040216030201050a0221180a080c0c420a11060703090f 65
    0x5006192802d42400544046682d410540c040390707490003444428207007407188070440d0070340c1c03401403c10700004142504640d00602c0014031543d5110600d41e480403079504002545070f810aa10080d282d00c80c000a8042d003001c540c11400100144c050900da01d040510f0b0a040c81100c4488050302000f002c0c1c070701300d607070203c01b0709941520494040d04400d501c2442110f115804000c0507080c0d6410710300e00144040740f51101018114100000d000341070703a03901d09030302d0401005040180e4500018081a0203030590354400c3e0380c00703440492002c200340c105448c6403a013144aa0300810980d81c44104250490041d680710301000b281100a21070080350786800d0541000b92810001d4000f01c44114043c07404250000032079a099007c1780525245900308000401c01c0d404846011008101d81036003040407a02d02c000b4240c1c21010301650303448100c2d400b088442007440c400d100c0d0340c0c1d03078005401a1500c05541c1185826100316000101c001e8803901c10751403076903403081401802d050141c41f0400e031a1a00c1d2 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 618347823 1250 618346573 618346577
    0xa14160f1b120c140102040602031c090f12090602010212070f09152c03120a03060b04081605030a0f03030b0f091302090108030a02071a040e04050106050307050f1807 73
    0x51400c001155a5061001c103002e45680c0354480303007826150110442400c0f00d4036400580c0141f00511100c0d40200035a481031441c6011410040304140005002e0082014040e044124110700041882201c041d4404020b015031648070340b059070388500300c1c00c0b0300c6690701e000000c8610102013000340e0f01c036072035803040c08015181000080c1e889580350300040e100c00307901002066040c00c0b0318418004d03015500c08044903070040d0b8440c0100321000b00386c4801e0241c107182c5004800142080441c0d000303a0000f80a041c1c0c40345000e032900e4a4101c043ea1394003c080000d19100d400c82c2c0005064a03000a207000541e9200c19910000c406a0760242c0180154841c200e503c42e00840905549841e4440d4040c070034814114108841c0e1ba00340180400c1e0001038100c464250801c001c0318070400d07000607030801200c10012010100ba81101400f11941c0075581003055151520341c10322041c0f02054100a058541c1242514034007681c8a0402410035608480304c0d0300040c04400307401d001c1e9113441c5804c0e4000303854 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 618349073 1250 618347823 618347867
    0xb040b04022404030c0e0103050604030c23010506090a05040c060507031704060f0501080304050d0b0a0e011b1103071a090705040c0507030e0a03020d0f03020f0102030a14160f 77
    0x1044612201102c042104042c580042410000e10924414400060103090480b00d580d50440d00c41a4541c80000e00103070034064a00c054404200d040c0b4005294004004583c440100d1b40340341c0c09004c1c00c03041e00c420b4841e03081040410101007407441003d0155a020b0300c10300d241072030030741d082d1842c1e0801e203002d030140880c0300580c01d1f50014140105204910803c00019500c400080c12000c660041e00042405e610600080c000ca441d140154402c86030000c408051998998074424017030105803585100e50350030146100008284010f40520001060b11128400141146070307075564011003d02815541440004010442d0360040141e00041c1507420395a0040d156030103d02691240751070a80011400118501890f038014440c42c81e440c000c54030000c10f01e00c8c640002e443d10f119008081d081c107107006244c2e41018000c00100041c5070303103c0001d645900c0c2904c0148014a00c3c044a400c081040500103a5080486a02c00046407a01d0b01d50086403001d402084800a4071211020038071109 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 618350323 1250 618349073 618349099
    0x20108101a03090d0807020d0302070609151e05150409260c010b0402040f03020f06040f081005070201021215060f0d3306050d1b200a0b040b0402 64
    0x10706200d809016061141807680c0b410181ea40c00d103041d446421030f50411013400203108040d6404a0304226069103450056200c00041c10188024079190400030000d131a50003903030400c4043c0780c01c824000991044e0002140740c9103c5c042042e1030080300c0d0503a00c1c0d9208064040c080c5482e50041030312034003510480c0c10302202090004450007441c00c410302296004078007069161002d00442d00f489005407000d500b00303407030a505900d10f44000d020003813040d0400b0b110b09225456040039107005280e00600c0c5818550f0320b41c0320544551502c1c407210700729420300c8000783c8443d005008032828030100c40b101c04804d070399015000c000c0b54401ca205035403240e0100304c1401c054039680060504080c03800400140c0c40c00001070140400e0b00c00c90504044107e0500c0b20302d090a00010103000c941071814602c1e502e00c0b52000020050200f100c0400c4545070791410039501d0755005040c1d000c2c113601c20b0000e209040e40000c40940d6a40c800400a01c124120000200050004c4110941203403010741418071410f6 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 618351573 1250 618350323 618350339
    0x80609030d050a1d0604060c0309081605030903071212141801050405190f08060618090102130b180111030f070203030c0a050a0b070309030f030c0c05030a030603031805060702010810 80
    0x2240180d001390754044000d1200303002e034500c00c1400c243d5440c20700704440a910b664444560082c03041e0400c074100305203842014440180708641010030020b0945091540707400426568109800301900d264078054021460140251710b1401100711521005041200c90300e48680f0207104c0401c03450402806010010b100c1d140c21078090b82c070340c2c03160744413110315070420405200064285d40007600c9a80030a0034082252106c1c401c03c1030205110884d100320b0350b5203106060180c07041000c440400c0042000000e000d00101c000b50026200020080862001030001112058905034905016800411154940c0031107100200f890600c0035050741d0800c06c90312a60b50414001580c280c800341c00c1241c11b00d08001c80d01c9004c41c0e01001d64242004400c080b520000c2c034824244440f902030540c2c40d48100d42d903a01810a16200b03950103412a40e59200c1ca1030024081c3c50030344021004103000044540001c02050309120954a0140c0035a0030404503400440e4000c10181510304454640c03007003c18050 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 618352823 1250 618351573 618351611
    0x301090e01240305101109090709050d03030204180b010905060d0902090c1306020d0914033901141204080403050609061611062706160306080609030d050a 68
    0x608004002009491800c1c07503414400c581051703a8402d07260071400880d030010030301a654040d07c2958500981d0b0385400090b40e4026540d00450750080b004d0240e40c04059164000708241d0f20307000400c8009003403400b004401e848450307000501007800706900384036604058000e0b150070203400b079021038421155008641c03482004da0744645503550005541461424031031440d4018212840103041c3d00c9000b03080140f14889500030302c0f4144c0315462940105503030821101800064034880c0c0c805440080343e40008803545d08202940d080a1181100c403298001c0d948506030f0341c1c0e140d602501d4440e80010510ac0c42100030000c4880c410240070100220310b04128040c4941007880041c04a030508800c141014040008000100090184112100b01d0702141c525000400c039215001c402082141e1300c0098001c01000c2c0708030303100306002c10604880c4090780002c8254030303031410041607460b0b06620b9100c14044811580300d60041000c401885520780c4419445003074204001014521700071102600 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 618354073 1250 618352823 618352871
    0x1140d060b0301090917030106050405060a1103030a0501030302061003050a1103012703081b0714011d011b0c0c0b18040f0c1205010518100e01030305130b040b0301090e01 75
    0x1d160303541700c150200010034a1a5aa038411103010038215071402000921900c9a402101e0080c20b01003000c2981c80d00034170301c1003190b4155409498a0b40f800031310420040c4000d20040d03006200c2c01011505d034203e0b001079201940c0d00700d40034008002031603d8081c0300c0c00d1034200c401e40540d6203100c4010404da809180a40601d0305403010161039003107003801030050802900382185050100400c2400121080c100c0c2d8020354001080b12031509010b401c14010410040f60b841d021100718522a000c410641c03000c0408120f520301d900c00060b40c881c007101e00450105004061480c240418040319102c81c01400d0508505c0d000303242c1d404003000c00b0030f0070b0f2000c080c48001c420341c844800c0b16101d40c00207180d4441c0015032100b0480742d8502400211000b611002c502d11000380e10003c200c64100305041c2c100500802c060030001942d69140081060740804c1d0502c03a446529200800c06400c603030201c9040745c661018060840e400c1034580d90003419000719481256584070000d10740b51510000d030b110701c = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 618355323 1250 618354073 618354089
    0x1603091407060f0815060901081005090a090618020904170405040213090e010c080112061404050a02030d03020315090c0c06150f030f071703040e0a0c0e0f01140d060b0301 75
    0x416000d03c1c00b52894801400e60341088a10303602d180c88a40398401540d031704581c2460400100d480b10b11324404c00103001c0e08090380100955041000b8601a038010403049031203a10104044001c02c449040107004000c0025031216031440414041441c101c9110a0500071140e0303646031561f6100000c04a81c400490801d21500700380301040810a40e1198403001a1f0a00092040110342400245110014001d94102881444600081c072045074090441c0100d0310f1030100c0d80e0b080604006a035500c0149049200e4814280100b0131244240281c9002c2e582c0c01c0d4441d00320032000410803000c0031008101c5040144140310700060204100129409015440380b06c2096003003481c140540ca905805003540254443e004a440c84100000c0400c119620502c8101c003510a8111841c00c5200b2b039480b031044041000c052151409a603485100080010307114040b0380900c0d941404480c08005000394085682c402022500f034250a00410450380c0c3d4120003d41540c0380c0d500d10b1000d800c00c0e048050 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 618356573 1250 618355323 618355337
    0x3010306231e090309030601090507020f1203010509070c050d05071505070305090c010c15020a3f0902101805030f030c06010801050c030103120e0a0306020310050603160309140706 79
    0x1101d624800300320fa00491204095482c100781400400e61798903061003611400c1d039440002600061091001190055203082a0703141d484501c0d00710304047d0828000c03180300340035501c0420319850091008021032a4010042e2000742072401c401d4505421000007600e00a00c85088048091a6481803905c01d801903103001845043c6110000c1c40c3c17007105801345041c8181e400da200c000c070b09000c0541d0320860303500130050f80d01c0400c25401c40d0b2a4041111642c1801d8466103045161004101041038030a500e947c40c4a003200030310b81c003005540801001a4014842840c100c0f080380c40b421510203070442020b0614412507864020a00e00240c0390415040b07a04003259030f104000080c8155401446240000c0c021800c0a51001559200600c0001c1130511800f10310080300d401080401e651202c0100000d8135a070b5a41041c1010350303c04c0301c203d150308803840e0307010480740b43c0710301901d00a1500490210f203403003c0c1d100c00d030020a404c41e825140e4148104c113005090004001010107480c0c140e42d002 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 618357823 1250 618356573 618356611
    0x304050a060c0503070c140a0b010e0703290d020103110a020c0108060315070f171915030c1a0c0106081f090803070f050c0106240e060301030623 64
    0x107045800800100c420007508105114030141d012800706906500140a00645040e1071502c519040c1d4100c00107141e0000080002a24050000002d10400ca50f0b02c0620402110602080c02d1032a0700490ac0c4400b03200e1901780c1810709210072004c001c64410704001944100c0305100d1001c64201a414600590110070110110b59104c00d407990002401d9004101c0c0d811400103070000544010500780070080c021842c402e425102c0c1c6488000d032030140e8a10380780707030170007107109031440020306c945035009411f20410309524400c441c40d00c0308803a0010200300c140d0303090881410072124154004810314406001002003e0020305c03842c2c004098003402811203103c41c0607212011101c1d0030640034454907080c003503400b01d1b000404070390307000c0d940d45041d007001c50688200740c03132030b00954501345a590318040c404500d8803e4100101c0d8191105071074071700541c05c0400105e62001d01c1c062900c1d00408180010000203904d500303d508a1621400c507982c0c0c2401c2404000401d0b042118100c1d01420402c0c010 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 618359073 1250 618357823 618357833
    0x1908121b1002190e151e130e0105120c09070203070b0903030a0e0609120a111603061b0e1309053f07030c0c0f08011a030d0903110d02060304050a 64
    0x1001a940e910304011416940d0741000444503078171149206400c100010301000d145000a858400031407802c1c26083d2100402c0c03030011040c110700c5c051800c69070401b40000ca100e160404c011800c404400005044d981120000d00840c00c101034580001e5100a0018400080080000e5445111083d0066440340f8045a0f50000d40d141d00301d00d640c0541001c418070110300c1000c10326600c840b0403114a9070b82c0c0c0003a044211000300755114543c190b805002c040b50b443d4442025444205c0740a02d5080c0302d0225108041200d0032211106400400c90300040d4900d182000301882e1401c5641e844005900740342c94865904003040f982030100c3c602d400c0d194450002020898500c0270100c4854800320401c01c030504101c4c603202c1c40d18040c0a000c500303240d881c1041030b19100117024284901c1004401682ca500c0980604081000ca15507020500396415403070400203006051000156142c400c407511f940c032282c04120018482c00d0f0409820020103015803a00c200030b41c09548214018000c410040c202 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 618360323 1250 618359073 618359107
    0x5090307171002040803121317070201020606010306150e030a08160302100501140409020d080a020c0f0906090403120b042313030e060d0603021e1908121b1002 70
    0xc044403951040c40f040c0504071001041d103c41d40542d1003d80440c0d1105230800d0000c1c1e504480c02007020340440007030070000018078050241c061003a0212011900d45c1001034041d1501c2c0d002d220b001e0510f090081c8807151192808600310031003d1f00f80c42c401951621030040680c884403125a4100c600158407080580c100042175859070701030020802c650504133080803210603440480e2250740c44510100555403901c1c15441d4407648503802c3c69079007460100180d120104030804502ca24500703c600303039640c102800d070180714900043c001400b5940326507040d0741581c400044102900ea5071610020981c507903100e0010003150388800c9840c20395880041c2c1c8100035004103500c1c10701c0c02c04400c1c900000e0b0042d40308480306004403011611a1050b210035001004c080d07101941c804000000c440c814801e10144d50001c520645402d0147d1030344d89101025506a4403070410542d121134109103055007614003600880a180c03450400103c019a441450410100c9445444990003d0004180040001 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 618361573 1250 618360323 618360343
    0x80108150112030201380303070506040807030203070519020406090c09140102150109140f0103211407050d020f0a020f090406111602010f111c0509030717 68
    0x100800d500021295494880038042c03140074181001c062401007014000e4101d00911125829100c15502c030011040701310403c0112050350742213100070045c0c9030703007801306c00c0300d24154000c402002039403120341d070390500341d44070030402d50440c0014449840064004e102031280080c5034592503820070120700400c412106198040c1c100145040c0131004000e400882c0780c0b048506a000c4100c880494000503820120b0302040c4110f0f24461100100760817040794407089418405010010312692030301c080c01c603090300c01c0c0809440401c500000c1110010089040c0c0c1c2d01c4104c0c1c5c07400c00070041d5400e107a500d20340c010a0013110f081c0c1103c40c1805810b6030421080c009a130014009042442081d0081760b40c0203841608940144000d82c0040d0900030660040700c04034464000042c1d4604626404003d0190440340890014020501c0300e0a0719109210314141c0c0ca02810240143c01045411840880410425402170000a120505155500b406081d009200e10701c1e031400d1031031904076114145001c1003 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 618362823 1250 618361573 618361589
    0x80a080f0702060f04150c0518060405030709020f09091305010506030601060f0507050114010b04030c0608010e01090b01020f010c050a0201060f0b0a0f0309150c02160b0a030f29010801 81
    0x30007070303665400074001d604001450380e400c8407510795040440406004031009202c01e81041d43d454000e41d13000e801032a51034202d580380c14200e00b0440401209200c2c07880343d29415072002c04103004446c21a0b0040c1040e50550b81483e00d01810500412000c1e007040f50102851004c140f241c10904c103007030094a80c070100407000b0f01142e6060610180c840a40708844408128000c54600208103003544207800e03008244130b0041240da50b030b600804040d40b081c0001c99010203031201c00036106001e0f401c1c503410788280c003010180607828440080010469425064114425a40660341e10442031040180c4a801c59580701c0e0345038124034000c3c1c09e40d000b41d0b000c50000c06080c4010440c51510301c0030f0b500340c142249045c0e21314072141c00c0b00310094000141d014005401040c1034102c09280d070350142c40d2101c0725400751240c00c4500c0041c0c01e41d200041c41006c8480b0020440340241610076448090196036047c4001040c10b014852000714070000106a114194504004046e40d13030411f080a004040072 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 618364073 1250 618362823 618362851
    0x18010e0106090f230a0e0708120403120503130201030905010212041b0501021b010e0118081c0206060d02040f060f080304050a170c09040c05090a06060801060201060e040803060a0f03080a08 83
    0x4002541d04d240020078038100756a0351440e43c5113035a801c2c00141d00400d282c0040750700b00b03984850350b80d68550003480203d8610080ba4400d9a1140c0074900784c900c28802074180d112107103601e8005501410303403804122003035507003007051400101e160641d06004a001d4000c03402003038a608070100103040e440d08114190342c0304400200b07881c258a541c40d0010383c020328100f10004d04803001a11a503403100010350344641d40400100703111600140c03211864641805860308145c00c04001e90702d0340740540b03403d07410058a03107402c005418160040c18600500d071100040c2d65079110740b041c0c0d0810568125000c2500001800c21692520a00c003030003a00e400b04081c07000c452040c050a0b914050000c095005450140c00101444000e1548900412000e0321498252a0950102000b4406405140045003404001184e8144140704041c155099001c800410351255141c10203940c200500550f40303c4011180418441819882d8000943c402d04c0001d4864800d44405401c00d18000c200000301520 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 618365323 1250 618364073 618364121
    0x703211110060f05370b070305091e090703091e1b0b030f16170c032a0d111e0a0201061e03060209030c032e020f0318010e0106090f 58
    0x800c40311111204004442c0915030940d218160170045240c0c460100101c4c0490803009050704900204902e0f18121001c401c02c034240c520f14841030400600c01034026031400c0c00104058004d5002083e4540500c403054141c24808025510aa403400401c44400302c1c28024040d50f030655a1000014011140c022800c4d490405020342e1101c100074001c48110003050301c0712802d03501813400e02c41c241038a00ca40403134502d000c0e000710900b64010f843e0030301103841c0595030080b0213080c00d000c40350042601c072040345030000a841c1800a000103c40b1408507510401c1071201c100d41d10b00c195152864080380c071507181c0103504070290846025900c854441100c2c04c2c2000d1903d84060040400d880d8001c4c40141c95082c81004a481d00503a151540c0d0140f050810003014a20408802002030325110488091b0f018000d101c030088e4050400100ca01c446c0620100300d00c40191402803030750700c982c040002415220310840c5070035074040b54064082d0503135900f007001d82482a80101960400b40000c05080b61038 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 618366573 1250 618365323 618365359
    0x12050c060907270608010603030c1223130e10031b0b0409050403260a0c260615030a020301060306060e0307140d0606080f06090703211110060f05 64
    0x40018090300b8940e48540b901d0111942c42640503082e0440200300300c80d26854094007440f041c820603111302f030045441080140c803c0108c205011407802844407102209280b5400c4c81e0061080024108541034001c141d10326680c0c4010b110f0802c181d1030002141c85d50a10055000345143c5002c00d01c6103c500a000c0010300d181100d044403c41d04001030380d5034503820b00f1152111180000c4102c1003e1400c0200125a0f00c080d00340101c03180001088401d008100603505448289a4a140004140c0e03421a06804043d1701c1940440060464040d045140d5204121a4800c80b00034007000e40c0440148005a491302c120000380c551070074800014016100000e83d6401c0701d1099140c407040445102040303484502d055a103403980302c10b05002c1c41d9242d8514548500d0707036000f0700400b40305010029003885d2000950703030226070f0420600c08100504080959107030740c1c0c4003440305c10300140f02e0b134031024000100201c10602e20304103400603106003002d1180310b000d2010784c0420300c070301c00000d00600b1141d = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 618367823 1250 618366573 618366599
    0x91f050403170405100908010f150e04140d0503240102150903091e1c0b0408031b030a1a0306010602030f0d140705033c07030912050c060907 62
    0x30b508900d4803095080030615442c82ca00c00c9421943c3c020004a03200e001c2e10381c00c8002c510540702c0390720007071000007000c0b001c2c80e0458820704d00c1c03141c0302e8410300c1c8204000c01300300310b0040c0c1250160203040c0c1c203084030a01813440c100701109060f000901c00810007844da408803102d100b6a001c1e160101c6413014082d00000e41c0c0701400c081c09050782c0c2c2150701142d808803040040b00d01c8003602134000c42340030803030401c5140c0b1501000d010600607a2042660703140b44070800d03c99aa000c2c6d2101007401641c8564482c1032141d0402030a40400c0c1c1c0b256002040e500e203004001c0c40c8076034801c0c600400e002003182440600700004449d424040d0b44140c0c010f005250b004030070b503292005e180b0b00054a40d1101c2138243e016203401001202200484801c1c4a8038a50140c0114031401505250400c6040400d07035600d24504c5d40d00050100c00e00c01d1803900c0c07140d01408825600028280350101b6015102e0700e400100703520054001002c240c0001c0d5810082009101c59580140c145018001807441c1c084d124000da = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 618369073 1250 618367823 618367829
    0x20d050c0a170d030603080d0e1c05070302160305031b01110301030c08011406240f1201080d050703210b041103160203040f051513090c0905030a020d06020912010e03091f0504 77
    0x2180e200c1c00509d007441c00401c40349401d00c0080060903c0c41c011140090300c41d501000003903006010b0190007481d00c0b49288800421030303074000010b502c0c01207440c004c08000d400c0303012410155501d03101203609214080300030b1406940120b5000414070700d40f01780f06003144d881941450240b0300c0c100c02c002540c1c3d90a00040d0020268540070301d0b061030740d040d200a50748100403e84880090210380080070410010b0114107807412481240c280303224618050f00c00b0302901b5401000503040c60240c49440029200d08050314540280100f000401240060143ca00508200756401004010440c601818906081011100740007031403400f4107118031a5041032207400368a014020790b2000c3c48448040004442200c2107042e50108403544030b400c00030192805d9001400003411150000c200c03464046000e44000b940202489018201680d0b983c0107500701719100c0340e2111140100a2042c0c0080c02031030100000711010b913603552681010856800001c50401000700d42030650501499080000c81f810307 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 618370323 1250 618369073 618369097
    0x100c0b040b10030204020304050609071205030315010c12030507260606030601140307020d02070605030f070c05070b040b1c0204050105030c0708041205030a09080c030a020d050c0a170d03060308 85
    0x307541e100c150484185005901c0250050310000810081c0300300460064080c0c1c201405442d0000c0e0703180c210641800035078802030069041080884c040384418041201c0081c41810000900c8865864101400c0142c0d0541404262034804000c0000d50140302030f001500b12800d4146261145900015070120080003180551000030103e0200e80c0200ca21081c00220312010b81c0d52441c0c1004000e407142c1c0d0700349a810141c455075002007111409101641d11502600304086980d642e017200c04c4034112400b010648541c0030701d038004100c0b25020360043c00540500c2c1c02469961401120664032485031402d040070b82441404140481ea80c48011a50018048180d00e03482e00ea040c2450030302c510540d070001454403850924403003000f8021014040c0c40d952511150003071969058055154001c0c2c81e0503980c9030300301810b900c0040c5400c3d064100b0b00760080d000c83d200071565402040c0107070940e400070a140300e0611a40b8015800410004005140e2481c061100d00e103035a540b51100e01031000301c20b0b2 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 618371573 1250 618370323 618370343
    0x15020105071e0c020d060e070e01120210080411060c030a0905060c06010e1504060e0108010b090912071a0108011e1415030f1b100e0d06050907080a11100c0b04 70
    0x203645c3d43d44413005501d5000070b8104424000300700419590303980b03031080020503501900009010520801d050462036005820202041908001120386a600810845080b08406e0b201402a00c1d080040c14040d02800025650380004000250089a140d840740f4858a1f00b08280c032100100425020b044951444800c00d660720340aca024142c00710a00046504245030007000180541f007484064122900340000b080300e003134041c0a21026210440c2c0c1c105c00390b4420810120440030b000001c0009901800321030040d40952801c9446041d4280c2c0126210f0f0744800c1400c400d10310081031100e010320b1a25040101500403120590030440c0205440d00f0395100e200380500c242c90074480840320402e800145d0f034036158010718030300343d034049181404c0c012114241c22400040c01510800440c400040c000c0203c0c013125035940002c0d203401012407085d40168000080d15640401228412910070440d03403d06191881c00c2c01038002c0c010480360100715021030500042034441462030342140e04045610703 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 618372823 1250 618371573 618371597
    0x4120f050d0c03050a050c12070f140c060f0c07050705061303060e070315150e10031e060c03181b0816150f021005100f15020105071e 59
    0x55414080d81c001e1011031030514440b01d01481e4540e20140c80368031001c0d000c1106c1d46803c0c2c2c0c070034418040d00e480c2424000800000c100100d004020030003c50f0524030b480078445102820481103500140c04102550b07102105102000c14424001a8094050381c0344508018881d21082d50303035000c41c42018018140081c2c0c0e41440154503104502440d04140180121160002c0c21075880c2003d00c01600c0041d401650801464054000c10080d07032a4460f1120140d0f0600e010044444c03030252180b030070000340f40000000a0000c01020040348000c080010b80607800341420310559916010260405140050281126285040f100f80341c940082c48907000c00c2540b03901401d0720300301e46c21828061060748a0303c100149204c4c41c031001d6450480c650010713092000b405840c0030704551003540140c3c2101c800c4440b861401d900081e80005100f42c100c2005a03601885e0741201c080b82c110880a824000d00a428103809000e03081d008041803802d501e1409a000803c0c00e0786280750a45410450091401 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 618374073 1250 618372823 618372827
    0x507050f0603010e100e0c0904061e0302040b1c08032212050a0309170c0106050a060921060f05070215010602100903021c0c0c09020f2b0e0601090b060304120f 70
    0x5070018191200d242d20781e9051101c44001f05d90095034900e40300314141000030500c1c203079807800407003818144290039440078216820400641024640b407a040388122941d181d0680c4420610000715000d035603c0c503680e040c1106124000b0018a0f91822492100c540a00000d0120038804081d0451131030300c0740e180c40740711400300c001d48500000900381e0540400b03141c610882120081c14289000c0c0c008202581d41e9406001d1041800d214640204106c3c0c0f408220541c01014060724480181110882c111a683c0d52a000c0315071605c0d003e08217554030030401a0283e010410420803c036096001d4002d50714005009503226505040805626281c40030001058020400c0070000c8044560507241310721802e10061240480c0c20090b1001c2d0300a240004400d2014400c07030b0715680700c0c0480686440003181e880d00240c88010290409110900340400b503241c2d080c1b2403400c0d840c6091014115030b5140040102c15600341000d40f9100d99401c00070300c00060b03004080c2030700c0a280e6051026540800001c2 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 618375323 1250 618374073 618374101
    0x1905030d030e5712030d060b0301030b0f0402090406020a120612020109061106060f0a08010903081801061202190b120a0507090302030a030e15040b070507050f0603010e 74
    0x43e0b1004400e00c03442c40207180084507040b460f40e48891050f0022010b60003503400c0005a0281c00e00f02c10380c486016440d1420a41c0900300064504000ca91801c0d03070400d07403201110826031250134010000b20040c002c00a4105040b03030886808100d80700142402c0d000185036681c0588010306041c3c0c000b07000f011140c01781400100c080031903802004040d81d20b6100132030400d1480e034201e0004542100100e44c0d10b010b264950031043c0d041000304115507804040c000721540c004012ba6100e20740c0c510004600109000e903048151203651002e0b61030400c1400c1c080d21a0501d00051403d0741407400c1840007520340c0040021858040700c0180148504108900c80d0940641140611400000344070901c101c0800d040390280890f0ba00070007603079440310030440b80d00b00b050200941c1900003058120100307209205110910600410070300c10054581030403030300f0b40d00550040c01d08010100c1c0100500805002c00002044c041d58070401d5001c010000070101d120502416256052120205a4071451052 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 618376573 1250 618375323 618375343
    0x403030b040908030609070305070f0c03170108030a020d03020a2c092d010b0a03020a020c030708010c17060a0e10180e06090d08070e01030f090f021905030d030e 71
    0x20041001e82c101d03050080d00c0b640211031042c041c044110109500b0742c420f1241ca482a84507580742c460341c0e04001c0c0102c840001c5c00300705508001d203030300750f107488000d02401040c02040418015a80c0c1c0811160190070014000b031104245403061002e1a41e486d00110700c1c01c841301c000c140c0100c542d811545400e0103404007154081d0028110300401c5022941c2075816540680020b900780f80c0340e1220024200701440900030000000410f0101c00029030094010340480c00140c016659401441d00200346007041684c000002a9140c000340c28a0070303000342508141c1500d650a58085152a20104201d03041506c910228900d144000030211904185004003030700d0805450001031762000720481c00b07000d1008102000d401741d4008203100c1ca80c005a41103c600030368603408402c0e81c0c0e256081c8c80c081e2a0103202818151241c29008a07407441d48a107443e882d104480018400c100c80c01800b00126010403004ad9540242c9814800303a50002032200030303081b0780e00d4081070340074502034005c1c18505406 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 618377823 1250 618376573 618376579
    0x5010507081f0503071502150405060604062312190309050a0803070314090a0305030712080702072301170901050103150b0604090e030c070602060a0609090b0f0403030b 74
    0x100512244650100201c1c0c001e0090721000e100e01c145460003403507801941d10403c0da0550061400b001803442048030700b1040040da005a07640340c0310740c1c0341204020b0021078080301c0a0b0440000c000380d0380b0781071042c58003410303010151799040008624004c865030170070203416105113251089802c0313100703007000054aa22440d00d804103100d0958a0003401d05040c42c040c65103e112400c80200d91740c0400001d0314512038140ea03490084151381341d0392008a902083c1c419800c03010350038011003c40c604000603e90b0a21501c1501c0042d00c1000004020020107031038031085400220081040d101100900340804580d440240346002d12140103132200c5c290034003468500380e0b030b10007040b680d00c0040d07000701e04a074050148045428681b803420812603d4545841343d000344c0500083c0300030f400e9a0300a941c041d0b211002c8a10b019041e80000307280850310780c410340c011b0707000c242003240a034001e01404005195811051125011680d02c002c2c50b603100505010000540600040500d4401e0300300d050141400303 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 618379073 1250 618377823 618377831
    0x2010207050c06131d15010c121110020406050d05010609030c06050d02090d060b0a1418090f010e0703052b05030709091b020606271f06030501050f0102070b090105090d0501 76
    0x400d00c03990b4071702c044a19081d001184e280003003081d405403090f8210b155000c050a2a1512002d10659207a81004041421441480707502c00d0221218402403002d00707805c0d101c55407601d0f50941e401c070035141c0503045842040003e602c03c00008450345402d4003642d03500d04265481d040c0c0418a58024020f44210302e0341700c0090029042400380b00c0cac4c010b6002803400d40340105020b03264807150a10700107110b25103400038400301c800e26240008505054101c00d52905948106450382d11540c02d584c1820080701c981e40108000b001080800c101d900d030031554204806405451081e00d40c07024032500c10104007409000400101b1513449001124041c1c58580c1d0100241d800c2450642c600d081014003039009480f83d507001c92060f02d44054004200d030380118601d41554401100c07a0b0190320040e00078a618049000c031542d40d0340c51b0b00c0250014001c241d034005201c0d0300d4541001015450501c01c0c0f410f6402241051180320200c50071105813071000c0c02d02c0f903076540040c4046900c001507038901904552030 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 618380323 1250 618379073 618379109
    0x8031c1b140309150c2208030a05090103020c060408130e06370603061403010203010302030a030c0206040b03040521070b070e01020a0b04060b10050a02070603150308030405100c02010207050c0613 86
    0x12005401c40c0c0306c1425183d0b0b0f940c3c10604000c180e103a1709004902e019481400400400fa200d90002c00300c200040c5070260a141e544c0301c103e4034013502500e046403030365401b1505100790040c054403c001000764504c0e104031401d0440110f401203417010011120f18010100404200c0072a0700e141040c81d4640700c645404558a050040c01000c02c2c0c02401c1075085001410b928030714050003568182c80c4c0080150080400c1660141e40e5413400c10000c9070021000c0c0170000d9040b4012000d544202c0c01100a064400520040c0e94449925411070403090107082c0016400700d046070050980c44007080c100340551200210041c1e05d0144d4041e0000c0c4240c0c40d80c0204010030189070000120754009840d11824a1141c00f000c0d1500d0140840000069000f11000c1215a119800c440040c1a8894000c08821345949510307180d94801c44080c0d43c5640124070403000300b1110322482c030284295100840c10880d40d030f40c0b1252182d44000ca00b82c41030201180c07043c0007940045483c001443c00156044c0d01240b = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 618381573 1250 618380323 618380341
    0x7150216150513050705090702011803030605010801060c0b190e0316050105010509040317070909020a03050603060f0108070b1b010e1b090705040509040c08031c1b14030915 76
    0x1c05aa040e0380401e080c000072500399110990030110056111002c2e026150401c0144444504010018801c5640302d4083c0d2551204440b44140c445003e55404a4000d041c0344c00948400b0041e4059400c004120103802e001c100074540c41500095190440040c92100480e2030020700300880c200d00ea640000140031000207040d07960b40440d54840c20003402607a1740c0e6001c101c607016040b100940443c9804041300c1c41d41e041080c000350700440302e00385045820380714040c400498100002040110f90382c0c0e000c0c008185010000341d03520007507000a004e000d6060041c12a1100b800388983c185040300802c5444440349000c540c00f61101c00c0b18020020f902598505540d1034000701c3d08500880c6c0c00c0941c06556042400360284a010a42c585528061409c410300600c06c03002402036580d40c161800108a165081c001001000c48039017091035469003c00042003201e81425481481030051200d42c00d215070410805080b48214a85a54032582e9003000c1500300204024241000c10f004020084490 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 618382823 1250 618381573 618381593
    0x1b0f08030a06050f06030708060108040f08070803090c0f01051b1e0a1716030809030d11030a0b1c0602090d05010903020703060f0e1e0a3c0807150216 66
    0x388204d692013128000030b420700465100c15280440026801d000148655000b00c0c9803a400034401d04104401001c0d03912510100e130041d090840d58180000300b0300c00305140801c0200200c410464095003551038041c0080e1043c41440485920012200c02c1701320b80c000c2c1803004542040b21030f5000b400c10032543c4241ca0300d07501800000c445a07100c0007480c41c119000c44c02980c0c2941c0305400000082c2985443c01d60710468014480080c0744420440c42c2c50090782e0f070042c0074410121411050300c0741070a9107040700791000d4200f514020b601480c00e1203e061001200001450b0308420016600c600030310200e00803290002c4050804c0d801d081c804000c041c2d0000301c81c021240900400c105500450218400b45c509901c44078074254020304264400c4040d9103850f095503512407003104c1104507259900741801c00080700271450200500e100c14441d40f1841d907407810f1020010004802401241d6411080303002d0b00b034010303210320030861011030720007101d504070748890450008661540080d0301c0c0a00302c2c2 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 618384073 1250 618382823 618382829
    0x2d0c05131502210f070f06020c0a03020606030a02210304120f06290f01030e2b030221040809130504061a031e0106030c081c020606011b0f08030a06 65
    0x40c0300f2a4510081061039000e070503181c14801d04480c1c5031009402d040c2003a0380102405942501a4061107030000350f552004081340000c030702c0680040c407034600f0040e06102c002840f00d40a5042a5602001681c8000703100c2a0303403c3c140c40c1c140346e034415280e01d181346020b190040c044010550180f041841030341801d964155105140502c140a81141c20b035440020b10b24454904000a0702c0e606450b01d004440d100d04d014040c03400044c14440025418580048100c0c40424480002503900d00102d911815900101c05800c0540c43c1031008940340c0310700c0203d4000300620041c2e02c40130804120f4400112540c0391070081c4200103005d07128041ca0018074050303c0482d4418a00100100c2e041554802c01c5444c440080150031020810024508a01802c001c41a0155a1307105c001c00024a004250005071420300c00500c08400c0d1540d072080b83c11b1101850005561251041041680e8400d07103403000c190380c1c00070020081e141403600c808600b21100300200040030100400240c0c6550740e00c00300403 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 618385323 1250 618384073 618384077
    0x31914190308330607060b0a0902040311031c111504140613030f12020906040801140a020c06012d170111040509040f14070b030a2d0c051315 62
    0xd8540c04281e100c440101a80742203c0c0a4282d14080080e180400203820030324000c0c44041000d2403040d00042da400e8258009200070b5501080034020b000da000604240e0700010303001084407414403c800d841402e0000d6112042140da2400c0102000050001c0d1b200e60100560804c040c0c02c2914146101075813034825601c0b00d1207100000340c50300c0079150f02c6d5025160151103845001800c000129102c44185040d040c119408126400041c0c035428010b100130106c003400064400c5201902c10030808014102d100e800e401170150a4101c40c001c03074240c1c11108101c1d0400c0300900302020071040d120200f42d4901c115014414005070350000c3c41d0054400401c928020405407040c0d050f5648c7e240174501400b900015540c4c0058002400d1b10520403c6138014a440c203403c0e207085c070802e0300c0e11165030000c49028501100b8090b8050050250a410f062551841c5500c0722100303105186002c84080680310040d01c803124900001c3c010030803100740b10301072450a1002900c403031605003000c0c02641310301c0c0 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 618386573 1250 618385323 618385351
    0x20d0605090f10261009020405240607060902090406060f0f0815100806150a150824040e071a0307050304060b0112021b0c031914190308 60
    0x415442e0031015481014640d8101c26403505201154040100640c4e955a200940701301c0c600072841d0402c07518085500910012a00c0c002510511054800c003505a0f003001d4603680440003984101580508000000d480b1561110300500300750010b030400c0c800207074100034020300740020300c121034211800703171004c001d804c80150390303902c003401d0019050b44505075072038108801903580301d83c203c440246c20a4111840310300c61901d41200c1828440141d60f07034150824000c80f69005810f012000c48001c0c0041207980440c034281640150810700014101b01e8541542048611800000303402c488100901400802200340d0103403003142ea50f0810b01404003801e4401214100c2c513110341c0c0440703114403110787c0c541d4117523140c076542e68010b406440d04441c184078402101e2110020688040c000c9030b10044904000c0e450042c002a0408291140307684c025000312820070303000111909548005036100d80385c0321190a015440b0b50610300d00b0071201d12000550000c41040c5a0703c400281d00030382120580078 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 618387823 1250 618386573 618386581
    0xd1b18020c0d05130504090f061d0f0a0b0105010c15050108031b071d0a061e0501030f090803011707050916020622151407021b040203040b0f0405030706020d060509 72
    0x65110b00844c42624110030704000180030038141a002844190300c80e400445d0595050b5450100303031180c120309516019520002c3d0080c1d14401c01c0b14100c1c01e103445001e440c098010342c036120301d45001401181c1c14000c014101078100300000300030403608459030404009a503103c2c8100c64076540091403071008008010b0f403400008601185030f1080318500d0488203000001144003030350400004103e0b070a2560b0b140d00014000603084620301000ca07008190044c00d508000014086441500200e0801407500b0740040029034240c0449054030340d242014442000151805460400540c00c41c542240d040414490039007000c13000016001c80d20740984c0d1241e500c030511482d01d0714035081c00c0590b0107403100070880450b0703c1500780f0300070004001c0e000c140c200309406144900002500c04030010380c0104000f0102a0041550b030b50702c0c131412a000d5140d4113050311000700814025110400e51800d040101d07042001c200116002c0c164008000d41d25101c2c072140520050041d40708607401811040c00107 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 618389073 1250 618387823 618387827
    0x1061202032d1b030907171603050c1206070801090e0c0402040803371b0506250201060e06040209011b0602120705070b0a090303180b180a020d1b18020c0d 68
    0x1485c483c101c41401804d0040c034142d202150703008071145041030390242002016007140300700300400c00345009900910040203003038240a204c00c1400a00c014640044040c05041a4050381841c111480c4010201c0c50101d2000524140070f4480350700e0354024400240000c4001c07003c0084e280029102c0c401d2a00150724140c0c0c0550594101d1513458882c060f0503503125141d0244103031a41d000703079240c0350100050460343c6d1103150100650350140c03119500600100d40710104070381034051034110b1000b440124542203540d245184003a01080c82a5008500311601d6481900349281c1d51500d0142e071100e030351050409200030343c008a030307409135051980300082f01140503c003211b001070743c070103a041420ba603049511402800540d1084042507100e040c0162505152214440900d0050007941980d085c9510b002c41c030340481d144114000e410005c90200076079501c50714495180c0d0454504075059128011140d403480d2a5004811070004100390109240e88550103408052608811a410500c0075101 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 618390323 1250 618389073 618389077
    0x30c120f061a040305100c030f0501080a05010c020f0a1e1a04110f010f03150806310f020d0c0b0f0a0f0801030b0c070203010906020c0c03070e01061202032d1b 70
    0x10b043c0354000003600606c0580d079800408080e865240000b00e04c5080312a0005541080c5d018503050340c84509207209020003031042110f0b4001c81d00003042c0b2150304c1d08100351141545280681a04548007104294a100d44007581c550390f44401d8280118440d00303203200400505890545103003800f1030a2261608010202e034421840503182d40341ca007070b8101c40403809420840c0500c40d2110711007000007090340c400c2090500607660740c0785040d01c000196030841342d590b59245614086802c00c0e031800c000f10388800c035000e04440d01910202c0e18103489041c0456500501d0740444803039680012081080c0c84100080d1400d03042d50343e60f0301d07606410024222481042800090059240000030442c00090360005100a5201a0012130aa4280c2c0c40326812a085a00b0469581c0c0012102da1500d1a0600371400a001d00000c040e0855060071401030a0000c94400d03c680ca90b400000b00314043c91800741e580802d03503020045200d04151070b0382c00c80c0c801c80540e03d400c00a1a0040390300c02407080c0340c0c2 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 618391573 1250 618390323 618390329
    0x20405090f0d0206091507020118060b040b0f0a052b11040e0303091c0c050102130503010b100804030c020103090b0420061617070b01080313090b0102030901030c120f061a04 76
    0x5c02461600301114840e0b0105034007801240656580e0f0b241e58104404030344060301454002c4000107201282c04050109540e00303020820705c140940c803041c5170305a82e00380702c20f0203070390302520030b0b2103a00f9045c402e400088241c1c818403690f403c8000b014608100c1080c0e02440d500300c047e1f034140859076500d4091540c0f800143c6107088140c02816003100e03c401e07a008280c514031510300d020100c1e00080d03110f840c220ba0005199000048180c5014411803c017401980c0003030005554090300f000440c90010f1241c0e00160000302004003030031546c002e41e07109030001c201c103075000078128100d401c04c0d01c0d10450750701400c84d04140f411208400c0707207651300e00300040c1c80301d00001c0840401e86082a541d13030f002c000b80001200c4980041408417401080f07032a80201e0281038400021503640c07a032800e102c007a43c03074540c2c01032101c5400e1601000e51a45d020003038a80c20413007170801241074800a002680d6012043c071600e903910345405960a601c0001c0c0d0003440440e0a0707075440040011480f64640311520687c0 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 618392823 1250 618391573 618391591
    0x19060b060c030d0221010e15011e020303090705010c05061311041e0c14043c060e03010b0a1814070e1206040317091207111009050a051507020405090f0d0206 69
    0x200044c40c4440c0070300454032340150502d000000010082640303004c01908102000042c2e00100401c0021001040020064182400d0803044811103607503590380c5034801001a40c11690039480881080840408050000b500070814403516142e4a000c00c40050f0129109401f03d090601603043c96004440c1901c00040c1d188800b0314082c1000000503101c80818a140300c8091b90685030002c0701c200d26000314400600348105001c039031605400511074036021100c148a079140c100304400e203503071342c43d08407003125585011720b15850010440d090081c0f00b895810310403280c0080422444950003141191000c9089070f8420000c02181d80701507451400301c034010040b40429002c0c11000100c1c0000617400001c1c0421504612162080c0e03e4043d040140c04031803a84d0b2141c2c0307030b00ca6403511410003003a500c85481c00000c811324110004e01e028a07107203d04c034095a40307940d00b500d212a03920212640f25802401c280070300d0402d0782c000c0342d4800d090030340f03c0c16501402c00280f05051000c500300b8040c0e0f0700300d = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 618394073 1250 618392823 618392849
    0x1214090705120c03010507050301030c06032703030f0f061a090607080c1204180501050904030c0602030a09200a05010c03020a110a0815060108010819060b060c030d022101 75
    0x201082c40305102e25089408030910800080f60182e80c2d003401028440c3e65244c0d100d903284c5d490751400782e0701046160130640515043c01c1841080b50401032075a10b492082840880301c141541c2000d40080070b140824038802820141c07051101001c9804c441304603810b48a8550700d01d0501e01c4100c0450059419496000e101003045c0c00c0410101005401c042c0800029900c1c100380940d40c80450381c1c0b00783e105540000d24501c0c04840414144510f90041074151411300a46c81c00342d5005142e0340301c90000401e0241c0c0030000c101200225881850741d1940b00c0032000000910090000411880e0010300f80300381801e02d4081000e502c50501041215410380050414188643e00c141ea00070303c0126054101c5440c050002c1e010700104089681452100308103174070750600d90001440410141c00103c2198017000c03202c1c0744040002c0f01c2c21046d03030300080000780018003000020482c1c070421003030704034609c800f0692031160107541d070060483c140c007907039a1092142c0d101c80903880390b042445002660340c01 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 618395323 1250 618394073 618394079
    0x504020a090b031503030c0d020706110a02013e010b03010b180606071211011409070e0a06030602070819090506070209070c020910061101020721050f040612140907 72
    0xb52001454100418400e941803040441012920b107801075003000031950300c443d280c601d0740ca07014020b240c0034220603e0300d150051400460560350310403030b604c0241001b4840d00034500211180d041d0500312a01183c4a982900389142c0c2480105000c0e0b03501c90140d4039040809140d440c0c144590000308002805001c410031494001d1410310100034001d80c1c1049040026000044c1e074240504559001c0344c60b0b02504148602c41142160080060b0700808401002070000b0382070001082022984d000d01204070350360340c0084a102401d441e40c8020000740c008034020082000072000340120442c0d00c9010003401c2c0003c0030882c1c2d04807984c445d458210408009a1001d8104080400e500901d907060075030306000360394046820600121504d58840d1a444010b00110340c1c09081c60704502c000400a500708080340d00d03050b105603000080d22a911188003c80c207400b500034000d480f00042203c0d9000e440302e64400d03000d000002050880e140e52841c0510207540c1c48031164000d8011140b02e4000c10724203003 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 618396573 1250 618395323 618395339
    0x130e07020f060133350a0903080c0a0306120c06021c050a08151f0f1404050f0a030b011e0801150504020f04080303040f0b24010806041b03060f0504020a09 68
    0x101240c0c0f0301d0810000c007140b001c05c0c041c10b041106a14001104050b64150941101c81903943c0141c0b0404c2e0203404c0c01f444401080d40302030344a40040150038001c0ea00e9103210010b40050500e9400308441c00c0e008260748040c040002105001c40c0c2a58003581d138401003070f468800328140403840d0307980860010310400506501c140c06a540c40752800b4400c41481d004040041d038031280c2c003858000140001c484448400d5800807000131806e1807414104500307a00da05841c0c00700d0180e8021075000301006280310605a540311584001550130808130441940c50f0130880c81c28030b204406005550f4021100041e194405105031083c014080c41c10a582c10b0500d81008003a50002c41844c154140500000c00c40c04014801507010300d01c51000700021207050324020380c00075070040240f00c400d90400001140d90f001100141444034007482c0140c16540c48070300007002000c2d01c00d1000449520716941120054161f0b103da1f05840140076a500c0701a510b6042001760700c20000d0302d42c0040c6d07410070104500e40d = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 618397823 1250 618396573 618396659
    0xc09060f050f0a1205160909060608040605060102070308130806010501090302181911090a0501181701150e041a1e060d06051603110915130e07020f0601 67
    0x321240c039203204e070b500c6a881408181c1e0300c03d0340c6588181c0d200706c2c100c1843c1ca40001e1440c0c018000204244189494003102914007074000380050003da8440e00002c5a682c401d100000107181c2c440310580c0c45800c101d0902c142129640591702807403103007034000300e03c40d03001d541c05070120707039009151040100140e04008825480500701104940181100b005d0b4040315024505424104070311040e140ea140008010007821941d1140f4184070714104005118029403000ca802c1c0c0e5510030b04c031102028101d0200b03004004400c00248506010380d4081840380c4200300c518002d502891107480c1c481d2999212482d28501a00c9903543c0703001d484180081400e8103011183e120b8002405842c42030100e031034580503a44111400e10009200da4031182c2140e0301440b8071116582d170032043d1400c00007014080b41d40013610480c041c04600010a501d80521400020000030301000103030721405042002c0040e540720070881008040d4041e00d400406e00320b64110740c1e0390b140c007502c0145d2105580c1c4280d040ca418 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 618399073 1250 618397823 618397837
    0x603060402071a090f061003030f1107030204050a0f2316110a060212070203040b2a0a030206063607050f04080703030e0303090102100e07050307090c09060f050f 71
    0x10782403001581c0703c0d884041c40039a01ca60f140c03001030704400301400e00c0507043c11002015401c030b0b10030307460701030001ca0350140c2c0d40c1c1303001d01843c18160084c811190843d80352241d96480294054109020003d038135600750804034081c04d80030002d2018550b1029030003221101c4e408008140941d00c1300043c052a440c0058413507040e22420101d5001d040101720b9400c1ca8000b0700182d03034441d000079048001080e8103192550004051020710f01b46404c0116509182c4039804e00b00c003042e16006060044901000342ea641d2014003901110542c407060b1034083e49402d411900c1e188122800242000c1c10944c21080114480180c5580c01101c0c9962500b040400400b4010004208044c002e458840b070510000740b002c0c0000c5002007850f286035240043c800c20181c45004d02039042803014102c40c1c1d0300000d004c450040b403d0804180440c0c0404045d10b004101e83c802c5500d07204032003001410300c4e240d034801c1e184280a6941e100116407a41c1e0140c5003465103110000014070100102048400004041c000d9 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 618400323 1250 618399073 618399083
    0x5060127050d06020a0e0a030c231804020102061509010b070f080c01050105031912140d060b0717091e060d0908090108090c0a0b160c030f0c1202060306040207 70
    0x6201e407128007064041c0a64401114203903400960750345000d80144003000d4100d400ca031305070403060440d44c1d143e082d03501910030405244d45480c00d4685001c0e1003020030309c01030000780584141381d40d201504200040705031402c0c0c0c054003030040421682070000aa03422201c4000d0107201c10b59107484004480c5a01041c0e007031f1041160000c9200004000400070042410088000304095040108040c01c040d11402c441070390943d00e1a035100000c0341320800d201414244c0c00c15455074003603820703403e201d44100380000128503c2e01c0c10207c6c0300070b011300160103c64000c500f43c80c00385c0001e890310286445030001d000d0784000e20400c50344c20003181641024941c2c00240905017891103190310b50f42501d190500444051002040c49000780d41e003c000f41c2d6000304104000c040214080f00450349503101c40c02124001440001c07c042d4001000d403809041603480486040301c6641c07814851500c0000c581d0465403210817030070000d60052150020b10109400411031882d50b03c0d044104002540302a004a603 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 618401573 1250 618400323 618400397
    0xb09010c0f0524240901171c0504090e0114060d06090f03080703050906061f1707020d140c10021b060720160303031104080d0e04050a050601 62
    0x124035800590b01d00814030b41003e2400a9080c890114440340010322580c0440d1141c100c10340d03030165516401103044500010000f8000000c0344138032070814120351141d1f2480c512181482c0a00c81d0f001e802401110442c01c010407a50382040c40f510b0a1324982140c3c46407081d4130102056171850400708124000344100e4000031101c02ca030b0b0307406a8000c0d0300323001a4041a2000308020f0919014081c00380d000c010308010b46040d2800c0340024103512109807014096400301c0445442c602d0040d0903403402c240750b40c0c400788400d280c041402550b070010426014001041c1e841889030700840c2c201030b1080958418054070205500d1202e1034001d41001e80c0c2a501000484010305164409004040c0102100c0d03540482c040e030004404204403201c5241810070b980b0a044040750348084101010640f40d00d40340108040080c40704546481c050303500204031074011501810341c0e854226100100c2d89a040d10b0500c02030b40e41100d88400ca42c41124190f01040c451092006031603054499214540700c0048944 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 618402823 1250 618401573 618401593
    0x21100c020327180f07050c0c03010f0b0f0603010b09040f0207060504030f11190209070c1e0b0c03010b1602062101050436030306050d03050307090b09010c0f05 70
    0x2080e84034049034500d0341001d0815070700c643c180310308002100029a800211076081c0444035442c6241c0085c510b104002000c100c2c01c052010070710400406440050007408158071518030324005010038013441d4420380304030070240d805082020903a030480c0c901d003d00300e05083c1c18405000c083e000e00c00f070360344485a08004141c0041d445226190207030303000e1354451071000004000506440030640c0100d170b9961002e0403140d010804160080d04041e415644140702d42c4620009840546903544000c02c00030701800341c1884114101d00c2000a94050512807860352211502442d10b0300c028010b840c0000000c010301e02c610200c0d1602614500c0c40600902d207060441221400c40c541058a5000507078600360040000e8070300381c0910881f4951207040b0f80d1a401b2900c88403444582c106100e150b40f603046480c4101890b00a0348640c0c0204009002c0c0c102c241c62038030b4000c10030350003140d400007c03488855012424002c480c00751903181c00181c40d444c90002042d02c80e0b00c01c001500200300e41c0e41c8070700c007505 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 618404073 1250 618402823 618402847
    0x70309030c060911120c0a0b1b010c050c120901080f04150614040e010501140d08070f11040e010939030507061407080d0b030a06051521100c0203 64
    0xb21041c081c4034014600c040301c104001454055040385c400c0ca074002103148403140e80e0307048007804840d88110301c507a40b118900c6011000340c025006c4140035502c4e11102d4040700c0c2e00840200200c140d0340042d00d40d180400c81c40349226002d10101c03030b0700140c17070800010b50170030000c2d001e6a0400e005610740c10154006007905401d0340c00d03613042004000006480c0d2403441c00c0078000c1c001d50350700302d0340284202c2d81072100d00400150030070f119a1154801000b5002848108000c03645140c1c1c201c03c03089030181c070505103c40c094081c0503d00d400b462511a035070206103818803c0760300091303011040e6840c0945040040741300d85405040d00b01119000f415480341d41142080500083d0301c104064000c06181010252440c00c1100e0011940c103020050b030310000b1901c108903400c82441642c0082c900c071082d00402d01d000e040d407030020f00c414540024803c3d0402d0114027503d5207002164050080341c18064600128114611100c40d030b58042c5034a803101c5155a001000d181030244100c90501c442e100300 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 618405323 1250 618404073 618404081
    0x30306041a1905030d0206150f181014040c4e200412031715040c0c0503180f03060103060e010f02030c0a0315170618010c08070309030c06 61
    0x141150b038200c000003c20aa003000d00c0a18142c1403540050029450b184800d035581d190b22200b614130a0f005604078001c1692244d960100044190b90051194a8920035483c4a03d100e406011030314a98446442c0742d900c2c0c0781c054110b00d04841d540c1d104014064035151000042c4103106c4402c200c552000c40a0f90f01b00e03c0058694a414404604840901c2a1a04ca0868085e46905020102e808040032040303240c2c0c4040720100c03445207124040200d4907080c22521000d041a18942d400003000a00564000d511800d980943d411103041121090800d0709031000d904140b00100b00d50800e205040020681e42c01c080c400810240407000e041384007500181c01e10f00260800c0700c08079611080518811002d210302c3c1c41c2d2082440c0b007145541001e04903141c5070701580a0103070405803200545503002da640e0707011400030031100b030701104204603040a2076118642100c40c8040407803440c0a05007801014081e1044940080d00c80348003984518000704d0150000c4a0142c003401500c88070800040c1c0c02e80b103 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 618406573 1250 618405323 618405349
    0xa080c040510020129010c08030a02040b030703050411040507020a021302070b041a01050a0506030a05070201060506040b1c11030c0a1e0c030f18140d0c080a020102150108030306041a 80
    0x800003581804424a00221081590385e4904030b0300361082508050360400711801710a0b411070005502c9540c0d41a0000c0a845a600b01031190f9101000340440e040e0190005401075128800240750341140c40140000c40380308660803401a03000569110150821306c05c1401c0c0c2007400040540b6005440d02c402070880420794086074151411199598560300b510740c0075001d007404952040800b03141800188a9010103000203004540d80c50102e66558004d5001d5001404040d203001d07101c45e95500100e049820241d102c1c50741c500300108921103009580300d00b03c0309895040e08030b400d60300d81d45d05d10407040d00f01070103000901c280c035002c00004d00c00600403400140d01580e0f03011075000c0c007441c0c006c103100900800b82c400c0c0140000800c10b0199210b04103000d90b620300c124010809005000540e00d107600303c1014142501c0c1040128180002090a250799030003038080f1055050035068042541d8400d00c0f80718010780081c00800c0380d03440c0030303005030500d80c0441d6170465140140c180010040c5280d03078 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 618407823 1250 618406573 618406577
    0x6052503080720060105061c0518120903030a0309030210050109060302270604020a020a08030109090b0f1312030617060106020106051c0b091507020d030b040c050a080c040510 77
    0x1c0e04001405500940c442e4141000f0a22280c00000c15040240d85510600501c0c0c45032a000c515143c0201c0c00c1050340c00e4900a140003402141000e1030b00c4641158201c410070010f0007405038101c840380a1404a032508140500114078100c002e48049005103844034044045010303a400a1000c40c1c002c0c01a01d000e800041030000c0c800d4036500c108584541c001d121064a0308000680b5402b611a00361420707030081042d200513030381c0c2d1030540080781000e004a100409005022002103045012a48080243c0e03204901402403620762515002c5c9600e030490b03035010038500250a0000048000c01904059641402e000c581c2a460341651815034801040c20310389580034400401150350309000340382c0105000e461501c8a27102c400264103004560080c003910b02e0f0110380104a10710800c0240381c10241c00a0070500741410b0594000351140c20140303102000a090404c42d41b01c44ca460b1258012540603030f200c044c5080403003601603c400c00e0007401c2050003403050000142c2501c0c1c408101c00c1c510040e03 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 618409073 1250 618407823 618407837
    0x306151206010e0a06080a110f0403080d0501050d020d030c0c051e011d0a09111902030301030b070207050907030e0106170705012309010507050102090409140d0f0906052503 76
    0x50780004103071040c0d002c0140c1c82104854410403207540c00c4a9119004285c0b0003020540107440031149030039111b0020014004880020008140500e01002d802d4842051405001590f641e50801810390600b07040a035101d409890b800e00000d0040071001c2807584142203200c2c0b25907903500011144000940e030304c01c90140340e101c1c0030607a69000c0c5050714031446603a42409540000400306200e9140c0d030094074095070795101c503041400001001d40d8030b06035003900761140314424104029129003003880300700c038000000c0011070005800441c03900142c3e00c014110762001e40d03802d68114094100042c90503c0c130355841d0340102d00344151540781d80d0000741440040c42e51918020004104d880d00f10030f2244985098180d800d0107074101c40440d0030380c002c2403a0041e07d030310703103428098020300ca0424640e51041c5480c034100b08101e80d441d05111a80c042c3c205481c1034401c0c101c2c0503640007a8000705a0006110344c1d4041c4011801000038240040b90075034400004484844d03042d02140c0b52413000c0c5d000c82c0700 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 618410323 1250 618409073 618409081
    0x18111c1e050f1f0b0303040f03030908070609060c020f1c06020301171f2003040506190506010c12020a08040305030306041508030f0319020a2007060207050603061512 73
    0x300700705032210003005a005000715655503000e0418584483e102d00403044d2140c01011a5603020026107014010481c1c01203911940c9142c0500000010b00c00d61100780200500050441d0041032001d00303d03241a2610040c0121640c00c01421483c40d100b8a42c1c01040700d045045070500580100c1d880c284075010040e1380f0350504001c100444007001c1540304aa004003000845440011690f8900d030100100c04514030680e42d0040c000c040c0020b42202e0600d03404400c01081c42030004905010341c074076080d07825104004014460558070f048540c01c0c0801c41e010031800020f03413000502051042184107450707010301a40c5d10b4281c0d0b40d200c1da0040c0d0311940040140041c40c9418854623064001c0c1c1003400741c1607460201029128003892842a1407800c0110004449024500b000302d201c0c4c5c2210340440d42c0b001e100d24081d01402d50601c0481120801803041c61005000084e100c0944000350004c2441a1410040080c5075100411054020301c03034442e0302c419001e0312009000741c542280742e06411031030 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 618411573 1250 618410323 618410333
    0xc0301060c080f07060b040f11121806090106050901060e090f040311030a030f05070903050703080d15080307050705011b0803090c060408070602160b12040203010e120d18111c1e 78
    0x80080e82340036400d1410041030507110503402100d0720841003c0000030155070b944032071040c110041c0d240c0078450048000300b00c6910010f42c0a04155035046501e81c180c2c0c0d0325a917049a204851042072500f20000c00c011540484056203166806413091034940c42c0d00e07a1440700d5071706640002c811940030035111080312240c8103c03801156888001860880c015030b103543c8915030748098511024104282c005503036091402e840d000319200c0c149030131000e203849a076401010303903030750180805230355034010410080307450361141d6944100c8140700c02c50004a00e1107512400d01d5540b0107003040d074440c862200d4040907038031040082e000404030000a0a04107250400107400c1c800c1c0600103110030b800160f030510149036048103640c20384120580040c1582c1d1580b0200c0d004140c10701c44d4040612402d0084610001000b000b031464924403d0309101c0c2c1c80e685020900f6005090384010300400c51001e40e000181081184440c20301e0084101860300101611910300b42e094480e90320002c603a4650b05030040c00 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 618412823 1250 618411573 618411581
    0xf0c06030207050709050c030426040e09010c020606010212180a030807020306090105092a0409110a12080d23162604110103060911031506030c0301060c080f07060b04 73
    0x102c0804401e00071b925144451620750f110042c00103040185a9260120312301103ca09483d07801e00300a100755841d900c900c50341409a03411140700100350b0815075409900c41c03020030180d0113200103800401c00c0c46070048500b24550000240c000041d0f1414a40000c00c5c2d480348070342001103000310b01890741d40c1003d0061600304a030040c04407896030304240c11300c200f100740014010010245d9a040e1111880d16440240070342103029140c0364001d00380301c001c105108501c0b000c800d030190308584841e0101c2c2da5505c4031001c0c901118010345030500c18080c40014402a8000d0b03c4681c440c8481403030b1044054107803400d00b6100b074406020100c1807142520301142c21616a411003862900b8084003509081b51000c03000390010001001c004c0d42005002e880d034001e41201c000b0704a000d000340f14036085507445001360f4100f2210070001940c00c1d0403903100c1d428000c040320b001d0100c40c0f2800d40b950382400419941d6985091013100e040b20100b06170b0314034420303607406400d02901c140e40c089249411481004266 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 618414073 1250 618412823 618412829
    0x4060f0303020c031911060714100e0d021002180d0f02100509061801110304080f0706082a071a06090109051603151208030a060f050a030f0f0c060302070507 69
    0x10b6408400418800c0305c0c0c003205800700300e521444802e043e64402011801a0180000017031111142c042c9160074090089611a041142d50b01c0c10451040302e198255680d07103401500030056041844107000100f055001400458200f80c484c180e6120381d00045a109000740c40140c0340744042c0701c02c030002c42c40c1c02030030036045444030b10344181420704040c0028003610400c2110320b000c0804003800b08450b402425600319461081c4c05403501d45545003082500c403000c01081d000140104000420158000c04056004045802e005c54507804140e450307001c1404110b001c80000c0e60b062014000181000c081c410500604010740c003801c0c20700c02c060ac0003c0d80c040c1c100c00c440c2800d01080000c180c200d14075007480d00f0034078500840c1300c40f108080311124101c540c0184054401c020305135007d1007417090041d4024082e03c503040040a50301c0c00c003070a2040b940c3c040c0c3c03a88000c0385034040010546850610320719038060503031b02140c4c2601e41d803100740c4a08a60720210210380c011030f00c40f0a0081c00d20000000b = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 618415323 1250 618414073 618414079
    0x18081c050705071208070905090a0c080c0c0a0f030203041e1814070c02060918041401020a090b090315010f050a081c030518010204230f0a030b1504060f0303020c 71
    0x1c005042d56210960b15403599144c040201c000001500c00f40300f10800401030030060a991081d040171102d1030064a4821202800b1900348000f00b00c082000d075080796507224148014040828850703980030b0029880020540452009000104500e84802c041c43d400c3e510b424a071102c200d240a46074012110510f01040d225481c100103500700c3c48080090383c0d0301c181d0a10702ba01074422180300003078440c040c50400541142801226004c510641160b50f40035502544402c156104440c01b49405c0c1d00c1441941d400050619204100454200f40034101441c0c004041d99900c90556400d80d8882030241d22682156001d80d008014030305010340708074050b100d010003601021050500303000c0b9200d840c142e10341c100b40d40c40d0300145e60310090000741348440341040000c1d0355981d516111007104a42c1180d94085507000310740010034a26140c0307094880c0e80005070901c402140303181c84e5070111850060a001100d491780d84000203555852141e04003410f544510071344801c2c11070400030718040c006611540 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 618416573 1250 618415323 618415327
    0x50901080303070f05030a0e0a050102030714031003060506010e030318120706080606030403050c0607080604110301060e010e0604080f0a140304050105030c0f13180b0301021c18081c050705 83
    0x54900c0d801140181300c05194200580e807522001c0350349000700803c90780300c0141e00510003020200722040d0003e40c0140500e9460742489500e1080200e0765100950350200a5405020100000b82194111642c4880b050401d00030464035400824295031001e80144001d0030312034014606403800d0060680c051101c103000f046047e04104000d40f10b28030103410140700f0040800010304242c0314a00b182d00407441c02e01524054141010050084001035031524400e9040102c47c1c1403502d00201542d0413a2030580d940752004031324000568450200010458010b03a0070400030038548407c2014401c42c0ca040f0005014010003800c2105004003041003580c1142c10421017000103aa204050f250021b14400740b0507032368803c40c041c4810b58070034135410502c9003010f00740008404040c0390007002610036065051098010040826080748103110004100c0c800c060301c1038804050303d500110342c44a500041c01a4084c0580b502d41003900701082400341c1640100100400c030491380921900b140c80350420324 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 618417823 1250 618416573 618416581
    0x10c17130209060a08010c050a0206130308150a0e010b0c0f061506030a150f0504241e0803161b0e0703052214011104030f020d051015050901080303 65
    0x100c4945030920180c8114218804280c1507940c491001c8000c0921704020405080300e08005005c1c0e4003d5012080175004160006d0a02020a168618404e6040d66040800e55801c0701040d045010424480e03081464050080b8140c200c50300007074064041a01c1c000d07184e4811805252401e15000d00600d400d40241051101640701103d231040601000c41e101920b0b55500030002008010030751100c4e084054080c00015031a103151009810b50380d05480a125200c24180c408924407104064400140000d01c410486000d103981244903400c0d0350301c4400f6000c0d9132035680e01d103140c22100c0c03ca170050340140ca070303001000000000c80c1500e0b030040400040d00c1c3d15001c2c0c1c200700d40d140181050181500c0301c0c00a07402800d030704941c100560814464112411003818a400c03c840d928040c9482507203029941031060808806440c00c8a5010140c141881455401d11050480000003101c0610900480d4061755066004007820405105032100d01c1902d0b1100f0440003000690045805800400c184 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 618419073 1250 618417823 618417841
    0xf0d030e07050d050a1a330103020a0e04051608010510020d0509010c02030f0a0b070e03280b28050705160201200a062a21060305010c17 60
    0x4480040350402c91100c40e9041885c01d2281204004200326200000304250803e4040380d00c0c01184d040200c504107440101c0400940e03503001e41c1032070301c0c070000e107964428235171007500140540c0b20700e407501052910310140441c044d29400c0c0c4503c0100b40d94590303041c4030280e00028190040c03004560260501c490054047e4841103090340d8102003200025070810580d0154241d0910664080c041350106402c1c2d4682c65101c8040d140201c90014071600031511940c0700d100d001c0b450010040c00707441000c0302c0394a0b240030350900c1c46031200c1c5540f216052001040a2204d05846414421600c0d100d8036400d07610540780c0d030303900c800420240c2c0c82d105c2407202c207a50007030070b8810039040d108056080d0460b9000503548600c440d20008460b40d190301d10883c2d02000825050b07901407190100b480380b003003c4543e09414945198640c4460003007080c003050550f20441c0f10030703804950138000445590050543e80c0c240e408a407c20380703d41e91248880c0c0ca003141d0282d4035003d5414000134402d000c0c2800e00e11 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 618420323 1250 618419073 618419083
    0xc0111120a1e18080c030a02010c020c030d0c14070b0703030c05030705070f170412020111150c1e270405240f03060a05100602060603120a0e120f0d030e 67
    0xc90b5951a50380d1003902c1480800444400ca0710f401c245503984695607540c0407580c0394484501a0019420250207070509400090400801d6400902404800021420884d10042c910030182c1c2d001d4845001d00c0414403081c44120060500d0b0351a1b55500c481c182809010344050103684001c005080040110050388031040d198542c0d40500502220355907400c18501401061012940400e400600024904000001807031110306c01c1c0c0382d01d00341d1000d650349242c550a000c0c12402c1485030690000340040300803001000301c10503098010492201e041c1d041902904500506000070b412801051501c0326000009062300401f10341c00c1c0100c2c908440b030b5003030f80402e0108000c0f006421000c148000d54075150f80320a0b42300068100c070305526106943c90090182078801c40c514003100e02004c116a40b000c260148542e101800070038180d2881020070005034010301022040001400030780546039103000305052690688002003560403d080c02103405c20a03118001f20a06242601000c0c5072070340424 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 618421573 1250 618420323 618420371
    0x9120a170906041703090d050304080c0d02070504060e04150203060109150531150903060f0504060b0306090312131a0405061003170f12010906080601060807080a090201050c0111120a 80
    0xa4115103035100d500e403070bc88a0003011401d1429019298001d017440c0c3c0d00248040803600c04913400e20582e5070b1203100b0684520195000b83c036070080d49070154648031f2a83c00a64010f4018074080084a9031040c000c000c4901c4d0a03a10300c0014000610108820245443c40f010031488803883d080f2000f60768004100600c041c0b0450f40b0242074451008a150b0040041c9c50055801500a22912489203151001040202d07011601d041c6071030b0007510107040c00141d4601c6201c02034019441c100b0061006940580700400701c0001c8400041c0c000005001c3d140c100341e00440a80d40b243c41c1c0d04292800342d050580003050340300d10089040041010504480e5503e4072801a00403650f5200c00c08480030207039109603c507407281c0098081c00051124a103070320400c1200c03088001e660490b6260b040465030b01d942075074a60300007210180840c4841000c0e07400480c0300c9105052032494440c1181c1105c5c25a00d0003034400007041130101d035018281900c0058540d11034001c00c010080d0b260107020340400280c01070 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 618422823 1250 618421573 618421577
    0x130c020c0f010915050304060c030204080307151d1b1909020318070303021b0303040b1c0603142406010225030204140601030b010809120a170906041703090d 69
    0x100d010040d64003903201d110141c4042546a404200a40b138042d1441d070003664100c413507a141011081001d4860f10a640607228900055031a002140d1900b40c5500040b222528003143e84000c0301001142040351441d06a40c18409080520448038a05095030380d00d446d8103000e0611180b01a044104c0b0704d20388810707103003071030380060316520b50707981c80782e4207013034144000e07250713210b2148017006041d00002c804a40c9403000d440b0b491a6902c807014107480303024511a100301c1c0c0c0b500307100880b00402d001c500300b1104030341840d00188850756500c85008000400107810b5190300140c2d00c0341c1d15081c0600e480700821a4080e4203030010309015000079620039051304907410781c8030b542c0400e2803607500c410b0b6244020b40d0018018480c142c05500354400c00e98041d520740340800e01c1c040441c1c8855010b00c0c56107201d000c40002420382c40c1d0078071030110921f512100070320007085030030310b83e50401c002010421401280c103000140380900d82454001000c2800319101e0004600500070407480c0080003d01c13207942500c034 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 618424073 1250 618422823 618422839
    0x10611070609060f181d010b0f1605010216031809090b040201110717011a01020a02030a060c0c060203091c02061026061e070c0213020304020f060c0c130c020c 70
    0x810300444843d031640034105c82c80b5045580018148100804424180e011003640584690342c4007240c4c200d5226440c802081000c050017840c1e06118001e03042e0800600590003d450301c103000031a07900c3c000340d40c1070440114013065051080c03034108080900140415036010414110551240c8804a200904c0281000702c000350300c040442090201600904404041c0541d00d10b810700058040e0034403011003014405600c0c1a801307190f200094031000141c01a0180c02d01c1155a10f8600282030341c0000b503002e1059000b10034000078024401503101d104c5581c0540001016803528000c410342e4500b4110031903100005016500d118200300108440c1a0303840110303854282c10860000c1c0105189104032800781070108690f17040c0581e201851650304c81c40306401d035034985a065404c0002c489019401c100054800040c000c0c07540e0040d82c02c20f00040410a9980b50400010300c0c96100030903419a94208038a0002503080c07034142002c0700d90101409000c8010700d10760081d40c40010308a01d5201d9561 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 618425323 1250 618424073 618424097
    0x30c0b070c050a03080307020d08060d1202010b0a06030e0c0a03030818120a0309031e0507140f12040801050604090f0312110c15010b04030b0c030c0d050f01061107060906 75
    0x3401c82001014082c20f0100060b44d24140321109400841d20007000d802008031400f01c9a00c00d03507116110310030007032600d2450400758481829600801c40150259036958100c00103580d03c0c02d15080060015a5010400e95951700c1c006090813940041c00d800794521980c103000190300300040a43c40b0008482c259002e01c0904903851a02140c201090000c82001448428080e0315030041d030003481c041c0c2c54402980391980700048048070310350070842c0011024403501c00011a20840c600d00540d1210403a101042c280b411142070103d18842d404004200240400070440c00b80145a40150102c0c1d04000c0c0c004107807038440d0710907420f580c01401c1000c00c4034210504036080d4088800c07500b03035a600580f40d07480e0b01840e555441c20000080c14040403100002406020030003124280c4ea8007202d000305540b1003100e4114650006080c1d0100070505110030301c000f500c50f02c50140b04803120050441c0a525020000d0b15000200b40030106940018805004082d0441c0401044642c0f5140c50440a96 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 618426573 1250 618425323 618425333
    0xd0c030203120a050a0509060115180506030a091b05010e040504052407090e100501080c0c010c02013e0d0605090405010c080601110a020f04060306021308070906030c0b07 75
    0x200c1c00b829425521100801c0c80352000c116441075100c0c641c10801000076481381103100e0b540d8002489800c05010030342e50700d10901d44c0706030381c2100028440340d04d00d0340b00c0303403a100018015003049401d078000f6940c4030b14240074007500002c40e12035107040b55000c22886041100003805200c406202c2c80c0556220000b29041200802408060710080c46603080c1e050b0600000d400d05000581d2003100194130300d00041489101359480c18041d280c00c40c0c080c004540b602c0b006460142006081d0000b2a40074005c400c012107003805090350407400c0354000648807103c841c030086004101403400300a680e0303280c3c004290110420305d2015031040c110850351074080b211806400f80c40d0542080c1c1e0883d05940601c010070205402c2088000000c0d204d14120790340d41c40044a003035444407820506540505001e80c05418101548170340d4980140000c0390503601d94a560083c2d07403064403590401c0460030810082c451081c0011805030454040a1002c02d184d51a0300200284600400780006000111081004 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 618427823 1250 618426573 618426577
    0x30b1c121e020106290306120703021509100806130f0b062d12010b211302010e01020f0c090606070204061206060e071704060f06170f030406020d0c030203 68
    0x61200300e140c101c000018031000740a0700151040c3c0c0d0b85407607102c102ca420314034130070300107681c98039002040c1e411540c0342410065a036a51488140c03850084078004005030f10f607886580c544805101c030090341ca80c0e0354801d002c41401e10a40345c07010020700506000315030b030307601e11b41c41e041ca13880c4503003c1202004414450001e1180380b140560103000020304440e100003202e036400580e401c0c01c054032580c0c108490001c01a100b411748100d400d101080050001044010240c401d820b0a003170003405035144005038100c0e03044180c0e1f0b0303107c1a080d50f4040c0f008640c0e02c031601440041080c406031030400e0307141d00341d04d17560848550210b1081080500042d180c0c0c552000b590a217580041c424446142d64200070002c14440c0102540c01c81c0c10460040340d08004146000d026080c5540c0302d01002d8444a401c040444000d081100c0c2c141d180da034941c1c1c803240c880c00348801809003414001003101c0d03110807251030203400e0349254065130400e01040201d1500841d4510500d8041c0c144010380303884505e03040b4218 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 618429073 1250 618427823 618427847
    0x221060f0306011d0a02030121050c1c061a010206070e01050d0603060c02060a14130312060e07030f05011a0307020a060e06010302120102070c050103020c1e0d030b1c12 74
    0x103200d10381c0002246080e08200203140c20144c0301100240d11407460b854241d1000340188050305204161064000746080c0b810040d890044050741c0c030030502440003a0010b18460b420b0303001c5030b0b01d0f100200b043c86143d01c43c034550507840780042c0000f04500300000c5c0d03c52000404160900100c01905551a400349080300d2500ba00d4101c2000282e40b0780ca0898001c051a0183d4801407040c100050441c0469100d21290064021000c1540d03a03902d100d040001001010110100142c11a00401e0070142d406044050002c5d425103903003a2404550007001c440d2107211040e00c0d04c0c1000c004220100c95036040d00360041c1000e07003199883c0d454200036883c0602c3302400601451030b00d20403400c070880204241d41620702c2201e1701410712020b407803868242d002c1e840e0064071480c50030108100641c002d500500c03800d041e92082c0d5440403c4224400a10181c1081960541c0c200c00d0703c0b0b140356a0b240c85010fa104c01c0464000c50b400c0ca110b03c91302480034011200804c100d404551a5060b00e00899001c065 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 618430323 1250 618429073 618429079
    0x12020105100509101d04140d050d0209280e06010e060d0906110c06072c0f010201110705010906060b1c0e1501030305074d030d0917010221060f 63
    0x1c00301010300400e80c0240121070030b845045404800c107d074140041019901005c49940c3d0301d0501c00b45162031002540030221459105c6805060042000095003010b885070352000c500400d1a0f16004000005070b80050680e4100020b08440c1d0071103584003004d0302c48600084500050204491408400404444444d1900840c01140f00341b43c1c0d440029101b03100e04299076075010808111603500745241c0009880590031a0044d004060130700748401a611a40e50510012858440c81d41042400d58008001074420365116440030b01841000c1c0101c40061845041c0107150540c4500c0c030304220911080d60601c0b00c0d4a5204860345102c0409c54481070a50500c04558296900d140260155122450031106a07418880d04420049005005a040c641d03010144c11803000c0000151194000f40d4546a050f04131052071185607201001680300070f2203180c0b50800c41078100001902040c0381c030181c03025683c1c0104040d04215080074100c0390350841203403450500c0e440f241d0000c0c0c4d02d144d0707035844560 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 618431573 1250 618430323 618430349
    0x50c070902030c070c1211040c0c0813060e0a062f060f091e060c1b0f031312050c0111010906110318070807030b0415050709031202010510050910 64
    0x31004a4030001040c0d00d501c01c910700e414250340c4104510580051b802c1c00f4140b460340c400f02503980c1c105a0401d00e20038115203001607000d01e4503528003007150040c2d8070700c81d0341d030f880d00300107010550f040030944004000495103918078514000c4001d02000ca003650710782c02c2c81d80030800c032100d0358080804c2030720081e500030a0340c9103403500d1444014420400c5a441c265407280441d500a220022981c20b41030708140c83c042e00c00d0341d82d02840c1110603442286401101e600b03018108280a009005400d03c03210790310061036541e10180c1c07140708003400a41001c21101002d05846000403000549540d0041d0282400a0702000801c0310600500c2203c4010703009d0781c2404102d01c0c5005012009500c00c000e910901c1400e02c09130400c0564030305507030003481040d0307000c0001030001c60004485a40d00ca80700e11001d079042ca1512640c0000e566083e82c5401c04140c10740814005c0011807000300020229502c001c020610340b100001880101d103200303c901544040c000315440c44603640c3e18601030601156069 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 618432823 1250 618431573 618431581
    0xc07060806130b0f012102070b04030f1110090c080a0501050406060f031128030f022d040b0a050307030b040b060607080a0302210103030201050403080702061006050c07090203 77
    0x24001031012200c00c1d01c207000c00402024020194403400c200000e0180c420710509011200560380180c449448000d03644030344064250508050008080e07080c0b0034000092541001c0c5000f070300d032402c20031105040c00580d11400e001d81c2400a850b00070100103e501240c44003103401c1040f030303021164012808070300421000740c0601c0015005140a0ad114004c100281c9554076001e2607203a00600004203001c03040c44d50391045151a40c080c656002c00a00b454811f0b000b240c50805d10041294400c44aa018101c6160b09601c3d000503821003d40e43e07140031095090300702d00b20103e101070000c0c125110791354500c041c8140d501c940862002422001d4112500d585c1c890a150130011700468003107030130168903000209582003002c26158140c0c0c2c402501803c0a032489400d601039040842c04401803160210b202c206c41000488242c0210b0098000103031a0a06040c000d15813407004000e80f0541d4008406e00a11103079035034aa400700c0381c040c40c3c00f5854901e142e040d182494900d0f441800d01f640088140 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 618434073 1250 618432823 618432827
    0x100b19030b100b0a090501120b04020307080103030e01020c101b0605150a21080c0f15180a0506130501060503010e160807050a09020f0702040f0f151a0a050c0706 71
    0x90295282c4180b9410296548040002500c280000c100014080b44810466075004808845040719074080100359128510041030407600215600d0f00095540c00040003455040728105500300b000388090a003001036000130441001030b06140c00d042000c203401c910108a030150580204950016080c842801c4c2140c443c4410a0310000341f0784100925003000404c44440c0f1000300b49080940242461103403591100e0010342c1208500c2c1d01c15000c1c99074020a80d10052081040014001100324801d04080d00b945840381084080a9040e82c02200104082000010526030101c0c9207100b02c02d440f40103240203405003031958000da425600b040c07158090403201080c0325120401340610340103103d54480b181a6a0909445819045241140248189102234000b0010413021280036850721410b507010030105d5036000c06111010380e455031003103044c3c84a4060120704508131094003076080d0809a03948030911100000c84081040081d00b4003450f8000c2e41520b039502000400d551000350740c1c000c0 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 618435323 1250 618434073 618434093
    0x4021815010f0908070e09031b0a0b1f0306050a09170c0d020d08040204090602040302090f01090b04020406021b030106120537110f220c05090102100b1903 68
    0x549011485008040c10190302c90f045000450342100024602203281000401a03190054030540003404100300030031030b60920fa00c800e150324209800402c0307810b01c1428007001340c48002d0440d48241c0c5604691030381700560116440c2c1984e401810008032502c0c2c4e0303a900d1004014400c80106492030f220707504c81014002d14040c180b542c01800a5030b200c141410012030321442c0100b5060302050945010502505241c0d00000040b481104010710341703a240d8002400d0f4170021900900c0c600b04100c0184102a1180140000698180d03400c1d07003041d0400d0000f9494064a01c0c0f400d44107001d5051510203a50250844001071000d041d80f0001c840d05820040e403141c1640d4903210060040c0c0d40d45488880e01842000e580942c6101e16100d681c14650303501d400b0006900c000f40e413040000203542106c2d642c130819050399958644080044040781c03000da80c1507402145031603040c00011f0140b170b02303d030341c011031020280fa588107000541c4807003c4000075070108400510008100300c2c1c020105c10407483e014 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 618436573 1250 618435323 618435361
    0x8010204030b070806090c0f130e160521060f0d0f0501180c06030504030e03010c0302070b0606030103030903021c0602030c040e1b04140607050d0504031e0b0708040218 74
    0x2e01036103a903032450020384082e03c041d202d075a04907002d200091004c1070840054442042c6c000c032042e02d0441a40c08502c410121170300719030315044003c0184190340030090200c8804001ca81415070502003031080440443e0750f8214000c0f03000c880800050b0701d0ba43c1d9007840310740c1d0350b4004040138944403040c10489070703140108600321829841d161a13440a4800d49201255180e1300048800300b01e420000120090b10004d40118180f1101d1400c18429503428081d01010308030f0380c7d40040e00c403486030802180c0100c0260207203010301030810040c800319038403000c1131040e40e8058034801f0f01401101d24030b07500c0b4149900080c00391031000c418084010f414600400c120f03007400d00055140d80700d8038442c0500c040f0314601003600c9142080308010300c030b80d040480319440744014007050405529445a0b4288203086412400150300000d0900802071058500c6240008078000000c0110860381c503020305a00280410040c088594002030844d41e60860510103280c10550075241410302102200018074448 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 618437823 1250 618436573 618436583
    0xe010e0306040f030914030c040b040b1816091a0f070615090c03140f090a05070b040611061302060d06031506030c050609062203050607210614040c12060801020403 72
    0x100c0c0029030740d86c100b0304024000c1006028101807226102004010319541120a03041303038861010085565070040810794200806042000714640a484010149500380405042c400003010500800515400b00301074000402c040c150307280e60010f1790445034014407000a01407800c10120500301680310f0310307141c1241d0942100748040e1080301816000d8409a40f4a5603903040c04200080d00e00e100f15200c5908203e0510550351000000d485803810140d50f50010801340c0c500203030030030501e9404640e00c145210700b500a0001d038180040014104092014080c0c81038102103000d401d03042c5954030030b40c025540042d022a0345600d00304100003034000c902c019240c02045610008203401c1800455000002c01070405190540401c071001110800303c40d0b03074190020900c00440010420040c00d030140b40d068545920b02c09100070b00c103c1c02160081400241c0f0708044c0204800390040304100d070152002c581c00300e14040382078070490301135045c103120b034001e203041c1180024070032010b60080c07056038022 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 618439073 1250 618437823 618437837
    0x3020f2a010c0b06041104090f0203190506010c0303090c09062414091903050102030c0318070f09020901021c091a040e01180f060e18060103050303070e010e0306040f03 74
    0xc0001034504890541c0050300c0b40b90001c00113081854142c3c45000407012a80c02a400d00791541d00090031191502d50600c0000e500005005000c1141102440c0c801c001e01410301052610a00080c205041024010b00b03054403482000c00700a42d02c40e461020b0010200108412940c548050f031001c1c09403000640115240768550a80921420070007a0039031074108030500d800381c10003e0003034000c030400c184104000c8040300400015001e00086000f9030f074100d070307a5840b0300b8a082c08402c800030f114035100d10390b403045030104014800c0c1c41040341280c8c084107005890301c5034200180d0828050b80d45101e4001d0700c1000c2030f5006600102200c050300c800c10119400c1c001300c05003048007441940203c9100d482d049004211501c000d640c4081c01000d01140455410700c01d04200c01540d41301d4206200340c1d00c003c41044405000d90489440803581040140000d500d55100c65880348800341002d8104489003039200001d0340201c00d04840c032100507049440d149018180301e8250200550308500140700 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 618440323 1250 618439073 618439153
    0x50918060f1f210606030206042405120c16020d050d0e03010216020d030203130306092109030201140c030c0c040e0f1b0f0d050106030212030a080103020d03020f 71
    0x5008410070944400c02e4040c0820120501150b41c43e44804200b2910651103c4000c401a110140908006d14000c0304020344840300d060201c110883e503507140e40c204a001c3c4005000382941101e41500080304001c055911662401a086442d00e4041c020790000301d0380d419031040004c0028403058071400c030b669445484c0111400c0600382d10507641030080d000e8a102d18800549070028180d50454400d00469207841d4a03000c0c0c0b0703138484046500c1964056516407100313045c4101c1000e40d4801903c1d0760302c0c1c950003080400014050030102e01020b4100090102550080e2000030211910803003044102c907118181d401c000c60b651401500c0c074078083c908000400c1040d000000e440d0080135095005450420340d081c0e030f00f140000c000003080e9405101320b04155000d8550100c88100319029100110b941403d40c014400c40800e148480c40c0c0301d44c41081528020342d40b003030b00681540e504a40c0307440d07140c80e9130908914115040708504060700849034144104142410500d000d1031041510124481d4 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 618441573 1250 618440323 618440371
    0x20f060a082703040506031e0114011202030402180c160501200c060f070207030c060e03060c04150c14010216031b230709050a0c1b030504050918060f 66
    0x2d0a82c0001610340c001d200902035490300d0006540e100a032901341d6003407010181c0d00d8896890082e4803500380d4034003041c1e0700c1c2c8035541c1c0304000407a105800da00640c0385007040e901003140d0741c0701003040ca140500d42c1401b040c01569030404480c400d01245584c50015000d03410014002d2881d003410303166801014240883c0702d08250255280c13850254080c1160740c0d5000001040060014481421130090740da01100180c0f03000c032100b02030441550f0b080d200da0b12030010b06103405d001416210242000303000800001c0c036960348040311640b0718a4480b0000c07500d450b10802c05403d042108169500101d0784d042a45c6640e80f004078981d0090361401c8860602110703518603290700c48000345c06400b05c6060b026540708984400c040540503034040750a51540c0d100c00100f103d80a030b03003280b40140c4998a1a07401c1d6070084c1e00b0745c00780b102000450341304816a5806800c0b840382d8450355020b251514005841e80700d80e2940e05801085c108240ca0042c43c00091401900c61300300e601000580000110190a83c = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 618442823 1250 618441573 618441631
    0xb04151409090714090703090c0b0c15042001051c0902030607080702030a080c0d0603060507020111040b09040507180801291e03070308040806060301060501180909020f060a08 77
    0x2903041352000c0a900d90708010b00403180d000422107414540c407011191f001407540c0c40c0078130041401a034896114403880407c84d05119007046039030040c024010074000425030040c07440303007490300c142c200c0094a180341d00103031942e015038440c0a0003807201c00416021005c054000080300c0e40300310142c0d000c1f03a41e568015107540c2c40076074042006134002d10204441c640120001c42e000240c1d104094100b8075006055010354039a42c1045a68645802c1480b00c0e06d502401a6400c0c0c24020381003d0815007840c502d405a4054007555901c00ca899401040b4114040e01e0300034405445025400710392901c0b05d06280c06011280b150110980000440002100581e41c00c80003c600c000c0280400d5540044501184941e008000d50f0601a4403000000112000c0081006107000f001074141403400c0d9042508452880d8000f505024031840605240d092601e951829a601d900002070307404042d0000c1038007028070752800d87c1c014030000740c1c0a0850b0f402240c02032061303401c0e00c5414902e42211a504140e1 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 618444073 1250 618442823 618442829
    0x3060f0308040e040804080105040302103c0207020d060606091418090c100e09010603050906070305040501020d0c05030a0506030c030a2a06080a06080c130b041514090907 75
    0x4009101c107200810f08442d22a81080c01031407660304050b1a40d102c242120f80940b404c50141c1c0c030401e4511081d0301180200c1041c5160000c01c1c078444c950036907503d84040c504040b000d4403a0200340c50352401100c1903054644458014141104121443ca0400c00401180c019140401e20000c000240820707003120b03491000f0005860040c031060b101c4101e00d1100d501030000b1485024031071001820f52143c919208070320f40e240e41c070006500d103c0d900f40203018a06030031003000c160500c4200281c4000000301c02d44c02c100c1c60b18002903560744500700140240107001c085108581461030a00d0036550001c080c40c0514940c0c071041045450b0b0104241c3c1e1802e10f00006034042c0c00481c2100c01280b5820388100c0d0131030a2206044100b150082e40700c008005642100c400706481c1d00034010480001d1060002074140d41e0001c2524903440000142c860690345036600d221794460071180d072640c40315040954450f050003001e07454161655000c5022500000713595005544450000780c202c00d0000d022421 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 618445323 1250 618444073 618444083
    0x60405061b120f120a051302101202040303030203420a0f060f141810020f0106080c01030e0109080d02070816050c0a0e060a06031505040e07030303060f03 68
    0x40c12a0001007500c0328031a4480d01c8985020720500a040e6004420040140d02c4411052581c1c4210425219070004000742c150b642a030700d00b00420448500c042c1c00342e0105a011200c0c008942d1302400c080342d02d02000c0707024648690001c1000000c064042e0040d42c0038601119010350841322400082d102895408480c0c3c4e0b444000351404051898854031800039030030003411440791540c540b5410300240410740d00c000000f400000b029010154454007107408c021224107928541403040c19423081ca529018400c40c460074401a50600c07290080107445c1c81a80d401000784034569a848500d91100c8030b0402c0c0e1408203040600d21b542e128418415001b100b5848020582440c0f021924040207400c89001114645400c0003110581451070111900191144000704901d003050300c00c1c001c00e00c025611840030800000c0900641c1c3d40c504900b2000e03a04980303000560740b24541c01c040c2710b030610703548226045403038204000020003002c60a102075070700a860611000f41d8920707089040c12170314400544 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 618446573 1250 618445323 618445327
    0x3190e04060b12010b03070e0d050c19150e0d050f0105060306060a2909090a051e0408070b0406020d140108120f030115091505070b060a06021209120601060c06060506040506 76
    0x8403142e002c09143c1000e117614142c1d510303c0e89003009c00c040c3c2882030380540300f41d405401c80303080c507152402c4150720350540000174045c40c0c2c1c949038801081e2425243c0c1c441c2809018281e40d0300c01e848001d0030341445504842101c030f80103044581c040c02001c0944409001340282c1c0300066050400104040c1161054130901100c03402c0c440449200001d03056603140210010020b072030880d07480300c00c0d42e802070003d01d00007d9103007841842c1c0c0c25008407a040c250741c48040c801c20400800d007400b0554060760b4104503c0404d540c0c4520340300c0001c1c456811540300a0b880d2001c841d80c00d01103115098181c40884080705d01c48110b41414000e24002c541000454200800c01882081910039640410910600b0100c42007070f150025030a00e0324182d034586001902c00300c1d00c00c00707100781a082c95402030000e48103000140c0c01c00100a48403606446852180f590008072a08a40c42d43c001d8a424400040306903505945c403000001d020092551041c1c40e0b9609182000c21039281000c12602282c2d4021300180c = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 618447823 1250 618446573 618446579
    0xf050603061303182607060306180f0e0f010f0b09010806181c0509130e03040b21070305040b0108010e0c010c260408100603080f0c03190e04060b1201 66
    0x40d4811080400c4208441c055400005c65485401e85d100b6883d0202d54032445c0035108030081c514180c85503215808060802e103081040c404854800e200080b602d02d00400c44d8604d40c1420000fa1031a0000c2c00907510810060340000c16040d8450f4000250864085c00b0b00202c0c20104401c1102c280121400c85d00040003183e031440320b20b40c00d003440b0305000c0b0944400e040c0310301200c0089070b0302d26000800b0400004800ba1301d450905122070255103810801c0145a05404000c2d540f806140038510044000180d00e00c0310912148520200f80303103840c0c03007480321700e080b09008002c2c00c0143d4044031040038190011a0742c0340103000f5424029400c80042c10550304c0c003001125210703540300d0705440b42c21150404c4240501185440c0162a047c186040c1ea01e510344945c0b540760001c0301c0546542e0610f40b080501c001030358030085030b102d0a15080c0d6552203040d0760a03542c0c25841030548501043e0241c9020f40b0304250000c1c03c2501403802190108840c958420805502c0c1c8a407440c42c0c0b0511146038018 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 618449073 1250 618447823 618447827
    0x204080c042309120d1b0c03021b010c02090a060f12031b03111b0a06050a020307020607060204050d03110706080105101101060803040b0418020c1b041e0f050603061303 74
    0x901c0c3d101d10010100c81d10841c2e80d40300d24100350b002800c010201c9407200f501003000e041d180c0001d601d02d01145401d9500b000d4a41b030085d00c0c0d22180810040e2284101c801c1440c6a00c2111031000340d43d0000c00441c5141412001c505c0104080d1107814142c181011001540403210b40c941d0300c500c0d40507128240c030581141c07500c40400c5200c041c118207110000154040380442000782c8002ca05d5081202c0201003c01020010300402c158040c1042020400070b2903a030382d50201c1510f091740d5040e1200384d07c0b03550170b18102c0040d005a8010940080b1440010f100303141e48041000c0782c00d00712406070360035141c907810100c0e210a07003401040d81102e483c07001110701c0c42c0320703d18180b1041c0b4035000006546031a010b0040c1954030a0b40059080340b00414140090200c802c080364602d20b159108520b001221a60191124000c01c8407a84491500408803080d0f02ca907080b0b005007030188400381481c3c2c0c20313200b0300100030f110825400e00c08a28040008142c2c1c240014651b0007030840b240d140b0740a5000f9501 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 618450323 1250 618449073 618449141
    0xa18051b04021c0f0e03040f120819200c01090303050c01060924090c0e0108180d09030b070903110d08040b03040b31060513150204080c04 61
    0x45a001a401c21240000e0f6041a900030b108140d00900404c60f0024400110159510b4403800030658000b00b01c108030058403424040704072400042c099804003550305002d44e4070b00601e2039060000406482c2c2c088a03d900c00b050100c81c5002d4440c648810250015a541d220234044459000c600310000c1070001c47d008002600203c04070000100d49a0b407600144c10035945048002c0122028201c1c041c1480d02042c813180002e800e000d4010403008018820007020b059801c139400c2d040c403241001156642d19940452000c8061030b0045420404460000078518102840706541e41c1c00b10f200442e010512568483e011642c005544107030003206c0e002002546000d01c10126040001004005000103480d000385100e2405080c10141c9881c0c440d1309426005180c68140c1c4c2903002030102e124022601214440b0701d41e03040f02c0b000500c1d41d100551182403887c4003030081c08085002800c07008150a0760010b101355034650042d11810f405210620054a4650001c1c0644400f0669002055054045 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 618451573 1250 618450323 618450373
    0x2130606050f0d0207141f021801030e03130f030c06361e0306060803030f0a0b0d3201060b07110102160807080c0114091e03070b030a1805 61
    0x146498425a194000390103a188201891f8201030300c0050350f200c10360369038800340d4071f96001549400b51482008407890b54109581c5c0c14599540300507401c4090070429101980074118801594030345a40035a01300e40b1240c801101c00d0b00042d0008038080d4444e14090600300c0c3d681c029400a10520030800d000c1981018002c0013075100307200001210b51030340d808004100d02c03558600e00c82d90b0642c280035051320201c0d081b8207403581c420001c0c8443c2d11241c4032000e61000450800040e003030758500000f00014991140a0000300b40600d80046c0c0b060035800c0d41100e2400780d030080e08004060103045090301e120744a0070016046c144a0f0002180d2014a0070a03002c1051068601c9445c04000c882800300c240c0d00413070346950000d0020700040c00c0401100240880900700011164000c03440940d041c440c0485141c00b8000804840c2c0112400c55281903035010014284c4000d1600c4000c125000c0d00100c503414015424840c0898017196401e285000150300507002e0005201c504003002d0511009803 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 618452823 1250 618451573 618451597
    0x2070b0f18010c030b13050103030f2f0303060a051002150c12090d030e03040f05061c020f0702040b0d0b0c0a09050d12020d0327050c040e0a02130606050f 68
    0x11407805441c0200b84a4086021140d4030000745102e40b0105202800c0344654404485910b002d0050000c00e40022242695604501e032a035022600c1c1c1324600c034000c04c00c400040702104d226140951211000c0055440b0300d20644240010a40d500200005000c1424011000d03030011080a050303040c0202005070720100f1410824a40560b40a0144500c0c3c2c1c01c81c4c2c9005641c00858065030034a5241c0204400c4620450041d0708181c2071034802d5890010910911303101700c10020f600c0d940043c50005903081900d08441c01c5440da40c45117200040d96100c841c0481c880d9241003500901031030070261407805281c00c41d5600003656581c94103c407090b485894801c1c10b00c120384100141c1030b500c00321804042445602c1c85c0c400728260300c01c06460002e03040450010b050a10000d80d02344021040e000301403600304002d104042c0c00d1404c10905040420b50440e41150034a60103c001c008001512060603200396424542002c0c5141d01e0011a0704900034840015820808107000c81100c0c1c1c003500300c6030910 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 618454073 1250 618452823 618452851
    0x10902090109180f0803180f0d031e05010b1b0f1203070c38040312020d020706021603020601120f0f141f050c0a080a11090a030602070b0a02070b0f 65
    0xaa00d800c8414454135500725102200002002502281c408480c3c1244c03a01d403000b42814480c80e40c411f5215010b0180c044201030303881e0080e05e172081580344030103d0944010020021541c540c41c1c8201c0c1356201f034040600ea811601c42c4810311110008030000c032079001070041e1520083c0500400da4a0b403010349880100400e1002241c08500c040060f00c00d5446c0440190001a100380c132810f0218428038400c0c1101902c040030003010940204440c407031080100310041c1c0d5001d0100c04000280a0340e2030151440c0d1002c140c4034124503500d0644d40700079020342c00b101c625070790350740c9140483c0030b02240041107080c14180f80c2c0009403020400302552403042c42400004060031007418501341c4d2000c442d800280e400d1081851103149442500e8110804039203203840d048507810003601012014200d1450142d03a4030003070142c40b46402c190380360b40170007d0219014940d00c1c1840e0300a9040b040090b9046a07846004c0307610b0700080e1003265a020391200d80b8503402d0781c66051454141ca40103241c1c1c14000c843e = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 618455323 1250 618454073 618454121
    0x10b01020c01210213060c0c06031a0409060e030f220b04030615030b0f160e211207080d050a060e0103140c0301060807170303010803041502120403110f03010902090109 74
    0x40203502c2805000c895440300c7c00d800c0e503170501c3c10b01c4044d02e074400020b251802c50340000d4540e0b4145400c10966003a0782c0441d0400315480c164000300390b101c000c41c0c010302010030098011042c0000030070640300a8112020490356604408a09025520070100d4482d420841080010050b401c034031040214142a402c0c960b503680c4030307034408200031584800303803104c00c008100d003185040300843c01c01c00342481c0181204852001155500d1034450700f00c00c842c1107120114280b00030800401e003d400018a205490b00003d25015600b41c0042d481d08204604050001e100f2001c14454902110031205100c04903034a9601c41040c40a86160111540e0050200180c110780782405800c005002200052a030a0301e040d003c40b000114105030300c60355170001c0004008a01c3c002090305c0c140e42c0801039202d1950003100381039203000c480301d48202e9603803000b040001c1401411007045501c0b10741502c800d41d64000400815088906031030300294420740301001442a01c0d41a800100c10410740050a8400c440d = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 618456573 1250 618455323 618455347
    0x1404020d081303030e040e0f030307051e040605030717100b0306010201090c170d111c050c01050c130605070c0e0a090c030803062d1c06020a030c02010b01020c012102 73
    0x4541c100341c0115504510017004c60806105601550101e100a09401d4002120b02900c134071000d4800b07400c000011941e440052030b104004400e070510003060540d01c51342c0b5440079010380c0080703072014041540302e80c07040100584030300d03102c0c0704019400c0b0310104c06042010f002602d42020b00303030a0440d940c40d0350640001e0140305018020b88075104151065402403c006442c01d001884c10400708510700c510301c043e17040002043c0e049045001900c1e414018402e904440e11301070000034445a42c01c25062240340540e110007801c00541400840c003455484450a650300d01c242d4000505040d0410380400025921a60082c2c000921003804180b410b050b495002e040e10440e0019110010300005018144c504452900100345001c0d03500030034004000403a0102c21038501d6050f001d02c030803010804140146503940681940c0c041c0e03045440386205580100103002c000c2400c005586803d100c010290300000c0d00e00300c003990503514009178602105464442280d14045051459000d0080c028150 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 618457823 1250 618456573 618456607
    0x3060b03040609020f061602060703170a0b0108061002030a030b01051926040c121727030102250501060909031d0d08040308090307090e1f1404020d08 66
    0x2402110b0101e00800303140104204d54109161091040da410000100d0914000c80141301e400e0301240c03140c0e140d21041c20700f0340b0441907061001c6841c05240040200c01c000e140d0149040003400e903074552156540d9401e0000c165030f075821000c0540e03c18803441d41031314481c0d000b141d89002c040c0340450500019400a1713089414070021503020035600c03002c542001c0147c603d80041100c5080030744480341405c0d21101c481c170300d29000341303502c280111072050b0a0240000340c4e4080c0a212507000b5176910300070400d0303a2044580480ca0040c9400410ba40310755854140243e441c3c181401c503071304400c03004070071200340121100c1004544039525204001070b00c580510505038224007c0d1110000c00010341d0b29040c03014034211009104081e200c206a02080300082540d042c0ea900880c0c00703544130f10705400a40b81001680c8604c12003824414600d410103404221004a100742e8071084014207410b06c1542d06441844c03403024440015000003501514000e40d0018a07140625000352401a14520900e691 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 618459073 1250 618457823 618457831
    0x60a020714030304051804030302040302090c040e07021f0c02100f1d07080c060a0512010f180b0f010e0607080c0604152d0608011d011b080c0a03060b03 67
    0x26810a030030401c0540409080040007010440107180340c0760801e40040d082d02014500f441315588210700003006c040c0207a04a8000e0754009081e08010314050304402d0181e4000e014041e400b010b001c005c60501d6000296001e0902c8820254085031608050030000030410990108118410000b40039070308a154800d42005450004010401340201c4c84c0038444049011101182c50340308170000c21888902080c215440c0c50200e0302c9a03915402c0d0f03241111640203041110320088000c40000500b0750021070303007030200ca00c50000750303d0103070703114800300201d64440d510b1039002510355082c1c0d00690300c66100080401d0005050900304412600e4802c4140c2084204c40c400d41d010105200500c0b0304407210b4080b140c4005801d1107610f0842c00040b40f13a010403094102c5491002c4114034081c0741980001c0050080352008009880b25115860720101c0304440d01d0b8071075480c11503422401400a03c03501d020002644070f0400a4642c90000d1407607174008500602099695540030940c0700f15000110f0003 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 618460323 1250 618459073 618459077
    0x4181703060109180204081204061d0424030308011211130216031706150a0e0102010204051008150d080301060e062802060708060a031112060708040b070905010e040903090302060a 79
    0x6c6038246011145041007102c5805021101400704001d9154403c04e02c1030200751040d11400c0c04039054002c0303400360540054600301c510004602d0544129030f00411802c60713020350b4642c14035903038130400c00341070003201100030b044041442404071a80c01c26000e09562200f0000005107400c103104408128619248021000030305008181c2180c03035942642250000300841d800011440f1162116030f483c807480141e2024010981e600350100e038006e5040c1c6000300806400501c00b11300194008040d00811a206840d0381400d102050043c14240c0082901c154040350040c41e40c1d00f080001d4401555413440580c0c03103039040010803c030081c03e480e40d88405080004004940d0000d55020b030400b800107100340300700001d01003000780c241c6d2100c801c00b0450b174120400081a51981e408100ca40c41460f1004034944140b0051001c5039501c510700a1107140207d95512050b101c03484103e030242880e106050000307060300503c50140c5002e62060074601d10900745002e02550b00e601083c0e040c0c01c60883c0d440 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 618461573 1250 618460323 618460327
    0x806030304092c03071a0609040605090f0d02070e240607080717030105030d030504120c020102070806010618080304050907140705100203060102100501050a12052a041817030601091802 81
    0x1708000c074080011a41ca0001d10860000e0316001010840020380188050040e946a0003c14a03540052164400446001c3c040e55900d04c0c5d042e801075514007280c845c00c10f030500d800d0300140607030300018402d042d8035490410b416420416041000a546c00100060303400705020400e140002e1041d800108103807501c00d0340e850b01c1e07614000c10181882981c6c40d00c0c03806d050504007040000782198010861060a50504c03240003440c0d800100d01c0c0500c0d60704011020b11900002007405500300f4003400000480d2003025001b15140d46120351640248c0c4103030b5800140c5000810801402518000a45100da000950030300030301c0d80b1098504505040036211441d800028409035503410300c02c0228110401c10140429451b14000c034004822521544a800e00203100d030800300002404800610b41c10390f07120422206442004048102085001c6ca1141b4075020b005111014298103c607071464110140c02c80f050781c42811002d8544c8010600d50400040e101d000c90007410702c042311b4a10000c6454010703 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 618462823 1250 618461573 618461587
    0x1127040204050a090b04021c0f1b050d030203031314031c060f0803091201020403020a1814060d14010f1d0607050301080615030a02060a020a120806030304092c03 71
    0x42110000f411a003039841c03c00c1060300208800c031000c0d50300541d042d0345115071504038090b0180c506190410061841101250030014442e0f10540e440280c1c1c244014440103966840400003000300c1c00d080140580c00610020311605000035041000c0fa002d040381e035506200140e5900d08581c000540c40f200008051525103c0c1c20b20352080d0b00c06040342c03403445504941401e440d41d5030381c0110384240d407142040c6600032400e80800e40603a0010350303000c2c0807840078a403265540700c14081d0001e840910980361800e458032882e151070f000d50003010054194400c1d00076507290000c0140342c1060800b00f07592141419845010184142003200d01b030039403440158002c00304514180742d070243c4000708105040c00140200d02d0b02184854020075480302000384001389a0109041201e01e100180d88140003041c2008159000304117100024800e2806140211a01031305568800081d41c0e0300d501503105100c24444083c295011541045040354401602c071000511211141040400c2003102d41001c1140 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 618464073 1250 618462823 618462829
    0x230114060114040b07150c050c010b0d030905060c1c03090c08010c0503012d061e170112050f12040e1005130911030d0905120609070311270402 63
    0x6140c001209181619802403080304810785400b85004600c482c2600080c0e46040206404100310390710038400c028003d080d100800a04160801c00340703400c5650819815209074a4403903c540c02081e4035807104802542440b09201954208220322101307449074000030504c050000710b080441503070740c0c5d4002c642517447d0b02d025215010680d1041030340341c1c182040b02d081c071900101524150f03042060403080740b401008429040050003542018040c6001c1004601d25a0108881404160301c460301600d00c02d095200b11101d43c000010908610307030707807001840130170243c008242d8424001d07002c4640d0800004100c2e41484010000441065800141006504010b00410780d210b0311031440c10070558501004500146546551081440d50740c9500101308440c076002600544c0c1e000d01200d80c2c0a2200c070010f841a1018040c1500c1003240c0c44480344a410300156680c814040c0001030500545190b0b10704400c040d1884025512868040b01c0d0701000c03c4002d00000c04800000044e900c0d41024014 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 618465323 1250 618464073 618464111
    0x70f0c0b040525030c0b030c0f04150306140a0b0c070e010e07020f0303070f03090206070501020307091403030c030904091106030907030c05060304020d02010e040f02120f010803070213092301 84
    0x2403d074104103981c1c041002c107101811290480c2c4040c0c04450b9280d59000c2d0210492003900504c0450399404030700031404100751200b0f00d5642c2030b292010000c10b501c070740c201c40c400800c01454540c426040c180030701810480c1c8014100d4004540300b00c1d800d01751500400d41e840c0f08240c005225400031042041010b42e41009015031400500000d145542000c0400a007a100d840000d039040c140c40340301000864642c80708550202da0008003c540b02c0c18402c400924180352482602d00c602a100d8600c030340d43c98048100c56990074600c00952038114004180b002034036000e003060381c403514400c40d038200742e4556400070b512070b404940191032024258a0041c07480352041d004140910001d00c02c00c170041c0c6410040c11401602400c2046400030488000ba01070800040e410740b41d14000300f0707100165613800c4112801000b5003020f52801da031701d03002c086580703014000019520181407503200140c43d03000e0340210b0710035001c0d8003000c4000c0d454034448401c640c41030000d00c205030340d03c000b40d94a0001001c4 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 618466573 1250 618465323 618465373
    0x921080409020406051c090309120c17030309010c05030105220b03010501061e020601030b190f1d06060d0308041b0305030f030a0b010206070503182b1b02030303070f0c0b0405 77
    0x1b804002c00316468030003d195212038000d880100c103001841c00d06000400312590b00804045100c03495620300217403001c1e104d4000b500d407096250308024803100018010f80590781610030107044440c900100d08607010004c3c20003030207514050340d9503e82604544003809218040c00560700c80004000b50403903400304040305009400115042400144009005070342c841d50480c0e049100e607030240c49141c500302c0051074400c4501904514146040364010702c6045842a451500401e03242140c0d141400c4c4000585a80707170050010310143e00050025810034184040f01c0180340c1e2191120382c880c0d4500d8510703403100c0129070000300040304110040c0c400d4000c10424074400c1c4050241170410f124060010301000c0c00a88500100c02042c400d80c407000c001c1d9000c0c0403034880f00185811400c8060a10412810a01500007042d00500f40002d0700020f00c100080c81e4064000d614603950540b04a6420b203204480100700142c00c01c0381000f1400000c0c190380510f0141011303140c1c0c081c0604514814800c188 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 618467823 1250 618466573 618466627
    0xb010816090207030806060307050c0f30042c010b040527040308130803040c0311030d050a1407150c080105031f0c02070503031b0706092108040902040605 68
    0x254400285d40005c000d6040b50055545035283c3d1030301801542c4034050700310030038510f105a2420f00f41d4100c00140c464928508803803042c05411040382594101d400b410109000715808100801c0541882149014401d10b000001c20810001c90268401100b083c5c1c0b02d098808000309050055180c00e99401c44c00301003c00303400100c200c22040740c42e29900010006400e2140060024800c12000c41c5111004c6501c84005a40d034641171410303480e40c808034001a110007185003910f0515040005101d04c1c00200c0d85c40340340c2000caa2520840f0030f01141c130b2403159042c10a0214000040c0c0840011400500b01c0c3c0f0003096002c801c0e5801000707090168030135442503128540700618040d108100310301c3d040f0f001102240798805054143c0c601a031560040f0b0309840f001980b0303c88a0500017407044051042000e80e41c080341e990074203e505d0f00c41c1d8082d190740d80700108051801a004028060940c40c41210362900f000d54070760000f01280c00551020020800000e01c1c1c1101044400c1180b00d000022 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 618469073 1250 618467823 618467827
    0x80111071101080606040b070803040c051207090509070f06030b0f0901050105180303120906010e06090601050f1308070906061704110d11060301091a1813030c0b0108160902 76
    0x3035200d8031031100c0d800c101c81e814001c601c004642e403503c45008440c060300c5485981a9200c4442c40c1090907039008980583d24101800000f2680d803400002203182411510000c0ca015130a00b44103100515015101c42050303c03400e0400151403100900c010020702154400007024441e0506105000399500d020350b10405800c03005200903a001400d0f80c07403942d001e80400d80d0340001c0d079000c2481c621440e860720a04c0700c01c4104008160703400194060585070302c003002d0445900d65506002d028801550290301088050202e40c0c075071140d0501810035001031824041e141551078000509140d0540c014003612074940400b80412034211044020701500003401d02011f1510b910303010044141d8100c014400c01e1540c0c8001c0034000d5210303414280c0d1200600403650395035280407481c020541c00500c410214090800410145048403510b8001408400d025104da500d41120010075910a0012818441117461050214400181041c06402400020840a41c6402d00c94602500d15403200c1c447d9401 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 618470323 1250 618469073 618469087
    0x3060f011503021309090605090f010608030703050304050c12010f0605010c02061206010918021b0c030c1912300c0b220f02010f09050a0b0f13080601080111 69
    0x16001ca0549501c1c02440c1c010f8580c880c02d1140407130814a81c0c045410b06040c050700034240159544018022000c0b1412038201c6c04090500d64280c0d4003d204ac03410541040c052400070900440007036501612a50a4130700c10440307a80046c03c50740c41001c0d00710581c0e564501961000c1001d11942c030181c03000742041140c041c0d5560000d07807071384511030300a800c1c0281440450201d074051810704c4003409815a1880d0b600403000110b00c02900b1484441e452440c034054403000ba000c01041c200c0b4083d4018002d00310304040c0200344680d40080150b0042e541094480c00a802c0000f01c2ca8400914860310141070f40b080c1e08504010083c29100c4400003041e020107031001c84c0764000310001001c6501112110855589008001c00703078044034050404001507130700c03c40030007241041610b9420f10036260a200ca080003d802c45075000d507805001c1c0c0004040c042030220040210142c115110255100e5140c4412f0040c3c122006213290b201103500d80c08417005214070f120a0180a28110340c40701c0703960801320 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 618471573 1250 618470323 618470339
    0xe031e0703061d120a09050402070b1311130203060405011e1e120303050a2d020d0b04021b190b06010e03070e1e0a0e0a12090509040f0203060f01 64
    0x2800d440020111980c1e1011101003450b50074240c2000340f0402c0913a61410041510441030b640310600b08000500d4810b001705880c0b0f000c3c800c3e54040707500b00f10084202d41c3c900c1c00840302c4440f0320b0404c0d503c8460312600d09a6035030b252f440340580d070002c9003000761316030406a06000c10360300c0681101d0401a042c80c500040003058880d90700232188410f4421403847c5600e0001220341c03100350001101c01c0e00012441c001d041d01743c0c00c224041c440014003040003464801401c2410041e8a03000c400c4208800c02c43c0b10101500d4001d00800d02a9190003d420100d0701c2c0020100c0c0d114181c81000100d94200c1070031100b009210f80319550b032003d0262000606e05660b024056403000705010b050001000040003261000c000000c081c10221a1159182c10000c2c03110075940010080905803d454100003410101c0601802c0e0300916620700a0148000715070700c0d01e40c40400240c1c90070402521a0000031503642c1c070203007140a14001e85203800400558010b15050920003011400103009103001005901 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 618472823 1250 618471573 618471583
    0x90a020423100f0e0a0f030b150a140a0504090f0309090207021815030604080c01110f0706020714160e06030d2109050106140414100303210207030e031e 67
    0x1001c0740b40000d01e404016905a944d500d0760021190410079095020034241d40c0c84008109613801070100c29926919014a0050012429070b09900041c20744d50030040d2000c400031050030802d0080564116a8843e404501140c840000560303034001c0d85101c3d4410705d504024188060115040305510b402c4098002c03c0b10040c1e407801c100c201c800304000041e004c500d072a0058040c5907005040d2130280c180790601c40500c1e0001805c0324980e510380600620b005182804503154001d10182d02c0c1d0505401d919010020340040310240c1d030140e0101d11208400c8400e00c07105e154102c0c2c019401c22010706105101151810050a140c0070381e100c4000d036901d0503000282c2180c04030310f04250b0b07034106110351000b00c082c1c072208000800f00c2d800c103880441c00102c8802450401102550200585602c91049604000c01500e4041c4c0c0ba03c3c802c001480070034425204d50700780d40d40e4a91824009281860804120f9002072004e4000501031465801e0500d81408224071601366820055480720244440b65155 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 618474073 1250 618472823 618472849
    0x810060e06030d140310170f0105010b0901120c050f1b0114090312220b060312041d07050724060510090e04050106150906020601061707050711090a020423 68
    0x4c8002100082032641d44003180000342c00050038006250209440040d60b41d450400b80c4411542000c0012850071004030a07290340380e01c140c1d203c1100f4033092580100810071400d0787c000300641080b120b244140f482c4000c00708401402e01002c07211079101c80c0729085a60340c0d1400559092200144620544c0000c19115800d1000e0300340701c50343c0c445c03030368552001c101d00840c450b103c082c0c03118400900082c8085e00388030344030650a8501804103103608281c1803049008a00c0144000c024105840d104109415804052402e00c075182c8242c94898034584903c510500348a4110414840314500d814000d03800241002d030740504142e0304090b409441c0f0b151502030780301da200419002400742b0400350403d00c0288840411001a201408401000d4041e9401000058801c00000040b440d201c0c24900d8150310710805400d296864452040307505071b02414094a0340c2c100c0000351003a695400070703802e0140403070850045e44e40b80f514002140c0700300001807440ca02c403200c1c1480c100382c0e04c80075415489 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 618475323 1250 618474073 618474107
    0xc060e0f0d060c171311030307020d030f1701170c0a030b150d17030103020907020604051504020315010b04170a08040605071703040f060b0f0d0611040810060e06030d 73
    0x43c4843d910012901d554200d000254050f11442c2409001c103401640303130002900542c016503520b40e18105041e038034412000d00942014030300101c000480d1040d04407400c501c03894644400f100b070100f52201984900be0f00304004034070702600c0c00d061101d010010003809010580b20b1a80c040e2841c4c844041c100d0005100b003128040d0100560070b680c0d06c00f0f96460303000f0360100541c685c061040c1c01c2c1e10307200c0c0c009000407805148400003080100e40000f44640c801d82d40720004001e8003402004a06000b400680b00326010b03c0b40311100102c00c0d03108002d0314080c044071845c1c6a110b529007140031032046603d9012403000d4016050303840105035590111815520b09062044d41c4616601e000800d000c00c040d000c0704910401b0090008110006c0581800540102028040700c00100d080000080d100400c450703000c08002205400944a508502030801e12810140d04050b40d85461906106003026449003099480200340b0902000410b60782d040b0500b60014400901c02d6040a82920154803407881 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 618476573 1250 618475323 618475331
    0x1b030c03110115080703030f1803020d1109070206040c090c0516030219060903030b1503061203160f020310020906041a0708071b0e07020a06050a110301030c060e0f0d06 74
    0x81100c0094001010202000e8001040c0301daa0312413060712581c440c00120700080180c10060310052054089a9211315400764414100d0315547c20440f041c2044041140e203401c3e00c5904000f1540c491580e28419040c0c3d401134001440c0c9403400b403003400310039001074143c1440e012020040781d41c0002a80c4501c000d9903541e400400301c505050703261006103800c2210709100350326000200321241d00a407641901c00d44007400000000c00030045800e108908888100c281440050030516104101416104030760042c0c030300d480c5161074084001302e030583e415207002e00d0500c55081141020000c820503011240700460800003602c00145140c4150f04c20011004410520000c5c01c00104003151455a0f02c49030309a175444840c42c205d003821411030600c096020130b9060000b0f49a12010a0911900321a400f42082185a42d40d2074005c100c054000c0311010358400c0000040045a00114080c6004104940c4c4051a020004101c003024520490041841001d109001c1d1204e1038a2a40316500043c045 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 618477823 1250 618476573 618476597
    0x2040f021308120a030e1002040609080f010605100e0a170f1510030f03140415020f0a0203060c07060609090528020904021e10030e0f0a02090c0f0f1305011b030c03 72
    0x1511f00342c40d9403690000300b840020002110b0307030010301400481d41084155403c98844e001a607080340c0eaa44074007078000784422403402c1003078810b00140010000c01000c8560b078580714486100c0354080e03015200000c0d03000380c1b56803c0d50729003000742903403071800c003940f81c9068a0251072400c010349040c44010088200b0b40e10b84070406010381e180007103121030f02e4515030b1116501c0c244128001c4680410b00c016000e0002084c032008808074580503025000380c0200300ca03840e83d03c41592154403909007074440030780d01e410214030020f407070062104d1107000350010302c8084480300d0762144d2540300945294030003042c0d440c2d003c0140c448980031a442601240d5011154485a0440307240002200c51198801c6d071644240c1c0d0030a415910400f5038003184801c4407800305200301195aa420460300217540b212801c1c0003c5c05008015000300313441004640514106803460034100129040055100c4d40c00319450014801540d00000092144450080620800c150b90b107002d0040c6098480c060100701c00342c0244 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 618479073 1250 618477823 618477851
    0xb030106030c020f30180103230a050402101d01050f0c0f060f06120c220c0206070908030a050f0702010c0f030e03010b01090312030506030c0316030b0709081207020d02040f021308120a03 82
    0x30130562070b04810f003400b00d00d42212b09100800d4100c074102e00c1540041c0c000e154680c4540c1701715a5065419048640307804140005554a03005500e4080b0007000c100b1030004070000a005248094071150024a00c40c04c100411190001c0c008001901070030841e610040d088070000b03a80c801e001810340349103203100400c0d4480d050b03003800c1da090007542a040501102e0b00d50380c00175a96205580f1946c42809040c1c90302ea0345503c03842013400c1c0e240050403d01800d1a180c28080050900720301c1410328010414a0740c1c0d540002070980c54041d00072078040c88548e126402d080c010a96a82001d07e05106c0350713030541c0d9400d103209000003110410550b562000400c1a1020400365941c000024100da0300005200c01200d50500140812250840c280011400c0d03180190201d009079104e03a00a040000d1090700c6c100410380160380140d905c000058408405a03c40c1d11840101c0ca0001401580d11000c1d12800300c0301d900207a115110300c0d4400707010011a1072080041d100c201407940f030301048400d02c503d00 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 618480323 1250 618479073 618479111
    0x1060c1707080a02120301050315060406030506130c09060e0c0c0a05251d0f070909180b060f061b0307080d0c0206010e010b030106030c020f30180103 66
    0x450001910001440750500c1114806018950b441d94200c40c080041810f903c0c20500003840303400c0c0c160744102101800c42c01c0c074002d043c1d40b2420140001402c25602d03202c1a1030302509441142e4641440c000b51418080403d5100020b4182c004050100c18980200380e4000c88000f0300c134584c4460b0210380d001b802c040c10b03c81c001c16640c0180c100e4002c0b10014030000003803048580d800010780c40c00900001d40201340d805041c0040c003c11300364506561105103c0050850040825041144698011170000c07044d00c603903008a4041c0720a42c40c1c0d0091840c004c0110783c402b4000900c00d294004000281e0341c1e84400b1a0059001e90b0032402100c601481c4d200d00d140030700c101c010a104400b1500c140c0d440380c150300581d604200b03031742114843e90380d40300e440b01141428010103100c24000c01c01407101d10f021344c2000a1000c5a441110310001400c00464140070040702009880c1011851009955020044545e041208881001d02d03005070151703000d03840407071034010a060646038040c2c98045210350310 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 618481573 1250 618480323 618480353
    0x302120d090902071e030201050601030f0b130b03030d09050604151a1201020c0a150c09080d031a090f100801181e0807050a0215071104090809041d1002090901060c 72
    0x911700160000741d1501074040d280c1107514038006841c08030752200081d600c3c0141d4104207409000030500460654551001d0907030485041d4151204000043d01c501091159102c6a401480607001ea4146803070104c0050355004080e280300d50901e00c511041c08680108001d082c882111110022401ca628283c003a00801d8150302ca94003407113145006000203688150048070070035408000d1080040416154000e82c0c0c05070b840c0350b6205d02c0364061007601940c04039000580c480c804580c8400d110740065002c4504445200b1403000582c140f09083e103101d943c010260100d000240100502503c074074005a05001020301174502030a100040c0400090000e65030035001804c40c2d50354042d5040c42c80da508400b0f00224003405408901203800015a41510149588a01d1200c1c0c212034800421014215906d0203880448040042c1801603945105401703903d00d50b20a420010030b0710400d090308000504102584d02401084403441c1e90781c035420034605407281c0c1d0620b01c99580d0301c0d04001c1c07140c0308402 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 618482823 1250 618481573 618481613
    0xd08041b06120f05040f11030c04060303030b131a060706060f0803041a073f02150919120908030a1d0a0e01050d08160b010302120d09090207 62
    0x3062869001c02030400004a010b03091004100003ca00360890300100c1d03003e4040d22a42032200001904a185900c1c0f0341c400604030b030012280c0b60001403c550045d40105e0110755610180c0e501810440411000038801030780402000c92080490340c0b00940000340b461040780c001980d8402c02400c3e50011024180c0f5140b00d007034190312610341036aa54010302944036041c1c010340380c1e16503480c500011510061b90001c0e000442403400d0000004100f0010100a04801021604914403851417140600d1594503070092004007074440d08072003401c101400b512200c0c0c2000c8007001b815044040400c0410340d1101c42d44006100100381160341429607040728800703000008207401e0b403561188a00040340000e405c0c54981410001c20014421594402c0c2020810403034010045494821804011035014410040c03070600801d03042034122180090481e82a0706600040c01941004800c0d0000091400c004040803180341c01d019004003801c0c447c035100e117600000e0345002c2003120a180d100801c40d41d = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 618484073 1250 618482823 618482873
    0x904020f040e1003020111011a0d050c0d1b0509010308030609060a1802040609050306060d1b03021c0308010b07030c060b01050d050a0c0315031a0a020c060c0703030f02030105030d0804 81
    0x24200e10701043c4880c441a07001801003c8102c51040c0103209980042c5448003880500c401317244284080018941011346541c002d6040080e01078441300e801241131449115080300c2000c2c3c104000c00f0170300054200a014161100040c8006519042126040700c0b08550b00e0025541c3d200004035170001a4000701c0102d08009561922103001d6009401543c0c4651980e1607015202c07010305035164030884800c1d503c81da01c1c5841380b01052110300700c410036030f0b850803032030b5840380d16500410651004d00ca1300011440000701d0900905a00c1900180500310b140030382c514115080e10300030251400d481c40546130560f41d140e00141603014034111003810050090a100314941070301440024801004081c0100f0b040c54070701c24031520030103400c10540382d12801c00412200344025003010990010200c40b80254200034800d040c90081050a100c3d03d4030320110b50341c40500d860001c0c00e86203289040c2400c0750061005002640e40407032103128003405460003990300e40e01c0d814038400c1c1181c1040a030014110f5 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 618485323 1250 618484073 618484081
    0x7030618050a03080f06090601050d200c0c0907020a020d12031b0c050f0d090e15041103010801200702062101060e031203040506070c1106030a0f05100602030904020f040e 75
    0x7800e03684558841801c0c48800e903101014031041040c1108c807180003032170411200c446103c05a0011900404041d035885044030048401c40a0354081c0410001661040100e00020301d0032070240340d40f03c0c0c00b40c405410803a41590104482ca2080303100113050202e00034011841511aa00001c502083e40c0850b0580203100940a00440e62842c001e90b498001d40c0c0880c07801c084000b030031a240220726520540344524140c1c00556884000e04034052054456102042c19a03540c020100d015090114280d03695240007400c1d0708454400340202a100c02d0b0014443c0c2042003041600d03141d81c1c0540304160b90300010300c541e400075514118110f0000f0807840012501a901454101e03070f0b00d4055084401c2c4148080d103802c01c500086500410580c440400680700600c50301102d0a440d100d40381003501302881c3c40004843d030708212450408103645d801f070720183c010240038070340e040224058880c0c015424024001d40f02e02c18162614051600029051baa5600000c200c0b001441c1c5d00030103020b1424 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 618486573 1250 618485323 618485327
    0xc130b0616061409060c0a02070f080609100c140309011811030c090402101404080105040b16051602061b0a060c0e09150d03120c030e0106060306060207030618050a03 73
    0x45085800e0300d005141c183c07031090a018000005004992550040c141541c9040c4c00e1059030740060400b104502a401300060007520003403d000113815400d000d000e85180030f0340b17900c0c40c2041c0664100c0c0c4050800d92a50401da40140b030300301e4a55112081c5550b42ea032041e0f08903014000b0000200e100030580c1d0612018081d4501c00b908155004406035a00040c091080020400042c1e40c0a980072030100c94141581e80a001074032010100142c800742801d82e11041603085500032142541d076145030b0380401806824513a661080d00b54113060460030005041c210083c2d0340e20381100203024102c001091607120059200940c1c40b103005200321155212180f400d42d000e0040e07141d1000125054002e201c009140c030b500c03442c0c422100000081c20381d00010003040382c004000e400980a21209045400d692802406080d06480c580d4501059020202d4241030840c0d201c1c2d40000304140c41d14006206450f80403c1a10460750071000c040381d0003800d504031310a40054084001d04503c50070108a007055 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 618487823 1250 618486573 618486607
    0xf090806070c05070b040311240c0307110108090d03110c011503060507080c0711010e060d0504030e0901080706270609140301061d0405010e250f080c130b06 69
    0x94803032020b8401a650782c405607179082c011030100420107181c8010b40880341c01d001c00d105048000d905901c20a0984685140c04103502c0000c0ca031129410018814042c49103403503000d03180300700138030302541c0c40d2614542c2103450300e03c1c4000c51010161201c2500d0715600d9100e0694104110f03860080000c3c3c0703a0365190100c0204a440300f180d403a8242000141c406006131509403040004c001c1c41b5240c2451591400c07080821f40c54036034188007212100d07071070941b81e0001400e8102031481000516040c01c1c100034095405400209200c1e51100006100c21040440c1000441d4000d003844140040c071025000509039074101c00040b4480040e200081e1319501c1004442125916800c1e010f2825035802850300362059409810602d507150b0003404042841491080e9016015800004140c0c0848014a0903c2c00c500c54a0080b000d00c58010b8080310300b44a8070340000c046803603c10760340034646000291902c10b64035055100f4524581c180075180400c0e001440d101d1801010f0a41e90600484503010036 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 618489073 1250 618487823 618487847
    0x6091b081002031501080717180105310f1a060a080106050901151704050706020c01110604020f190902030a0c0e0307050909100603060c0305100e0105010f09080607 72
    0x41c4145200ea402215040c4220b9000e25034450f500004000e81c1801034030131105c00f5204800f0080340b40049034400c4200780f10940201d90503401318061103030040b111400c1d61300c080c041c042c040f030360051f41a01c0100c0d070400b00070101d010181045594605030501d40440e98440300d02a04080c0207014200b0910350640700c607845580d0441d0050209902c0705e410500303d0b0760354006c1d56040462030005001c06180198891541c1c1c68611740080c0300b046105541b060240142c45c112166072001000341b103015018054807659840c01c0c40d00c03c0c06005040100c135510140500042c0c01001a0144e8282c47e417101605000484000e90307181840c0d5a54031610742c001e40c4100c950900d2146003030481c20a0700d1244c560000d202c200100102446070400301003088a48000e88461190300ca801e0160f803100c180b9000d013100031400fa400c00502500756040c00b4081d11f4005141c0a240008078100380302ca030038100c00d40f84c190340c2d080c070303100340c0030760380c03a0302c10b03030740c28680d5000300003d445802d0400440640c441d14070619 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 618490323 1250 618489073 618489089
    0x6020c010203010f0e040807030e0d14010e1e030409091e0515071d01141306030207020f03060106020d03050402180c0c120a021f1103040b09010b060403030c020d06091b 74
    0xf0360362014170305030105054a00500b00001006558046481002226911040246101030007003082e561101d8070072020b0065001c036519a100d203110560103014840e03401321049882c80b07104200e00440d584a00c954022501800d56410400050005c01b50010741c03040070f41500400c4190903400c04550340c41c0450038280390004010002001c3c035104840100d4428020340c00514501001001034400a8041d16084035010703060010550404c1107030a031600804c4291001a90f07a03040340103000c0c01e007102c908220701070740c0401c004024596001031401d50300c134003501c3c0005240c0c590380b001900e42000c49550b880308078081002e1000075403030b0200901086410b401262035131140c010b400b401c42c0c01496940d00150700100e8030000c052156081d46410400345075800902405d8442c0c0c0d0700881d0300160cc081d90301e01044070070450070f0a401d21518000c2e030302c2240d110342090701d141d80042950b0280c0000a00a140306608101081159004903440d5540711070b0020b480b00c040e40100340d0700c10700ca11036045 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 618491573 1250 618490323 618490349
    0xf0b190201020a1b15050c0a09080c01090e07110703080a120b150c030c07171603080304030e030102070c18060509130807051c02030403061410150201020706020c01020301 75
    0x150300520880300c03180559100c960040303440301c804d070b0f5a8810030318040d01c102c0300026625000302000d00c582417043c2d0803040816103d00310544001d020351002d810449990340400d0004a080ea000807203582120311682c40c00303042c0d580b07010f803c0740d440d803200510f8603540c0f0812602104110001e4068948200c5d030303236150521580110a204290368004c5000b5401c00350080c0b201203000681e0740204564524041100d24040410b1070845c40c00d47e0660002d094600003044400c0301c50004e00030705c03540391100700000424074115102c50b05544030103080101841200f0b00e00035000c1d207003074040d100e100b81c00011034605e40769a01c220b5541030255902c3d01041c58034002c1e0100344e1345040c22145000e812400341110001e120b90ba9100040e0384421420707901031003845038401034030015039100c2002a100e5405107482d20710b180344c41401e580780e500e8220242064101000096030028014800321004a85c000304003035030040041c0c0c02840791a82c0030300361600024507081c0491054000750304036940c04000310 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 618492823 1250 618491573 618491617
    0xa240303090e1513020c1f0e0c100212130503010e01050114030102070b0c0706020729070509030a030f03020c010f06180c0210050907210c0603050c120408040f0b 71
    0x3100440c030103041c1503203c000c80391309560145080e40546000515032048070400f0714000005150a2501031421804036204d418081c1e00c550b050058501500050b115a0b00c0000c0410000e502d0b807881c0c0381c00c0342450f4030204003c03c0454240c402c90009010250080100c0d04182924a028040c02d0141600f0b00310401050241c030f050510841d1004c5402004003c4c40c0d858a01c0803c5896200a60584106400313002c450003261055881822265074180c01c1e200004440c8403134110031400a06c14418000180003450342c40e100407846000b019813524142c240e41c2102101a00203018a0321b45c1d0b04250318020a902c052885079201034255040c01c980350b0030741c400045010043e04c03404107240d0016005000c40903a03071407285d000540c2000403030040d5000f15440c2e60342a080425170808494016441c1c061540a0101c40407801000c0c1c039480c607080c01107140c083ca01d58464402c12101c552800e0b84040000c0500c0543c00958000e0884101a004072071f9030b0f6041c920740354001501440c120601c107c885 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 618494073 1250 618492823 618492841
    0x30080a05150a0504110f1204030206060a030c050f010309051b032503140f0307240e031b010609060b22051809211e0408060a240303090e 60
    0x4405a50000e08901d10342c1d092405120243c5140480030704403040503c102d40d00070043c0e50282950f9403054034110081e18042c00d00034a84003001d080e0600031050410140b003c9800c100c8103d05484003030b110028140c100e000100d00030f000300d10000c1c0150251031044161402061207419508104034200c500c41d0901c41c40c485c04017001d140d201012515490400c00000d4080402c16071789862200507915803c4071910031600316400740d20200c6a010341c0e1050800c4040070704150005103621800208468a132a81440343d40b807089604a070000c10320000c1d03250f0701c10070035080800030b002000c03401e1119956501100406400518034500d0490100c4d600401c20468885400b0480f00010034903d0f040c2554280c840a00341c000c0c02d001c0136070090700700c00001d19091190352100800d580301001e5480709008444041446001d0100100500801041200481c0002d10a41024500200061032a80500d040002c9011240c000070300c8076000000205054010320482c3c1180c1404c82c07440110b954104407 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 618495323 1250 618494073 618494101
    0xc0910050f0a080303180f0d0207050406210b0a15030b0604060b27010903020402030718090902152802060f07050f1207140706050a0e0d0c30080a05 65
    0x9410003544c01880000c41e4103001c03144034109500310308140c404990780060868105014410304002692161000704031508181c4a800c0c0101040c2c0c004100312a021344101070003c00c1000058051198900420318503034181d4010400d89510918403492035942c2c2c50b043c0c400c2602141da10344290301e088000100303c00041d003114480c021000c921554500807100707444030303410f007000c00314100001d039100800103840c0c6100a50080c1c21544500440508080303800082040541005001d6030404642c000140c541c0e180021242108440e141d0319041c080780061f22040c131501d413100030b0050f442240000d0075000315130782d40100c200b90702040c220340d1410340548661040e005e050281c0354080010703410200304021101d80200c000d00c1d101d020540b040c000101a900300c44d8050700e08070f40d81d40030f00040343c1061162803081e80545d00902824460258054032043d826000075014001050016041d03400c1c1000341030a1140c00d80841e40f0385880040000d003000c3c01203034005640e41c80c00b80420032070780c000c0d48 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 618496573 1250 618495323 618495329
    0x20a0b1302090412021515042403080f0d060b1914090111150c0a0206060f0f06160204051602010b011707210e2d07090506030c0910050f0a 61
    0x4005807603030f210341d0f6890302c141c0c0d00c0c501d0b014111b00540e121109032241048040d0f0080042c803035455403208a4904102c03c4460b00c3d40440010b00c250b8104807444007203034200d541141e03044040380e0b0700c99042c20b940013030302d1041003103540649140000200f20200040b014040b4468a80c40c1c0504014052100752880c802c800040404807006202c01c12280d0b120360405511041100c0584288444aa41e00f01c0e0500040d140791900000c04a071600686034100101c0d907100320101c405501e507000203008110b01c0342c00c00034003601894000800218903c0700d400700001c01680904200400e2030440d104050300c5c00a201124010f5080c504025405c4d0f209840e11640c0c05070300ea0a009440c1c807840c005030f03024a81150301c4a03003082e90b9403044c59541c03154400c01d44100c0d420b00140126001c24200001681260940d21100108000d0703030005024000a00c0c5054a2040700001800c0e259100024601405100c50035800a1038a007003010410148542d00d08480c0180c0b2110440614101085a2065240 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 618497823 1250 618496573 618496579
    0x1061b02151c05010602060711060606160302070b0a210b1302030702190507060906090f0312140d1a040c0c02040902011b0311100902010519090f0303020a0b1302 71
    0x454504568a207200204a1100c02412050300e01501202c0402070340d600364000005600610104100c1c10341009400c210300000c1c402428040c64010005861801181007080e04001c8070650902014001c00481c00508040c0c44103503200d41c03801d500201301204400c0000c031000c1e01e25207524240405802884c0002c880244800c00a04503156450f001b50801842c003c218840c44854801d148000860030303114902130700241c10700030b05000300540490610352081082181c0c17900c082008000f109001019a13600c10500c0c1451540c10780d0441c0c2c4629400e9003c030843c50002500040e048055110084030210712000e005e020101d6800c00086440ca407600b04085801c960380140185820f5000702521481410080c0042160030084001030540303001c12004203203032000307610103520100083c410700340d402d003014400c0c2303009a80000d240d40190300b088409000042002c02d5801d0003000c03428090301e0341380600350405641c0d0400941d81c071900101550b04014120200b403078107003100311594442d9005 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 618499073 1250 618497823 618497839
    0xc112e09060f0819150806041e0803070f140307030209010305070f050f0c0715050a08090712110f0402160c12021012021909060206090a12140d020f0301061b02 70
    0x3c10b4100304020104e00710500d40c0c2d1000025003034062044000070b800c240d4010011841c1c21300c0c0100052001c0701c007100d0501031105921001034461800c80380c0c84401494098000317007509005480d4040b00030241803607a071000c001c0000c0c03903504d50301400644070260b07414815502d410b18152441c0230303203070144000038404010f4200e080c5081002065201501d40403228620f42d9003580303510340400d1200c000c000680001e021410168004481500504070f80054401c1515107031241841d000448001403c00350b6090302d1410645d19030744481c80907180a4001d5540d0403100340d1900082281c0a0111190a00d00a0100d50820400c0c09028083e50103072010f0364021070118262402440500040c80e050740070855140103000881c02d02c803506201d91100503105080c0320000e824030b80c004215040940c40203403014082909440d0f00d6034041001d052203031420b5460341244105c0d01c0f0b04040100f0003400040d0b688104007100e80158100d0310556504007142c000e030004e560341e030b800290010703500000f2 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 618500323 1250 618499073 618499081
    0x60103080c0304090615120e0d030b0a080d0801080f06060d0f050f072d03110625050a1106030f01090b010e03060f160c050a0204021c0507090e070f0c112e09060f08 72
    0xf0b900052f030b01c150023000d4400456a078904249050043d04640380040c044000401c10b40f882080b051600003840d4000e0141d5140c03280100e6504900c1e00340282124482c0382640c3c05108003840074003105c8424409032044a07455209a41d20b07405816a8a00c2041301c0075103604011641900810550b9407000481c900944c001040142030b0b0012081c8000a4425003101c0d00c642450800354a26203204a001d0982c440035030402908038083d103040a80550002c008002a080300c4c86051030559400040001d0020340728001280d1961030421003580504c00d1009204101c0ca000d040c941c452480c094000d02184c0002d1011070f40000c20740b1005003960b00c40c421a8006141c1900908080c424201c8042c0724140041043c0c0250751040e1002d00c04117500709018040b6002601b1910390000c428107060f07030350341030340c4030020550041c14038064101d0003501c0c5038001603940c2510190b48011103640c101140d20010804641c40c400c811800804600e1500300010643e0007101d0400100c0b0356901c0d1580c41e541d03 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 618501573 1250 618500323 618500327
    0x1f08030d02070c0e2401210c0504080f070801060501050c1c050d141905010f060e031204030c0608090105010f0b070f0206160213050405060103080c0304090615120e0d 73
    0x2c071034100e41c0300e408100c000c03800c803c0318101c081c41808000c0030340e1142c502c1c040074080341880702128641049001481c00d07a1541815180004e505e4800c0000195005ca2110032120f0340150f4104c0409801000704641c22a00c00140103c292042000200502651440151514071400d0f40d440303107035000074400b41002e81c01c1c00580f0000c1c518901702280341040c4010bc5108a800034442d003001040d00400740b2030018100c0c400c4000440020b08104520b50401100384000005841443c0400451010400c4030b504d0a100c0d10301404c083c913145d0794031107840c0c0c90300d4032050703005020701030004054030005078015405014003412940103c9485120508050904121362f0203a03100352080016140d00b24010384441005003480b20103a2564411340c0d200303104000821200900c0710440c00d0901082c8000b0400124580381100d900c0101c1c0c0381c0d20350103080742c603056000305e40c080c43c1200d2600400054440e05074226121519465481c0224554201d45ca4402c440c071034843c40c00564040046a01030074 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 618502823 1250 618501573 618501577
    0x60a080d05030a380a0315020f0d0203010305010b150703051e070b090f0106080307080a0819020a12051f1a0d050c04080708070303051606020f0c061f08030d02 70
    0x42e0724201040300400120103485030035040807040c013581030000041003001c10111104190b050115100b8000900d1034603141141201c035407240302007a6000400303010450403c012160341200c5002c0542d100c2d81d407400c0581c000c10180303141d0f90080c2d81c0b049040c00e1a0700250100c940d1164192681c0307051610103910060300b40305038000000e01c0081000540045079101d0200791081c00d420008180d60601610541d00750340b6aa44484420340c01400000c001401035425a40d801445140c8100182c0d2803120f40d0031405086980c403010144005001181250300021241a4207002e16092203980c03111030034a03080c542c294180002c0341d901d1180600000e040e46000e800c0039088421030a041c40248928642255030a40710540303664400282000591401d00c4030b940104036540181074a9861503c01600910501c6001c038030341c01400280b50b04110707441d03045d0b40341c0505c20b201d416120309284000b6952080260351204002600940034225a00051540b4055440f500055401c0038099500c0c0c1c0083c0d = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 618504073 1250 618502823 618502831
    0x5070903050a150c05040503120903010204050d03030209010e09150112020c0708010e0c0901030c090f020715090b0c030c04031103150c0304030809060f061c080a030212060a080d0503 80
    0x1046500040420000c1020451041c0a031100708107a805a14000c4120391001200384140242440100025038020640f0700143c1200403a0300d03500c42803007000900a200ea0b402190b440000030b104402816416030152413a00c03c02c0e240c0942201a00c030030010240070484603401c600e100010b08943c49c0d4410002582410b085000160034904448265810038000d138000400c0b6a64032444900701032002c114200e805541030321000e6565042d9116042800400d00455026980b601c80041890795154121160303150403482800d1a026110641400f42c80071070030a5401c0341c13103400490140891002200d004407541d000c02841d080c55a034a25800c0210800300e0303039040c01580c228510b84828044407500c200c0c8620007480d40d0b8605494040e0044002400004040d480b80c02008101190700360030f207170000d00c100c880301c00040c0080e802c01300c5040e90483c02000400081035010145030550098010101020f0241c4031550745d070750074030010a2440c401c0b081158000007541010786e00a00046801c = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 618505323 1250 618504073 618504077
    0xc0a030c051309240501050d02030c120c041a040509010605030c010309020a051f140306010801170a05121c02030405070303050906040f080c040c0f1e170a06061e09090507 75
    0xa0a00d00361281d104d40589004a464000001000d48000c5001440780d103015040490785207620135600c0d00426921210502c2c428041c07243d8148814071001c0401c28805018801041440b08005c0070000040c00d002d4542c449002d603003400c011400604041c040c0318280da001034014210f00d014400114041c2c130300360b42c090360840c248070740204003a00c9600d082c0203011103003032040141c01d9030200001c09080c07040c006030030840d000b8014400c281e81e22641840c110382c410100308903480b90b520285424090220f800500303d11a8910718800101c05e180907101e1502400240072055007010380751001d9220498000f0b1503030704009003d10020707004901800300d421010300054103241d00c40c811160344810387c2c0c1125a469021001c840103c0c9018020700046c40300902d808000541042c1015044081030f031841c00e0216149551300104c00d20600030030f225031110050001c0c141c00d013540c407040240503d000d2a400039241c917024007844c1e411000d107140d800715aa0313514036850b890102c1030402404c1c09400481 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 618506573 1250 618505323 618505331
    0x816080c0706020705010c080714040b030712050a240305030910090302060d0501320904140a08030f070207050a121109040602091201111210050904050a050c0a030c0513 74
    0x20602600c09000301511407400007032001f070345200103441800000e2020003082101208800c2220146e401d880480b107003482c00c1500c80d1910b110982c1d034000ca03000d0914035545400e00300f018a003900d820040302103030003034400200800180302c01da1038402030703001c0501540c0c0100800001c0d402e2400725040a00c03030b40e16086152548990003e200750b4050171580c91082c0d01e07440180809400c050070900d03514810004000d10560840a44465048140705148644181b40c002402d124042102e00340050b00c00d000d83d80640d5081c90850000e42040c0c03540340450f944000003440f41c0740000b481006840000341032242c02468000e0055100d10040c208441109a1003054812074484401d0240520302c5220003585908016050150b40304511039001d0030f6030704100b00708640842c09004c0314051400c83d03c89001035940c481425062003056800350b82c00110000401051050215046442c1c500c50030541f200100c000c07042045c80241c03808040c0503d00395440c00c01280c81c00c2e42c0f1020312801540b0000c5 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 618507823 1250 618506573 618506587
    0x1209080702091f1a2a070b19080a2c0f03090a0b0c01110a0302040815061c021207060807110105060108072a1b0812030c03040f1e0209070816080c 64
    0x180c22080c00c100151403170f00e00f6030fa0103000240070b1010b0400760610380411400d0404841c2d868400b19196280c05083c00f20380303000b08405038001e0300541994003028031714425945066908480c0a1480d5400201074018801421094840402152186100186141040c0e802e0013030181c0b82d60f101071a021415035a0f81c0c4204103905074100540401d501d5a1401a01c880c94400d5060a024051401c2c00114070500c003005482d59a044540309003400e50000444d005815101044a84030b80d070240c007240e0311882c0c10005d410b40c3d0003a4a3381c41903680795945552107010f01001740c00c1ea481070702c2c0079000c643c0c1c000c0050585072007080014000285034800c1c0341c2001c80c000102e00b140c2d40d95401590401889980441000a104490001003000000a0140b031000072107600303141c000540304606904000001c034040c082814940c500c0540c009500c10340c0c0d000c940700d10038502629518101c0c012401d80380010001c9000300649072254402c50089000b0510581c0b00711070300c4000802c4070707000b14018031001c = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 618509073 1250 618507823 618507847
    0x304091d0f010c0e060a0212030a0e0102071b05030d0c030804020a091a040608030f0304080c0f061807051807081b0a020120030603100902011209080702091f1a 70
    0x14041c0740c0c40c0d4000a550180800014442c13021548100d024403020044010300607400184101d0300749084580a813a07803a4105280080c040c01e1600944560004c01c0300002e110645281c60401c04482c02c4000032560380c1d20516448442c1c000704400807030b0301f078542180442e016990f22a802440209940c01d6991142c22107000c507403030309480c2034080213070030014071090034240304510103840c1903070003907003801d0f10344150600390703c4003c2c8001e00301c41000c90741c030140070020094100c0441103402030754071134640021191106180c840d4044041d00c01c0d0300001640c2e0400c0c2d00c1e07105c2c0d40520590b10b103a85664084055a101c42c0c00780810304804001041c0002800d044406403600c1c02481d0700116044101c1a002c100d0304411032810301c2c0e0790a00f042070041654002551a44105a00a001c50721300b500c0c1c001640d034028102203802c80c1c0b40c00c0030748550400103404024680c00740b00b110011500d8030340314040509a0010100b121175500c485009018104904a404400c403a006211394544407040c250 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 618510323 1250 618509073 618509083
    0xf070e040c03020d11090d020f041119120207150b1912031d0901050d05070e040305092409240c0325030906121b0503061302030103050304091d 63
    0x2078440001d0307002c1880c080c040034030f0007034106190344510f60b942003040d944001948445080b00c0240308000309511b0b0341c01c07511560040340008a01d940025140c0c00840031010200c0e250904c600009a100014030400804901c00e0b650901d81041d002c805080700007629a004110750503000b0f40c840b01c115801140c1140b070042c5100540280c207403800e000710f41132401500b51022051004019014024040c00e151a480222030440c2c60454008040c40c0c104c1c20318506100c0d840c0c100440b802660b404010034107030844001c0c01242d00c20340d100c102140c90748800d440b01014610072551051005c110340e49003840c0c001e1521900c0924803442c2948259100c5141c81da56201502400c43d82c0c2002c1100c1c9540400c403a01030202200d41400c9411854079540c00625400b01d60068005000414600c1e02140700147d00031880e021762000d2548052200c200080d1058200301d84071441101591800603c1440c02d0007924101da074000c00460405090900711070181107001c0c810901404d00c001100e080c5081044 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 618511573 1250 618510323 618510341
    0x10e070b09010905090f0c160b011d07030b0a05042003010905010f050607080d020706060503030307080406060b091507030507080f030609130b13080d020a32030f070e04 74
    0x14596540310007a2002406842c1164003045c41080781c0ca042000085000c1419907100d8000c8090350303603800c22092080c6010715103c01c0076040e682c4240c000304401d01945030700195035850522180456441f54402c60a0f1400e40e062150412800c040030010b900300ba4018000601d81145011074002600d59882c0003a0800d174081c401c5075844200421081c655201d00d0b071f01409042d200c1501c0c000b0641c680d4031f161312405580840b100d03800521407040c0005980800c001d807000805603903481c240f0a00c020100081a541070b600303940b5142c000101a1100412541003a074007a0910b0f515052102c5c0d01d411507084907005605100e0104403450000740403038020051081181100744c0c5908002c028007841c40341c02001950310300702441a0801080c42c3e03202d865484003411040102c4d14225181c00082401001d850701603c1c7c1c00851044055508405105401d6074060400c014a0780c0b070300c8880e2160300c01d951441c5207042042001c80c002c40480050a50f12680d6800c0c4101c00000c0180810200c0706404 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 618512823 1250 618511573 618511589
    0xe0111030a0b010e1c0807020d03020a140106080c04110f07030215010501030b010c110a0801050a02040905162307050712031206050603130510090b060306101a0c010e07 74
    0x204000407086118600d941c140038a0403545260358107011a525020f00e500c045201c600a00401c02041018000c0310075096025084083e803501c1c9113806555407500302c80071100005200400c0d00740090501c500000c41d03d09000921411003010306105c0200084020001002400c0201508401010740105070040c800d0b0b00500381c00c00400480649800180c00103030415007484403850542ea0b100c545120306a8002900c82610251400050340c091030560020003e0750070030040110858441e4044d00499035101d4041c44183d903010014442038240240c00e40200e40081c100c10030055a0382ea915407554520a01d05282c50902d840312440d00b409544212600860000304100300f59110b07000e80496107a100c002c1c091b0b80e00300700000b603907800002c000da460708038841440700c10b01000301b080107503482070742c4410402d07000c581c1400b480400040b0764544c02881000003040003041c0c640a104125030440745c03000c01445050000341519404200352190b03540d03e035186109440020310400d00200120 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 618514073 1250 618512823 618512827
    0x303020d020f030f250203010603060531060b030a0c090c0e19030809010306030f11011b080406030902060d020a020c150906041404061512050a0506100807030e0111 72
    0xe00000b440c0c21180c00801d00c15030014848480600c406000355404200103002c01000b0405202440b80c1054030054080d5041d804c1c89000014401217500040c003d0441d4800750803412079244458660180d8080ca820642d01c11001d04c10115913a03500c00e80365850000d0030b807000210326445418046559070080c4100a13524020071450b1a00001018080c0c0030a40d09003408202020000105404a110142100c40d000410b141568840e510240185078440c0304103c016456041c500c0c0d5010b0030080107030101d5001e03545282c0e003a01001d200d4000551255035a8501410184220064950260201d8004109216007980e000e0280041e103030642075580180101e2664800300540000ba460508206105c10444001103854035000c642c15203045409001c0403c1014000c0343c018011b640c0701c2d21030708180320762051806900000c00c1001784606081804607032540a2050112081900c20907440318842200502189c05805003d5001078542400242071504034040c9094078440b540e10f88c501440 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 618515323 1250 618514073 618514093
    0xc0b04050f060a1e0b030a0308070e060703090509090102030c03010308070507030212010b011706101b0525051c020f040b040606020f0601121a040503070510020403140604080906180307030302 84
    0x500d0980026a00c1803034001d05c54001030501003502d07844004070190030060004001303040c05012740050142e128010f4101aa80c0700c05050041103849140075003845000c4220100e10400c5050081d00d004400c480c100c646180d00e90750b074100042d4041e0000311000d029400001015035500d03090043c940480d2800400c00000341c0c40010441e03221401c49000326400502446031a4407604200107400c10340381000da0a900b00700d48800c40c41d004580b0000c0051064400e18803443c9011085000c031180c4903089142c29076110401c015040301c1240300d900c90306030b481800b4005890841c0071001d003043e000d0400200041004003007030075680b10b03400c0000903030700040ca0a000c200b002c005c80c900404541800200340b24044c4d842c188270540d0860076074110200d52001c181030101c2070080780e40440d401421070f825400c4090510780030350440e00c0191880340e02c45542241d02d45021940a1240da8416811480e10394280204056030b003150203180198511905541040d44042000901a5001c3e030001e10307810322 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 618516573 1250 618515323 618515351
    0x301061403150411010e0f060408011e05191806050103080306130209060a0c0c091406040e0c180a0f110306090c070c0b0d0905031612050a0c0b04050f060a 68
    0x94030040301c00ba907070101410040401c0007072040408400b401d01e4280702035011000014200707141c401c0c1d2075510940c0010009911141580414007100008800159103550480c7d102d00320341045603c0c6040e8498150354000c41e50080c4d12003441001c0ca14a1154841c4061f01c512040701c10036003089174500800401d200381480d142407121404805070b4002d620b08030201002c64800d010b108160350030700c0007129104c02001051480800500507400081000b00d0086110350120031003078a81a010b1440c0894040d807622020500700c6403414040e040110f80320020550582c81c4400070103032405203941e500540306a180d24010080c1d00440598026241d041c80d400300210750801803c50942030720100030703803c00201881400003c0311581d1441c2c3e0385508a01c0801c002900105400510038040080c4801c0709242511020314600d016601000c0c16074616032082c0c8a901c290308100300490101119007001520303500e180c40d4030900c248280c40d008a950110949801c02c1a50091740c015218100310304c03204 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 618517823 1250 618516573 618516583
    0x100c0807060f09121b0c09020309010207021302030103020f0109080604110a15030203011d01120f020303070c030b0f0601020708031e0c011118030d080402010e01111b040f0c0801060c110301061403 86
    0xc40e100020014564408640e080c0e14400c0c0c925054020001801c2b58100b0740c161001f00d40c02500c0d07480380d0400300f05000002d6009010032031241011603410001d6500c40e040c6003064840790402800e40b6201c42d1510b2501007041c1ea40031394071911980020925170714400d00301f161326813542c170096180c0d410031039070075883c1548003440091615214010443c02c0d28031280d070303280345030024034041030942c40d8000f1900310701c40c103107014040c00445078001040105080c00395101c0c0122000014440d01c41c00c0049856a42500ca2140594000c0c070500c0440b1240c8900d050b41d25240b0a0490318007030b4225541760a603480d0b001c00340e0520501003a03032000f5006074645100303031500480191644101c04800605550070150010381084000348a80c24240d024244c00034508103a602168403103035000d08030354000742845482d640940d0606030a0010b40c400b034029044213100a40341e001803a0300b410800c480c4441800d4082d11303513620780900b810481e2001e00c40c40014006070340075200078000710b1042c9841c1c0 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 618519073 1250 618517823 618517847
    0x901111204121e050c0d1109040b0108010b041104061103040312020c03071d0708072007090e0613290106090f1413051906080f010b100c0807060f0912 66
    0x404421000740001402c04917020130002e00898809100340c50314104046168100b80030507801c00e004030280030138403540241060403189614000d10005102c0d4080c0000e03911412a03060300910700384070902040340140000044034240408407424a5501e84441802c0d018481869000d60012030fa010f0040c242400100f004c0c0a4040b412019003e59010040348048024400d100300306440010662031031090950000021007108091004620982045d0301d8003558032405c0c0c0030916000c9844c580071008108944a5401c040480e54140304980b109400920503112484828644000039004a6807500704540a01034030f40c0d40b000080c2c10404030034200700c8d49030049100790030b00008444151b80c80989003424441038030340200781a1120856401da0506c00401d5101d40e604158020490260020380c261000c09680b00038405000d00500380121500c820740c04000103000c1d41035010110301c0d0b0f0340040250604c40c03000000c0b20828602c404080320300c021f0049a020b10305640b4200702c05d60000c100c2000f = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 618520323 1250 618519073 618519113
    0x4050c1e030f04060b0d063608040b0304170304060e07051203270307081b09010b040e04151a01020f0d02032704061212080705090111120412 62
    0x554102002c1c0500b400c00003c200421003078032a0040b1285482d48020a000b09078482c4d000d000b0700c0d08101039140104c20306103006140e003229049a512110341010340a01080d00812840e1425003441e103503001682c8010f200703641c860918404101003000c62030056100341d0080300300140b42c25000405504040d00b55008c070f0b204606000001c502d40c90040107c2d0618592034070140c18012845c4503c0c0e0840c5007d064079075040c040c0700d40004500764045200700e03005010b000904048d980c05800c20021440a00500603802410302003407041050201140ea00a805110015211400e0028800a4401514580c0c1070641a0b03e44120b01d942c040005100800c0c10b8406403142d150200d20003503907405164403030300d0b0308070700750f03211031881e0000c07038240d03003c801e0090410320203140c5031904a10200030b003400848840080341d04000041e8881c04a01d4024115581c40302d00d8204d8540045483c00c10090b500031f028002e0168020305580501c00800c02400854074102c40940c3c1c0b814101000e40085d021018 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 618521573 1250 618520323 618520327
    0xa05220329101401120c03060810020a0f0c0c0918021002010c14090a1d06030d020604020a0e0903130e1006020a050d050f0c030c0a140a020d060f020904050c1e 70
    0x445031440794969066030580c58641c030400c0030041c012108454140040040311b89003500e02c14480303074540c01c54015a94190f048614050000c50740034224402c1300904000101132001141c1103910800302c40809030f000342c03403600b401ca0711034914070121100c1d103800e100380d80141c40c800c1e8114148402c0410413119540020000050036000c080d000d0b406040d84651499000203100056036501c0c00d0789001307440a00101207000390072091a01c0032003420b80e84107100c0e11400f00228800c91000450320b104076030180c0202e402c640381552a10fa05000070b00310003032901060050b5044001015407500044c100e041c041403550900300c0c080000c3e02d046810000031500b01c45030000100e600018500928001884e010740d4583c0d40704464045030144a442c04424080001d411401c00800140c01c18074600640c001800d4180c0c010b50f450b070f55005000b00a40050b1001c0d10a00420129480358011000407000580751038420000141111000c0707504024138600860340d4402c21051059141c11a03803010340243c = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 618522823 1250 618521573 618521581
    0x807050903060601050a180f030b0112050c010e0423070329090a15060c0b0a021606200403060f0c080402011d0a03020d030302180a0b0a05220329 64
    0x180c0c40780c0004012038184a800215458442d108410403065402c003921101d4209403255044c42300c00b4502d110035142a80044000726100c152140d05000c2c49a0000c021307c0b5056203407005444010302c0c4a080e950059070341810180c46040049a88410340140303400011030310300804098101d80c2418094980d0311155181164400b01249841070044000c466402132681d500f0b6241c0c01034841580c900904080c00079000482d80e4020142d203403502d01c00d24030305004e5603805160008074020403922801e401c0080c1d080e14003144165011080511345508620144880051100c0507940725500c2101ea05507075080303045200c800e40c130512032040194076050b13111741096000240030301c5c4000441c40745889100c0b000300362503807002c80490003540c0c05804805681210300b00900203401c20b801d0014032080c1150b286000380b4069280b20241c503000100c0a003000810381d01103c140d0001c400302158003100a03061340204000030502c0700154410701440d038401c10b483e03c0b90396141992082600c06140b0b094140 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 618524073 1250 618522823 618522829
    0xf12061505030408040f1706071812020a0306050106021014040201050405130e0d0e0f0d0213091401110a090f0608060d030e09070806010e030c0d080a2001060608070509 74
    0x5a2692101d140c80e5859843d1414248060f00c101d81c485903102c031045100040500c454816580c404c0e0012050311000d80d41c0400a59040d9500c1c1c05151101164110900003041504440000180003034201e484141c2c480d525503040301c2e020780114000d41e20000344a0fa0342a01d9009411001140c00070405184c1803541c000f07003142c000c5008282c801c0e0105904e10300e010107203a2046200008500456070000600000505100c000c001124000c0a040392214001e003460394081c03503c00e03030142c44019080c40090f40100200b0a881040ba0400c0e10740810700300ca20000d0143d0b002e080400031200750b480b0f2842c0c101034a42c0e403e6034002900c140d440c50007004070b1600280700781d034002811b0b9403010f0081d02c00e2401301e9181c0050703404103602c484050306120041c1e41c8400040d12851b002e895107405100c46000309030b03030f44000d01a032650001c60309195100140f0440041d0110411504000d40b0215020b50564001080c80300c1100c0c45030740d601c9040010790380c070442a54004010781401c0785011400313404 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 618525179 1106 618524073 618524099
    0x1a04020316290c10020f07050a08030702010e070e040206090a1d0609090f280203060c27060d0e0c0402041e0501030b0303032a0a0f1206 60
    0x2040000c0c4995404407500c8103d076000805078a2458030000f4003942c8040320345442d2030000c3c003440c1c00080082015044413880b50301c207140c40c5d1802c04002401c4614800441e460342d40b0456040240a0701540308a400503016100f2650f54215480400c0609110380e000321603203100075a207601c0c41c0b07280380c103c00d004403c2140c0800054503810a91982ca20782030201c80d4050f0460040074071a21849010452140d00500444220108a80011f410660200c948420f40320000441c2a51507a0040c07114084110241c00743d0300d1500d0359400700300d660044508043c11681e07921503203504200104407030110f03104000c0c01507650f02c1e158903004104806204611207040907030100403900358003a0203000c408074000340c019421580e4640e42c01e00b410340c4003660620442c220560500c1104202c90003030400c0907040c0c48400d100e00b40210003e15101c0801c490b03000a84c5414418088124031350f031 = true := by decide +kernel

theorem cover : BRFrame.Cov 618345323 618525179 := by
  have h0 := BRFrame.cov_init 618345323
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618345323 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618345323 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618345323 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618345323 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618345323 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618345323 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618345323 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618345323 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618345323 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618345323 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618345323 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618345323 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618345323 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618345323 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618345323 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618345323 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618345323 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618345323 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618345323 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618345323 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618345323 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618345323 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618345323 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618345323 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618345323 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618345323 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618345323 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618345323 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618345323 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618345323 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618345323 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618345323 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618345323 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618345323 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618345323 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618345323 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618345323 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618345323 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618345323 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618345323 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618345323 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618345323 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618345323 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618345323 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618345323 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618345323 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618345323 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618345323 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618345323 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618345323 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618345323 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618345323 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618345323 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618345323 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618345323 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618345323 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618345323 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618345323 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618345323 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618345323 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618345323 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618345323 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618345323 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618345323 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618345323 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618345323 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618345323 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618345323 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618345323 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618345323 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618345323 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618345323 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618345323 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618345323 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618345323 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618345323 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618345323 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618345323 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618345323 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618345323 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618345323 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618345323 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618345323 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618345323 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618345323 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618345323 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618345323 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618345323 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618345323 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618345323 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618345323 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618345323 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618345323 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618345323 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618345323 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618345323 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618345323 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618345323 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618345323 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618345323 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618345323 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618345323 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618345323 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618345323 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618345323 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618345323 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618345323 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618345323 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618345323 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618345323 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618345323 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618345323 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618345323 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618345323 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618345323 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618345323 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618345323 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618345323 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618345323 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618345323 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618345323 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618345323 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618345323 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618345323 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618345323 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618345323 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618345323 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618345323 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618345323 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618345323 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618345323 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618345323 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618345323 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618345323 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618345323 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618345323 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618345323 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618345323 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618345323 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618345323 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618345323 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618345323 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618345323 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618345323 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 618345323 ≤ n) (h2 : n < 618525179) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
