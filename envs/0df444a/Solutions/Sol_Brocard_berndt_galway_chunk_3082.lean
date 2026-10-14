-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3082
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T08:36:26.905401+00:00
-- url     : https://prove2.me/submissions/368cf201-9d8a-4a61-96a2-8653f1ac0244

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 554136690 ≤ n < 554316546 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 554137940 1250 554136690 554136701
    0x80307090e041a15060d1d030a03060306060602030f161a04050102031611100207020303070c030804080105011d07030c0e03061806010519052e09031109150d060e10 72
    0x1da81140f41900d0b52810059629440c40c95043d680c03140d400d00c0142d0b401c18066200c0c1e01040354900070706000030406841b4515640020172008000303501c502040c010860b240c041c0340000c0986000660400b0030ba08030842da28041d0005401c4a41a014504428031288880308024000300301050001424181444c6003c0c0d8011a0030360040d40c105041241c0480c461451030381d241c403001c03014150045828040740080c1d409840c0c00e03641072000340000c6022800144e00c90000f94803660b901d950fa10f02d8074140c1400d65005030701405074481c4001c540e40b1824040300040703030300203024507001600c8003100390180c80c001d400382049078246c86880c0030050180f4918151985000c5a2000c6031710b141ea80d24104010160f01c00c41000c818183c0c08002c000f1070422620030780071700da202d80d021120782d0311801d0540710080d90351803c04005081c548080062150b10396491030245001d540707071011490003044002d00e00175092a0180604401c01c8650148505644511160140c1e035050707800b0740e015212180068903 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 554139190 1250 554137940 554137973
    0x1e220b0304110d030905061c020d06030c090c1d031e0f12040b0a0e0a0812030402011d031b0105160b01060212130506070c050d3507080307090e04 64
    0x1103000780381c0c102d24503145503e0b410340c40d855680d80310f2150500707090008070780084079036502180c10130070321035213040d151b002600c900321035400d000840710301d1820300c1d140d410385540c00300316100e28103405003012560091144035070345100b200c20f807401e0583d6000309242407034206811180c05607900384c811010502041001c3c91003180c0c0d00f2500300e03182004281d0071a1146104904003035804100a05001f0f028403042a5420002000d030300e095556440a1824808481d19000243d017000082008541e0810111122508603255090305000d9070004280d407404040070b00210000086401ca441d45c2c0305404441e2040198200000d6118a0389044408503030203004e00000350041c6201010040011410740d140745085185100080f807a210500030386602402060302c10703c2c2540030204494480b55200d51400b031050050404840004401001703110855070945615101c02c0c120740700c2c000c030302020380c0c842079008903100b6541c2e00d030010160b406505540c0201009d5004904110600c000090a401e00341c = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 554140440 1250 554139190 554139203
    0x203070c150b01021507021c03060609140d2012030d0e011404030309020d061406100207060e061305030601080318030613112209030201111e220b0304 66
    0x488118442800b07a9070400c15090069014550a0f1003800e045d140c01c3e83c0111081c01501c5600d0182005030822601030880d050100351104002c0081641c004130441c0101500c102c0780e02042840800903240000c00c0c0000381c030755070707170310341044104000322000b04109140203180024602584120039100c0c0c2044030420951450040400c04004041c0104032440106140c110310035511030f0380640080103422810b980283d820a400000140b66200340c40d10111041241c5103903141c160100311910074020004002c541200b9000c0001030340114001c0c0b000300d401ca802a40751a60044088444152a031210758180f15007000054070081c040001c140941460640282d107480c0c11050599900c004c0e5580403541c081081c040001c02c00503080f010340610000c0101e0002d0645000d054800c0c07044039007000f00c0542e1181c6071800c040d0240304450000500c881c081c2d0a11300110840002200c6500e00038484041c00207842c1d15000b45c1c44030300300080626002c4c84402d079403120900b0b861038100310b40460f540c = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 554141690 1250 554140440 554140463
    0x1d070e0604140c03040303020d092d050d120e03220b04030209070c020303120901051504050c18030a0516052b080c07080f0a0b07050a0c030e01050d0203070c 69
    0x29030030710340075200ca900580a1194500d46035036a4204181d0300c0140140c0401d5802d200c2c01803040080d00410710303030602403000c000c804100c0c0607100d00c020b241150200c0d601e000b0008650002900440d2140c101c05007810000074640008810102411485540c0c116600000030790742d4512040c2b940c120255940c82505002c010b40f20324034a06c96100300e01020354000008400550014421600907290710320150035a41081c44844214011002c00da420b03c4459450f80e0400a2a0040304c0c0b19075010076003190140a98206036410014a21580309101407512041105580540b02046400030659100d01107c030f030381a00485040d42140b0600031540f00701c80340710842c282c1680740f2208254000b15006000760b00640d030355503140e50b60f02c003641d00b101034028404001243c0100307021007d400c202c6034028000d0542c441c5000d040d81e600c000d084409020003840002d04050780b120303404040d00d5160802d810b80841c01c00060300c03d4050350740070b44000c038000010011055404113007611003a1040b9540040d = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 554142940 1250 554141690 554141701
    0x10b2e18050603071b05010902010e0d020a03060902060f1c0f060302010518010e1314100602060f0403020106090516030c09080a06090c0905010e091605011e031d070e 73
    0x20421416000d4a80451000a007406640750010056400030304da41005c5000700801500407080381106031040c0d401c0c1e59202428815560401950040c26104903181030660311698005500f1070700c00c0c080540150b5440e0100ca085480e11401c50b01b42303240c032500007134440c00d4850344001a03070264070180c400a07003450500f0503552080d0042505580e1305840c3c05040008031282901d00f5203190346054100301020003444440e4130b401129404e501c0468002050013044440001e0348004040c015100351061500d00f08a031075408118a60080780300380440b44141c489080407409404260810f58405103000180b26030000d0322441300b0100c0c0500e031018080350303102030f600340c4208840f4030038020260000c98040000498a500c040406481549801d404640740c8207218121131003600171350001c0c402d50092040c2002c04010040f41c03585034641c042c150a052400081145100100c4018011285600110320b240280c00ca120040b10f2080c441c00c1c0d40c01d1200d0002d0b501c00151142c03000c4001c0c2d0101042c2d = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 554144190 1250 554142940 554142947
    0x5060708030a09050a21180e07030609020a030b04061410050f0f0a0e0f011d0f0111010603050705120c0a030b0a09050a050618010203130201051605070906170604050d050c010b2e 78
    0xda00c16040c00085080d149048034488230f104005100004050340c669010441c0c18580c4003901001080795400265035600c070090104072802504160034030301c10b02d2080740446c3d445240c41c3d001c0650600c0e005442c1c080701c0707040c1e02841c001c1800c0703410460004524010040d9202c9210914141e044940d041c20403202d03801518031003200229041000c1039412003c1d26410728801c00b541d0984185044a00d07200b055503030b50300319505500b0480e95600f0040c0d04014516001030b1610420500d071015201800b94100003403d940490f12004014040420000e180d51640b40d000030348032900103083e02c45a10240c940306403140d508485440422000d0403103280c050605100fa0307403240000116100c11080150010340302c41d000144601914000c0500322800a43c1c248000d0700100000d10022031447d040c01c0b40100181c140d0380304075489a005c24200004200b000070428000b07000e03410255a1610b1b807641c494090848918401d4004019200c02066075074024280106802080400a944805103600310b = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 554145440 1250 554144190 554144207
    0x60c0c0602030a2003040c0e090a02090c030901060510020d03150e0405060a1505010819110a05040f060815040b0a051c020307050a08060f1e0c2205060708030a09050a21 74
    0x90081412010184064048e44d046503402a0340202150100f10150b1300080100c00110744144e82040d003c020301416840074020b00e0098102100c07401c0c0d07201c0c0e260700000d41d00e0b029000c54a08240d1551622034a03180390710780c900080c009405410209280c2030401580e2200180e4140c81000c0c039102d01c492141581d0380d010020396034143e45c2d0f207242d6120a40625441c200f00f604071480c0c0c6503102001403d403983c4c1002009142c00036125039841d03a28140c40340c882ca0300c196100c0e80500c00c02e48100501c1072489881c055003c4030031a4001071810100e008580102c1c03d680103150050548551920075012780310045210510071801ca4040036111400d02409503e140f04600c500c0c0d100001280fa0071500c1000d8a81c03148601c8a4400c1d1654549003221025405444050b4204800031300120741c5092115890000340300305440c861154540300200b90640700d40030300a00426000f00114040b42c42c5608030682071034014040300e02c5100c031800e110f41c400704201030f880e0403881140302d01040c850291110 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 554146690 1250 554145440 554145443
    0x160302030118270507080606030a03090504050718060315170604021509090f240102030313020a0905010b12090f2d101d03030c07060c0c0602030a200304 67
    0x1007045031910b00c8680702c003070242140010895800078400b8080c070a104a2510b007442d005000401e902890400303410b0800c080501400d0082c2c202c07065500c08640c100c02d40c0c1c012505e043c0c8000a09589802080380c0021622403c00804032041c0800240150301d9001070084800418058649035550b0080d40880290000d44841c2c42c0c00820000340076161070302c2d01030b1140aa88048901c1c00309030000145240345c040b00c0c042c64112882040c0f105104170586207201400c0c128408580840074031002035540c0c00300508400d145403010700c8000454070380c807080900800030040140a2540c42d20964142034110540c41c0c0701e85004240040c203c41000035a400703520700c48034054641c02842080d0038038042150104203c0032011894990b013651400c11003d500e4448045c00010201c241d00d02150420b0b140b2180e0150b07550007071040c00200880d4200f00d540789613100c0d10000d05414074800907502540e5146010303240302e1021007044020b4025800880e040598000c20703588d0701170101c0d05820140000e680 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 554147940 1250 554146690 554146709
    0x7090b09040b06010903080c011b02030309121c11191e080a0e1c18030c0b071109010306060305120304031205061c111002061902090d17031603020301 66
    0x21601080b0075004007904981d06240246a2645030380350409aa408000c4000c0d09a40d15039020811100c02000c13400e1142d903601c0910b00e98103204d0766503079544501d20094850030380e0014001809a070114800200034400140c28804000c640020071b215421440c104070710202a0174084117007034810b01800c401061144451140e41000b0711085445500091440d40d50350366828070894110380421075a02d0141718582d44801004010328010001581d640b0200441b000e402c0b018000210359080d2078040e951501c90320b41d00e40c0c110b0304202c1c0031007000f03041c4550403070840400132086c00069080700c01a2400359089905021003000e10300c045110450b0042c1c00242e0641000d0f01c42c060541203203420107802010b0100e03450200c2c1e408100110b840b6011500455115162101814005a03045050f140d0340040d04041c40c28403a800c80c40721003c1d05180c100d0f82d0024000c4c1da10358808403914020358100400c0510790600c8003038140a07600989815034054500002166868400c0c002c5a060b200b8500 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 554149190 1250 554147940 554147959
    0x912020d14070303020d06080a030e0a0b0f0c16060807080f1521010f0b0414010e070f020a1b06030b03070b090d11150301030201110307050606310e07090b 68
    0x45144075541c01456045007015001c00c84c40700181ca50380500005081d018001e840040b86516025001941001c41c0c0c41c020041000c040107100c3c45d06d4160f503010f4103001040d0b580c80d90081e05040c208a0309884020030202d8860300401d01da5486400b50b0700c295101e03142d0841035101e42c001c1c40080c00701210340d095009000b140840e164140380440700f00340280b07100348070341510140c50300c40c3c250b442075400009420b5980440d01c1c05450320b8041d00342110510f4140808550400c0c01c0c0d110710300f8005081714107210248090614152081103c50b0b815608490003003440000542985070032100307449190300180c20100403003414603011880008840340282d00ba0314040301242030007080d080d82c01060360307103860103244c00805454141c0c4403d04945003242d031076940c3d819440003500b0005042c3ca41c001540c400d02c43e04001400005031150400c904955004070489400781c15007003819588402c24a2740360102081028541a4200142c1c007002403083d00d80003620743c046002120240c440d401c0e400a1441d = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 554150440 1250 554149190 554149217
    0x9160e06060f07061a031203090601050f131a011e0818100614120d090320030307060f240e070c17091302040305150603100f0912020d 59
    0x80001c00541c03035071400542c20545903490b10412110001d00c17040803401020f010705018901444109544c00384403050038107505042c00760607615901406480d02a6245084459842d03948081c1e000422941190600200e0300c4650007100011289030902e02040740c1c1071a541190180d0f20801c5118881540d5004450b92003c1920101c02e0100c46a07010b140100b510a1504031024060f64015040d4110220b403211512028480c50664900b9000c0301500000e0352051403a51201b6100100c9802000d80c0403e43c669070b55541d01d0007225004103500d0300c40000d0020421040f5008043c00c12082c2c0820045111404048440082c244018103582a4a00401d000510040980c2600280340345031046820015a89143e00c501c11a0a01c150283e0013280304c1001c0c0c41c0030b0303884410000003150305508241c61a40c40a40d5500441100c07068001c5600001d00c00d0380301080018004001c0c104103100508150b0386110003170000303041c20f0301c030100f103c0e500b19589400081e00800c0444a40e80d03801a500c4003 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 554151690 1250 554150440 554150449
    0x1908130816060f0c05040f060e01090611011407080a050604020a120e070b210105011b0209070311030109090c050f0d020904030e0301020d0605011d060d0c050705031209160e06 77
    0x107a070300b1110345a540c0e160700c440c0900c91141c50131442c07094035000da41c1c40c1028500c60030010a50310440820030440711040061764818031450869815007000d00070300082c0794080c0c1c0542040704003042901180e41c05c024100c0d5000e0646c0d401040d9014080007240c8038442440164070503d5a00e1010500c42c01e6034003201c4d00690b20151003400c100e02034441c07442d1a1075008505603c4050203200c211040209100720741400c8503018010082400c000c81b12806030b0010321a005103803039029200e50024400240d1950290f00891903d4020402c41e40d503a603114501e00c002084804029252040365060201e100c0c20300b0380c3d0a0100e030000401c800e50702012a400c001004400801c00c808012405183e01c4040c1c81c2400600540c108002c00481d0b0740342001e000500d440e040d28000e05030700001e90115101612900f0032100140a00b440c04a50b00000c800306407054410a0801001880005088000d00da0880080b90140c4948000e4900509d130764840420f50110710b000e6104003800b801c0128800707141 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 554152940 1250 554151690 554151727
    0x120e0c0901171002030c19020d02070308030c09040c030606021b0f0409080f0a0504061d0d1704030f1a0c030103080313060f0e06010e0912030f041719081308 69
    0xc00c00b0031941d0020010403c14141d0304165090041d02c500802c0c3c0020318480d000b0360f421200c00c94401041c8010b200b040c000c2d42e400540c4030180c0003980000124031516254000c445a6080150080c0411003a02c0703001801081e03103205010050142d075000580540c1d14080702040c10200070104000c0b0343c1228100300082c2000300040381c010808004001010b0000310140c4624041625841d4a40e03180c518090b107640804110036503410704040c00700b40140e81e82e650b2100f0030340c0c0041210100840b2440c5c07454851140f41c2019124080d10300205040001e0955418240b0004003a003040c503444101610082d1300003804001d18107601400043c2c004031086034a880240d004240100d1607084605030b007000c4591402c5002c070240c00560040c0207044040c0080360304005204000d01d207101888102c134401c1e000181c80104d5400e5190301040c203004200c1c188a5940c4605808030341e4031850240c40655114048200d940424a01e41c0081d4003403070b2052820a0382d94100c40800d02e4102040c151113a000c0 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 554154190 1250 554152940 554152979
    0x3090918010e0709050901050a02040308030f04030912200343140907050f1e041a030f0702010b06040902032806030203120903070e040c15120e0c0901 66
    0x40d40c480100c8801d9000700f2000e4010816540c001070301d410103522070b9094540c0280f800c7d103a140100010000601440c080700e40c4540e940c801c401c082d0b111440c00f15240e2050341c0c0842840030940b002e42d424001545803168401d52380d44a0b40040c1e414090515444403025144141e440382120030f0300c0c00358901d61071605c544800075134020001316420240344864107071a4000c1c0f00d802c0c3d0b15039103140f40303030901e0010716812104c40e00f0524102000c640d101c2c4210310400840e840f0303140040c075041e60b480c0e01d0700302030700e010b400c000c5404c45083e0144110001e464004407501c040c01032904004c9041c440c0184591030140c0000341c8010f1410307041061240c0a07600181c201a0007100c0c18010941c0c6c039a400f4652038541c840050041101c6203180101450030b08403100f118030014007003100c86400d40e80041e038072040700d00a000b03aa03416961400d140f000208503510040402c01210b05000701d295200c09a403141d0802042c04014035089c2c41c0f5203c0c0c1c5d41d0610004180c02c000948014401c03540c01c0708c850b95160 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 554155440 1250 554154190 554154193
    0x70b07030f020c190302040b0d020901090209040b0904290601050403170919051525140a1b2909031204080303180f1b011b030207090e03090918 63
    0x40600002040842c3d032131902c5a84408580c481c24411850b00c0d01580c144081c003240e45101c180941c0e00010301c4071130188140c04e103d81c2e00141d605413580751600946009400107154405a103032604185280704880358a0340d0004c1e02c8440c9403200d6401d4582114001d0700180c2d201414582107684071440c585003039002c030030410004c0c0a80785465440c2209034905034002c4445040c200e20340800e01000c1c004840c4490300b0040188960140c01d401101a215644140b200c204c0c1d1541960618505280ba448550308840c004c03024007105025029010090b8848071240c258119590303002c011075424000030500000180640b00c42c1d0380029503001030010540b0040950718508050407450b6050341c130688c030022458101004100482031444100d0320483c42180190100742d02d44e806140e1614080384008100702c41807440e40100340d116030130440c203681020712704652200c0030b03080c0a9590ba036540305520040d81001c081d40e10026020007600d240c00c0e00034280b00c0494690343c0340002844907030f8820782100d = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 554156690 1250 554155440 554155453
    0xe0c0306010804231c0f050909130c12020a06030c0c0209041e0b010519240509040606050702130b0f0f030a08030f010303090803040b0306190b03010620070b07030f02 73
    0x80303180000003008a4070015005002c4550303030309080820400c08500c25420b00545501c136458040c0c00c00111260540115440313803190f2b88a00d50340b654a04407020240c44080c01000104a60b14181414200280211400030b986541c03080e044041d1a85c1020040008151108400050030304030981d50700a8420703c20444014a0304000816130b14035101c0030346040d482100100020305240000c2649241c07050b10060555040c10070140030442c1c12038203042024018024030055511500548440400080c010f212440e034600004000c1e0700030300300a074450040000089005022446004040080038000d40e440d00c1d101c00801c11005a043c400e01e0301405500b040c00c001030404c0340110701c01c0c100c81105580d01e50460a0040503c04036400c501072a510400060041500540640303034011811030710341d0703071b0340e490941080030180c01e961084013400000300002c00c00c2c0390810480c14019400100e1205e20281880300d80f696075500d4404c03120701c07000410011022074072034800042d07055142c4c01200c14 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 554157940 1250 554156690 554156723
    0x606030a0309090e2e060b160312020d0c05040518041707030c0b010f18020403080d270501380402030601021903020c0907030b130c0306030f080705070e0c0306010804 73
    0x71701e250840201c103603285914a21a032482449490702420812401504080b0040158016132650a03009000c0c8403024203180540000b640490760b150054060074440780d4a0000301401507042806501e10a0005040f9841500c001140031031040781c00c001080e02d1140e181300d2400081d4801c0105404100040c071610000c2005540400d0090000b900c0700b0b0500391400444640a10019100412450041104002244022040c0c90188290103000a14202c40801162204101105a10880768081c181030144141076004860900b42c00c210030228600c114401240f029003043c0c6034000104021000c40c40b030030154080c59003d0b9040c01182c0d03500c40240c1507071b500308103400703000c60050f407106050b411542006614141c0041c05401d0900c00700c42c140700040c4002e00c48410f4102010764800e0f8404a40303100b41c02c45002181c0003120302c15440d0050415260544c00300d20300383d80718400c96100180043c0b030010b000303100d4516480381a046403680001100c1310b041c0640140e90560690030301c03c2 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 554159190 1250 554157940 554157973
    0x4030e19090510090606050c0a06051306092003010e03040308070f02030f010c0e0609030d0c03030225020a050d020d110a050a23190306020d020409020a0507050606030a0309090e 78
    0x38010f80903903090030911450300384424155080c0d508040b080040c203110303d000240c0e0002c1c40304421580418082116560440c45c01c00724007001c0e201400b00b41c104025882442480c040d0070100154000d2240b4480c0d429100f45426100d001060b00c5555208000410111310300f074000d001000c1c803c2c400e001001c4c0e001d800182c41c10780e6824500d0000e075560441100c0343e039000040400702c80070a85a26050151210000f511402c030a043c0009112060541000b0107200350f040350b110401700304594090282c6107900148000d0842c0c000ca0062880300404501c0d0320b460405040b605500602011025025075501403407807000d154803d4010b070400c04003096a6031509941000b03090542540c0d100003400020703024080522540070f6010f802c4007820324003040c240c1a4034005032900814003507a509c840280c28030080c40340d45c0c0803032851480450404032559001d030003468603500400441c0d5203900ca0304100750301e0341010100100031480302c9e80200000d9619400401248210a0a4032020f000d840c0c54030 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 554160440 1250 554159190 554159201
    0xe190506030109052b170103020d06141609080604050606060705011b030c32070f0b09072904060c0602070c0b0d1802370905160804030e1909 62
    0x185ca260864400829070050312010030400f60480d46448078070501102c24021502606000180c02810084507000500096401c695901003648601002d41c0c44c0c0522140b01d40f0814045001c00100c64040010302c450001600c82d0061b038102015200d140c480004102d800c0d4800c1d075045a09540302d92051180030300a171000141502603840c0400e41c4040c2e010000c1c10051a004103265500210100b40c4010705403042d40746641c07403021b424558581d03450500c4140c2c6103247d44000c0500b083c0d40c08102c0041d002080150440d0341d00b02001600c1b04980103110140c042000e04c2c070013811001c1c001001410301c1400d181c0c0799280200001880c040a0f6141c07110380c494a90048a041c400000d2408040c0100d40b00c0d05459a00c4016592919403565001902c070030200071060700540d00014582150701c0644412101140344182c2c1d03000c00c1130755001c0c00e102403e001c803000e0003c010f4140c0212601070052509a200d01c2d410f03034880100d5247c480070080c0c004040141e407049a03034002404113600030107200b107 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 554161690 1250 554160440 554160463
    0x80102030c030609130c0303120b091e0c0301031205030403141b100c08060402031f0905090d09030201050a0305150a06021f090213021c1b090e19050603010905 70
    0x803142e49180020034042c0f100c0018101c9088200c1480110011030355004040041c1d075450318207190b01c4602c20f55690098103e0030082c6030310841075005c1c882c8103a90403001c0300015454001c0b060072540c2d65203000001e40801d1002a06002d9400641011184558011540107110b41030080717071034454001036081900200080707401001410003281c0030303807070070000d07030344514400c1030244046450b12900034030702c00000e081d4501894011010a180084070300c0b8100304030349800c00425800f9910300b100006010b05a802c0505030013101600c22070b0500c14854031007a030360180c550038600005460100c0c01050002c2100c004802100301c1035034036540b00140180204241d50043c0305020100d6146980351158101c4100e01c14a051050001615140c1c807000300c5c005040301c01a1900210712003500718002c502042d80103039141035440c4800e00c000c41d441c0d05054000e541d60317410180d00c8a91907403410034117031651000d014156000d8108000381d60811603110902400104610049075603851908211a04 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 554162940 1250 554161690 554161711
    0x6010c0602030f1504062610051003031202040f180e060903070303060b0306030c1003020c07091a0307050102060a0903020a15060e0c210601020a0c09020406140712110708010203 78
    0x6210160400740154401031350308403010007950f4038040b00305074400000383c1340900e40350100c680072840300d90600c40d622016946440620540c605042c01c40324003034050000700c001c600e01c2d000700038807006030348243c0301590800c090340c2103e1418004130341580c44002412641158407110324550003002409032600854456004544a031f149180203400c1e900c180d00240034803c0280204030084c1d9000a228201c19016500b0907180c2c40703c48412001780c401c1500d0161b2600c107458000604660691080c10200810355207109001c445100b0507868112501c07681e40140d100c040402c1050619a000d130040e28400c2c011143d81001030754a00041c80e011103d56020165074200400103502d4219510351301c01060301085180070b40200f104070040800e0b08024080800a200241069000704520006c00e500180304000403035403901c43c20040c0d0703c076000c0c540010b403814000c0c0110341f0404040d00c0c4155440301d05400c0001c0c00c10b00845101038001c1e10800144100e02e80083c3c0740b04207200a6006800b0900c = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 554164190 1250 554162940 554162971
    0x90c091e0b0f060306010c060204080309040c0f0e060d060515191707201b03070f06140f040b0304030225050612101a0301090605010809030a0806010c060203 69
    0x80303040ea4110514030300528103080055907659a56151448100803404030307100d544903198800122801d06181400030940d81c4000b502091400000000c0c190341c034400c0701c0038000702c5030307180040b00c80e01d0141c3c502c0d002141000107003070020b1510344043c01c5c1d4114014800904907035070324009102946a40744651041400285154690f00750340e002001b08602414840755004200c1e010701041400140600e00304140d60451511540050803146415014070086480d1031501504086407154144102031081c8542e0100250140360102540d0403103c0d240c542c003604404a000032480c0358016100011b04000810020501000300005180940c1c041e900501c0300c107c8848100075641c80340440100c111942c55010001a521082211055100900c034056180c440c04030003a14503180d5000b900401543c1c3d040c401c29200311002443c100c2e110a0800d1004695880054504800039114190190000c2110f4400d01e4020300c02e443c0c0000061625450b81d08235512114100d130802d4030800e80d080c2805 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 554165440 1250 554164190 554164211
    0xc080a2322080607020a060504030207091d01060f060e120a0606061805060906090d06060302150a020606060708040b180d0f0506090606010e04090512030405010204050a06030c02070605030a090c09 86
    0x29044000d060b408005249900380307503101a60f9107180e0b250003454161203800181c1018401d024140041c800c0e8101480080e0485014050803440040d03101d0302c0390303c0c004000444041c0445078600b158050b440742200400104180410f1101070880500c01b40f06201d803050011304207120b8100101819920001c48030209100103a0314800e130b0303000c2d9100b00c02c1404001c160307036207080071240c081070202c4040034940018500700000e0100d55201030742c044500158043c50781810001000540c03007550940784ca540e100c4040110034001c24001902c52401030109005070411840200344002c080407a950a003d050340000c5d2558241d0f21040300c40c000581408010840c04001042d000410030000d42a50300d0403000081080465200d0030344126210381c6998180304040c04022030070b00307152107007580e00e1a06041031b9001c0d60142c481c4038029110000b00094042c403a1180d2020310800b64060428180791007070456240e00060145041242c1e10072008000500c0f08000070700620341070b00041b804a20030b = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 554166690 1250 554165440 554165497
    0xb19050a1724061519050c1009051b04060f1505040906091401060215040b0c041802030912070f03031a0d0c050112140a0c020102090a03210c080a23 65
    0x581a04c407042ca40144110030507402a4640300c1803080300f0303240546d1254801007025160800840d0034000280c03070032002c0300910002184032090301050f030104998442d180070500049602c148611600b070b0007150824044d00320b081e003c0100205092814904281c0c81d60300000481d48079a000d002a16540c400108030b095901c1032283c0102441c2c005400d0041070b0038518000b51000a000901d141180340000c1d60444008040da07020304910030868860014081c4403100035441030b615407e1504c100c2074031851801c030910032210095401608070700030076500d07034040d070143c01c8601c1080780d80342c081115076200d0346405d100486854065403542d0191032400002415010444000c042c0e00b909190084454a10742c0b0030854220120482c0000c0d40011001e080b40240030f03003007565038001400400082032111242d01d82c0b50920800840340b00002e24040140c41030b0300100c400404a0b84140b126410860140084018801c5c00c4080c0520f016a00100c12003a603010b064052004003038030b00c1c014001c515 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 554167940 1250 554166690 554166709
    0x9010206010617040210090b04090203010305070503010c1704050106171c18060806030a06020403050d02010507020c0a1203020c030f030d1a0303070206030a020c010501090b19050a172406 82
    0x99600f0400880d100400c0e400b09500d400a1010340500440400c0300342e1984a0300340e60300100001c60f03003251210345540d003c1020350320a11043d01c0c40e1180381c2d4041054038040c800c1100e05400c030b03111a5400e0300c10420100c4a100010402c2c1c81c07039540e45100003030316400e80040200b070080420141102c0a000d500f884103084001142c0c80400c119600b030402502589801d9030142c80c02410100d00f1030b0b40d141c0002c2d142000c068401400c01c0d00103d03001040180000d112030080072540c000744100d9407800406c80c3d603980141130241c0e0025610b4400c0055030312600141612502074415280d4421a07940481c1c0b0389410040b03176200d60342c0005071404111071544500d04450342524a0100c81d81000c400080c2e0f04c3c050840042d11074000040401c8440c2120340c120381340c0012080080c0f1070780d03079141c00c2000140f903c00c0b801400780c2094120441e020b00d80d6841a015210001c5c4100492410000050514040000707014442c0c843d5414403200e1444602000c281d143c405094010b0343e01c0c000c424040003d1 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 554169190 1250 554167940 554167949
    0x1c0e1c030c0f0e041104090903030e07082404060e1c090e010e0c030c0c1c2a0b09030d060e0402011b110904031b03230f0715140c0901020601 62
    0x24441d501c594466070000c0e85481002c8200d40c04200200304c410f0a45451041d58840114a85004000810190181c000e1501c500d054425100c0e030070380d28209103407553b17815060144000440d81d030140d101c1201d005401d410034051040001e0f0340001d601411715001810380320051108040070b01e02c030f505e5401031681028091080c05144a5454800c0803076100b030001c0c1010106010100000b41c03850018029900c098102e403044404102504d011840c0460403901036400244482e0400c45030441d00850204281d00030b001c030011070610035103814403003941c058001e4200c0e003c10000513007070f084240200b0b006420000141c1850b402c1920000d00a00101441507484070303681290b070f80c00305010245e032031205a41031751880c2e0183e4a43c501141e0003482c0603005626500e07141c040c1001d0603401811907000080101d44a0301000513024110ba40f4001c0c01d4104040700810810f4000094501c2610baa810321200f80c0844d02c040d2140580380400021507040300524400304d001110396034104406030050 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 554170440 1250 554169190 554169197
    0x1912031d060405010e2404060504090506060304150903050409150f08010c020a0f1a0a0f0e011a04090204020903010e100c05030411090414010203090a150b061c0e1c030c 74
    0x510b03003000601110707107044035503111b046c090408084440049a21b407008510020181d6511502c030340340903040c0c1d0828003611528074a0440002c07500d0510b40d0450303010366000b40100082903142c42900c800b801c560a822010807078140800a1100710a0040301007510030b44210030740340c0d818014140107100761940b02a8960381041c0e071948400303801054050109030852103006c0100200e0601c00400e011042c99540711803034002c00c104a0058540c4054180c110140f814804489100d180a00307803031007503241c03081c94100a0901c8600d850140e0000c82036030b2018001508200d041e20009085941800c0315207026040042c3d5400907800501c0355140200041c01c0480c11424152140c9141c50040448540100012404101030101c40480021a03143c020025592841c1651229445858410341110080130504400400090074060081400f001074040d0b410701ca08038075034481c0391052103441c08401d0303a1008203000d01a410b0051520b045040301001d605200c8100005084421141454040 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 554171690 1250 554170440 554170447
    0x509090a0b0c2a070e07030212100b0a050a0c080d2c03091002010906240605030906070e060d020706330b090f0d0b0718080c1912031d06 60
    0x214000c80f08038240180b4403102403102c88145043c50780c5429070075004102c20720070903400c110495a00da002044441c0044100d000b5540b1150141075411b83d4034000c203c07642c0014440b1911151150780900110f403042d140541e40000d81d40ca403082e00780d204154071410581c541e00d52055401044120070009540c45d4041e41c0c1c0b80f00884038032900c9015095601c0d01c9200344c914040d9910f80300350040500950020000c1085070a502030b2890b0140740205c4014034501504000145140200700340c0b40701d541900042e042e561340700d81c0c04030740800c084405694000c1082c010880c000f811032020303180e1180704000c00110640b55800c071000c060610190480390120400100e400100b406a40d1400c4a074203860340382d1107040c0400024101d01850a01503003042d02e02418000340036402d4500380c0034100c980c4a4418500030303500500441c0d41180140040356009802074590307414130ba50048030f041c0755403040a43c41c1b5111203281440030802e00040c4d0000341d50760a03000400c0e02c1c2665101443c4403c8450514 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 554172940 1250 554171690 554171707
    0x12060a0b07030c02010e06031501110f07091107170903160501050901080721050604051003021804030c080a020604060f06120204090501022a24130c0509090a0b0c 71
    0x40c140315100c001800c0102030b00ca03400859004d2030700b01d500820000c08068a0380b4041251204440b2118502400a9481002001c0c003103c04540700c1c6080c1600000351136880d0903c25900060805802100c8009204201c6000071519124201c0e07814180381141c070b0b60b94a038140405162910100040001c5d6607104810041c50381c10508452042c0340a0901c80e415035202c6606850000b0f022140c04100d0708001c0000e0b0824140307034041489410304072000c00903a1150b0007000d060f82c1c03640c040250403e03006180d0034a002401200180c0c005c0c840e15004040f15142c6da195120340c0c000f5103120700036074070200c20f010803c00c03d4041c441e0340d082052000c004080c035208520304d1118982c43d02a004550310034006040c001700390103c03844108c0351000c400e4200319100340400c0c2891014078003c940d00408205401d0b0b5110300119002c62030300e14550b5001900c0b120040582000e01000484000c0319041000400c1c0c0c442c890703028424031006001d0403902e11181802d002c50000100031030280c8004210a40 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 554174190 1250 554172940 554172959
    0x20603182b080708010e060a0504020a0903051e0d140c072601091106090103020409021614010212010b090d051c02241b07061a040b03010209030d1d120312060a 70
    0x40c1180c0380000c6e08811511000045454841640c1043c1d40060002801c8040e00380c02180e403400f103c0c40788003102e000c5280980f034428000380d42c548500040d04030120010390b01d8491030350b0071299461104000c0c980703a91041c0c5c65280c040e603648143c5440104092035221015002e100300712101d50000244800c200c5a9581c6a451014240051090300c021850a002d64441d505039406490f4141e0219603c070b001c10030155030010654004c0b1420440c110a4084810060091352040c010744c02554120303900f440f10280d0141c120300079241d040012000e407a80800c900b0022918203680c200c540c0206d02e0701c2141c0090600d103141c1c001040c140501e8190204e10142560303040d038019490b1021b50720f008410300c2450329a105030a00030b00344506054107080700c03c2c81400e1401032480300b06c90030080015410241805c1c1c2c024144041e40c03581102c15110b050303030700901488481001d400b601100606e94500095130100000090341610b5101103000030b131365028900c07080d4100000b21740d203031a00752610031801d = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 554175440 1250 554174190 554174207
    0x90f020a0e0405070507050106240c03170c0909070309050105071106011e0b0c0705030d03050c03070309050f011a210d121103150102010609020a0507020603182b0807 73
    0x160040c3c0d9598002008a40b203501542c1c5007650003402807000c181da40701c8000c4181c03020186415401002404001c805000f620503007182c43d403540340d01c0d1581800603244036001030b0007020306001702d00812410140f0f69805900c14810210350f00c001500c0742d26070030041d007102c000038085024001c400c500c80d194020002007103411901d40b5070f0381481e022126108440c1140f00b69200321600e100215901c40d0701d0b0800701d4502d0076200154100c43d00000266411016690f0540e407604003c8010000b080c4802c0c401e41008503024007800c01c8428050b0f2002c441c50844004a03800001042d0f911044030491520851440b02444040043e810003071060448039218000300c00000f003448a091034051100701641c00001004581c01e0341c00b6217070310b015444406103074650000117006502c1e1640101c1d244919109a903102c1c100d6907905c5061014541c02d002c016403000d420116003010038010045c008004121410910036808059400b042c0840d403031000c02d902140c1d454081c04020020001000c1c0e209a20 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 554176690 1250 554175440 554175467
    0x1606140702150c0601030c031106040e010626091b04020f04050904030c0c0b09040c0810060c0303020d020d0b0a12030c0807110a030507060215040c1a130807090f020a 73
    0x4241c60002c0740744400c10352040e5404400c0e0b6025880001051003000400002103074001d00340722010246403010001c43e0304c554010311440c10300141c010301446105102c12211400054400d0005840145035800c1014040752403040981c02801d0011004d540b0702005d80b0300300c2c0e040d1425410810201c112038824019030084030700449185001900381344c0701c1c04030070b80819000802c0c603038500e0301d85400c10f44580c0304c40b1116001d181884a42850540314035140751050420441c514046400d020080314000110601601055004d002c0c0f41c1b03041d0700910080c944500c5070079000800d00d801409000e00320b082c0d9032000030542c0d01c0e01c1020000c641c02ca8607401c801d41d400108282e550806242501803034210490081d00001410008010003070006080b07403c2d074640d034003114840008044507a1005600700c1d0b0081c03d1030030590041081c00064442d80a18500b4940210306260340d801c81a040054075a00c41803141d40324080400c207034005841008041000408103500e080c070701c410054102e203c009803 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 554177940 1250 554176690 554176699
    0x807081908031306050103030309021c030815040e0610081c08060108250e0118080a08030c0c1b0a3309082a0a030f060506061603021606140702 63
    0x103192403a03d1040e400d41c00b07504c000d04000950f100c0c1802402803c0c001c0342240075030010740c69468031000c02814103100b182d2580c1c074003215588800d1001041c05060707680c40d80042d1514a030301c02c00f11050014500c00d103c2901c102d445540f401801038940160796407091102034898500341d0b0000d1303002400f00d03030046003803c0002c0d8a883e010b0144a103d001c0d04400261660340940b1000744035031003a04169410826640c2e10000e4500c150000b25840c0a849140d9180d40f10500c9840000d440e90040c4da8854a29440b1038203100001e40c1d418180703140c4510040401d1144140c3c0b405a10782240d9420103400c0c141080070a0000034109050450041401081c5505035481c04052481c130407400100502407074019141c0c4401c0340c0c0c010100701d010b401031540040e091402c41c401280ad040300f140c130449400001201c5140c50315200c81e4020b1034050a540d410541c100300c0c02440054003020004103031700c258000c060440c0180840300b0303031944640100c010000d4010000000c003071624140c0384120340448 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 554179190 1250 554177940 554177947
    0xf0d0b0c031504110d0e0313120f05070803041508070507060902030106181a120a0201051b030a09140301050709140d020a0308031905040c0303030e1f02040807081908 73
    0x1042e0560280806290755000b410207903040c0d4246901409085c680d101200180b20303442059000700c4d201d0180e03003103a0301045078010080044101c035040c201e1100d4004ca030404c05036a00340c1c503490b007042c02c590815000b592001400700003001405051043c040154a0404850300b0b1040e80200a4072500a0152061f07450b400001c066640a46c05400100241004003103140200700305907002e8815a40f0f2807041c000c02c5203d104a0b414800c2c1030003051200800078000034480c0303a0054401d070f048210112400f4400e5041e11030400402c000038001c44d81261a04200c81d80303815020740501d071001c0b038041d00a906000512821030781250b0250144c481403411256100100e0000c00c025000e070550196000c56881c0b00081800407000040d8050140003a50820201c6240c080030251703202910010710b215050042040801c2c441d612544580f02c0c00c1041e911403081c00f42d041c40c625a42c500349503d01c603900150400a04504000910050060300050249000e0018458440310301c075101c05040c615000 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 554180440 1250 554179190 554179201
    0x61805150912010f0e0d030c17072c010e03060c030105061303050a060f0e1c14091c06141302040c0509040c18060f021b0301110a030207060c0503092d010f0b0f0d0b0c03 74
    0x144440b0f0304e1030189820704541e010405800312040c0d14000b409073301280780c908015071035060114400703100d80305c0a0100b03032940c0d10304018032940740c1c00311040c009404c00310180440050018404018958040c000100d0240920b010a41c2100c00000c50301c2480c0c3e0003009107041200082a410544050605000d88141d0034041e40d0380c07851203102821648000382e05110003100445004240c01c29000e654204000810320349050051101a50b124000f44070b0100c0c2c210062820703410040341c03c00b0a10b01a03081c1492203000c6001e60700d01100306408121541a01120041c042860a0042049183c46043d40c01d20303000c0a9111103400c024140c511300360a0850649442c00d40102d0800c04550036082c0d51000e080c07800070000e4128560031140eaa0400c0501208148241c1c141c0e030007614000c0c05014849221140d9120044800c44503138900c548084115195030403e12030000130645099002c148008c40030100400380303040342400c511a2400f40040c03404680140c45556000340302650013560381e02d42 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 554181690 1250 554180440 554180447
    0x3021c02030102041e080105070f05041514300c09040f0b030a050708010b0f0609040e0c0909030702011106040f0f0309080610061805150912010f0e0d030c1707 70
    0x507500701c10000171001260ba503040c00d40c01c00f1842191007140c0208100e4a45c0a41200c03130b02e4040b202c80000500601c414070084103071190ba240310340c0703c6040140d244050015240002d0304003255030079034041d003402d2104039240c3c142d2001c0e1024508002c03442c51480c008070b52010b1801100c0146008550b9a80d14161030f8545502000741010000d088600801c0035250007a900e000c3c80c0a00d0403030b54200040b500319400d003911403c240c110001e103060f00b0f0105500c14003008000c0e00ca046411440350300c00780c1040340c64141e04940100503e0014550b44c5146000140400c9000105400d03598400002c2001144801d0118050a5403055003c100e42c802424210b4600a0a030000b0403140030360010300040d1040105404215101606e0f00f4510b088504d50b890b00c144103d20840382c00c00c800740a54803070f483d80c0d00d004000c41000104051800c01416035000c1c00c503640c20383c09040c2c10303a6801060002600401840306450040e00d41801003000b0900c009154001146c40c04203004250808100110301 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 554182940 1250 554181690 554181697
    0x5030f030109020702181506181905240702090408040e09060612160e1909050607030632040e0a030c02090a0c02060f04050f030c03040504051003021c02030102 70
    0x560851a1a035031201d14040c003d511400f0224450300c0610a201a1000c040b20701500c60211035801c42c41c1d021000e8113020b016404015400d40500b42c6190b0b0344515502d032580d10480d03460383c10501d00c102c1e0504040c040075aa0152220749079241102103401307039024130402c85004560581e222903e64441e850190b8640c0a6a0012110401d1900c104501280d0000b0198030890b0120b03130b6685100815103d294848981d1540f0301200302c115072082c0405815120141d070410501c0c820701a4034055024010100c6010000459854009009004c441541400b60070098060210040065030300f0040e419110001070302a21700d08440c1c0c1c035017400c90360f40302e511242c00e040071030702520029a0585001060f0390002503049100f01110408035010300618811403101e034125800410300e0b83c43e440420084424010302c02c5600c3d02c64131030700e100c401900f80094003072482d1150080d0386842c01c110400040e5400100700e41d120303039850001040940e17030f6810041c0c950b0b00c9044940849446c00e00110b0301910 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 554184190 1250 554182940 554182957
    0x12020414060f0723070905040b1324051515071502040e01120302010f050c1e13031a01080c060d0b19060c05011a010207061206080706050403050d080907060c0503 71
    0x4844402c62000c01440305254501349004c03005555200f40c4516651088500944015242010351400100a010110101e039550750041e030605211000c0c1c422980f00e0b02c41e803621500c11140d1100140316101c03000d038421000d9520b003192140004a1000710002290090481c041c1420354814003030010060940d04450140084005020482d84c503071402002c006000c5c041240151b103098003c00e17000c44240300300c0d40544051501c4602d0090214110980303040302d0f010b0261844420441d915006a40c070b00c144004510402ea0740b0010f0124514400910b4816407100e41c0c1900010302c1c000c11076071140704803a0205480710000940c0720281020554142110404c0c801c040c00b10003010440c1c0360494114102c0500c9a13000f4880380c02d80704184480c0e411402d404902503488144280b01150103407410444540d980c04000503202d41d00d014051901640b58001004103d002800303200b4098140008503016940d030504010314103054021950392011445044108a00040703030b102000400d10403517959030b = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 554185440 1250 554184190 554184203
    0x1416050c0a0c080d14090f040b03010f0b01090b0f19020c040606020309041a090109020306010c0605042603040b180102040e042909060610270612020414060f07 70
    0x1402546030480c01c0c44440d0040307903651320908080408035442007500300f1032049420101c509100d503150901c0244240700b05000d500a80b141e00051442d14240706080403030003c1000403800d2480800090440c095a400880c4881b00c00c0064042c520041800c07190350030104148405140c04940f412410122a980c0c420340c403600b44030001418980c00005000519011103040000380f6141c190108501c02070035150360030801c41001049405101d601569020906041c04022040d132591403108990003180c04690441000a2030001e01d0650900d0a0000e02d20303024180c950b052540b240c07001004014041d40004244060740b0350f400000f90107450040c4800070104e807150074070703240400103031511700c1c84005400b001610141090941c0302c06540148a05009001c02d41c80310401d1109100e900649202444449510400c852040c0320b1844850308140541010b0035003025801002c0004000541400d10700501051100304c1c0419280807120134110f41e1b040c0c0e0746503a002400c40300c3c000c002016144 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 554186690 1250 554185440 554185453
    0xd02150703020604050111041217070f1505060904030c0b061309080301090b18150f150c121333020708071e03030509030f030a180503011416050c 64
    0x8041e0000f9034a80501e108800900900018080030304d8540220f120b43c24884241d10842c0005c98904c050845e00e01c898013802502d801010344590304505000c12089841505002c07100304030603518412950445e01c00c0b98126614101601d0081c1018009440035107000e42400228804e03a03100069580f041c1c02440c8180070354071a900300742c0c000380c209108240a0f107080942400c3c80340341c00d0010440040c00c050f1260465160312040d042440e10410081c1d0700200150045245da40d5a4001c0082c04400c1c00c05d00c60b0707031300e80c0b0448a6060110a80c4190752800051004c0f10a03491240c68400aa0700780040b2003c1101c42451306c400e10526006140d0741542c1c04594000f6010b50100c0c150041e0b4043d83c08480030545e0700c0000c900c40074104a4400102c0e0040d070307002d02c0041c0c4114010300700c0303800040480b03c0c0c0d40503154a150440c0d01c403400310000b11b18009207904c840c11034040381e080242000c030b00810024402040c41c0660001c000c0c002c0214100e6000700e06c50050050b416540c09803030b640219600c = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 554187940 1250 554186690 554186693
    0xd120e041b0e090903030c0a093303050c03071209020603040501090c080f030a0f02010b030d1d0316060305100e0f072a03030b0102030c0a08091801080c0d021507 71
    0x7680411400300c140060b41c9a80d1840007424402c440c14021481c00c1c1c0154036541e02c41d001da0840b40c0005c40c5035403c1005210b4001050000c035060b035400c01c80c02000f817001c142e17050244103441d091034040703500906050008004201c440702c0c0a0f254006800d08080f039801103030060784401080f443d10021f40c0688013009000a1080542c800006203100312100402207441d840840d50315035610750328204a900030003031484180d102e291035022900301d5000100d44000700380000ba0034411200c89140c000f03441c544841e80f0b40c910f10036003c103c164040e8040c00c0c616141c4088652410100d0048170b05150b1114089201e20b18680308041c002e1030200910080d604203056100c0d0341d0041504d0150024043c401110b507400c034a0550b0100d50842580c12880e415002d60b4142d01800e0f0035080306055000500c682c259041080c000c1e4a00c02e40714122880d919034116003044400d10760f4030003030050051b4000040c030001d03034001411000c02c0d004407003c148031400b520010740c2622803058030701310920000c1040c00 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 554189190 1250 554187940 554187971
    0x605130f081213080415050c0a051605010c030e21030a171005090f0603070b0409020d060611072706060206060111010b01090b13051c050f07050d120e04 67
    0xc402914084031200d4940e1030710060300707400c00c40001c4c001650811041100c00d1003070344400729484c403905259050003100c00f5414141040d010040e100c1c0e03041441c824400c60300d01c0700c015003c0c09003400c110080400948000780390448402001d070007030540c20480d0000400c440c800b800740f9881030382202c2da51140c00708024128550150a03403101101080417800358400354007100d00f0b071040a0003034155541c0d40142203019241c0581020742501a1110204084441200800c041c01d210b40c0c0c0540d49508900001048450070b40c030107420040b0007a8002012a00070420004a40081d6042001c2003002c1d6000851a4402c1c031011a283e072401000088040c0c002c10402e1240c00c00345c035881881c040b298081802d0310101501280002e000c4241400000c1c45d06000c1c003408244509403500080d06e400200d11100300301c40705034480f0f1100c02c2050342005400c0043e0310b40301d41040c014005c0030f40b400001c0f1b00443d52002008002e02c0030055010501c40c460600c0b941140002001800301c00070712401078 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 554190440 1250 554189190 554189197
    0x3030c030e041e0906150f05090606071227260706050a0c081e07330902011101051008010b01110606091b0309031b010c0c0605130f08 59
    0x44010615074201034403107242611070080d05516200103900070031000c0100400910416104507a4a03944503081c90501c4030601284029001203901d61412a06060402c80902c40081c011881841c0800924000034050b08048181da2180d0030841200580d610b1035140b48891841e1100070052400c60020380c1c50001c1c3d60300d0351101c2c0c40d03107401215980416915030312089640900000b241d0f0070070081442c14801c40707512a8844c05100329034101400a045400d2820701c01242d1100c8450104030901445051041401264605010a0280707070540c80461851002021041000c1e9903807003845041d64064200c45421401d040001c00c02468102c40d61034152140e4051200c03a5841c01860700c11950290084100080c0e41a000700159034405c420018040c0c801400c0301c017201e0400e40f40012990300407000e94002d4580c400a1910fa05a4810703140c2800e06503065081941c1c1440c045c842e078507402ca0000750650350810b001181c55640c2c610503000b0074401090080c46030000303201e01c005200840c00135 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 554191690 1250 554190440 554190443
    0x30c120c022b021506040207021302030402040c1b080a050d020c0d182709080307020303070f09031101030c020106080f01020403060b040209090a021e030406050603250e0a020409020403030c 83
    0x8949500c03400321850703210070b0800c00d000d01513072081800400f081c10150030180d02450080015251162507404500c0810030300d00100041900801840214600f0340115408848145040001d000740790303210282a90130800d0190001d60005a00d00f00203108d0742c101e80940301004825980d91a80d15059640c44152088000c0001d03024042ca10403000a800b02e041115992250b52814480c0b006010700c0035807100b400c51881c141d8464040001842c105d0155202d503c00b80c010310744915241c0000340000c0381074401d0000700288a00e007072001030701c0d80500c113100a03c00c0c030b070004683c902d5901c1130340141413580000a0078030441c0030030012600150003c3c400c0d43e00c1248180000000d00052106138052048071680c8800f40b280010a107040e01e501134880d0a0000100490320f868100c1050b50ba90b0041d2000c2d1038150b01d0314108403c6003410000406480d58882e00005c80e19000c8a00014000c614054490000e0390100401e001100c00d80544020305220002159110707034030301c6c000d418000720600 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 554192940 1250 554191690 554191723
    0x8390621100b0a09061220070b100b030705090406051c1a09030304032321090706050a050d0e03030a090b010b0f07020d02061c020301090f1b030c120c02 67
    0x1000b0980d842c2c4181540d62920f00e64584116807424138506941ea040c4c8022000c2a0039a102010290104030079800b180c41495442c00a540301024149403d20401c010401e280b0311031140810016002c040c0100e030360081542ca40213407501c20301c0d400100035103010b41c802a8402c58100d014244802140b10b8440c1583c415480c805601107041156240401e0456001c0381ea90410310000d40030a0107103c2e001e10320304452651018461801d440ca000c140c100340d000039145e030900d1680202000c07601401d550806541c4004003100c51804500038418894a8a514104071001c1010035002c2e2940d044404012683e0007a2602c91900d6901e1800030400300310143c0f0b002005070000100009502c0450303a044121440300ca00d0000c50790207218201c1c00b0303803d04a0b0401002c200c224008003200c02c0701c1440742203840340545e89500d4965500103a600c20032004000358500203c80c2c0300b0010804802c012203041303040c00326007d00344140541d01408184950003001e41800c144a04885e40800d00181035990f203c1d = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 554194190 1250 554192940 554192971
    0x501020f0f0a031103040308160c1205071a0915220311040c120e0a06050109020a12090c18020a0305070c080a08100512060108390621 59
    0x511a501d8120300e0302144a500090307502800700344101008407104420408072868207070340e60744801c2981e020102c03146103560103503400000c02480e00344179002841a2284104403070243d807101c07901c800310f40c0309000681505040c1c40346d4149181c0151031280c036000302a0b41d9981c025014480507030b4080c89002c040514900c0c0c0641141c10541504010b4039000b410581c84c1c2c5c6000010300c0018840e1183c601c05010300400f20940d000c117180900d0140000c004003034000400f05180c800b06903007041c0c1003c00c03a68014000d070074000d5400991201011110007010542001c1401c00210600c0d898204070f01034201880241006215a0000c00704034455507000c11095503103000464000315480c400030040d1908000c95116188034045c040d800245070b01078802c80390b540d04009280c202d13001d810a4035035002000108102c50301032103880b417a0551a04108500380c194041003070b00c00b103581501008145200020307056030301e644040c2c44400b14051400c80400c600c08403010302ca501e0440c0c0118040b003620 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 554195440 1250 554194190 554194213
    0x510080d021c0509040c0e040524040f0b030a080720090a020a0311130f050f010e0d0c031506050f0f030c04090302030c011505030607020c09010b0702040e16050102 72
    0x504144408080e07405040c0404a03041c401ca15260507455850401c44203003c1640c141d40d46100c1e0144524050b120040088007610920050b00c000801c00c00c00c4060401c05096483d004214000119104441c001044185100c0ca20018098031800c1905445282902c1040108601c0208003ca010342071030300d0302080a040c0c5078802030308014616040100c21011510307400d403035005820242e249007000320788180d0483d044059500201c010003d08495184100140c1c203215002ca030280000355038694090710035000203808032181082c00e502420385ca1203450148000d4901d907001a651150403c00e105080c1c3d080e8102800c2c160141034801d4034a44d202400b50300c6c0011600500a80240c05811025131250400009250108040e41580010056249200703821b10450070403c01c5080e81c00c41b52410042458580000189102c0565000008483d1143d03500b0742c0c200d04660307680310760075591005403001c9400351010708181200c40c41400200400d03100155015410f85900380e003101d40e0f04004 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 554196690 1250 554195440 554195443
    0x93d090b07240c0212030136050405101a0a27060815010501020d2007030b0c0c07050604080601030803070c080d0f050a0621111f0917060f0406061206051008 69
    0x707200d403c0000c2d884002e040030002c1d1007088c078042120981d0b020f5030307044524917001c0301b0340e14100d07005c84098020108181034498503101e41e80c43c0341c02c90760b0219881607081010a020b06500e01981020805007000d40104031050751654040503981d4009000745580c03046000d03030343c5a14000098040074404000316095100043d100782c4410316550780c441c2c00c08550003c4801c0101500c84107503034050702001001080c10451000d00420585220b00d90f40c140322650300c1d00340061604454416401040200403852000804034103407500900115030300c0e15400341c1612624503440f4010400c50f80400d005d1880035655018954550580780d00303100b0750350b03241104000c6442a0040c4c0302040c00028040700701188413566030000c5032003040c5100c44030984900084010080450009800c0c01e01140c40303103155800500d11009120040d100a0341080d04200c80b515803000a04000880081d1b400180921106070442402801e0000c0d942900180c0d80c20464060704c0100d5994560f00e100070800280040d0 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 554197940 1250 554196690 554196697
    0x4060902032514030d0e0609030304121118181903030911040b0a0326030f010602010e030a1d010c1704060206060f09010b0708093d090b07240c0212 65
    0xb00100074000b00c840300391058900340030205506c0d800090901c00e40c0c009803802c00003000500304154840b0000d1010b403a10000c0000d0142000e4028008a144542c1c0749101001e001e400402818512482c1843c24600c1440d00f41030b40800003030300f009100403c092580540c031220303071140100802d14642d8466014002565200d0241942159100c0e10030008645035444284402602900d074401c0307060036540030702c0e0540080c1c81080e4444851001080441d0302407251008440f400c0001e181420b0040f2406494042260322040ca48402c24107608507503849038524080051f4130680c00400d04400890304041500140150340c00b520442000c01e5961401e101c000101e94002030807050301e40e08241105069420000003110740003820711142149a668840c4200648500c00c0d1b9040321320b01c1c0c078040003101108070601b480500c1922068014565120450b03c0544440e1000141c1d103000c07600e0000a0340401003829844010420350b090200c24003070300b1054064105500310b44403400c640080000b02d10 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 554199190 1250 554197940 554197979
    0xf09040206030a0213080703050d09060e090c03090f1e070806010506190c1403070b0a02091003020a02160e250e0d020a0b07151104030f020405040609020325 69
    0x1031082c00055440d502e03903001050490001c1408414440d5100c54003898905c40d90800c0303030650400140c801440d640400c59030001d1240380342004000305444040b50041c1000f8260880a0200000080e08888100090740d4410824001c41d0540503100b204d8815040c0782e422428032034015144001008840081c01905982c8010141d03460449024244502240e2a00c1d00e002031220b0213440c030005c5070303070500c0e021410091a4007442e07a8041e145400f10710302c40018000e0305072900c1480040642e4440d5581c00700f6007900e134240160740d01180b1005914100c8007550542c1264081f000110300d00580e2010740b40500d846e03202e2941c001c0345a00040024955801500c800a5800c01d414080781c600360408444160014041e800408c2d20342007552400c2c1c0c400d28090700d921000101241e510440d9200c2c0943e0841ca1202040c00c0601311f503680100a0254800688601d494101141c18001c050b0301076401158020100d50a55030030380c840e915049002c0201e1122102020800035036103407012500c09149 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 554200440 1250 554199190 554199199
    0x14100911040b010c14030a0305130f1502040f0b0c1e0d0f050d0606050c06011a0a1202131716030b0c13090c0905030f030705031209100507030504020f090402 69
    0x240030160500004060381c1c1c110a0400c00200c4029020980031281c01e11005600009140e542032100c0000c0d09851024201c0305116445245800224182c044038403001c0d5882411803200c04824207100004c0c2c025900f102a032507070000000a80001030301c00520112a0881c1660401415a40044114607a102841005400101003504100c0c81849580103041300350030070504000480341500704842c9c01d90802404540c0000b000c00b07107804100f04076801026680400384400c22580304000150190071094010b12190446589200c14590162a414042e902096a0792996501a418010440342c02000940188040704468038903564200b1b040ea504041c94500c0e130b4031094119403031342e80f110720318480401f4410b6001c00e0b203040310b000708600659203a454040c01402c100400d0306006124400c441c0b1507104004403400030b1004000d86031809032004c0101410b030b445542d9242005001e8002c480b211307152104001405030507502a5018030f0007543c2d80d4540290700010300c00706585c15140070350711 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 554201690 1250 554200440 554200463
    0x301030209010308130e04061d0d051c0b180f0a05090d08130c03120905030708120304140a0303020304060e2a040e010e060105030f0303010e070525141009 68
    0x22810303410080002c4802c4580d030740c066a80c4e5052030700e0062000c1e20300f220318545807000000042010604004c278240a1800751005003d1908003800ca48610b100100c6642c010803880000040c0c50351002a20110140c24140601c2900c00c404c440324004a4900d00d00810090200d80d1503c807e114940c460380001c8014200c8406002d010f80340030300c00034201d190000c280495030001070b441140c1d001c01148204100c0d01c1e41c1c048200c01506002341900b005001c0d50198070104281c1310002480100c00703040fa210b0a54070b841e41e0404010410f1041e10035016031041c62500c00c101545a4010b5204500a150401a90103190034554403000500c2007550b2071007140000141c0703000c1d40c4550000283c001040054540c101240705400d40f54541c80341e44164003d0b100400c090b05007800a01c128000c0000614555030400201c81100d503c041c00c94010840c0c04118640075819420b06c0104c800300c001c00d00071070030f140c502d4607a4000207014605510350107081a80f081004207802810300c80d5500c400746080 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 554202940 1250 554201690 554201693
    0x13020603091c050a021207150f0902010e0114071b0509040b0a060504060803221706152b0c0b190306151b06020f040b0a02010b221e05131103010203010302090103 71
    0x2d07a45c010b10f005072580b00030a4010000c5003068409c00318519140e900c00b24480d403903800050003100c00e0456083c103012a801c10998003a15140c11203400c00d9010000c4000d21703400e030300b550140012039000346411035212010701040c0f000000c036486c071501800005100480d03c0e03909000070703030310107228500c502c0c2c0c0705005030b0030302c90001114120001c94091042009598a107002d24201d480510f2920050700b045040c040c002c0080c0506240303100c0e080d5890710800040c2001300007540ba00d101190f08010808803d4010425182c60780c100510801d85c80d2929080e070070b81400214020900341d4400309140840014442d0300036020240c50b2403554999a600803c507ca900c042c0100d88803080704c40603420060340c010301150304090409004502c62407600c0720b958480183c00c4036514000c2510903a00d0300303104038148420010f2400c40c40c0540e08089650f2159461417541c89134030400901ca0541000e04116803080384000006049006141d00002c110a00d41032500300d101c00c0c08082c3d08507103440010310 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 554204190 1250 554202940 554202973
    0x50a0303080106030f150902040602060c07050304033e031501080309010e040617010c12022803020c1b0a3503070b0a1a01050a0806010813020603091c050a02 69
    0x500c174070700180300881c0b034034080e8104000c41001c2d40c00c04441660b002c1028402c07154100b1446600180d1030400511704a06030310303100d540c0c0c040e0340b00051008406a10301000e110f000222040c0c901100c402c49810064500f000b2340710b01c50341401e0300307009109420b003003480c00b01518050350403148850090b42c0350505800c01140c0c07000482040d15082a103c000004650941c500c110302c0d840d1a1100000354040c0080c002401540e010b0604c0449a005005407102801d41002210a001c100c1020100c148503645065020380a00810b95a290149803560340003990542c4d42011660800c44035101e03150b40340c2a01c90b6803c542050440b91645003108422183e03404900d003116019140821281050a00d9803080008003040300c0c1400465240d00501c09840804c40326640071000c00d007080c42c10416108401414120010103041c10420b003640842e4916001e01500001d168020b00b03550390301d10b080820356583c1c10146046c81c000032450310452102c01d20500c207403180303a29a503015144405504402c032 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 554205440 1250 554204190 554204201
    0x1103040f020f01050f12160927140907060305070201141302010512010909050c0409110f060f070b1012020105070f110904060b010306061b0213020d0203040f0c050a030308010603 78
    0x3181807082c2017000125a000e100054003000904032618103451401d801a2203a50002281c120103011034550240f0149054403541584143d001c10095000d0a074000920054040043e1802140c04044184445144082104425561161814000ea8035826400c0b400c954500c10000802c1c01603202241d48805145640039019005240c0281404610b11525806403c280d22005041d0355a031002410058103010b50007030344900b12410458120a62102c0010940c5003030341c544a0001c0b0440c900c46503031420159a94540007d0362952101c1c00da20f4480035900003528100000309501000281c482014005030394820f40c180c3d600c070b0600310070b90b580b52560280c0c00400c54000350b0355041e00c0016112142e1080c0700384d01a142c04200d10020310000760856030075410403c00c2000c05400100001014083c2d40d611550542e04210001488040e14000b4091402c003144014000810b00091202d8045030003180d5001c0e60700001e803550340f0401c101072041c0620005011481601c01002264002e9004 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 554206690 1250 554205440 554205469
    0x816031805061807090c0e1c060204060f081014060d020d0c0522080705060c1203040b01030c210b13020a0e15061e0705150f04061103040f02 62
    0x111003411840356211824094102c8203495189441c01040100d08400c0002c1802080003d00c1000140010007004194a6184840c14000c210000ba050a1080b0210201c0d0545801820440d03c8948866000300642000072105002030043d4001c01d07d0303854404a4101111000c882c00003c0b02c41c928180302a0342c000c04a1405110741c00d03c5403860103040f90040c414602e03030603a00d1941da40e02038080d9070080303407160481e04059a00b480c0b00f88a80320b0700042c00000e0710002c840d00c545500720000b01b80d2909089200e00011080007109010803c0050b4003468140e0740f251840c000051707100e4450b06400d250034038171030000004180c00d21000c6207011120b5500b18511070b000034072070f5442d90007048410000b80c0c40030142602c03070f20030402070008021038a0030212040b03030744034030700300c00000704070403450350b00300f5040d100000018040200001040019095059034681d1042c1e0320b0320f1408114032001c129001d83d076403403c10440d10018041030003224400c1d0750000503034040d40f403d5001e01a58005a150303 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 554207940 1250 554206690 554206721
    0xa060c092c1b0f09040e0a02211f091202030c03030105150706230601030e0c13060e071e09050d060507031107060218010c020108010b130b0c030c010b01081603 70
    0x14806001e14920008011608540c0303030b9255100d8066007031004a85441841d46c07601e802c0540ba000044e9905129a1161001d0001c40800c0302440380001e4202161200b1001114114005006030101c0d160803042c402801003035545008100740da0b0a80e220710548202620940080006000c180342000c00e0320004005c03480301030304041c21035403410308985d151090b50248a00c5551032011864402c3c0c49154014000e180500040c50200402c0796a21b44041100344142401500642051102d601010041117400d01d502e00720700307060a01420503070812940ba02e005d490042c201c0c41c000d00501c2c0b01d80488901400700c0050b00241e8803148003c0201501410800d501c944040c4420501c4c4005850402d0060b14016078500c1c3d0f000d40040d2680d05214001d0501c03030f2101190303026030f070040002030440d0041c100d407590b912509401c4844008290b00002c00d4154003084250100b10000042d00465880ca0b008103c0c1042c01d03070043d948074108a800c4442c68480c101e07007990ba6071013034102c0440e0422081 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 554209190 1250 554207940 554207971
    0x42907031b24020d0f0606021509030d0921051e070201270509100503030703110a02090117012d090f06020403080304031b0809011409030a060c092c 65
    0x82d00c82d11602c0104040c2c8103281c0d0013081044004a0311311071205e510701c021908000d0185407100103501c40300001d921042d11704481001802d032610610458052a44801c030410038606145031281c1007008481c01c900c1c00039010095050600e000300c00f280c3d0128000200c0307400704405805065056444607600700e0400540802164520f500803036a200c15220301c01c421912141080240701240000a00d25907444441c6030080005450110448100b036415180a6140e24500c0d0151450300170000b00c000d4209021500003d40904070314413111182022000a01102e615102031600c0c1d900e41031a020142d0040740144020b6111642c803494040c3c0c41024050704e921900d849072070890b000350f407054401400000030401010307486400340c003008a1819064010240d29261042140581e00a09049c00400c01211810156030410780340101070040450340100443d1400001a04c078052540c00411150103020030150b80c00ea03408a22618111016941c2c100b8914402211107400341c045100c807851031 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 554210440 1250 554209190 554209223
    0xf03080705100501080c180415020f1908070906030c09270f091b03080d15030b07320319060510050702030613051005060114042907031b 60
    0x50240500910540e0050200f0000705804d209420321f030202c000c0343d816601401c200009a21144504103066400b0005032901c07c1000070740c1040c400c0041c42c1e9042d200403001d802c4610340c0030b504c09119681c40c3d599040300c10790381c0c40182c1c19a403100c4541301c04a0811070040c00148109038040c1c220010300c0d0000100d0408816810080b40c1d40c8041061420351960400414425480034201d0780e243d09da0402204240b8507242d0305030038060703048528107058694a240414070201807822001d56081000140e0504042102600008212040d8840d814580050311801c4001d00e0001c090060010358143c51695500c1500804000c03110010a00c2640c60701d002c1490713210100c50500d40107064444030b07500c492900400d803030f02e03400919500300401e0700304840002410206044020400c0d148001c40c41d904d420006032a0310b278040002007a40c000c0482e0014601040d00c02410000c45901c10054100b1079460f0182900d101d484809808190001c2091990b079810300040304100c0e010749014130484416 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 554211690 1250 554210440 554210473
    0x20d120e100c05150f1308070204060b0c060603072d0f08060118050106050a110c090a020a080c030c0306010c0c05040f0c0e1905040209130c02060f100f03080705 71
    0x400350741200050050704104108401000b0041d44040401c0c0c0c025614900010800d054003402440d06082e0310010158108001a01c0c003034410042c1c0c010014400e041e1524000d42c41a0403000c8254854410380002c00c1a60601141c40000e6488060703114140070420070310401ca0307500040c0d6006058854100c006030407013920301381c40d010344404405030502d549400003245504a2600b811800745141c90010000c2640280450b0300c0c40c001400c00f8a40060711207034180c10300100300700c030300d8200c52001b003000590742c85580148031114031364403001e11540751104103503140d000071511250303005003c0012a590b9030081c03450201c200c2c030586221a449071218041410f403900001003400203510303407462104803500241020403846041d00c1858843c001401e0403402250107100d410300481c2e000070b0700c06858481410980502c0101a010300288801c1c0500965454040301c454056440c80c4001c58442c0311092007160445840c1d5240304082c82c1503403210607550784503074021604d501c01c0c24011008103d4 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 554212940 1250 554211690 554211709
    0x519050c0301050a02030402130605011e0302090901060f02120702060405150d150306060803070b15010c0c080c0f120319050c06160e010201021c05060a031502041e03020d120e 77
    0x10135200035889003842d1060090515030704546111f406d080074010701c903591744100c900e5141d045e200c402e0351201c1000700c8154006e202d105182c0b034220340c0d600700229000d6008901c01d01c645046ea8200d170b54803500d10380185540c4c054160000c0d408070003000104210f18014858203100b2203024401c5c0d140c56800224107017260b128903445076045102050410a02016126130001041420091032810001d550307407401f01c4a000700131649500f90b40c14007041a0744034030202c5070b00a511581880c801b44e2200046952141c07900f82c03452180360b114241c000107040c2402c010f10190740c19030065042054240b03290f9620f020030035218040050a000095480d42c08100c200c1c050a4588083c101c2100c1a0400402c414844400541035a00400191a8400b0314611408042e41c0d43c0c940000c513a240c0c0c0000501c281050350016006034601d0f488500e1460740c0b5030042044860103000e1840402d000d14448102c007a5510010354001c1c441042d80e000714890b0b80000d0101056403078400482c408000c00280403a6 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 554214190 1250 554212940 554212951
    0x9090b1b040e010308091f21090201080f07020c03030a030614010f0507110102031e0a200d11150c030901180f0f02040603050609010608010e070e010510030608031813090519050c030105 81
    0x8e018600c24161411181c3d05141c6078101d103c0144070a000b2900003174800c100140407007151008540c002060284240400030b4404001000c1d02c0d600d00d206040200904140d00034521616414031040e001c540c000c545081e01034034a602d54505140c1580c441e02c603034094180c00281940010055503004002e030507c00d45600d254001010380710031442000170a0f4140302040c0009948282090380741c4840002001c1c8103a00c60b602d05a44070f034078003030f980c642414002e50b00b5005441d030341428414082518406107200c4c40303500c030080021500410441c00c3c5030080e41000707402d441c44005c174000840d80e0307441010300e6240080c1000c100c0700d43d01c0c1c7d611072500030100d85550702039540382d40c18400d0000a005441601c11110000c0c4589410310b480c9002a5106207c0c4620601d20f041112101c64081c0c0c00020084c10003606072520b035407441190744a01c0d64851041c0d40705480020441a9003100ea1050105081e00b0a00074040c403410003840d402860280c0000f5a620701c50034001c0081c0799001d0007100e00c20f2 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 554215440 1250 554214190 554214197
    0x503041a0c0c060a0b0109090c030e010e0607142802010b030a05162c060d06060e0103030e010201140a0c0e03060408070b100b030a1509090b1b040e010308091f 70
    0x2e0549440841c01c24001800520301c03181000c00b560410303031f03024013442c048d5040c5001c00201031a103440b0036002450342a01880c880c0d42007107690300e06100b0100e0914840d8a058941841c0d8000440582400e88100d50301006212030807411400f00264a0b0501018014030780000134540006c400080e1030840719090440d0240d005040c3c1c2000f055281d4940c038020600c42d001250409207401c2c5140741070b80b1106011107000c110a002410560300c91000070207154000208101c0241c69a07400b07400f19209000650100340d0b80341e180d4186500c14031504178051806c03464104c443d113a407041070018040b01c5076807008020074412240e047c0e03a02032184a000300d2080342ca042d81e910082c035141259020040000c0c19001e000003042151852610451364415142000090206001810f2010304d80031500800c1010385803c007400100420200d800c0c1c041da035100a802d40d180700029511040b80700d2400f071521100181c078010800100400054103802100914100c801404817600200e444400380099001 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 554216690 1250 554215440 554215447
    0x70e1f03080a0c14060f090f0c0312070606050d050307060b010809060a11311706040f2d060b0a0f0308161e0c080c090c09041104060201090b06030610060503041a0c 72
    0x355020042360303075084094005040c0740710070038000135220141920000e00c000380c0000c20400f0000d00d80d1105010b020003c103401440a0b41b1305003540d50750080001291028500755107050b03a58010b000c40c5115012038002098103541d95010b01020300003003010002c41c454140300602e4045852005680d83d045501c22000104000e2050891920607550020040c072445090160781c5100100b11580d0154000441003220341c000d24001010303030322401c075044140c00300c820f203120088088123605030218080c4105120764100c1508004610309071348a00341c1c0c0409010030410001d040940584046000100380d80da003894661038084140c809071040458800107480c03000d08001c0b2600c40d41c0050010b010003061030084020109002480151070031a2000700883c0c101607554071a08100c20480460b00c0322a1103503620503020f80a0400420f04943c1290b4240008400303090000b86a4402c00400444441c01c501d086010b07a0550f10243c011354510458100e8002d520081c824400e0180e409180e2060780d = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 554217940 1250 554216690 554216701
    0x4110f09130618030519020f0106120510050c09040b030c0402030411090f0c12130606090b0a080102090f010833120115090b010e03070e1f03080a0c14060f 68
    0x494000039142500714024a00c0000480c5c1d200080d2003400080b1141403146401544090345802d4290311950f0032582840004641c004e0702c11032030103031540315008460300046844c00013400d1310000c54803201e541a0511005850f0b26180c0c004500c0c0600180030354150401400c08a8113981c4112025508805510302900982c1010030109511840754810140315087c501c1c41480244038041064080c00031410106844601496047c2c0405900503c1082100c0e507411030240a401011721183c441c0340d10f0500065034030018002c4648001d40205880c004a03c054010340300f01c507014001e1455031400400961a0010142e1002140e007141c808098041d142c0404110031126048194401a4100b82412000161070b0f0303145000d41c0d0854074080742c04202400100e41c0c1117850f41409600d4800c6000002e4111800d8030b56a02132511841008000b8090b005032200103481031100400d120020001c0c2c241180c40391980400301d074400c1050b404410700b40307900c2c0c40c5415001d440f960241c2050b0414010b = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 554219190 1250 554217940 554217953
    0x4090912020a0507060e12030a08070306140105160c05030a050705100f020604020d14030d0b04060b03070c0602090310110306030610290c0a0510140f04110f0913 71
    0xd4510100c1c4000c00580d0220f40d6400e4484500b8030a070020b01281d401100001d94800c401581507211705012291905e00e40c44d40142059016200381021928282000c204050f0252903510007607010703142c00e031404814140900d070840568006031000600b0620101c0e05940034003040e01e5050103078005100d410f00f030008000c8054a080c900e0b20a109519010804c01074011a480d0340c0700742c045400002c0070180341084250364040c0400d1032841d0000080c01011850b03154094581003c094404102190319040d01421502c0b00340c40d0031003c10413011051000800b5a0014141218042c042d103408e880036a01a2059410310052070007a603001100f000001e080c01c005541c0e004403078250080c811403404d0030181c00f80800c20540004519008000014a054030045400e500030031b90407a440c158660a20355111041c180c2c0c503490032820241100b03240c030750384600d15000d640007402102003511036a850400039200390200c590481140940c04a1603a035a0828600c605000b42c90600b60310b4a074030713101 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 554220440 1250 554219190 554219213
    0x80703020d0c0c0611250609091109060a050403021302300604090302031207050301080d0807120c031b03051501020a080a050a02070b040803040f060816080604060506040909 76
    0x1d0003081000004200803036031101401c0100d41356400c00d2129460040280e50400e2190210321109140307104204a5090240c1c01940845807140c1d0303414010f645685503032041d154040c010701030040003400051000e20304100100a1039149090051502e5961760100d00c116000c000006a49a8042015a2040c10000c1054480d0b42e4010b0300c04544910040c0b4002800d0001e08100c0c01642d0350102001003500030811621400307c0071401d09090301d00207000410a9009004840c81401805000201c0c94007500d0755074000d1019850b00c0c03403217600c2c108481e0000c00c0e04808103000c05454a1038191060448141c640c64000f803568080b40c10f20340b951021103401c4489400034110341c0280c54071400700c1c4800080d10803690381e0740303021603584041c00c404a2511071960058602080001000502020000010006c0f20000c40135080c1003940d4070420380e030b4001d041f074211103014500f888140c1124810051b0f154044401440040c016440318007003000d80e0800c1c2c014030040b65468024006104400311003 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 554221690 1250 554220440 554220463
    0x1e020c120d0f0e0609041505010f1803020112140703150f06090504020f130905060301061d34050d05010f26070e071806230f04050a0308070302 63
    0x20a9400c4841400801c200b4051041d50100f0802c030400300c0c040c1e500d400c119500e501d00100309200121541c55413040301c00044c401c1b6404101c0c203900e10392549004408920348103000603425030b652440c3d5001910700c240782070348601e43d099071002d543c10600c1e45d12001174001c40407030394001341038614062020905061a000150300d0b0f203507541d08010566011140209036002070780c0160b2903400e160b0711582e00e400340c007018030f200003000500421030022680c4140e00c00e2008130000d202c056030320440c01604014036814020003130f08400014002003202e107002c3d40c13000c0c0144e0303100c5540200030240300c103550074a20614000950000744e6140b00f55050085c0340c007403d4225496456a03182001000108000044401d800106c10700c0080000e130741882220018001c10462640d945401031008008984240a145032402c1300c010104801d032282004031a00c40c01d01c20484803424034201c9074109600b120141d0200d80804110109964450a1048006600c10065a5120391a0340b070041e0801b0101540b = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 554222940 1250 554221690 554221693
    0x611030412020307050907081b1809061305100801050a18020112060801020a050405030d020a05120c010905030703030e120a09031128050a1d01060f1e020c12 69
    0x4440001002008440032a0140300c84241c0008651022078200034483d4011a84441c2c2801000f442d035401c180c840d8851640e0281c04100d10300310452040362030003000300580320784079400581c080508022880d00e0300b040707000300f10610344d041040d0040151201210180044100100d0400c400b40c4d007409081e0b08051042001d005203241d14142c204010603481c2d001c0c1c100410082103564006099000c607014201035002503607142044e0340080c2c074035402881014000e03c03a030000a04c029202240da540c000782c1c410098003090b001d2400044464000608002255580d04030300400910200010b100d04c03442901d0200303d80400c240329605088034040341c84403c4004104003001c90f48e11620302030650b503201100c1100c0880c8030010a1450f903540f0100000300c0b4050707c4c480d0400303180710341d5030707040700e4080b074064201c01d448010000c210607110b482041d2043c01e0b40c0041c040c1d11b00928a041d407900544c50010b000c03900301500c1700b482d10108203c0340c0258001031800192420510b0103940820f00080 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 554224190 1250 554222940 554222957
    0xd050d0c020118330617012309010e030301080a02210a0f0303140406140601020127030e060f0403120504050618060409090b09150103020303040e04150603060903080106 74
    0x1051080459420070020029165401c00e020480d240090710b15940d00c0c1364042c000c5004040582900a02041c05000c0c19040e8030410f80e8441e540501641c000880942e0b0712100b49940c0c140d414042c840c000d024180955260855032110351400c10185008061240080081c49a00d005000f008a401103001c030a2440c0d410f03070301058480014803142542e900039002c544201c00d50504800a1400728020b56200040740240300c203214540e0000300103401d41050b0744c040c7c0d8460340016804c031380004600d90140c4072070445040042d540310344e00c0488c0318000d00749807444540c17900010f48a07601c40600c2524494022801f401849100c1c0d84916240c442400d1651620f804d090010b04513004020442c18501c4009400366001e844400c02d640080120810038071428203a460a0040c40c44200c44404040c4100b500404214131942905030480b1740142c040e514150510b0a2405046801030080d40c102c0c141215907000b40501d40302e500001e5000e10000201100680b40c0240461010f900003c10001e816 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 554225440 1250 554224190 554224211
    0xc0e0612010914040b0f04021813021206060d0323070f05070603061409070207030c0909050606030a12110322140108070f1112180108010f08070e0a0902030d050d0c0201 74
    0x43d141c49410441b82d504555460b40c4038030006001509101160800800901c14031000d40f180502590a1610032128000800c0d20140055547c000443c1e600d9403080010005030082402500d0070400c90303441ca9903c8455407400b0713079a030f2006d0348441070440301e41a04818102c00d002041c05540041c01a42c5000d01c4031925000380c2038000c405c440c040320f1282034490301003180301d802040500000d580c080000443d0555890360346006026105080d55107000b003d0000e44503181c04140c5220300b0b0703880300040c040c58015010131501901c000203801d91510080290040a9005841103285650b81c021000f540b00c0c18842e801d68040b000000a60500518034148503d0540000c0042d03401c85052078040c104c0e0302c510400f51b00d003845880c1c1c030b030a807a400095a115442248401030415440a80390707a480d5980c0c0d0259034580740700b00d00c41c944040d001998103100901e1148038454002184d18000305038901c0b10340003c1d080414081702d0f000460400903c3d031010300414021100420140c0c0020005d840c2c10b03 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 554226690 1250 554225440 554225453
    0xe01080607120b1e010e2202030403050c070f0911031302041107061109030105070903150506010519090e010f08060a11070c06091805190c0e061201091404 68
    0x1070805000d200c0e4090002c402004550300c000240350340240034408006078103a100011150310f070303401c0703000852103111208542003150301c2103c2030042028072014020345901710002500050001c0342013140400009289010800004011384165042c035000345240c0745161003198240b19501c550410107204120381c001c044102412070940603140070400090101c4500b665204103080100078030303d0400c186c40c94008260241c03540c0401640200a40e45441200380c0d49842e0920005100180f104000341c0c0b0050150040c2d0b82000c8103041107418601c98070880d035044079081c08641c000925100041014032401c01801d401482905083c42585081502c80c0791030b980700034190008642c8900b14a0b01118400040b114030f00e03003000140314056101c003801400c1c0e9016124a8000d180010040090314140340305442c010304001c8108080d484400480c0c5001d451220003100900c82005030865003611010f0007040d0050860041040079030400313800340c0840d151503503541e5000f11100c0801000030007 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 554227940 1250 554226690 554226703
    0x90f0105060a0e010e27010e0c19090308040303120609051b070c09090b150306060f1c0803090d0809030a090308071106040b0c1e0618030409020a180e0108 68
    0x201883c00589200c100c43c01a5a20b100740182d05070010401a480d181d4000d10701e030700f84403040712258200040d9a8821051a041c0c100750b0300c94084580c10084007600400c451514120102942000b0904c65a41d07282c15038680c01030742c81034000c20740144610f0800040303440742c1c501034414101d04100d5814003500c4080ca46080010181d6070403c00039211040c00100150320008200465040c05010032510b400b203103014090350013141b80b040002c60010a45000300314076109050180c400300c0208144020000c0c003001c09540f1340340f09040d02c3c0b410360100d03002c00003d520a16001c401080c2420145400030031100000700300d208960400d212040b03082d640290040101d0303812a1815498118500b400340e41000c00f6849150701c244000390004200b180b1101800d003e1840030b058074482842c2400300e00d2144182848409160421400105849209100018198281d40842303081540b5900c10008980c03101c0b10300b030081080718100d81d04003140b01c407400024101e1a8a04c404c5545000c081a56415 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 554229190 1250 554227940 554227957
    0x60f11120a0903090501050705070803070f0b070212090603040f050a2001051606020309242d040305030c0f16020a0609031a070509031b150408070314070806070806090f010506 77
    0x40024611049c400200b21040c003900810382034a03650400361401e6002812903100407541e02c0d413070700001038525002242240b0f007205030640c507500d03000f0001f0410196600060045444110841d07404d4042070040008203e034601c2400085910140200040d0b184540d00d64001d041203010003904110712554018144c42940c0000050303125225160000c3c189282030500c0441c000000901400070031102d00405e0140c8240d103650051000d49851040d91215481c16400803112141c0216001901c24001564050300407031a26040000c1c0c10452441540010031040d82c00314048114401d5280c500b081c240200000d08186440c0d518582e101e030350045a80090180810900000540e00c500400071946210f10080aa9003003900c041c04408802d000720000e0340c01001c02e0350320315560315400d1080301e060303a00d18002030011038039582c1c440058410310402d110943c024000c2c0001d130000d0402105000d00000d4030707070010600e0254140301101030010280081510380744e00400580e1a503404440c0340780e = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 554230440 1250 554229190 554229197
    0x31b080c27040201020f0307080a080f06031b0402040909141023280c0324031b1505030702120304020f010f02011409030a1b1e060f11120a0903090501 66
    0x40d911800180e046c8003001d0420752450000080110030015118002c0c0288800c645410b03c2035243c98503414980e0380c045982580680c046100c4012140ca00c2d0103030002103034000c02c0540341c140c5450ba800280c0d42445011078804151800080c440b072414006a281074039500b80c100300d10342c2c004100401c1140c0421031140c0080d101408540540c10280700240341024001c2244143c6041609150040c010701540b080043d2500006145007000c44800000010103c8012a40c46003175440303000c031401480c0701c400d601a845000010b4841d5071705043c10040d568503111a526407130b0000d07000e81040c1e0350100e140350b049001c10802c001659440350000d20502c1c00e00e8007841c00721000c0000e900403e0420342080783e040d102c0080100c00d1030004001c202d84105596444940d0a00000d000001900c1900c0100305048080200b264003c070020000706c0c45c0e00400000c00e0004140c59000e04807290042e900a81060005124480880c02c20a040c1c10641c440003c0101d103280782c40c018a01d102500509040 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 554231690 1250 554230440 554230519
    0xa150506180c0d020a0503060103051b0f090121150e240d020901080c100201060b0406030908070b24180a0b030f070e01031205041a090109031b080c 65
    0x60a40102c1550351403940b0076000c564039280008090700310b402c100e0b1201d00290811000616a4450340359014007550214082d034240100340d410b00d42c1c00d40061f0605410454400b1100303922500705083d000d19602d007248005418100100400c10036449070300098000c1051100b0300c1071010060050504101d040341c06450b46401101c006101e4011410000c1d41c08807141002091070790001c221014111303001c0360a01e2500c49241401d070b00380c6420744a0b8071500c142c18002001950301a800690459200308a220714040f903a070b844041c0641e042e00d03059400a03485039801d202481c5001072480d203060454100c9050b100801c40e0441405d0010030f14490681c4803007801250361420050f0441900c2c017001521042c0d07803240c04a030303044c040c2440181c030004091100d42c0c1e41c85019a085405850705107030805021031990705401d02a620502403036042043c012310000c082440702000c103122101d20741c0000340080c40c3c490018a0422205200c900c139440718100c0701c0102184985152aa401c45a00c8291 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 554232940 1250 554231690 554231701
    0x9070f090c050715050601080603010b09150102030903121207091211061614010518190f0b2505092404030f1406011a03010608040c05030d020a15050618 67
    0x440d0300030014028511040303e10000013030140f94018034803441e4283e030b401d002680c0f0103040509032040201004d030003003000030210b0038035080702240040c03400c81801100d03c0c0110b24000b2034540307041010142c0c50404003150031651254030004480d0400140d151003604941421b00b000070801c41c41e94010a0f9103081c05112000703445e44002d80e010a000311a100302d4030030342ca060204400e00410381c1030000d5440d0000107860001d0001040c501d54070000000e0103114003005810503103001c03401040c6d41030b00400e00c610000421340d1075158826240ba10325000b01c0f1040c1500700c40301210040d09041440300600c08030140e5150240984030782446580310299894001400840502c1150005850216602b04000a00848007800c1e0400c1c0e8003401110803503030341c402050b02d80003107401d44900072050410041141a204d001225001070145100007406a55a00003c0c644580e9006035005038000c200700c1d0701400f40b030b101c01502800c8120014030143c038000f80000d840e880500340307a203a103881140128070f = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 554234190 1250 554232940 554232947
    0x6080709180e0109050706020f010501231003090501050403030902131b051e0c16080f101d0a05060a0e010b03030d021b0106060e150702030a0201121e1409070f090c 72
    0x134a2aa000400d030355006868000080d25810340341914000c5600b00000040c1ea403512000740502e1158080c0e00800703004503001001100c0c040000058101912a5524804140280710355070140c0e201c0c0c0c40014641c0103134418032000a40342d1041c1d40b1120718040ca4038608001d99286007810500c1480c080342da0b28032404003c01141010707028044100d6011440c5030040708000b41e8401da0700340d80c408404810790f0fa1815070f075a0314454110164031381c002c40b000610f01c00960300b04d1103054805120701112a015940c455141c44030b41c05040d2880c0d072111040c442c141825225102068001c80e0080c000b004004000c00ea0307a103d521200303114954001072510021138001e91804090b22002d0003030014941d203050041103065400d01c4103101d10700400015800c1b400303400460384803d5004d0050700c1401520380054805048030000d00c010580c944003541c510f05c00c80c1c0c00d001c1c0d84c00f02c0c00b0000601c45058006030208523900802c4183c140d8450001448100c0030301e58048200c4201c2030700843d40d03802100303044 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 554235440 1250 554234190 554234201
    0x1e0403021c021002040902122202130f0f0615030e0c090603070305060106030203090d0503010302031011130b07050d02010c050316090b0f070b0606160803090f1606080709180e01 78
    0x3019840485c0109216003aa002401b201c4100c98a241036512a035185071000b04c1c82c4020b045e00824a680904018203000b08461030070081c48600269410520b9102416240105440200307143d03207180c24082c074004075900820340da0551904010902c03901c22007603524110a40700c0c520450104001416076903041208001644e40082511029652480041c0181d00181da07913505c0c0c2d0007105000103056100c2d00660b4100ca40081c02007050400d295400c400a0400648490b590401041400c4201110f400154020500d0070340c2c0355038411441c10114140390a03e6400811a410503101700c2d0069445001d507070304135212100441500880701000d48805006900085005401145202c1c1c040f070000068a6024081d020b81d4845603922020440385100d003040034a400000540000045440a000740d076120411800712174442251101091030a905040d0700207180340780d01014000d41d43e1080440c0d4015010341883c001480c20305216a10b030006011007211030710b55070340c0384021054094114 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 554236690 1250 554235440 554235463
    0x70b041424130806071701060305060d020402031003060b03010219110319270e16051e07021503040b15030a14010204150c020d17040f0803031e0403021c02 68
    0x5a6600d620340361140d040748602e032084011038050007001511440c0030300c2c4281d00f000350ba800882c02c144c0c28084242c0007008084d0080e604001003030496001a150351004600404804d500c80003410b01e5440c1c110241c40061010501a0340140300144002500311500080c100c0d0b142032036080840c0e0600000d1650040c41100041c468810100340d400c1500310542581004032039400e840041c017102e18012884103a44030745003024401000281c09040111042c1c82041e210b480c0c058900f01c10206000014645100c1040d5081d8000400108600e0102120017282e003403400c40904500d000d4403840b184400003404640040c1104030010346030ba6042c0221801c1e0396124480c034003082070b29000c06000b50800d0142d0021820060301c0480410300451030211a503a0040c6150340c5a4002e9440c010482c02e09000c102581000b40000b04003007039a414954040c00d074a00c01980c0362311740030020f03180c8000c0c0500021602001e500034000400d41c0460b050b4050012040310315040402c0c03200c2245488a01243c = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 554237940 1250 554236690 554236759
    0x1c20090114031003060507020109021f090902120106180605030106030b0f1002060a050117060a24080a020114270609060c010e010b0f010801060315090f050405070b0414 74
    0x8000e8507140440f0004240d90180d41e0401065940c0c4170203038200c1f254818041e51201c0fa440061b99840542d0303882910a12451800401c440d655410202c26a000b1200307660301c11007000014040550f01403003a0440103c895a1507240b64a0070a010b030041c40180030b41d0b000c05484002e00001600d404204520003000035185c6806403410b41c50007500c860013540c99440c203c0c2800000911000c03102c0208101940b00c401410141e1a030b00307400d0004041c02d460341c50700001d6000c07511140410b000d10310401401c3c100041c0040d12075900c0010810090034100d402c000106110300300241d042068483c51340519100d001d40c882d022000012400d01401c1c2c0000d40c005070004011302d80c11410741002030803800c1e00009100d66038045003000700030300d1030b441440d00141041c1c00410207644240c2003c4840c002e551007100f0f00340e40b140d0580050f6484500c100b424075803110140f0003041030070849500101304038a8001d04090130b051a28204604040ca00c0f40b08085d004094200100d5452520b40d404032001d0 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 554239190 1250 554237940 554237947
    0x241404030506150406150c0c030605010608010e0c030f1503010615050c071a0f25060222050135040f0203070b09010e0409050a05070b1c20090114 64
    0x182869840b00c040b40c0c000002504a80400201d00b01800307444260354011583d040c3c80b0100720b800f1070b13401d50704034029a22000202400004240302d80718041c007810140c2c0c2d5070714066040010740c0080010107401e0b0b8280b40806c01c10800044079088030f80d5040714000078100d4451045000190250034503806c0b2814400c1c00c0c810440b50250014014220302c8212001e5030809642d407520544200b14101281c00b520b2802c0101c0e460f0018000001c20708001107480114000e038480c11940e11034030003a0350441e80c0070382c00540c0707241100c600800c09004e03242c20394605c0407407800e1100080511681301741c0c202e18080c010524403d61003002025800d2455072003e044800c0c40d00e41070544144440c42c40c00e038001e00507402e0104140c43c218084610400303041e110140314400d61420300009000013501542c80780943c0240c2c50000b407003408860010907400c500c00380c851480c60710400041d400c2c81c007801c07411445d0041c45a400e24a00755000070348946004141e40391404c100040e44c001040540d04442e8a070000f = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 554240440 1250 554239190 554239193
    0x2150603150c0d0b03010203010b07020f030f100b01080609040f0215090d060b09063c040c0f030b0a0303022104030218090d0302030103080318192001030624140403 72
    0x60912080307a03d10611005640d80c080c10300300d00c820b00580c0e40c440707001c001510241c2844a28000e40b4040a011180041b420814003410104031040181c10291500e02c2c0303220743e6900011864102504540100c002c0c1040d03500c200c100102014000c2c007811400c41c0359400c80d110842680c00100029104403404000c074070304000113259008003076100e0006040402d0f418107000300c0050032078403c9410400c0d5400c182d00040c404403035400301c2d0440401303807a0380034035103840c0c41c010400358180548030f0752000042e0140182c162201e689006002d04504802000401c2d0f00080c200d480c114805002a13068100094110f40d91040750000b0b0340110001e0360132480408401031903849401d503d07068400035184110b045003a82301c20720000d06014001e20109110384144400c610421000004503034a1440e41c68000c900326650741000e0312510005a004c0504100c080c44640f4048402d02e4100081400c159060050000607003c911080708010b01c600000c40c004c81860030704114140e40562540d90300d = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 554241690 1250 554240440 554240461
    0x270309190503070b03010513091502041202040609021801031503051501030302010c08010506070b0603010605130c0305090c06121306111c060b1e04050a0602010507020d020c010215060315 82
    0x6a01c1101e00070302c680600050300110342c1083e42c0c16204002c1c0861a540f205501d5070002d02020382040d51a4030035040f040702c20780a6440100000c190724031041c034860205004000c01c07600c0640c001c240090040cc0001c050080c0c50244074200703082400c001406603205419440d4a02c4107400080643c4100700c24904554260102a03040702c1c03203079000740724291030141c2c00c4514041c00c0c46800c1c6c0159080c440403001990035943c107030b4045405000024410f9a0b00b0006c1c100350031001d0f00781200e507920103c004185606018003a8092410380042c002001000041303151780c400c12900b00203c4111101044500101e540c464101da0707003146003440103656401e002c0d10203520008410718824004000390180400a002d680c007102e1850b80c64a003810356020050003690020280d0342402c8404000202d182d680b10400c03a805060544d00000d0140f40ca4071010b8a440e02c1c2402001c01c0d54040c2c050150942c0e40004d4078158071400a000103415140c42001ca0b10341a414558080d9903c030704410405040103 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 554242940 1250 554241690 554241739
    0xc13030209010b1b0d120c0516120f0810150219030302030a0c170a0203090a080c03040504061d161209110a050a0f050d1109040c1805270309 62
    0x39412072040110901d00c0b16682d601c5001a1800308606265103940c00d43e16a202407c030741103505100345040d503844000b0911059030304089405c02103000711846101c1e1302200142103a451070a00414609051071503655104c214840d042c184c1e0215800001045d10038031000c1c00500a018644201d64207a207030180c043e40044039103505130782c90840c507a003c0c648942240c0b0ba02c1591140014203988542c0e4241020350300080ca038000900c85c2171600710008a04d0401080380c44030f888081c584031410401004141e90041e032100201c0c00c48281c2c0110400c080303a06150b0002c0e0f5003203421a1141d807090b02074665010484515800d945403130101d10070301c101c041072000062401c0b50642c800d00e44070802c2004032582c1d80074810444d003910505004070305003120651001801a07503010382e510326150000e100010b0485040741d0018020b0000c0001510144034651000c22802040c03000345098184003040c0c4d2801c500d5566100400c081d21491168148100d440407031001c0c0c2100d02011070941d441901e1031 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 554244190 1250 554242940 554242957
    0xe070f02031b0102190e0f09250207081002040306050703050105031f060b04120203010c08090c01110a120210050108070e070e0a030524060d110907021f09031d01080c13030209010b 79
    0x24505144191800700408c41c81003807008540c1e615030385200792028004600d079900c0c40540c40b8403400440d5104040081d08842c0041c0b840140c0c4e076505524180e401d494010300854241800d1500606c100c0c0d0307010070305103070102d52880320300e0821038101e03180d0005d0314450b80881c184003000940400d103801c0d803410545a07103000ba0000c0c000007002c010f040701d02c09401c0750003581c5a0007106040c5120342c802c080800e458800070703040396030392185600c0311000140d2452180e400350384190a08282d903195402800d005204010141804901d8207010304850903000740329038200b0506041580c21542c40c02046005075820401316150b030150310050081e0700090313082c62014041d00c503000900520b00a01a8001036a00100d10082107032032a0911020140103880c0b0030960180b04485200742c0030382c030808100000b54142c0030428032030504024001800c1c180e030860b01c84002c403c0c070b50640c0c2d0304a400e150704404010112503460710400404a448512070300020340c0041a10300004203030103000c010385202d4 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 554245440 1250 554244190 554244199
    0xc06070c0e04060c11210d092108070809030a080a18060203071b170f0712020a0c09150608070e0d0b1803160b041a100e070f02031b0102190e 62
    0x1100c090904d81c2d409078203059121402180c402d0a11ba0310346d0f030010b4003c0c1c000c18280403c0c800303115592207040701e00707200f810040c902c0ca1089032184103a0140c0c0d020f40005090401c0c84076400c015952503101c1c81071012020501032903001044074070419501580001c50a04c401e800640f010340742ca40040d5000790356801c0065210000380c1d2640d0f44184090250300d5004065005000005280418940003000001103d50003481024081041040c0310780e6602581d0740600198140c40c9844042c2c0c1003550440c0c2081d0f898a1551070805da0b4120076035080d0b03202030602d4005680c50090890304c50940f1480c1707a03000800d4480c00c008000390902c0c010300600c0e00e00200c61948883c088541c0d40c038054078800c0184000400c20300c00109a811044941181c000c40399052400c000c132450000d001d000741e40e041240600e001041140d1460101d026800c800c0c5032400028103080140000e55030b00a05091302900045541810f02443d0258100e60a0011119005180c0f010784c0c20080c1001003024400d0380035 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 554246690 1250 554245440 554245457
    0x3020d030b0d14010518010b010c0605091e0d020d05070203030304030e2404080705150717070f080309060f16080a02130e0a0608030909010b03040f150b030118050c06070c0e04060c 79
    0x3c46e103041c00354030031809042c0c0d502c858038140ca40f02d442c05010050802c551074050241079004600d071042155071540780d038030000c04194503005002858621001e680c203040090901054005a40110440c1e80194140c902024840d030381c44001354034950b02c2c400700d401f000c1d4440c0004803a041c80360040e04c1107600304c030155100760365200d0134001890103c00c200844c042003001800001103156800070100b138910107040d403c294540c1d650300a2004030f02e100b40c0b2102d034080304111601000300003944e407150084160230302070300b4040070001c1d2500c21003166106200340741c0d0001d190001c1c0d642c10b5580d016240140c0000055440c014001c00b04026189010700a081c16000700e01c1110001c200c030450307500944030f901d0507860306a08103010303040070b072084074000b000c1c884036000700d104408a01c9030b45034202000120f188a0100701404c403203001c10341c02c201140003220800411b4001c20700040344c1400743d440c240d0f60800d600e46040410074a400c0600d0050054040c481405040d82c0400e603402041d40342e2078907 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 554247940 1250 554246690 554246731
    0x90d022124100b04031205070503040e0103120c020627060a09030209100305030412020f040e031308060105030d0305271e1b1302040b040306090b06060703020d030b0d140105 76
    0x2c291998000d10540d42d070100000c100141d10702004840f40f04440c40c20b1818908035564071030443d4026402600f545043d8401031041c810419070b12000500c3c01e0420740c0d1445000d901054407409188009900560a4103d581c28440000c042d10b00200e40103040e65518441401c003d80a10881d0005901039062000001d10031010006541c00f601e0300030b0000d50910b45010b180081c000c002c80012a04080d040851410707a403682c0c062002c110076000055500d40c0309400c44641003041551181c007880d80010010003a80e200428507101d0f10702c0038603022a243d65a00c1d4940d84004080740c016165098124450500c90750201e00c81c6105140300190151400b84028200da492034000803a8030110340a450951143c50b1072140126200c41c940c001609159940e80d000c040d40c0c00681c020b070780c1c064481c0d40030010044d0200500ea40404110340c181e0800381503480c02540c0b0089085400c05161f600c208008180d600e101c41283c1c0190f1128090400f41e490080e202d001e40020349610114103400200c0c4039 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 554249190 1250 554247940 554247961
    0x8031f0602030f0d090804050301050f01090b0303120c0d060510110d08040b150307080f1f291801060203071505092d030a0203130803090d022124 64
    0x300b0200d1103200b89414813203502200d8000b003500d5074049603658001c200c001403e0320300f8001c540c421840100b41c0007682d0715000c1c018060341c0c0c51042682c86600100000100c031b1022200464100308038204e90b41d1030300f0421450b00000d25258100f01d5100078004814400c05a1280c680c07003040f000c0700d00f0340b100780a039003005a075940030565000300900e100c44005541c00c00046042c103040d00c40181183c00c400e5440300c585007820b084038003000b19034000000c0c50b1101104015421100382c172040042104180142d10410031620340c22650800010484090740b030f5030341e0311075149811841058a041a5655800060356a40c40420201e40c60142e4801175049a64107228562148a820010380b03030014404500e60b20403200d82c030320a102040500b42a803800003042000c1c0c8129101c0d0303002107070780d94100d49114030003605c0d0b5840a00709510402c2a018141c8424444202d40340d4180c5e030f402682c030040241ea03281a2070403041d0344540d208500c0e40181a200d41009000052040a0010682d40b204452403 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 554250440 1250 554249190 554249197
    0x20f0c0c0901030807080307180f0303020f030414060f04350c0a050103020a12050f0601021005070504060e27011a0c031821071d280908031f060203 65
    0x6014031500340207110120321b468005640c060418940030702c002c954403010b481380f1071054000d800039140070b18003401016010015032032080c18003030040d401c19203040c0800b18002d090b180360718041c10b0f010440e010304040c0b14090320060820200700407602071541e100208440101a0b0030801c1c48503031002200d0440c1c01042d41d1032441005044180801d081c030b0010760103984181404020420400070b0350301650100d2090901628000c068840c1c5400d0501c00246011040d0170401035440c0f40c04180441140c1050803179044039803601f400c00c20044420001500b035a00c044060745070b00c01d101c0601030a0700030072400606940a00a140050300b003140c545910070f00415a00ca28254410009041c00341d01084210b40c00940c020a4103610400041c00015500341c44002620f09512680c01400074101511407490300250181054007a0301e003c10700004143c0c2010285000c9907a442c032010a101a0ac0d00015000e641181a640e80c82c1400d451510382112201790b80d0204240440740410752030b02c08402c9 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 554251690 1250 554250440 554250443
    0x3060512060601031802091e09070e010312091701050109060b0702030a080f040305030d0b010318020105090910170307120203120c0a0e1509030c0a0f03060b0310020f0c0c090103 78
    0x28541d42ea80d40c1c00650040001c102e044400c03150540c903920050b61049800c0740304100e4240452407000c0101c8250441100c042c003015103503003140b1010f0014240d00910641181c0d00101d000c041201081010f54940800d40c00004810758140c0080f200f050054210302c2c101c82020030104052070b070702c1d0202d654600503040005d50507084522540e0200f102d9401800744000700424483c40c040c1e482d40c840d4a961722180c0505040c540b64100362080f9038142c480c4c44504070050b41082075003019a800204284180e150482c45004544041103200382c16041d102c01070408208288082c982c0b0400f113035502e4120034004c0f2100140001416a10f501c013005a13904030301e4242c41c01c0f85940320000c4d40030680d00143e20f04c90802200d20349900f0207a88081100a00c0c002c0c1c0e0400a54500040c02070500744000700c1c89485c002e003d01136080000800e03503010340040300d411420000c0c0c2c403148080000c1c1041e02030041c00300700d14000320b01c6018401d040c000810f11003c80341c0440c0d8101d01d5200500000c600d09100 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 554252940 1250 554251690 554251693
    0x20c1e01060f06260106080708010e0606031909020339030601051e0d08040302040b01030603020f010c060b0a0801050711010603030504061b0c0f080d03020909070e0105040e0a0c03060512 82
    0x401c210345800350201003880070085007070312002440c40e00042c4e890b0600340e2181d40000d090105124405401000c60707805030070300010501092038107401040d1903100150003038041c169145900081081c16038800009079500405603a41c03074103000d41e4440001c11041801ea158a031440c1040d0800b20741146080168030040c02900e030503880d04007005100308201d084015041a80e10b03050342d01b030b6650034842902602c41d20700c05450300c0c118010704c01112440611207040c1071800f5420b20147c1e13112030780e20010350000d1030410901131452801001030b002e01c2074100c0c1c00c0200054080ba00450640185100b0403803036071a6061b810480320202d007030b03400d18400600420005c02040c0710003841010f05811031034828804240c100d2155841518514090317218402c80300c6d8105003440381080c240304038003030100c0e10314042d81080314003400248407000c0034045400344883c0c00b0540130682d024405960090a0142c4641e115103485685c11001e44211036080c0d000a20b040380103d000d14000d901110004043c10 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 554254190 1250 554252940 554252969
    0x14010509030c0f0115140a080d0201020406090b0a200c040603080702010201052a1806070615080307020901090b031c0c020f090c070b060a080703062405090a090206070204020c1e0106 80
    0x111003030401c0c6d0074200200d821582c44c020110746980c0c20441d15100d1240d903400183d032980b6084008040d0304a607040502400b00130010710b26410b52001381c10020001c500801820030340c02055541c60069150a4280c0003802d184000050105030710141640340d0003a002486580e81d400103405140c03082c3c02c4420498800d0160030104040a800600310341603800510078042e40c03445002030f0294001c1101207440f2600c59941c0250b482c0e0b0210044010706001000b141415280e0340056444241405018096541c0e6600364180d0340c0e04100c1040b01c006030010420030b0850a050041940b40480001c4e03014400103160341c00c03075040c02d0314103a10440082c008641000041c1d40e54110540c5c001c8c1c4203c0d489480c1007070215040e201408131000440c4500350026014850444c840341c1c140c0e081c00e054428510f41c503001c0005454508010f5441080341c000080c03050314920020f1285c2c0120300000e50418804541164846000070300d054031040e0035041805aa04da00a515007601ca00313010752000c022814 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 554255440 1250 554254190 554254199
    0xf030305030f0c1b10110310050f0a260d0807140a09080303010f0320010f050703170a0903021e0c010e150f090a0f050d0b0414010509030c0f0115 64
    0x15030289030000080783c0340c14030b422003030a103030300c0b00c50243c0004034190b4100d00000074251816108070140000f514466608500e0851a401000042da1051900a00d0569110409984c6001014015001c10150800c0002038403400940d1618043e2040211f441a1503d400c1c05500650700548203006940d62404080300c85045007e21f40c003d841000c00b8000c50b0700001c00c1e100c00a00207035010308180c5070418050361850030314482e81f008400701244401c40780414500c1d9039920000a01100c416800c10b183c9d00c60b41480d040300c6403d242441c0c510703100028003e00441d03401503002011b080d40240d08545009081c0030104c07104c00e80c126903c1303000d940294560080365025610142c6119001400d81c038a0300d40c450480b409030303403228109843d1114000f800780801e00d44500c40301d000d07100700300307040752a141408041840f1600d841c01c007501e140300300000035040110208540e01014100402445142026001d4a582e038224942c580308500904c7c40341e070440081486a403100c0c3c120401c100d0005c0303140 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 554256690 1250 554255440 554255461
    0x211406040218090403030c09140d0b180303040321181502070803130314030103051005181c2606040209010e09100f0501030e032b0c0201060905010f03030503 69
    0x4500b01d500c2c000789188800c11a40d41d40c81c0041c421400fa071408295403140001c001d02403182030300b08090410101d00c1c66a80c40c1c0b60030721002080750740000300001e55140c4120910002120140c4840640710000401003055030000f1f0481004480404280500580401c1042134806a00383c200301110744610700380219021800035403168070495801440c020b584d4030740c048554402c4600c2100111415044010103510038514131040549420712811541541c8d00e16442c2c0c1250b4010007030b0340b81c07120007103940b403044000703412102c0380408202d648288429582490000712000344001054050003445070010041c00c0d1b80e000d070604d055030841035583ea201040002c1d04034151035810850460f400314496243c16410b06d0084403407800e41c84e405464110709034074007000d0341c004034101801c0800c04c2d41c024000009480d000c100200f500807210104510300c24003041e00c64a592001420a54507005080c3c040d48108292808640c09010503a214003c8007180c0d612031100070300045040002501d507408 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 554257940 1250 554256690 554256697
    0x10501020a062711030f0d080703022506090302070b042603040e0f0108010b19091e020d021c0b090c360108100e07050702030307122114060402 63
    0x80e4910f1204008544194458418039203801c58800b1007036010800320340340c00c1003130010f1130003088010203a6811a4000501545001d000c08040c140c022079021050000d0140c51074201303a207101c0380e400c1c40c0c0d041e09081018254203101903001d0302881c5408100c1940510071901522441940c00e0010000700902d08004041ca0521001501045c0000b049428105030058050080c240700d100703ca5042c0542c05c2c3c219070000c4501485002440030f5545000c901006100844660f210002084810a04000300c00500754050f00e00151000502203a002e24582c0a400c00003160380c008100340340c0b03030b4010300d01b218003100c82180d01200c8040002c1c20707445541c000b000b61510b80142080e001030844003151507151920300b4001310b00c40781c48003003945503486243d0940c8680220640c0030801e10303000f105080c100010b441c1d0810050001140810f640f400c03c215501d0f03984c000900c51701c1601c5400024a0b0212040040c00f842140c2c49810700190054090000141c0c140500c1c00c640da251401000020350 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 554259190 1250 554257940 554257961
    0x715051003081c14090109050f0105010303091401020a02090f1b0405090408030c1605100b0420180909010501060212180f0a0806130b0c130e150d0305120708010501020a06 75
    0xa46510410216000040d2228000c051090010507c04000d260041c140070b49020015296894100100046503018549008803030b000101d00281c96070b289c00403828a000da010294218103850305110074496120704d0284905510321070206c0700030990009400300e100b81e00c42c1650080000300483c0100d4200e0000b1508600c0684819191012007002401001c0301c02c0000c1e5215080782d00003910003125402600038100c402c071010042a1034103400384010b2545104240c94010000c0380604201c06580404c4c070340713003c0007882c0010754908201824044c000902400300103000c0c90305401c0504908009132102c0085903945500b4509c092402d100004280801f166070020403203000041035002030010302d00071102a055080184441c1c20109807406025052101c03804003040540028840400d54405842da502c3c03032001d00d5203c0d801401809002d44001e0303540030600408800805400c200109140d551031018109142d640002c2500c84001c24420580540c11032604040080c500317a10801c0c0b0b09 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 554260440 1250 554259190 554259247
    0xf030f0c0c0307030f050106050a050d03030f0f060b03010510020115030b040f0803010e07090605041206110d02120108010c0c03080f1f0803040302190b090d0c0b071505100308 77
    0x11001207001034a000c440e07501c180c90b0086000c3e05102400028050b6401814042d503000c0d01c25498070780072600905540501408050b51004404100c03011504031a0380c030320050b101404403645500300030701250300030321609200342c868010740c0b84054010b02035401105c1d403500c4daa200d942d2941d280c1402181c0001c2c02100c21440d0510301a000800c4000550301034292001506028981002d015044032069001a402d2003810710023082101706101e00c1c1d40350143c1c0244e000c00d0b51002d440499803180618514030014a0000c65822280c0c0e0314070090358100e840007c02841103609090b0185c0360800e000c1400760020301c0e00c0000030648000d081007990000801c0504000384201d0920040e040c41e21a0400b29690300000360030415071411446520300e44054841d18101c4d1071405802c807802c2e2081d050507078068812000c102040c0101010100001c00151032078603030b60b00c407510382010b028100205807011540b401d00030412400d0790203103440540e980003500c81d2a00c0359608030003005100d44071000565 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 554261690 1250 554260440 554260453
    0x5060f0f1204140c090402100e041b030902131b05070213090309080f16090504030c1406010918050d080a150b0a080108030a090510030906150e010501020f030f0c 71
    0x1121404007082d02c00c500070f07030140708880c5452a0941c10041180442403040791004140005a500e20100040d003c882d818441103080c00400460041c0000c800056565038240b992117900d0f5805400205800e80b003201c2039540b4000b40380c0705204440500388601c0c1d40c002c00e88040040d090145000b0001280018204908041545011015103203400d004800140c80b0030030400c4040390400c054a9a504440080c112400c4601110805040705110b0310001644401c0810185402504058001900b001c15450561402044199100d000f1710651170741c0e0745000c1022600003210701460003603c1e40003001d00740d01070300b00700103c91952015000000503940e8403802040900b44007809001050200302140c2c0ba00043d5a01500c0b00d00305900c011103d070810000308064582c045041001d43b0804c85d905900001c14240880c01070a50240003402c0d030f454200c0000f141400d0903000000c40d0b005041d144003ea803503200490301c0321a0300102a940b41e1050020a040e00801c9024040504210301114507 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 554262940 1250 554261690 554261707
    0x712050d02030a0f0b0f010806040911180106140a0c020910091406090601050c0a0f03090306020315030c01030b03030f0717190f0309030c03110f07180b040605060f0f 73
    0x300da0040d14200d5400d40d03202000451131a19001300c1540c1081241c0503011212a8000642a110010202403159554043e01c1c010801c040c1c1c02d55040030005410000001c1d1060209041d80d03000780140b6010480e60038801140705040011500800704d00d580d90389984010b81c0c244095500003500c0c8007440800d03020086416012440342c441c18001100b6203c40324180501440760a41000d00303890b041140802a1800d01500003c03020001c80c1e01c00fa200400988605040704c001500e40c0008003001d00000610110440d101000805400218181c482803403204005500311807606000d0f1750960010f100d140724941402024002c55030095503014085040481c00d180a41e006244810f068442100069915940252090002e440d14101001100e400e030300d01801040d20031000030f0401540c4d544107030804505018545100b03001c1c00c00c80c1c0a071a19445d1219207403880303660550901c5d10f001014540d6280500490b000c90f0b00280c4120b280140d402e03044640d603070002c1c01244190008001e00d09 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 554264190 1250 554262940 554262967
    0x1120e0a05030a03021206090108030418020c030a080103021008220201020a06140f01091802060a1b030e010f023c0601030f02040e06071205090c0a170c03070b071205 73
    0x3c103801041d030340140d540490000c00012180064000c034041d12003000188200c98000080760260349802c800040310b840e820b42e8050203413090041000c40c500011402c100002c1d0000d2040f07050700c0c8201c802c034803080030f052000c550b8440d040b00c0fa0b1100c0c80c1043c020003404070201021311301c158010320689240c0e418070344808080c0c41e01a003403025640e00120030400e0014042d0000c0e40075281400043c0230030a1074259070040d0380140341020b4410080001d2418039580035007031903125958003200882200c41c544c14041d2044422083d02404141d414030b4000105202080044101c0c21600702816484c2c40b9407180e0119a1074800700c20710104080701614000d040c2040302e1402144210725203010203043d03205010507504015001001944440141701c282c51300000e0ba00000d502c01007000070f243d913860800d40d180aa5182d42240c00c03510348000460300705004001e40d800c0644403421110340c66845000c2c1960f840040c4101e001940c41404880b000400c60b06002988404034605a81005581800030 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 554265440 1250 554264190 554264197
    0x7090b01022a030606030318040b0109080a050a02030d230304081b01062324190c0c0815070c0317070f020f070528030f080406080c070201120e0a0503 66
    0x10604403403198a000941d1808110069020340c00340c4c0512300741306110102100801c0221401031103a62210400c0400e6481507030394000a020150407640c800c05141440d544500803a10241e01078050840b441c034180b409074918500034251490320020b201000340760501c01e6013000d0400ca40011080100045070070000380b04d444041895000050550f24084d0850043d00d400b610700002080740c210040240d690364005c0c501d040b1141e001c041c00c240c0b228141c0e01150300c6030f5104150350b180140301d4116190781c001490740e0100e220300700700d00740961030740a0180d94a00c0c00c3e8a42049044141c005850a4450703c04c00420510a04000c0d000c1d40030200c602c2c005c500d0803102ca100150510080510881d8104480310105811201420704142004040b503c1c2c3c031404034070108010307006907001040c1060384440d81c008580000344645c41ca2806e2900c5070300b030b0b44584503000014987c0b2021410241c59035040b50510380d816180d02c6c0704a0020a041c801038110b0148503a014010341104a000c6501071004 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 554266690 1250 554265440 554265493
    0xe0c040e06090706080c0909040f0602270a0b04030f0c0f150f08101403030d09140d080f040b06041515030c080105101b0f0c0509130507090b0102 64
    0x41c1986151040c0600c2c54062194400d40c200703d01c41043c001308084050860780c2c41b1344140d030810510303600ea0504551010ba1490000d014600c00035000e5801c10150407150030034104421307280180c000010402504da6036500840000b044200302c10000100251003c00310f071351203080e0b104c20b030960714401464140140e5010400300c4c58420306070810103a00c280030302c10082c620300f03121300e50b1300742070206102000f003602940102141401c0b205005640400a40340710b003030711400501c5041041d20f403420603000c3e0100011075034400d0942094650f4055030b24544942c101c1c0c162150030b0f94454a4103030004c030010707203061f801650300c3c03480301c41c1d044d2440390103c041d24292803ea4107410046900400b240c2c202150401048000380043c000c590310085182c02c46111464294805402c45072280d03030080100354000e28000d0000324280800c400c840e1800d0440f00c045841c1019603540361039002825903e140028100c0d008080c06002544041e80480c0c0880c0e41171040760940d145517010030410741019600e = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 554267940 1250 554266690 554266693
    0x3030a08130f0317180c09060a0308030a060501110d05030712060b070b061f0915110d02150c28090503030a0806030c0f0a14041e0e0d0e060a030e0c040e 67
    0x70842c107001d03044d43d5050704034022901803900749140080490300c0308014080306101d03000403808120144e544850140180d50804103140d941c0c148a03800500404451040c1404501ca10308000b071b0301a404140156010348940384c5a107580d45060088a0744180e4180304d10520f90303501c90224920305001c0151480610070101803181e8104641001740c480b008000486070301c0383c00c44d11610072940c400c400c90308482404544440300c101d4000c081e10038441414855240c0d101d0101d602420750390015580390b021481401ca1511074481c12000c0700c0c1886a10520702c02e048110100c00c2401d0303400500c00403829802d01c0d058a4164072480000d04650040040c0000151001e00b0b0180c0c900d000d10108541c000200c4244201e481c21001066240002d441840011020925540380b240c4542d0032044400e01000b1000c00c09894010382c0900903c801403c3c901b031881901c0c900c0901e540100a20220f202d0010809030401450402c124050049460221114042c1c6103540c17180340c8403405191a0a0b60100 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 554269190 1250 554267940 554267957
    0x705040e0a140109150b0c01090204150f060e0a050621070c0b09060f1305160b0406021005070e060706020412050109020102060c160308040f0b010303020c040b0f03030a08130f03 78
    0xba00280203010681003500b1051a003501c4c501d1014008030400c0865241588198403501016241801042e880501940240c14460f4441c41030100129050655400610ba0b112160300c1d0304044943c0c42d40d000c0210b40110244106001524142001c2c189920205c2c040e04040342d8241400b1113178202c16204e000108000c2101c00c810880c8201903107501800380c1d001081903181c03080300024501809840040001039480d01c09040c05824000c4ca100c0c440c240c501c081d01c242c1d0b0350180c10764541c09031082000600846d903030000c4802035400b03264000e980716524026110200d008000080d44101d4040303e00645c2000b0000380d02890038141542c0602039800000c2649580c0000390600000400e85031701da0504100f0701891100d10005c0720b0a40d501442c080c40f00b9540c500d000d001d030140c00d510180c21000205c0002040640c0018000704840c401e0354240400396900050006034034081d036100d41d05800502038984c07858858004103074071007404103c45e0b0090ba80c03500c502528010040050b8005094607 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 554270440 1250 554269190 554269211
    0x20d141e01060e0408030c0708130308030a0501120f02220e03430204020c060a1b14071b030f06050f0c09060d1d07060c0c0506030f010605030705040e0a 67
    0x1c0c480c2c0802000c90469554642c41e113035a482143d84402081f801a070000483d8060a01c0307802816074103003e20b81c0020041603038507400c10040e42d0f08200d5204a00604103800822600c034241d6102c04942d620816180500c01e496080102141c100b5150406051509100c1035044045004130111100048055540e80c1010011101c06010902507440c2b040b4040f541c400c00c50010440080015400e103012418001503480010003034841d491101d03006101e0700c0140071030110103501c084114951854866001d00e6101000c1d50603100c0e0082d540c2202805005070400b11f0814071301704908421030054501103a48a5032402d02c50389412000780e540c10360741c0040244a290342c0e070180d900002d4082c0e1003800c001c180000180c0511078625001c05180e00c52007200e00c50b92040e203c6c001c2a040c58401e0b5825152180c2d0020b082090b03203c8245c450030420240042c0c1070805404032030089020301d816142580c205217065455603c050800d20820004010014841100104250003032a40500100b803070403e4 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 554271690 1250 554270440 554270443
    0xc0a1403060a20090a12031101060626091212100e010311011b0602270d081e07060606030c02011a03030301050d030e03010c0f11060f04020d141e 64
    0x82030842030b030745010440d8803982c3d00720299000c0d102d22000c3c441d955582883c00b01e4203a0185c0c1c0d004241c4400c0111101d410150002e4040300c0700401350f00208049590740c0c10845900003e803490020410621210301440e1600b024401c0e8803945420485114409100c1a64441c1e4004503148001100142c02d201c0c5605c01070882a000342941940304510b0f5045848440c001d05840d91402d040c491020008240191010006602c8070f402c00421915101b1041c1d903d46e611a904400404800e4500320000c810320384034122500180d00284041c2c213100c5000304030010400b803123044a05005090120340000745050007580c019003002e642c00300e0100e1190340080d082d41c1030040b03002001075504122010a86001060301d0440e0812200408000594101950b0b5032040300d28080d01942445010501da076003000030811190480d0b511100f110784100c0740142c85032400d654228800380f401e404140580380003d03811041501404500202c040740f4580949059603584000d0100c99041d0041c0d50200c00 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 554272940 1250 554271690 554271703
    0x61302040e3904092315030f0303040f0605060a120f02100806013f06050102070f14090403030b0303030a05060108010803070b010b07060e0304030c03020a0f03050604140c0a1403 78
    0x603141c0c07112004070b5910455010034000e6001e072401c140d035620046404000c00b000043d040b1102c00340c1803c0e440c00d0141040014542c0349136860301900c100d4002241890000088074031503900901042140c8540c0e81e96000500005881554801d51480340850415882c0a18080040c410451001ca441151051022400407450b110303050102c7d000c104030380b5036089504400c500740c111121108200000030034040101010500c0a441d030820b210342c403400c040c16840202a10026000c9038191a82c400401301c1c04131440c00380c1900103000c0f0171508040d007030104a05800c41c4c46030401046d1160700101180c59a0400c88043e60074030b40f1482881000c1d6081084c2e640980740c0b0b074003d1481e04c041622488415070040c8112140400c0008580d03003480f40c15480700341100590f400340c0303640726540e08001e54030220b6404241d201c0c0344495070000d554140007912800b10380d88617015200c01d03030300e5131500340304031001c068003524901400552035850b40c0c0f02c0c208403015048201d241d140b610044000c0c54034284 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 554274190 1250 554272940 554273011
    0x40e04120903030e0f190e15040203041505130b130201080a0506011d03030706060f180b010906050d0b0301020f0d051f0513200301080114040b061302040e 68
    0x1c0c41a02440400d81c40140d011008405440ba001c0c402510408aa00c0a0a4484500d40541c5290001c252402c2d8402014000c0c47d500240100c0d450395002007000303d100964004082004203030b10740055158070782009901844249030145882d0454a5001e0780f20001c94a0319940031590702d00c0801c640e04045220342110f4405003c104905d410b00c000381c41040e035807140c0d42d900380810240301a5a41c040049561a0307500600034860315a50b241d100710102618041c050b01c0900b00b55285200343c0c42440741c81d04131441603458503195071404000780c2c0d90380e1007046080c4905840700f100d1406901c00b40000c0040c0910000e5065841510384040400c4400240800c1c0c1c59840203001310150750031040b210003d8a0085032004e01141c0d420030000c0c0201050350801c000b880701c1c4a80b0140d03c00c05400a1812519000028849071000205034011010220b5000701929000800b180d01340c104181c9904400c901c2c66001840e041c0c0f18110030701e82a03000c4407513070030740b20041c0901b040910411002c01c5016 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 554275440 1250 554274190 554274197
    0x615090605030f070f050616021206090f030a09090b030c0a080d0e01090305030301061407150c1704051b150304050c2d0105090f0915150a0c0f050a08040e0412 70
    0x100d04054140300391740b0302442a01d01c0b4100c0031030802000c1507002c3c81e2413440d47c2c3c020b1402c15123909907100541c0351802114030354510f02944144407000c400100c11255040b14503603c61843da800c00c00003030002c021048413560188100700d155005919510010000384c14030600418156a4520000b81852200d038074460401c800707810208001080041500d05403103580c01d00c49a8102900820f0859025610b0040c20341940c03000300c18078840c866409403001c040c0399510900c680315440000c0100010036140100640c0c491064040c209103988180700d0407030f1004207604850416929542060340040e501034905810010511001c0c0c0307003040c8003004030189044507801d084488442e414000041d009c0c400d0602000142024060382e4400d18203e10b018001d00348040d50901c0d031401e0103031441208400b8080c1030b003c401c10200c55540c00598002100c55a03414a10000e070755501000b001c2700803012240ea11071203078030a0000c2c4001c00a4006440b5204240c1c040c1e180030304141000b507952040343c0062 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 554276690 1250 554275440 554275453
    0x181d0307020609040b0f1504060801090b060d09020a0510031d01090510050402040b06030705030712020309070303050c240901060f030209040803060f12010207260a0c0615090605030f 80
    0x5844100c03d4882c0208110342c001111401d2501203108070a650070210b03482081c402c081c00c103061034000a401640c05564414406a0702d0f902c200c07003151f5041388000e60090301800704030750802e19a04220f110510203481200c0b0302e917440c3e021036101000d5000180101e61942c0c1118100c00090703100044500300700c0300034441409681c607200d031108020350740d007410f89880e080014250340303031138004281407440a00025500e11f840540200607801c29680600024501603050b0500c0391540241c074085d01c03461001e00a480d01c1c50340d041d00d081d407000202828500421220070440107840e14145141040d990760000f0720700c0d16400103400c444041e08030320400040700c001440942c5440d90301c1c0394002d90040c035403a40c0e40c0f140c200040f10002c1c0c407180c0961008130802011018001900035010052082c415282d4940c04a45e2500e019038110f44203410f040803c0c0207100481e44030740100c4105a01807280046d8248400142c1c2441a07110b400c1006c51a850302c00c10030444c1400c100060b058000400507005 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 554277940 1250 554276690 554276693
    0x10813031e02010902060a120c0306080304090b0d0c030b0103140303090309040e01020c060103150b0607050606091008011b08090d020c22021605070b072406181d0307 73
    0x30401d820395007000800610103400403860300135031100c43c0302e54000b010349454008030540140107003680202c000900c0c1c141040303502210300a000b160180c4002c00051414982423000c0c0070700806800380c580313500c852680b8120021039080110140558010303040c3d40455030440c1070004411500c00c0b03030001c031703a4001c1041004d40000070042c0c4da01c0c0c202c1164042414040c4000e101c1c00381c0a0031400c0b5803203000340b500001c10850319146d1116803902c07680d0180302206035401003102c54055981d018240360400d2000545501c0e001840b01e510461440e52804403d0f182c1c0c5046003151264145041c03042c070010f042c0e00c1810b8004a90a83c4601d20000500d80c220828078020345a000d03101c000c3e400303403540b40181d0302c2640d6051402850188003120071502c5080b02c040d0b20081c0281948203842c0d038007a40340301080e1981d14204940a1a4111111203480c1d1000c4003500540c010054004000030758800380850004450f0100034803084500e6008110740c100380140355841c3d45003145118542d40104400f50 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 554279190 1250 554277940 554277947
    0x105150406031e020a0201050910020406090306150f031a0f0105011b05120f091306060903320105040201080f10050405100f0305031312030c08030a1d0c01081303 71
    0x5096444a2502050b2100c1c140150461003081c4590f030a200790000c1140101d0711350551003e885081020111200c0c05500482d21080744558000c03c1c1c00910030f41800e001007071140e000300070794034604400305d1561659411000030304c6404c0d42084070100e038044410719003500c08805041e000942840b81c03000300c0d49001c0010344440525803610042298840c1000705001d4184803400d800d443d55050341e940d403003002c88a402940d200c40829480b40c0a20078125032520303403074440c510544082d612a100002d0458071801c01c280ba09214041c510210000c148581c0c0015465101c4c4040d02c0900102d240e0a2620024041d0400204081c050304103400401c15010407880c40e00701101d4003500d00080b161101003148044000b943c00100e104c04074441e00204014000000b00504000fa103410a0b003551030301c070b03031424030005a034002d00000c034000c00c0c1c1801700d80407400442e0880c103070840001d450b08110314150941c200007000f050154014600720710302540c002c4c81860344042c001001844a007640c3d540507 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 554280440 1250 554279190 554279197
    0x105090d02090a1410030326070c1707032c1c0f020306130308090c090c0c03070b101701090512090a181b1d011b02091509010515 57
    0x19100d01c0c285804200d0030841a40084034140040c803064155103015280c61050f41c42d10710044002451000c6079050303003842588c1c4195a50990b840452154451220485a030a45110150307841c03242c0b00c184a048855000042480700d11031b880d0000c0c220704400711000c103008004081280c070704042040350300950714448210b544250940d001c4440350080d00340158940c02c0100d00940510622041c0032850700e4400140c4943e0340702e543c41e0181607560030012911030801d5040c054200509030042020b8140140c0a0400c0307401510841e41010b000e0340b1641f034601400d651010345408181c2c6c00f84002080b541e5100e1400e0007050082c49801000c2c4e643d20750b6140d000d0281245400301041d00301d2555030b00c802c0c0078020142c20508540b1143c0164050b40188610500c40c41000f05840c41440d40341d004211004440303003e940da17003c0341c007600c800550b5140c806034089041101c0e000562030042c0c0d40e5a03e00303801901a500c01d079907803c5039802072000044042e00114850309990780001d8241881d40200d = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 554281690 1250 554280440 554280443
    0x2030607080c04080a14060c04030f020d170a08061f020601050f0604050d060221040201020c0411040803071104060515030a020706020706090f021906090611030c070b07110105090d 79
    0x5440c1d10340e1110301071007290003282c0001606024a0216405109144400680300c950b44415940e890b00e07210b06003030140c031691000401b24000e803522000903152614801000f41d0141c5215032507103a000301c0694031a808102c00c5004200b4401c18841682003454020301c5071008a880d801c0240d08000000e582c94805108540c840c0401401d05510743c1c5403d000e07500100030141c41d14070303040348511700b010182d00400c4000c0e44800c1c807000610000008246881d00564040c0c001d07112401c000d80920001e031110b0030322124034400030880020407810800042840350b010f007000c0005060344000300401d40345641e1205100740230b0840400c1e00d15861100700c035082041c1180c01643c0f0308052a007800607005000000c0e03d502c0c5050903100602240c19030040c1402d10860b03c10040070701c40b0a6001c1613090b5401020000303000c0c4d0720b080c07016074003c80d0000310920002003201d080c00c0f030803000d5501c0c224464020154981020640008102407419007411115090030100e0404072018003013032900c81070180 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 554282940 1250 554281690 554281697
    0x1504030c1b0812251218060c020f04060302120a03030f0509030a050a09080a1104140114060c0111030c0a02070603200a03180501060f08010b100c05071203030506040c030902030607 79
    0x80405a039007161a04200380c90b65004c074001c2c00c0419080504041c10461070140210340c2039510380e006283d00e0f0700301e070341a102c140c0c60300400342485800b8040740c1c803d4032665540155440f070010002d6501c03400a0307030044100304020210000036180007000e6800d00c035048004542031a040c0b00300010040156000001145810390300c8140c821002c50303810000303500541c80c071301583c80d02006021400001400aa50a6809100a0804100d00901002c092107500c6028403640c500107881e2038175000504102070103100124940747c01211800d80c41d40140ca42e08404100000e4601a69405106c140700901540c10b0410120009140c40f030a4015100c12401002000061881459010f80d00040729240c52031441d00001a0500c3d142c1d008000d24020451a210700c2100020402c2c414080d1046000d00501910710709400007900392103440201908465a0280210101d000e441c00d002c400150b40c02035401084904085040c4000c98080c0202801011309010a03080507841c00030303120360441030618 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 554284190 1250 554282940 554282947
    0x103051c172806180b030c01020c040509010204080f0a03021608190c210302071a18010e1003050a20180301150b04030204050109060f15021504030c1b0812 68
    0x10b5115038540b00c41c110101e42d4901a80071130541290030003040c1c000c10101c0308010422010003050780d01c170b20028a050040e8454034460080342001e401894004900d01c0001d401c00e0f843d240843d0600304070b810041c4495121101c184c3c140f503410490116032803414101e00a041d42030043c295103070070f0304540540d0480401c0c3c09540c1080126030340b42c030080020405110007041042110324090510020903401846a0701022501610300124403074030328050b5402d2860300d0315003040800b4600307080c01c03c5810310501107015449912502a0040d00d0300700b980d4005810301e0a81c0941c802c81c1d00000030103c010f0400110307106442c44240c1291f040038004001c1100d01c601c0840020b000d852415801802c5c200e0401c40000d00c4c501500c041d10a4a100716400e10290703807940402000c4944a10802000c12440001040403900240d66078006030a41d00c1618110030072803981c2c0c101c01409950480000705910540414441e00090103da00480480341e41e40c2c4a240040c659910704049800401c03508000 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 554285440 1250 554284190 554284231
    0x160804030e130501031b06030507020309040f0b0415170304050f060313170a09121703040c033003090809040e0708070305030a0f0507021005030c0c01050103051c17 72
    0x2445584251142c1482440290307100d28046150540b8008813107003940e05c1780b6000c07400600a0103014400e91080d4000d41c2007403400c404100150000c00b000c5101c41c0d42d1580d00c601c150b10389004e400b10181019030001d11709460041080360310302083d114407015030002e1005014a581e0b10b840d00709915000c854168494139002100e46000d2940c4100401482d00450704a094400c07800c0a0700d088010754559015055642450715001c080100c0c0c01008000c1249000180c001c1070f03070185401a0080c8141c1141985070740d0b07005010041302da01c5c80010024015203c2c80b5052034407000036410400e10341800038a0843d9070348000d40c0210022944541d895903d1518459810001640200703108801c48500c0c07070341e07801c00c1030701d030742c8603103001d00000724040d02a580c0c443c001d004444040d039001e0000f0360800d60012045805810217000c41c11404400c0180804030142401690301a500920283c180f06990026544130030031000c06a50912186045c801c001c0031000d07000b641c1c4546100c11071003200003072 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 554286690 1250 554285440 554285449
    0x2100b130603030806030c220c0212030702030d0501230f062503030c0206090a0605060d020d030f03150806010b0304080f030703050402090a1b0f05160303050f160804030e 75
    0x3692401114a40340a40002c10f06034800c1c0b500780620026070546004e03d50202c10700103017000d5684186060300c9480303049141c8861a5102d220300c46101e10541d41e031002c0b001040d007010341c0240c854100607840030807168440c0c2c40340c1c460a40104926040707480181c1140319569240c102003608240b26034040c0c50050001d0300c1c0c0e0011159410303028845c107032482401c00031102c0400c05162003034002a1900c001419600c0c0006030540c040c144000017007140d0354859544401510b0700410254016852260034001601d4035040211160303c03a4448504c4540c4c1502c0c024220b6230310080505e001c01700f402040260120100d90581550a00c0c01410b6480c1d0b1182000f402c0b611030080d04e021800000020403d20580c1503000c1c0c0d0086100301d0360712103c1e84800c441c0c0000d980f0132507003484074030f0400ba01c5680007038061a5010103400709400c20508100465041d0a0600c034007610a40200740c43d0010003600d031303250b81304d260742c810810004500011482c0c00014034804008100805010f03509107480d840707a44 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 554287940 1250 554286690 554286709
    0x31209081e031606050a0b0a030203060c0705010605090c2205060d0509030708071208010618050906030a0b0a061703211008060a140708150d02010507210212030702100b 74
    0x1c020004518108551421600a110031140c2c00e084071f150041d2080b00b481c01c2810f407070440350020001c0c1800c1e00c40d46a44801c5a01c550400c41b0a90350303c4a0009164860046041c881e200203441079440c1d5100c83d4090142001c110300c0a001c40104c8402400a60b40e01d00c00d507607050320000c4c00000d1550310224000e01d9807207003500107001c800c0041a9502040341e1031b960b03080c0300840f5568043c00da036600e9001b40d0b54600c2c441c0c84500440d0002000740301c0303414076180140d070044c1d00504403604002d054455007403008054030102c4c2103075110b540900411441c5606185200380a4009500d080210107604190504100764820003064440204000c41c0f070040d0054003621201d030549050303040c0b40d84040020000040c80c08010745607a000104070a0103605800d00c6403010144602069800208015020701480c4040341485820701841000c501403888508007002c900c1402132000680c03400107450002c1d21b1502020008040081003605030f80400c000072010000c0c0c0c0e000c5107582c02000010310102 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 554289190 1250 554287940 554287957
    0x111807032003040804080d0f080f07050912010204090b0604030c3b1b0304210c050304153221040302100e010908091e0a030507031209081e03 62
    0x22081c4000d00c0080c00080c011106401b04490159240d4181520344400a000c0c1d800410300c8500007601d02c1c01c281141e030340e0006c201c1c50201d180c021040d0000f1103004800d10300c04a90b03907011034203120040c0c203031282400d100340031100d190915140d540d8009015165015003030308440b060201c1601560b240c20b58004020008681440c541d001110800311010210f03010000c08a680e031080c403198068504036400340360820f0703c8002d4088045040c0798882841d8101004110349040c481c0003185091001e00050716046044c214a1000484028480c0c507226100400800d0004128441b904207001440035002c650900c2503203820031280b40d4980b01d610b1075010700303e1714800c104010806502099990040c90244e9003005005045e0b807245080b1400c8070340003081c28004000e061007602c0e1038100881c501000d1b8845482060311030003c20410005030784111015488101c0a008004805046040306101494452541c501c1d10070344540e140e90a1078a03183d5a9202c880e040d0284009108441d03020 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 554290440 1250 554289190 554289251
    0x2091c02100e06090d0618080c060709030503120c041a0c01050115020709110d0e0d090b040f06080a06090c05030106020c0d170307090305010e07170a0314300411180703 74
    0x1a03c03242008d68070390f400344d080c0080c140259000501e42030301500a541c140c94004000b03608003407007241404004039002d003901003544000d00c40001c09035607680828601c54403042204d5121601e4a034070b2801d441041e00440d100242100c01004002c2e40080d040007125240e1001058a804c0700300c9442030b51040f010011611403c10903500e4144000040030856a03070786590306001c266a40308041828040c50003401c00c13541410004002c520300c10091550001040310002409903550f0400c0c0b400c039043c0000b81c40203e00c000c40108040b54041c08841072841003600c510b582d409140d522110410842c4ca03540c02c5101c0c0c0400894120742c4641c510700d02440d40b0000070020046841007036a81c0d5001c91055002d4500e0b400e1864540440119840005580c96100d40500003003621508085400c280e03580907002a24014042c88017001034201d80088007440c81e411018101403c04d80220007402c0c0010340a00c0d10b0401030145205451800c40e80700e1041d207000910b0307507181d4014500c04e00e01c0400380741d6517 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 554291690 1250 554290440 554290481
    0xf080f0304030206100503121818010302090709080a0320070e0907050a140103180b070c1a04240204080604151413060f02091c02100e06090d06 63
    0x60514001540258041d808586103552498510000300700c45008144d0960000880190742184030000361144181c001509600c00c040d1102103112180c503007203102401e2042200402c190304004503115080b00103450324460b207e09020b08543c3d66a50080c0c000c04010201d4018589900d10079410780a0a03204007d96040315518011010550b07826240c134580c03030058940c006268603240e01d1100464804080764809540100c005400404019881181120100c82840f000402003400c9510846260f200c03102812684e043c0000c0070322903402403207003112650701800007150382240388400041e00d8000100d00f4dc000c0c800184080c0c09aa880800381344207035000e100801c4107200b1140c88154400400300900036600e405007070144000d441c40c1802001729928140803540b650002031060001e01c20141c0342004210118070114046072040e102c400701051000b0840c81d1a401d0021003400c14a004c4031403a81180000d4918451401c00d644a004503605400401119400050400a120b04071101c03 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 554292940 1250 554291690 554291707
    0x10050f0622060e030102090109050f0d0f03020d02211602040b030a060209100c0f0809030115150f0212040e06030a08040308030f090106030b06090403030b0a060315090b090c070f08 79
    0x1c03410300e103000754000314042040c00070141c10144240c9000f010f050391380000300d61400e400d102501740030180e01c54010450070a550049003405c1007240308c0c54820303402440c0c041501c81000f4140034880c2040c8851142c2c506500705682841400c1da136081202e000385400c3c034030b001d20010b00188022510b0316010300620701910140806e0364058042c41c182030320784181c6019584030440303020441c41d4000341444650400304002c1024000940b070700b0640a0000501e51304002405e5448070210f070303c184aa0000c07040304440441e4003100700c0310f0105407030008181800120320035a500340142c0c06080d0158041100003a441c1c0e07020040103010369000360050381c0d115283e04100031144d00495800b6120341010b40860040101445031508580d04000701041c07589425003005900f21024005400b0540c640140c0412079448825900c02003c0e40c1e01e00080940c00200c0000043d401035000c00c1109180a245001548945c02416800121040556502c04d1646000740c1c21f81c52580d0301901c42d0801255040 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 554294190 1250 554292940 554292997
    0x30a09120908071703030f04110a14100828060902040b0912062a19050c07090605060405010e010908031c050a020c0d030c09030f080d0e030310050f06 66
    0x20688110301c0540e02280e0700c03070014160292a11343ca051040d44100005512200e201ca491030300944113986c0d0206044032980045d4404429070849400403075400b041d000649807900f800d014a403100e040403202c91400c01c080200805450102c042011048010742c0e0f2611050b42c0180c02524400c035085480300c1e1203412840780c0342c010410b030318020303000405042407034200002e480788100181601c130309521500060703910380717540050304840c00d0202c01d0000c00d49240100d5801080c010b83d65030b5103511000039400701403903d0400e50141d2480780c039184041c080c54403440c0854090301c07001e00f803c1c0080011200101c61000482d0b200c0503580c00301003904503407001c081c036507080c514201403c00e02041c0c13941c0210004910030394011481d694802c029130010036000340c2010f904404a03080c8034a40a40c2c079140c5030320fca0645981280c1c03030b24000441500003099403243c43c41c1c03112903900850640c9400130000a81911900a191040c0407003c4d03819907d96501e01240c1c0004d030705032600d46441070421001c4 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 554295440 1250 554294190 554294207
    0x2d0c0c0f0f0f1a0a0e0904030c020319051c022a040c0813030c0c050312131202060d09050c061b010e120403020618040216290408030a0912 61
    0x7a40190900005070390b402c500c482000352015482d0301002440c00244206250b4800e910140600000040b0035000b0b5035070592542c42940251229030030ba030342e00d10405083c42c0d010030390761001d41142500d1001007807000801c80380c42d501056099100c00c5994100760316140851803400e01031640d06c1a0411010350051070b40880d09003e6405104459250600743d0313071044215825001513070700380c0306040424070070844c04000502450281e04c035035441e040401c0c00d220203101055070400c0b000410008078400c0c0701400001b403040b0030034080300c0030969000030010300c130711511100d02c7c0da213580e4844248801070285210b8000c00a1100d036803140310301408601e01d9600c0c04c004141c0d500e0305281c035070400e80c041034080750017140a040310710b000d0071503007008555048030b89401d03134a00c1542c04256860303d0301d20041401d4240b008140c0b030107111500c2c050049814210381c3c80702e0038680c9841502115031300015581c2040e8404645a02c4c0d03900c841104005085020380500280755004c220410190020707542c = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 554296690 1250 554295440 554295449
    0x8041b17150103110112090c090b1314010303081906240207141e030313051c0b0a020a030b0306101d01030206220902282d0c0c0f 57
    0x584008a008000c6034080c1842403002074088592400380c01c05540c8100c011030003840001c1000144687c2a0701c51078144c19090300304080041d44c0d200800e405140290900d00b00703660050062042c0310041d00c13000c1c0c00d110103100090a100c00f803808074517500300c1529400e1800480c214104000c45d92681042c1c540c451003c10030107096820f10104428038408165102580c2450103540e220349111014003440c589041e2070b445100100364007007046039400740000c0800140e25810740c1d507064240350400051416848540070101b0010942000182418441c160722282e40c01700141c0b2000c0070030f801c3d0007a049001043e5410f02442d410400e07000b0000c07080d0015981c02d0b14120300411034440642c0da02d00f1080c040070703500020078005442e1110014180e580e4071502d030084500c0c1c103030f6681c01840c1070740c00115010380302c070b400b40c2105209203d0702044240c1005036403602440c0d080d00e4400a4002507a000c10340e11002802880c2d03030036484d000d4500381c01d8031075122903011240e9a80c0d41d01d10200c06043d024 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 554297940 1250 554296690 554296693
    0x7080c16060e0103021204170c060f0106030c05120a32040c12050717070812270d1101030e10020702030f0a0209070813021507030f1d0108041b17 64
    0x2c09940394803d2003512039205410120001c0b9403100d0710385c40c0700c65242c0c299031a001c4c10308000d2001c00c54001d000c014080ca80340c2022007415410f22801909881041c000841045418040c00011030702d0420240c0c0c100f45a20b40015400c45d8201d14525141885908140304800141e00071500c14a45201c0d20300c41c601441603400d80686a07000c1d1100c880c80020050084c1e404001c040c0104145800800c903d440076004841e401692040300600384440070410706840e03000801c5c80075411140544482c50391140d000d030302c0c00006003500040c0b1141c400d0907001d0141300042c03403040c800341d0003a0b000700070410011080b41d03803600580410501940c042a012030180c01607005075200d540000464614556008040b103c641da03c00d50120b40c110001020442c0c0302c2012030802000d1303100c159100381c03c0721080b1200c940d02d0a0030308010300b02c0010b080e241010040180124032604281d500c1e000404071092900a400d40c80d03a040a1403114401a243d1124102e02800020802491081004032210200 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 554299190 1250 554297940 554297957
    0x2071a070c0f0621090614070f0f080c0d0603082a030406020307080a0c080403080324011b0204141609060305040c06030e150f0106020c060705070b07080c1606 70
    0x1070340c0d02e400654450701000c924500e0801d0740a4882c900a0072a45003500382c0080c40a10548802003a600030010000041526105121296034080740c4210703500181d0038500d400001501c0d00900701c140041260b45010008181e0181d00c5029800c4807008640000005403520503282e030703c0701c881d100103803c050280c4054007445800e034000f1054030202c81d02c070b802441c02c101a989400e4600d41c0580507400401441c081c09100003441c50700030b00301542c096840e65031240760101c80c031640300310701100802c013241b51400071903503507a0302c018241200300c03003040390000e503a01910100c1c0240140b40310603203c9248074020040002d01c294940b40c0c0c40d8150307550759007001e41e5416042e0105d540665016000024170201401000d010fa00001804a00d5404880d03010340300e01c26590302c01c4030035150811108400e10042025540c10007014403040812a0703518900021b40d07440030b5440c0740da88140c003451440881d1800c14420100d040d6904d081070b11040d00d19440143d05d14403c00000d6000d404007082020 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 554300440 1250 554299190 554299199
    0xf0c050f070f1e03030507080c1009020108060f09011820090906010c08092b05060f0114220b030f03120a0e030909040809060a0e0306090a0305030106050a02071a070c 73
    0x490380401800e550503c11042e0305545089845504c08142a00c02440c10020752510b45402c0140344000c80041d6400180a42c0b07a01c0010141400070b460030307100e002400c2442245076184140302d41144d4072007100d01400750764280400045c10100e203003074140b0405c100180d03201c41004401804a004101c0d0315020035560180191050100000042c1009209010b05820340c245000c0c403c0e00c2001c414600c010409003c400c804105079452012107040e000242841900c0d001e601c1094090226044060000d805940110340301000e0fa181400703e41d5442c04c440402da101d2a0700c090f15051010f001e50728a42d107500180340e82d07544040c02c24401c0800810014210a02610441650714080009545001d03c2c40d0100b028003440544262101c140c03c106404056550034020311041c00e05d904d4992824408604150400780700174919011a00244078003800070b507200080303905441c140e00345140c440d0810a070881ca4000e0720b0b001700700d0303040707404004084840f4060b001d0901c1c5441400d0014003542c44 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 554301690 1250 554300440 554300459
    0x2011e0e10021203070e0d06060b1b0f0d2a120206070f0507020d0c0f0f090f05090312040c0b271002070b0912060f0708090304050a03030f0c050f070f 66
    0x601c032400c2e80c103440620105800700c1c403d0051b0740f070b9136070020b040d0740072544140c0b5440d0840e020b84d400785404020019008a4141c10150780820070000030b405040041c4407290013035202e5030113056250030080031034501041d00502a03241070079050388205a08114007503240020040d80701e01321031070252003040c0005141d14415095040020b00b1540c1e0300e41070036610b078203000410b00c0074403040f00c680d18540400f25143d0381420301a0001c00480b01c99041041c0351141e12811a42d27860407048081d400c02e420030000c80d5001084440f0740c031030740c0aa09082c0d0365500f0a84040e16064015000c900d80000e44940980c503885500843d041c0b10081480c240b0041c0400c100100a06d0600b000c0540c001200130401054024094507500a010b4400340170840340c4010942001c0080740c01c442c1125042c000d004000da4045002139118480c00c000b5880c10303007028000382c000580c1d8840201002035003003848862134401e801301684190b2200859801303031030108645849502da802030395050820860001003400781c = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 554302940 1250 554301690 554301703
    0xb12060601350a021b0303040c0308030723040501110607210b210d0503130602030408161a0601050f0d0906090c0f0f0b03060f01030902011e0e1002 65
    0xc16100d01d12040c41482d40b0848049421405102070000d00003000b00680021110510804600304016a2501c21107031204d5a28040064845150300510401000900741075168085d680c010580f90f440c1d03543c03400c00312000350800035406c07a0b50713540344900040c0c4030300c0c00050020b64000341c0b101c5003480c802040540d07455800b10f51f02c00005800707400e081c41d140e8040003000c824039040d01c0c006c03c3d0301500a0105842006201c0055003c03aa800d41c0f00c84030304820301c8088059980b1345000c625509120f544400410100c10025208a40c004041401c1008540c200d60788815002013520070788900d8123060b810108081e0040c06156002c60004007035602ca00200d800b40c035071501030b803030900b0b04451401c00180748400040b01d410740d59071040e4011a0100d49401e000b031460140704001c8508200b010424003e00380d009908010051050240f00d80c2e42c1c000c509000c100c00c0c0380000b0314905500042741d1441c006054070b440001641e9281000f0f550240c01d485806c9001d03542024890070b900b4049030b0300c00 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 554304190 1250 554302940 554302951
    0x21608280f030525170601050a0f030e07170105180105060d140c04020f040f050f09070e04150807030302150106080c0c030f04141906200a080a030b1206 67
    0x5440040d8000500d001e94002500009210130703809220040d140d504680007060022400812810b111007900f0441c00300d01d10f82c1c03003102880c8c020300304492124040c08009407240d1880c2490f440303402c6402903c0040040c00c0050000c141d8060080c07800e0810907008040079202c1c000314040482d0000c86100050103424050b41c030150001d2030084582d00c43e8a141110880c0c1025540100811101e2035601c600140c000d20000040255486140c41c0a0b40040f0501d68130860240c2c184540202050396000310340d0f68024103605040172030b083d250300050700a040080c6143c0e40f4858004000c80e4150000032680c058920a03002c41d03000e90450398420100f00000d20a032800103d03050002100004c50710050a201c90385542220704141004156003030580151300030211081444195840503d07100c01d204c2540d0000d000c1d0480c0a0f41001802030128044014034084403d010a00058be100b040100c1c07200140c02201ca5a142c10848000402134080c8400c218421940900c8110002c0c1004c2490350084 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 554305440 1250 554304190 554304197
    0x3010504150e0319030b0a06020f120313050d0e01030c050405030a1103031209010516210507120614090603061302090601030e0a03020601030b010b09090c070602160828 74
    0x91005030140544004402c020550006001d004401d002084002031011100d440210300340381c100041c400041120340c480300c21944030070541d0312010800304480c415031040501c4a80d0729a41d810345100c4988103840d004002d48180c2d0414904240d00042d0008a188261b8041c0300c0b100c05200708441c2c0e070103280541c42e07040c0c01c0b98400c880007a201c100014030300d9601506581c10220b03c1001014108411601c0c110581d440b801000411007121005808400c45400c000500351100000441d100f280c461440e00c02903940c401052200b030062040351b54944640100b070000503183c59040c01000d203d07465070750003000075101003480c900e40402c00601c106a011007201301524a502040a40d00020b0003241c1416595070300c01d03903004c2d82408102101ca019800515165255142c0140c03d810141d2208440c4a4244400e00048d610708981320f8101c13960150854a4020303071304100b0001d02c242429040c12140034501c003010020f040c0040d0408040c00005040740d5000b00e10706081c405072100104001 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 554306690 1250 554305440 554305463
    0x10f050606040b0906091507060f06060311030f15060703180b0403020d15060e07050304050c04061406030405010e0304180c0815091e1e010f050d120e1c060b03010504 73
    0x11308101e0044c1660300001007181c1f076158210060060a948181800d03902c036504c0b44204542c55460b402040005c0000c0d01e81007040a02e10305d04240e441c0009015804480c00c41004100c01c0720190494007000c540042c845a0f070703484545030142100758080c00c001c85c0043c1e4071400213003140d40728050710112034011b4100701151005030b44180c160078500d481e22008565400d00459029002002c03944100c0305512503541d24105401c0591a0007501040300c0c5c8120309156051000b1903020801d401500d10540d1440d03240d4950b4640603024048040d01000107201c0418009030340804203282c4001d88940b800100f18040000b42c3c1121034403000c0301c55895122900c0400c0000b07085c100c2606900c076083d084c003c015490403009418541c08181c0b02c0704601c0b9000d10130402c82c0c00071406001d004244400e1003080840c03a1002091036030b2070703100014100181490410000324010303105406c08800c01801500211014480307110110f0841d2029900c461802504002e00d0505100343e50190780c025040211703 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 554307940 1250 554306690 554306707
    0x31309050f060a0b0a271404150504020705030903030d150e0403300e010b010e1e010c0c030c0b03011a09031209010c05070f0305060609040b0f040f080309010f050606040b 75
    0x140c1d40c451201c0d0381c06c202d503940c007003010080443c41c5000340e4072243c041c40c20150b181640e410703400360300891001e10880c41c1c280440c07c00c0920741101e1341103a206840150300c03007829080290950184030382d45a098000010480b03141140b80c0e2050401d040e0030b4a0804406d0b40395000b1401c4064100c038010042212040440741e03100c04090000015034051040c402c4245a00e9018416600a84100d280d030f603454402c219995a0021290800c40000f502c5d184991034080040c1090030003c007040354144800341c1612011b100c1041c0c801d00146402401c3c0294590b0303134400b440e465a01c00d21508425602013031100d0b03065100703030044540c031030300040081a1054043d60022026400320702080d0501103c00124400504103101c0c0c18002e100c4401c4904860789142803450800300000c2516116041640812000601c90203046402000304500c4034100d6556141484800d40c9807000600145004420880200c405410500c103e400c41710040c005501d5038030501240d80950302980540c1e9030700b8400000c = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 554309190 1250 554307940 554307959
    0x7030b01082a0a0506122d0a05100e090a050c0402120613020c10021b03040608010b0c19051e190209090309100906021b0d0f0203010e031309050f060a 66
    0x2c00c48100100040302440c1d503403001540b40e40c000605041c0032949001004100c0021620065107111480d10303210254034800c45d040796100c001070411403007035903400c04071765912a500c00c408040c1039202407500060900343c41095980101d0303d0300710b505104200249030740c0d050034020b681070404101c019078070a841d0802000040d0044c41e8049a040358240214007441e00100042020b006441400680e20501403040b01086200181603103000d502c108002c111150b44950744504403958010303900e80702e0344044030050614000030b00d91045441c918400c1400d1200c00f0070001c850194508207031114550322140113499080d401882030002d4803010b6000c002d82004e48600303501000400c1523030700d48003104000515070702c01c60014900090380243e00b070003500e404106114094803c2125003580c0c069038000108c045940c8100101243c017007422000854509400c031b8504251040306a030303140e04001084400b20201072244510603402c00001c550302054401c24240070310b90107010084e4850900d00180c = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 554310440 1250 554309190 554309263
    0x180b0a050103090f0203010510031713180f020301030c05010305092805010e010c020d090902040f090f0f050408091c3906090e010e070f031104120507030b0108 70
    0x1900c2c00c895a861134001a40c0030b11074107109030031080c60044400d0460902152005010050300d82c030000400020714442001c40d40d003070072240d049004601884088990001400400407500740090011002008101d00e200100302510001e07030b400c000c203075a0160764a903600481c84040040812034032034415549400611310710054012800403501a8a1030401800c560382c070900e40c0010707009030001900c0399074480d80c0c0300e0050114503015810306003401d43c14814081c03244151070517540d070380e0140205280c05401407800030030a46010452031409040102c599403180031003501c03400c6664035040010703000b661090081c1d50070001c0b4280da103415901003a1038811407880006503600408800005034281424207003e003810755954107400b840c0a454090080040e0040307042c0805103401c100047e6404040f60601100034500410003040c800028071a03131160b5089050450b10304440d11080c454006200301c00ca0388130b4411444261b13605d1071a2600c4619400100006440c880d10029281040b106070 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 554311690 1250 554310440 554310443
    0x30b0a0f1a0906150409050403082a0304020d060f1a0303180d051f020705010b010906020c090705190903120203070213090204060506030403030e011a0612180d0801180b0a05010309 79
    0x1101c0c00d104c4003a501080c01d030000e5200480c1c4540b59800c03c01019400340c091904900a000700c04118101000b040300e40f9150300c200c0c4120241c02000040955035075111108a4940001040014001b03403841c51014108c0100400011106900c06014600300001200c450000002041e0607420802003048200c2014150644e89446004980b40c480000c4190302e101c00310f240c110040c2c0e04d6100b0310b051829030300580301c0c0a042c400d003901c0070404c0c41d8001c25010b11549044502c60450782e2404d40a592501910443e203407500107103600c440c40181c020824400b0350380036a80c1e29280d18208001280d59200d5044004e4009109108a03114114241c01084403184020004508161601d0101300b06800448003a00065210340c0401d620040a1240e4400190b20a84100c01450742e04003107a41032142c15100f805002d685400200140c20306d00031130410b040c0a00a43d0500c203098840186255428011901081c001b0380400c00d86000902c10b4201c90701020300140300c02d41c5001c006500802c0044070 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 554312940 1250 554311690 554311699
    0xd030f0e060f070e0a050a0501030c0327031107151b021e090a140712090f060903170907031e0209010e101d06150403050304030b0a0f1a0906 62
    0x104484004001d224440c8280c1c0404003001d050f1030007840041038100c500c00454080d0b10b081c0000d00860b00c48500e6a800d454080c2404a0b10407091542113004122a0740c140200032814020710310a4a20407640074401400303039849020f010340d07007241e441d11810f181c030560711070700001c1704100c5000e805006016109409002c007002d0805254010980d4010109003260b441d01c4508103410f040e1a10100c01500103106290070003230315011512114800f0301c0030b000101030007100318000c104c2080381d8004841c180da0007400b07408000964036020007d04482e010450100381d01d034100c00c1d41c1082c901c9441d4496801680105800d524584804052210105140c02039015516841001d611448039460003804841449541d61170261202e000644c8240c100c1c0040701c058080d40304555002c2c0300d0564011408a486105a0105503041d000c1d506c5650301c000c0090002080010a02240c00c14262140d48540000d1250f6055604200c04507040741340b10300c0046401454480c0c40d404c0c0400400c1d8842c90140 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 554314190 1250 554312940 554312951
    0x1b090c07020d140616090e1807080303010602031b0a1a091e280507030b1e150a060c21021e010207020a0b31090614100e0307060305041505090606031501080d030f 71
    0x100281194826083b035805a1300010703058042200b01000c0e0200c549045010700000d070020f542d0900c0340e4004a0310382c0c00c908005001314420300030a12808516144407050703851081d02d03403045140c03551070740c1446507008a46190042942c0c000d405941c1e840c02d07400000303040142e04550f1040d62107080074044103082110607102000d144071103031000d40070b155144814012002800100011000e00342c01250401120310b040c0000500b203555110207c1c5c2880d2840d8586008100c8100d14040d4603000001003554070303a40c1000140e2040d801440c01c14020f0ba103c00c803094070740c90804501c2c4951610448600b201e50700c84002d2120701d400341d00002c040d43d00d010312034a50700c01c0c4150584a494101c4841010018802880c505e02138a50207c074170310505000e440ca8040100080d1141ca152080105060702da4000408100114009102e0002c01c200d040110317040030307100d05540307440881d50301e4000d200d00601d0781d036003680c3c0100d254100c4030040c0040c1440e0078282c408801a001d007806000013540c840 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 554315440 1250 554314190 554314199
    0xf060507020114040b091e03070201110309030105010e0906060102061905150603091e0a0809060307090902040e270606010c0309051002010e1b090c07020d140616090e1807 75
    0x400d0480c4c011800790000c0c01642c00c00e18041d6040402c18110064500800b0404003c0100080b0a41e01850b40900b0101001040144044e01354411010305690651800c00081002150215142c0c041c5034600100c4200d030b503620f001644c4c2c640317003900d040080c1c217201050442c3d182b19540006138000300c0b1140c3c00c1d20700d810341d1001c504aa0000d581b030ba809034200400c01c07000000040c0700c00c1030401703140000340480000b43c2c540501e0f07446a490410b004240010001d001d0900500d40d8500070031142c00215911035850110740c0e1488402d85201c03584003c240100ea004040581100c0354151680b400b074800b0b030b00c40310300640300d1100d001407c901380078001c00006044c0e59502c900300141c4820781c002040302c5029108007420200c0080707540003600840b1a00803502c5e02c1c0c0d1b450241d0301581000030f06a9407655400000c1c0090300e03100000340010080040e080c00039030041495400384a80000b103002455028a05842c42e10540c00b41c2c402915501d000201c0300c1a4400d1003610b180d0121080d252807a869 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 554316546 1106 554315440 554315471
    0x260402130207080408070902071101020c0f06210a0c09170307060b060d0f1401050a1a03070e030a0f0203071d070c05160f0914040f0605070201 63
    0x1003908820070249a0071980581441d00881b0041ca503502c0d1104083e5006503022592241c4400980166500000f6000c0032940001c0480001118000600105800000c0807120a18984000202c1c001c00620385034094042034102003a04841c1030b0010708090100d81c418904000d03030a03412081070502009581c00254403807070115242c0220700010350503014085050044902e0a00c1685481b00c0650040080760000403810616a13039820811408014602c1002c50340b21041c03030b0300d51704007211a00a6a2221880c00d11612640d5a10040303850041400c0e4211807410303103141084158a020030100d0020801d0908a034404003074080704c0108060b02a06450500c07000c01400c104000c0240a40ca1440140280c145c040d25501e000e8403410030154402d10850528084c210f910700209600541c1c4a02c1d00714bc4c07210000d480b1561340300001d1800a05480855698801d11b00441c3c50 = true := by decide +kernel

theorem cover : BRFrame.Cov 554136690 554316546 := by
  have h0 := BRFrame.cov_init 554136690
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554136690 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554136690 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554136690 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554136690 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554136690 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554136690 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554136690 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554136690 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554136690 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554136690 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554136690 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554136690 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554136690 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554136690 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554136690 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554136690 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554136690 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554136690 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554136690 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554136690 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554136690 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554136690 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554136690 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554136690 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554136690 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554136690 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554136690 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554136690 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554136690 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554136690 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554136690 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554136690 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554136690 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554136690 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554136690 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554136690 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554136690 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554136690 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554136690 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554136690 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554136690 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554136690 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554136690 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554136690 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554136690 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554136690 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554136690 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554136690 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554136690 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554136690 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554136690 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554136690 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554136690 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554136690 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554136690 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554136690 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554136690 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554136690 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554136690 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554136690 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554136690 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554136690 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554136690 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554136690 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554136690 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554136690 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554136690 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554136690 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554136690 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554136690 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554136690 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554136690 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554136690 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554136690 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554136690 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554136690 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554136690 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554136690 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554136690 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554136690 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554136690 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554136690 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554136690 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554136690 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554136690 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554136690 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554136690 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554136690 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554136690 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554136690 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554136690 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554136690 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554136690 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554136690 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554136690 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554136690 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554136690 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554136690 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554136690 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554136690 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554136690 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554136690 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554136690 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554136690 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554136690 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554136690 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554136690 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554136690 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554136690 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554136690 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554136690 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554136690 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554136690 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554136690 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554136690 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554136690 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554136690 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554136690 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554136690 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554136690 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554136690 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554136690 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554136690 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554136690 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554136690 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554136690 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554136690 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554136690 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554136690 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554136690 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554136690 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554136690 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554136690 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554136690 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554136690 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554136690 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554136690 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554136690 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554136690 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554136690 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554136690 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554136690 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554136690 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554136690 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 554136690 ≤ n) (h2 : n < 554316546) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
