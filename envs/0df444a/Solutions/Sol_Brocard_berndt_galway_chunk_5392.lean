-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_5392
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T15:43:14.692094+00:00
-- url     : https://prove2.me/submissions/d7c6ffe2-4de3-49b9-8535-6e5ac99b13b6

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 969604316 ≤ n < 969784172 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 969605566 1250 969604316 969604319
    0xa05040b071a043021060317030703182001031104030c08070501030b0a1a09131407090f230904030503090111030105010806060d1119030f11041e 64
    0x200c00b0140c00c1c40340344520000d51804040940000003044901c1441c1059200c022a0f103e4503500005e0100001e402c80e82e1135904601d1105102000e020107400040c03002200d04402d0f880700c000d401c040c50041c0066101032100d03802291404032030171901c05c0301406e2079400156003201480101425544654185400f18040c84e15010318011648207520440d082007900804004904e028006240500800d280c10b12441c401c0d480090b9104650780540c030291035a402d102c0440c42c1c803d4046a54000003d403c034801c443c1260b40c248006c2250011569600708888002100e0070700c03420301182034808030102c0107038040c00c01c41500c440d10400a510101641140b1a9880940e43e001c0c10910441c801c0c4d58482e50380c0f50411560b825034060b5288102030f40030034001402540e0700450001d52000040d01c00c180c481c02c510403480c02900701c001042c100070750300181580300d011001c5840c0c92078039604e49043c0088401003200000315103044c8800c94114105000502c002d4907120b0080701c8540c0c68803958800117 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 969606816 1250 969605566 969605603
    0x601030911040203070e030106050321132105240106050904061e1802041d0c0904060f420c05071e05060a2f0f030903120a05040b07 58
    0xc4c1d10503107445d4089001141c4d144800d1809025802c09801d0540181052070780c0c2c240000000c5081e56140f9450840104800382e840788140b20300401401010000100c4000210f240f580701640ca10f8262014000e48226643c1a00180140700f40c800d8034102050940e0710b8681c0465a641003100c1d0076600546a28002407005a850903007442015602103a6656030f00c0c0c039040100c1e6011000170074585900500c010480400d010790078480c1207125240100701c0d0350b10340170b1075040c40c4030742c541669002c2c0c9881c10104104062503194400d07542030381505135001d15601a00e00103a144021104103400018561440000daa60ba055030143c5090410f0503a5070403503520a81021141c0c0c03c1411445246044200c001d40702011071002000c081e074000e07181030084e5038010000081d040c8411071540d0084040c09003540780030b5018603450030600c01d07200e00c5508601600c0d143da0007422094403a02c1124101840754200c0b008840d50b00c2c501d0744a0a10b4240703401040581c6030002030302581c403032026030308000c1070 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 969608066 1250 969606816 969606821
    0x308030405062712030a140a0902030f01090228030807030206060906060c03070b100f0f030b0a0e0d1101020d05131401020a09090518120706140c03060103091104 71
    0x390388648040c0c606407030905254a0800c2e4010740060201d81c0340822141c100b0000b00b80b180540f182103407120703030b01c0d51102d40d401c0150150100d480c6488004d9000c00c0f88085407581b1810b6943c1c4214251042e071078411200c242070307030070300180a507010f400401130b10050100b201d0f601c403101c01a0780e0882e5042d50b80e07869111654114403070940158004d001000a586000d0710207551011046484a0501319803c001984c1ea006800b0010544a0320300081480340a10f541040020840c00751503080854481c034030050500030710300c4120307942c03144400807a0701e40754035000d030b11014072a0340d005101380300e4182d00480d1202800c000396865075601300810740540c1e00d00d00a19100310710f01c40c0c410072083c2141c54120b2211080b240130035416441840701040040e0f0041c4904100c2e02c2d41a0081415240c20f071022104500d00c4114115520403c0541e180d20000a030140c490315018910800000140c82c00044085404403240d16548804000040480d80640d1040c10018001c0e400032120f801140d012030704 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 969609316 1250 969608066 969608071
    0x605220b1204060e0a21020705130e060606030127020909040c080c010309030203040b0a1701032306010f180e010c020f012403030e1305010605041d070f050a09030803 73
    0xc00c0741084140403460041d1411140c41030010301c2d20213a9919103000c0c141c00c504003000c0801c110025009014801c0011001a003c01030032080f20302040842c0d80f004004400e0741c132200e8002d090004110b0700e003003020740303040718200c000c0c0308a04018a0140d005c4034840d04200f00c105a401e219030034498481984207840366100d40ea583c180203042c1481913280080c1d0f0850203040604240078400041e60110a40c3c08503581c0882c1583c4607040d405d8281d4540b002119051240d0713210034000030034840c1c044244540c0d180c0d070f80500901200ca108801d902d969003401000e1590001d02d4042000b14041000d4460315041604001543e54610383c00900b99607103010074a0040c0d100b120307508000d20007803007020380e1600303a80c14038411135007640d825030081c1d40b8030300c80a001d1140c8004e079200140c0b504082c034a40c007007080400300035668544601600c070350480c1c00f8080c508216030408908401d41d5506075409608151107a01e00c0b0042c1200c204d441c1e40c880100c030000c02c0103050001000410941c003460 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 969610566 1250 969609316 969609337
    0x919020a03200906060310030b060109090207050312010f0609061b1e0201080a0b030c0607050f120703030606091d0405030c07081c02070e011217030c070501060f0605220b 75
    0x1c1c0c03105003c00100b660050300c01d600c62076081084c818101415185041203d0780700172008100e035100300040e1004040b5074400009940006200300400c54048000c04035581000e440941623600d580c0303030050089460081c400407400d500028040540900c0707074180c00c48080031407a03903250306694613014114201050040c00c046e550420b0001c541c0c00c1014154041644001001100003040000b03036182601e80e0128004c0400151f2002030000a0041c1c2d01c0441d074080c02c450709540403212944596103c680140c00091a0520111713110b84904a09011180800c488204c03c440001b0010031f408400b80c801c80c0c09100400c01e0320101038080c40a203004084000c090041c9240c0041d210041143c2032181104541101134180030700d4103189110382c15108051500119180300d031a0003d085052030700180d44010020003080282d080030402490914416402403141555445000e00010110301a81c40810010302400c5e500366106103110b4940c020690308c00c0c568035680c1c0320707140c2d9691100d440003 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 969611816 1250 969610566 969610613
    0xb0408061f0f150206150a0501081306050117060603030a052502040c032304050d0f020114010e01060f031109120309061201031b080d030b010c02030f06070f02060919020a03 76
    0x203c403550103100b0542e010900c2c100c2c0084020106000410400e002d00419040c0581d5402003401c40c155440f004024540c842420455940c541079996606013030400c1404061040c500010161308022058a41400c0703e51511401c1c550031410080d0002c0c0182c0c0c00080c030701c03144000704000d0783d00c5006801e0021600d840008520f506006500d4904e26041c0101400510310018400010380009143c98264500d2402590044800208a0160641d803031030580c020385043c0042000800c61619904030341d0316031900009800510419015034400402081c11007200388031040c524100000c40150640c0b4040589103801e030464002011508850812200c03100c882c0014010407018016622003d50456103c108003854284d1295a030300303030300020300c00f0941c070b50301e06205c10f0340a82c04c140141640241035a9100c9900000300d0703580c507401c039882c40010380034800003038800e80045101805594120042c0441d007401803034540d1b86c2202d404080f070300300030840c40000218054840308000100c80a0f49c0 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 969613066 1250 969611816 969611849
    0x81921051f0315060503030403150b0d050111090112090c0b0c0f010509010903020120040302150f070317070e030705040507110f0c190e04060e01330b0408061f0f 71
    0x8000880e13180e908424081d13481000184003148040d004c48441440790000800d40c250444081903c7c0d00315039900404035804c01c2011080c0007240c030054180d680742030b83c9101070ba0024078041e10503940e140d40068480c0400d0001400100c0716580101840c0f1032142c1210400a03098018a08440044408400c217940d44e940c44400c140d42801109031101408840c0c5000c01c10702e00d50b02003184514400217220b1080b0310203086112014405036520950a4103c05440d101181170182540038404286034003110814002010540a5400241080005401082264140f200f4400103100c003811120502c11540d070000c1c40e42a0400000d084410400c01400c00c85d0109002d2140301034200e4103514201c900c0380d034180000c0360b1030010b07030b82c0c0306410507008141e0f8081c000c0c1c824010070040c565050b45544108040ba100101c000000b00460b241c80035481c0c256079500c03603030640c0340a130780200301d1584c002c1d1021440540211103078404c40418401c044030119640c0c00ca0512100e0f03158090000783c1c160810 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 969614316 1250 969613066 969613103
    0x25051306090f0501030204081b0a170607031103130609020604080708150f1612140109091a0609060105072108010e07080712110d09081921051f03 64
    0x5180c00070070f0300b82402d500385400e0001070345e1107000c10002401c11480380388402c22207030703a5100040010008248502c440150340f03092107841c1c2904440080c0030034107094050719114502c02c100c91040c1d00401405c8140c0f03200385e48090141c104000142d80c094000e000c0801d0b507190030f10504000780a41001001c24949600c540e1106000c02030041c0c02110881080040441c20341108007042d01c042c2c645204201038684070710000700340307040000070b41c200c1c444004500300d00c01d036001940c0b46001d05401c0c901884500f9000500000455a0030340154030100401c02550260010b4030f4134a02c14046d411491800b0b10b19480d42c0c522005013000001c0c4520010482203000e604141e41011643ca442d41d854506070310040e1641801c1d01e401480a95220b124051030303005042a201c16000b00c290a20401d0301d24100304902d50411803c25156100701c032400d40750203015108244d800c00c544140610031030a11035500000300002818100206100502c01d03004010200540001d1445843c036003c80c550f1203071 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 969615566 1250 969614316 969614339
    0x3020405011d180a030804050f010509031b01051522110702040605121221010b090a0803130e10051c060501061b2a09050703050f2505130609 62
    0xe003c0e06003000c0100550a10780c001094440080340c2505100c1c9081c0c54a103030a5160921440a01c4069440c020134494480c1e000700080c45900021030208442031baa1081d06800c0301d80a550b04400c903503180250361a9410416082030911b02c4400c0068244055080900155003803c0c0f249401c1039030004d0030608629252107440080c04064450720049400340c00d10a03500c0c5000909a80350031008502810011904c80065247c1420350232800c0300c550f903400e41c10a0f80d070450341040b07200c0d0b2074034000440c0405001058a035040804d00611240d10315124890a083e4805002000c140c05448004546a141da8130310824290a81226190440941c00c15004444068014004100e41c20420948101106405040c400c1d001a00041c840e0700c40d141c0080305a001650b83d0100110324240040c80500d10361141744201d9140c1c80c2030005a03540a2000e0001034101d07a0001641800c002c0704500c1e10982e103c4008400c11070801d80d02c1e22240c900034400c7c02d605a440000090f040000030f011301c81098 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 969616816 1250 969615566 969615571
    0x908030a09091103010302010c0308270a02040e030a051804020f0426012003060d0c0305030304060c02010207150902041413021507050331030311210306060a0903020405011d 76
    0x100710f0364155411940020020590000b02604100300400803c009011807072020441c54007800c813140a100750030303510589840703151000380e1040745402400c1005040200c11581884a280c2e144d91a15000ba010040b80c58070405006030000d500f8007160303281e000074500500c0a0f0450b034058503480c20302400c0e00080440400301c0c3c0e06242e4103141170201e640840240d2188040c80120000b6240d81e41c5c840030402007003668402821001c0312a0000050040100055009c0c5001d180280b100416100050b42030f0b102e5184000c00c0490320407044a08020150700000b120352000b080404c81e0310000b10440c101d20402d039034403040d0390702c81c261207400c40c5400001c2e01110341402081c0d90401d5004c0e2a0726449004401500800c884d024003030000c614240710020070902026900c041d00700343c032030a00601d030141202c500171452050345206904401241c4404900700c1441103210b14540e600000e03c0b459400054000051000e0400003000599860007510702a2014144031080718510010003400c00320003 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 969618066 1250 969616816 969616841
    0x40e0a0f150501030207020f0307091d0c06030f0702031909050111060f0c070c211205120c09210604060612200609040c08070e01051c0b010908030a0909 67
    0x40000450600744071544400407107100b42001038542c1c0c41e41c004540415002c80c052641802002702c040b65040441c0e01c20342c0b0700c505000540b8041c8480c61255640c49440380300c8a5405402440043c0503000c1c40703040103038070540c0c0380b05482c1003111507600d84e031400241895920200d840d00009012650340900c4001d035200d01903008089506180498188041007e07182d100c030440001107180a01c902c50312000c0003005800201e100c100b50325048201d4030002c8400860f510600c078a42c03000c0b00ca203e01c058030003103100300b10b009a040d25015007540c3d060703001120041c1c002d0140140203030021060580075a005820710040c20692516107805411036805401c000c0b840000912540003007802880c41100a1810141c80c1c1010980400024454065004a0f55100d41401000d80e00c040d84092514002c800d280c0b00d44d01c0c414a410010744142c0601d03101301e44109141130301c4c05020800358000242401c0181004480a03480760aa141141d001e4001e04020036101141004507140b0351003039090409a = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 969619316 1250 969618066 969618071
    0x9040e0a2a0501050405101404091a04020306060a080403091e0e0c13031101030f06080a0b0a05062b0605010321020304031718040e101a030a0b10030503040e0a0f 71
    0xe10b000601680181d00030396000341e011000104074240660754005500e241003240d16165a61460420064030120b41900c005800b004034440044c1824020b0320b0252000400141c10004906003c55494100900a80030010518000103400142d41e8941400c00503100214000d80e0424411180c1400d01800088003100d0400c5209001d14803150700d0b070181d90380504540c02c14840c4400482c05403629014030580341d0701c1c0c80400958503a000900d000303064424800d0f420150ba9640d94131040320021914644c018004d8455a00110b090164500540c1800e081c042002421900d034001101d609810484880360308010107400f450000c0705030301c24280c0340d00c000e43c503050071230341ea07104480c0143c02c10401c103500204d42d01440102d1041c2d0b858030030341c0242042114840020901d80d69103042e80301a5009072a01b070304500c6112111150040841e4041c0041403c03c4007a942d41d0000c103c01898040903406403d804030000d1824001840140b403c2c1807006824145000c1d46800c80d1070240d0302c042000e1 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 969620566 1250 969619316 969619319
    0x2101701050922030e0603070932060a140304060510080601050a03110d150c030c050f0a1b1505070f0c0c06031a040203100e0105030d090b09040e0a2a 66
    0x81e14095169510b000003403165409075501d016254080c90802582e4040d002104002040c9c5c0d024242d8030171030340e45101403103044c9030808500c21402d0340614106107900d03410062010070308141005100420340b034134280403e86030568629410b074109403021143c864880b814480600010046100900014000341400d540340000040c641d042e14030005040e20100c1a81c42015903661902848540e00301243d0303001c500c60707152428024141000041701081c9410320000c00d043c4583c0950341c201d65420481e03840c0260307216040e5015020b45421620301c1195500406c0001d440315001081c1d5400b119012501e4107140c200a0030300b104101418003004003842c1c885002c200f40b5034000c004c64025080005600d608000b081d001200c00400e0150084d000100380005001c08002c20811200400341009003662110101500c50041e8001c480c00a100c40401b0712440b1100401400e540c04000d0002490450703c0104070304200750b0710015110100240d05207000340d49410380140f002d0500303034140076129 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 969621816 1250 969620566 969620581
    0x60b0603150405070c0b190608070503030d09050a1b0905011703030f0403092d0902040b03010e0c0d09060e06070f0914030106081e0114070f08040c03021017010509 72
    0x18041ca08028496030302d50b00030072129402080c94001040d000300b000f4145143c2641589040580e10303085000f0a8500b0b035000403122004107243c0c090b6500280658070382440c02d24080003804000009540e00c1c0641004240002d50004130301007041891482c00103a14507080f00c9108580c0b05a1004540ca030541c480c0c414440804011668000705440d542c031a1910b03682011544100c017600240a030210b030200c140e01031070020301d10100700480310219000380d582300d02141003640035078071408100650500040c800c03816410303122540078218880c22824900481c129500380c4280340410344400e95038004c1d142d0720003801c0c440d603503201c1568100030000e42c081640c0202044001d100d1807400044074099100da55800b0341000000f4210501118503030080c011100c2c07030080e008454200c00c2e41c40e00300c0b03940038404010801c44c451540e545801c000080e008200743c41d03000004000b141c5501070f2490110045c0e4514148100345241541e40719840c504107400c0d40c012002c1a040317144900103640400c00c19 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 969623066 1250 969621816 969621841
    0x4020a050405060309010e120403141c11011e0207050c15090103090f0b0106081602072102030115090f140c041a1204120314270c030118060b0603 64
    0x4680b07041c2c0d002d40c4d582d0784009001e401030206600d807107414020340daaa0024410041d0181c02640d0090803c0400895494200d6955040b08120090781c2202095884201350240f1450b81041e1803081c0080f895117082c034040301c13180d480d19030002405a4003043e1203080c8201003240402c0d241c07094a40c1c802003256010f6405840c01001c1c541410981c0390780c03900040158000a00103042d501510404043d40c4900b005001c405040755601d81d4010203030310440e0420301c0042c81c807044810300e604003c0d98a16035250041b1304038800b00c042c4c3e05503484400400f02c804110303c920b00101121080020341e20031100b408c8060301c122481c5415201d000806000c0b20b440840119030071110308131104481d030340e458207411703410303002e03661b10a44246d85080421051045140d030801200d400741c5d86c100081100b41801d04000d590568414280ca9240101d0244601101040515020b12913046410350804040000d007943e03000003800f00c60030950350981040003d40d0040c01020b00342125141d04610f005c4c17030880203 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 969624316 1250 969623066 969623069
    0x9060501210f0213090902010f020a0c0e0414030c0c0411120f06010c050d0f2a0f060204150c1704120803040c03060c2c03100f11032404020a0504 64
    0x104942e403009001d24260040c0c1c111050340d103129001e8607034142d441280400500340c852050303004c10202c8c0d884104c4140301089801c01940d21220505c0f0860174107103140c1d0701203030080045901d61a2030a2001c4242003c201810403111640010401d088c0c0001c18070042d1107074448044c08000d000d004481074855545125a0300042c4075101000d40d96900c00101c44004142ca03001d041802a031903080070182d8082c40d00700a0310b10503181c106080403e082c0c0c113407402a01017080307200860300003003640000da01c403501b00d40c1041c011400503082c29158a0025005000f05450002140c5528120020041c040f408041c100d5030024000381070902d03000d200700710340c25507401c01080d58800000003010002c079520780d00081c6412040400c003c0559102c09050b40070501c030321a5144017850313280c82c8071821000d080380844201030041c1044178849840c04c0040c10803c0580124251560031306c0d40c10f845108091881404003280500e05907507000091501145541c18041c00f80380104a940003d030b0300182145c0 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 969625566 1250 969624316 969624377
    0x61205060402150f0a033b0c01140f0d1410030b0c0f0f0705100c090e0a0506010915030f1104030b09070509130206071506081002041a2107030609060501 67
    0x600c0c00141e074050361003a540c4601d01c142c07c15001809500b01d814004600c44020720400032161818400360042d6801d071100c86880b0f0800804100305039052035030784040c012840000d4404101e030034038045c81400e0795100700c450615901c0d800030b00b08140411185641d40041c044134803185031010725a800d0b56148a106220030152000103401e00800404000c000607030409100100b0205050b840b009007a001603114081240e01d5003030100d1808500d0784a15809043d050319841c0350b55141110305032241440185180130b06a507800036980c17100030350144178100303000c050205a4071810b51500d0980450003414072017090780040802c2c45152512600f164006410500942402803948005843c5121b0008014403191080d40c01c008100c0a68006400355805c44080da840310103480e0030f2104900035803048a03a0824003041c040c107600500702c024411031280f001e003c400e64001007044400e1080135107107100020794502c2c1c100454480c0d4412100605400d1070a240d100105407840f21401d4034051104 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 969626816 1250 969625566 969625571
    0x32a12040206070c0815060418060b0a1206050105091807030206090d1505060a060c080702210304080d030507093c0611061b040b0706061205060402150f0a03 69
    0x40940d9120b20a0b107030f086030300010300300310b080d241c2c548640c4031200c080c5650b140440d08008220940740500698026819420542810307507140d84a55024103010b40308070342c010b09138801c081044000007548061541c011070340865554074007000c0c01059440185405603c0509100c1d41001300d00c00f0854000b01c030703011685070f6241c1d8261000501d41400c0090010404400c613550008182859040180f040740f00300c9440d98416170310001515a04104a001000800c0800c41c140041c030b498501910081c0c482a00307102920305805810b440c5902c59000003526a20000580c05040e6160040703170f078080254070b403103214189894445038610b0505201e200c680005131445088000181207a183c101c8001d0344100b035050341d03444010b410441c404144103d540204800141e010f10b0801012441d03034610081c291610b45008001e00464110b0001290380381d84a41c00040c40001440c1c2e441a264010340c05408907084c244104040d014110f1005454482c0170b00203104068054402d03a10400d10f90b0501 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 969628066 1250 969626816 969626821
    0x406050604230612031306030e010e120717070201120b01020c1e1908060105011110112722090807062f0409020a020a0215032a12 57
    0x1806080b41032100c4180d40520b2104440491000d8681070107044162000c81c850126107103400e0301c0e0f1152111014007080540810020284668007007624208100000901c2807440e000035400d194030140050001704020440909024078822403030380d9551039222a030310746070280d4006400c4120480c1e504181a03030751694004164024401020f00c902e004184441010102c07922000815524050724000c07c2c40c00c04140c80782400740c0000003642d103d500102032583c0ba0600443d525050142c2600150142442c08040d1200c0d50042102038503818079026290501c9800c0b00c0c0d123100c086440e4030303145005005226110344030040da00305440039450032040f002c242d00b000000074002d03e07071008100100c005035900c14001c01d40d100000384001c040d42c00b6040c00c80e501007a81030342102000703041e0702c0404000400105840394002c02c1103031480c2c015201c481c41160000740542702c1c28075984504100002c100308000b08040f48a030030b0b240d6890400c5010000341c0c0c5e201c040a000c3c022a010001107860003 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 969629316 1250 969628066 969628069
    0x503190c0c0b07030c1a01060f0302070b06120a080c060106030b090610050306030118060c030c09030804061809020310030302071a04150e1504060306141e040b04020705030705071d04060506 83
    0x400c5c4d013550704007142c2030700582180a0402920000d205010000300c5034403082980a110b802200c3e00c0d03039007180704503583c0c0c1c0f00c0301c040200d124103818400c9418800c900c1207000264070303100640382e266a00030260206d50300d0305001500395400a40303014890701c54081000b80c60340c0d60208005841d0050300e42a0b440380e0b50316000c2801482580e180e10701d4052514120002c01c011604150b0310850195814403165400040070794034045503002c000c00d20f42050006110043c8103034039250307040910407400c101c900d989440e00720032a4070640782d03e041d48880307040910070306404101a9005008007040070001c50290012031021f80114000d43e21440c0440d0750108806100c3c0b040040d010000030318800c600f00545608052680c020701ca020007090800300001581504003503465441180584420032480059030007207000c0060000f8540d0003030359400c00c00b109803158805403080e28410300046540e220207080c00c0e4908107042e4031400c6410b18140c512106d00e04240d00054010307502c010040340c11341386c880 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 969630566 1250 969629316 969629327
    0x30c1b18270304050409050a15150b03060423040209090c150d020708040f03050d020a03050f0a110303192405060d02120a050106030c0f200f03070503190c0c0b0703 72
    0x510140d031060400603480c0c01d0100c0460070000e039a1190a506d1002ca000b0785210041cac2d110913002c03118004030003808101d1002d070b20006690268000f0800034408040034003211198151450203449031040740104401c50429041854221543c00020081c03094a8000035000211140140c003000202184003400784580e0307010384101a602180040d00c035625400e040340780c07001611042d1100e1040e5031000c2203031800424485000c1d50142c0d541450080d0365424107a1076441200c1c0c0340100310ba02c03001d0304800d01d4280050760142c1041c2e001311003440900364080040c0c0e1000084501e4000961848104080c1801c400d0400c030b0b00103481880e180c402400d140e400a010b006051414901c048003042100c05842d0300040c1600c055072010010b060305007000301c9089448001c4600415445200c00282c030301005104000903280c4812070f00c126490300070040c110f800c115805c8030107034004a141d030b1217200d180d000301c028080d03149042005940d40d501c0303030a1155220710a500e206840000c07458240751007803 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 969631816 1250 969630566 969630569
    0x513020a211e021503010b030f181b10020f060403230a1701060309020a0e1812070201030c020a0f080d110c0a0c1d0f0702030c1b18270304 61
    0x8051040c20300c0c1815450082c01008a000300e114001030314039401ea100040090324117840e600f05940d400c40d03540c96651400d1000160008000484c101c005032089041005800c808008a0f00c92950704401341040c03016140c40400c1c0301081d90000d240c61800003d00040740342c0d0050f014604035503111048a1041224a0140c403850107180001900f2080550084005480c0b407409000407000c4eaaa0b13041c040303085401c1c0401c02503114100d0b80341003024407003040e030700740c0c0000031050030145502d1072200140c5801c044110400e01c1030b0010440605540e014800e41403020168000341c03841d4090742c1c1d54106614403d0134024440c5002042c084001c040c203a2241c85a19960202c0e16a100c64103241295146030f6400304650210b915080800d000340000d8001000610f0f40006d070303c2c02d8441001041d480640180700c40300f140701c00e024002c04554100300705101c0ca46440000c6404030480383c00d00089a00d254029a4031480b030005104001c001511409a4084100e400c00795444d54001d6060071f40c40346 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 969633066 1250 969631816 969631823
    0x50f030403091205061b09011e030608190c05090c030a15051503090606060a0527090c0406120203242818090f030f0504090504080903010513020a21 65
    0x524402604201c1c4c009005801040741900340c01243c0401d040305c016505c00c00c045503001808072043d0444110500c41c80c00380001040c14049404d0352075224042c0b90405102c8900304411548888100f03208420780144c0140c44259403d01c01450013007a007001d01c1c400508850080da5485131081c02c085d4043d06480058640280086507039141394940e0300322030700142e500c80564020840890325a240c06130131030320040300a4549509204140302c0c0c0c102141d40c0c41810203180980809203040e03030b41e21031140d0361045841c0051a9100c500348403006001406c0104622045403041081c0030141d1040052610120141c1c0b00c240a19110740c00031901ca0f441442441801074230131042554000d1702c0d50f02c410140d612007851108541007402c0c480e020703550300a1000e816102417002c0718001ca031241d9010391005865041c105d140c01d6a60202104580c001c0340c040c1d8254001150035561450280038040d0861010100b203864a90b56030000f40d6102e03418030542d10840b01c80041990009090146014015003 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 969634316 1250 969633066 969633089
    0x1140f0c0c01020703030b131b03020a0504090e01091a0402060414040f1e0c051903050907031406100e3108131d010b0f07021c030f09090c050f03040309 67
    0x4d0b18003e0058804d00c0c80c218418030b89100b00360000707240d40c03042c400341d1b450140700c0d0064481003c10580003940415442e1080182c10080465280064002c041c1004421000007035070007528209402c40c0a065510b003c5003076814070501016030369000540d0252030030702403d0807920407803c0008000b02000004444814201819040d40982c3c0481161441d20042010f008450b144c1004481900c41c0107640314103102c8000300e001100303110342d2000e64070406c010126402e02d0703140d44070003015882003e220310050b400501004051080343e9a03000052484010301d09250410191450700160030009800c01c1d0089501d41c907a00c1c5152501c030b0f10000742c00c0200b0035900c171030b1050f81c4609600540188415403551100c920ba252030008110780c101c031a0520181e007019090480b40d50280e000840581c5e11203114070071107080300d02c4028107a422a202c0e031110300c2d0341101c060010300714040a0340080004da00e0103036002812600a011a032510340ca450079950790756514601a02d050300301d034005144034407 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 969635566 1250 969634316 969634327
    0x100e15010302070f11150708030c162109090605031e03210f15010f03051312050d06061b020409140105012c06010c11031002030903041701140f0c0c0102 67
    0xd50317000f02403030b0f03540280c682c0e090300580921401414810400001c102500070000112249294000f90a8540c0c1030715041c01c103055161580c81d1315666481758a114036040c03005050110b904181d52000406da6480709200d0940340400098541059a4400101d26101d05c00031450382801d0049541c80f090801407034403040011400c28442c01e200300e46c141466880d0310003064000120740350003514418140c0d94260007a8042e40103c0140c0b40c003900b0140c5580d0500d2905001a40c0b401880c1e0368407005603038158503402c1c21a400c20503158294403d6080c00301484803d510030414420150340c0d15016034020481d4003151401a07000d2081c010b034184654640000402c0c41004a581400700c0b4541e0740d0310041000d07118903041801d0b641560a5404070782806428000100d14001212015034001c080d24030360441121114140e90040780da01c05035410000d424400e540c3c00e02003501d80b2100c40c00003081180e000c583d07000040c40000e40350190019001000560408040d030440c2c420a4850b0025915113 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 969636816 1250 969635566 969635573
    0x7062c010e0118090c0918150b16080d0f150303050f1e07030201150b030906010603050a09050a0b0612070e06010509060c070b0a030b040209090105010e0103090c1508100e15010302070f 81
    0xa10050041c401041c260b01f0201540031a0340c02020140a81600b1640701649800725540e803651002500d2410304000c01e5500b8081038401d00a095511564080802c07600c3c170309050b0070300312541c01d614201000c03000340b41071020070fa20006955061161200c01e0b0b1f551443c80703688140b08406488000801e03400081d03101c0405a06411801c0a60201081d07444659224800307403c56000c1215003860390341c0000c00400c01b90317109401064000c030450740c0c0082c0104241c1c0741e450500c444280c054850344004001c2c0092828112a101c07845000f22010301441402c0c403014180b080009064a81000300c0861a50303103956941c01201ca1024100c4211200d0316a580703500c071410b8000d03590b00408607183c8000c225490802e8021038003602001441d40290340e0905006403014841a04514100340c0d6824100001601d44080302d4054200e041c603400c1d480b072114900500100008000b040c00045e080010000031031100310454001e2010400f044c0b2080381c00004030000c0c0141000a40f01e0700c4000708100a2 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 969638066 1250 969636816 969636827
    0x901110301121b14010804171201060f0c03020c0411120108011b142b02070c03050607031404080c1218190f05060f0c07062c010e0118090c 61
    0x405128654006521050f03402445262038644034042e00c01c40e0f040e200d11050762080d007200394031030302c52082d40c019040c0b020280019a00414140c0410118520050000c280c0156080000f00d450f40742802c6a440240c0d0004d49504406004500468071500e01341d000400250642e6015405074609000700d603506c40040d80a03204603400345241d540c8402540e02d1540c0701ea0300c2c60641000142c11645000841e00c480d0703111212980040c00303100c0704030452103601c20b0980020400c840c004c40308406414150700f003040c101306000c2c05810906261441031004401c4102072585e0164000306580e848142d8080c1c01070600010030301d48070b210200003031100044101016008a5038405451641c0c10105005003124203940c0c038091020107132a0040c0c00c0240d86402c40040c140c802e69941081d04101040e0107543c60400c09030418004100d88010b904400f407104d480e407000b405c40c20a03100007490f0b0503d00207402c920444440300c2c10030130f40300c1003d1508a264007282004100b4588100f040c070203c00e10040c103 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 969639316 1250 969638066 969638099
    0x501022808060a0e060102010e010c020d0801050616030503130507090e1005090316050a05060109050105131407080606070f0c06030c020f030906071406071e050c150901110301 77
    0x10245010008030208a20980301140705110142c0000c2c03c0b64203144000c0388000d801002107045640706c00f180c089886080c0a52464003031642c0088c000c41d94a4030019008520582120b4040e480911101c058210034000062806405040403544d07600d0300030034060003d0f101c200c054490304c15444005072880a551045032241520030613210551021406041910026142a40e0581c400c1c0120550303480b00040380c804091142c030884201641d5982e51a00b0104240d00c045001d41e40d943c01001903007010702c0c0c000420003401341d0401c0b0441c0b41c41e50000c003a072000703040d540c204803a400000d030345500c64070b0407540f001d07401003114002100c02e480e1104510045020300b0b80068200809041c030f090000605840b4001ca42d406542071060f40028058560000366003a140c16096022406000100b4400b01d800f41e222603507002c0b0383c280c2e80900740b02030340b0007151207070b041140402207072a800c00080760007030740d0450b401010b0003e6220351141c0c50140582000d03142004100000008185003d05000c21 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 969640566 1250 969639316 969639367
    0x8060105041a0109052b05030903011b020607051605010906050714041d1b03010b0306030132040819020a0b010602060f130323070b0903031918050102 66
    0x1c0b4081c01e500a071101544008600350210701486000d20030f510300f8100350000403032141760300a804403650410052031000c5882c242c8440d000005e0072240740c00c082c0203a0000440c49090190311540700500255680342c0102034500b000310109010000031030402800c400c05030840028020000d035401d1120040109071040800f24994002c1600e80b0100d010644040300c81c039260003480a190314140c855140e1b00203000c1000e03c8841c0210b6040c54810328003031806000e03090078082e1640307894001e15084804580c40d4103a101c80e0250443e03040c04054102020110b4450110900c68540703181040c0107004190b21882002030440145000303560000b60401b801d030048140081990340c88900340d854441c1138621041c1e41c00c2c2800000c0d08042628008812141300b480c00ca080c3d042000c5807030350711441140d43e6900c44000040c102d014040200c6006401c00128005540356080010006080400121000300541d07140e0011601284208206032642500800203655911066140e91501c3c812024500d = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 969641816 1250 969640566 969640571
    0x1d0105090606092202040906050435030109020a020c100f03150b090907020a12080402120c0906040b03030904020f031009140a05090a0c1e080a170a0c0605010806010504 74
    0x90040e2511109441c0161424852400c4082d0013000000a00c200c406082c1c0e00709444040072000180944103140c401c50185000b6503a201500100c1d01c141d4548c10002409500203240b80300c542212403007144c1c11241038150059452400c1001079040c016503d1030b50b0b40c054030920200d040c542d0000190307200040140c1e010050040640f41c607034503080c0a4040e81c40a10b10034850000c02c2d080080100350445076a004403291420b195840020f1854801f0707003d0300141c0500144001c42c141418110052281c220203402128400c9003c03031000030b00189100d00c03650700c40450166549060080342d807100005002076548003012001c010036580b05690300012414006400114940a48510181c009201e01114251746070301d00b10001504000c0c0544080380900846000043d80602011009100c050529a00e25841100c5403403620381c01e5129a1f056040954040001042042c00919000c800740ae5541c40d0840c0c40c44c02c4039001c403d44d034001c08291410f000441c80d1200002c0785812550201d509 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 969643066 1250 969641816 969641821
    0xa050f0a0b2101020a030b0102010e070506070314030106021b010302090d0222021209070503150415060b07050c0111012705011103040609050d0c0218220f060b0d020303040b09041d01050906 83
    0x490882f580902d800c80e49402c00202070190b450080d0040c94035a0113840c060f00c01d4441601b06807032540c000e0342b01d00c1c0941d00020800585010910255038084070034241181446280070100e1103d41380d81c20001e2080c05036460840700044224811901c48601000454840c109800b4098480000303450300503075071241140000b4070786000503c0e004001c0e800c4c0700c0c405068460303a4510101b8074052400c580c64685a09010903920312000103003072440d01a000800b109080c410000d004020b6111f8001c0c41039061180d1260150a20760040458611244c122080d9114500300140180015100d08504500000030301c0103003d295002860503c2c021420b68030303a0361125000343c481a480c000002e42082559120300350101102080690208581804862003200c5010303860780914241d00c1143c103880c90064a4003804801c2c0300f00034400d5410b913180080a0900d400181d5a40203038455014101c000065842403919a03801c18100681c1070784200021000c0c6506190203403008581c2e50b1000d2080700700 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 969644316 1250 969643066 969643069
    0x40c0f12032a2d030504140d0b070c02041d0705130902030f071802130b0c07080607110f0a08030c070c0e04030f0f0e01052709040c08060a050f0a0b2101020a030b 71
    0x43e200c2201d40c0c1519441c2c58507141a0601140569503940290300840c0c0c0c003169008540d17810542442201c059072044440c00700c070705c10801218000300d00400c0a00a040e648503001c5030004450341030b01d074100e8030440c2c0e607102d1012a030090003100000035058061000d05c2001024001402401c0d074050000e040110074000c1a42800c80c00341c0606400c1c01521010108000819075008240c2c0481500c10b032040c440d00e4403202d0b45000b0f4103503403100c00500940650056142d0a1108a10390b422810203008852055100c504036070002034043c180c0440c001652078104150300810000621040441a07283c0c505410b020340364a42894465000c02c403412030b04040507100d00080803031b104c016158a42050403c0324200d103d0104401e000320205c2c01084050082c1d511a001140714600ca81c100e0000c007414591030b2401d000b409020030410710308190611403c0700f01c0040141d40715041130030019402c8802c000042004a440c80b9a03251254130a001c2031178540190014a0190002c4c3c8040c442c8042540 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 969645566 1250 969644316 969644393
    0x120106120e07030b0405100c0905010f260c0d0504050312010504051b030c0c07080f0f03130b0f072003010c0c02090c030903070812040c0f12032a 64
    0x118041d00703400c404001d20001d8001c40308550014021402c0340c81d1844541e04200440305803401d1100403404200c4100242d6034040481c2d41c0500703282c41d0040fa00c0466181d00c10351042160100700c00d18040800041c00c41c1c032820140d4401005034041401141401d0a0064880d0700003e800248a1255130002c0342a044ca40034683c00341300c0c6001c120511311f0134460251a10380000e040e100b4042c6040042c1c1c071880c8410004100035011010240030038101e420202032074214048800f5032550810300240c1e98510994450384102c40c3c2409030550b949074640751071381a038071404c0402410b41d1003030a20f07500c200a15402640307071745006038003c0001989440081d10032400890b8001c1d4002c128200040660404001440c0c00c010180f045a0030810301c2e5492903600e4010008481845d158078003000706011180c40c414004001030440f480b80281007002405040c003c418000d4280308090b080c844100c06c00107011501003404c090300038041240c81c900f912045698265104032004509007050451038100f = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 969646816 1250 969645566 969645581
    0x50109050913060f02090406081606031806020903011104121b120f022b0507090501032a03200f030312070f0c050a0b01092301060302070809040212010612 68
    0x21002c0d022050f542c07540c1c0a0566500d4031210181c003405899000d850701e0040b4005801000007501400c40c03e140d041e201010725a10a40405040c0340740c5040b541c0520400700010303a00910056601c500c3c80004c80e01420780c810761000d80710750000b070000e2020401c5405040e6075201d501e076440140c4c05118401c011b01404d004401a0510007a803000015941c40b00c494420351014142d60039070380125520004402d5049072682245110b48071140c100041884500054080700320104181d5046807030304120782c0000204000041941503120416110491201000b1a41301d4116002d51002004541001586041c2d041c020317508000e68103424680801581d418442c00d0512120980e2504800c03078003030300d04804000500205400440109101303110b80e22000e03005200b981d455515202040c0100c61000a50040d154000c02d8508100b10094071440c6c1160304ca0302d000750b21659a0b040043e101d1044403902607020348001640d4480204240da031504903191a110310b004941000150700659080 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 969648066 1250 969646816 969646831
    0x91b030210020a02091815040503191706010804060f1a0a30030c050d02010c1b0c0b0306130603060c080105011706091509090106181a12010b0306100501090509 70
    0x10500003c4001c1d900400d1b01c1c00c1c08501c0b40071a480c0c2c05c59401140c41d6044151000d40d660342000600c2211101d50070040b44100c0e42c035140104c491101000d65226444018204a041140d0075001c5420f20203aa00b00c0740396120200000c221202c0c1d4003030145081c400100b00759004680c41c400001d80302d041a901031414403640c00700f001035882c0d41c088100b441180c1202c03c4062086480550380030580800406032503650540001410102160700075040c15600c00700f0700c14101c5080802000504001c0104080b034440c1c0c01340c161603455101c0010407107255040d9041c1d040340b60810010901145810000310542c083c0c4404c000d42e62950011200040d030950a04600c0044101281d03c07030a01c034100300e03804101030008026003000c00000844404044d80c5090203a91102428000c0720300c05101e580c0c004910f10820002c03142c1a03a800040c1c440d035003000510940c480c2001c185c03015001c1d0825418180014241d540500d0080d511030b01d11552030240c2400918051800300b8903041c07004420340203640 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 969649316 1250 969648066 969648079
    0x40506070f0b0c0904050f0903070f020307050607030306090b010801082a0604180b03011e09050724081b0d0209190906031a28091b030210020a02 64
    0x404060101950045204881980e1420300c00707804948403040d014050f500d55184540d8a518030420401540d1000d404030026440c48000d1190307690000086400d030301d0707005040b01040e4142e800028140a45ea0303000541042d00001c11408040d41a0700260940341daa090810410242900454950800b40070b84803950380540c034460000d1480300001106d6641080750058107560210206045400940c044900c60a8140d4030481c0e01400b4014001807200c154003c024010304542c000b00c0080540c94500a890341d0b4203035010501c00b00384802c01c0035003168007284040512404c0300c3c80400160a842000081092000c0348c500c41c00161050050550400d041d82443c002d440e007a4020342c02803240a41c051004a40c07001c00964440a000c0182001d0000141032890350500b8411040411040d840500380c0d001044003d10301c48413018424812074041686456500c2a403200900c01000064a8404400d00750851036210303030b80400550f8800d5a090100440090007646d98004007070000b5031124 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 969650566 1250 969649316 969649319
    0x102151b07170a11010b030a1113090204050c12090703020a03120e0a090c12060806070c140a0f0c05060c070608090c060c0c0f030601080307080702010c02031f110c0304 74
    0x6000304041c2140c18040e1468078070b0124040005003055100c0c07280701d000701d07440450b030366003c00c1d00b8418001104000e4000d448076000d995189110b2515a8107005d00c2100c180d042d604e00040d02e5071011607900d902400402503800c00e01c0d14050180c1240000480445080d40040d640103808960b2100303c0f07602a05480c42d00e03046660344680b00d48a0644d0304204200140000c48590324120240010903e2450004104a007008000d000c3c802c54420040d01c142000802c000702d04000555541c066218903011998401a02c1c03c100420a1441c402c0c895208006000003032142d20a04968014811001460019554018481d050003500213044c03072a007004004001c1341d80181600c030340c440b51940c20f4448200e841c1001030b000740c1001001901641c0641da464256007401d1000580002044006149940c5409440c542d43d11600400809880d00410000304690050b00c3d005c0d040f0f50300034180d5018103112062020141002882c0451090918014202e4828028119010b2410760381c05180386c40d = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 969651816 1250 969650566 969650611
    0xd030203090126070c05011802010c0210021e07060e1005120402061905040513060302060706270501140a151e03050304080618031c051003020303030a0209010215 71
    0x1c02d00c04001a103039081103c0b10258070400e0711409100d40070644a4404d401e01d035003400da00316800083d010304900111b0a01c1005070f80c1041c070707080720503034100c4981c40741e0799100d50102d0620544a850b04041c000c01c1c0c12000064038046455820f0b51201e550301524143c02d1803c222644224021940c003050007041000380b0001c0c0301000c3d07544076001410a0b45409000071a00000320820285240001d0b070106061000d0700d00f0000c05210048643c409200d8036042d6000100c081c070541c1c1e4010320031a40c0d800480c2102c040d84a1102c2414030b074000c5408800f2060600034040c1013808002d00a400381e0f000012006102403290104c100b038010802c1700c40c01d0900800040d56a294180c8484494040c04000f00080d010401032020b00003110241c0341e10304214095040088151044e0a543c0d001406680d000c4c0e01c00040203c0032a221403000308071522000030000081500783c002942501002007044a241119001010749420070307030884400401c022141001e107002a200710021000031003526025 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 969653066 1250 969651816 969651827
    0x705060d0507090b210c0307080c0d0b040906050105030d080405030415110d020705010809030c0607050d1b0801050a091401050f0a271b080103060e07050a030b0103060b0d0302030901 80
    0x20041d4100800c1c1d503074a903480702c1840d80015140d00201403000c4052417400c4444034055420003007855003076081d410704402c05131200c0401040400c01410110302074401c980550001c0c0412500904200a500c065061400c0a0031003401076034000d00c2080b06100e0799070300c10080d040c4170301d422201541c1040e0822605060503207882d00f240d003c0200714001942c08000501002081d00003a800622a0381c1c81c0100241103414001c4c0201c2281c1c00c14000c00005000226030258080c00c1494440d640794134030302e50303440100841314040032030084a000c05039226401c4151141640c03401c0314150b203200d555621410503604c03595101704003003080344010403050401d03035175040e01c00c4d50081070172408a0b25a0101003810624100111000c41491690080b111840c843c07500860032001c8020f40c00724290354098102c0c8010304c401421565183c10869041809001c00740240000a21031307411165242481c0003c04001c1c007060300c04500d071110002803031030320028000702503a1640140d801c00c2d80d40d1006560 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 969654316 1250 969653066 969653071
    0x192402160e1317030406110a020c150c030a0e040e0d0c1b0519090c050403020f01110715020601080f0706080f0907090c0f02280609061803170601020705060d05 70
    0x46509280c0004001110f0301c81c65a0481241100c103034980c582403c004056031400400c036a440c84c420841030010700d03808034a88000e01001d07103840910088400c4a4060752044c14202d03072a03400f0100b40031030f140d9032002411240000032a8142300c0c0418a003003294581380918002800700300b580340e65400180c0c921515041900441c148610041e039240c0110ba0652410b0445d090354803c056030070b2003106140d1003035040207611072428a040074111f42c003282d61440013101641c148044450700000380c4808111f14000ba01449410090090114401940d106803e000b05a901d01891911401c0442d0004030a4225a002e5076564484d0301c40c00202240b201c030142407039640b402155800700c1d449401d03004070b03401d00120b60f50340111041440f100a040480d48884200c41c10302600304450700300002004a2125500480000394490035450400c0c0240421460310040e01c10002c201f800b03164000100d0315407201814000d0007603139200c0c0c004a803101e960380a01503001409204600f0352401a80c070155 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 969655566 1250 969654316 969654331
    0x1d0f030f07202e05030103200d0618020f04021216020f0604031d0d120f03020705120403050d030b1003020d0b03120301050a0f03110f192402160e 64
    0x954150030702c008200b2200786088003400c1c6002c0c808020f031041c9180d1281c1c0c40140750714a850b40c19541155203d042d0711311000910f409a140001003100e440c1e80d00c0030101030056000d80c080000c2225695009268420803900341c1c82298120030040d0942024003c031400d1696494940d0792030b42d00c0d4136125442800e0044410114802c0b810101c01c0e0307450070041c030ba000e02c6c003c2d02d40820081c842c2c02e1300100450010449801003406000540002c0c0aa0138018000c0c511818041440711415000320001c3c007030200c1c044c00324400c2c0c4001d49801c940c003170300620030f0320701031001d031050448101c42c16425111000c3e10290486a41e030150410380d4800d07406885401040107010418100342070009250500e202c1144240e824001300421031454070110030340c000e005030780c82c2c806044d01d544c40d03000100402015207401010b201d00201d6995444d5400640034481c00684c45414580324021048904e000794001016045100c080c442d4040c00000e00015140320329400c140c0c2c00341046d1414070303d15009400c0e071 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 969656816 1250 969655566 969655613
    0xe0604031b060f0b131806021b0307060504030e101d010314070305010f06110703060911060f0c0d0e2101020c0a060b0a091e0c121d0f030f07 62
    0x30001d103450007041c3d0f0f862540840460f01d10310882c100403180c503481182c40950303480e100f15007140489142541c49a00d030400d00050300c5d080f06140000c0d945034100d1241d000350100180b0f41c400c10a0541c0220f004a000b642c41058011346202448000e0b80a840e4000200300c200c20306141034000703100b00310b1884c6818134012485101d07030302200200300410703100301340400e4031803005100754840d08600c0030050503507213804203800510003000ba4a8200c103000190505807522805001d00038151413059600401611a0b0768441c0b5203001c035051758010382424880c0380103071104990b41c58413400700070004c0b0708020300095460316101c80041322136a803003000b420b455409100840d000301c030a001d0380724070f01d010b00c101180c00500c1004020705007409800004c400c52800d4818004203040b01c1c448214004440d200180c1c41310a90410b071404c020ba07500c2c0d412120304144180d5440d01072050300b102d40b10b0003003040310300901c68001c0d095280d000d03445503404c4014007444541c0218006c4e0191802000c1050b060b03 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 969658066 1250 969656816 969656867
    0x3090c04020706140708150420040f1a03161b05070609081005070819180f06050a1b12090c12051204080a0f050c220c030e060403 57
    0x21400741c0c1c0042d203003036410560fa034036800308981c580010a41d001c440e034a8802250315043e480804050f00c2121904d010b2559214402031800c000315003d0a08034020f0b0b0724588440e81c80d41124241490f5010f0003030469510111840216100001c0d01e002d200d0065018035510810071046030056845890420071050740441400410018018603003e0a001d5945005140c02e20103030526014820100204241c90607042241031503011015a4000c094401d041e80001b00002040c00036201101c400701c03c54404105420800c040c000440048520400c000d000f80c0d0f81c1d42219000719800003481603410743c0c0c041c10b20094503100c0d910641444812400000d181d08081e140c0301802c031441d420148010308012080c005009040102840228003d00f20714900342c10110400e032981295003004021801041d589800c110301801880159400940b03200b001e0300c04608100c50080144200604161400c81103584c402e11034001d01c144072501c00020b05050311641c2d0216800882a0001205620702248 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 969659316 1250 969658066 969658069
    0x304080d0c090602121213030c0c080304060e0105160303180b0f060901080a0809060a090824010501021902120307080c030705060105010521190606180f0305070b03090c 74
    0x18905000e000c60b03a072080d6031030821102030316009000e554003d01000a10010889444110b065640f20314881c0c0040e00340841071a0540e014078500e84000d04038025090042000383c0000050022122031b5528a061007a000b0015210f80c42010740741c5100c1c0b4010140c0d0000700c1e002e9000045980c00e00f132410b808048050315040c0c1e0000044d01d01000300da03420b000707211a9251000c5000c1c0504000c0c4041e200b00d000e195200880c0b0700c94528294010302012500c052f0190003031541d00c0043c00b442c1c00307503a000140000b4003008014841030081605e003500e0001304036944000b407010380c40005041240407000543c0c00f086146c06444002d8041e61004220300d40c0042c6081e00030b00104c0c86520021511010a81782060510b401600001d0401000740407908520018072480340c1c290400a802401a4a48030003d00341403542d60b601403040e5041120001d406540141110140048920440e041079140c07561080d03100103600c400781071a030200000b4428500b04400035a0010907040031039580700d20100 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 969660566 1250 969659316 969659321
    0x41401020a0909050f010e13060b0901140301050f1021020d031701120209150f03060c04090f110f03190501030f03030b092412060a02090307290304080d 67
    0xa92480001d0401c0c504120b64045402000c1c0c11100c58081e9803500e40c144000844410402000200c0307107101d08923403c061005c5544402c000e90300c0603008030070641e124507500c1c403203440e45581540250701e00b000150f04114171107038090041f00d8502c00100c44e28a02a40100c480c2d40d08090483c0c90340d40008407000590747c40d2600d01c5002d00c40c0d100c00004400c020308448444a05038014800700d821028002e00507039071f40103050b0340302e07107101081044158803402107802140701594150b09442454240312215818402078800c4500da40402c3c000425102c5504059820711000f44054400510801020400c1000950303030084c03400710380a00c940190044072080e180b00b0b80c000e850740c200f01440d88061503414028114018001d0b1840b10080c00c21606005650144281c685403200301014400350565486000d00d00402c01c8500b11201c1c0e040000400c0e00a60013007001a200748682e5a00058200c95002c0da01c0c2041001c10948180c1032160202d10b10701d40c801442240d468000b000406e40d810047e1 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 969661816 1250 969660566 969660577
    0x70f051207030e0714010c080c10050a02030603010b03011109091b0a0914190512030d021b010e0a0312111b0c1c020a090b0609060d050709120308070804140102 70
    0x2940d0128101e000041c0f400d0824032241c020005201d4841c2d03500c045070340c014021481c529408001e10380e550481e941c40b18140b0420182c00e4a4590400d018007980d55130540146005040440c020003c451601003003500720f606078101500411403c2c050340d4500d00d000f5004560003128050342000c48614006090307401d0380030402c802e021841d005030600084101e80da02c01c081940030341e4807030342c200d82402c00c400c41340e102d900c80e05102d003a0406085101100c00c1c4142c90280c40a5601035403140d250b481c10b100e0880320003468a88642c83d00c103001c0d8041700001031124a590b0940c45000382c942b481030390000640138080011031401c104000d41e03000328160304201c0c82c00a40e444080c0034403a115008120464840c440c103c1200607500d0a41c00260b41c400c0b0901003202e00250000500301c4820005c10642c0c040e4240650703110501084184000e111504203c0c85503482c3e40d200d60303002d034440041c0c04d4815200540980018054400070710098002c0a845030440d000c0d90720222481861310201d420399020 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 969663066 1250 969661816 969661831
    0x15060415031203050a020301181a1801171c1b1e0b0709060215060301060302060301030507090b0402280903062c2b03090b040308220506070f0512 64
    0x1c00c50b500140c264903100f11500b10000700c81c1586154509402c40034240a2031017088400c5a41d24288038420280b4030680c1c25900300a820070628000400344070304401002d21a6909401c81e40c1060151100f001c02c40146250240741c000396420b00600c01160005450802511500c440300509004515000071500003410900c0e01d540038200f40d8507010f106103002805840a100c181402480040e4001c10740944c0d00e4400210f4100e0b5655400002e405040b00d640069048100040088103203d008246802074035500c20090200081e90400d100803441403002a1690172100740f000c0d23030340c1c011070b0046002c0c440c090b2070111041c0d074483c1ca82d20100d4040c070a020040d0000e9042191042c0d04210700c4901504041000c2c0ca03605503151425040c1d400308011800d44a82c20b40da089500500990000c500c65030040c61184680c5482c4c41c1c0582490300564000f00300840500315020610340d1107440c0201d403076002c0f01402c4680c99100c02514140e04202081040c440d0900000a4601c48c1c1222180329941 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 969664316 1250 969663066 969663083
    0x1e03030a20100903020d020d09050d210e09100e010306090809040509030a021b0307060807020a0c150e04021c11120f0601090f0b12060402090d06090c0b040501021506041503 76
    0x2844c900686803801c184c0b0442c00703541201103541907482d001400401240d0f0180e800d40800e800901d42000090191300c200c2034403180101003940e07038542c08184c400704070b40140c401c082c0f980c9500790007000c407903210b111301c89121380e46e40010310004115800450360107214a500905201e4414001000d07140c0c102d511115030f51011841e41d50480d8100720401d00c035000d003c2507074201070001c004207489122a000d040140b105401c0881d4405200300000c1c501d035a0070440c6001c0c25911841001c48102c015070700e07040024202400c020742840c3c1403003229040403000e541540f0160074070b00380354054407429400d10400f420a102241209007408101c51181c80345422000c00f625166001404642c1c0d980c00003070021607614404e11512080078100d4000350b04603051900d07945e41d801e0001f0064480d03000000e0700030103201030303140030001107070400040d44e88904001e01086840c2c03170910801c0d01072171007050f00507071045c0b115402d5107010b11a0150000006000413038604580c0810051071300842d40115021355 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 969665566 1250 969664316 969664331
    0x110409020d3212071112240105010c0201210612050f12070f020f0402120a1b140f0408070b040e090307030822050f010b1e03030a2010 59
    0x2100b88481c221890003807800c040c0c034a903401e60090381c40380d440209030758004000910105100418502003a00c1c4c03001030441c41640300380303070449855000c418105034070b20881c0c50a0001d0050348a0106060f41d03010fa40d001101e007202c0d001119a2008035200110045541a0003040c1d20000d0040a000c0c00043c1e1003416501c4080c600346207000c54060914802d40c10403410030091441c6001124812a00700220303039968021400007800002000540c1c680c0588002485000c902003034031845e1040c000b00c103007007004d521804024404a8401004100055144040b6880c161081d0001e004201d0041c0202c0d41041d4031940420b1402e0b51075041002020f4012400f00921000144c460703600c12180009503041030400d58025148410140600d0820b2503890494440380d4101e084808a03150801d0131a59003070302d41e041190080c800d489149000c2c0000d4983d034034030040105e242c802164000340040d0320f4400d00d05402c45114010140300d40700360702c2001038040b40900402c40d1001465100900080b00c4d03 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 969666816 1250 969665566 969665603
    0x3070c031403010333053126041205030c0d03020f0f07050f010911100203040f050103020903070308070b0604051617090709060308030f0108060c07110409020d 70
    0x6984071030356052107600308018400036450410240d11000e140d00c50b000041000c044a08145030201c901c02404c91802c0308102240181c07202c4589140a0803400c02c0c0c6c04103200c0782c0e11400c54480c180190289440c03c2c401d11038807468100c040001496040068101900c2d040035100c0b40287d1042641c03240e001080550030b1680074062618015151b040c11071038a0301418181076680190040b40002e900040740301c4080c080d081c0a900f02104000d402000000e0b12840e0220f00c112642000c0e0303015043c190b204100e05400001200d06852078100462004c0380b621004501a6106441142d014020080300000061010b8050003442d0312171203403407000c0d1070302000b03110484800510b10348082c00407040d546000754005c0160300e6140c001c10399111041d0b0f45c942140c1e26080c510341c4000007482c0381c00b000005001c00040914054190351401d014140da172200b020b81e5628090700d800b201c0000400c0807400082d5161042141924003a00105200405800090700300d012160107a92824180302c8502c6203 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 969668066 1250 969666816 969666827
    0xa080303040602121006022107080309010f06060302090a1e05030a0308160903112e050405030f010c0206220b01080109030314150d020f0402040605070b060901060507060911030303070c03 82
    0x21107002502c007242450306e50001e503a50998440354894422005000008000039800c07200001d0300021240d41e641414810b1600030038005000701801460144003003034852107802140c0001400a014090305800c21074009071000f41442500d4079410302e40307070015140c5c80500c21140c00c0303400717070f2a0700c100c620788590403020601418103101e04202c40040c3c1840001c0d80756486649203403003500d4205225181d07050215410b4140c4003012013903946032407000c5402ba071050080050b16019001d44007003900c02d0313030601d003a69198441d0b040943c00c094001105150410781e001c40e9680e008489103c03041d11a00c07101e03441502a040280107035100c0d004c141c1816054000e6101c1d100f40700d1200d00c0e40b40351020300d9540045101d081d55109403002c002040955035400f00641806400074002c40d030711984d80102030156442100c00311000c0d90035000250143c600190b030203040359000c1c0c5415203000c0351a50760800420f005801282c10105540840e603098508001035849803680d0703181d00617404140d0602406 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 969669316 1250 969668066 969668071
    0x24080615030109050711122a0a08030406020d0f1b180501050a0306050310090b0112080331080d0e210715051306050105180708060a08030304060212 65
    0x2035480ea41020515003a0500701d03411141024400140d945880c40115181c03101034611110501c03440400c084940b5801e4010921481c0805c1a01c21241032071004910003020594040300d150405407295001c148404021648030380305840040ca04001d0001e00401c0b503038101001c0341c0c2c0317960364280040012560301c0000c220b5401760410303814003104482c1d90f101d000c0b03440c010a8100320000c240551094041d030880c2010380340040130307224450300c2d00d09000003c01200f241620054480000090742104040b007948840740c120103094a1503481049002c0c1180e8900085201c1c820391744008860341c1c907140802d0303007150700c41c1d240503580c0c1a10424030400d441728403101000a801190040d5030885070f401c2180589808100b05540340c20725401c040312481d40400c0348858407400d0070100400400352110002a042c894141044141d0300c9a00740510354242c034906440c0300c071001c8045210240030303600c0d090344001c0042a9a00f81503e907500300d130858105544c03c40c1c1181d000700d0751240c41c500c03c2c41040d5 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 969670566 1250 969669316 969669319
    0xf0902040c02010902030d270803091c0309030b06060f070c030b1f050f0103110d0b030d09060e0405063006090a050a0f0c0e070203070615050105070b0a06240806 71
    0x20213076040750006515a00c5031a28201030042503100d13021119414000f6404108103415507084981d03540c41d0b1151650b00c83c058081c032461400040082e00d0000301e8501c920f0035010798481040a0030360391144610780010b05234580c8600140a0200044a49001020790034411141402032030702d1454a5001e4100c06001b842011320750010701e03110071525940c000d04860044601a90070010640140e0040c003c00b0250341841400140f4071038001240e400581c02d0420540c00c0707503800c080410742218038107054012003000a0307900a0031810391500e90050b40d0081001030002540d07204810000301c00c40040140400010349081c1c401a400000340502c40e440000c000c05414205e00d680d0342c00b5202c262001000305000000c038a11024440b0b5141d19101828401d220301000d400e1045000e592a009903004a41607400e203100d412000700c11301c680e082280c4060b150a0300b840c2c256500d102203072900400143d05203036100000107820310303194020b88856200b2906218031080c1c0c0180280344050041c8001e = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 969671816 1250 969670566 969670571
    0x7080c0f011d0d0806040b09010e0f13120e040609060906061e05071410090c0302091e0115051204110907020c03030a082d0709300807060f0902040c0201 67
    0x200403410040f40301529200e5510f003003610b0390768413000280240007840103c2c0d0071030700050000c0344543c41c130103405014200c00802c21101d969400c803030030142c6410350070080c10110420200c0c030005026012084440800400104041c0e17120502e28080342c03506d80c4900764060721030008003c526088080811802c0500c64007111110500d02c024050703119076500104071040700311080a400030180451384041140700350612680480d41840020b1400d20300082c1e109119060115036001c80c20540015000344001038020a83e180051036080c2d2514030030090107210080149a81819070150710310300c40e0307108a4640b40d410028006012503c13000401c070b40203640c03042c03101540d02e640001c1640c000039181d1a00e1010307035440010181c00102140203981e0741d0041c1c2d01610100001c080200340c403403199644e070510850b40d98004450b54096a0301d034540c405070010b50f071840413000041c100444d5405030240c946000140c2d90741c241100c3c0004d032017000e0310350b990451108500e004c0c01034540b020040d03c0203 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 969673066 1250 969671816 969671861
    0x5010e030c09062407061b020616141324050a1403060d0501050a0b0103180b1303031401080109021527130c08010515120a0e0307080c0f01 61
    0x205200300342c042d051038070441c504d48000984070b500c0d0f1400c01000c0d0360000c2c00e980b1122280b8010380a80640070303042510028035424800c0e041e10000e1094840d07407003152400c1141c0340c802000d4aa44c014107108240c0310030708100c2134803143c0541d441000102507001d0000c1c0e2110700b5848000c0d9420191560804002041055200c203940c02242c1030440c40e00003640c190350342c036000002005807011241c003d000c0c0d406c2804000782d402d9150300c04800d90400780c900b40208001c0f00556411524108030003444002e4280101e0a85059100901c0e2001c0c400d0800090710f51f41c0c80c0c40c4808a04090303100240036074441540350110300300280c5907030f1018030324554241801e14a050864070561840604402c010410726010380c40d0755501400a0855003403041003001d0365480704000e01800090240902801e43c44200d4908150700400322090500e000c0603041242e25120740300b0025000000712081c1602c018072130000480c504000918103072140c0ca001700f002c25a80c0220f80d007956031115405161230004000e = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 969674316 1250 969673066 969673069
    0x1d070f080f0d05160c030602090405010f05030a080310051809010c02150109090317070512150f09091c0906020d030c0f030213170105040201120b1804022805010e030c 73
    0x1070100080b101403d0560722076804200d085041c0c2850000908601c001d001c00209100040d40182090b00050718240626030f00c8201010044549100c1c464043c0e010b6035655011420500c05541c02a030b00c0d2040d504a03a503110001418203403040c00000701a945501806101002445980440e808a00290100c1020080e4954102005109801549031246d4210f0109485a142491064007005400d00c981c01d01c0040140640c104600b604444210301c0e001c156064200c010589034014001c3c109001d4003152018000c0500b40070780010194800d02052049031006000802e001e034a180c1c1e41c3e11643c0d8903042000785418114880f01041c5464018103810365a0300803113265261035607003005a5101341204094000002c0c2e58007a2940d8140155a44650001908202d00581c002da039000c0303024991240d00b0382240c0213503100e40d80c00b203848100e0f14100b8804075540780d8030600007400742e9803030805041e100c480d48400c00340d4090310407400300f402c0c0003540c1c00c59228102803200354002c000700a400c50 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 969675566 1250 969674316 969674323
    0x1031205030a02070605010b0408070b0c061b040b0d0b18070c060c050903030f0403030329130b090403020610080a02091530060a0506221d070f080f 65
    0x60a0100000000014003007840c0307804481100e0360000e0304029039a502c0441110a82181c080c02c5c0741c50041c171400255100814007902c00303c24030400682600d40390b04070042e503030b40401540d0184001782400300003600c11195028081190184102140b2420081c003000402d0b40c0c410720941400c624001440400c03580280030701e101c66849800007035110708901c0152064012582c0d52503151000103000407140040c0740141040302d109480074818203060321001c1071325175502c04854505100340040106545040c21105122006030700c00041c07000e9000c008196441001c035004d0340541c0c808420310801001407400a0020302e0043c0252000c0e10441d40065018000a44000f030f10b003114085501c800e527507100304212819640200d04080c070915810801e6480d0b0011056001400b0701000100b007406580522482142c00405542403200071840b103003503212401403604d00050b682d00c03504024966849500c00c0b00703e04507008001c02403138000e0740220030b031b0b568100d40026000210311122505001 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 969676816 1250 969675566 969675593
    0x80c1c0f02120309040903051207030b010c2d0305090315060d020112060e010602070317030c09060a09030b0118110703080105120f1b09060a0506090d0206092e080103 73
    0x110350078030b81d1507116910b5070301c0d44c040c007000550301c685003a00540030190030000400d020b0f41c81201d451172641e25002e0a400316039240030a41d02080c070040170000080d010240341d00b08540d41104421000d25000101080320380c0d104003c40c0440c60000701c04c03501d803600304180c000ca0003240420356024035000020a040c0c0592450003030600203100c460140400300358004002410603840004c881d50ba40c0c0c44025940d5840303100a40703000c5803050003c0c5204000d2000c4911a9824810281c41d0165440c1071190760390280001c8010880b41c4400800000c810000c698028010001c91003501561681454202c40340d00c208d0040c8030301c08001d0b5500180d0881030303c41c11500100c8108008641d014000d50404158031914440c80c0904039502d234044549003280108a0707010b03110300c0c1e410307034618040c80502c000c540601d641c40001440110b64a241ca00d001009031480581158200750044d00442c20003402b03101c084003109480010640d00700119502c508101884d86046401346d407545d01d9400940b802c9 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 969678066 1250 969676816 969676819
    0x110403050c04110a0e060c031621050301051315032102030301031106031b070f0c050f090a05060312120f10120204050705270307291b07080c1c0f02 65
    0x8140d984800c1b5641d41080d201904ca0000c140d03540c0380c050001e480c2040c1d50303807c01120750001c050503640400003c2d114045040d80e00b41c50701d6107142d00708820804003498145500c03030410f441d40710072280c0e42c0d91015400000d41c0700d100180f004c80100d000308894800f1501d4454110341c01403004001046041d288890b400e0002d54490790f69803a0a48131094050134000c01290011000440d0000c201880e5180c440e840c1c090b41c503404440c5d4844080104802c4118011a880407c0c04041042d1030356031b17840f65412801c01001c1303452100142640e082030fa0400002454a1401c80007080382030f0b0510f10940c2d90200ca500744945034a414520104100c05e4400400785c052503550001440c4503010700c040321460144c05424044200500070384801810304045001c0c064050428001981450481e0107103000119541c81e0b200f070481c80071200300eaa0044010340b40740d07410740442406406003d101c090045c145541c0a441c5081c40380c010b2000002e00c03820302e4000f480b102850384005c144105204901d4aa0 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 969679316 1250 969678066 969678077
    0x403111207060f0e0a0c0f06030501080d0f0216080709050903030403120911130902010e060f3708010f1202011b060603060e070305010b0307030c05090c0c01110403050c04110a 77
    0x16030f039a00500421440008080d24400c400035079090080c0640c0d41000c407001d00c44108502a240d08040b000c0d00c80c20310903040c3c20b5000740d1200b0700460282c141c08501041b9441190300c104035050480865450740c2c4d12a00003030700310030424810301c865070144a0780455008015031a508184d540200480304000600c886156241c3d41d550400c4a92201448601402030041d500a90214602401000d5984042b40402d10235000c0e00302608180041e00c590205500d08035007071600500120b092805a5441a44024159140d82103e66079400bc005018612a95041050740c1486146005411341c0d070044000c0011500d040c600603a805494010320858100b026455041103107016009410903400051119050044040d904031001074403404880c0100001d21500078100289070f1220307454000035012500142084c0301d00c1c00c0c1011181c3d00302c65005003a43c44c10b000381c4111030131620fa96000c2410008001010401d0080070001d46070300d107100f114104445c403201412070a951040481c048140314 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 969680566 1250 969679316 969679331
    0xf0c030213080f0a0b0702030c0607030c0e0a06051605011404081306050f07030e01050c0d08060a060305090d05070201020a2f22050915090d031410140a05030f06040311120706 77
    0x43c802d00503101e000003100b00321001c4bc1401040900035240000d0325000240400c05c84141c0c1d8034162103900210340703054450301c0c503080014403155241403038400c055a03030b5900d03101d0310461064140c54061045020302c0e521342d00c9402c5442080d80051103a442201000018098844900c1d0214121164650706081890154810100695950140300c504c403129000e0401031f00e85181c2c00c021001c0c4101001c6511500054035150143c0444001360b0302032005900007040d1b000e07030f140510000c0c00014014011240b081144d99500d40300d55510910b070b0042134071100302402031105101c02d46940114110f4446e5400c0c0c0381e41345d0355203000400c0c0402400722911075011580c05e000500c1243c0c2003280038003e81115207800e207611030b0703144051046000082e1812038220a0843da02c2c0207540211031030568035400b680380003c00c20548042030046517010031061400100d81e5010042d0290b1194100702401061516080107000c40100d004140540d0300300c0e03030100701c1788100c000488699a9020200040a8 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 969681816 1250 969680566 969680581
    0xa081005040c120c0905070f02100b0d0b04060606030b120a060c0e0d0606050f0105090307060302130b0705101a031e0a081c0605040216030e040f0c030213080f0a0b 72
    0x1c15998403c00c580d600c40740d41d034002d210305020340e041035880301101400766498904040f641d02e00c000450750010707000041a082d801c101074002010249000700340d04c071521000e49511007100c0341610101d84090381d581d0100811501b50161110b092001c6681208010100c80310680b54045090001c100c1942c9041d0601c1044c000c0314003102112001e441805d01c2c211520700300c001040940a200d1003600000c070a194a580f2460403185164000350181860030702d05101030b00a07400c003030a004500c03020440c0200b5480c01c020050f2040c0c500400081c0714100c00d2071280e034200c507030a6000b02c9100304000300500311074a00058410110b110184c1c114000030640206c1c0d401c1c40007045c0010f042750300c001a02604a506d290785103c45c215401002c01640765284104001c07485443da90190290024100501090084c09040c2e0300e107a000d4230104a01168003000000c580380d20a0000c082507020480542c0348805081c064042e04a0030014000201c90910580c0e036801111402008602e4007c000346c0300 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 969683066 1250 969681816 969681833
    0x4060e1201110315120303040c26030f0304030f080402150a020f010204080a1208011809020102031209061e040c15020f0d02100e0c130c030b090a06080c0a08100504 72
    0x1910b440c1445612804c1c802403409a600a00d04858420340d40324510b00d01d020004412280141d600280002c0c159180c00c41648502030241500750b4040303c940d1480b620311b03a040c4000c0c520100d849845650f03a282514001c0d00303200022441030700300204001040b0058031206411203800e01c030480a185c075030400c40c1003203103890fa24524000043d40045000039500d500040c002140e18418016080d00280ea03800480d840b00c0709104010030b003c10341400e01009403041d40003040f65401072041c1c907e0200c03c00403008c02100e058400c0792503580003004118403000c40d4010440540f07a0b282d9400010f0402e0f8460303442c800c403a0301500301d220600c4170280015034020009080b1464440741951040b07889020701035103810506400e603280605280a10003000d00104458503420703001000101c0c526800242c500091070210a40018595a00085803659455054040c0308a030000c0c000f0030900c1c2001d000504141045442c24014103514205003c1d5000108002e130700c0007090b410002c0c86a0355402c02220 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 969684316 1250 969683066 969683081
    0x1b0503030a060e0a09330e030901020d080f0105010309110d03110607030e03030402040b0a050901091a01030b01020616023c01050f07081f03050f060f0c120c0d0e0f01060b04060e1201 80
    0x10306031034030070881c7c05404007001130031400e08240c080c0ea10300300903c0002d4a260b20105c802814424402006000c41d600940c01031403801d0040d1004480000d03a800030400700d06e4001c5003600401c030200d15980da4038108116499001140307181c244040829140145d03034a000c06400244182c2d1a03a40f40202a101c07c0081801440014040300c199607591818200415201d06400c40c2801c59119040c180c0d4001e0298999601d01030380280120f64901050344140000410b102c011030003500c550020b082c21a15489408502c4544418252140c0c507111300419800003d184149904100c2000004001d101c51550300c0300c0c0508044081c1c0d5521109010b0503100ca00c02903d1581c1540004018440c0014401d5422009001200c240b41c881c4a014034440004070f607007181c1040d0401441e5031020607040c1c0d254011115032070041c10100035403038907010b440ca4440885507950101600a0401d034090207042c00a201c01e041081c135040c2000f40003003600f030102c03825a0003666004060703901400309500241 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 969685566 1250 969684316 969684413
    0x3040503070306051321120b0d120201090b1005090105092707030b0f0103110306090622051c090e0601021914070b180319031b0503030a060e0a09 64
    0x10b514030701b4a0840d0300c0303240d4038640040005924911340d0302e0044a9114401180000a21441c00c20401d03036224014240f6041c00102155201c5026400107403801a00500502555405000c541d0414042c001146070503481107208006440500099024071664801400d0880d42520103c0c010b0070134540c40d250041c1e0000741010351000130483e409600a0003581680e110343d14844040c4030040800d9078915040e00e41080703640008010606c100c030801100402d00d0417030b216000140955891746410f0800c0c44003400340314000031103541c83c01944404107a0252400008102083c106840001c0d0348143c80198046404443e11800060090f8442c9881c440b4800030211001070391202d0450076260802070b003880c0b0303c200c18503441d68285000b2400c00211840780c1c4803035080d0707130441c0c40440b01181030189846c61060001c0032500824400c1c40254403d080c0f0305000b0808a03d082d09211540d5030060a0300c0c5028500a04000004c1c80c03000d124211000071165810305125644808640d0f11900340d00c0e1 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 969686816 1250 969685566 969685583
    0xf04060503180c09190902030102040902070308060d050a0b040303060e09010b0f01230f040e070509030607030615030c0203040b1305040e030a082a030702061503030405030703060513 80
    0x62003540000110300c03601011001a0701814400c5103a40d58007181e01c0216881001440010140d891007482c1c1410101804000300309160380c3e401003800c80e0b109030001084140c000800c0410300d81c1004a1942041c0f041c1d8803014440d515880d40390f1143c81180005052a000d034022500345442600300b080900050304444c88541820300ba001c1c002c0c0318225041d80a0700702d04541046c0d56002d03010750400c1845040018031004c48500520f91254031800b2045901c9105100120706407081c54200c1e8401c40507a01e0300c1d551020604201450802e004140da0708041c10580103100c000c058081c1c02da94081542008a00c104031018207030300714011b94000b41651800031940c4550310042660b003508a5100307407000c10003907150b07505168480c4078051070640030030f0b000700214800c290368039a9100b180610102e04542044800c90b075645a50065a2480040c0c0c042000e000d1614010f00c2d000ba001002240194603040ca000b0220752902414480985078035610400180d9801001c800b40c201c5a500c596034 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 969688066 1250 969686816 969686819
    0xa14041d0a0b0c031012050a0606153009210203070204110406230f0d0e1009050c0f281d070c11030a3507020f010c03050f04 55
    0x14503a440c421140241d8040c00c6550106440720490000c1341e000f8180031050302c2d405410666a210103045070042190284074080071500801c50600c42d03007000c2d10f400307594905001c1c14640010030720303c0c24041c01403c0c90b40d00c42003040015060700f40e14246030840307140400e50003281d041080300c0c03210341c0070100c44001d008014011615070200c000c0000c079108031800c200c55104084001124080c901440700402c1d80d0851b41c50600c800a071010520012044000b46000040c0380086215041180259409604d80c41e801c81c102c0e40c05e1181c10025180d44900300284c100720340703179155500d916004084c01506907560303c4885841d19020820070002904d14015241c40380b603402ca102c070f4680d06c2004061141c0404004444860301c0c08180584d15682d505800c4100c40c2c5c40f000150806465400e5141c85031804500c0040c0081502082c00e03002411900781c012a040110311004c109a10340c0414114100040401a6915411650003810038a0704000e452998a0261070324411180105000350002c00c0 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 969689316 1250 969688066 969688121
    0x10c0201031e1e0c0509091b0d020f070221060619050a08150610020d0815030a110405060f0603180c06070c140913061e060e01080c0603060a1404 64
    0xf07255450160400e0401c00c60488840803102401aa2421a44007003801701080c0030351020507507011812104030b8024902458248200120703440741c070b01130b01d206502003000c03030561610013081c5012804442a410011642643c4607450740001400036104080c190940002c10420204010140c00301814a0102548409500d60b0383c44110419a02640102000034500c1c02c20071200802030303030f80750000c000c00c4091040a40d1081001000b1080e050500301261501c0d503420405203071164007070101a848015190300380825220009c180b14081d04a03103110300759130785444045a5001c5002c03002c0c050305905425030b131400d00008070f05450b400f03500803482400f8001a00e58100c204c0d0000c06980102c548a20180700c14034404854044040107034081080200d151500040c10741c1402d0342d0611182c1c01105009400ca440d1504400c0d00c00e40e01c0070041c0640d58003005000890201220301c00e08602c1c150303001910304106070145030081c501d02c02e075140751910741d9004949550581142405010381c00c2c0b4 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 969690566 1250 969689316 969689351
    0xa05040302061e06130f380117060310110904051830040e09010c020712080d0e060910110c1e01020708120702010513030f0f1205040b060111010b010c0201031e 70
    0xc800034245094078030b041c040c1c49007078505201007007c181c4032034400c4500390450307107c0c0c00d03002480c480e090700482d504200c03444000d01c14441054000da02237501d860b28442844110740008002e1003103002a01ba40030102140050749100310b000d0000c0c08998040f5010401048a80c03e800d21850444080f40c0407452807205c007940e41c0b0850915000304445002440d08903512026485a030b121490714021a801040b440c02c024641a000c4002c0440c0605249000c0c41c584078048130f44425907080440d4010410010b8024204400f50700c00c00c003400c1890b58407082e0740f80c0005c030403105480764010141c4103c00100390169401343d5044207a00307031901c4903c14401030b410403c48020006504c1c2000041c14503100d92038800004c0d070191785402e06c60319800c1043da0f800c664242c052060015100c105d45040256001c0c1c50320441c030441d07015a103414540001b506462942030103a003180d05101780c0c2c4026992011040e20038a409180200e0801441e9400c444c4130041000d012038a0b0b414000c0040d01d004440 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 969691816 1250 969690566 969690611
    0x210302011d03191d060702030118051f060506090d050f0f010914064804061815350103120302040b040513140a05040302061e06130f 58
    0x1200040f020028000080b40c10003d14100e0800c6038446108143c01814004060042c0741e1014000098050210348204503030402c071041240d180d80100080011040b204403a03407103030001c000d400c0c8004e80c103010009007140600e9a1260180380540300c40810700c03004010f41901d080b080e105644403000b0003000e0901914104d80241e400080002404440c40c0d80020780070b110784082c48070060042070031000c54801019104500d4000e0302100386040a80282c22004034192100c5010507549601d030040241c612104100d07100c210b5184100100b1000c690030b000703070701e40000900c0c1030380c0c0400701b4101a241c807150104500d441050740d10310340c03a80403030041c1401c1d05030390003030f2440c10101640340c0040b41a0710407405400c200710003d0008000500f0300000c3e01a030150905408550710404141c1d00040600c00c4a00c00c44081d203500c180f1080c59014001c0a82103c0849411441e07009500481d0a8600015000d00d000c0d014401c0001d8841c105a44080d540300b100d07400901c5081101c1c00b000b101c2c2c00f182c = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 969693066 1250 969691816 969691837
    0x2120118060b040506030414010609020f0c0d0203120703090c12030f03050627100308031f051c0f020315070e280303180819060f06210302011d03 64
    0x400e403020516030402c0007900e0494030003c0039545159103d9540d04011013614000c56540d40d00c0d04030110703020460340007420607840b080290948a5251a413207614107550000e5041c259002081100d81c0d1101101003240d02015a05011911a029140070042100c0aa100c40320304000c1e400d061040650081441c40c1a90080c0e81c2403059448030010000c0c0b40d5082d5101c440c505182540c007182454400b02034660004041030010a160313070301c1d180c00f1000d503c21070320203038100d48014044140740e0254400c18040e00c0c040d683c0540400381d40d00010a0030200382d0010302154003038039180046541c10443ca2803507082c0243e0703070310290601200180040c040f070f0311050b104000c81d031145451080241c0ca180220422421031108a0785143c8064642401895003070017860040f21010444600800000400d80c80810088031000d0b20383c18010116082c0c0b21a0421460401504011360f0100140c100750055910444490b806101e2a05031f004100b0303e40089103251800c2d082800c00c51012001c0d182c43c412 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 969694316 1250 969693066 969693071
    0x30c081c0513110301060602031e120a020418152303010c030c14030f011401180605070c120b0a0c030f1a030c0604080303070f030e190312111c02120118 67
    0x700343d01010300b03840312401980016401801108a03c4030450b440e603560031801241c9614001b010381e0304054403481201c3c0c0100031a0001010841c0300c600b0a409811030621441c2005200c195902042410056108600038181c031a0452100d030511103005441c40080100200842140385d2009406410f00480c80c5010820000d40d1501010200c41124131030402a400e030540750b1f0074402c5030300f1802400c070a010304202c404155103903451024024a00900200e44030141c44034140d142540c413042032504648000b022100e610000110309088091300007100c01c10100384460401411801000074103200307100d00742085101e185c613580d117400003400c11030160251927419440d0384c1800079603c40c074801c40e100756000304001900c640c4120302e40011160b0394600400c1d103416041c04645405850b50041c14052200d0500004241e00444840320b00000d8120601100d2900202002076000b032052100190540f848408851a9580d0442d20781d00411001000b042d6103d003402c09140800e1140001445e2 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 969695566 1250 969694316 969694343
    0x51602060904230907050609090403090b03010806090d0507030c02040b0f040603082104150903020a0f05010510091b052101030c1a03040b0129180a12030c081c0513 72
    0x403005c20140c040d10341c00340c81c0354600083d82c014000541030040059003001801c800100c0c4800341d0b08010350083c0010381c000c015504001c06443c0c1010000700300d22048c06010021200040c0d00819180c41042d011039002a800b00f00c2d101084a840001c01096031013850040702204024141014202076240142e00341c82c010b81001d4504206c0f101941c014025401015070401c00759070540040a4562080c4180c8901e03080c01e9a42150740080ca10003250a83d45600401264400c044010801030110700300900007101d0042c2000c2d03102034114400713030402000185c48950076260400301040c60400b9540c403002c81d80d4034280130040c0845406141c40001102100083c1c1c8800d240540e80920780185180011f40d291030000008485a0079664049420f0030414000c0d00080340041c001200001650060800020042055141041d0030201c081c90700180302001190f8040c901d103035119445030056544100d020545c2510403074016031070000c0c500746070070072921442600081e48800e219012244544 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 969696816 1250 969695566 969695581
    0x91506021203060d0807031727060403141602030708060f0112020603010501030b01110607030501060f0c1203020307140a0e011101140c03130f11031c05160206090423 73
    0x70b01c003c1e500070307610456500c58400030680600080160703511900340f80307081541804602c2c02c4c407041140e60251941c6030802c1c0c0680c5c091104101c14607221004081c003014901503030b000e0710007184c00312001d002400100b5002034450301d51040c2400190000c0c01c949400d40d88141403607549000710380c0801081403550002420045503c002d26176a0341c018460360940c0e00f008011002851400640c1d41089030321410120b482905002ca80e00481042d5000b040641c107021010304844480d9440d08100041d184500c1d01103004410386400c003801c1d81c500545c0e6a1a407440c03c40b01c003c104e004642c0c4082e8005076501541d174200c29285c4480c0001c0e00c50f01550490f1015031070032201c049484007070700003400780050029480f90700115401100030600d26000d4020b40c07510040200c20301800c543e200e00c50394800c0d08510302004070800e1554003400d031108800e000280101280a1140c204948130200c1140030215540d48080d90703007078040034200300b2005d010000903a01d0090450301c24011740d03a0b010003141f001d = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 969698066 1250 969696816 969696853
    0x70215221401180302100b010c0b2712030103330218060403030c02010c060204081e1501080d0f0215130312060b0f070606030501020324090709180609150602 69
    0x403e03010340240444501b401800d1000d404402d903280c1c10003802e03641400006800354002400743c0d5103504044120300d4080e41c04c0b140322a00000e050a954003805180c007071800d088080700d055030b510055a00c0486966a10658040c0da0342030b00e2000c21808180c4020b00c428654060120394042c80f85040075034808506005280c0b00364007000c1c000940386000300d80954012109200304c140704100062030b06075214840d900f0078011403055019104c0030391249001080401151941843c981e400364400e525021a142d42e8007003d40555050140c00d107400e20f14140240550071240c038080c1d103080035514104001154a603400081100031030071110003551a10040d106600a49890342007041c90038142690944890f007081130112111a02d41d1030102c00500280041d501860503401c4451401c007c0384440f1803a40700b03145085004000410411800c160721240c2d030022100b00d070000e4031007514801e17200c2014041035003120081a04018070850207062541c00f05080350519070aa03504c006800004440d03 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 969699316 1250 969698066 969698111
    0xb090c090601050a0806221a04110403020904111026090d030218060408031b031207050903161e23011803060504030323070215221401 59
    0xc0050046100060003038545c0764100301d000300103282080c4520742c21141d4460070360070401c0c41e91300c60403808103450715040399210303d8008a80c03d00c1403c0320320512112900480c072010303216200400207d41130282403402b1800c80c00c3e0240030804035184150010b480f078802c61112040861007000c0d0300190344030554251b07004600420180030301a2516400318040c0d08902d0480400f400c404491000e1580c540d002800203050180107142c99040810b2082c590054501c904445074208000e03100c0140c00e401d11166014080703007001500c404543d40803a2400000c40412107100c2d000d88000308005aa10032000000c81540c64000c0c240c9031601d0811099950140c041d42c00c0c0751510031004500c0d805210b15403412070040340d25001d515603945810040c3c031019039041d004a0340d41c4c500e0b00c007880b50900450102d101408880056410540d03402580c031001c5265120000c0000400301e500005854101d5214240420304640380c003d00b0306240319030b1414000803898640c80c0c90340c22a24000c82d08903194 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 969700566 1250 969699316 969699319
    0x12060e01051c12201c0305060a0e043306170c01020604081b061320030c130f0f1a0a0b0d023702010507020c0d0615050306040b090c0906 60
    0x8072036180b1043e01380c51a020188600d500d00368000e008994644040040c2c582d1104011380d05032103029130801c0541110f4005d040a40640d0558105110030b0882040031500075034005c40502e030100100700060250018440d182c0c8245e90082700c0540701c46c0668100401b82d40e241c5200f50700c1c00040210b0b181d41c4880550000f80960803100009000c1a46003001c0c1c0f104200f8101c600a070240b075041801d00f400760845d03132200d40f0b01a5100c0f12041c01240340c19130a03441c00c2ca4041e4001c001c00c10780000d40c0da41306903801a2007803c0100c0b071000104c5130703070300410120b140c10103061003010840d02c200009814500f05580003010400034141c854030708101e80d00203ca010381d26447c5418a2007282d200a58409104030200300c41081d04280d40450b0340a181c10721509a120f156200321110100a003520300180c01700302154412100002141d4610351003078803160b4440000100700080c1c003241100c40c552540b15a80c10b010b244100818040c00440d0309100d03c6005064510181e030f05030030130118a800340e0380725 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 969701816 1250 969700566 969700583
    0xf0c18060d140f0601031b120207080a170c130905062229010503130302070e1003330f09121e050a0804020f010e030a0302030d1107020d06050712060e01051c 69
    0x1060060184e088c50020340c01c1001d016142c501191685c0c1000c0d409404034000081c030340d00e911061310076181c0c111600410308900f1035143c00c20082c0052500c140300e00aa140c002d541d0000b003001c540d07d100000280b0114001c0185901080d0300b04140146400c2d580030030700b03890103440300216076100c100c100c80c01181615200d04607183c0d01041407501c000e07890b04034294401d00c100490390032038501c0900d10070700030303005004d040e54103500d40740c440601581443d0403890071629240403003040c440c1c182c00e0242e050840010380c60158100b8080500401e8102a20505d90056071b2075030345070f2048400001c083c8542c0d5030800880c0110003107600340320306010f110000c1c070008003143c0103191121040030131075030501d07007203480450180000e07041c2044110220056030001400e910700c402580906140c006400b0f420030f0400d951a0040740c3c1c121161040181810740e13400010f403c540c0602d19000ca600040c00702000500e49544480aa5241c2806828440d818084100a0301c0800030103404900d075100210 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 969703066 1250 969701816 969701861
    0xd0e1e07050f150d0903262d0412091d010f060206010807092c0d081303140c03120408042108120a0e0d0201020409050f0c18060d140f060103 62
    0x1c04000c001c2c2c81000c03403c10003100e0210481801010400542c020f16211030074184c10207603c584481207050620928400801d0248d0fa0340b0280442d03081c1d445a001804400c0004a45004132480d0310b01d50400704001d1074420030100700c2c510b22001d1a041c1c0e2002703040c40702c0703490302c4400c246d80c1c60100344501816070f40095018480c034041341e04124100d900100c0c0754960562040c512400300000c3d0300031407005a000b45034465005521060841c1c2108940659030010001524020601d040c50703000303501002400241560354000c1042110107820f040c40700403880d13090515180619a120f8030400b4542c002d0451071400030464254031480341c0c2e40c80018240b0b024482020032100180082c2a0240c1030381c1c0d060351002e200d0060250000110141d070006070f5403800c0844030400c40704090207a02030b8401c200208030031065020200d0790703080000d901d10301607203c45200241e0244101507454040c83d08110521050440354405540516000c107440a100d0741c1e504011021500000d68040483c60041107 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 969704316 1250 969703066 969703087
    0x1903081f1a13050406140103110c120708160b090715200c090a0f2f1303020a0603090501050f07050406030b03030405090c0301170109080d0e1e07050f15 67
    0x408140405482d20801282d0380c42c0068110b0780c00b680704440070b24401190400541e07240c8509200341d00030607240c40c10611001881c075500c10603807120000a200c00500e100c14802e4003400c6e1448401d108202c191000c9480c03510201d01d80c001d6414011511803c50701058400e20b411f00010241d4442d907942c0c10b000c44415801240460101d03a0b0442405045009085522040d0f0041c0c0300300b004040c041152030a05208078203c500350420481d450a1116480707682203825524038000c101d065181c0f0f5240c0c0e41c0c89108480620407640002e500110042002800c01d4064000c2c40205015400810890f80c0d4403085d06100c02088940c80c0000c0c01c100001e0205500903800248a408080c0850b4142501c0f0004188480f906440c4045c4a0340f01100400480c0e02c007080b0310400c494030390f000344005c0710305640700000d80c0030f41010600750a880e4400450310708400c100350121940340001100d2591811000180c45000d5030080d58055003128040035003a00740443c20700402c00280701c2c0725150400c0d455 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 969705566 1250 969704316 969704369
    0x9070e06060a050d0c0807120506030309010302071a1302130c0804030809160b041e270f090c08060105012c01020a15020c071a18031903081f 62
    0x81d502c4080c04020300103030b8100e44507032003104c3c200d10998448403564200600c0c0a001d1a0009500824003401c1c901046010b46012094035901c610a00340940c4030440c916200c00112a14000495440300c5001005041114483c004089a00903100807070b42d0620415400b003a111841d180c04040350700d42e004980041d100d29455a80b204c4181c0984401c228000c00c07000c99112158000740c00218042802d10424440b101c42654442c44030b2400483c1e41c3c41c103031040ca80001e00354103055103500c4030b4400711003415241c1c2154030385060421042200d904a8549085402c445000d448100d102e9a000442d495000300380840e000070050040000e2100342c1c900c1c004580c00750504160440c06090004d20000d8410107107504000080c080140e200c088080c01e20b4503250043c0c0c049104c2d9901c1403503102c2c403100d10350202c5048941819049050340a540301013031400000c544c185440d2004500e08c0b10515911400643c05603059980b4140400c40468170300c16424440d028203440714800d080014400913280 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 969706816 1250 969705566 969705577
    0x1404030c034104120c030204140f070e061306170121300c0b06060a09060e0f1c0203070806070f0f140307080a200d0216050a0501021209070e0606 64
    0x20b91036031905454040c0c0382400040113508552100255500b8811460580a600140b01021100d2038941c548420304084514001d4602c1003031110701d0b000c0708603584031070b402c40d142d5509464184020741c0d40d9802c010401d90000d07000c03100030b0a10400208903a1004d010340104c04000d4028151510b000d034803400d281609220000c0e60145c000740300340700721406c030030514104d82d01692115460251607040078a10704000402091003620f04000c40f101407504050f41e507007074070940c0c40d0041901d6262404600b07420303a4140903070b6011400240000b00c03038400d1100002e0282c0701786d05440e46070b0368912005507122426180040400c908042c0181d6207480b41114041354100391401300039201300c0d0100d01545030310036148200041c82e1042004101039003030040040c9028540010b01c1c4803100c00f506d80303400d40100820241d12940004000d281002d0a03800070b9009900403007134450068032450300c40d000350f200e00004462000b480002400541000c201c0c60111040500300040b03569400301005100d5029 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 969708066 1250 969706816 969706937
    0x601120b0a080607080f060307030b0403170a1506030231031709090708160302030702030c1005160915050f0706020c0115050409050c0d061404030c03 66
    0x3603640c100e1140d900c4815600082240001400c9507060400005050340402016007403685a4881402226100016990100c0e500301c0c5e1202c2c0c8545491070200c650200c091034408402c00c1c1041400f00e0314030302d81d01191200d40861800d881c0c0c155911415000d81c00382018080320f8000558016942d2980404440f47d580712070007141c0300309a101e54415060f0a11040800000840440c041100303041900d0f0844c3c0000c80c5062020300c03407904c40301c0465850b00101045003055004008030341c0c1a0700810507030320150003c41c00d41e45c80351031004480d00208800c650003100b03048615043e51805000300307814001e64100c00e00029100e5085d01c0c098940303074051090461482c0042001d40f000c02d4283c4041c089240500c000401c0c03100203031080e05003091540c2c04c55071085250405100010f40006860180c09909642862848400d400c212008010740042072a280348010100710803da0721010030461244240c50b6006880440d40d60006103000b0300e07650707823815842c003203201044032146014040400388 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 969709316 1250 969708066 969708071
    0xf111e1c020307150e0a170c3010110a090b0f07080d0e010f1a090903041a040f0f030f030e0a08030c0106030b0c0a0906050c0f0d0509040c02010c08060112 68
    0x90710032011070030ba01c2e03041801d00020301c021100402854006d405030005d104550840022034080504a6250ba030038108251148070503200f5012001c2c04c0d0301c0700001007a03100041100d086405c0b42000d4907a01503c0c8074541051910072502e03005c501c0c26003034815a000c0341e42c4000e03041e4104034032052598010084d050707840e841484008002458140100720141401c1c4000c0f0fa00c100244103603007501c4210b4280300c0f0300d40c102401c09071803c900c02080403185400700d5041c0c031641c4541c1c10785800c600c223030b801003011100e028002203601e020150081c001c4803c0c0c0015520203a90310701a0800b28551800000c0c6000307425040b075404644200d0101c60903181c01001405090b42e9481d1940c85c60388143c00034076107a511050300300144180cee10007003a0b00140c0d60500c0d901c0c1c43c00018008060001034001e02c400c2c4000403c0550326503204018201c00850040100d078030185401c0e002622030340120b8040c40c8603d003001104e26000d0f2040c0280002e500d182c0e11010129200c01d03005494011283c1d03030000c3c4099 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 969710566 1250 969709316 969709319
    0xe030319061a0a0806010801031713050d06020c060115140f19091802031303030203130c060c020f0301020a0e0603191415030607020a080306010c0f111e1c020307 71
    0x40003444402c0003646955000b40d50b40310040700190604e2401001c030744c107008100004001040c0720300b5140344408000d500c00351f6504411038003903102c51900c0d000203070441c1d43c1c13140e41020401103600030404161392000700c91050703a842064030701c12080320f8110380001c0c4180b403c803282914800060700502007105411820904d0b0700c040c001d40c800b064003000d0005218814104043c10780300144903c0c4080009082d8550320700211446034940003064010301705580000040d801e4a01d05000303c0c6007a6009116501c225583e28004040440046080e48188455220108a031030148221200c042c515151003050500041c108441508000c0c40c0d8400d41c910b40003802541d00300c41c030500d074061503050782c120b00504218156016400314204018001c0d84510f0034040e01070380009510b130640707600ca8109903172a55001c0c0121228000c1d254010000503540094904015210018030301940094420024484094004501102c400001150802565070710700324401181001000d180780081e0886107090b = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 969711816 1250 969710566 969710579
    0x50a1d09090607110d090b2104050a050c041a09060109090609150602070509010e040c0308030408190912140a051c0f0306050105040b1e0d090c08010e03031906 70
    0x1414110388440c074507007000c003c0103a86a08020000c885803c1040202103140801c44003034903040c03150040710960000861880394000f141859850401d60a44100791141014a8842e54541c030300301c0c04075918000c00484050b0343c10b10344500c02d000741d001f02c2e03000c601482400a0003103440e0701070110741c10098880070106010291740554001072070000000542081d07a9071500c49210788a4120743c085422400e0208030554071041181d065a00c1c0c20082c44240d100c074588800c103058964001800b04031b01004102c1408141d0000e0300c03241110701c3d44040258107a0313508a41c03401c508d000e4686800e030354003000b034040303182c00d4600301e140179401088a115030055100d00345044409080081c4030301c007002c201c1000d19402550080402081e0401b40841418800041c0c500e001381d0013204a01140480c2c0c0b410400310000314690358a0b802c0c0b20403940e600c0c11000c40c00142261b10420b0f00c44550007a03000402a00520980030000c0c924030242d41181c5a0148031580c4110700381514581c152120f4002c203c0 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 969713066 1250 969711816 969711829
    0x207140f0a02030105090604080403231b100903051e0a050115051306080304120f12030204050109120b04021020070e15010906030c0c080409150e0403050a1d 69
    0x1100c02400600d15000544105401d4031402040e0664076040141408001503e01040d80c080c3d0780d0100300c1c0600022090000648000d020540e03030300360303c90079030082c5118400703260001c10b084042c0e8410508000c0070b18181ea056102d03100007401544000003c08242e84e00781041928542414280d43c0b10b0751164071a9400d488003510b80b20518089181c080001d03103840300550008100941007804181d2030902100e03220700582c8518859202c10161107400c2200d00e0301040313581e60340714008031700d81d1042c0720000b0300941040c0142401324215070b00c04038600c900004082500c0d035000e01c0000c02940c450b030034840010740c0398200703e0502c9038400c2180c6584010810366104640240000d090041c035056003920207040c0036100c2141c41c00c410303c890000740d0b440080b6106031030f0a0704001c501104400c41c2162010202000540725000100300850091565048012002c0c6034018140e1802d0700c3d028076030718040041e100200451400c01603000301c81e000c2c40c803070641c500c103400c82d6400e181340b14004600d4 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 969714316 1250 969713066 969713083
    0xc1e0209090f01050711030315060f0a020f010509010e0c10110d030e062508060102240405150c0d05040203070e0a150f150305040507080a120f05030402090a020714 72
    0x495400a20b440c040b910802d10455a1200c011703e810304080000100d10b507281d220160214030000f49429240c602511000704850b00e0083c0021140e0751002d0301c00e0002e446e6041d403142c00360b06500b08408121030030710500039001005240400b4010940c169820007240001e803070010402c0c4a0207104111150701c0900c8002100401c584000c1285021100c0b23003424000c000300142008407510700011429503a00081000c0101d2904107200243c94a400503890b003031411070402544502c2c5c40c00c3c0035864003400c0200e40514485e10854020a010301412140700b80700b110796a400d00030510081c1002e2959420603504540080d0980f04015207800e1410b610300030484013543e0f4a40c5400b80c207401d013862582d121004203550414448600c3c200b000700e00c40980303412624002c054482002c202803010600c204801400388a04480502c503880c600103010041c031031112404a02a0300710304500c1806041100d1003203900826070000c640d9060100e100942190805444640e10b04010024654017000701c103070b = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 969715566 1250 969714316 969714331
    0xa05063f0f0d18050117060126010f0602100e03030c070f080403061d0a020303041401030f050405060103150e060105060708091e040b010c0203030703050702310609050402010c1e0209 80
    0x41d003001c076100718029049420380c085810054403440c020051b056819406810110034a4800030301c13000c120b110081041801c520f000050405000084c10755203081d6200126485034080d601e090709018005400ca40f414803107102160420030004180444c2c0c1c01c02428814441c0701200c0d00c440c015161008903401030b810844146030342d04100012204480710002c41d401c0620010001684203a021940303034080c5120f2180540b070354440710881a1300076040b0207203088003040100240e281504066640d0794080c441924194000c0301d0404081101c1c1c00358400070003001b4018807080c1d00e46424450f8075030188506a078030340000d00c00c0c81500c0c0c0e10b07a61000b03240d0f07018043c0e00e00c2d241103c40400c003c6079000030342141400360070350340714005031008801d841030b490305810159180d4040340086003d402510048100103051040840c150701404106854000740101007084102d03100c940a00440b503040d64040c4c045529103070304500280031070301250180000c030a515500503409134007060003880c041e900308 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 969716816 1250 969715566 969715577
    0x702070f060203090418030c02101b060212090d0c0b06011202121f0303020c04110c060103050a060c110a3525020d060b060f030a05063f0f0d 62
    0x20b450300e00c1c09020b480b1001b0f20f01b0113030822070a4103640141c00c8000b40c8600034000c125070070301ca120050140181f80103402c07071000416907009451074103c000754441d02005180b0861040031524004c400121380c0b01e81c209584400e1403146880e00d07401c9064070b0040089042200c214008081d41981d40050458814030044c0c0a84905000140131f20b03070002071150058449001e4000c002103076000582c035507411400d0720300141d4402040104895880b464020841501c00c5030000000c1003030005103000c000c0d0044404115018a100c0d08980c1e9205180718680c06903c0181000d000c1010402d040c3c8011444400f614804a03081d141072070490030b40d8502c9480f101010440b075000340e9400720074074a10800a95503480c0606240d001941d41d61138002c000d80555075a40c5d01c01d009455410855244001881d202516072034407104410141c4022980d080c065603d158101d1486400c440c000c1016020440e000040101005241d06880e111b0040c20315a0b481507c10704a01c1190a00611010313510786d40c4c42 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 969718066 1250 969716816 969716827
    0xb0406091505040c020d0e15031017011505010305060f03011e0e0303060d0f0c080102130305100b101101110307080702210d3c06120f0b0702070f060203 67
    0x944015100300e92025000e02e041c96002c41d00285c0c08525128030810038100f4020000200d4003003280088030020040d04a500082031050b04c51041001400b03c0c3ca060081fa00508400c3d0304490070b0307a0a9120100c2c042c110030b01c3c248810740c080d401003680143e010345180140d80c8190000f03170035610301500300e5a00c1c680340054030318001618000c158200100b4001149541407440105519002441c40078040203030300302c0c0c41010841481c1c040c0d001800802c009646030340d4134004e160441074080c03008490502c42c855144e40c80648d103008a0700300300001410384024500c01201a03071040d000401c41d40c5595a19200000f076041480003641c094095580d90b50b185242001c00a8500034205002101d1640c5800c4a800c00b02405421541c0009440c02e011404211500300b4061060450071901d54808149480000c01e10100c139181401c59140c00041c00603545d1800d2001030101ca182e0b0290259242d0751500d004101600881a0401c000d0320440301080e0b0703034000e4802c2d24041c81c3c10000040e00300044 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 969719316 1250 969718066 969718091
    0x3020705010903030c0e0f0d08090a17280302100519020d021b070e040305210703090201020c0a0317091f0e04150b0a140904060e040c06091d0a0b040609 67
    0x1001c1824240554010f5801f0f00c10358005107241c055084020320f1600d0000c1e20201c0d035212101c64400078405611001070388042b01e02841e850b0924034581240001021910740c801040b5011a440300503007680180c208110114501000f0f072000410000803102082200180030b10148000c01e036a4040c0d502c0161514140107204032030404019407038419900142c014401301c2c0220100a81013907041c00d050740c0e9510b507d200300031506882034030785401c50702c4002080045501900202050341c0300340e09803502c0f2407100d4100a481d0310f45010140408400300e007011500400da00c024a5100d5000700b00290508041d408002400c0152800c203001071341540c0140154200b90181c4070600352050303162780107a4101103c42e4414020100100c00b04030b1782404040090b8030900032280c030924040c0090002540f40c078010025940c0c00e607802c0b40c003803012240000b41c8078400d03440a001e45020b80c40350001081d00800c0c1500c03281c005440000840d1b40c5d46240d010650381d611039140203161503130303010600d4440c202 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 969720566 1250 969719316 969719327
    0x702032115030607021005070210050717010b04060c02010e03010b03030703111b060306040506150d0608060f0417030403091d040b090f0d210e1e120d05060103020705010903030c 78
    0x10071207000f0b620210610050300d4003c1039000c15445900700010342035580d070744101d282c20003400e4007441c0fa62824060200c0d090f840840303910092203402c60b0700096603881da0041030394410b034801d02c800580c10521031401980326040b1030040c420001e0020913120601c00000303007994441042200030500d6000b0001e05814284030001e08a508102c0c4154811014070100b04a07210040c03459200b80d07a1400085c5056643c20301c14402c000b440030545807240384858044005140a0044003028811840001d02c1c28104200007403103203900c50108086208040c4040f405030f000503000700c051004804000c501c1c42c0f10803105190031051007140b403c00741404d0511031304101021304500090b4114080f40010381000044032820301d131043c44e180c815610002d20341042514014140103809081401c4a08640310019910740403c203250300105a010318207034013560316180360740300ca0072205050012a09280c0564419940301c001030401601d03082d441d40d2034030300f1603600c140c0890201c0d88c1d42c900790fa080d0341e120 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 969721816 1250 969720566 969720601
    0x120f091009030212030402030f0f2a031009080f0a03060f05040b012703080c030903010b010507050604080d0e0a03110c19030f050a02030a050601050907031b0807020321 74
    0x141010051407807280c900039150402440382c1400100000081000c54808010301140c160503101035808417842c0c1c41b081d0340c441021000070500c840540c6080303440040a011181c0650f50000e000701380e0061020781190140c401d05105840070f900610840c0c40351080d1600600c09136060307680002c1e0150034006c821a05644940205000c0c80c50806041c1403070b44c1000070010302070943d0350031440014100c110306c407084a1540001704881030105803611410000405060b400c0c908800a00c601c1c440d5200450f050700a07a000584a64403000100b404100c856000b04500d6004401c0030904c04c5501000c580303091000b0a088002030710f90784d00103806040900407081c5205003211014021407074401642001005808054a900000c000c203104000f0100030b00f0440c5540502922105001410881d03181e01c400d204280c040c00d074000001e48500e120340318103071200200c01001500c054050000b290002030003803003c415031200b00310030700da0320310480c401450b1b0501c4c40342145801d1400c09000783c01c0d450721 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 969723066 1250 969721816 969721843
    0xe090d030f0e100f021c05180c01050a080403020106120b0a0501090605030c1e04050c0310090b0915030703061e060f06020a15021201060305011e03170d02120f09 71
    0x1c081001000b16000f04038030340c10784030f0081e000c1088582488500000c0c86024240b02005a6004206404034001e4000e6449074801c1c1207030440301181c510341103456035242268203001500802854640c68064201150418081d01c000202541c41da8000ca40d40c51107450152a40100300c000c201031b0b10024043c2d6405000c0940d0188001450900401d50311200f00c0710061280030300e0340410a10820004000603e074000400c144000d00f41040d140859500a0701e10100000d40395801203a03445450090030144040a01955503c2c1c0e0341c4800c03801286612821503906000d0040c001004c01c2c100e008508c81501020340014044d8003442000080341c030954000304e190303030107200100070280c1c0100e00c11072102e03007050415200a40300740101b002841001103c2c003c3d0b5418500100c0ca40c0d41c113034812070594012810743e0380d1315001107450100c07041c0b403880014600c508804e080f03a11000e400002e00701c102c141100c003500340040010b10303e01c0c00a084402d20354071080c401c204806200c00301301c41c81c01c7c600b4 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 969724316 1250 969723066 969723071
    0x9090203190b061e0324092b051e04170c10200111090a0b1e180a080a0b072615181b131e0e090d030f 45
    0x1e5681e050306030748000c044610801c006104600020141604048480f50040c10340da1880f10b440590303482d00d52105501c040c00310039034000540c4a0340c00038100c905104280701c0d40f4881c842c160f0031030641e85c515202400810009001e12044640007446a0185282c0c0d10f09450301c0e0341c201045c440c102d80361010980100c0e1700c203c05151150311007440100b0320305214901119480c490f000d800303840b5160003800d880f4540ca86881518081100009000040300850b1180c29072565020300040f9070042c9850000c501c54010940c1520001e0700008200d0b890020200342c1d840e109500000310840b000e580304455542080d90750301c04004611803542d40c000d10504202c50f520000c0d00d40400c0c50f0987c00300703143e01c1030021008240f01000120451100d01c0005116819610004030b40403102002902c0038521000468400c0c1c180300005400e584940e03c1751000b0403109880c00c40d9062000000c0309100e40441082c0c1d2000c43c0c001e4032100414803072a20000200703006454108018204c4200d03464000030b061 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 969725566 1250 969724316 969724363
    0x30809010e0418060b0a06170406090c030f030e041a1e12011a190306090302100e1c031a040b0a0306020f04140306130209040516120c08010e070b03040c0f09090203 72
    0x5401204004121031000c05500007a17641e403402c400180090140940300d1221228000100080c1d035166600f100e109568260180304c2c1c138000d01003540c400d404e102158000c0301d4140e4150307080000403113c0300450001c5000941c514a408030360049044c4a12a1141c0d450f407000100300803081001b2156058280d80342021a42c00852001c40d0b2061b40c007000b06081d84600c583d4082c50304c01c01a0483d4021000b00410001c414051925a10507404400c1c51088800c40c50403101c03180a0302c02d4829000d07040c0d044030400410101008010081c0125065000900c00d00200c042441880503046505c51402905d0307039507052402c08101c543c1c00d483c005101750b1060040001c0420500322404000350b040e00c0442072501c0301c1c6002414080d1204c2c4e140c80604808000254510701c103d031040c3d603180140361103120b00d6201c40b240750980d0000080f0b00c80541c0140002c00c4601101002164000d000d031604000094a031105142d00d20102e6100a10052725043c02c0310075850305108022401d808a0900c103840b4 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 969726816 1250 969725566 969725579
    0x20d18030c030b0c0906030c030411010e101803080c060915041a04020d1209051504081b0d0b15090109090309140301150e040302011b0504030809010e0418060b0a 71
    0xc00c07076000c0200101c81e040c2c080381c1d10300d070401c080c0c91000c0381c014542d035240e1400300d0745200300e6042181c0c142c035aa07400545030600340d405440c004010020190410815000014040e10701006a0b42150a01814104000041450080a00b41c40118071019010504154580b1491b04248090464014803450180300001d04401016204201a4440c034841640c5500000f0b000c81484031014280244071641203400380e5002040c1000d4402c1100c0c1902c04246544031501107010b00e014058803640042a901d020a25050b034180d90f101004110444000140c1d4694804001c2a12542125102800051020301c0c0203002e090242182610801c4a0758503920000c1401009100701c1c0c861150300002c15410b51000e400c41040340602d0805c0c00c408503543c26415403102c20840c2c0540040d4a080250440b010300c0c0000f069140c201d070b0313440e28149410354540701b015034444800c843c18040e100300c98640c10b480e6130280e28000c9160104206e00807409040c07102c1601c0c12001010312640311480c0600c842c = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 969728066 1250 969726816 969726833
    0xd030c050a0c0f02011403130212010c0c020904080717040e0c0702061c060f0b090306090703020108070f0201140a020a020705061611030a081c0b03060f2e06020d1803 73
    0x2500720b0111080c0c043e03070380010784d91040650212240814000304011002c401400c5000c0820700c20384001401da980c0740d0b480c1e402c9804140e5480d0009052480d134030090b151409031207420078041d0069528140e900d61310b03c4c420003c600c860b44200710300841c080007040706400c00303d50300c80c1405001910304ad65035030006a0911409400c01001108101d00f402e40b100c2c3c0d03900c420040c180c01c40c0c40400041c0c84581e00300c0d254008001440c031a12800c0700160b951000411150b040701e50603101c00683d03031a5440c0544400708160903034800c41d0b40e00c3d90380401003400103c6950051455480042e41c8064035035000f402e00c0d0883c1c00031400762900f001107a4042940000100d03885030082060388a00d415100003e00340072031281702414800c000300c0c0d503401308403940140046201c01d03c2001c00c1034840007070a044e04d03600101c0e00890400310701d0001030600483c5507911611154168456141c1d00c0c240801c0c2c00705818540c00c0440141d1009207c0660325811505000c5c8000728449c42c000503524540c0c6030030a = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 969729316 1250 969728066 969728087
    0x304050a0b0d0623030c060f0405010c060207050307140f01090803060d140307080a09140109050f0d210f0302030105030a1b0e0a02120109140c0a09080307050d030c050a 74
    0x503004000076000c0e902c0744a03611850240a84d048012050001108402c0c400815210410711034010042421051300d80041200c1400b814691000e051070726102c01034a0038200d030350b010395605400b00210300001d98180014155030744500c0040c9104010010203500c0c101c1c00b500520104e03894000c24002203501501500c3d07204070115400d103c01d000a141444120381980e00c220007601c808500101040000000b07091008082c0c0e4030706003003a07503d404000a90144090590228001c08800d0016042c84420320144034000346c001c0c140c1c9411643c445c001110000041c00091240040e00700b1820b522080004001c01c552030154115410180000d0310354030007000082c1210715a07102c0c6c02141000c1c0d1000d000a142c004503e02143c81c1402c60180a50301041c448001e0b0481e8800118a0640310310071024800c1a981802e20707180c0e031700d800400290303004030281c00c01c1c0b182c910800100c1312800c00060a400d031003640605200c141802d006410740c2d00410380e010a00c5818081a001c0d160300115504 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 969730566 1250 969729316 969729329
    0x122006040f1e1b171f0c02030403020405150f010c1502030c090603070903030e0303270301090b01061e0c05030a120204090207050f010f0908030f1015020d02060c03100e1009051303090501020304050a 87
    0x918105806400d88ca540715940c8004e401074201000c0050380f1000107030140181c0d02c1602d0450f50b00941c000110750324036403540014000c40600140e40d8012105074055139100716040789040c42c100d40c40000070b2031900129a248009034010505108040e488800b0349020501540294201500c2c16041c140607403c2810311043d01c4110410550256001d410005e40c2640220a411155840d100700401884c05030303943d503208890202001041510440071400145d4000004d1420803d410108480c10000b6006078440b1030b07020f11021508032198030042c0806489034005180d6283e0000c0e0702da0944006001140c0704e02c3ca010101e0001c2421001180c3d88a04c0000f8107044550b11001d9050700040103802c4202c2c03400b014517031103c110f0f400040300c4801600c185c00b200e4050380d9012070014184030032196560b5034a541002005000041c510709078205080c101120700e000c0e22070013030208035032044684a00c0b00c10302c2e9410405042d005450740d8080e08080c40030b14076103070034040416004001841500e = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 969731816 1250 969730566 969730571
    0x1d06070213091b061e050901020f0d030f1a09070c030c0605070f021506010e010311090306040606030b010e040302150a09122006040f1e1b171f 63
    0x220441d51518041140d2034250142005418800c1c10710000d412068107030744003020800310780800d41d240203440f0071072030b442c0c150040710701e0503e0100101c0315500800001c80c1584641c1c843c1c00c0c01984280a807502140e256503000680320030f085005402d031150b0707080c1e988045da400081d00c00390341c98140300c2580c84440d6081c4668180c0c42441d00300c9000d042d804025241c10f25203024004c070590704c10380f5104640c9080d8200c40001e003038104007000e5060240d801e41e01141a1120319031081d40250132801ca42d8082d0000c0505003011000441e0511108807012690150727580c0c801e00400c00c10140f01030141401404030321991a01e0758002e50768654480c64800805c42c03103400141c1e810804d03084504040d602610324001390100744e4014040300e520a11003c0741140030040100042000a89144195000300f111203007103083d41c03900519140fa064541200c415103450300d0001c00c08071401030010000c02c0110f0340041d40f400c101d10600550020700031440d90000b074450741406007045e461181e03003481079600 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 969733066 1250 969731816 969731827
    0xd050f0322150e0a0f12030818070312030e070e070207060c1a0a06051e011d0310021e070807021e130b01111009050c030c0904110a09020c030304121d06 67
    0x24410f0300c4c241d010900880801038049094080d10954100d00742c0f1a40394a900e0b80c980c620943e0316110b45e0780d070901550344124402c001280700786461901e19075150034002907202c0e6680e003c84c200356460308880030068100c82071110460b0704003d0007004200e58908100c40d072402d6695003000b0144003440341b80000f112000720342c000d1842e501800040078010441040803021140c00200300780c0041c0c03000d01040443c15180380110040b071300c440102d030700200a0b2880c01c1ea52080b183c020f4024080080303101c2800c000d0500d00340d0400e40101482c40c040c07140300340c481d20030744104444182100080740e040002625920842c1c3c568203448101c03a0381d040808612034000a00490300c041c600039145020707210728804550801c400e5071055000d203000b481a2000c000da00d20a05540300e80320303140c941c0c01a4903e00043c3c04103a50107181c00f28110020003a090203070341c581303402c030580e005014079a030545c00000900c400c010850a00c0218050310b03080038507000c0140400d5482c0415040180341c01000001072 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 969734316 1250 969733066 969733069
    0x10240309061104091a04020a09031b1a0408060702010b0a061209080310090506180408220e01060f02060103051e0c04111306050f09010309020d050f0322150e 69
    0x50720714110005802503eaa540d4042c60001c2c142c5103a8a05114016503030042642c101402115059401c82d114401c4081c0342d95600740034440c030701442180a90001c240411920484154241700c1401920315a884501300404281070034405401d5030706581c03624001d00b25503110103150400b106c0c2c0900700b80c801410707002411009003016002c001c2802ca400410410700092941055080e175070901820400c1d5941c0708184181407542c5862250010540000200040e030008002d114441414560f050400c12a150401c6c0340c00003504a411080c83c00c000512015600c5003440704c000360648002c00300c65140d91600c0c0c0c0c88001d2504102a4450b05055900c207654081102c03000600d40036000304401c0358500e034115141c0d04001c521081041d03043d0400140644104155201d000301c007407000e0b140ca202d81005600900340140100c1e004018140a480400d8082c00000701c140710103405595a00350030030b10002d04a042403d40f403400003a09009004161400501d03003a121300a08100800e4240c0c0700 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 969735566 1250 969734316 969734321
    0x30403110d2303220b07060e0a0503070f0b0a0c0c03051e0304060906061a0409050703110a0305070305010609060c0602131a0406031404051b0105130e1024030906 71
    0x800c82e0700c120700d42200351041d00c180007006100d00000200d5615000c1c1c804441032403240b20500c04d03807082c41c0041c06028042a100da004518181d5420100c0d0000300c01a91001d0940e0000503003590809a05103c80d001d001024205c1c5034080403036002086410400070025000307600f0000c02a007005070106034100c215000c09e0100790380c000c98840310b03a201d00d0a0300e0264050284500102e4240e82400000500c00e10000031086030189050718440c103083c240441d040013090028106001c05440d194601a9500c840300203101700c0300d035603a0100d12440e182402400740da0041e8040400c004d10140204a11356012030300e07060455100740003595581140c8047d02c0003034419048204d14001000c038852140b0240c0000b80210345040d10b05100c1e00c1413551222a08a0048a0180c4540c00c1303100000e500d807925280c00d2207140c1c03050401c42d0405c00150540a0140c0c040e0b0040c143c81c0504034140042050b8510040c001492842c520501540407402c41031460340480080c0c209051320303903003480b08001954 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 969736816 1250 969735566 969735593
    0xf2a06070605070516080c070e0f01061805090403080a0605010801061b0c0f0803040305070e1b1309050108030d11070317040f05060411040f0c020706050a1116080f030403110d 77
    0x40c0c0150403000d22608040c4482c3c0d2007040c40d42c1f001d229810000402481e128005032040048042501c62130313181c1402500c6c00c0f00314200d081c071342c0169400c020a49a4038020424091800b0345d039440320a20708064048c0851300f00b90400d606001d04040100001030340708640c0d19140780c54180b6225095042c0c41e02003545849500506a2501c0030500890322580000141041324050307001c0700c803200d58600c2c0e2004905c03019212111101e850280007104410100014140000360799000340001e171b6151155030480c0e00a0300301009680000581d0880f0504900911203202840c0c10f1951800810759030182103108500c203442c0703542c1d0b00d00c0002000e004248400041c810f4000091f201d95180c01c1c2f80402d44004e02c00d000f40d22684c913051084200c00341f24420451040100d40040c0551b41c103190007074605401c180385860070421007961000050005100b6610a28040b00d5141c1810303044c41e56031400c0182041825119500030300040000c500c5c04800d4190f8042c081d04c0902d007421060a00e01820700d5030 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 969738066 1250 969736816 969736837
    0xc0d230a05061819110108190f0c0e01080123210703030816020604030e0310090503040626010504050a1d161211040b03030c0f2a060706050705 63
    0x1100204458000c082e44407180126440e025580d480d118101815104c000355a40980105880070007540300d5400f80c04e1150308103100492075501059100b00880c2600d07640b503c120342142e102e802d100300d01c94000c0f074100d4220301d003400c0c010703499030500740d0100100e1100c1c0362802a40004103000300607625000108691b2003c0107065403030364448164038a07628050752104500044265000421214411a41c18038075042a0301030300541c0c503542c80440d200c54580401650501540d08103c0e1841424812101058424805140c452b440c00768040d0480c148003422000084d44051032280d031003581200c1394151102180d00107515250715040400038101c015291460401080a40da511940081d0506010048220030981c940c1c4818040d0300210505000900b0405407210300081031810740c03c8102d001001408803410700d01e0102c9441d2810030a1072181d40c264101c0660307002001003407196003440b400e09d03030f280190301a60031004c54881c1c412600080d021076610030100340d0751440703581100d440c24803 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 969739316 1250 969738066 969738073
    0x160908060a0509060112050d08090127061a0a090c02121c0501172d160603050105030c06072003010c0302040806060a03110d03050409020d0204080c0d230a05 69
    0x18040c80c903100030302c8143d4002c85244560000020001c1074010f00c3c81c4c2032a44400600b07442081900203550800000c1c10780801135484800080318806d040c9942e10316410342c00e41e5245800c80701d00703100d001c0700c6048242d42c1c249802c0686616003500c44103000c004584c005000050f1861840408904107010b5a40f85509034800042018141d0140c81341c2103515104884100103a998600d02d00d0000050346044419a8100b02c12004d6480d20001c1240c00b80c5c01c50460010031b00c1301c0d02140c02d0418080d502d52521211950805011301076251150030301515082d00109960083e40d00050428007920783c0003040003000601d4510840b43e88504001c6080300900240005030070008046c010350040c0c0252081c520444001902606d0080d401c4800c50f46c00c107403520b2186080c0b2003400141c00201c0d40950a00000700000a802c05803440103002e410200340005845031300b021452401e1481c21460148141c90700700d103190104d6420340e000c04056001e1041f5045801e0042c000606050b10084013800750700 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 969740566 1250 969739316 969739321
    0x130e210d02030a022809120f05150717091e0c0d0326040209060d1a090d0f050723070302040e0c150705060703020304030c0f0f030801080102090916090806 68
    0x4401d4010745841c0d0381c1180e0041850006205c0e0b2091400f00340c912100003004181e003084034040f190000b00000380104800300f90300500ba283e151524034002d0804000d40742c5242009410343d4441d08404001c404a45407000301c0c24070144039956210000c0d24400d050a111542061440003007001550206024000f040082c0f01d60601601c0c02c0c1c9100302e604003804500c1405412101c0710004584103da00a24405080e00d0743e5062001000c05614100e52412000100ca140c03083c0015000d485010f0070310041014850110004040c021049110030500c08148981d80000348101880380124a51555010700d54005110082c6070080690000e50080d00d0850500101c1034080380107154400280c820210194035109034502d2841100350241194209c6800b040d103252290300103581060080c0b038600000307440381d102e841c840551030030220740c15403001000f1010035800052243c0100141402182840f600b0b1004c1007500350b0041040c04940740081c1031a404074000c00342d500c040c141001c1140c0091 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 969741816 1250 969740566 969740581
    0x60b0a170a060c05090315072709060e04021f02031902252102010c1205070303050c04050a06050c15190b0307141c080f09130e210d0203 60
    0x22484041c0540300c0c1c40c00e000050300440d000d0401c03203842840c00703002000b0140355090446030340d100c090140010071100000700c1d03a0001f2138282c0c60401d841054105548a8609031980c01142c10a43c001461503003480c00f00030143c1d403909561254603071100e4035100d1801040c4407c0381540704162082000c0c0c8543c103030745221103a000840c0308100350303184552020b5604200310001d8010451169444d0528042c1d80c001011900051140042e4030605180500c0a601d40e251240150703400a660700040f004a80d0105040d49400b6958001c104c01610700e00e82414500800e103211500d0282c1424070000045021204070208020300014030303d22000c54041c20594600c519800c04101d141180c1c2d4105100a5000c0c503003c1280811034400d6a850303503030344851701c042c09007807290b041d20480020549082300c004140681300800400300c0c44450030707135a062560200407800d0030f2900d884180d2480d181000004500009509046821740308103d1110340040350740704414898403400300310107070000c400e10045 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 969743066 1250 969741816 969741823
    0xc030f0a0e12040918050a12120230040b06010f020c03100b030607030509060a05070509040507020c04140c0307050f131d0a2a03060306090809030f06090307060b0a17 73
    0x3c1d0341c4e948005104480000c112600c0b00041c44801820036041900d600c4002915107900c0e10b03020815007010100141450206001ca0b04920781e503a0034510f2a510446140081c0d0154020540c4002a0a0381904050b15051800300c2d0041415050004041c61040e169008001018500d2001030807501c40c180480c10440107030500d482d0842c0a4032660000c2841c0d103000b4001c5031312a9207417500900e116928005042c000d02406441901480700c00c211142581c0c07664040d5904c50001600107081011110051000300e840ba07020016201d103a11040c081020120f4003200e03004606480c0054807861084e548084c00c0c40f4440284440c0c1244480019041511a0000c000700b1042c5400b110140d03600c3d03144071b040e00e800030390020801000b800d00312040c113901c040241d111001c2c0e00d40040d40b280c076582d8042c12240c800100b507640b0310740407034100a030345000c102c1034803892001c0c40130b003a076801d00ea40340b1035503070191400061009444004100c0c003500c686c44e80707800074079030500043c507074500035800580c8 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 969744316 1250 969743066 969743069
    0x1c050a020906030d0e22090b2202090c0a031b02011e0b010c0b10090f020903010b0409080d0b1f030b03070602070f06031a04091a0f0c030f0a0e1204 65
    0x10503440d00052100d140104800c03010013000d441e44945407500600b0030100d200d000c10b0100f6800c14942c0c030300c0d102c0c101c680b00f1001841e08c40ca44010720b900781b44069082200100310703d950344041401c469070068a60001154100c00c1340700b42c068a84202003815030290003103108a045994a00090381c05542d4150801106140340100f112450a804500b00c8255000c0c6580786010a1070303800c9480008506101e03040d804030010001e00001d0b9210030440040d03805944c81c0e100345c1038021070450b079035107407c0c421070101c02811942000081c03600e695100c071a01400c0400d1600d00d54034550302d81c040c0c031400b01040701003080083c00785251800c0100a03000303002030415180030344500c50010501a000040100c1625142c071002d0700010314083c0110094001c0c42c020301c20b480080490469a17807150700405060612a25500c007000007190385d07910180c0c030014641d8441090300010300060130418403c9a400c03802e02c4901c01e84542d1010310940c09001c2c003070802c9460f88210060740c104440741001800 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 969745566 1250 969744316 969744319
    0xd1103041a0331150b09090a03140406090513090602030c030f0f0c0d0905030705010606020a030216060804141f020910030603020f040209030a0b0c03310308061c050a02 74
    0x31401003004081500300c0f1118100724040e0043c102807022401800305482c0f2100744140204001d6101c00101d5040c000c1603039044419441900504205070704644400d09264201380d00707600f81440c00200800410705841402e0051980b050f4032041060190022415a90400c80a5659081c0110100110361084030140c521804400214042200c2c22f030030940144004040d950401e1000015200100310300d00003105c3c039120030804034000680a000d0100180501e402521f000c180604010f8100078048000c50308003800300c2c400703004e1a900309241c2a00310750840c0100141c1a86e09030a64a01501c204469480c4424034141c1999242d203900104510b01c020783d0321041070600c644094068844500000358484c0d0703c08500315183c10a0b601400d08424000d00b180c02540360707a1035900080405513103400311031030000104545114980e1a40c035800b0f44404a29140b040d01060f29042c0466409004003009202004540136503100e8a403409201018206038115a540d0b2404682d81c000c11b4800701e = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 969746816 1250 969745566 969745591
    0xf1305040b0f030c04020a03091b030b060613140a0b161407180e0a1a04110928060f180c09290f030a1a060306030d1103041a03 56
    0x8546042c4141031903024034014009000703038190081000041d400441e60700040565585109011407100c50300c0003218802c490f0104d01707142c1181021012454000c4c04e46000f10300800c400c07072a108020380d5610490b42c120049961300c0f0440d0000075400403441e0b000c0320071040301146080e054806e204039010b1642c841c070921000703d9900169583c94032200e200399902c0020401181031100280c3d00310310420f1b0040e0b01595880c031165912440b43c1110007000c008500c451404120400c80c1440c1301101d0810f040f1103031300c0c443c50081114000300c6d4144008018105440344003e000000c41d030440d4028150542c0350302455500c41a180e4030000b00d012116181c01c1c18144903084860040d043c0d5000c0d510300d01d03580c081c2c00e0200700e2054160040d10348030392041c400c100842108080174002850040003000004500280714040c400c442a9000300224400c030410814450a9074002a0384c80f0300c01d6160a01180f84204402c0b0740e421400303181e1101c0400440d800d140c07210240b040c4015481030040c2c440b207 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 969748066 1250 969746816 969746831
    0x4090b0f100305090c151206040f050103031715090114310f060807120503121e070201110a270e041209060e04090609020a03060e10090b011205030f130504 68
    0x20040098400715903052a500104551201f002c0c18001003680084050004680d40c0b5240b07c4c1c000480340c09178030030340003d0304c9244c600ca16001d0b0204c081d030b00540c04121800074403d038030002614282040c41910003c44032801c110740d05807140d1a83c000c2484243d881031011040c96141d41114041035403000034020314011010308a00030301e10581c07045d2203d1900503c4100d0500a442024094007441039803244005e0106000c5c0c8035a000c42180b24100642018401c1000341441441012002c0c10240659051541181180c0901e0042d1030315441355241802ca280d50b103100440b000410b019103000c02500c10200070481c01c0c03864503240c0c0543e1082c5a449215a0001d000300c491a42e24013450000561580180000d460680c22a04603180203000000302260907034002441581141d000f16106911410006c091070000c0c8080010184c242909000a8904e643e0b40c8601b000140110080303180011a00c900344441001900d4002d41c00d00b908690320b2607420304c40c90030380003030784103144c0f0560900c00d5 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 969749316 1250 969748066 969748069
    0x103050705030f2d07031506091103090d051b0102280f080f0403111b0f0f0a03060c0c1a060a05270702030c0a0c0513020f04090b0f100305090c 63
    0xc41c4850301c5880c021004415141c104080c1400c0c5540b130010380d26208001e03010010034400c0c210000d80309012500010700c1c6151070001026640e01c52849003411030b0510801c60045800304910b004d49050303284c40e50340d0f100c11b280e01c291490f9500c0944005580301180c18140e138100b426503155014a4040c69101d03068030306504443d9641d104c401d500000d0084408103c0d82d082e503d41d1190094400e041030304035600c00010303607890405086e8450900c240032540111507801c0902e15181d03007480a0324503071741800c2d01d0030120744040d2003480004c281079919144c00250b1481420001c91460f4821025400303d2404242e6401c1d107403066805a00c201c8440c9400100341c07410425501c0c040700303070b4440d5081e03544100d40e011200c0c0c1c40040500d420341c0820801218245c10503c40003007070501c11b115507161507007014180900500300f181940301541c410021080c000780f000060340c04882c041c1070089071400d5074402040c61384580031007890f00600c404c011241ea042e05600154442e004510071514200a03410 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 969750566 1250 969749316 969749323
    0x4060e0a06020306130501081e0a060e06041a16050d061d01030b0708011410020c15070605060d0f021005160c0501020d02011406040b12030f0408120415051803060103050705030f 78
    0x4160032340e50b440030740c040c81c007600301c841a0250f00703180304252030f40507986d0345808040d1090003d4807502500700004100030400c85076107010150500124840c0c09282ca05068111400c00c880c0c4103052202c0410036010006283d001140030713080328100c900f03100e039450084c901c13401028081280c0c048006c4000420b4180f0480055040b11070b104446104a0364040c00e00280005c104021000c40c0141d61821303d2584601000e40079140e00c1414159560000342041001c0f5240684110301c1003600000c080041004060035080c0d15404440480481d4800f944c240c90603c200c41000d000041c00890302400d000001420400310b0310f0030780a681041c3e504c00012400ca4940c1c10b001c100301912a4023048103824583d02c920082c5202828680501d024410f85501e10341002100d0184014001000d000e45041800b02c16107100d22520001e05041c203007007010b600000351880c0001000004924070000c004440c1c02c200860314003406440701035843c0d00b00b094940c2c002c4c0c001c450281c801c40041860080000 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 969751816 1250 969750566 969750569
    0x2070201170901200a030e0a05030d1512030e010e0907120b010908030f0304020f01080f0a0b150a02010608120c0312090f030d0b150a05030f04060e0a06020306130501 73
    0x5a44166401110000101c844440601207108541da1201e0034440343d030700b60000640d00d2002d0550745440d45035036100202030341c044a118a515070801e01801c000100d0000036514624103802010444035841454400c21258541c406030004103010090f4040c150000c102822401080c3daa0703040300150402402204201560008001104602c140c0c0842e2603035840558010030500d0090b0440c0d66a40c0102d2458105400c40e0031005000001d00045141140c000810030f4028202241c0d58a010301010700316000042040e0811502c50440207016038610510360074401658110548441268100900803e464042c1c5142c0d84980e20314688820a01c5095610100300384005510305800300303580300c50242010308008011b10806180e1070100c3c4d001d001910b00180381c8a0f000400c040003c0c08c11a0715072a45807200e02a100820901107107607440030840780d01c190786041c10301d075503111460610300400c80040e27404228051640d50f1420010550000d6000398400c40c1d181c46191036210080c0c085400c00e = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 969753066 1250 969751816 969751819
    0x105010f18090203030c030a110d030e030d20040e0f07031506030b03160b0a080609040f0303050601211401232e0f0f0c030e0d14011406010210020702 66
    0x160404007805424980111a84510140940f820448800701092a6400001c52200841c4500c040601c40010030000b0340c04604d06480c0038000402204961034580c410000402c04150310b4a201a49040c4a61004800586010b0700b003661265070384001d5460440c00da40e205c0d0554801d8002c9144980b00380110092511204444680c441c54004185c000342900304000741c05005183c100009055030840c061300901c000042c1780c0e60344a011200030800a00206041d118840f254280400709803604508a066039142c04c001641c1d0b191403006981180781407541c3c0b003010818031500060300800d50056441444c00d088000d02c180d80310000800581d9185507285160305d000c3c8200d015601d842c1070030f40e5209903904985200021030b110031901e5030480c580040e02060111110100b2241e05c401043d0441c1102d1500021100c0c1654006120a510400301e5100344001c05801d428001c01c6107940f40e4900f4250000c010085110843d0000700000b140c0c036a002d40516140306480700b000d4000c46111a50 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 969754316 1250 969753066 969753089
    0x130203031611090403090317030c03010e1302030604030216050f060a0813060608010b09060103020c100c050d0501081b060403050715030b0409052d0705060703030e160302030105010f 80
    0x300c0218101e06148041050b00e058849074407803021611802140c030700407802075490910860541c140709610041440c1d00380c489800410400c0b0100b04a5020740c0d044d40c1264140c1c00054840092003c058418010042d515001c1e40381400708258001500d21080744100c10b215020310f0303507901004884644400082d800040401c020301e0f201e44508140c0354020780040c48141014195190074048903000d0700428242c4e991a90f11803a149440040c07140d08c60824682540340c18038040341180c0b542d0001048519540d03c2e0002021a280a03500782d680c0c1148000042040c1d41e522030303079039589400d190302d11081004101500e9401d81419011a02529040001031001070724001f5094100340c51180d030a42010754481103841c00340c5d500c2c020111030f240140010603090305045070700390045501045030a5401210143c00301840c10104648040360421a031494440025040c182c01401e10421940400e02030380030310000c031888580389801564000d03002001640c1e260f5820354007002047c05088000d49 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 969755566 1250 969754316 969754327
    0xb0a03022d0114120601090317030f060618010305040c1716050102010b03060403080c1204050f25061419091802071a0714040b0901020f0a23012901030513020303 71
    0x10080380513541200c0f040c13600c640425542d44401141c000c56482d185070000f07002003402020f040605000360060000c65950f8941142d0100d19a818101340c101d080c1415224400a030500002506401c02412041440e1411500d100e120f2034581d840c0b80040c2c030340c40c60050300c00f0596506c1442205122100030300140a0758031552030565091500a01004026504014404100d944800014012031066004003410174074900202e04208500321480c1c0007400e240d10700e04603101064079480450303415042c05500310300090104415031003042440b001c40c2d684445200c481652140034541101d003442210301540c101005040140d01c165040a0301480c0341c404003038400e00e049050f09800180307509140008400c078444101c0d07d40c00030307800280460b80110b0b806950b9601400000a500404000380204420558401e82c0202c0d6814525030280100c841441c5e00310025405200c030626251307000c00030041c030008407040750780101d240c440c0003900788408100b148503226403c0c010790f64014059420075 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 969756816 1250 969755566 969755587
    0x1814090c16061505030607021501060318080a0c05190c09020a05090306012705040c121509050703030912050c010806010e1e0103061d0402040b0a03022d0114 69
    0x150400755001c00803200100408000903194402d0100890016505040d072134503010405052050007418102590054035803094a0000030080c43e05452103801c0001c0c8540c007905030707195042c1c0c50803401071107180e000442080054104001a824910880071140d4190344004001c0940204200c0182860700880040c441034000360080c3c201071b0302510b8014180100d2400083c43c0c6202039002030242030500b44d401306c5041c8440c1c11640c2c68100d084040c45507007082e03965000121858401c0104e0703110f410815108000c8569400c413005215000d0501260005040454441e01c0a110440102d200c00030b00140181c0f840301c00c1160b0f990041c0c05801c0d01601540151407442c1c1c000e02850410145022a0601daa102810002a00c00c01102011014510000034048810035005200380780180c100d001c45403a46081303ca54080ea042e6004a4000200804603040c40040c1d000254001c1107043d542a54280c0301c1e0032a40c10301c55800c402d04844c1c2c544001035030741d0b401d00d00d0341d030201d44003c00038590036 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 969758066 1250 969756816 969756841
    0x180e1c0c15050a0b0301052d0c071a064f0e061b072310020c060415050709090b0d06051806160f180b0307181409 50
    0x1558000c40d080082080c408040504942d0300700c901c412a01e640b98002c50103400e0921845610000070142d00e00406185d4140000540940c07103884518a690000690300460071800d841107a0390004003a80840384030003400c80368110489645020340d641c440c0140c2e10440a25140521510384581c0e140c80000362010001500944501d504d094501c1200b51488140070780b00312048400b10030050b0042c0e00701001185180280307000c10030100d12041c01501b02040d000f40c6440c0006032083c010521280d01244450308004001c560701035281d20100b11001d1904001c5042d030301c654812401c552221482d00441c0742126001e450303c0b00090480c02c020300a5041c036030701950145400821310910030309a552002c00741c600032151404504c510f412008103046081122a421014448903423521a043c02d800610305000b44900c00c0401000b9062071520342c7d91000c07544007404020001907a2850b047c440075042403001c0f680b010030390100c09030001d030b1000e8540d401418034100030502c90300c40e150000071840 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 969759316 1250 969758066 969758087
    0x9010b030a060314150a050915090c09070c031b0506060d05030f0f1e04471c06080705040c0521040b0105011b021216180e1c 55
    0x1180c0da5030b8840400440d091386144024224520010301140e04c01904e44441030102800300c0c0d882c01d0401090201000c0080b80c000b11a184d0038041007000da40c0c00c00102d01e00000b000c5003a0304a16403070140050558004d060b40e08160298481c44945d010907c00c00e00c0e4806809006081c6400c80d20120301a4a41050340741501da000300e0071203090901c04c103c4051550302c407042c0c1000b48140012815402c1c0d50034400315141d105400c0045007000d01c1e0140c4c00c038254100351150840d0380200c0d000c0e4541c10032010345480e000011844006c2c0003102900300b4034015402161401d41c9444400c00910000e0194042c1500b0f80751610b000d040349616203424007025103285c0000c541409814031402d0120360320008400000e402502400c6802e04140c1005010140c0c180c100504210400c1403101e40b003aa4201c400d140594142c6502001542a031203181c100348502c03001c207a00070160000020360070301206001d00c00043c0c030a41004024001c1c9265580e0b0314465000d81501c01011a40305580c83c040d0280c0314 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 969760566 1250 969759316 969759331
    0x1d07080106080615030f07030c090807120804180902041506090b0d0204150306050f040903081b16140f0f0a030f050f040305010e0c2202070f1403030916030209010b03 73
    0x40e521118030302e4130b0055801c1110710340749668000e010084501d41c03600038041030031500d0a00c03007840c030b041504164460900703000d00503a0305a400a010100700c2c100045400821440402030303500c061030120b407000b03000c1c4420168422820300d2101074000e02079078050001c64000d0740700c1da03052510301082403486400c905401c84e2a25828000012980001c403000300081c1c1c5142c0e07001480c1d5041c107003003105240003440003030301942c0f80c107051600027034000314000e4014103001c0c68007071742001e02d680b00100c51044400d08550701da0704005c440100441d00702c003020104100e109a4420000800d46981c2d0340e6281103010184d0b41c0095101404a40251001400c8200c145040c0d072400040061001d207c0d48658011215603540340f0112b404c0510900c200980444110303882e01c01002440e040035080d2108240031040142d000540404020241b481c0d81c407465130140b56401c4103c003c0e4003a07612900100da000102e801441c40410038008030203400b60a40b54018031104043c0d0804041c4881e58100138a1003 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 969761816 1250 969760566 969760579
    0x201030e01090807030908330a06030c080a111203030609130516031b05010207060516021c05070b03040b0406020a031d161406090d02060d060b03011d070801060806 72
    0xe40403400c80740003000014025202d80d21b1891800d43c80324a4410460081c8941c42150103010b0b4010114140d00745259254600d0b504954980820b08001440c0342d40c402000f10b148401c00061511010030580081409402c0301c200c002510b4040c00300c600500001385080e03410420002c1c225140001c441c64100c2e41d01c61498007141800d60f561880c008402811409120203498100300b00712040042041d00300c40850201c4d0f640e4a03141c00170350f07980014061003090240116500301805240c2030250115500103050150300140b007070900013003030800003090b5a11f01920001140454441d0100c03030140d80d01180ca0002d55945031500c030b0094000b402c00b070040645500300340e61030f02c1c9101907220940b403100c0c000e00442c0c03580030f1200403409030550100c41c000007000c69040a96036101e00303840942c44d05480c1c01651040500c005200752081c0c41c58000850b00e81503000c9007101030b050145069031001c0908220101d00d40e03021084002d01200c030fa400051550006121481c440cad81c4554100c400a403e0 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 969763066 1250 969761816 969761831
    0xf0e01090305070522050a02070b060301020a0c030807121104150903080a20060a0b2b0b0c04170c0306072115120317130807110d060c020307170301050d0201030e01 72
    0xc5e98141c60040c1d41c1c00311000d07004a9480c0a00412404070780d007001040b002145000c005c450050280380c21900098140191100040d00300382c01000c43c1100d80b880000104118907000d1000401078011740144c003d6034040c03815891401e030140c1305500640381c114041a0814080d5001203034065811040301d1140e001000481c15000e41c1000140e005140a07180030400388007410501c0113500c45022803140c0d5801807003a039030301803144104d290110740c0c1001d0300703000f542d40b0700c22060b5042c41240d020070302107c40100040913899010600114404080342900c0654035071460859070703d07151359011160818143d81d45001e0055607070100c0240301c25510740111040e684c1d4200c0c400116030f55800d60204a01c0002661340903212018903900002c00c1c2407860f843c4c82242c0310400e082c0241d05006090043d40224100d0695a0044210120754022403d203c44248141e00075100c0d0402e2404859002841044501010600307056a040c1c6801800c1486860396039001100602103031840d80c0e2065580b03150 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 969764316 1250 969763066 969763129
    0x140901050f040909110f221808070501060608190213030c180e01110a180e1810090213090c0914090d050304030e0108070e0409030f0e010903050705 65
    0x1d0401801510310018100407141007084400f14031105240c0300c6c031869001c501550340c400e14110241158087c103800ca01c10455030003c003e000034248800300b1803200c0c02000c01c0248840040641c40d12510003400159500c410568000400743d402c4110045090040d07103954020b40c5c05000d40681410088243c265179464200d1052215042000e54000d4201e078001c0f82080c900031807411000c690000c00201100080407010f501484d00640c081090f2030001035002d039180c1e5071403005401109219000d50900141d0a100201e07410b40030940c03801aa80c4820b0041150b22075650040e40203820345034401007080d41c00c03004268110003185e401c601c01c0e07408208440d06102d07000801e000904014003a082515200c1c0c80c203503400103200e080260801c100310000e6440800f03900100350a0030844100d4980035002d44480481c0140b058000340342040c0e19044c181d000402501010311501c0d11603e01c004600115080070a901018045902c103d60230882800d0482c00262030310442c1c2c030381c40322121480d032 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 969765566 1250 969764316 969764347
    0x1121b050d061403060c070f06020d4a150a020a0201050c031311010309122016170a020312030601021e1c2a0c050301060614090105 58
    0x81400000840105034140d060800788655400b4002040c21110081416400680c0d103040c000c24400d01000042181c6c5c0801c03c42d40324201800e40c0c4604259200c2030f810110000825617000900080c01000300c1004025044402c0641c00c504450420918501d5005000c6808480560840d07458890241d107207400000410300180142c07a80d0307801603998038104200a080d02c101070414425081c0800c18400d035a80300b4030b00b8859007584196000720040c0c20344011f0b0010b044132400945a03d405500309117180340e100710707a240040c13600e45007079614901c210300040d80c402c1840c0700d0400b2820141c10601001e40c0c6425403004d0103900c84101c81d60901140d0100f410004684903c03580c07000003100b0b001c01580c0501c03069078114880380f5028a0038401070310070703541c0380b11010440f801c003010211031141003407180c0b0b03a441c4513440203800780110a0f15805500d8902c0b0410205031981d01d26040085418503041c00394204032401c2e580c50300748020303000c07074a084140c3c086d1580c0d40c14400104100c07880c016103003 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 969766816 1250 969765566 969765611
    0x20f040c05031b0301050307031202150f06090903031b0c010905031603020f0a030507020108060f0910030303050906040c0314031207080114030c0a09020d0f0501090c020d0905030c0112 81
    0xc1e510396440b030501008002c0d190040000b1824403800a00060109403000a2407004a0760460748041050440388020f0342008a1004202400039a48080100c2c556440311020300801c1c059868401d560b0301d01c914561240801d803113030310300e9800181038800080c0002001d0031828101e10000900308100341e48045c41d5601c08860440c0310554a480c02c82410b405111105400c4283d0f40a4a980500c41d03500400500c54080c00a06210306000840c5254403061310500c5440b901900000d45070800c10038000704003103580300440000c0d0800c00016484400402d01c10f004541c07100010102038196501c8030310000400054135401c2c03006122800011242121250080440c2e4075401c000d54184821410b2145035000c2e440d00035804510100c105032554402d1038101c4405540042c1c40e00d411035046c401920641190320415402d003000803d1070612a40a5607510400740c0845220001c04030042d180d000a502c503059054106103441452940141c400000d02c080d210800105240c1103a42e012209814 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 969768066 1250 969766816 969766841
    0x50c03072909060414090f040b0604231f0605070c09050c07080d02030103060501170d030b0307081b01091e0306020d0207050f01090309080102070b06040905070e19141909020f04 78
    0x1d488805c6050405115254011008180c0364001c0d1505031121a5022406030485014070365404801c0014200380c80545542e810660258502d410840c00e41c0d080b4068a01010740306c2c0c201d0201c00100f2038044c0e0103c4014650208610300c0307035858000c0e9240113110003030901c8030860040208000040414008095810404000503101c0d415030404004441051300701d5007010311001e03031200c00b078400000d0b045000c0e00c0d503250114030407015901180c107010055012640034401c010041d9401440006146a1501c0a9030341c156001c0e03859179444880802818145040d48071300380c0510101e4404d0f00201100e2042100240c0341414076a500c42c40d1106131494141d01365910a01e1108050740004014001c1c00c1800c02541001107a46560700d104c10060855886180c0c0e603103070041000410710034840203048034242c8541c03903e080402681c1e080d031b100351890303006072403d030000d0700c00d840d8111607a014260000c105103460103c1c13030281008081690050346d2000c7c41540b807450310355440c0201d1000300d00 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 969769316 1250 969768066 969768089
    0x310020a030e0d1d10120f060b0c060103060b0f10050304170705060601170601021b120d050a020607020118020f0a0b0d020703180e161806050304050c030729090604 72
    0xa40f00c502d960580304c140d004500c201c45440801e05d5050380003461140704030f0407510002d04e01c800b20b07003000c00508450740000324610001c14080c0003e040480d6080c101c0340111411b0000c0c640600401140144164003150320504c0b00c4100c200c00c1c0e1203603020710b510620541c245011103541301d80302090303604052000c851a81c801400c000702940d0002c22044030800c8540410800e0030008001f0792a00e8862000000c45c0e00f40d030520f001d80b542c1d03100182500d8200c3e4019100300300b10000e00106582d008214103070141c81208040f402e4184148660030b040c100c0a5a082100005d40e800c102262001d114140e42c408030192011a640c85044001c2c810480102001a0380e0082c1c4d02e00600000c0080c0c0441402c50f82c07081c070412040c48510b4005500610388003d0130700360005c00c1801c2d030b412407e520320703101d419104080209446400c007000318019070044089668811720b5504069840750607024102c400f083c85c40642a00040c10071a02c00e800c942d9104150070403042070041a541e80042e031000c8417011 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 969770566 1250 969769316 969769337
    0x15090b010e0409020f0f012601170d17060303071403031506120c0a1413030b06030303090c060a0e09040c060e063a150609060e0310020a030e0d 63
    0x6800061501c0300c0502a58280011041034002604800c40104414000c2e54000c1441c0200da10410400d94040c40350f080c0c0b070145407507046900f41410000d0042595010300e4802041e44c076003001480881114403a60f0700e000605842d103a0402028000c0d02070364051009210340400904482d00e901204203800f80255100e2503c50740794407100030007100c0180142020400c5407140f0944a018a41c8a540100220f5039001c414000b03d440030603102c822040580301040c0d040071051500041001c6a0080d00c20300180e4640c82c00301030b140e20040c0c80c3c14200358007841451078242070550140c507041e0f00e01c1c02c00505042844000c2000d800003203c0171240c142c2d001c40280890fa070000380c045070015040d40d913141001d011404105040a032281e4070b07035241c4c4013000e20481588c21072035104040710710b0200c103200c41100005020100c504e940200c0300880c9080c440403c60a205251650000100400625040340f24840f908002c0d40844200f0041640320070710b07903000134820000c10b4001652a41c0700900d44 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 969771816 1250 969770566 969770569
    0x50d0530040314041d0408070c090207030e060903190c0f060203121b0301060c080d0212091b030a0816060c0f120c05030403200d030b0405090606060406050a020115090b 74
    0x100f0300c8101030022188140b0083c0840584c0d0081104400c0d54298049030036243c5081840d054012400d004100030361107100800e0a400c0d940140c50864413903190550118100d104010050085000d20b6030180c0c40048103035050508816441c8445000e034914801079515001d45005e00e0f00c0c15000100580d100282810040007a5681c0c1540244000e8000c4905c00b000c0841807510b11042c458041003080002200c42400301d1882103070030540341e02cac85c00c540c0c5440d415409681105c0c101c802d090540568400c0c11402c0148980900b0350500c0103000d802c807801c40e40e8035071110740c00002100c071801e440313101d24000040503440f6049100e44c550b1120702c1084103000000742140c0c0d04500704017903141051160184150003c0c150b07078000d40e00d420250401090b10880460b04110820350307011038454803420111150305540094209042500c09005030341d98009429070380c0754140c0e07901d034004204005c01c004581c440c10207001782140358400841c0826900944c0700c1030400d141c0040c0c403600c1c4c3e91024015035 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 969773066 1250 969771816 969771827
    0x5060a0302120c01091e0308030a0e1e06130b01120501091a2205060610030207020d0303020d1a030d0509010c060c210b01210b0a09050103120507050d05300403 70
    0x107028003441103034000881b0030040c404843c41c0c440180904004408180b0590094024070444100344084039243d2a6a140b4070070826000540303c2020b000d5030300030802e0300190300350204500703420040002c4c09034a4200702c00160300f0071384400d07501956101864800036841600302d501d03403141c030009980700b03041c02e8018144140c083c00300c214064502c004030300c00081010445981c004d101b15000120181d0425003170700640724070355000f035000c0c0e800f28114040640541c05402d204111a2080002a03203480300409100c2401d401c440e8107601c100c2e0165104c03441103008200c900c8040c900010390b102d25030741e8801642c0064424030b011a0748905a540500c10440030300901c140403100a00c070300c0e0407503800600710280c3c2102800490035403d0000180400c25003100c58000390244c5803584040d61203030f881e40106020f0004891003c44090342c6413045126009588010f60000c0c041d041c2c6441c2c4142c00d5a0f41da00090350b0540260303a41d0403055001070f80943c000e898000b1519202c1c0185003501d0010034 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 969774316 1250 969773066 969773069
    0x19090c020105070c120c020d0807030807030b060403050a0210090b03040602040806070503040221120a0804021302120c07020a0f150e0319081b0109050d030e06071205060a0302120c0109 81
    0x80203184d00380076000c10300c6850b00b1031407107019080c01a442c0e1014008220f4800720508098141080003541170308056002e20b409110344d00c00d507030070080c3c0c40b005010042d26204134400500994440c0300204054134004468103d510031600f49584c2e01a90b407648a526a041102c05407080340d0b0200301004a480c044c80328550040c03031032900c81d141d45000c0e0b0009600612900340000c4042d54981d007805904010000020554808100d580d00c4a02c140f00092182e50300321801c9008141440500f07006050500a80c6e0600e404000c509080b5614100d180e080d503001003500b680d0120b00800001a00c0c580160040094039003402c40350b080c1d20480101400d1245603803c054065404424071301184040c8110340345480d0f0b40508451380d910018a4170000201d21040c0c0b60b00170b0752070101d8000070842c0000780c45070300c40816141444540400c01d42e168a43c4021030340000480c0e003400409450888070383c0802d81c4040014000120b2075201d801007500041c00620070f1300e459014540039001d568010383e6100 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 969775566 1250 969774316 969774331
    0x303030b0406050604260105280501030b061203070b010902070b0609090d180509010f030b090102031918060504030513080105060f010f1b08040608011e0e0619090c020105 75
    0x700c66807508010840a05c01c138030130000350004c031441b50201401ca600c80c6a5107003d02e00020311580c00e1410300034010700c400d0b04076010345070075610000321444014059a0704a035040703d5194041d584140030304c10312904484180035039000812000d000900c10444042c0a8105103000584030041413030104440036016265902c20206034080081030f0400040444503603180d031802c40c0200c5d90706113400ca416403035030300300641c0030000400105036401c03415a4082240d0107510500c450780c8569290b40c0c204d01c4203441c2c001c1d12000f0440d0101d25502103801840303944200741e00100309101103499101c11220140d03030480014000203540d10030324541d020414080d00044d00200410300b00b0400141c08a42e80e5804035042c412007103040400306e07000c0e400c2d042000140b0916110614080d01e40340410758400c0c003640c000719400c24000b040303a20b500104090041010120410b0041c107020850380c0c4c648000b808142c2c04044842c1610040c11b07507250390001080404408240803d080384044d0950b20014a0390 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 969776816 1250 969775566 969775571
    0x150705040915303806041d0a110d080307030603020f0f010215090708030408300a0c06020903010e0705090f0403091413020c0a030f0203030709030b060d0c0f0303030b04 74
    0xc0050301d5030404094202d41c0a456078224110403034212a0213030030501c0d40096404840d11081e00c508042d50454412102210100010381c224001c075a1219007040c20a007481c0c0c03003d03420000141d8420814142640000c01c0041d500060f91703100c1c20680e204070307443d800083e1103010403c110b04060f03180001c09502100ca01042a505800003551145a102c080289404900c04102e5280b018400003001c0e08202040c1d136916500c401310345035502c42c81d00d145400d400e100390b19109452445525008540c3d002c1d181c69141107d00f10301140c5954041106551007542080b1a041c1030382c00344200000b0301c01150140c01007500d080100300040e500201000843c080c441c00f0000000e0740058a0302c00da030320a94000108071440000b0818200300140212007040c4001041000528000f800301d603054401d0362860321082d00e11408a840c2d00041d10726401050030b00c14244001044100f90342d50040e80600f07001810300a03911204014041c60388a0f40d4035205019040c02895494090944149400e5409 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 969778066 1250 969776816 969776879
    0x61e08071a07060207020a061d03120a0305090c030105070e011211040b07030203090d030c06051315090f0209100303091a1803101506020c12150705040915 68
    0x10702000c004012a4500c0d1558009400030801000c1d6064950b95900074040781c01083d1a41c8010f0644440000c541c0e0302204044603008041c0b60000e007840ca1039070050901c0b130070007000304419006004064156400b9000d4010800b520392000d11400f8800d6110395a2480646100000540600748141d5901101ca0510214091482410049400712811070000c1569000b10707007030883c2180124008a50f10401c102408414036a0161100e014540209010891074890921440140403901030060000344000c6211031145182e03400811f003240540e00d100b50303030401a0b000801014086030a4001008440f03000c0c4289540551a4000f03408030304000c48004d00004200c940e5801121440318001000d80c0c4100a10703181403282c00803c6061080c00c1c41004400c540c0211401c0560043d0b1005200d9070924800500e070103400c80d500300f254000980303003110003a018801c0c207800c01030501080c0301d002c000010301401584500c002e031003070110b00c0b010741c1c40c10200515903c0d101e242101c0c4804103802d14 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 969779316 1250 969778066 969778079
    0x18131a040213140109080d03020702010e01020a03080703021303020402030c0d06080a051f0b03031804050709062718091e20031c0305010905010e090607050a030f061e0807 75
    0x42c820255201200400c2c0c2d00c0400b1030048030a04201c0e002690140a4044502c46a07a0190042c10406100f41c0b24210203091160049036108105000500041c06200115034200e000c1d5006080d142240d90012040725240c0d00840d040c0da1042c1e8a01c1c0b00c2d0320001880c900200c80714841e000107031041c40e02400a10946403030302039aa2100840144100c480d04412249000195000500c50a80941038030307214144010200040035021854900440c14903001407544e600c606204c2040d91501e0711140c054550303450300c62503040f2401e82c85469034800c028000ca44014081d41c4002c1c0344002c9030000c40c0344061450005d42e458410340f100500001c4040551000540702a030316401441c0640d0b040c40000003e1001178601744900d484400c00c43c00c11514101070700c2c0c2c503400650503a0f881020a21660b41ea1384492503050134215150b090315001a00811907452040d001040d58089071314005c81c9441141d1100422101254003c41c0e42c0d00c0150800b11103d1401d6481c40c009190302400303000c00e649040e0 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 969780566 1250 969779316 969779347
    0x10204060807081509040308090d0f020a06020f0906072301061203030e12131d06010903260f09040c0c0c15050705100b12010b031218131a0402 63
    0x200b5507414000610005030348001c006440000d100d1008041034014109402c1c06400c01c0f0302038031220114080e45503d2181ca0f4050354860100310156801014407081d1a04c03050020341200c0c40540070520200680d05469503114041e080aa0180400e000c05070181d0302103003100c001c0344d00408560390414108020640e540c6001c60f880315010f05010800214680c2c58a080c800307010b40c2152040008140645850b8170420110203445081007241c10b9004000c0303204c41c0c640d000303d034078a00092420000780002000408080703032101108850980c0010f41001c50031058010841103840c0d03103070200782c40d2086c4c41d050042d01c082d59014200944030140c0ba8640458452150051181c2c00c01c006045a16141c402c404a0360b01035080303415141c0418950000201420130308044503c60141b140c4080140a0184a500700143e001002000c507407055030b00a45487d000560017030714410350a80100c2031911440321002000a40d0000000c10040014107035101e88a4000f02e9800b4a1040c4822804400700c2c0 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 969781816 1250 969780566 969780571
    0x140d0303020d0209030105070f2a030c03020f1009170a0e0402090303120c07120206160f030e031903320603120703080411040c0e0409060209030f060105040501080102040608 76
    0x52a000d60b07140c0e0440d001030081c0c8507584030036405610380420841a607030700c51440202d4010540d00c903842c9450b50300604100a02a40c14903200305170096440300064010701c83c42140c0c42c468010b4500e14800171800c41c1c101070f5a5080b0b140c4031f5848204036420017050501016003d100c8442407401c1070440d0328003c1500c0004038070503010315400111205165810403d90b2880b442e0049076603700c0c9461580d250864110b160304a869009807031400355a98000b01d003042c492241442110300580c001a401c888100b0594401d100341680c40b1245824148140000c0c808921107000c1c107a000c1082540050456101900b8200c103081c06e014a40303218031224450350648001c0e89015105501e0b40c2c0e000a0034403d425180141340d4400045071410035800007042c61141d4015000d8070703455440c040901c0240c800313140d032010016940c4080d80380f6602d85903101054850240500504002030071003c01e1401145003800710103680711400403c01c0b4034240c0034071400740445074001c4d070400f4584013010b400000d02 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 969783066 1250 969781816 969781823
    0xc030402011119060e120906121f03030c110a05060901122409060506121f0807080705130903050f07060219030609050604150612020f0a030e07140d 65
    0x102c0318100e9000400042d0281e4220b161480003d110600d0000020803203e440028680504121100c0494140302919000880501440d1902d9410040c1e80107c10005286c601c030f0114901c2c0e0307072042214030f41c02d48002d503109407100460030200e0b0400310410029039005e944a50000364051040d030f1520360990344c024401382041511040e2455010000e45203004403080078101c03501701c81d01c801c86092405800c41d050300c2010041c064a4030180915449031139a0241e050410801207035003812500030035208150920345540076152240312880c02d0403120b90042480340d000500600c15032610040300c410381d0030300312002c003d5100942c0d80035085000310788a541c100a0040342040921403107404880820034000340e00c180c0140c81030809002054640070b6030480d6840c3c0320014510742003502c5624280c9180c1c1e034040200d9880d10380203ca041d1004075100f1205030f001d0000621124404016003050941520046240c0301604003c0389488101d034401b131a4800624028011516411169040da582 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 969784172 1106 969783066 969783077
    0x30904020a0f090902121803121021152d090b130209040210050f040f0602240a0504020a030524010504140a0e0114040b070206010e0c03040201 63
    0x14401c21000018504004240090104c7d02d000415030b01c010301b101d107401400303604507581c10010380d081449942c511001780b010704501017001c3c0282c2d5000801003800c030440e484820701d04450f01c11041115980e01e0112143d0f02c0c00c030112003000b0142c448104c000281d0020100003d00b05c1c0001500c030141040081400b50841c1881c118030302e9002030441c035030341e2640e8081050031900a1b89200034064108001c0d0125075207071000c2c00c001c0c142c00d50368003107103403911401034182a8014010314890490410307640c01c0c000280c011a800030341c4042d00041560316880460110081600041c10a01c00c0c0103451800610b490240e4005000e084c1c03c40300c035642d86005002c00c3da035001c00d200070540359010000c1c03085e17030460b0300444c3e0a83c8100300115a007640031140c440d05407800e0b1000da0305040407170104403c290b010031080f40180310350268028107140040701c0c2c07034260002a000904010 = true := by decide +kernel

theorem cover : BRFrame.Cov 969604316 969784172 := by
  have h0 := BRFrame.cov_init 969604316
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969604316 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969604316 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969604316 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969604316 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969604316 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969604316 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969604316 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969604316 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969604316 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969604316 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969604316 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969604316 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969604316 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969604316 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969604316 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969604316 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969604316 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969604316 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969604316 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969604316 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969604316 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969604316 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969604316 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969604316 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969604316 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969604316 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969604316 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969604316 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969604316 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969604316 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969604316 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969604316 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969604316 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969604316 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969604316 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969604316 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969604316 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969604316 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969604316 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969604316 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969604316 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969604316 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969604316 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969604316 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969604316 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969604316 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969604316 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969604316 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969604316 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969604316 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969604316 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969604316 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969604316 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969604316 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969604316 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969604316 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969604316 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969604316 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969604316 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969604316 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969604316 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969604316 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969604316 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969604316 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969604316 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969604316 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969604316 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969604316 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969604316 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969604316 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969604316 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969604316 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969604316 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969604316 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969604316 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969604316 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969604316 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969604316 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969604316 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969604316 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969604316 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969604316 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969604316 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969604316 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969604316 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969604316 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969604316 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969604316 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969604316 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969604316 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969604316 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969604316 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969604316 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969604316 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969604316 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969604316 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969604316 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969604316 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969604316 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969604316 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969604316 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969604316 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969604316 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969604316 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969604316 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969604316 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969604316 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969604316 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969604316 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969604316 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969604316 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969604316 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969604316 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969604316 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969604316 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969604316 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969604316 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969604316 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969604316 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969604316 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969604316 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969604316 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969604316 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969604316 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969604316 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969604316 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969604316 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969604316 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969604316 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969604316 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969604316 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969604316 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969604316 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969604316 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969604316 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969604316 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969604316 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969604316 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969604316 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969604316 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969604316 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969604316 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969604316 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969604316 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 969604316 ≤ n) (h2 : n < 969784172) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
