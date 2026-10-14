-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2134
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T05:44:47.473351+00:00
-- url     : https://prove2.me/submissions/007ac10b-6643-4c3a-8ef1-0e9773005b82

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 383633093 ≤ n < 383812949 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 383634343 1250 383633093 383633113
    0x3020117041115190201051e100506030405150703020f1210030812010906050114030f071202040b09010210150e07032705060601320904061d0a020403030806040c0e03 73
    0x3030580c0700c0034104c0002c1e6512420a02d03041c0c410b004207802500b0a40c0d84c0a040340c009036841c00f0991004c1c140038290400c034100010a034456402851155001e90098100c20401c14503a048890000b0100d42c20980304110758842c03800140140c414503001840c0600459840c80d4448207072401641000d401d02c40b010a824410340401c002031416240d54040510078075030750708019180c0083c001d04074005d2030014400600c100c003100c02240e80c80300d05803901030b1604180d401e15804a030311030b070044400e4440014001d00d8550b01003107140c2908034600010000091024007210000031140519000b0204003404241994440e0308004d03010910700700c81c0c60048400c003200c2040c018007d00101d48038094440051665030041c80701c6002c0007003241c4a440c201c9855001e040381c40030404117840d0306102c10b11807213031240c41758410100941541d4484c502607041c0b03c400140131241c01088404514010041032000a07400380342c56801441c05d6a0110b403605021800f83d1748214034201c43ca130948a00180a = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 383635593 1250 383634343 383634379
    0xf0c010b06030a06050a0f1a070303090c0e0a29040b01210b150c1c0203130f0e1308120c040302030a050c090a06030c0314030c0f1c0801030201170411 66
    0x940c1110740c21150058901d540f442c0354091f030605071144000c0c400b1001146800c425038400184400383c400d180004895102d175540e104041910b802000400200760108a1100c0d401e00c214000000014440ca603070030441c1501c1c1c0211044903c00502603074541c6100a103a9004905201da07030007a001ca4080c061708840f440304010036904004500c10b0440201148160a41a048601044514002c0c000100d0f81c1184c03009944002e240c01c80452004214815400741c0b1005180042c0003410410246075143c420f645221401c054207404241845800740b50000c0c0d100002c64154000501ca4445541d0381c071000c009290080e0b50000e1340500494622a040000201c3c000c0c07000d0808030707565001c0b501c2e00280c42045915034040140b400c9541501880071034400903591201580310b2007140c3c81d08a1010382541050030740c040d0340180d5880201e2440250055581d10310026040c2d14000004e985160002000300c1041c440c040d203c0741801000c242880703495183c1042c0084007500345560340c840c034111 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 383636843 1250 383635593 383635601
    0x10e150714060a0b15040302060d2705060114060a0503160c020409050607080f100314030f0a2003180f0a03050f072309011809020904350f0c010b06030a 67
    0x201c81d10804404180c017002c0c81c090801d4800f680d4010304124204010410908001d000902040c80010350403400d20444108840740c080b07020f8401c00241c00a545440f003003c0c08545001c283e1032041809000c82801d96a02500356944a803021070000c83c202c0101c181601c8207004204040e402c01d007000325040500c440040c0d02401038076190750b810f0450780e030444102c20000e810303151580c1120000c1c60400c04142d00711031a800072411002030b01d1400403100c46122050b1320800c031000c0414a1000e2101d541040f604400c6a6500e021002c4c602e8907000c060380b081d1040d0492549132050244072410021600d0351003500000c1c40d0b000c030440e0424200400d41a42d502c48501c944c0c0c48503004201c0f582866004043c46043d64400500b5140c0140d003407503a003030b418035420031a4054a13950741085d640542d0f0f13540f20880c06540180e85003403006103e4011401481075010808041d9400d030445031002003103090444903456500c80000740c944807103208150141a101c804103510040c08010b000c400b100540c8 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 383638093 1250 383636843 383636861
    0xf24060a0504140103090201020318032b110a110411070f0c080115231219030311030403020604081617040801060510050405010e12030304050c010806010e150714060a 73
    0x7803440103d165000110705a40e074651009005070001d01402000206000101c100c0210040c142e850840400b005405c000c03c4a660402c40c80202d200784102d0305420000120148000c000540040507843d10345a4040864542d902d0040341d0310a200506d082c01d50064545490f40034110261210b00c0e410b00b43c002d484c40e80548c14180d440c088072450151940d074404c00840c0c19503403210b2240f908940034503010314034030303407040c0d80241102816801180040c0403222049112015113403510083d070800900f10b61031a91915251801001808042034002803402c0d4010f40c010040c50f40c074030703c1c1201c40c1d10742400b03d03000400088400103c6201c4000701d81c00380054564500013040740b190b580f0b0070040390740804200b00c0e001c104100010310595204811440e58110043c02c401012000114400d2071741d4811107040c0d4054014030a0a40c0b50361344010354903040f081c03d103010b9071601c460800080716600c0d544401148800c001501d00c0800481000340390041d08007500761040c92030400700d41c90150801c45 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 383639343 1250 383638093 383638109
    0x50a0506040c0c051507020c0a0621050f060f03010e0703032111040905100b0a0818030903030412140109082d0901050703170a09020a05090f24060a0504 67
    0x401ca0b14180d5104502c060740d0b90340c000c0700038002014004140d010b4144050701c01011409452039540040d2031f0210040001c040c2582d49140401d408070341803810a00003082c0d10030f01400c04090024001c06049144d40003101100c6881005e0300da080040c5c010001d06007001e242380100c110000c103140d0003480c5200c4040c05a40c04020f1001c1d482c0c54401142c1003408039103507114003400f0910421910754403072680700380d40e040280d441540300c010f80d07801c982040a80a000901150401c41c0c40c40550011a50f000d001d14010360400c62114000f9031280280d0064107840002000b031175091003074a80078814201c0c5000005c20101002c1e040c0300740307941e101d000040d1718120482d02011084800341c6542d10080d0501003924104032007080111000e600409095041114100f1800000c0440312002d500422a11074001004445031060210034a050751003140718001090030000303100c0d02d0403100c0350321511805480b80040c083d030407007071003210b450f040541c0c010802048001700c940c1c121000740156a682 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 383640593 1250 383639343 383639351
    0x1120e07061b02012003070b0a1a03012703050403020607030806100801060815061306030e0d020118020d080d02040320030109020f13060803071a1b030606090112050a050604 76
    0x11991195500b110060024000342402050005100122501910031410381c8103036842d186554880ca00310303c0c02034507c1c170350040e0b88442000186000c40b0390010b40d02400d800030b10461006190b40401c2c03122510220341c1c3d030440c00c032051040603c65021540910341c0188030030745a1019050003840404110f8142d400f44c0c582c040c41880e1540690401030480c1c0c1e941c0e41c1e101281d41da07490364036401240241d0082c1c000030148401d210340f0081000c0d400183c2442d940000758206003101d420325114103e03102c203056900d0031500c03902c55099008140c0b05660140d401b489014280e2800e01350b2031080001c022035031440440c010040102d1150340c4000407541e809950b8048900c01e080508907414588000d50103c013091000e080d9003404049003045c890441000100c850345c60450318110303402030004451405180c2d0344d044c00000030035800e035044031251040000065070a01d00c200d2601c40a00110312500d00407880342c01d41d130710a1501664808a80354248040d04002c02040e000e040c00b0b40f0f80038421410 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 383641843 1250 383640593 383640617
    0x1091e030314030405060a0c0509040c18060906170717071206050603010e040b090f12040305010f060e07050d0b0a030b040203060702010b100302090a03020607080408070816060e01120e0706 83
    0x500010f9078040c035000000350009072282d039008001403040c100800700340042806916440d036a071784030f103c051404503164034908003100300d5420a8810f980d0001e60910111340003e00c400c65000500603940c17201c81d03180d07403082c0c1c0314542c0503034042c2d807c0b5040000c403446900030003680643c880a01030f00c00c0c01e840030502c1210344074002c004c0c0c140001d0037090710b8590a03800050201e410410714541204141064071001105401d40d40c0c20640f50025600261000080402c104142442140700780a41c0c2c14041011500f8038448401407030303010704100b04000e00854081110310250740300c401c0c40d136002030008045580e6440c2940e2584c0e4100d5090388680a03500010300a140180580d83c0c0300600100341d9516404802ca0981c025001062020742140c00d071107011005031034800040030300d03500802103541c90b50315049169240044a81200f24503801c42d044145503610790119000961380c1e2800c058001609060040f1440421402c80301038981c20300503000140d0034041040702c01d840c46070352100d03030441c0307 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 383643093 1250 383641843 383641877
    0x319020d1206061713061a030610050d0b0702070b13051306062c06040305030c0d11030403020d03050c2a04020306090609041e05240402031b01091e0303 67
    0x20b40d210b03d03404524925003105441c4038450045520038500b80ca0b840b0560072580b2a403003100d282c000300410340003440750480d00b1841c0401800754800e6880300e41075803450a05000c120205501d200c014802c00e916800304002d01e0083c002680908500300c0e41c1600c0c1c03207801075001c400e40c0c1c0d43c1c461240149048091000303a1546802404140d038150780311401c10720840780f45408003d11003807200e1400580342080303115030341c0ca40005100541c020001540c6a1800808003803e008a07502c84c001071084007051034958081c0031081d50304981d0101e83c05450490365040c15200d501c01c40d12001c0607030007030080810801d241002007040440201c032034244032440c20340c244403c034842694103e92210700c1d030000800624048200c80d83c880e2207031440481042024030300c0c00f42a0002c20003244c690f0000e142808032610756601c00312000a091851035103d0801c0d4000c179132582040b001d03e40c4070410358840303840542d0181e000742c030040038402c46400d0000440c48603090740d00d0050100f04e000910b22203003088040 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 383644343 1250 383643093 383643101
    0x130b0702060717060418080a0e0613060302090607120c061b0e040c032409110a0f0c050c03151509010803040e040606030209130b06030d021506030319020d12 69
    0xc1d038503202c000280c3d200f504450320740b940040c8501d90060315803d00140d1104100e1580d50b406100c5d4000c55142c4400301405408400c01030400b0780a070800740001c658030500741c070034182100c0490900694586403100480d40a100303e4001410020101da01400300b070303a004c11003e41007401a041007090360b9156030a5000501d08030700d408000b8030b5210742c50049190681c072240c42e40460307040c0044c03c0800c091700c110b040a000b540c03001901c1e450000800c28201075009076141c0d2400d03410030514200007000702621020300c0c0b445140410000c0c00c1c0680c01c22404011010301c03940001e00300c035490301e40c078180040301c02011201420a05008030180d1068101507032a54143c3d1a01005142803e00741081c1d08102903004000361407482d220f000c00000f50304e9001105000b050044c50701c1035007019604043c10382c4080605001d00940c04068260601c550204401c2500c01c0c800a00980d40d03125800000c0c918051603440940ca0980c040484000c540c0024000d1400341d610b4468002c440c44e4800900211 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 383645593 1250 383644343 383644351
    0x30f0f0f1d121204031103030301030201050706090c05030111280c1b0e240108150402090d050303070e031c0c060c110f060712090203030409050402030a0b130b070206 73
    0xc51500140014103040501c400d048840c005082e0b040c14100000e00107240c402540c141100c3c0c444006014000e2068590041d03040f03050546c020740c99940355500003400c902c82d41c0030185c0307510390303482c02e405c03c1100c404032503801007070010024800c01e0348002c1807030100d03030050044111a08043c803250803c403040340c144c001d101030b01e0f0701d4408e0045e005494512942e4405449080c501c2e0141401040d40c64520f0725050091000000c1c8800c04034200c0ca03030000d200a0750800c0c03814031040100f0848800c1d2190702d015661201507c015031248001c0010a40041d2082001031581c0408402c10806551003003588504180440480743d4141c60031411070001c01803c80003000081030401d100d00464a03a400040301038aa41c0b612010003080c42c0701080c2480303410440c20825030050360030702510035031001e0007808801c0e070345a0800c100b21455001940e01d03c19841070700d601c180c4032000901559010300400002c039070894010881c628100868070713403048900c40100c6103080f5203000301d000188009000c500c1 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 383646843 1250 383645593 383645597
    0x30705060a0f050c070e07080a0506031b0604091404051e0c1c0b090f070902160b1005120a020102010606080906040f08040f0b0d060503030703050d090602040b07030f0f0f 75
    0x74100d01c1000840d28070204410040074000b0402c0031100c0d400d41088094000c2001c40d242c00c0081c00c240000801106000d01401e90040c245014031199990100b04801d0107520b4482c1200e88000c080301240150007598030001c0c845140140201d46054240000e502c2a440781781036034580c0d0300f0304c540c0c1d03100c41c125641c540c0c00d141d00510007500c06041c85460b105207043c81020341c400050060355001100b120417a888403075a08203485014100302e04011303540113011408401d509241c109200c8200c401428200540442d2280000c84c1203401048440005080050008042c031000302c088031340e4800c92541700700c1c01907203003510001e00c03240300b404c00340c0c01403c03260060207042d1916100c041e030f0407072042815100b28208100000300d41481140072401401c441d001d898888046c6180032080703034541c1c2c0c400c5010b0f0300100141f9001940c01022100ca0181e62200090a003445080042c028001c98018800340316001a0071002d02d5006010b10040558656403184402002c4108a441000000a00d00 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 383648093 1250 383646843 383646847
    0x3090709051e0106030b0108010f060c060906020d0c180b070c05100e0310150b030f010b1605070b070b180303060d030e04060f0302090f040b0613090c030503130503070506 75
    0x9644215004903401c5440c080000c1d84490b0b00684500c0800c0007a030041004c25030b5120301700c0d1256000304003540103104030003030f05820a1030300f10043c00c4900f81441c000c02c0c40303645105000030408035605441521503441d10400000f0950000605040f02c19000507452824000d00001c180011400315101203030300503044541e0605c0c001c00d1102c450301000c06030080c448903000132040c544040002c00145c24060f600821005030005c103524400c00c050b080030003070020800030400d046182e003020904640d400d514050317445920200d003084854410000a2603400b070f070305002904080c0e0700b014040c41806000c8080950300c80d06071303404900b403036915100c4058005000081292800c02904c2c50014020300f00304900300188000075003110116003100b10303403605120342801582000d01030306512500c0307600090742d5401c1c0740d02c0b5007803000b000030482445140e00b41c070320441c2c14140b9003040083c164803d00481e00c0d0f0b61249800c940b250030074110a4031011080100084601d00000c4040c00c444019100c4d078 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 383649343 1250 383648093 383648099
    0x30903050601030320010b2b12080a1103090604030507050f1c030506030105060a051306090e0114090d0504030204050402012f0d0302040302180a0e0604030203180603010e1323160605030907 83
    0x7041d07205030402c800d441101502860100700109d1403030209940a5640c29200d00c5c080a000c0b085a00c3c601c22000d20030300600421612041c001a459005070305802c1090b01d07174090345080e23440c2c0310102800e21503900038005941e41803408106001c41504040e18244180e68428040c18203c074400c840c00e9500204000007004503080040314082d0319803070002c012607801c1d103420440e800d458203145030030000d07959a141025449290382c40310307800440180c080d04c901261900028151300980c00080c0c80f440c0e481c4045811a0b00034181c04408001230780313021300c0d00701155a5500c556400400d031419180109204604140d20034403c41c1c064a40c0181040c418008840c001c0c50000801841c03008110b548600d1210007190801102d4451072003a8025540c407985044104e0410181c6d80031a40251018030040c00005003038000a41d01640243e00c010384a003a030300703000e246504803030810501c0c0b507000076220042020210702000062f02c1e0143c040c140380c0d5038800445035072000b1a00300c1015000b020080c = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 383650593 1250 383649343 383649379
    0x70e031504080906130e060109030c03171b0109030e150a0e12120d0f0203042102011b20061b07050a0501021c05131e030903050601030320010b 63
    0x8140c0181c001c0c01410f007048403860210303615070711074103105a01001136541006051166010194070860078078050309a030f031950380d94040c4003450740030003420101c002d036000c00010300d00c80030b840710102000540280c0e171100b607141500074071343ca2006400280c00e40c000300345141004e400031156920070036071441ca81001c4c902e003240c4901c5503940440d4886207004007001d1946e020440840e0320401004107a40d544881d1720500110703480c140600708070030b0040c02007002040599044024202c00d550011361040c0314504120700500d441d216010071048041541500079900004200701d0031856081d100c501950840030581e11842210407100780700e500c040395400c54070900090f2103018416821909032400070f5a4003030a80e0421440f60545030882c0c83d811001c0080390161a800841c102c4500725012215201c1e00030038400f010111560040382d403041e408040c400d0b4805001160070409036100e5503141c0c40c004020540a4602c0d5446403101008650892018841d0421020000700140610b00c006022 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 383651843 1250 383650593 383650633
    0x30c1d01060813110904121b030c03030c03020913060504060608061f1404090b01351b0d0605150a08070c0c03081204060c1d120a050d020f06070e03 65
    0x4036108004c2c00e00391003580d01c07018070580c010b62240341101c00f4141350020040465078040103800500c00350001503004641c010303810307a01058243c9004109211401d201f83c001e0301c0b64843d01500203d0410a844006030796611810640d1005c507400e000940d510b5404403181241502c1c910341c03000350a0340341c0e0400618801e45240700c0416042c810000120032640995a802aa00070004242c1303030400d80e195903900c62048203002420008021020450f02e0100a0600d40c207000e1940700900d00010594521028400506901c000d00b03109030758403040c41001c0302a0480c0e200313890151140c1d02240d004a024401600c000010607030f1800304994401000321201c441d030003000c2e6040e0b44045008004265404023715404a007400c03100a58100f9141070030845501107960020418401403040402b41090980c02880d00c04990030320150740154400b6041856240d402007445c458030303103415685600031651040103804031013a0b6200b81d403108000c0c0c600840840010703038190800309034048100201d0107 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 383653093 1250 383651843 383651881
    0x10812090d1a16031d0d08180a1b0906080303071218230d050405040b130615090506040b030f091038060405010c1407030c1d010608 58
    0x201820502d10864008101c1a00c2a01e0081c95a02e4960050400c03613018021000c580c02c480c8206583c5108450140361075050800c46401080201800318442c9281182c07082140c01461050754503034905860407001e420241c8484080300708010f10000f8060429200d201e00722421800654519600e400c01252404007134814045019940d80b0007000c28402160280c1c00a44282410b0781002c4c40d140781c008034407000f0100b0002950280041940441c0d0007010f45007207550540e070200340100d001c0006003403950074010801c16945403c20004081c130841d1015481800e030390701c9403103182c0d8503001480f880d840b40c1c1c050b00903a4201040071030303401c0c0c803c00580c3e40d11000c86410380710f411407504036003026220082544080e45040c010000080c040e00c014400004043d401c86468039045900071441c640210f01c1380702e050101c620401428000e4000706512021102c2050b240071310388900e05290443e130b0302d015a100b007400904071094a080000c80c4241a1811915420820b0340c503000b18200b4048074803 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 383654343 1250 383653093 383653103
    0x60806091b0304240207020f120304060c0c09020c0705010f0c1a06060d0e1b0d17070201050d0c031e140433020d0c17010605130e1806010812090d 64
    0x101c450120320824401d404131010a0840140c1e40b403071a4010488140c5411680521541c9150072180b00038000200711401c0b601c44ac204401c07081c2c0c4505203440d106245601100c0c2d41da00001d8080350320f000104804007641c0f0b098940000c01229220101c4441c0f01c030520007003100b0101c6000d0030440d0b100301a407940c8550018855454114a84000010b0b00d541621045207640051001164500440146801c00ca0191441c220350b9030141c0340c410050310000c095440c82040012004156486902200c401d140c403030700c0070300030811004802402801078440f10851b144031071108910301d05070360103095454101030240c140e40c3e4440b82c807400c074581104061405070516030300034009201c1c401003007000d04091002005868481411108065404003040c050801116610700ba0403103181d00d14283c10340b400b5292480d100e03080d001031144a04403a8001e400051f0a407030400c208403200400d0f0810f80000e40b07080c0c07529039903513001040e9503240301c00101303040350810b100c4140607050000c0c04640c064051 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 383655593 1250 383654343 383654363
    0x5040c030627060f020f0a030606021e06010b030a0e0708070302010e040504082b090f0c09020316120b0409110a0f14010e060d2f03070f0806030c030313060806091b0304 74
    0x40b01c6c1c0c030305140d0f11584618011944800c410000300e9014010454840d14049090300201d9600071559110141401030607511701000c0f000c241d841a0580c840c0010491850841d4009520ac1030100e60700c0d200307480101e00080a6110040b010706050064a002c2c0b0790003101c05040101105080b001074084543d61002179140d0002e882d82c40b081c5004015481d40584100b0800e54118203240c0c40380030694011820a0340100244200400303010b04507d0080358601e1300126001403c030045001c0c2618108080c6e04c1401e0050740400c0c00150812400710b404100e80701029035548040e4880400e4003032081c3c20b07030780c01601c0d1000d4085d40501140042d4080081c051413500c00041220001c481c0e24285902800c0307141a41c21a1060f0080040c0c050305012030051415843e007039800500000c2940c0b01002081000000304405071000c0145001c408801015291a404030101c60020010343e4450300000a05140101d510341c2030841c5072a005d49014960b60040c19210f4100402580c4082d00496201c900c0d = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 383656843 1250 383655593 383655607
    0xc0901050a1b061a041a060702151c0f0c0e0f060706060e0705190201112a07080102210408030703021c050903040905010501020d0c02090601030b0405040c030627060f02 74
    0x2503104020040001900c200c52090b400414071044900281150f59451b0000186003074903039502040d5940789504982034580302250780b02c0141c0d80d010b0f82c2c1b00d60000301403003586030b0700403c010303001803259a03040042081001280f980c21103411950f408030b00e41015581c03590081d1420101c00400310302c1c0c01200c010070708541d100c94101c1080411104000042e40100e00c22100030040305942444004a10092256900d090740b00c0c00b540c8140c0202000154107403462062500711f4a11076410229411705650b900b50b40c500040b03010b503000402c01c80e5440c0b0b089200034801008560280e0090b80c000c8420b0f4119601c00a0550007540b0060b0201304480700140310000c1000c943c02103500c50780d01000555207032442c10520005031401a003049043d034010282840086510000c0e03140c1c11a01282c20801940750700006800810019102075007003828041007005000d480c605030011640305000c10846400000702084695050054000b595000c2005603800700c0e1498118422a04080500500d8201 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 383658093 1250 383656843 383656853
    0x30f0b090a0507110f0a030906050f03070e1f0f08160e040b0d1209090f18030f051603080f010e040206030a020307021507030e06010504061202040908040506040e010e0c0901050a1b 79
    0x28821540031941c0e4005001c40c800c065200403082300034402420010f00780b00310b0084c0d1000500004050702c08110100c1f420b440e241d030751906080a07240e0b40740088800001c01400c0103046981161020020580903004034a401d10000d0180200c096030341e44080b21200e0003000c00029000452103690710500c02a4020042078403801c499451610366280c084c499403600c031081c41524019400080160700d80001d180200740c0304041e010030b5a0745032a00e148070508403041501c0b18000c144002d0010303e902e5116104064011032102e000d4590728080411582c0d03160464800064210b4000f0b400440500100d18003100a030095604607000340140c0741c000a21510140c1c0340c003400c45100e00040d49500100106000521405000d864240ca05000960500b401880840307e03000c0b00901482d5140c040c541131100420583d0003500c0000e0201d40e84a41d5030400010b503410a000314104c0080c2c0e280820020f00c102c508075111104c040e10b82a0070150b03004803e07a000c2c01c103141c0c41030b405021011083c000030 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 383659343 1250 383658093 383658103
    0xc011512020925020708010b010318121205161707020a0b09010b100e04050a0e0c100504091b020f03041202060c3a02160b090105070c08030307030f0b090a050711 71
    0x103000f950040109034604050582541d4425170954140340c0b17403103512042d02c000300340707804104c64206240000c4940f49800880b500013060f001039240510300420b02008040d9005100144074a40d07480d82c11425040710700b64030980064640c43c000d40d001d2480c00c0001000c046905922407208000040c2001a81c0c01150656541a0090300020048080c1d0200c903d801d1203841d41002c3d440340c040110031280c0e05140d41d191103407600c0074403840c0c042d0441c141843c4078004640c003811000790207001078101c1012070001c2c44402c0030100054011584117464061380082a40e04481d002c5082d500c60794515020311440c0d030b00601e0a1805409441c51041c2150f03010002004d203070301c640d03071250b88510403805066800302d00551040f045421546084900b02d00100040c1c0c1540c01d00d207600350b60342c4003920060b50b2038461030000520a584001c4c00003104200400910b00c24800c03600c00f48554413103007402004550031119075560040304003000c5541c540895203c00d520060b2400c3c8596405c1c5021610b030b16107 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 383660593 1250 383659343 383659411
    0x8010e070f26160f050103050a020702012109050a051507080c0f090a0302100801030c05010f05030c0d09140307050613050a03030b01300b040b0303030112030c080a050c0115120209 79
    0x50713a01e5000c10480c9580c5446501d82c4003c0501c021803c2411a900003010254122030303920a23001514810240070515030300885116610808554551840745002d030b44401000d00100e00110640000851103805030401c0c601c222040c1000c185080040010070b002904507416050b0001d1402c400440140c84444030705400d05a680c130ec428080d80345140440e200d80880e0040c6040249103020054000e41100a990300b0422501515454442e04000d0000030719021101409101c0c40c256501240b000c00700c010701c03140380038500307581e03c2d6a0b030384e00113403000003d4180041c0507178041964031010a210354822203480030145400c0c0340c40403081740d60410301c1d002e68400d03448038440034192603107034603d40c420070214030130584041c80048100d100082c0c0301e01052042c00b008810b034800e20b0b0100b511031000c2140050b03100000549604c5166030040c641e40021141d00d2107507281000e40c0e802c01d900022040c1c11541d000568982c0c1703100590070310402c0d410260171889006860709850014001140340c13000c407 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 383661843 1250 383660593 383660609
    0xc1005090a020a15090b0c010f0603120f0c030c031d03010501090c030b180c070f02090a02030a0b030c03100b010909021207170f01090207020d020a08010e070f2616 72
    0x1c4004180100403984046078025185034010002880303801360440c103000c0440d46510203880e16840d145810034003400e002e070080c03025145030843c048200091401d80f803c04000304d55a000300d03070095440035500c0c003401c1c0e00d001d00415001504440000c0c8280110b084000601201d160000909000709080d40d82c281c020004090311001180f0580d5814807441e10310070021115100c56a032508940500c0310f002501d03034a9007c1002a080041c818800c044034034040d4050076121b42c91810000700300c000c0d08181c0d00e039a0030034200a01403d183c40c0004070300c404072030010f020b0002c91410f095003800418468040b18140501800e0010381e80c922440500703644e110425002895260000008041c0429660903a403184500814800e098200c1150f00c0c1c15200c1200c00140c1e1038a0900010b6001c4440500c02544042880400300d040c09064100f9104041c0240840b51505c1d10385d40b80c010000b1703550042c0840c1c0341d00721428501580c8001000901c10940c0c2040e00d080d07020201c0044540c01c13498200c412 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 383663093 1250 383661843 383661853
    0x124300201030902040e1c08011202010e060c12040e0a05042003010b090118050f0c0d05041a04050a05060115020303060f06040e070504080715020a1101030b0613031709030d050c100509 81
    0x700504401031f51803264030441c07030203880340e604103003501c01c201a400034084c0c10080b40209916aa40310030040701c0350006a03200b160400900a8a42112540140900d140c000e0000303011070851055030068500465000c50703241c4030b045900003082e0b49401c0790b10300558150341302e07504140c9680b54040007a0280400e40740c004100d081b0788023000140d950282c1540c43e118046410002f800c941d010650f045e000594002040f65192030030140c000402d018000401e10400e0003c0c84100140058640340980c0302d00c1c240d0311960b90700d02504902c07803035a41c000000740e082080014114603209031ba0940c3d01500910303007818241c444171b0368240e81c9400c8840d4270101e140000c06200400c02046254018410f580d00e002d02109040e000a444003c0d0301c0c001803120011034282c0d019680280c201070f283d0080504296129001180000750751605c43c403059a0040200009001c2d9002a904407600004080d000b00890300610000b211702d9817203030301c114405000340b0586080d00c1026020b401d0288000c0702c0108 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 383664343 1250 383663093 383663113
    0x90a1701060f0e010e07020c060d0b0a060f05040b0c0703170c120f04150c0210020106030303060909080f0a110a0b0103020f030604170703030e0124300201030902040e 73
    0x182151203542000c0d00500b02c18108022504908289034199401680c03803e2041d21030306c2003680781050300e0062030362040011a82101d03488844d840485650002c5035104141540c41342c09840044501c41c48100140f030822040c030400540d039004202c1108010211401596241c031089070980032b41c804980001400a22000d0088041000315090801c2d2485181744c07141e00e440f0048140310700c0c890300240a4407040e41d51960750241d00d800720b4003a009404c1c0340c445820000003d000b008503000c1140464a403100110343e0b10070701d2180100e040d0740540d00e01e241c28802e00c1d034018a5003120038090108082c080401643d01e030103102c01c99081c0d2040e6480822035065104000d968080c10104602a500100800c130205142180304c901d5071124180c01a910714507428224050600f1042104071982040c0c168030519140000c2c80c054006010b008490244d120001441c0005182070f811021480882d001c1d04a40d0380c0442c400d40745841410f000800708110707400318040d51074101c40c041103034108a4441c = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 383665593 1250 383664343 383664389
    0xf06040f05120d080a0507020c090712060806040c0e0c0f0c010504060e031911030d150501030e030c0c220c020c010f020d021e01060f08060118090b0615090a 69
    0x440721840b1a6009014007200c2c12200030301c255401410401103a80700c402184140d03000b40044001450003070034940745487c1155001d0070350200300c031100c59482d1418900140d0b518001c00c180c0d0003264803e4a8410182c50845130145102010b0002180380e41c1c1004200003010380c502c01002d10040300000890280380501303006049406000c1c404907103030802c0005500d46040b05c92051070640300e504008850002c266240e902c0d500885060a00359440c00c0800d000308505800c0110071034600740d80c2400414510f00c3e285859014180008810394021081d980d01860724840c202110340441c075400c0b0b6050300c2c1d00919400d0f244090020005038101060017011960b0003c0007541413819030000300040120820000e54605185541102d440d00c148410303800c1d40400c0d0801d9004007124a0200f50300c0b6211014282c8601003803085120040b0b5088607507008a40702d009440c00c02d030b0440c0948003036030344030390601c10814000040b2450600c070030041280c2540d51080c01314060480040b8028a01c203145407a = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 383666843 1250 383665593 383665609
    0xb06180405070806220204090216140304030f2d030c110609030a02041d01050709060906170711120a12050a1b0f0201141509070e15090f06040f05 64
    0x2000041001620130441c41c2c1e15452070b000741c0d080100340d503643d9820384501d80c24001c1c01142c202c4141180001455100104104a00c18810b4003400c0025140c00c80c8070302c075940e00d2140784402404444613003c2d00012600c1c40c050045609000785102469000c0c003400740303005400800023207003c2071900c83d0380ca05002c03a02c6540070001030150784640ca4071245070006585e0f0640c11000030b10558481048103c600d009008a0910b000100001e1080e42002107001c0c120070501d000380c100194004c4c40018085100d0840e403503c419074440b4103c1c45840307841c8221000d000b092521000c51295055290400da0600024102d40b01e142c2e6078005101e19011510050710310150056001c2410a80d0710840806160501d8001c0161410b01802c5006500340c00e80c05807028515447e186c64524040040401c0c140132811140c1c00225244016560790404c2501c00054420500b50090440305885801140c0d26000346001e800c018840c3c040070303c0180000b01e541d4407942050100c440c0d43e4070100218200084 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 383668093 1250 383666843 383666851
    0x303030203091902011b0c0f0b25020a060e010c0f061d010209100807110709020304150504051b06040e09010b03150403080f1504140402010908010c1e02010b06180405 73
    0xc0100042e031096000207003000c00c2044551084a0040407146c1003000c0011010014444c80c4080041241e640ea041c443c1504401100032804580c200c04030407600e46052080c00081e07000305040134082c24200125500c00f240c0e14030782c1c1400159101000821184e40044014034070070000461100c400041c4107901d40e840a5452032203070300500008155a480030325400100c811441e0201044d540c0100c12220342c0030001003200280164a0040303000001d0750001c5119500801089100084640740700e01141c0041794058600d0f00814561100d4580c1d00c00707502c985c140001c1215050035200c001d00c4080200603034041900307070364402d9410550305042c0018040610040382402d02450592030141448070001c215029004c0d030440001c03484400c0c6103001c6000000600300b00a505903903d1255038280080d14164013041c03020900003a86041409404080380d0150703180c5d0310007801c3c0e17074001c2208015151188103554031690082440d403640e601601c1007030442c0141c441000c0000080c84100c03600a4 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 383669343 1250 383668093 383668123
    0xd0f0e0706090f0b030c040b0703020102030402042a200d180801051e0c0f0d0b0112180813170706030c050a08070c050c04051806090102181201110301030303020309 72
    0x800c100b01c2c03440500100c4040344e60003c4d81942d00d9540415922080c81a9040110b442d107021440e8800d0590544c0518030841c802d903010407510b00b0540546000015880584074007541c002c035140b0300244108001c488d60b070b20001484010080d00c805041c00c090a0f9076907000022140c042420802d03038200e0300c1c0e0004101d19802000103040c00c0071200c200100440c40f40b01c46113240070100b0035007804e070001c641c19021a0f8042e59214812254070348098100036254a00280302c0c0d8803003d404110a00c00d85107500f0040c2c04140302000107540d0002c1e00e07000b0201c40e140d0032244203170028007501c0c40341c0300100070880000500844e50403e000070341107500d035019403000c01c0001d0000d030401e10b400c900030b2a000a4581482c51210666117045403902e100c07418810307001824007040c0305102c141c2e00c86c2080f0a07410381c0b0945035a592100521805c03800340a03c0040c0a01d0300c0300704400340f41000364030803654441c0e03180007048900c0c000c68640000c3d8400e0b0320460000e40e002080182003e0140444401c8038040 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 383670593 1250 383669343 383669357
    0xd03050a0b100f09030b01091a0a14010c1403030108030a020d0201021206010e2205061c020906012607051207030b09040602031012060b030d0503040c1202060d0f0e0706 74
    0xc0310110341c540c0420b064050601030225802001c407030003100100d0080d58050319044407903031594140d4028161080f00e0203000d48621000d59258500500c984068404482c0356641c0c041030310004645489030303120251540090039140c0519024148011070107003503d1401541d83c0c000c0d604d8000e18102c41c00d03004804591041c420303014007442c0b04102c10b402c0b03102403a08003402c400711000184000000030003441040c810018842d00c030070468200522601c0e04940780c080c20901d0358214200c2101c00b00e4029032280d0381c031001440540c0100c0c0c41c142c060341c0e8061150441100c0e0099107906000607141030010a1000c134002d4040c0c80c0031030100394465410303c0c09010041c80c07940802d1076010080c0000f0140c85d00440020050b6100710312080040c02107416203086200360382090320041040d80591350180c0070700c4003504100c60150088a00440e80100035a483c0303403401505011540d88504220303400802001141c1a2542a018094046040395000200c810300c44050900d040b403a68044420300c111 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 383671843 1250 383670593 383670611
    0x6040f120807080f0c1e04210c270216120201061d070306050d0602070213060803030f060105092205010f0803032206020d0f0501090515060d06080f100c0518060c0109080c0d03050a 79
    0x40400100322140541842e00ac4040c40480584038603018070402e24092000c0360007070115403001400c0d01c1190140408000d01e08039140100e00b80ca10500806802e00a00344581daa03003210a9403140e4003815510340040c1d4181c440b000204120181c1000b035401a40100b81c0b0030075440d01c8042c108080800c440108555498800c840b40c80e0700006229400c5140c843e0005280e507406a021241c0f503140081c655034000c0c0348500c0ca01d242c545198445002580380400102e072018441402c2826181c407400110b085079035000c0741c42124150810354107407170302c650002c060011700940058005014111800300f03100b808032113038404442d01640800760f0541401c2c01d0084040308203000e040c140c00e048e928145e450421418240281030b540d400f54256109140d520b072101c001c00303d84100b00f010861006d1254510000b0111942e0141c80c81d51a03603090b5000000959140050040c515040031500209004c1420388400ca640d030041c5580640c01d40100305d144c0140755140c45803e0f03008030355190030415155 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 383673093 1250 383671843 383671853
    0x60a0b0a030305090406080316050f010b011b06060815060414280b03070b07051006061709010f060611070501080c071b0806040f120807080f0c1e0421 66
    0x4640d01c8090144000002c2d4200303252100d0304410007920084c3c08980d0b6800348008441034484030403001382e809010350f004800c01184c06009007004500160740300518490440f00c411140d0010b107074101da44070f9945000050300d540c2801017201c104c5100c00300032094070b07204050000b92019800303011030720301c07031b0034104121009026071b00c19000f0440d130200a8a000440b0081e4003c0c4102601c0d503078948a10480001c1212201004200e8180300e0310984040050350340d00c20003030301c40038061000030549081c00344200220350300c059580001c3c10340000c02c81044901d07a00c802c075207094020100094005140003000441000540010b000c280381045403480c0803480d14600e40111000180410783c86036a40e0640880e208200c005485650240c0351541401d00c0c1c00905940302d018200e440f4108400303414040c2c0d000c2c0388004e04c1061152680c2c0301ea1340c4c9181d281d200c0204000d0043c010400306000f11500e00071001088010000b040c04003a0b5600d04140341050035100103914104500405c180d8100051 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 383674343 1250 383673093 383673109
    0x1170a15270e070b0c030306150c0a0f02011205090c042403020f0d05070b04080601050108060f0f0324090f06011206020307020a02060f0703030e0102090a060809150711060a0b 77
    0x140450300c0000e1100000d090b643c02c280a0354050443d40302c011644060b0744c0c402100941c0101021101a0042d1001c9564a0481d00030300902e03120302e0704184003403804101081d01740c44006205141c5003081e01000c410000c21680156200f80307859108030f8003e1111300302441040da138602e84070800906803000071110040c1d80b0380750000034000c0e030810350310f10302540750100b5000600780c0c030005444c0081d882d121460035507040391107800c007a0310a0300000209035000f070300114018403000c1c00b00c0700800392902c240700315424500c6003650103104001040400010150310740035520380a207503001d550308040392600d150141280c1107941c980c000c100100003500d40c0c5003088803010780c030034005070312903803880c0060741098285400a500701200040d180000ac1c81e40707008008262003501c0c204003001034501210300301c0c0924a42c0c240c101c01c45d90420b11003140034080d9150300074240001c441100021884c0c12141d000207540c0803000c0f0300703081e4031142c2c0d941040c010b4662002c1c4000040003803c200c400019010 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 383675593 1250 383674343 383674409
    0xb011814010e01081314070e09030705100b0907030b030a05030a050714010b01210b06070602040513140c13120c0e01080c1008093a031a060901170a15 66
    0x40340e00e03520341c0448200107002c01d8001b040031981e208e20500d020090240c03603030300081049800b8007905912a50407907141c840d82201c0314000e0503481469580001c00d900074802051440d07414070814191000140080005004000c92541c5560710742c07000f41340040d407181840c1850200c6034100301080c14140d0344612421450344050010003400c500c3c000950303008044014415800440c001002820300000f500200121201600d028010f5015441c691040341e8954103400c056108a5000c24080d20621000e000c11500341c170110b603011a82d800016032643c1b50800d084510079889001041507601c614201801040c081010303001102c07201000449000c41040c0f05014411204007040c0284030400441486c10745142c2c1c0c0380036915800c0c0890a204840d1904a507214a4607403c07c40b03034611074020042d0b0190345003040c0c1101210582040040d4208a0b9280e0400c0b02504240a0300030341c0390111030058601d44400030300d10a035000c0c065408801030304034880c80008080a40b91003c802c140f00c50203 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 383676843 1250 383675593 383675603
    0x1106061c03050c250e0f1603020d0513020301060807140d140f060405010606050403031202030406090803010b0a08010510120e0c03010f0e0c010c050706030b011814010e010813 77
    0x403140240c98196124060b1103032103079203442440e0100700464150720340e5034544505200300b140d0203039aa007401c90340f624045461010000214010034841d50102560030044c00e42400c025040c414000e000b1000c9032000c40b00e0741400500d5000d040150b04082c0704501c003030544d40d0041c04145017040e14129a54041c00000340c001d01c20070403600244001c0a044180602070507060360329400e140040142e4410b030544013520325500e490070008059019000715030442e0744c180c55000008440401c1c0c0b10007034000030000d950058031181e181d000100301034000c40c081c00b030141c1c04a44402da0340400620291050304241e0243c92050700d441241c6812076014074041165001c00f1860112540340e290429400031191505982004445214421039800107034000c00303010129048a0702c41001140d01007009480580180c0056900303005442c466080300c410303054107040090b0080012030f007401c2d542145034002e102c28802e20170300040c07540e40f0a100020030a07091800c4181400c0002a03011060048840286 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 383678093 1250 383676843 383676889
    0x40c020303010b030f060d06140910051012080d0606110706050708070f051e030405150406081f0b12011404060f06030902010c02060a020c010206250f031409070501110606 75
    0x1074550b0f1400b007c2c02c46994840d005220380035401105000711142503481400074001c1140741c20003400d00c1d1207902d2207100c3c0c1f1600070141c2c0789466040303151082c42410075600d080c001c201c0c80c50b00c03400074007035100140300c1079440f00b04800c0e070a0015400c089441d0030400c10400c0810010740840c2603d41541c185541281103291071400625002d0320f041c50071004020720046418040341c8001020001d40304450090303a540c6c40c82d05a628251100e84107d000d04800720fa11200400d80041c22300c540c8070010744019419810f0962620032802c0b403900125034002e08a0401d038014800698401c0c8254030304102520244503403820411110a403e40d28040e0008043e921030055066a20410061302d40c2500502140da03a01c0b840780000307440780c07150019a0b015100b41004280b200d007600d81207080004c07e90340000700000d64040111400001c18510908064580d4144803404414551050152107000001d10384185400c001410204104241541e503400c05410480103481d038005c1c204004040d894201 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 383679343 1250 383678093 383678101
    0x6030509030403062f0c0c1503040b040203070308031611030c0a1202010f0603140d080907050411090301020a020f0105070302070507031b030506010303020d17150f1201140402040c020303010b030f 86
    0x40c030703041d00441402d0700045c0b180d94003143c00300a400102801daa03100d003600c00c22a140010b101c101080d0084065070403208000040200c1d541a4005420500c0103065840c0c165807030b00c0303440c4a500184d844c081c280300c2d5040e4004c0a181c00c10248212640c42c80d000e10b0801110200d141d031504a070240c0a0007114066000300d1b9910300c00c0d881070442e80e28040041204a80b682803415244850400c698114131035030001000c000d00402407148100d510200401841e41010144000b61652052040e40d4010034441e0750b14580e003c0c0050a00040c0c10383c005c20000e0324602e021402e45034054407030f40a0610402a81c40845c10100d0711105803600042c0c80c040000e502100071b10440c0d11948040c00f03a0140d40008020140c2c08a1b40307011a45155850200b030040c400c030031305100201a00c04940c2c41106c0c49807180c2c00c1c1007076060b410b52000c00424a000f21484030048a0a42d603005d4080e0204921190401045103001e01c200e07000c02190303200071800c0d0343c18900314190a10015080140c5070802000213 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 383680593 1250 383679343 383679371
    0x50609010e22030e040905030d0e030f030a090807021e1e010f050f070503040b0a020c01030501050604121703090d0225230301021303020f04140604020705071208070b010603050903040306 82
    0x390f0080d00e800b170030811420945040040d1a5000514980f402d070f400c00d44007002100d400005c2c2c982c42c003510244d0600e1611100a450000e244072001140c441c0700c14010300c1c000d41e844200407035242900c0f07041245d40c00c01038000c1204c00c007a000341b140c0e8041c00502070420345903807180d19502c2c4981c95050403645c4a02f4440410114080d030003008005200005e40400c80c28044000f8001d04140c80d000c41c1c200840040054095410900031240c1002d41800b040204041096801d807000340690048102c09800140801d4a5070080380c1800c80d65000b0044400416810040401880c2c0ba000c22401509414194908a581c1c6840b50002d542d540102100d000d0100c441034504000004008554440d401650054000403620060b072050526682000071810a80524648032106d41d42042c03c940e40d200c1040000d4002c4901a40c0500c1540c0b03001c10a0941d001000c1c80190182c2d07626502d800386031810084010b4160040303001c0508200602201040c000140c1d003e484c1d00450100b850540c510b84 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 383681843 1250 383680593 383680607
    0x6100f0e102307120e031506130908130602300408010504030801051516060c09050409050304050f0307060c0201300c0e010e010c0f0206040b03070201050609010e2203 73
    0xc8010400490391102c421646400402e82103202c2e0404588000d6104001e68030340d1a9103008580540121b8002c1412900300404250301003001800e0003207a00e1910180c0c1c1c1100c003412412070300314030b0000700000d846030003d0075117000f080144001c110840c0b4155500b07945010014200025009241c8503aa503010500f050f10003504008000300502d20700f609008010036000c1c800e103400341804422020b0040c810504a602e61504a06400c511440507950304008042c04800c0d50708008920030080340075603990240d0080030b40242d00440d110303420b020800414059820b84d5074032940c45100c04100341600240e00909968090a198110307140d1200c15000c149540d0b000300245102203e42840c0070503032075025012188655483c140c214400000540740102504a91400700e034444d18030b100040c0f40c0c18526414584050a014103103580d03601d10320000d4105907810700140c4d4407038042140c40c0c01d025402d00d0040c46203500030390f55403c03d0120403180a421100b14080202400700c20f40070305020f014 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 383683093 1250 383681843 383681867
    0x6070f0501110a12060e01150f050409060f0302180103020a0b03060415091a040204261002160b0f010509010306020a020114070c021518060c0a06050403050306100f0e10 74
    0xd540c1d550fa0745000c40100710318000c24449124901d040030100e880445840428145c418220000205288180742603c162100020110410000308030101d102c401c18061030004244540c106050a4254030401c60900d04903840300e1104c0c82107c004002581e41c0c1d03100842103400001c0903680d80e480716004200900150102441c03040842d0f04000391901c03a5034485425003035110b0b0740d460420b4103142004260310491046104101002c0300b071110300c0c91007600b12141c0d900320030112124100c40130b400900b0303a04a100b40340e00d460b50020401062080264032540c0c031480b0000080c0c495810600003560454060001500c0780e9404502c440b6614000d6028203c0d986c04810b5141d56460591380040c040600c8400490044030340d01a80d85910585109451051080c0c100c4629000d020400780200c6030842141043d6900c62295640c021410038031034940540e00a42c1c80356903c0c500751003480540440b03003403103400300908541c9038042564080c81c90201079004881d0358014a03810001100e860074009 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 383684343 1250 383683093 383683121
    0x7050136080d090b1602010911010315053106080d05070f020904060b100201020c0c0907020a06060b030a06080a020f06030a1e0902192403110307020706030e0c06070f0501 75
    0x10001043c080c4e02ca440910800d418888021140e049110480c00d0380c41c000801804d20380f42c40350103600c96000c0d8000c481102d605081c1070100f40d03a650300080d074074414114065621591944000780c0304450600302d120326084058140205403610b04201e40c0c48400e003e241c001c0210101d103090800c0078003001820315135001001102d43e81014100180144841e40c1258031545005040080013401802a0b071501d038566006003030094060014807000307a0b8010006000c50140c0600c203400241c0314817841020741000e0505a459288c899104400c40c1c200743c110300c035a5444030a0f400c0050b600c19256903035842041d01c4107500d82e220140441c000d0151010340040d0b00c0e4415520210480c0d443e0700800350280202c800c2021003461001c0200d0740301c254002c4070fa40c2601000c40d100560148002002400e06900d00082c010040c60481000398005540070700c01038003d103108022080e4035000b500b803000d0500014086400043d030021703c651060010042c200000c02c950041440310a46c0010b183e85020 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 383685593 1250 383684343 383684351
    0x9070c0b0a1b020d180503070e04050c0a120312141f1a0306040f0203221104060806040317070c0201030f02040504140a110702060901050702040905070b07050136080d 73
    0x450b000b940703940002040301c0000340b0a10316204814000c074258811520043c0181040c0c5052100603221000010000d4a8a21400025020545845442c03c004201402442c03010b5802c900d00100900791000034000c0f403d00b0b00800c81540c4020f581c209802c14449507442c1100c00b0000014407940c3c402c2e030701ca14080b110400061450f0001900203520a0108541c10000d10614419050032808113941050030b0749551085420802c6501d900c10071b2207805002da84281040280000301981c807503810080360b40c2c1103201808100350300b003100226180c5400344040740a11f02004000d15180c40040040d04243d124503165910702410f5046030050a00a8000e211149401d52100e200c10002c3d2503203040c10f45020f40c402c400d42c014034243e4011030b030b00400c10380c5420800c100443d56030300040000d0364083d81c6d40010000091042150000030810907200540b40c44071414041c2c219a05c2108100901c0400c00c6681101d40d032002416105102501004194145e030f824225524011041018041494 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 383686843 1250 383685593 383685641
    0x312240301060605040504050105060a050a050d0209060a030e0606030604050c211207050d1d04021809070f0228020402032205010204030b1e061302070f0803041109070c0b0a 76
    0x4c0300006106459064400780036a91f030352000d12100b07206000018001520502966816030310840052400300754186d0054202000400000d41650200703580c4404290758001881c00389500748601079012404034040d09583c43c1c2902c134a40c0b10200680b4951066846044c10201a1b464139900d804661501040f1032012080784415032159104400551b000d101e022445402c8603c11606212000600545280c00071898400e10000c0d4108101c5445e2000c00011407140c0c03502c0707030214148031b024155131350701080d01c9801c0b02a00703005c0d5480070b2484c41c4030801d40420400d0306012001c41a1a815180180c4e02d603254a10400c107031a40718500d0317008801c104506c0c828072505401600c00d807030240c20074034410f4445000d00102d15070444141791320340840d04001451844c1c8483c0040104203a000050f1500d0304c103a0701c00c06500540c1a0071610002c0c04428032041c03000307000040310302100680d4442c0031420800c50142203418a01c0004119661075000110303805090780020140e003222080d11009512 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 383688093 1250 383686843 383686847
    0x604230a1814070303140a05040911040803070f060e01020c0604151506020c01090e01060c030f02121c0b010203031306020901141204050f0106060e060d02120408030403030b010203122403010606 85
    0x8a030303120030380001c2c0c60f28010005003d030790302c00c0307400f54047c0c0d07142d0b18a0301d0b2402d481c2c80c000d0170394014180f02c0028140400104c1c02003c0c00181080b6101c1c10800b055003440b4980319044440100030415a42e105001c1203903021000039210360050340060390200b00010140f0408007a0030518500c0c008500c600400140054000078030b000700705000d881d5518403030740703504151186400c24414800010016107a00e00030a0003030216103400c10261041c0c03038860300c01c59245441c61340715005041705021506180748810589100d120840c0a00344041c6145050840c04110400d988540160075a580054a480e89a002c2c2990000e514008014181c896146911684889204071010f0342c460107001c0f8401801441842980f00740c0d9903680351000c14842500030700c00781d5000300c102c50780c40b19400c10006a8403816800181d01c194444c1001d00e54078946481c0050950380050340c814150341c030134800b84840b44605868294420f40001d100801c031000220044900648500c07201d07055441c1c03401c0420555 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 383689343 1250 383688093 383688103
    0x507021903200d0f08130902030c0d0608013305090f04021201110f0d0b0901030501020703140717070305121009060614030f06060c070e0604230a1814 66
    0x21a0360498500d21004210600040c80e1115000512080e01a80c1280004d0030b40800f0741b800240e1004100c034403d40f94442c903400c03a0b00c01d0301c8003070307007a00d011803d114140c1d180c0c0142c00141954100a20a000425454180c000b0003d040075012151903180c142e4120141031601009000062600021782810103c8c201d20001c251026030040c201e014080c4440201406880620404108554a0300d100040702121039042017000790442c9407503024080099840c071524502039400380740010390310486407602070034000130200303505800c034800c2c00b103400480e041105d04144140403605040e65014146400c6606114102220501400e40c0701403210790049850740e02e082e0b4800c3c2c0c1c800c00c00d072500c070700003580c010841403414042d0500410004242203403200c2d485401890140209042c016600e204e00d007862030310307040b002810b0000030422450340f0b082d00820340715442c07540000c188a02d020300d05054a0200030815188691181c0c484240301e904114100c07a000c0c0c00141040081000c1c8007019140c0d = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 383690593 1250 383689343 383689373
    0xa1206030605061c030207031403070212100e0d08070302070204061d0a0b0a14040207030e100c030f0c080901031116140717030711061306030b010810060903030507021903 75
    0x30f26080c0c044c0c280c11041843e0a920350f15056001403800d986035503902c0110324000c41071411680000c4c040c980042c3c0b2f6180840d03450000750380c0901481a040803e40e0101c031040c009028241d40002600d0088030380081c0e940d6040342d40c5140140c1d40b840e035400403c0107880150f00803d00c041c0c3d040c500c0700164503071f010068001e50002c0414050b42c5040f0302040240c071000d000e01a6410321884000c0c0701850164000d001e05803203403c2003141d0f48914000100d805041590344008503d85922550425038442c00300143c0c0f02c41810111a581160384414020340107060302d5905040ea280d02010f4243c2020080d00d03048103125108140c06c0c0101c0c94120410780340d0202c505d486101d009000304101900040944440b04900025800d11825498084418100d990020342044041002c0b00300f42c100c0303440380320107001c058402140c0c0841650004211240c0106050300c0e909061400703000c921790010420040b283c0501d0495140c006900010f24020200360013120840d002c00f030000200030b900d030550140 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 383691843 1250 383690593 383690599
    0x2070818040e06061003200a021609050103030c140f0609030901090b0301030807020d060908160b070918150b04080a0213110702060309010b031509121305060a120603060506 76
    0x18000781c00b551582d07144000e5400070f83c045a00004908414031030382c008003200840220b002c420a05800014460754071a0940400503046000024500301e0385001c242c0091100182c03c0100b98515240141b6807004014020443c4000c44025407600d801040240410300016040c0d480c581443c1100759540d80c0090b08150205da0100400200c103045102a01c4c12030b80c0240001c0e240201660070050b00c288001001c80f03c16660303610303c5000c509040042c2104101030f003094420590307103041c55145448000d20010402c13100407014411a0313000c8046549004441d000850081d0b07074074050310164080c0f03820001e00d87d100441e00146a82e00003a0600310680260b0f031b92051408014201c9083d501e1444401928943c204005001814060011a40240c040700000380e5404002c0009050195507034800c0e5802d0106000e00841081c288449107031044c2c5035200e14a41507001c0042c40f0516814400d540c4076490100b03006c603400380a400c64a11400c15044204043c80d01c1c0e252180051100fa0780580c0 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 383693093 1250 383691843 383691851
    0x60334080705030d0c05070e0a23160e010e1816020a050d05091804060f05010b1312080702030a0503130b04050f0405070e0301020f071106090d1103010207081804 71
    0x224440c02045580548101401a088080c2d10040545a100c44902c0440d820310a01c880042c5207400100c0c0c00380240c240d0380740890a00240900119400c201113820504070480c4024404403200d501d0b1085114000c0b410100000c0c80c80302c0068801ea29104100ea802288913035000e140800c400c010f544c401c0103658003040c81c034814842c00f01d0351910b48050081c03030fa5102e000300d440340600036000b41c01e1a11005014484800d12103000358a1b24109841c11181c80c3d4680b098482d00085078003645000d040380f820030508100d0701a426502450303180c0300d06450f04228000c06824010060304640540350003904450340c0810600d001c50b0740368017032018800c0746d081710500032952804440032a02250320003042d0001c1242038000300801010050840024820310658a0f402901c0a002400c5000803003442e45031500001d0500402d01c030a04407465106043c2000002515603403031581d20710f1107801036180344860311840003080c02445001809084080b000c5a00355905944000e1a40b0380d40e07082e038041c0 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 383694343 1250 383693093 383693099
    0x6150e06090432090f0c01020a060906020f1603020c010e0f1e0607030903050105011202090a0c0201091e110405010803040e072106080c0301092411070812010f0302011403060334 78
    0x1a885100d082106d030300503082080c54001044554200540c0c1c1802590300518000d00e04060391100e0740004004004500c21202c0541455014000d20020030b40c2800c21801e221142000260480e4084035428801c1102c0c0712080891000b41112000001d0302510b9681d8550f160308000e000880c091104540c6582002d002203080f640c800c4100c1e10b80c2d5070103400b54040b40c940f0700343d00c03000d00b4102c0f020004540d07840c0000b4000c200084c10b40604118203685d69086000c0d1800c01c40c2080c0301d0203942a001d581084010031a00e40000308603402c4858030321203000c158541070001c4424813480c0910182e24100400180003402141c0d000f40c0480d040002269100a051814103003610b00f10080905000c3d0500f02c040d40003155040760400c0109000c9000480004500301c090781034024031006c0d91400c0c4045221001204461107403409803c000000074a20752445d80000c081044101924484250220100e0302c01d48040141c011246201b00a5a90b6451002c04131036042c5120261b406041102c10703000 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 383695593 1250 383694343 383694373
    0x10f0302090a0e340302070311251710020c1e011506030b010c02090c07200109050d0503040302010c1e030c17093303010906150e0609043209 62
    0x100042c00c40e0f50030034184098184c0d80980086d00202402d6050111458040200c50f105000d041c420401c4c0d613081c600c00181341c00f186e02d4111100d400281400c000054081412400050046070240ca044805a40c50403444080c1d414504848804d0310304074116500d1558004064018481c0085811902c862007544c4aa04909540720010f2340d90110b07a001c1c0d61240542440088564010281000300313141c50000d03a21b1440301c00d600308100d003141c121401017000c0d030343c0d003e00140c000300021034410b101c02100d5159503403240305a200007810300085100c4182000601c0303040c0541d5040141907142e000381c0c2d03410b001c0c280c0c0069807801c50b444038448000104880000081c0ea100c860007030001c0703003c02411041481c1021509481040807000300140341500606100103501034040081c01003009890140072205070501403490301c2c01c0c070814030100969038407220103842c08102c0440300841e0031250b501c203e181c802c08103114115447c105010510501e248504c4071344c0500301d07603400c94080341c402c1445 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 383696843 1250 383695593 383695651
    0x1211040c0f08060f1f0203070b010609050a06081f0306020903161404020706023703050c030c16020303030c07020f09070c3c030f020c010e010f0302090a0e 68
    0x3070400442e2101c00030890500348201e29142d203100c0540410400e1010048080f510381da01a42c4030016400080c01c0b07403c00492015480c018103a83c00c0071903107503040c03600140781c481c0740e8020003040152104c0045c1d0400c01c910050040c0103005d0100c01c404903101d04140003c0d5100d046040d000c0c2c8200d041c010200c5050590043c1100c0e414900c801408003640c003000003075031242d94103495154003402000405807404000b607540a58065034001030259002010440c2c4021205100c1858600b20030230041d4816542240d50041d11440c038071b81e941c0d02280300b45140951480740030b501840040100501400000010404280200d80a010003403401e0b041081c100e00c21500c2a00060325554050f00044a2a1450312109039681075510340780141c0189044d038804007481c480b000b902034202c0303109041c2c1000b01843d1480142c1b000e002c01203032140c000b800807041622014108498280d03907202080c400c4d41500c02002008184185e507982c1c50109441081c0241e46407031004600c41c141079101410550 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 383698093 1250 383696843 383696867
    0x3070c0b01030b092e0b150d0c0f1d04110d05040c0906120f110d080c0304051e010e06030c040308040b220e07031505180702010510060c0204151211040c 67
    0x1815085081a00e176140001c0c5c61b00c1c20220f9080b040d0000b010f000032603040d0140810039009500010101c5203c800140001c2d03080c601d030030520102c0c0f11a11a64041c10764854143d9078180c9002c2001d00c04c00490410347d11545c0c485007802c07031804083c4002c0080954002d0101c40c0340407001d100e855144e044d0f4248010f2a0b40b401070109034501c3c4e5900005046803045010b50900a20020090300c0b40d80300d07500f081e4000c112508903a04005800d2100d440c024000c800240c0c108403280525080140c00070b400c0020a0303400600c500c0740400041c80b81c0c0320000c2107401650780130824680b1503681d07800404032600914880240c0d0141d01c2c09140c000f080a220050403110a41f220090949885009500030406900c0e50b8980401d0188041601e482e007400d800e512041c0750f1940000c92170205002800c441d00030f03211031f40e0040303010300030030609521403680841280c0407200000c8e002800076550441d070f54168000c030321034600c0351140d80500c0040004c1d10504c1605807014081c07289920b50855260750002 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 383699343 1250 383698093 383698153
    0xc03050d0e0a090f09080a050a0f080103081e0f13140d080a180b0406082a041a040306090f05060903130b0c01090b0117011406030307030503070c0b01030b09 69
    0x180080015020703a80002c01800300c01c000c0010791701c01544404074954408045200800c50000710340c480181d107c0e5029104c80302c24940b000555065545003d520310805a42c000e0302505990410079100c01c42048407403482c20a0900d9648161414022045612520a40600308810403c3d0041801d100404072415036102080a150100d03001040d5030010b128550750791409449640802c4001d100e20090000d00310075160351800340b030300f039000c1c440d07a010f01480c080800341d40c40444407044150000342e0b401d940d810704001c14443e00d01785400d04240600d0740060416420001041305002103404690503081c010b101707680407907442003e40c0b0380d02d2065621981c0b100d0018603080140380e14071000344c891400752000200b0b100485803101c00f045d0f5000e13040916800054229200700800902c80c03003000040d62103400e07a40b0b18000001070f849020b15100542406000000109080e01c54050650140d0b40510044035558680c10040c44a020417105003946104452400720b01101a076036141c040c0902e4 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 383700593 1250 383699343 383699359
    0xb0f040c0e1b03041119050a090c030f1d060a0912050c1f0b03160803031302030a15020a03060e06210f0307060b011701180908070f0c03050d0e 63
    0x48071801075140001800088466400d401c0701e101c02c0b5241004501480c0903080764103111144008100d102c21035440008070003040c0810802560322903000c2d0008450500b0000a00540e0150003903002d00b00c80c10300d212480e490136400740c00d0242104080d01c820400041111171641c0c8611a000c101ca8414002801060304201e0b014213143c072403001407416003101010381b145440e11803090300030744c000e041204030341da42c035000010950b090400900700d0b10250a01c0c8200b056250507845516480301409810002d09441c0c4507c0642d00e0403c540010103030310940400c0203c04c03aa107d0002501b159982200080c2007540c00901d10404001d100c1c0500b400900c904c0d0040c1c40b040b039520700002800c09421003030190b0f5814400c106828406004114050140803485d021150700041c500841c4d280745008500e0b0f003000501180364015103055040005800c0015036404c0c604007501c580c06691402420444425a07080401200c201c0180031280324501700c80c013401c080c50099407842c461480482d040850 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 383701843 1250 383700593 383700599
    0x10f240e04060b010507080a020604050606060703090b0307050408030703030b09150102100911040903051905160f0218070c02033d060b0a080108060c0708121f09090b0f040c 76
    0xc2c95000c0002d8a50504060b0f2401b661943c82000d540c01c408030783d501507040306040005101d030912040354860411030f07002d403a2400b81c4d0350140001d00e10f4011541c0426001c030000e07054900420455000d84400750440c5e4548c5201d180003800303490390610240c0600e41c040003007074055034190b03421003e03500140c010b40b01090b2500c0440c1e0042c044124241c40150b00007a089020340c60f60b201e501c440d45c1c060ba580c143e81d445c42c9401d1300025000440702004200c1c04029900b0300c408820081c00303406600221603a1807510b0707400014440082d00c8400030401e0901014413402c103401a05000b0803500c294150307030084002c0503614080114000080c458031a00e40d4035844507040c03035803000f2036190f90002c000400f40e4503403829500c40e0300031a12440200300f018006000c0c003c0208910399010210400c080c1c54200d40d65240c5213140909405050340c50603d8020900c10100340e4914104043c4012001c41c0d540c0e901c2c5114009080500c8007a543d8444c00408111401c829a144034812038100e0801e84607145 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 383703093 1250 383701843 383701853
    0xe07020f0a11090a1b02100b030d020601050d0f0501050708090f060603100b040905100b09090601080c270c0a0e03070518060d05030a0c0c1d0106080a0b03010f240e04 73
    0x210040201561690312001c217004078403040e000c10310039140d0b81d00802c100c221550240040b603642c0c0c00c0840c400c3c4c0c4801055042c0942c000752860555009858103494000c030f0b031518445070421203100404075400d080401c03203282d03445140542700da011b200c202c64100e91201c11260703d0741415103110f9090340040411000a5070303550444c01d400c0b10082c0000410801d039884544c180340380c58803205041038440807070341c0061508282003078110f220f4101400965140506159a40e080840c003140a051503050900b149200152506482c40d00c0300f600c950303c2c2c50414400d0440d5400004007101081c0740c540f135941c60f400e00181c2c01080c1d0f4005081c3c2952641c9140c0c1104420170000d0201d40c1c400c03201c088071000210180083c0c1054403840d100ca6a0341c03811490080280c00217034000031f003102c03141500c0741040c410030078105046442078108190b41d0385410f02a50041d1603129000780d0550700701040030400564945c016000c4400c420705c100f850400f9031407444018030791481804500408031740841c1c0498 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 383704343 1250 383703093 383703109
    0x90a020a2003070204050405010f11130e06041b021e0d2304180b030606100c0605150a0e1005040c12180b09061902090a0e041104060e07020f0a11 64
    0x24440078100c2c0e050070156030000b003d5650841e030480d00c994540d0a03040718a05c090003140f4841500d03e10341810100b050003490700c800c00c07901c13461104400090100c1c505460320781c04080803150315010000c468103452000703076640040401c03010918400d450802c0c4071150100361480070400c00e0740c5803d00580d800302d920103000311004c0560030303100042100241c3c05074a40c510b07041000628801240c04118041014140540282014056000d0210140300903900c00b101c0b800c0c5aa0010002078540c9644003107049525070480c0d01c031341004142d040410460388404a01c1d100351270804200e07a9040d29001408162014615048080303038800a004440340100d41224003c804252030304800ea220302c0e03c3d642204601034503c4102500444c061290341d40b200c1100859402c0341c1e91041d80b0780400c401c0810314600b2340f03101d007030084e070404001718080007001e106035048120001c20600100c0d4440051030107030b103001d5800303501600c03a098030708001e00d81c0807a00900e000c0d0002716880d400545a001e000d000 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 383705593 1250 383704343 383704397
    0x1c03391b2402041806091e020d4808240409030e040e06060112020a021002030901020306210a03051b070e071202031015050f0414090a020a 61
    0x582222000d407050401d807000c2c0000b000030099249a091000900307004940c1142c2250100b01c0c01c00d00b001000c00071032214429003040300140180d03208130000382d10004010011580409100300341d10780c8000e0407540c800c1c0e884144d140301c0e5608040ba0b20003184203812007000c160b001154000c00001c0e552100096a25240500040c8907241050700038006001c41e03985040c00c4012403586002024217017410b2040142c8800b201d80204168145400081c18500400381c2115842d030700028403d1201d4800e00c0901c2844080e280207540700e042901c4643d010750011588039001c0c12500145442c0e402e5140c48145640d201c80003d09000381c115201101c041d400f054160b05095040b504400c1d00340010091034009004c414880d06840c1029000204914441e030b0003091a1401441400800c0c4502106407003100d40114070420300001614007a12580211800603a442c0e801180c0000d03200c180c00d8180003910300480d00b808160340d480210100301c1c001c0d0b01503c00003c40e5108941c4010707228814000310 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 383706843 1250 383705593 383705633
    0x2011107030b0f100e060310020d06050402280203120f0a06080a030801090b15090603040314031005040b010503130204090201021c0201140106050a021c03391b 70
    0x203030700d0340c0700c03602080c00039545018040f00000403c11000a80840d03d005000d035000c0040e41801e0541c00207565038900c079070005d07815500040d0b510980c40030742d014000078040030b4030541d201d00c2806002070050b4001d6907900828490112000c440c01d01c003008680e0a005ea1603801051501d41e9583d003031400310002d2501c01140d0f601c6c2004241c9000401c05540b100d840b0f40e03500c09041d0705144040054511480b10580240e00b0815500b040e03885800035640c80315010f8030780d59226619810200c0e01010700c410801d915050000c02e02502c0c1750f088182005980d0196814000c0a00e498011503541c4001c981010387e10740d50242100040c0f03416003003074100900500c101e45030014466484c0705116451500c0d603015070b6540c1d07440700352201a50a040e004100318141541041803d10001c0e484c2c034001c1168401c2c203c5418001045d442c0a80d00c07960b2983e6410490003500d044c2d40e0185c02507624000780030440c40c210f012545a500b882030404000103820035690b01480252661010703902054104c1c2c03001 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 383708093 1250 383706843 383706853
    0x209070503340f02011503032a0c06030b0f09040f060b120c01030e030c0a0312020408120301081b1003020703021002032e08060f040501090209070306170712020111 72
    0x581c403480155480d59400240301d595020030752059010340f212000318290015a411315070140b0172185900300c010100c07905828015008005e944514a00341c0348813003002c00c00e0600fa85040c0502a4019450054405503102040b60f0211507080103403285000620381d0b80314010740300080008180b62102648140310700e40101e1040718400025541c103010280d20485540300380c1c4107290540e07160181c02c11074056600a1071801120040140d114044400c001c2c081c017815002c40110071420794122001480d17a02c040c1d44c00c0d07030309107442c01c00c1541c001c1c0725030281d501c82c9940046005e100c440d0310540b4250018488044c525260600307601a4000301c101b074041d801100d0342c41c80c001003640021440781030240c0c00701200c40c0c07003040300104419840c0b06003503501003901010300164500042d0160414403003c0154140e940702c1c9000b602508003540d00035080311890781480030581e05504a4429501441e0340e85c0b0500448048990342d0b122944190000c11644808407009540107441c0304c1c103005403c0d0140c070 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 383709343 1250 383708093 383708131
    0xe04020c01050f16033e07060c09050906011e09050d1104050f04031d0d0503070318090e030d02071106030c0309010516172503021803010204030209070503 68
    0xd801c480c801c651030f4031003200140c1000b80700c0001d009400b1004006060130020100b4034070009106507801c042c1c110204900c0509414500c070525101e1488050394003110b681e4072031919144018000144582011894030040840c0620b04080864454a410f940c0c00012a11030702d0380b502c002e0500f040800030300003903100100301d0f0341710107809400481c0200800d07581c07000401c0c107000c101c900c02041d508012455500b4807000a81c042e840c154890740c0100c41940140c56880000c00742030904100800c1d510001903801d0415401c0000d000e442d5400e1700000c004103940d070180c2415503240d0315040c115608200701a4840c404154060481e0b04d0050343c400001170450804510a50300684209041403c04010848051024001c06900003150340b006440340c04042130107040f40200041c03560300c82011600096480700b032841210602c40d00007100791660155410054020341c801d24805038406a03004007526a4201402228200c139406061002642c2c0e408030b040703c07030350005041590a03240c04440c003 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 383710593 1250 383709343 383709367
    0x3020c011a100305010501080c07020301060504050f090105060906240c01110310061706010f020c061303112b050f0105041208060a032a24120b09070e0402 68
    0x8180074a019240031504800c4040070054415446140c0d042094100340040c00b680e680810b00743e4100038003944a94585d0010f1001a0143c0343c1c5411580d0444d16000070015200d1964010034001c0480d01c0080003241c0310740080c08072800040354103540060309048144460050b51041c2c071000680c0418250038009090040d5003952481540c0d608440c4d0003005010030220b40586610003004a4200b455540441d1100750441c61001403869050110503c7c01072031881c000d1104a8000d200103105559410000944031030003d854041034448410200c10190142000c1c0100000d004074102c0c2030b450030940e41180310f84e005a03500202e5407405044010980003109019982c000c3c0d00c51101c920304d40b00c600c2c500411141c40101603070300c610080744040000c54000034480c5c220640c4010404114a40c00c1c1800395040f15684c0700760040c0d85110525480024809400754801b45903a462584000c6107017845010740d00b1010100740e12144003404100c0d0140185286c51065201a00140c1800180415 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 383711843 1250 383710593 383710601
    0x330301030c031b030210080606092d01020a08040e04050f0f070501080a0b0904020f0406270e0a03020c1c140105071e02030403020d0c050a080a0c0905070210050703020c01 75
    0x81110300601c001c0e4203204110401c10420800700409010343d21683c90341c0c00090b0021307400d1040e1010300043c0400305025864140458041010103400010075005000d9241307100200340302901e0110300014030300350196102107032141c5070b00e4001072498281424004514542d0401820880d01441294089503c00006014044403c05590040c2100b00e24150015140000c010034021030380c4d103003103182840d03075171a00001d81d0070a8040c1c0300c85004100318400701c3c000b419107400c00020021080c0c1044e0f0000d44800b0801c4501060300340900c101280011400d503658402e040003805070700158404401420a16160103c1da00f00c98131134250b00740180c40c1d2518440070b00203c2040390b512002000f04680d04a070f0501040101c0c2c41944400100c0140001c1d02e0b0f0082d804001d21440071050441c00780001405050041c0000800a8040c0c507501c4510682d203520b0640121001d1410910010b1024080d20426100b00a41d8004e0207007110381084150040134000c0c171900030302d0790030300080b0142e51007486 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 383713093 1250 383711843 383711849
    0x819090509070327051e030405060d05040c12050a030f18030302010b10110d080c090a0f06031803050301140a030b1e090c0609061b030a08040b0f06330301 68
    0x900160881418008444c402c0c00b520a0800140403401d51400190b40051011002c813194420b500800e080e040b80c00307017584a07a900c900e500c0240415170f000b14000c0b581c0903a00451040403400c0c2003650700e030510700c00c101070144043c09a0b00a0310085020a005003040c070390050591070042d004400c45c11506a0f65800c0c2d820640060703554034420402e500348a0074001445c5142d060480016031511030f941d42e1003441400b00d104004445011400400203901a01d071040f0700100101074440d268103421004a495100d00c5d0002400d04420740002184001a161102c5d0136649007495a800d02c4406c4104250300300e03459401c100c00307441c000b0100d58480000d43c00703030780409000e11804503a5203215005000c081c01c00c1c5a00c0e0012100c20f410380e500c0a0403908070744401e0382c0c0c0c40d46803414001c90070801c0f4a5541110340a01001420440203a071002250b03200d14801c6428124a0311445a0017101c0e07803040362640d0304032407000181c48480c1c07100000103000883e6603941c80d00c050240329502c0740b9500300ba4 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 383714343 1250 383713093 383713097
    0x30a0c081c0f1d030919030f030201020c070b09090c1b010504030201050601021002091e130203010602070513201b0f06090f06090d0311090303031003030806030a081909050907 77
    0xc03a0b5180c801c0d800345003e410300824a038100c401c400405503469100e03140d4a940300c1d4400c3c00f44204101c569039032140045800c1204a440c0d06400d04002e0701071b40c00415400c0050048400100340d40e550081541c000d04805000240990744841181a2661050103d000c00030b542c0b41c00071880c0740c0c007401a03e205d10722940c0003007800d0401e9800680745c24160950707540707042d0061102c00040d1b1100702c110211400c5801c4040300321600d00c40880c2003800c80644d056800d900000004c540340b600001d042048640955440c45944035034222902143c000490b819660b01460b41c81310f214403080e00241c20304261080b515444d01041c0c62074240707480c44050304828180c100d2420030080382c0302402044aa02c100002604880c0350411005490741c1c10013040b40705150b945c1e0800d4444214070303826a200c0300c0014023101c1d41c0e800e0100c05ca184880039071204030000790441e80060501c0c00c02080045640340c0c008461400d040c0003600345520040941c40040070018151000900c036502c680f07845014030919 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 383715593 1250 383714343 383714351
    0x5220c03031808061b09101106060406030b15010203041d25200c04050906090f0316110d0602040b03150103060b0d0e0f03030108071707050102030a0c081c 68
    0xd450003030400340080d191100151042c50040101c541d01040340c2d40d01070000b134010311000d000c500f0300e85241d0041d100b90a41050007c42c0307400743c03140c1015060240c00c0645046820a07503403c801c10007996514040180399448031400b18514046008082503001070500680f81016140c00754140b00017014055920b20350b1041c42070141790041c440324124031110546841300c0082c07000380003074010f0703640c85140200150000c3c0719007490207041c401607850b100010320a00507030400c610b401e9681e11007503e032110315000d0122180c000e20800811100c042c3d2000744040700040c2207403100d5107080354076422590842020181680001d002d44020800340403c5104152281420700c0c01851103114564240d041c03520380a8140081640041a1940f000303a081009c144000304445281c102f01d00c500081880c0d10001c070011031003200200e50031041d14540413a01d20100702c544180360350342d0014441c06003d80c1040080038441c910078070740c490300e240c000c1d03030040e02e0196a007021806101c078141c1c000c090280d407 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 383716843 1250 383715593 383715599
    0x310050a0504020a0c1203020f0316030c0e030712061d070f14030714040b093c070809030c06010306090c0605070b0a1e02030a0606091208070605220c 66
    0x402440c110107004292400c6007403681070113000e030030b02a0b07500c0c0142c02480c81901510a8900c2601201d801c5198007016a4580c18240e0229006a034092850008a8142014450404c0c400d44201e2a0010002d004000d400e26091060030313074850010041e15480e0320b8110042010118106811412400d14000e0100501e4a4840c0e00d011003640c2040e10900044060301d41595000505c09064400c0006440c075003154400010b0000c2240b0422a50881944400c000d900e000740189541c40701e9041c00480c030030100b01d80c020300281c00c81c0c03034040088030044030100340c089206459441d03010540c9400c0742e1034564428919440c20074244c6c02207c1c01511061079104000c90910880002c0520b803d0a600f0010255582e0841460080c14914020790f0350302842d505a005000e100c84020100c4802c542d42d00b8580c0c2810080d06d02401400041170f400f2400044100703017481910341c2643c00101c002d0078044147c0e2044040d0801400c030f030360a41c0308240700c070444e900b00c403180094003840b501d40d101180346 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 383718093 1250 383716843 383716849
    0x1b0a020f12030a120b0306090a021e010c110a030b040c0501090e06010219020102012909060306191505090a0f0e010203010f0e22050a0302120a0e0103150803031005 72
    0x21036000c95005001c10020401107090010030b07a07a0000c101c0c00d1190200151000315401003241d104025494482d0500f07101d000303080403070fa49403001e0007a00d400d070f6482c0c0c80a060402c060405d20310607002a26841c000f41c007007184000310100c6e551000b8000402c0d16a20345400e40c1c046002d80f0b0540342d5138010300c0c0c20400c03507070003108402c001e1520300c00d503484030301d0700000103500c0b510118808212482e40302c403c0000c41e8801c2d444141004020602810b40e8901e0754400382c14103c001c0c030203a004076074070400f10398146030000320284030b5003500500d04542148070026030b000e04010800a60008948000420030703a440b980c0c4175105407001c880c0000c4912000c203924013580d1208031012000d07403042005000244401e044541038803840220040d035074582e90801000800c034506030b001400c2c1484856010002c000c5820f0440c4c1d8002e60894140000340b00e070711141c520403028500040707002e4501e5000254002d400801407003040120b400c844a03514552141194800c0301c1d4034070622061a02072150b46 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 383719343 1250 383718093 383718109
    0x4030f03080f060103090c03030806031509010c021504240209090106050a080604090b0c0f0c03070f210c0204111207090503010c09030206040303030b060403120504060311070c030b0c1b0a02 83
    0x80342440c003400076038059201d2521f0741d1800d00001d0100029100080d1003030700d08110381c040d046c0c1000040003580c43d0401c1c42c64020550a20301e02e00502a007a05000005074044010740203039002442540038041d00720441c10305000703080400d10b111341c090003100d40c9070352815481030081455440b11980c40c0c0380315400604075280100154841c1e442c1c004040081b0341e07074865113a070010304121030503901e0300070744240d0809000700d40800c1c00e28403000942c0d01c10025190f80300307010309100d1041c3d880003002d00e400c0506002076501c00c95000075101c00c0f450b0054030f000d8000c1442000310509842c5003100c0c140c10300d0003214041742c4410108a00403000c2245080c244a604204d54051030000c1071a81580e00240c0ca9100d0f0b48400382c2019222240400b10340da401e07084600a50b401f003005000100c2000d400b5001e600a88500400700786002c02c0001800740707400840f0a183d600c0081c00e4109800c41c0c3d10254410000350600019000a00006a4620b10f0320092007200740420700400c2c40307030700501c1040000 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 383720593 1250 383719343 383719351
    0x30b010b1206060d020c010e030406030e150601120204030b07031e020f070b2503151a07150216080405030601050102010b0102100c0e09040b1008030a0c061104030f03080f 75
    0x1a04009820301d6000d040c0140d6000102119850380c1e815a0140440103402805010310103035207441381c91850024004010011501581c4003400100d0905010a813580c540542e030110b0484650005101584512141070203c0f426440060401d6202d8072900d808044c00c96681010035540c1e2840d042481c40611442840c0140000662614000a0404030180258000201004c044038080313250010032101c000e42c10540c0358842d0f41c20042c50380e001800760100e01c0d8408010b06108101080e42c1c600d4102c0c0d00b0000305101d080c01c0c6444002c2d580c42e007403180360106180c0040d50074003440511860394200018401e006245840c1c03204e05200c1054204135044c0d0010b0305580c0340a000384050398000c0740480810a0f6070400280d00094200d00341c45820400c80c805501805c000200030030044080c90050150b190160004140c9441e01741c50b03070b80e92150f0550500400c02041d030207030005025030841304000c21029082c41c18140e8907038401c810501505021000f107000401080369140000c003603da40 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 383721843 1250 383720593 383720609
    0xf110913061a0d1413150c080c1315020c042301120c03080a05030106020105070206100b18030a0b1f1a0919090519020c060f130b10030b01 61
    0x40340b404a84004440e12040d1980071440e0100345220f000c040da40c00f556941c1404040051135203406800542e0020820300121075550308030040030000e000314412918908440d80b10905582c5074040620815009405121150582520081090740d20b03041600080320841e002000c1020981d0700700020386540b241c4007405050b003182c42850386040c0781c0180381100c0901c16001c144800c0b41c1020392105400da000a0300b106c07070002e002154180d100303004504840c00c0350700030006a10350000882e1580d1003a9003541010540c45c1c424000e101070000146035064014400c11412010b240210b810301d0324030a13056076144041c03020480f850150240312900302c510302c1071445080342440c0030340ea9504c850040c11a40d2890205000b040d5886100844003050016690075003280d1b55480204017903d42110484030065600036041e1220496000b55861800c509000c1c0c0b011360344201e07640c084241c005041008070b2102c1420000455148492140104803002c0414582ca085042c015104d90b0b041c0d1103156 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 383723093 1250 383721843 383721851
    0x40f021806010f170c0c071d060a050108160f110601030c030516060f08060f220f0b010504090b030a080a050406140c0c0f060d1103060f0603090d0e040f110913 70
    0x4801d0480d804d050384402d03c61000b980702c080307943e111032800c0c000b0b41107541070089030311903806030a03000200c0301d00c1018200c5843e901035484c0c00044954007019102030100b0b40b00031801d008500d0040300d034003203004610300c0c0c0200f84401e0108142e20745103080e8400e07a02a28000024014032409210034601c40c95120139003a09a450114010080c2c01200d06c5802080105804110503507100f1400d1402004004e02c4c140d43c1007600315048140c086400c80f40300341c0c1490040034100061803070285808401c4161941e5041c00e14190350900944250312007592b050050380048030000d0821030140414490a0355040d445505060021300380400003d550148075070305001842080300300040e03001540100b52090444880f40350040b1780d1901942201242050521192103c000709060156114040031181c01401141020921000d40b10640303940d21345401001c03c1d04101c0380111030032010400e0141c03001503c0114050b2200c22200d0784000d05240083c0020b030115503151040312001c6c0181640720800c = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 383724343 1250 383723093 383723117
    0x131b0339090f15032117041101080115230702060c0706230706020c121c050f01080a0f05030903030a0305070f0801081f06030203060126010203160503040f021806010f 73
    0x5011800001810300c0d00c1c5c250501240c4820304c15640309400920301da010a0302e03030615190460045500f52540c90010f62181c0000034980c042419035110b042c03103a180e0342e005035500c5404800c800007111400c5c024040402009005880f00b9000705045000c40c00039040180c2420350080840040b02c003010284100ad050446510038010220741000e544003400503540c0e51500b11007400c088000c02d554811010100b5484441030301c084078504000c02c6c42a082100755030b4240c400720000401e0084202035444900d8090000f1540c1c6804613070180100c08833420038040100003072855014105ca000080d88800078000080d810031810102042607003001002e03503041c461599910016041000320741b9000b000c0c0b41007a400250700c02070145070080c080d40c1c1c082da111030319030256003080800400810070900703248901031018425070f0302904480b48081c1d17082d01d030303e50111005d8001500039215030b505140008016601e1030181c188229605403a2021391810a0000d8080e40b04807040d2018040b00c10014 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 383725593 1250 383724343 383724353
    0x30d0203030c160f0c09061a1317030706180c06080f1b0706060308120606040602060105010302070303020f0a0f03110702030c090717131b0339090f1503 67
    0x5a6102c40c03580402c80070103800c900303101d004130700300607009030040003100030108107a480c80d0460016220b800961001130718901d5405015841032042c101d8240382c0d01c41c400e000c0821045a854101c41030501142d081c00f803203899074000c484502d001f03105078041080d2804100b00707200b001c0d0340c0140245d05001d000d42c58040c1035101039442c0240200c10130500c0b0000c0e28010a143d1090b41c0196400c00c904001c030381e0703c030300c0c140413160700c02c1d184094414180e0002900c1d92a0190464080c1e49040d0701034585a4a0580190081d4020b101d086051580a0140003d107410070702c003034aa042c13401d940314040704651038400350440d1001030100040207010010070000d61000140000c01c51402e433181e06035a91401011121003041d0341d003040000f20f2403401d10002804a400c0d2082c928090032061000003016003200b00700410511005025110068014104c0175000b41565141040c202403013203000114404080c0c544840d400c12411075966110410001d0303501c1c4145010701318022030b915085425500e40c = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 383726843 1250 383725593 383725597
    0x60603010605120a061502070305060c0a0c150b0402190e010912080715090b100806010e1911040f170d050f03090a02031e010f15050f011e050306030d0203030c 70
    0x310904a0342c0386001310f015280c05910a20050074048410300c1050b8054200a4403106188404d580c5413060303101045c1c9200c02c2004075510003000b07441c2e000107540503940e0007010781c90346e500901c455545c60ba0f29078210b8035140014a0034004890720000911510003000c0d05900405072058100000f03600c050045140d00080003000c80d42211100d91180c5c3c10b494500c81c20002c04403404200390a0894210820210340d681034015180c0500701d8406e2a12046065030341e0300700748504c000013100000030841175030040483c1c291804c0c02c0400400c0f00e2a41c00c1420703180354000c0d80045030b2a00d03c3d9408010440c0e0341c03403411315103010031005899146801c0500400718022070800784442031001000c25180c400c10030148442d294040c064401c0340005c44090740f469106403c0001140d400c080d00e410000c4100c0c4100d2451499040c8041c1f2707594244420300ca60124940000e506000e61183c103a5071018400901d00c4100344203903980350b6a803070034005050401c09000c104406550003441031255051804007 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 383728093 1250 383726843 383726857
    0x703060605092202040b04080d05070b011a2701030c090308030601200a060212060f33040806100509040503160f0204140f011406030f090c1201020c06060603010605 72
    0x4251111104541d901482069071071003061411384002000540004042c01801c00c503050b6100380c072610744074114251194403900d40018055105400148210a540c0280d205d102400c024240c1c20480d00401107600503001c07a51071031850300d42258490480d070b45801120f070340310300c0c0e032034625400c0d8915510101c2500000d46014107003c0328180218404c425180e4000c0c040c0d1090381101e0f4500d010f802c000000b50f01c12004000040820000a00541407900f040200f28101812107402d540c12610242d104540c002550a0070403410005120a48069000707400034010320400b0700f810341080600d4121484041d03100318064601c40c002c100c00b0800110076690100207541c80740703032039501c2d900d84180d4210b000f03400207500c2490461940d00c1c81014261081c441e4400400403500d44c4d0302c0e0742144903400500d030407144d030100c001c1000861750b8080500a90b000000001103501c03428240e000101c440d041000740204d0381e940464402081481008401e40104045d070381f1919550401d00028841e03c40c0b01 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 383729343 1250 383728093 383728099
    0x3030703080f0c07020d0308010303120b030d031a040204060206061f140a09120302240c090409060605090c130e07050304060b011106010f0807170319021f0f05070306060509 76
    0x1800103c55500581c21110929402000003001d41c030a40340191114400f80019000125a03110340c1110307584601c500c0181040c010010210034031040d60071000b40c418040700c00f4050141f01e40510840d00d07a030010348060400b94000c2c000d146090030501c0882581040c0b61801da000c1e928501250b41c0d040604540b041c0321205410340c2d942c895060035030b40d640c8a64880c00c03454039201c0d0750000b40b5a01262400c0d1500011942001383e1800c0c0140740329400f000d546460b007610081062100030700d4583d1000c3c606c0f074807440f8081010340d0baa00001d00d0040b003ca0740900c070402c00142503281c80384c41c244e0b01070242041c081105034030300b1700301002001c03800300600c0201619555614000142e00a8218001441c0d04004440309580c407452021001d01440c401c0340c0c035501c103003c0c02060000c5200342040c40106110010b504100343d4202c41e800000052074110158000e003502c505e480d140584898600d042500c4c0040b5891001651b000c0c00c84400402d400101032812000b4440c41d43d02400720390f0f4100e011 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 383730593 1250 383729343 383729371
    0xa0b0604032306010330050f090103060b04080f0d051e09012f0c0f0d020105280305060906120601050411250201030b0a0605041e0308070303060807050303070308 71
    0x38884503403101c00d01140c18440d03200b540000803c1200786d0042c44824482d40c00d00c50490040d28044803207083e10782d000880030030340c00c0c000c0840e00d010000180c02c003d03005250103c1d070315646804507a4580c0c0141c2040d80a40c024400049210104103c2d1011030109031411510380b0028015100d902030b6040507409000e82c0c001100d10b002e0f885041008020220b07281251840342440d58100711004544c81000d445001d50034035480c1070315080204082c1290054400d2100c2c151076401155580d02c54003103041b04000c1c2d004002018080007190719401201621b00050b0b50074580e04105003014010100da101d005000c50380c40d008500403401c1411908140d41c04541d0720020540785100e4010030b080d13209642e01d0f80e0001c0c8005060100e03c030031128002e0300d04000000d64601031004100b43c03800341c0b10100f8000c2208100255606400900c3c80b20030f210086180c589036922012075902c00007088d000039403160310510640c1802d109070b0303006007003c500a502c1c0080958000c0d0109a005000b80452065 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 383731843 1250 383730593 383730623
    0x60320151608031b0313030e03150f07030e03040609030215092404120302160e0c03041e020a12020909010c020c01030b041103070f0305090304030819030902090c0c060a0b060403 78
    0x903158144280513010ba10389902c030700e03000461406c0090a041e0035400941c80e003a80e8159130402094030313010b11440d01181c41e40c6941d44c9420168207000641384608041d9a02d81043c0c0c03103131050002d00081c04031070307440307001c810300c2c50040000c0ca542074404c148010000304100a8540c1d160442c40c010348030400384441c40c0340d03170741c0a41c04030601035948120711030403088004000b0150702064084078141610800001c10340c881d02c10868001007180c1494040c802040481d020404084074418030101d1b6640340c40e9030030345a50108111101d660300c05aa25039224040c6030840c9080c0e1461607200010000800030301c4e9201c0d074003e42d150380300542c00b4141680c4119000407a120394000d44115204000f07816038038200703000c0040917042d003100e8413000207140c0b60100b54900c02c003100b2101100c1e00045d440c0c4c107040c0da106c0071103250a8240e203280c040c036030713140c5611005072104101140b083c03a91001403501c1d440c0a180140c244400204002045031500c1100d0031a9a2200144e80c140c83e044007902c1e0b84085 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 383733093 1250 383731843 383731861
    0x6030c090f0403122f0408070b0c03190c151505060702041d0c0a06020706050a360f1a0f09060d0e06040c150c0602090406032015160803 60
    0x1401e00c1641c117101681008010030071029807650114a02d0301c0c0720070782602c400300f042d005901034200d4540080e201008602011380103858540aa0400d5a01d000d0082d01103107019031710741008c1d50200e07040c4c5400c00c09105440c600c00449000d003101c188840c0d0211200c040c82a40c0c14020144550320118001d019503e403175120213a50007082c0015504210390881296070307940c0c81c69845220b401c0c03007640412814400300f104400c44086440700c1e4181404924255111200d180070a0400d0b0b41c140c011036111021103611050541c1d0941e010002c5900b4040c0c0e03100075940b107070441914544619440840d0318041c408503180b8918156100352650054800070703601d44603840b07220501e1403d010340c4603440200840c9441c006d510558004502d555036000303561045c50885620f41c0802e00c1841080d0100c0c3c4150020001540010000a0b0007516030340c45c80180181041c01c402490070791000c840302410115400d5401c003501a5291f41444005107042d2000001d01100a201280200101341002 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 383734343 1250 383733093 383733107
    0x12061914090303040b0c04030b070e06191815050d02070201020111030f1e07020303040b041416030b0601111009240209011e020a03110a020409140606030c090f0403 72
    0x151031902000349810a03011240d500d400c01c1e135060b200d403c030420201d07070300d04100c8040740c00310307580004011416915001c080d20484018180c00740c2140007045131103072407602e81c401680108602d1b15503c1300c030285043d035200442100c0c1c0041c5500955079060a01c116048000d96000c03c43e48040507039521802d1004078090841d1210081e0202008824444e210106c0c544c240d218184480c1c81c1070703040d007000c6a000c0f83c1c0c0d0700a40d20390b40036800400200d8003150341401410343c85406139200050401c0201d0440b481c080a0079440030480400d400e00f403041028003015142c0100091070412102d510741c0c20180c5d05c50400c80701d035110140c0e880d1501c1c3e0070031503d06445100f68907402d80010440b07000702d40c190040d40c001940580026202988071103041c00d9005c400f200000349500a04100c2407a9400352624020b0303485120151041c04c00f0400140da80e0701410b0819445010110070509404c001c191400c0d2020300310611a812401c1269115201c031402c4603841a6441e42880e81da80703031824260f80c1c607 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 383735593 1250 383734343 383734361
    0x604230402030a05120a0f020705060901050c1509030d06050904080f1b01110a182105030d05040c0305070e1e06060c0111032703191206080d0e120619 66
    0x280c003d80e100c81e554081e03c0c801401c0d42c80251f4030303062415214004200e81700d4040740900c40e40710100303011050540d481100a0a03260401c1012280e03051811b00a2100d130810441d20307c0e039141d0002900c6200c02140f4001d04008000649060340c440c1081d51f650b47c0c05004410b010f00705804080756609003d001c062001070848204402085000d40e09045407940d43d100e458224085581c1c0580450490b4200d00385500b00c0c3d804841c50900003c0e4040320910b0750741d0050b416030319403000344408103c1c50200d1090318084c500c1040c0d0310000b0303891842c0c00f41c24282c80303034044200038810208002d030f2200d4160702010b6410002102a5207580e810b070000d03510b4018040080040c2d0720f0420210b0f00405100011400f880d01e254258140e440e0100a01c61002050095590710303802c02d01c410300d03c0003081c00c01508134240c0350902c650100344030218041243d0050340302151a5016112038941d00f41c00c441010f04041c0c003645c002c60030045004580390348141c054101c4103100804c424140401c0c100e50300a103d0 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 383736843 1250 383735593 383735603
    0x3050d051003030305010b03070e040b060c010204121b06020303060910030516080c0a27180501020a08070302071a1008030c010b0f030c03060c090a210b0604230402030a 74
    0x109040c0400e44480381c0d69140001c6000c2460a0000304040808170282d03071152081c2c0e91601c4035110b07460300b40406010381400c0e890300082d040c062005211000c0c0003400140c1180c9031603080b02c0565040062241713011a13003511034480306003001e10042d030f0301000300c0381d10100c1034803110241d1f2105c5080303003102880c90f44080c0c66405590301c0e05d05a11500c80c5c84508031001e031030489040149040400050003140d00c5081c600e01c0301007900001181001091741c0342e6200c40c0a0000d034600d407589802c9100345079000201e40e43e0b503001500e013801640210520780c200314a4a0b0440c10b04c00e0a680310040035035a4400c0b0400000e07030000103801c1c03003101007194015145100640c7d4444210b103511714007908125009034441d20440c00c08044a060010340c40420140c0200100020745801c0302c000250f520507040751f5000008408082004103410054940981400d4510800b4540c00e00304200300e000058100c6214034101140741e000c01800070000003da0728065803c951030307100c2c1d20010345401410300000717003 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 383738093 1250 383736843 383736851
    0x129030108011505040b0a4416050f0d0609060c020c0111061003080a0c081801020c04090c05011209060507090807080102130e0402060903060f0a0b0303120105040903050d 75
    0x42482040d001404903d12400102044584900800065a5200c2c0c079003030304011010300400100c60a80102c2905075031a01491900024090103040442c16124201050020788030002c071081a040106240d035003400650b1480701e40c10840014949969440918803440800c4289000e00040b070b40080d1075554040b43c200f02e92032012402a4481d16054bc2c0f140c042500c03846117070600d91021401a11648004611107031250640c0d8482c80c072904507982e2f40c03040180141e0490002000c040003480f050410030142188074031000c0009151100120405000d00c0c00c110020001448902031101942c00908200e210509562080001000c0300301021340140d017000b0a2100164021000c60309031844003003580c0642d41c4543d017440c20303403091004a5201c0c68803d201040000741c013500d843d070402e10080c1410301e080e0040740043e18000068a03141d2010310340804bc403149200c1407003070765646074040c1c0140d0305050050f4685072039024144240c0340116100c41d078603010144a034045409100391118100 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 383739343 1250 383738093 383738099
    0x3020114070305090d08010509040209100b031f090911011d090c032d0105090c090306070207050a050102160b13050a031202060703090b0613021308160506040303020601290301 77
    0x3005400f00b524014800e010300303040014030b14410a14641600c0002d0201202621241d0038000700680040011807400200715000c0b5000d1a1400298041c0c01c070320001c00c1d4880b1030710711880c006083d243d0000108515051083c40000c0b100b448601c2000b100342486421095520480d03500c45400a4036142c0c018120800c2003c00083c030f402860050f5014140c60700d004452505003003202c1900c552251440710504010060f0b840d00c0014268070a03a011103450a1400f02c0000c0b9280400580b180c0000d80c0112400340442e00b400b80c1e00b000108000d10080020422042c00d1201c504a18003038081c1c0501c0c00503c007910f85204010280081170b01500e005c8100d81c2e28240880c02500d0085201c006018200114048070704c01d018031852660482c0d618034aa40744c3c441080b803050741c20080400485e80034000c070301007401101d48840c02410303024040c10001130800c0c1244249041600700b24415170041c4400d002099000409606499840d003c4042c035002c5420400100d0b5070f244200e0b114408004004 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 383740593 1250 383739343 383739347
    0x12120f0504050a08070815070c0f0f0602070602070203160b0d0506031c02030a080604051014011814150309120c1f060302010e0a0302030303310f03090603270302011407 74
    0x144040f110300800740c0d03450010240380b110010505548800004441842000c04982c000cac00860045200384c03105c41941c0100d03035030002640c11040707041d5001640440c0c3c100650a0902040b840c04190840c02582c060030540080c0250003410701c2e030080295104001121500c0401c840d07510402d0820780c003100c81c225034030002c0d40c0354408000400045c0070000419001d06007401020700881054071035408003030400d18140c90048000c3d6000b0304000310003070615241548450b0070703006001c0340d400aa03d045006010302c800b0702c0c428612884200d500304100602c001c00454041c040788090f1803010b0365000c5c2c256440d460440c0e207400c10142d030040c144005030200925404181100e100313032242e8150a248108100900035507100c00382d0103400402c00644026016003218201c540175588104119500c0c0c8041d1240b4a117003441100c0045d4401140e03401d050f00076008000505541c039007441507100c00c42c1e0592007800c0c100c0442c82580c070f90481e181c08140c002e4120098440c603940002529181c40781c00 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 383741843 1250 383740593 383740603
    0x9050306041b14030d03020c0a0b0c0a020c0102030f03130c1a1c02120105131e09030809161401050f0a08010f05040c0912020303040503030d0207060612120f0504050a08 74
    0x16502e60602c40700c20006280400500b42c03144514010f0150003103400d0100142e010f580016642d0046001d5940d0090003e065100003500400c01036085039140c038140d0380301034038101009440e2815540305000d02c42070888070004895105036982c13030000b0080c51034900032000c010260000d481007003c2c1c0210341900403116026060b20545140180c0d95072980704100d100700c1c454400668a04c44c00c1c8801031102d8103280b55440321050071048001242260504c08084000c2110340310641152544458000c1c190b12069007904021a94080e20b070b00301c1c090548003917000c0e00344101150300002c00351001490f80554240c2c0e0f104280030301429541e080100000700aa002409600710002400c2c801003580d0405200780900c07000581c84d0049201e041c003584011143c0705d00c00485e4940700030440860030f0b840500280c070401c45030040240c0c0768038951030488265030f4507403c0207003030398461f9203090003050800342c1030044bc80d41400c00440e00e030350b491411101440f507508074940001620000082d44000012 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 383743093 1250 383741843 383741873
    0x7120509010810050607030f0513030b01091103010f03031b061d0d090b120a11040e0403031a090109020a03091b060212040b0f18091527160905030604 66
    0x60340e040303641d036601d00641c0e03100c22a010b0785801c881e0510617480000d02134480c0c08d00342041401c2250514242d004c5050041d54503070421580c0842040c010802510540101b01c44003485681242c10340d0305080c0404000c0d070080c4009400c000403207201803030307404580002d000d4554000390180100051030354000d00311007a010f02d80c12984200311450340710078031454044050721a02a48a0b1600000e45591000c5132400340080154076600c030345500300d484141000384000c00c00c20040021908d0541805001c0b01c1d080c400c100061807911441003001c0e43da1405050543c0c042e0300005846210a02e0214010001c130b0b500104140312030314454010801140300070301164a076500b02e808204043d003144215004501ca00b90841c001800010310241c400d0000e40056420314001600006108001845442c8183e54000c481842076900d4819424400c1111499038140b0070902034007482e0400844201c44001c01c80b641b44190007000b0b006403442200b0070401400300904691050805080c08064007030042 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 383744343 1250 383743093 383743097
    0x70f0c0f03021e1e060c1005060a0618150e030f0304180b1809030d180606080d020601030b0c36090103050c04051e04050106060305150a0b0c01020712050901 69
    0x4060b88200803c0405810042c1c8014104015061810751000e03a5a0610790702140c1c4040c090140c900c08107820811317182045500e240109131800c0c05418041c840f446600f240d0100040e9410103d2501b156096100c219a5900d038410303151030304c2c484111500d441c07078004c00d98540100d1060f01c1e11054004040c2c81501c080702ea100902c12001c460100481303205442441c0c0108843c54030340b980001c40d500e496403105035070065901c0d196481005000f11040b1030300244844203036100810500007540b00343d2002c0c050710350040888000d8480c01954138281480001d140c01d1082c8005464a8103800039562a07000f101d501400c80c0c0c40f40c25101480301c0070445041d4021100c01d440e0310640c038140c5130301c604903600100074040c04141d01c010f00c80a00b0700100a64140303000521884207003001445a5403103140140000503181d0305001c0014180d8101805040b1007803ca5854942c46980d452849011100145580755482144505850190140c99030150000b2941403150b12025045002410201400d03 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 383745593 1250 383744343 383744359
    0x19090f110604031e0618050d1b03020c0d050705040f020304060b0405010f0e100e130302070e090c21030307180522050703060e0109060f08010506010c0305070f0c0f0302 74
    0x6401e024040c0501c2c40042c000c0f6074205040c908030ba010342e1a07411032601a61001c0780300007402c5540d40d01e0b020089001c841c0c0d580300c00381e0b2006883d84105d00242138244505905009241a20025516124203c070341c0d2240d00140c9403941000003c0010364006c10003d0b109200c0c1c640c90510140080d0070440341500c94a081c008020924907080c031441e41038603e17201040001c142402d22910031140d00800028014040c140081501c0e081d00c09014030a5101003c4c16003281c455150090400c02260f110b0131514043c0802e20191410100c0e00140302c00c402d6444c0c807140b0300442e0081c0301898088188074039a020010900109d20381c0180078a4200400d81a5500040e5503203042c040c001000610142d440407200b581c1014162854211300d03003110f100d140110b121a1291041c0c1d80c9850280d04c5104015038035113003008035400000d0501d0041c2580c500801c9103150000000e454120403905c0142044000030700e0004120610034600c02c215000550f40362036030b40b6141401d420f45014001640310ba101 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 383746843 1250 383745593 383745623
    0x150a0b1812060c0d060e0406091103010b1509041b0201050402180403021009060b040e0105072706201902011106060a14310b0105120f19090f 62
    0x704010320000e84401500074400c0c1d41d15002c440119070801c003650102d1540310400003400c0c0c61917051590180303010381d0000030700040b140b1301024900f426800c440e0007641881900d1405943e80c06401d590b818414000c1c41c1d0b00e0003a040020010a045107114204000e0b00e409009416415440745218034420b590140b4480d0800000700352600044030010016448080307240c0503103210703030480310200d44500004a60048120006019a003171001c12441030381d5610100491607902044c04068103181e810001c110500c00d58118160200c41c4c010312007800900e40d2103041e02500000c40000001100c01035589413140da85503800d10034154101640060016100341414400125a10f402010000c28124000e4600b0f0a03040c5040c070f41d401181c1c2d010812055600610200c0001c600071401c011180210125050380d0b503000715104c5e901d01b2410802e0a0001c46400348040c01550f41003401c011003c0c3c0c841d620704103004a03c4c80c000c1c0041c042203051208500820503111140180c1c02e220303280c00c02c01e56031 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 383748093 1250 383746843 383746849
    0xb09070c11010c03050c0a030806090a0603020a030219080706052101060f0c030201110a03050103020a080a0b1305010921030c1809020304050a0b0c0a080a0b1305150a0b18 75
    0x3800d0000a0120120000c00212070b6000e80c0d10070100c540f00381080c600788043c240a442c2444003844054010030703c0701040214525241c5106513114030865005c01c2100e045802040c00c803500c901000340200c40081704040c000e0302400d41341004207c20000c0f00e030340c1a00c808000b815a004000841d2400b01c41640c440001b0f07006182d00ca060381c20583d65040384600034001201c440c10f9440701601595610704a502911500c640100070b580b103540c07004941c0d545984180300310300c0302a030300c075642c15084241c01138005034820282030f812004010303440752003520b1424414010204590000d118002800c8850103820290180d1050600c8545007000140c5480d20151a1b04041003000101d1902072201400705c28403a40c040c54001e8005c4080303c00c0079034a60b0303800340c00403c29218005900c074080b0315100c40e503501c244410350008103080180005100380c400314290308010490080d0b07560b140c00c0044e400416070440d5214405006180350141d80e5501060492940802c00c021918800c5507a08000b0741 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 383749343 1250 383748093 383748107
    0x222060b190e10180306060b0c0c060405010203070807170d09140609060705071104021b0f0a0305030a0903050d0f02041502060c1b0703170a123b0703060b0907 70
    0x2c2c01c054811900180c07240e5040314101142420b03190003903941d14012000c14203910458000d0420002c80c0380d0b0b01c0c03034246a0240f519441c00d030900d1240b0401c00042c01a660701000b552030140c0d0200c0065141c00480ca40009040a800c00c414150003010519040b2f04006400c4040c030680070385030003114401c40041058940100320340d20002c5520890100b1502441280242a400d0143e18031b1054071403000d0028060380c0c80403190403401c41d505000324820900512911201c16440f40c000e04030120a944d0192a5000080000c00f1080d070303a00260701030601810880381d100a40003070400900440141d400d000350090f004d03412070383c24146801461503000180940c0140d540c06030150030503100c0350461549000801d80d09074180034030107000001407030070710007119401c500584035034855031720301c100500030014201c880c0c180301e0070240e00d188140c1007841a900340c4240d40e0386210303c086010307402000c0045451180354081c800d4040c008140a400e038841c11030583d007110414500c1d00d030154102c404c0 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 383750593 1250 383749343 383749367
    0x10c030207080609060a050a09120e04090b010f031403040602100c05040306053603030402040c0207050607030903110402040605090d020a0b22090203071704021302070308190e07030222060b19 84
    0x280c140c1007a82200d03d80503558bc0315003404007c2021403500800d0761800201d2000703900942c002403080405008020490003807000c1640250011410240b8040307000b581c49140b1060b401d903c590303840d861900c0a20507000c850155810190034000c90408030b1143d03180030100d6032044218003038401803851604920344403c5140080c41c00650039502e441d002c0000a140c030b00e14440561085030780015184c1c44000c05084980c1c041d13254010700c0c910310704003038012500c101c0c0414892407041009116042d0002c1c1600d5080000303803203115801a5907c0403907034001240e00880031a010100380000c00613040f94030b0000751145032145081d0b90355a144020180d00050b02c052021500e4044201e01252a20415540c8640010f0844040c1703004014407004907888000d0680000b06003004208162580c201d458500600c0c011080041200310366165460b00e4107404020b1080030090b003d22000741c4041c2d052120000f00100030020345a44c0d40d203c48050344040c50b10310150a089488081070341c080c94841c0e6403 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 383751843 1250 383750593 383750603
    0x204050105040b0d06170f0118150903030e03040f170c0f1201110d050405060603060f0a0c050c01020a050403021804020d02010f1b050c0f04110405010c030207080609060a050a09 78
    0x28103041c640029066002140c0362110140d46400000e1040020790f1b030041000c06900251031402c1006540d10700752100180c0148205120030350340d00015520580030304400040650001d0310005078941100500300010309411544030104012401462803d099400c07110b540f01059402c1c0c1c1c01e801000c0c1c6030070b00300744015808140e031600116241040120200e019010500029407508000c1c0192020340000304941c0019945008110070414100005900000c00300c000b405189807000e1421104031000f0000f9107200d80b2070310340c0e00c0210301600039140d40c0c0548000a40d21501607041c020b005400c6440168803450b034003a8165100c21307085c01000c2c0035035006040d4545064950b00155480c0311042030344820050301940f01e00c00c0150402c048c000d00e504c1000900b82418a1000700301d80d0000d81c219080c40b03240ba0611000100018004550803114282402c0000e0442d604045e818a501030340051128010314040296007072000c1181e5102d90a000403c00c0380d40ca450310315000700d1300c0ba0280200 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 383753093 1250 383751843 383751847
    0x40b1f050a0b07030c080a0302070c05040e0c01030c02070e040503031b16020d02010c02040905010504020a083c0f011b3b0d06050f07020129150c0318040204050105 72
    0x2000d107180c10003c00305030b0b0003400c0254488406944014856010540420010703030701040d04010040c2c0841d2440040c04106c0f002c1c07001494076070700203440718000c1d5107141c14181e42c0c034006100c05000b03000c400001d1444030301889203841c00b414196102e40c41100c0c20055040341e51900e40440d1f915406481c50100f091b000d0f02414000c582c20b102e402e41c40880241c0c140400c0903c1200142e98601410100520920022407070f03003001d1042c01440f1b46190061903041d001161240d85a0b405c414a03004440d0070841d0900640ca59240070000b0011003030100041c41c054490b40710110101500320403005070482552071880501110708039520702080781e81c181014400e9103003501c4040c00f41405c0c0c151008050603242e80b401c55400091214950482c00c682060f1210b007008500c2d8003038812560b012005000a1003422070b440c0c1040040a00f65501c01141d140c000c0c031410783c0e078480900c9045411104d0304155a102141004c096403900f140c03d02c00c52241000001d103105007000d0090301e04899068680034 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 383754343 1250 383753093 383753099
    0x60905010b09070203271002010e0d0f120f060b03090303040318150810080d09030b060d1205071e0c0e0601030e070b0903010f060605030709080703030e01081e040b1f050a 75
    0x4001081b000c184990b0962409400b5010303592030210041800c9140e8000003a00055054a24144140903c0322000e1190395034500b10001d421042d42c4203104107074240022070205000204006100301e401c02c10010314084100514007000200450040340203480d01041d200d810703900c100c0c00d0041c0740194039002d050036199025145c000d00c4c0d2981c10510540c1c12611603a1136981451906200844982c00111006801c20521030114100358101c00282d58501d814501529058aa18040600e0740e0400c02d00080136000d01c47c1b07000b8401d000c92044050300002c2011420103203a43d075054001c815032844d040c0c0100e00f4540c0644904a04d40c124400501141c03443c001a10307602e82c001b4010b080e059521070828030514480342c4151400381c2101d0700d0315912814a080e00070a0104150412042070740020707020300200340c0024800c021443c0928142049944144248007075200c40180c403038880b54a0001d000030000801d5034079101d41c1c0b01c900702048a0440246150300c042c038038441e0b20741280300c8070028 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 383755593 1250 383754343 383754367
    0x120f060f091e1e03020c13020406140301052103250c0501021b01030b03030708040e070801060f0e04021e120103060e03040f050d030314010609080111180108091603060905010b09070203 81
    0x2100e10901a005031129003072400b0100d103140b2501f41c0580700b40c55002030240301c2c00d85c0142e440180d008604402c141190706140204080510b2101c810300c446d020300704500d4140e64104101d81424400500322803020fa100110540002c003096012150100054004640b0354400110340ca4901010030240c06541c0b8001e0041d8018040306004d1038050104100e194003140241d0000c7c0014041d0301740400c1c9628103400d0042c545007060b0009005c1044021002c05e0070342d0701c00c81e8209100422900140e40310142c400340c0c592801c4030802c0015981010488103407514411101c00c3c101c034052501804100714143c85940c172440740d805103a80d41440044107212070700704118030300c0c07410348241800525140e400c1940c075030121090340f18000050401c01e007445800c40a006002c20260304407402418910182e40412156100240e41410802d8000c00641c01410070410070100c1c1040310045882d554072828202c01a000800302036480d5070904d10100a581403d40ea041d10804155025500b0050950360b9 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 383756843 1250 383755593 383755643
    0x10f050f06130b150702040c050901020a08091c11310e0c0910080705041a1c02040e030a1d010507020d05071d01150206090304120f060f091e 62
    0x1450702c200d0b070ba8007051600354658458000c90f070f0040c2e200d003a1304d4800901c104825108034454400030400140804112a6000507407201d03600d0b40803203081d4032129048041040e0b441b440c0211075900c4118546041400034030305102200701030950710b1031000c110828052000000032211000c01d40c951240982a86515921071001d000c80d60065500300868400000c4804e60180c9080b008100b00c9030040060b000c0800158006281c145c1c2c0500903000c1c420f401c00242c900c0800402d02a4415113001002c2c00e0003448443c208582c004d20400c84407106107503c0d0351b66005506c404000c00d00441c28034414a050486805001c001691018506480b070750900280f00c440c1882101c01d4407030f00e84081000c020710031624415200b00713005103440c4c2d850214110036083c6e0101c2c04034155040b00c070902058550202c04c4905548802d4407075005151545420303960381c0104035001c1e200340d25040c1c0c0001c1302c800c0c0e0381206c130540d070007213039030503080313a80b440918580e200e0820000b080ca10168000108440314909 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 383758093 1250 383756843 383756869
    0xc030e0a1e030905040f0204080f120304031b020d111912061e050403020303040b0606130b090a0308220e01080a170d0515092206110c0a06020c010f050f06 68
    0x80e203d0903059448000c41c05480001064900480e0040780a000401d010020301e058182c1a0008100c50000441d0070509840060409001c01201540401001c0b0b400c031304c4c9441c03850380545918404065070400006c1d070545c202c41503204046140d620002031040b0068101510032201d00002d030390400f0343c5c80030010001018551400c92892100804801e09841410700c1203000e034015550328509443d006a03600802001300d48034100900444003070f02d55501c00b10054450f0400003681e26010b000010341e010086910050529000081d0b0301e400340003411208807900b40c0711804584098a03111070400d411400d0044624a922603e03030440801d003162540070340750404220451030a9007212006007a1401180c1c0341000304131406c1c0e1100c5a0425443d86503018101c020b4202d0003c0c480c0a0075121141082d1001c0d01880e00c0b0b80420100076507080441e03415620144c03c0352980c0a4a1230000003a40040c0882d20f070651030040b91009100340c501a09105a22024801169540e8a001c20bc02d181c8a58 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 383759343 1250 383758093 383758097
    0x290109181d0303010501080601030e03030f0619091506090e07350f091b091509010303090305010c0f09050103150f09090506060609091603110d0c030e0a1e03 69
    0x1c0c22062900200c001021420009030300a582e42c1d42c1440000f40140c200501040e04040c42d00700f12948001020041d2a00700f105c510300c0a849880b02c0000482240303041e24180023221052078002078682e220340c80020709802c51144540c401e0344c0e5480564520728540710700e100014040780081c5130701c1e01c180140d0000c60140503200500407410360103507020b100500d405940c0b0303800c403206102c0b51400c50007003594050341160003004c2c500b04841c0d0604012800c00c000d03a000b40c14203808643c8000034100d80c19540900940f42c41c98542c1d480c2002400c9400c94402680d01e0b502e0000080001032040c2485a5403d2b0b01c4e03222000c100d0326050045009080041d120240790000450200c1c055000041d20340043c801c9071004a80b04009050885c10140090000c030310440040006005035250242c0c000d5000764000700d0020303180729104c000d501400c42c5440d1291001c0000035110110440c035404165020003581d41045030303441007002d00b66034800d590703005485258808201d185422000c0300b04030004c0d00c81c0c = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 383760593 1250 383759343 383759351
    0x3030a0f050c070b03180106030203030a0e040b0301090b0609100f051c0506161107031203110403050304080325051e030d020f04030210080709051512090129010918 72
    0x202c025080009680121002000020a0141101000903180d140c5003900000300300711072031980000e6803403083d5001013003440855a42c0004a03966031340310b0207c1ca54090001c0c021131640d4036001c10311400455525105011040200d4240d101515100d42070340d44a8240160050a03c01045500c0c90041c5125040c03400c100100c20003c4c0c014408a401407820502a4484403400312018003021140911440c0c1d5502003030080000c15030300d4201004c040c0c00340c2800198501c04003100b0150b8407894001405501c0005030000700c030351001000b445c001c0030090b03068402c4415046949001c2d5064903000d845540803402520459140c803c12420342c10100003246d1400d01c508a01c0410ba8100c980c982d40c00b10070204042055040030101c81401114038544500540b1707021001605044660107001e0140d0401680d00c04003540d420119119051b01c5408107085162109a0300d003e030207c0c05030441001c080300040010380700242c83c0b038201038805860301400f20303080103060302a500903110301003e81515 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 383761843 1250 383760593 383760607
    0x3120c191104090b0f060613090e07030f03080105010806090c09090712060b0c2512050312180c030d021203091c08011d010506040b1e1803150603030a0f05 68
    0xd07485660b00300c0384103000e40701e510318010302d08003000b5030000c21503800b1f0003040007400b5000104080b403e054943c0345000196040b8818110703450940b442d0030007051000c804100c00c0030f15070803000b601e0403940d099846070002ea0300c00d0706200080901350383d010003035581480701110707601d000c00b005548000c180c50954203680740d924000003a00c0c415841041c81e4000001d035040c00d41d070240040c0300c00c22042e4142d43c000085100d0041d51007501449102911064200c510f010084284100c4280d080419400d5007181061040b0030f070500780099000e84244030703006044819081c04541041c2c0000c031a00079060802c020301500301980d10060000301903005490106c0000400d044500c42881000c0d0740e0304400c2c0d030402020031010300384a420601d044c0b944100401407540d501044a0945505118103902c542034086000d03201400701c44010060035003c5800101278002d1507100001d2079048041703448480140303210610859045e0b034145e070150010440140000c0c041e083d1511103004ca0b02e1705501d0420 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 383763093 1250 383761843 383761849
    0xf0203010507050d0f0b01200723010e0d1e0c051c0203061005030706050c031b1f0504020a12051203040c060e010806130e010b031b03120c1911 63
    0x8400c035103002c04144007184185140c9018030454120701200c8000704442000e440000c1e02e000380300000c82e400d594000d20748100b82c0005001901c010008000281c11102d5400a000d4405001d0001940011444150740c03210740740107400594915041009407400340c1d60081d01c208952000710064404441c10000060141c44500101d00c100d100c28540090380210380c41010b0400f2409040c1c0001403c94090500080e54046130300c40071038000e41410f981c0c400005600600b503000b100c0b240001a048002c0714185018046621035494056510f03504442d250381c1040f40444034107840c080e4100c04803590138081141315035a00d0400324090070490310780e40c00e04611800c1e036a00484048075114254001005540c2d001400b101480000742002212072030302e03c01090030120012125281d00340c460000400d400c80a610a03201c845001e419100b0f070309102029904201680340242d402031290500d28000e05000c070064940d592035060190540c60404545101054050710b8240d0740f182182c04010f603956 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 383764343 1250 383763093 383763101
    0x5070309150603021c030e0405070306080109050c0405011a040315270c0501030501080a0b1b220b04060f030903201f1a0108090f071d0c040f030f0f020301 68
    0x1c841e000c0c0c0456581d00b144140b10b94114043d2140c8802c0725604030103030000340c0003945c1ca000c1030f1080c3c9000866503550403013100a05030650011600b9460100c024040c010045440c600011094038203110a0741d9500c8030050000002e9070202820a00b4070003031002811245c1d041301064004080880d8007003103035504840c0031a0702c2d031b2b044200e00c500c00c10314410070181014070001041c0909042105d50b1400981c140c4403d851280200700701d43d04400140202d81401ea010b4007040070400403601c40340c04121f600c07002010201c07503d00c00007d000c00080c0e1034449104071802d49002e070740c41660540c01c021094010305407440003203050111440a2504a04d071521003007607031b42010380c001c3c480603e00c402003d03200000d03d03600d039141c0f50601240d1001d00d610140100e540da542840c24076029910f82e0011400c00e5408100c902d018003566000203444a414043c4e400c0c84181002d082d0380d680c503420381c1125284110b11a00940c3c0070042170800c041002445211302b0107020348011244003029600181c212 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 383765593 1250 383764343 383764373
    0x306050a200a0c15140108030a020106080c0d021c17130e010303090308030405070803070309140306010317090d0f030203030103020910060206150f040903090911070b040b060d0804060e010f020a030801060305070309 94
    0x1f581c00403034201d0700540e09001d40e10040c50480003402c1401507500114040b501c26a4019024940400e0f024840703a009800c41002e4a400541c0c1e40800440c6032440c00c46940054060504104140c0c0045401a2040905812254580c68141410303141d5503da20b2203800c000d006031080e000d468000614400148014124544207540e41c0d03103071070b0625040b0030145404a040b240640e01c0040180300081aa1001a13410f4111000390781d2112042800030304c1300d0380388190051001c4c60102c040c07010941c002001c0c5040e641300716075002642c1c1c0c41440d04801741a0a2040c04c005a02110120303107010501b4602820f0094090400405585a84045400c0d142081022000116014020010780800384241d0114002c61400380c2d20b000e80c552100d109000300a00003401840d00400414010f6450241c0c01100b90f40c070015030b64480781d075060080c3c001c140c0d0700280c90201d40c400c0d0107100300c1d510219199000703d80c55210b01400364280301045000f08002130441c02455900c11800d80410546801a010 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 383766843 1250 383765593 383765609
    0x24091e060109031e0212011401290d0203090f0a03050a0806010e03190302010b010207080a0b0705090a09060f0b0c0d0c14070f0515090603010608040201090306050a200a0c151401 78
    0x4114124418040700180d0b0b03044503030fa44d914141c0f02c00c8c182c01d0440240c50455006865640f41ca02c18551441c0c51441601000c076070755400000c80c0d005484598020754894040301c02a103107007a0511120985488903164000c00142040098207200c80c06400340940026061600f4600ea000f92400b09241040140200d01c0303a5400b1500902010741c240a03001d50b540d4280301a24400c0d1501410302c5d40d514519000400688807400000c45141c40344044d14802c0310010605024603a81b22241d8000b00080d0141e89450b120b04440030800e000c0440455000500c3c000061520500c040021030309122403030000c81b4150b048644d0b10a101e0b0781040040b01a05104440ca28040d10300700c200400807100c4620038496041c1481050701a03601d420a030b904554035420011100d40d03462004135240502900000d01d240d14080c24441000d4081c0d01c2400e01d5490a40590400c6a01a20011070303402800c0a0000044400400c2c50004400300500c0e00d1103803820001003402a0700c407000e0135103084240c1041d82c0b = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 383768093 1250 383766843 383766893
    0x3070f14070609050f1509060a09030b13080f0304170a0302090415050d032a03032909011203050f0301090b0102120f0d0207050a0b24091e06010903 65
    0xc8419020701070315004240906042c0720840c50074000c1860310392070100c02482052610800c81c40c441d0020110740c4d850a0040c0303056500c0d8000c04004c2c001f080307180010b0f030703000c000f1138002801d03219800501c098454100c00306500300300c0d880c407000311680d1000304104d5142061900e110b010000c4a0040c0400614507100540c03240d8405007071004032644212501001800080100846e89075190a0701800e5018075014000c158107007942d200c04003040400202040c00c004a04051551580c0b0800084c11071000c1640840380203107074a600a000b00ca0b05551200c20f460041025021301501c13801624860b00741282041102c1140349010b410907848480020f4031030084c1d041e07540c1e0522101d00e0076158007440b2420042280b171030141c14024040c04c8807005a000400c901889400c0000b180700d5680070303544814925003804440300d00c201919a2004c4a0400f030708080881c5030200640c2e1203030341c20034003180404040d03841e11603181102810060610602080102c003041c42d01c40c0750900f04007d00c510348 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 383769343 1250 383768093 383768123
    0x2030c01151e0302130b1f0f0f08040309152003090906030303070522051207050103051303020a0611130303051c06050306070809120d0509010615080a020c03070f 71
    0x340c5000310308100c161280b405140144016943c200d921610080304082c0012140c80382030203c2e0319980c0101c02d49011440c0d003800030707000d0342c2c1c02192110f41c0030300307541d0760405c1103d800d40aa035001c00580d002808610701c41d400380202002c0c004034540703040203450290f40a851451034801841c8440c90465000d40002600f844581404544940c0021040c1e0003146507242004004000d8014a4800c9443ca11141401100c000c4480080c101904004181c6000704031406101559000e03248102d070301090500c1d001410706604016102c000d03d4141e000350015040603510302d4010300201c0d0948841000900c207a5041d4144c0700b030f041018610940710f182d5680751060b143c94501004180241e4a03a040280500858074045259500000305040090564072803610640c20203e41d4901694804004108240f031240103820044c091b45051008100b02515800d01115070095020800003090102c004180807072410381c014194071068038140d904041581d03450444d100322919056680000381003d407 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 383770593 1250 383769343 383769359
    0x60909070f171203071202030c040b0c100e0726030f0a05040812040b0d09140d09030309050301020f0a050a02120304080403061409120f07300305130602070302030c0115 74
    0x140310300b25107500700c0f1419490000e1009062038804603000082680201c003003010004841c042c1d50103410605d05030394407000c0800d95180e40d41d1240c1240140c02d41005401c00a281300807070300d90709a804075645d010141108010340c0e20781c0a100c0b1010360301c4c0e1004104122202c9150001703001d0314a090703522103a41c0d503d05107810340fa202e09000c0722500000104810000c0d03a03181c10443e14021a8011b000ca01b81c040d07400d000c90410295032441015000c2e00201000543c3d20024100c00d0707074030035181c1c49003098662081c5400c078017a00300341c40c01c0200d08100200c00e26025801070982204584112289141612810019500706490840701ea10010a050041007680c0c0200303d01d0102110020b1201d242040400b1307661003540d080208070480010340e07010300115034411a4030294010b6100500c081c0c0b0384c01424510f04513240003c01d420b11103844c441c1710300e11038012035020f800c407100304404d44801c4d5107420000f50302000c8100c1c29444200100c242e204804c0c0111405403001201803582d151a000c05 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 383771843 1250 383770593 383770603
    0x110a1803150e1e0703060b04201b060f0a05180f030322020a15030902091006080705160209060d060507020a050106060e030604080306040603080f0306010e0414060909070f17 76
    0x9200c00d03400300010160000400036081d13046a1300301300003081100303005001c20000c12910246900035103004a01c0911501400000e01d521082001d00500740c81c0c07907a08240e11840c0541d01543c0540c071000c04a4451241d50b00413507046920002e0b001a030803040141c0d01d02d000010219542181c1000c001c001550304090001400001b40b80840040b940040e070004120285c1030040680c802c40f941c95401c0300c58030a60000c0c601541c041c05514142c2085545000840c800e40310300000214564001454107201e02d0540354402d031084095482c264681d800c00c00d02d10401003546400071020644900410a540a60380c000c41c02a00a00408009414080e0075518983c0183d41030095001d0386055a85000640b1588160400c14030340c0c580c0c40320000200605003d0340b014012802c0402c405120070001c50085010340307000d88600001c4524203052106590000c1800c1c58048403103000902c450405d210540c0d40542558143d030402c64948441c15140301c02d503008040208511492844220800c110f = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 383773093 1250 383771843 383771863
    0x303070804020a17060414070b1b10020405150705030d06060309030f020325060e122113020105030402040603021c03081e0601051b060406050613110a1803150e 70
    0x704c8124240e9070405866a20440075000403c1b032a1901d2080e00c038020b00303000c00b40182074500c5149549001c607098450340341c0542c09140442c2d0040b001d0280b409081403084600300e9201601d501040c84511844540c907400003501610b02c0d00080003402541c800922660300a4111f41e01c0000313014145050040214001038604020755204005203043c6040044402c020143c070000390f4000e00c0c400313140c001c014040c141d0441e5071078441c0751800c580300a000400780070f2030f01c03840c080d042e0805440d00c1c3c2c00c8041803007035825050900c2c4d112441c40255100c0ca005550081c00500080b982c203035039078081001d106020800000707010010100380105503010310a2508920300c0e464111004400b4180850480d01c0034120324103000001400c3c03204851000d402c40142c0000c00e060f07030760502c6c0a080403400b42178110b500e28490b0111200d0300c43c4d40c111922848006104a00c141c500f8001c0c05101604d00002ea40191011100c08400020008405c508095590344410740701158070080d003c0b00c0b0f403506030021 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 383774343 1250 383773093 383773109
    0xa1a0708190314150d14061608070507030e0f0409020a090c11010608070b130815190905060a0e03040e0c091c0f080a030e010903110c010e0915120303070804020a 71
    0x140a12800c00b408070b1800e4001301044841c441c00d070401d40750a01d1851981c502c140f04d140225420400045030501c0354030385061041d01c4110855680b017104407a90700c00c1200040110f0140400b040d40c41c20814030803041844042e0002510f44030030340004114180d0380e0f0002041c0c0d44c586000d42036459002140301d040d505ca0100a0010724144110b184d22058140100c107103154021511908100e65001ca40d00141410740985000ba20180b080c0400e40c0c0341120340c401811001c56200d0b24074901132240291007604180504036a813500102600500541c03a08056540710a03c00403921150070030140e070081000ca01c149a4134040502800740251540c00000d00c1d111076654020045940e4020b000c51280d801182c0c0c9a60f95000b0b44150014030700300515000c15841d12003100101070b040503020001c11100400c03038032121031b00e400460b040000554140c1d0010880c0001c030b1828900040f040c108542d008050490721603801c101c8510f1504121a400006080c002c01e20007942041e4605201400201c = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 383775593 1250 383774343 383774381
    0xd020418111801030b0604022205010813080912031c061e050a09090602070b011202041a032503080a08101a0a050a090506030106180906050a1a07081903 67
    0x8401c0d850b040000501c00541001201c1e400101940d680d607040343c0040146d060040700311082e00c50659071444150040d14045040c0da0045200c0a184002d076446459004101358580801c2c0b10034003c52481015400303030984014050516981c90000641c200d44400107000100e0510b00748808001920489030100d1184140b401480a0348690020f901620203428010420080c20b252160091180c020060605420400003084000752101a00c00d12070003141c05108810601a0210b4640f01d81c1010a605601070134001c0b1001060341c40c050286800020b490380d00710360b00e0f2038024403a4480c207003d03c00101c0201c100b12252006228500c054180801441258511004508064400c5600000a01902254005d0300a1007040042c010f048040c050b2270301e03940e45101c05450b20386116041c81131043d0281c800b081007601407081c103041b6540180502e008924007092911100e117800c1400d242c011080000c1d0000c140e2001c028600c040b2400c00e280c803071202c000401000c075044004e5240200c010 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 383776843 1250 383775593 383775619
    0x50a02070f060203030103120e0307030308040201110c1f03090c090b011b02010e060d0f1e241511010c0e0a05030312042012010902010e030f1b0d02041811 68
    0x1000045c0ca0540f07174444400c0d540b4182d00360702900c2d0030100504065045c410500044205944025000c1c0502c0c402e0700d8103441780b00c52180b404d0b111840b010119400080400c0031440504d01041c3d4400000c80a040019044203503031a078004998080d0080faa506448203202101075900000b22101034038502081044141d050380000c1c0b12005a0300030798070542000c2000c00900c1c11030b5120b00b69040c042081000702e540802243c1010361003941440d804985801c4002c42800b00d40710180103503440180b03c422402d81405280e48522062902142c1005a400d40107199071400340f04580d2a01c0300d5440b00440070b40d4440c02c1102c801c200d41c1110b40a03802c24010030000480310340e08a50896400701c02c440ca008080080c14070403c0351200281e82c0304090f000d541d4444003043d4001c0d09903074001e03030321024020740320014540c6d030304031140740040944e0100402c9100c40307106040100c001080103040014048040d0005819038a608001d004031702095100c10080009508802d078002c44255144030090706 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 383778093 1250 383776843 383776847
    0x106090e1914070f0306090e030919080a08040906091802040b040e030f04090b1c060c03090c090c030c0e0307051c0b040b090105070507020d030c02010c02040507050a02070f06 77
    0x400a408140c038030310079000d100e100031600d4000c040c880d4140700b8100002d01d04101d000f088500e0000d02030b07001c24503140c004144415140a030540402c42d01c3d00035490003c2590601107413103d03084000c400c0d0400e82c1c4010903a10300034420101c42c82d000e0f8a440781c0740c0f070829441c00200c44d16540500c000502c0c14030003202c00c0c100c020220398034a80403200090542c607884c0c0410080e0038031080003d0103000009524080b1b888050241081d507011010400103a8444010f015203940c48501c182c2402032030700030000c001282138101ca103100c60340e40313004600800b8075079840d003080307540e6040548410740392910400c01c60b82c1442410300c5004c131441d2080b4650747d00c070040b0b074032001180951760281032070f024411030060f80220340c5401203a111041001c03a180c541040c5070912410344195031039500303000200300b14511031303c15210340c5500100105080c003080d0b0740c00d2320a44010300c0101d042c0080c0190309809a03030b682c4202c511400403a26015a140f000340c0d0001d0522040b90031820314002c1400c0103010440d = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 383779343 1250 383778093 383778119
    0x90b0103020a17042409030e0f03120706020403120804030305060301110a18120804050102060f041e2604140d200d14100f02160b06040e0a0f0b010609 66
    0x741e181030f8068000c1e01c0741c2c200160780410204448841c0210540145800c141c0742e0312400d4502d003e6501e031030080e0300100400001500203070007190706034400844090b14a610b0001802e01c01d11908005207003c0d569a158003000c060840d0920201d2040740c100700034182c0600443d503002004030000c0040c00310300035811040380100e048050400803102200307440910006406c0000d0402c5891640041101d0324107a1899442400703000e00500601010801b0791140d06401400381d03910415000c0f101d1200c114501501011107402c3e50b09894241003440e010300c010401500d08004411825511410039460036000d10b0380d2000c05024090b209006070100704c0350301d00003840388108220200b0400d03003500018042c040c0d000000c0c01246040395902c02030700c00004c03003c003041c203c83c405001d00c00908501c6000ca009201c030302007030702c0080c400041c0080d2603003003459030024005000280f5601482d40e0a0724184c81500100c680b078000e0300214062060002e51940101442d00d44240030509102907107a00c1 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 383780593 1250 383779343 383779367
    0x6210b0a020c0f1e030f0414010e1305181b0607020103150914010b030c1209010612060e070b190e0303120403030212090c0a0e040f0210020601090b0103020a 69
    0x1002004003003041955640c044650403038802c0c2c00c40f80e00303604181c0103680740c4024000413a2a05040a4000e9850038080140c03041000c820020710300307152801015400a1592206c005d0400c034045440440b0350ba509400c4c400e00c02850b11001880d440e060249241c40c102c18181074080743d1040c3e0660000d150815030481251006a80c41a158101c03480140c1c050410010010a0300f0456030012401d201340741d00900544419107422246030b40e0320043c0302d4141c48280c170f220185442c100002559202e80310022034000881c0000012132940e00c101000301c0c044a0001111101d842d1118658050410407020020340020402c6500e008501e0510001c2c00d01c1a1100c101408018102100305a8007407007038488168548450200c0ad140c0340c41c00030000d5000c2007c040400c908000404d00c0200005103c191000b405841ca0380e0050415070100020a0000c10850311104070514000041c0c40340345410007000c0a80c3c004200c5941403031900c6040d215982c42203410548188017803152903031312007244648 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 383781843 1250 383780593 383780603
    0x30d020606030744010b04050c220b030106020304050103060504020a080f0a0b1011010509070e240d120f030902090a0b0d0b18100504200109080105040309090621 71
    0x200c00001d0766004401029000102c91161240c03200d10030f601d00142c01030804c080e0750080152010140070401124025900206e807418140080c1c2d40060800c5125800400540e0303203454000e5444c3d80424144d4400d80000d00142c201050401c95541c05000701c2000d403804403410360400d101410003d041c01c40c000d10511300301c560000440c00b100120b03407162a41c00c030003802c1c02c0700c3c1032010380000e000319041001d0000158a040d00003080c410021400d80309403003178203102c1314107a11009441c0d0241101c1810507081e040e9051480341903561407230301500c01607106051042c52a80684009000000480d0301300c028141021008001a600c410b1840e5001480321000030b4030b96412004110040303013448009100117500c1051224403010755001d002c003500c09504071004000004080c00c26254281e6008005c442c801c0003902e00414a000c80711100c0314185001d50000350340d0f4007003c0c00c0d03a44c196000c0d030100b40000000d110b403850600603100644500c0048080140d004401508404082000a09 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 383783093 1250 383781843 383781869
    0x90b10030c120609090c0501020d021506180103050105160507082203200a06030c020a0b0601020f030d0606020c0d080307030b010e101119120c1a0a0209030d0206060307 74
    0x145000d00001e100b105041002084025101d03802a0000e00318204181d803c18540c03840000c0c6588002401ca400700d81070350181c121080002c0c405410707080d01800ba03641c49501c0c1c9100740d115800c5604518003d5001d4000400d81d420714900100301c2c0703440d0742080000c21004000700c0011810700800c95290402400c085c8070045c9284601e081c10f03410b280c10081010900000d21100c4083d0440796400b08002192940c00300c40d074982d416004c40d400b078032500016030842c21205000c0703240300001d0783c2c1c05001030041e60005244031048508540c07244002003c5196250024084540c0c1040010701402d42645c8014030031440e5110841c1d00d020040c002c4040544503020000513900c2000f2400020402821b02d030700036800c2e20b101420342c5000e040307505c015220b4012010040401c003142280429088550005406020340e0308481d0310000300e800b44c0b0925041400b10001c00d0556102078810201e41c5d0300141c07901c40707071030816003000c01100023041103512000070300003103940c0030030440210344191000e16 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 383784343 1250 383783093 383783111
    0x304030b0a060e15040b01090f0504021c090f06050916090b0a0b19020c06030609190e061311040c1d0f090f0f010e0403020d0807020307050a030e0a090b1003 69
    0x20780507101a42151100c440120240001d40341e100074910718400c8225001c1c04841c0b001c0300116a0035480b403044109030500703240100003a003055401004540c0326816a55104404800303c001a00d1060504a030f0314a990089038003400031a02c5100e030000160f10103020750354001c0305681401d0401c1d005400001e81c1e92540c8501a54a683e1440024880c5d0b10071a81c0714166034103940582818040c1c400e0150245198101c1145004022a446084000c104c80e0058807016000040d50a012034040101e680c2c1d4032071849000001c02c0010722902c2403800da419810741616140e1070001c6100c401c85d0040742400501030314160401c42290f02200c1100390820246808400a00714070084170348642c21006030b20a000c1003006140c100342c462207030340d0003034440c590742d81c00c3d05d90710984101d4026006130048842a04018882c0c04481c0e04401c00e40b048a091003000c0d200c19040081400044010610b800e194098034280043c00000403c4001c800700481c40ca80b030702195440910400c074104241c0e44800d00 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 383785593 1250 383784343 383784361
    0x1c0f12230a021c0504060216030f0809031f0203070e06031302041e0f1a0a0605030c1b01050907170106060e1216080c18040f062c011e060501020304030b 67
    0x612840030074080480c03e01c414024050600c0e445070140c080140542d01c0c1074640100c000e900d00007281d9010945002c490610303110501c0070303001401865810b01611074000c4400300000a20754250041c50310040e80c9007450000030344080461400e10340946014400c2000c0304076a11031404055070150703000305e040100c00034500c804000c9130b00e00141c00e602d48091054102d603940c0c8a850000c01c0c10740300c122040c901c902084012405c074860707080024030410005940e002e2044c0a0b00d80c1000c0003050250070071079410002e094403000c0362440d02da0b9104080c1040001515400c541000b90202c00030484117092200041240b800e140d1064042c00801c2d0200c0c0e00c01004000d6450f404d000105810404c640343d2102a44034101459901c0c829018044000c104007100c440e094022a40481c241d1010981d80d07640ba00500000c034101803c11a281e1180041d80c0c0c4003610040140c00700c5000003544001c180b203001c8443c2c07083d0b680e0520070b80c60090706118a0740c000003241c09403500128808401d40d181184 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 383786843 1250 383785593 383785603
    0x522050702010b1203180a030b0114040207140102210c0d0515030105010303020601080609030a0e0d0c18091e081b01020409110307020d020105241c0f12230a02 70
    0x72803600282e03504020245060017002418441910f40c031040050007030780c0104045415580009059581e20f1801004921014403500810050240016041580540754170580074000030340406240d400041c08100e401c01c0e11a0251110030482181019082103e42840e19015821030000015540d101041e030742c9001102d40280950020000d0241d9a160b1500139140c100a100f54080c0c0d219003008035070f400c00007005540e10983d4a6840c40310401007034040060140340144c040d5039000e44030b05d001c58070524000e644442d208503490003281d11880740c13404800118581148130030404441600b000080c4c0780b4000c03502001c1e403150100c3d444a2090341c2881c02441103a01162446181c038844a001d540c900011f10b100f80302540030303103e0303580400d40168280c4008130340c1600703100e0044814552001000118008440000d0180008402e10410f14110300000800c25956010b510452804004000510090000c00c0d0315220b0951040c4400c01c44640c5501c035110050440041815003c03d03100b004 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 383788093 1250 383786843 383786861
    0x60d060f080102120705070b0a05060111011410050d050601060e12010219030c17160c0507080106030611130605030a0902030a0f0618050309090a02090306090d020106052205070201 79
    0x1080354000d9500c1003607900031361080582644038544040020030035405201910080c80d04840d5041c4184d840301c80020003464000c20705070601c5402c40c00300c086400240310b41c048182a000064142c0d044c00450310814041c541c0c401807141100c0d80c804000102c001c40c04504603070b06418230141041c7d680c40000c000e4213407804400115880032541c2c80c20002c610008003540d2485480c01c1100001c80340301143c0151035922804848180704010404446c0d1081c040d03050100c4d00d2a12010340303151651100d0a250703e540c03044006a450780814418000c1ca440340038580c03070074040190310700109408260401e200c58411030003070010200c0041c0e10070455400c40300046600905982114000b03203440700c0c01d080041d50a807040c5103051818005130302e08040141c0d41d503403c540114188070b102d02c20170050003030091140344419000d202d114601c1d1010040300c0e02842d18400901544058008003e007115585e0344038501c1039800c52280c00d090b146002200d001481c14140100d9565520003081e401340600312 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 383789343 1250 383788093 383788109
    0xf1802090f1314010f030b060904020103020c010212010e0901060e15030703080307020d080108010b130f06050d050618060709150e061b070e070f180b070c0303110a0c05060d06 77
    0x110700c10803440d071255038015814449042c3c5641c85407007080c5000194000104103181d00d60105006207051000f066000e40305150240c42c04c50040c0605007a40c201c0d0710a000940407410040c0085806800b1807030f40303c3d6086000f004828500b0f03507082540600038020341d526504213150007180351002c0c00164003840c3c0107001281d4138142010025907440303050b00340a00040110001040c03e1b034040c003407903440040c01081802c907040070707030400c5000b400c100401d6181c02e581e0f2000000d05031140c208030b5140c28020800b5081e60318003207000406401026000c850150401810060a640c000054000b540e1072101080e00c0030140c00c005030f41200c0424590b80e031040003c280186825800c4e04400c0142c204007060310722a030f90707603c1a4110010280e82c0b0b500400c41e4002c4030150b46210302c0b2282c03100300d07991654010190307441001d5001a840f602064542640202c2d042c41410381101000c800d1100440042c118040c00383c44480c2558151300950740300315030004810f803110045401102c0940445 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 383790593 1250 383789343 383789359
    0x4030b0c04080703150c0c03020714040e0106090902011101051b09210303160507050c0402161a16023f030c07030212040b1206060f0a020d090f1802090f 67
    0x3814004121708034102030529aa09041005800c5031046440001c4150325800504149040c0303004451104050f9402641056440d842ca800800c0240103a0001340610040003071604140d00005018a440c901140704607070400701440403282c62402c03000104444285801d45811000d00081e858a0700c0300b04004403001e0b80d60110400708000310046005601c000900070f03c0000c042c0045d5104d000720031014200f80c00503a81d80d001390500390005c180740800160b1403181c6188540e242c803100178114042c00b540c03407484802c0101030003013900034807240c503141c0c001410001c0286014140d00c000b00703156114149001e0340010042d14240711000c02c811304d01d03c4102e480307140924200e45243c2180320300364018400c0c1000c0d01c100d00d080c0800ca0701075134808e0400503c0e200025288200166001d0b045e141c200740b00700005140083c00001902150351282c0c0680089d10440c1c0005001e500c65402141100e090070808101940c0da0594003051707403d580c200507850340024800140745c0c0e802456150342104203 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 383791843 1250 383790593 383790599
    0xb160516051b03010606090513090209190f0908030a0b030c0d03210209060403060e15040f0507050102010e0307061805070e04030318020d03050304060f15090f0c0504030b0c040807 79
    0x20100c0c4502d0421410074400740d411000404140c00d9035014441c650225013156810b01450030003080000300101c880c0030114014030542d0208030058800c0f00c0400900c1c48542850803481498007650080840008050180b040f141e1a0080a44005000406029a2480103440c42d85040c0015603098500074500c0206016a0401a00c0c9458940425419070b903085c03000710182c0564429918004400b8044ca824142580c2d106030040c00c5800d003210507803060b5110f902c8603100c110010f40c82144121190241e040d6940f0f441071402002e9049281964102017026118404c0003050b66291900a070000c5500044141c40e404e0019410901070100d000c1e4110204040c3c04012110f40100e200785e4041080e2511038501000c015410480213500c0254142c084011a00c40c8002c0c5030020301802000031140c0105c002602240e2071018a8140200c51500130000411346224034a0881e0712004140420034441c4030027066442140002000d010608000c103e8503101d440503640541520320407079038444e407 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 383793093 1250 383791843 383791853
    0x1009030b0a09050c03011812020304030b01140319030f050f090d060c120b0d02100e03100b030f060f06090712020f18240a05070204110306090609040b160516 69
    0x1981d0b942602c540c40382d6041d210450605101342482900c400c4100c0b0440001503855240355180014000f007144018040880070030080340d191130081c2148005014030440c80e405141c06e091031044004104041011407501117608005142c804010620700255130309960740304050344d409043d01d456000700c3c20b03058205c00c1101e00c0e449031a09090a4030742c0c3e08481c008800c1c0350151007002c00390307640080012030312200606120310f1010360141e003802c007142c10041701d2001c6860002c0c4106180c0059440e0860001039040c142f214141444100d0040c000b1450100c00140050780003604d110300580301c0800003130046105103008a004a00b00c80190750301c458001c040c0c00960428540c182d0b85c0002e002090b40c0d103250940c80801c40d4032140210120164142c0210241c030f8021514000c14050100803980050b07480d4803444006400a0541030f449041440a00801410040030b140c054280402403001040201203441d03480602e245004c002081e00d2034080310b0701d00402074482e4804581000d540d007042 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 383794343 1250 383793093 383793101
    0x3040b160b060a0305070e06040b030a1a070f0e0f041803030519140a09020307080d0306080705010f0909022a0a200a030b06033a0e0f1009030b0a 64
    0x1d01840c0d0200c9561901020840800b40e40e100040a40d8460442080364400d6a42d4040c0d222030010b00c00601ca140c101e01107401c0440e03440e01200c540302c00e4280c07211083c91344d0000641048d02c0d07140044024800e0000604980030015031f152185107030841003e5a555550080390351201c040e000c0b0340e800710040c03a01a020f04070958071104c005600041002c6458100d01c500c100c403481e42d580c8051503440f820b122600030711a104099030107018011022801a078208803021300d0000550340017402903d01401c40d030400800e500f02904020821108850103036210003202d040d28281d0310b0050781d61600c681e20002300310001c68040002554003015010902c3d010580010301405611042c0c115000c8031624080070700841403a80d400b4806101c280041012050900da2000018044071500100c0c110380d40310504900310921506444451918055000246007500390b00250504908104c03c840000b02a45645074000d4080e2440e01e16100c3d41074030030004a001540c210400020500704034010002138 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 383795593 1250 383794343 383794387
    0x807050d0903120203070f030e0d060612020a050f01050702060a111603050615060412030c080d060807080703080706050702010f0f0c17010b03070c0302031215090708070e1203040b 79
    0x101140200c11982c860000c0112408503501464040700d180e51f83d581510400841440590400c1c4c030100c0d071000007405482200041c00103500c01c0d1910b10b0300340c41040440c6500f178000901034000c00b00034a03990b036007203420358a02c1541203d515850b151504002c075000050480200058440c0ea051807003100c0c1ca00100704240c0b8003c1e02510120b1796042c0c1680d410000a01090740c101d20100010828500039a041042c41c81c4245807040040c00715451b4030740180c0103000070500b210f80e01d18041202c03010410150004041142c09040c01610b07684610101340948a005401140c03140001000b81c0d1003940900c2101c030a03958200a010810210354005003100c80d000408a002684445c45482500945d076040303070f00b500c64040c6180e0f520807040700c40d04240901202980320500c1103407070000422200034400c90140c40031400d1020848200070160300003070a00002e000050083c45400b80e48010303c260300010a440c01c2401001c16079017240703180b00702c1d441140c0c1c0300c4007c54081d800a2507050304d0100c0e = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 383796843 1250 383795593 383795603
    0xf030e06070c3506060613230f011103090603060f060705100f020403150c05070206040e0603012910021e030c062815030c1205370807050d0903 63
    0x1c03202c109440901d24010410f82c42c1c0076481100007648901d442801003143d0760102850900c0c0c42e55803901024507c54400e907414440c00580351b88502801c14808681102409280170301c0c8413000070b41140d49a203e420300d034034014071000002940070703203459035607111008021781060303039542080c2002501c1d601011205507036035041685c00c00b11504a802503d0079282c000baa40c100184040b04034800401c032100d0001c0030701000b0701c0154050b030303644005000103050b548020f891070715201c003c00d821100f03100342d4840a501c040900b090342004071f40f500712090b4130aa40700c19000c028980c00381e19040914403180d0f207041d0340010b1103860700c3c4040040e01c41c024081045400903100c0401004403607030b98020f6050200131822000c40f11210f03682160743d555820f8a8009181174481c1c07210707150744403a60450485170b01c0000b085d2080000400c8000d040c500c405140d50045d035003034191040003100c1c1e9000c040c40c01c2d140320b080b4800e1113642c00850303641c2540300c411150000c844001c0075004002920085d20 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 383798093 1250 383796843 383796899
    0x60702010e0609070639030f05160602131a07020102150f040b2e0e0a1a0f04020d0c0216080102130909080d050114040e03070f030e06070c 61
    0x10403007074001040e07030082e6010000f0b00802414030384100c41e200d02d400b03010210301580e07040c920746041750814244017601041820804a00781800c02902c200c07100c49180041240c00c1040d04440c1e0080750340341400c240e0049026a80c1c131102400341c0106203481e0007202c1c003031501030032800b22841650000c0c4039091003a000e031004810b050381101c450f820f00302c0305100300c0252000041d001450601c2c200c2c0d80300854441c500c0200c22080d140b201400c60001e2038210390048058140150038100082d01e500c0603c1c08002e1040b100728000300c00b650b100302c0303445600485443e11001e0040ea00d98056904880c00c84600f045070090403403000b0f41d20b800070a107e0326504400540881c040381c041c002c44400c5000c1c075a06605291405002c2c1006002201050310304410a0014003203042c050b000c2c0c02d00030143c8503241d074416410310342000125040744c0e501c1c0340281d0040120200080355101c1c141995600b40c1080050031070464045100e42c41800802000002c89800101344c0f004100d10518960a82d166450 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 383799343 1250 383798093 383798111
    0x409060609031203051e070c0b0114030d21110301050a0501020f06063714060c0613030c080705010504060f0506030a113f070b04120c030b01060206070201 68
    0x1488041c52404082c02c0003140b180d049040b14000d4101e40d400404a560010380348440e24000080d125099402400080b403034044082403180d0300a40300d01412500d200074502104000001c1c3e41d1f4a003130902035040c000705d0110741d4135904000b00403080194150b441400040c140003081d014503802400f500303204081c002800b0981c0d5200041044010504c0b07001080c07280c880c94100038085203646802c8030000020081c00c95a8004100101c0c1d100380300d061985119030515440c4081c201c102203407140504424000030002040015105801c0f2046221407000e80c102805c04440e08900810302400608000a0007001c04c181548060312550080d0010807034030881d940b07034000b522010b4903119131541c000c50311704c000305180c4541231981540c01030100b50700d44c50410b40151a0440e546103401c0b800500e45c07000d07042d04518172200b580342090724060b260307803030620401d000240a18040d601c1040801148602081040c0605401454005081400c95a5289002941d441e4100c03500b17001942005049 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 383800593 1250 383799343 383799347
    0x120901020703050301091a04090803040501060b0c0307241409160e0a1d010606030e160b04060f05040506030c1c05010b09010e0d0c1403120301050306040f0807020a060504090606 78
    0x3407109158582d9690b85140d00e809181400790401d060380d030024681e8100740706226500d500c1074081c43c5216520f500c5e101d2805080003030031900e145c0d102c011800350402070040840d10110032585410b6102c003101c0514840003d480107060080c05581004da880d08a147c5c64040c0100c020302d210300841404c5840300503041d01d210b9402c03030340c0b40704e00300c0484c0528001c900300c0c550f19013000c103c4200c00130506440441008200d421364000c0d0348030b84003103a5980c01d400d0015200703000c00d0020210004030540a01d19003034500b80144140c2c440d0700b08200310794070241440b61007003040340d00030100204055100d0a0a001c007101d56032203084102e94102d8400ca4080d0320303400f0390294a0486400b2007001e400e1007220070054030842d1610796500e91011a0b6402c03c030004e00c400904002910301c0080d103004035a910402d051624403241d6014080324410b00041259540001365107a00903400440070105d180c252810a44078094490002d52041d45082c1c00300e403082d48480540201e0311880418800ca680e103e0f42 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 383801843 1250 383800593 383800597
    0x40311070f0602031605190b0a0f05040c090509031e03010501030614031507030b0a030506010801050c04150c030302191d0402071707082808010f081009080904060b12090102 76
    0x1000b0141e00306009160000e00100407039802c1c04e02903c207039562038504282045048004600859503002481c2c180521034246201d880a03070030000c4420841801d160716a11a020b03400c2c481c00c80c80d22386503000038080440038001e03134484405005103450403010402c140c1e003c0741c000740502d0340042d10748080010414070217111007c0c0010003034042c10b0444984903415402e010000c2a080500d0345802803411a40c6824210000540c044c001401c0741c0c0d4100300b502800c0d608003400342c801002e400d00c02801a59043d410800480085040032030f254200d924094000c3e0050030791800940070101e110020036034101258151902d43d41c04002400198001000304a018840010b450390014801c600b4021918000401da280c0c007440701142004840320901c0e8064400100340b0180524801042e89a40c1d000b5501502400545980e10072090801c45104d07550180740d000c000c0c82d03584442a500a20111000f00e6880140140c000d01070b0585495101c065648001003044010350214009156000d040c82 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 383803093 1250 383801843 383801849
    0x7150c170f1914040b07050d14030a0504031403042301020a0f1407080c0a170405060d0b0a033201020f030612030d05071d01080f0703020c0a0209040311070f 69
    0x2035150904039003000d10291010385095150900010015905100b00f940d000f4000908002c1c110300d698008602c0d10301e041c041040180e1080c490140048082003d101c030a907940300400d00d00c001083e68550400702d440d14001001c0b04e070303296000400d200a0201107000075140070540c0e081103040103e03500c003c500300c1c0716440140001410b210030290710b05119a21500042d00c99104443c1010a0343e16012080e034010380e8031102035844405500100084040c220301904011061241050f1130580070070a82c0c810442c03207103022596016002a40d0707649908160242d40c2212040b88080d0b10551b0b400d030000f0f0103a650501d5481c51005410489405001326095402420703455401c6440344004e120806d0803a2007059850301050080400191540c800d42e4031034200c1c0da94105404001c0307510b1100203004c002d070640c10000070070104104142845080ca4204120340b0340183d0740c00c0007020703450030415104d0b00294411041c00600080c150300405c403440349581034054500441d60f4079115407803030091b84 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 383804343 1250 383803093 383803117
    0x8070b040639120f020316020a0c050904060207060608060a110423130c0201150503060609060111150a140f04030207090504060f050703060623030f070207150c17 71
    0xd02500300c51071150003000700041c2c880c00d00c20f0f2180181c040e0321094901168050000b1580401013140c500c50703400d150103c02c1300d0360000c1c04400007070351100760303c3e0403150144a0052040740d001c18100001d5030b04665178290001c008000c000e440f4540940c4542058405550349030074500c0044200d50712400319001c50f81d031503120a4101c1c2c0c1c40070104488004000400354081d400035002c45020509010300310900e50759500029444c08180340d1040d48141035001207000b5444036041024a440d505a0241c200c0c10074200b02c0c44014400200c1031500390484021103030004800d061081c01e011640111000f24000c01030f0004a03582d10a2502003c071040790080d00692209400b0004516075074415038100b4026080403540d8a112038104040d01c03c20354103440081e41d145000c10040b980308448001031030903000848410076a2851000080c00050405100182c030003010410090081200300c006100365184002284059023014048918901e0300703076062401c4202d0000d03c4d80000c412920000700700 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 383805593 1250 383804343 383804411
    0x60f040213090510180e4306080f06120d020c1302090d03050a050d0908030702070e07020a061a090c1e0a21140a060929010c0c0308070b0406 62
    0x18910018081014190030180940c1440840c91f0003001c90b10881e44220701c03000c103010301704104000c910040b4070402d107828003805c4d9001e000c5140e2010000d9000400401043c0c095122132001919095500030106406d1140600c0d40307861a0f00400d10700150301c811115019200141441c040036840754038005544105240e290300000303030103040a0001900113280040c100900020300404640c0c9559080e0340d603580200400001a60412003c00680b084129050142c1000c04000c1c1d0b480c03560044c000c291949035451840079840d10728a9030384051005100388220f0030407040e081503a9002500a040000d8541110004c641b01d407822528101100d030b840110344078030103549003c0003a5004003902c0040c2c480e100c08444407030340281c0314068248440002007162034802184111104209404402d05201160b848560a450445140c0c1e202c2800c21202c1d0310304503d010501d0a103c2c1e00000d0400c80c2c042140c206000040c403403148282c3c4140c0f001c000700090320303d00c95204440102900524100 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 383806843 1250 383805593 383805629
    0x807050f010503041e030e09070c030e10030207330204060e13090614090f0c030c04050c0c0303091606170c0c0a061b090519030b060f040213090510 65
    0x40342d001198000c1c060064404000511850444040c0d019a002d41c0000d4074402d840340c0ca403810780740144d044402c1d0700b01034040c00907039a40600100c0d14006031500c1800704000800b0380300e010ba0102c9818550200f0742c15280c4080080064a101c01c201515130101441c620184107000b46200320380a450b615110280c051540608106100701d0302c040200380325486540080004006001ea00302d004440480a1540d02e8400d5080e8500014844c08001c4d56201381c0200100e924041b03045011a0b42c2075070041420b035980200c00ca110702c00e0200c901040d101c0001004481d00d000308000c00a9950803c2040c50310343d5460b0100c50790f001da2054403114542c80c902283c16000000014494003074240c00350b5407503100d1a00d54008171292121044c2d8400e50a844220004d98000000030150208440801d8101d01c404035000a0b443c19001c014490741c07448010800540d01c4c40a80261003400074001d41d0380d2802d44140c508180080c0c40784003101402d24000c41d00ba900c42c030840e80c050300c0f1072900502003500 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 383808093 1250 383806843 383806847
    0x1608190b0114010c02180f0c120a0504030207050a0f0e0f07050d0e0c060d0204031101020a030c03121503030215010801061503050a020f070b01080d030207022d0406090f05010807050f01 81
    0x6420050780c1804491302d184001038071142c4031204404038895465500b4642070034004401e50b0300030728048150300100081c200030050340410540210250b0030000e501c0d03a507450240c0c40d210b6150020765101070a8071000800c4500004180251a00d507071240ea03241d11802c00741d8194540c2501c0d0328000c100240060040e0803100e0784404154051042120300185510020540c40c0e4060f040e440c180a40002c0c00744203101a04207c89150341c2c080c80101008001070710000e02c0740303455042c014100103400b58464107603002c0d42c101c10081c40002d0b0070010744d1a52450040d661300924922694042d10520002881910600c10541102e0b0a0b6450700680610b0740070840007400010a00f50000f44c0c2801040454031155016200389842200700c101c09506010815242110200410042500401150006031181c49105107400f003d100403544000c00c8040088003501e1310f0780c0a9070403625098000402d41c41d26040324105030201d103400c00c010790301c0340c0d02540c82d400303180a203c0e0030120221281c1c01c03c1d4 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 383809343 1250 383808093 383808119
    0x2150402120709150611060405120c15010605070213050630030a020d120b0d020f030312150f090606040627030606050108011d06040c03020702031608190b01 69
    0xc0c600081c0c80419844816440440e8511300d80803048680c00d038030601080e40c1044406d15101c0f211002070605e49001d0351002d559114600c14024041c0010441945605041112006006101508510a6850b90001000d9811148003a803244e6003903001d981c1c025a143c81118000d4001501c2403042810b21243c51110141240c02c031b42d901c0c9100c801e004980c884c24005080b04404540c05081c0d412130103900113004a20002d40c403104107240a00c0405141d0381c0034842c80b82198195075111f1881144170000341980284610015003002c001c0c200400d080300481e8038252160b04683c80f44501c2d1400c1c0a1004c3c4400495040e41c20047c1000305029550056009251070080c64aa01040344080501040d000240c4c1d8000c540c440d07184c890910803036030444000da000d80344005200454480c442d401c2d692040c7c028090358020795503000c0c188021403090b011102100d401500b00e0700e8001070701200500030030310b40c880c0a0060044280d0000442040584240c0c078a802c00400c2a0390f90801c1d00c070340303450 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 383810593 1250 383809343 383809369
    0x50913030503060a0f08150c03010b0913110d0b1504030b0c090406170d031b02031207030b120c0406090e3708180406080307110d080f07050d02150402 66
    0xb45461300040c9050080b40140b01400d4100060728080804030711904070709402820000c820f500030700050211079001d605584a4010413250b8000301c9021955020040402c48594413031501d000850940b09501c580001400c00429a81c074404004241c3d0001e84a0003140070081400d041ca00103d9a62405130020303104420004100040c500e91301d80c0f500940028040b02008181c000400301d405080c1c1600c00d90b151074440701c400c20516070500800a442c0d2041d0713006130300c0c8541d040e03010846c000d03ca80e000103003801d0080c202c021a020f041c0915507890680c819124815400c002c40446d4011040c090003525000030801403201c0da680c10b11080c81090f10b140d0103151321403603d4500034030201c1c2d90f05e90b00c2c016004001482d614500061030390840443c041c1094000c908160007080382c0d80000040f903425540001c4544461004000011420040c1040c0a080100080b40207614aa4620000c10f01e441c4103a0440341010040407050382c840f164500100b00304114000010094100b92803207a000c = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 383811843 1250 383810593 383810599
    0x5370206090406030311070504060509010608100f080c1903080301051e0d060605190803030a180c1508010f0e0610030f1515020f06060d081306030f0605091303050306 73
    0x18000301070041021903559500942c0000d80d4140c281880140c103108050240101791000d00c00c481c1400d000c0b4003940c1c0c040c41600304006007480028141a240394000000d041e411012000d8142d844c1620341d81c1d100c620003103e2040b000c03040c3c0d005a02c21944400d1040743d42c8100054116880c0004000074502c2400f01d01600080310180036403030340e682c4424104254482c800000780359040200788159003400b200c4410004c00607050501c5071600010503a940100c24080c04600040780b140000c20b000c2650800500c3c80024400105081d1201280e00030f2980495441d01d0042ea0f07501c040c5a40c891192107a980c00485102c00b0491340d0424540d6254040d031903003000305400c61069400011140c5404407152078039012581405990421188511500300d98801012072419003c0c105032500000b40c0203a103e820044034510401c29003605941c280e43d41941d80e240d0440c1c2d1a040074000d010081c20016680e8a0310a000c24189440807125008685030303406407145009680d800e07600360b44040e00b2258 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 383812949 1106 383811843 383811847
    0x20a03022a0306090102030a0b15070602070c1e0302040f0e03040909020d02130e012a0804030e151207020703051528050405370206 58
    0xc481c118016046204090514645115500c01200c00703405020345800c0000d401410340c00380d4410041140c0512980740800c040184144807100c20200000c414030003000031072015805084058032404d00c8c41c3c29640c8514010f980d0100c50560440d0300d50b03460000744110701f0300f80216014440c4050007806106800040252030340614096181d4540c0d031440c3c24401c1d5911504040e804039005481c1480c21141c100030300d000f03403004582c1e000c03440d07081180525000250713654594003a803e5040b0190500c81c2d148003115180c0e4050801e03000c2062001d40d9440c41d07650041d20003645019180d126070b441da5079010166007103030010416415500f10020400105078046210340000801d00c10f0001c05945003e00c41c020340b088030329800314240740c0d140c501241c0c01007030340b083e40120b0003036045652002c0078441d00f01a40d22446480c15040c06241800141d0100801c00807100c50b10081102e4 = true := by decide +kernel

theorem cover : BRFrame.Cov 383633093 383812949 := by
  have h0 := BRFrame.cov_init 383633093
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383633093 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383633093 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383633093 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383633093 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383633093 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383633093 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383633093 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383633093 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383633093 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383633093 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383633093 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383633093 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383633093 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383633093 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383633093 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383633093 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383633093 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383633093 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383633093 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383633093 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383633093 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383633093 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383633093 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383633093 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383633093 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383633093 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383633093 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383633093 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383633093 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383633093 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383633093 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383633093 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383633093 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383633093 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383633093 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383633093 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383633093 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383633093 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383633093 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383633093 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383633093 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383633093 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383633093 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383633093 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383633093 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383633093 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383633093 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383633093 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383633093 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383633093 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383633093 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383633093 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383633093 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383633093 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383633093 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383633093 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383633093 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383633093 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383633093 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383633093 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383633093 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383633093 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383633093 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383633093 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383633093 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383633093 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383633093 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383633093 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383633093 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383633093 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383633093 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383633093 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383633093 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383633093 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383633093 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383633093 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383633093 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383633093 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383633093 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383633093 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383633093 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383633093 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383633093 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383633093 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383633093 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383633093 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383633093 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383633093 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383633093 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383633093 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383633093 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383633093 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383633093 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383633093 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383633093 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383633093 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383633093 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383633093 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383633093 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383633093 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383633093 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383633093 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383633093 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383633093 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383633093 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383633093 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383633093 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383633093 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383633093 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383633093 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383633093 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383633093 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383633093 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383633093 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383633093 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383633093 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383633093 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383633093 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383633093 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383633093 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383633093 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383633093 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383633093 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383633093 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383633093 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383633093 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383633093 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383633093 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383633093 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383633093 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383633093 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383633093 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383633093 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383633093 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383633093 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383633093 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383633093 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383633093 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383633093 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383633093 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383633093 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383633093 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383633093 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383633093 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 383633093 ≤ n) (h2 : n < 383812949) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
