-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0076
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T17:42:23.808524+00:00
-- url     : https://prove2.me/submissions/38f4a8f6-4c33-4c4d-84a5-6b677d2e770c

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 13489215 ≤ n < 13669071 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 13490465 1250 13489215 13489271
    0x806031009200f041a0102120306010801051002150903030702010b0a030807030809100603051e15010302120c04021b01061211040c05040905070215060604181a12150a02040e0a 77
    0x803c170001c48002a000040400010a03401c031002202040e50b60038041c4020b0791a18040740c00c0b10010001460b2001c2d41071101c20041c419128030695070b540ca61489041514410816040070003080703001a42403146c220030f4142103130b02040540c51625125241e10508a01a01308900d0800003400d42804000980182e070340301c01c0c2040f549640e81083c540f0707000c039500709020b500b50640c80300c1c031441070004400108000454819403a81d10303507402c101a00507800c4041550b400340e0607000b9150750315403001e0031000700c00804c0b0103201482c0040035401c40d00540c02c1001602a2422964045098401c0d40000000c0907100040d140c0b0071070300161030074000c80c1d03c015220341c1011f040000c590390103c0e115001250111707103000035032107040c208803582c000c03070103040c206d11356440e003822411119400500700800c4204200092038140804550810710614102d0b4490340025203980144100003c0c0d50780c04051a0401c60174181040c9000d86044806441da0800640300c2200c040c400d651201e400e0010008 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 13491715 1250 13490465 13490471
    0x803220b0903040618050102030307030504110a060e04050106020f0706030f090b0a0b0907020619090609020a081605040504030e062226060c04060c030e0604060806031009200f04 78
    0xc0260796a03030701c1d44603010b4180000c046001011652601c140182d003070b208160080e41c2141e40780c0808400070040140152035050303d024401c40191200c10b91f050103010150b880e51007140b10801800700b5900306034044002c543c02800d2450f0b003d0f0b00481c150003504c501e450046081da00c513845400150a440b0000f038461480f000c1030000000030380e0701095006c1c03020b407084c01c0590749021003070303031120350071075540102110300c21003108040085d50141846034881c48002a501c01c003600880c291f140980c00030825580f11102c0c00340b42d405141c810034020300c4121001e11440c602a50300612140066190318000c18021481441c0a174071a50b4500d4003600c40501c80000d655540e080046159896080202c650880342201c2103500c13012030720300d1140403818003182c43c248c50480110303070f0600e40c0c40040c4c1c10007055401c0007400c0e544610042005121503a1152414108401098280100e40050b0994070745440c00c003d002800c50004180c843c40d510301c440a024850401107446001082c41041c0c0c8146 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 13492965 1250 13491715 13491721
    0xb030714030a0c02150108120d061206050405070806130303050406020c01050703020910030207020a0302150c01050c040609080a02010906050a0201020d0608010203040501110708040506070201030207081602010806030a0803220b 99
    0x2c180c2e00040800f840b5600310742c6002c100380031140300c009083c055440207401c80b01c105841e15010100800c46954012000550b080d40c820303041c021448240001c958580d00d40e424001032100c1004070030090401d20000d40b4040c03d01000d005030750385a20100400740368442001600f400b4903641500e0310429000c00a12081c40e000a0041c000e51090403480d02c100c10344802980118031034030079582c00b40c3e07005d03208001c06401e5808000c0c6803a840d201e00003c41c40200a101c01c120020302400d0301801140981d180c899007803040241120200e80c0141809610084800000d80e030300840d42411180e0508149a885190341c2c4201d0291151101e034600607800c01c807000640400550095102d54000c000800038035405210000303441c440d040740585400c50600043c4020700d044802041c07440e00c14140103250000315628810380d81c100000040c1c803010071400d401c0555801150311640400102c001e440380c0340f02542c542900d400040d000100d020904010b02c03000ca0f80060401200c113400c914032140d285 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 13494215 1250 13492965 13492981
    0x40317130605070504050a05060d0902061305030d03020315130e0d1206140607060b0402040f0311120105220f050102040b0c010b01030b0904020907030912050414030a0506010b03071403 81
    0x4080d400e0304854103468100081c40f03040c811819601907400041050340040d103004200611900080920305940b955100030100503030740c141c0103102121001c210260f40034030702400c050403c030b0041510810305004008214502c2480d5030810643e5204036036000480c103107045054010661880140d0b8284200c40a02440d2230b007202020403203c13006a002c0c0080d0361600d6070203840034404e59803660405014401e031400a400307508111000ca0b0b0140006082c20703502c02c6e240140400660080d42c04000441c80c069003800d02c404003c49140c0013200900113814210b116051a960030440c2e00505002c0d10f40c56020402109000445590008000c0d0340f600d443d40c000c0026039100c0016000c1d03d40c03a100400280b540030740901440840c00611401041c1c0c0c13281c0030f05c0000ca0006107a00e04159a50305920700103120846060305483d020740e6915182c500b0aa048840750130001c11181c0300c0c0e840801814002100014414159098040c00d551617031200035080d50204100d00300342e003281a000c010441c2d00 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 13495465 1250 13494215 13494241
    0xf19061d0603070305030301060503150a03080c01180213091106030c030108190201050304060b0105130609150306080703080702120307110f0402030415050702030d0609060504051b04050108040317 86
    0x448040003005203845038010996540864480100260010300040140c80e00540c050b40e449200c9102098072001a103000800f4151250400c0307075500e0f8042071409a40e842407044040e0b00308400203010481d0b2454000400202d106003000b03000d80c1c0c03104c8281b8200000c0e80201d40310400c0c06411340d0340301c4c200b0841000c034603003090081040c01e1040d4051902000d60154454070540d806840c0c403407540d10703aa22800e02600300b90861905010040144409122001200b80e00400070703541e81c00c000c07a050241c021030002203a8003650030103050410a008494000c00c00d10112a0f00501641c2d0ba035200b48040742e005c0242010301d111600010414000b0300540f0202509000302c103c9081c10181069820401280802d45014140ba41c0311001500c4400c82a40599081801c41c011641401c041c07800e418251600c03a08860102920340c00100011b0619010741d07600310354041c9000c03000c10490349210095004500c5498100080c0701d0208040c50b00950030884200c15018480e1050303c4c5c0303900c1400d00 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 13496715 1250 13495465 13495499
    0xe031b032a06042d06021206150f03100b03090d0f030b0102100203040302070302090405010902030c010309050d030e07081b040f09200103020904060b1803070f03020607050f06011710060b030f1906 86
    0x3580325400000b0703060b2400610702750603e02000703466414041e00e0b030084d0341203030802130410407445c11558000c80d0000e041030203148a098464000d01b22040c0340d1000401040000301c0900031f041c00c00500042c26a00801c0340c000ea00f07081200144c5036903550034100d00d09081544017a4001448100780010300c0010b40150319000e00945c03c0340c0035140c00f43d004604503144c507040075220b50407003402c515919200e03400241200025400f00c030500e0341c44006207810054445080c040e00e0003c42003101c03003401c090281310880ca040c814208105805600c4502c0c400310501024554400003002d4004603a0085d81941e100100107041041204c1c8c84400e4505260b03c280496502120b2801070810180b40004410064800014206480500d16824060241c000f070104131102e0140080d0301c0361b0380a007044402e00804105604180701854000e28900300030380608900f107498106001401428404c1c4103ca0704881d9000c10074145030b684425030401c1000402e403040b829030405c02d00080305843d144001c08 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 13497965 1250 13496715 13496737
    0x1030905030412081e030106090b07060f02030a0b0a0b04060903080d060306060303050903010b0a0311040914010e070608010906080607120b0405101404020903100e031b032a06042d0602 81
    0x40645c980382e12114240000d101f10000146861014041d0110702c601800c1414400c41c40414421900c01a036006c1c1d0b0011242000640d0741c5a140c603102c0e2800c0d5504100034600240e20030f10300b90401030020004195400007415031440000c2a44c2411200e9214000546d04401c040091944078a00200f550303220280d054400d600b46040458030f0b00c0e10896103c104e0340d10031035165811a4103410b100141101744000c0c1d6149202102e0310030250000c1c081c421000030040b020300406803d00501521641060b00700100c0989091001c0c446a0b400007151600600c1504142c03100c6090340c441c1030080c0015004072074105062030103114101744810b41410691300e410b1041c2184e6503848090104034028004ca4035859400100b00398014031495000001004540042d2490090000c900342c888000540c200b10f003a600000344007006074030b461242c035107000080205207030540002e540b095550a0190000d082002641c3d549910680081020644250841030106403069142441c1000703421215400d0 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 13499215 1250 13497965 13497997
    0xa03050a0b0f0909030405040e070501110a1109060a050d030305010806090a0506011a0f070b01140105041d0c0408071403150606030a050402040b09040b0a0b10020c0103090503041208 80
    0x2204540d860086640307125028049075a038400c1c640030440d0380c12002d0a00308142c0803c000228003074549006070800443e141c0020884a460700c0001460700c1c450740210300650300311942000001e00c110b80c0a206031003048541181d00d4a69200142d0144c049900140d804450a500c01e001c1640640120313040303602c0c0606aa40a5585540c629250141010014043c0d04a600140704141030001c4004201c0070341c2030b04034242500401085695801440166002129200100592029a81c3c000d0f4668020701c0c2c440e060516002e04100306051007242c18103c03511501c00100341d0304020301682c0040203140200c96141d40c5c0c4000c800e41d458280c0751858080e010340d8078101c034006841250f407030103000e011b07103614030b95512501800000c1c07001401c00ca0b445500c40205205554074030b2482401140101e03012103171030411031400000c8138901d0b5a180d0081039450540720314981c000c6400b040e00c0d07900b8200868103895601e0720034211302c201c0d0000d0000c6403002204005014200f0041c05103030140b28841d03 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 13500465 1250 13499215 13499221
    0x6010c060b131d010608060c04170a05120d050105180112050f01050115080105060f041e03020d0605010e0603010e0303070c0602040807030305090a06020622060b0301050f061503010e160c0b01030303020a0305 91
    0x200c0d0321003074221680011500200401c03c20b4064ac0c0c000814201c1054003540c0c9082d2180d95480c3c04c2403120400301e035034440c011602240d80001d620850b4014642101c0001401180306d0f011003640c0380501c1900b20704136803600050140308090109021030441d880080080e0360311404041a030305c010031280c0d400504d9030380002c0750300c1c1072174000c40380225108552941807074079011104440041923081015034985a5500100503100c0b080c20518080c4a03140105481d03043c0501c2ea690000028100c500c82c0c1e040c8103e8000e0050080308503a00540140b9260816100324140100039100f0369101036598800d550001060503401800780540710400c48410143c00e0390380e00b013243c0d200c4095454000610031060310f55a40031790034080c9840c440c0f05840101c0d42541d401c000a08443c82252072904200c1d122081140c80d15008611000074654030102034151750400315003400d020720003403080500b0301110014200030ba0051003e0180290700c0081c0c4070040d81c4070324009005e07401144803100428200004 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 13501715 1250 13500465 13500479
    0xd0b210705010c080304060c1103040608070807030b090c0a030608030f030604050c03150f0d1a060a050402070503030a0e03070b01030503070201090504060501020a031d04060815060906010c060b131d0106 89
    0x4540c0f01690402802c605540712074a4420051400e10b4907041031066030b0005140003031090001d0300040031140c890815901e0603000c090175201004082404042c030b8900c4413055982d807050f0240c1c100d0700c4001d80c9500d43c00c803841c00b80d0081c042d54103c00c005103c040740b061081e901940040d072150400b51410b00a03030b01c9807520030000340016903e4804040000e03500451509005e080d03000042c400901c450715008058175400c058000700c07112510204c0480040180d02e042541e6040d00810b8190340451810440392030f1180c50f400f016100e00c40183c1c66003809800300a04005032180f0b5908402000100c1d40c0d280341466903a405884100c2c0460303003988000540745403d1080303400b26141078010785103018446d0340c11100c0317680240e400603c14046903150941500c42e403183d803000d019642c000700070010400b01945c80026008141c11f03c1040c001040241c941d034040403c41e40c40e0745c0007802207101c04a500005685051408440001d2494401b40c11800c420f2908040003070400000200440b0b900c0f0380d8 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 13502965 1250 13501715 13501727
    0x6090e07120506040308070e0406060206100821070f080a02061902040303090905060a15020a02030f01051b0705071806090c0c08092709030408070e011203050d0b21070501 75
    0x70041c029400c1080083c0100340500c0461ba8000a540350003c400a001c0f0000707070885030941c124800682c00f80d010030070060042a240405004600c2c001c0540340c40703041342400340e600c454018282d0410003065150030080c0d90109500e800358030103030f00c0383c40e00c0b44180700a40e0350703400310303039200e08080d10030380b8040f645403a407007180c00743c0e901039540303211203400c18203004043d04000c0c1483d600603018100001d01174107003090b114038103001580038244410f40d40c0100b40c130708914001803203080c3c2d1401c030901c600d0429074100600d10f001c480500b0360301c0d10f0141c10300c00d05090755984413804888900909516220303442d440302090700c060385010041803180100c02c88680d00c640c42c004107001c0c1c5c00c224441c0c040c9001643d103510202c40d2040d001640748c86105240715040159494040e13680301190070300c000708080c4003400141c00c190018488661503ca504861034400100150910500069030601c0c0e56807600400485003014207031803000c40d2248400712002c1d0403010303c40d80b24040ca40000c9119071080d0 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 13504215 1250 13502965 13502999
    0xf0c091410050702011808011a031504030e030f030a05030402100206040506040201030203090a021201020706060509070203070b0403030e03030907060807030c12050702010e1006050405060a08030a080901060906090e07 95
    0x503140c50201000031505035283d82c0300c008283c2c1400800010f07050081c98004081024081003c00407a40c41900d032038204180c2003001009100703401c101840700c0541d90001031a64016003511344110b007070002e90b020a040210260075128a40000203981c1c1011b41c2180003180240d03c261038412101d11464012a214002990700070055007210002c0b602540c401e402a503003051400042e07542114003a8001445003126801c0805140d402158220611078903208a070300070b01e8140c400f40d1080c42d02500003900c174464001e00a208091001c08a8180b41c800d60140001140700801c417a6242080c01c0b40c3ca5030b80d103c0d40b05060008074800300007a4441e1280c0a110540c0000c0e456031060b0404040c601c1000c0c0c0b100502d208110341d07031400c0d031101808080001410501500c0400522076050100b80025644010038050013224464020402548004101d440c210341d030b89002c10341a202e0070b0f58240941a0355000160b00341c28810040340e400c0d4030764003882e0034000c07480072602125943c003c01803072305c0001 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 13505465 1250 13504215 13504219
    0x607080106031a090405010f02070302100b04050702120a03020409090305130b090d111c14011401140d1103070605130909170d0b0405010b070302010515030606220f0c0914 75
    0x81007501e8014241842071a800510406c000305203c05411110012600145c009070010f074464086085020107510408681d040103503010310051801001c0030f940c07410711400c8102d003110000741d0076902c0c61095050341c028082c0000144800025414001c101c0d80103a1071b019206410b180c80000d45407064800c0700c0071040064030300d00403899103031110554244412a1581c200c0b000e1058a80100741480045061521038584915129082c41a590841e03032030468039036181c0c00400052200f001e4089030b0540c1c656040b20107070980744840c43c140c900203801c04080e0b6018866104042503c5801a01a0042040a010303211243d80d03610540015070700b03011005011101400350b002c803010019001016407600e02c80011500030300100c0403d0403504243d001c1d0002c4103012a01800305a82802501d422503c20702000c0c90030044540000c1d100c030006401355124030800e10051104d0300910507029000e0450100030032021014200100c00380003892440e40000e84c515030003081d103807102e40e0405400940 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 13506715 1250 13505465 13505501
    0xc0807020d0507080c010203070207080d08060102070e150d0b06041406060304081e0406050d050606070b06060a0905040504051e06071416020d05010606020c0117040b1806040302060708010603 84
    0x1c502030311603600c6510207440c840005c200040b001e0000340021030080791035031b0003800e0091a140016081c1401d452210302080f5624041c80116a400945c03e0151030796544814810b0302c804000b4024020100e403203d8000100c51494400e102120440c2d0b440384e84141c1d018081c46030107510541c444241150820340c855410700200c1d001c0344e0308c4409000003802c0c04103412150140101c05134010b4020b81d0140c1c0000f0000030f045034503140d447c040e0b246c020701c060702c40340c0c10091965520325890740e0042c4101e0182101040c541d03546840740180300c4c02828082c104005070300f45801d040361249400c1240107a4800708050385204100000744291249140c0d030382c2c108040980080003c00c1d80d100e0b0b1040003042104940040c0542e40d8500403d2101c0d02c690000141c0034a014070103400c0014100d41c0fa41800840701881c0c907017514095490741d206e42c0c4000003001541e5917050510411004030790049885c40b03440c041108050b000a8902c0c054091074451810300e03039035143d0032000e85500341c818440d1421 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 13507965 1250 13506715 13506733
    0x702060d020d020c07030803100e010b0901030f0225060b0a0302010512070309080d020703080603030301050307030f1b0b070501051f0918080a0905120c0d0b040602070b04060f0c080702 81
    0x14003a800b0b00180e4040410251501034204082403038803101d03810541c1c12410020510000705003400c11280100703440da081c0506c40d85804c00d454001d004240000741495222208881d400940c0c1e812200720300d002c20740304800103501045036000381810f420b048904610340308503900350b850916524800c40c1d5050791032030325000d424041d09a03502d0000d00002e00749606c802d41c0d24005110400a0003042c0304d0000016220086400c0c0140100070141045003e600100300500181c0c4000c2103010649802c0b2503441c259403210716008101c1d8009001070b004100f0542408104902400e00404080e80124002c0c40182c895071420203491070500c01d608450241d248007000380940680043c0c01111404c540501004902d45810308958011000c0c0e0000030154441404149024400c00084420200c02062500728040c042150012400d02c0600485400b2001404112051301203400550f44064014450704161821901a204a02c1c0070041a41422180c06d1103910940e24280304022741c0e8001d142c075074 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 13509215 1250 13507965 13507987
    0x80a02060d02041a09090708010e160504120305130f0e010306090204140f060a1703070320030a050a031805060c03070e030a230a0302070e0c09040c120b0402070206 72
    0x240c07000019081040d0240000901c4c1c0e02003070781c1840d40c03801100645030340e907424404010b00721100030300c0c1101380310f83c58006100b01e002000f03104c0c0d0301c9a5030350703210704031101c005500384c2e654011944000002016070a0440030140e000001d420801c3c1000c1c120005d094545000702c00581060103080b00031184040108003049258002510301400030384009000240413002d001c0100040307802d1415060080b0038020a4185210318500800300f0710704020445030101d04050300c901c1138040184c03c0103403d40c0c40c552108030841c60b000c3e60427200380440e9501c6091400c00f03040d40d0480150000030900e0100c5c1402c00040142d842c0041540c01400342507603940c0e0401c0b20b11580c02c090200010000c3c503424440203030300c01300000070340240500310321920300202559181c0d030343e1808015080d06811080403880000d80014101007690b10350303a402001030b501d0181d268440d0180820003036119003451440000a40c1041e40c801a1a0320424284444050303581404140c3c482d4400080d04842d04001482e0f0710 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 13510465 1250 13509215 13509217
    0xf08030f0702061c050a1a010201110d02090301060b0d06080c0a0510120f06030501020c0c030c0904030c02030a172206020a020405060607120f08070903030c0f0611040801020a0207080106080a0206 86
    0x2084501c4108080c4114250303104030340d02110103100840d903844101511f0080c025103503048042c00d200074048000074a2160301c0c40d000c1e01e4045480e007900450b5242017580c0a4000fa00500718219a040e01c910f2807100000c0600014070402c1c0450140903102e542c5820540e500c50180c03a4090311218000c01c41003c201c072100c102c06400441c1c255215850702210916005080085005000241e2540c00342000da60500481030071480c80f0381c4c08821080030700d03125035442c65401a01400c0101c55614107002003410160710843c000d02d190400e0040b0110309400c140a03101903985120214010081c4045a139401c100300c0c0110005a80a0446000149001c0e0845070744500081c1c03100781020082c0c0c1c0c40c1105e001c54082c3c0d44000c913506003101c8c840b45034810a1a5484010f518002403280d141d9200a091140707155006028102d1801e00c0310140003554000902603550b05000c9580c60760f07601c0045000703400c84255840140030726a80005d0708034050003110f0580d06800c0103001d5018540e42000a5 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 13511715 1250 13510465 13510477
    0xd020a150506010f08040c0902040b07030806060909040209130b04060501090e0703050717160e010812031501200f01051501030908121e0a0605010905100906050c071e0f08030f070206 80
    0x1c4400b03200003288c0a016170020380001c2800406541c0c8a07151403401402c0900010241c81c0114021302041d85c160b590391b21282d80081c0c0540706503c03a030711400541d52020740d848030080d148076080030070311040007060713800141294a00a810481c90582e40703815034880409210240c603660056034240020031a07600c041002d00b24007402c0347c1640726a00410035400790b865101d46c1141c2c02040040205500078011003c0301c03103100700068a18680012840080440f004a1504202103140b02880c0c10f682003035914440c0a10300c0c00c4a40121031914502e001e00000c903102000612000c5004200b540240503210941e584955003500708007032041035844005004054262075414111a2208200720b00d4005001d03200551011441d41d04100001d452210f0551145000301200360b010340d10907030f003c3c580c0d1041d02c0031868010703514040c02e05428640703815500034448a503d52401051044418016401102c2c0b590890b54007659071500c4454490281207422288460100140401882c141e030051503 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 13512965 1250 13511715 13511723
    0x503060d0212010203010305210406050901050d0e010b120c0102060109051003080d050105041a0d02010818150105031006030209010b070609140604030306080c010504030204020904020c0d020a150506010f0804 91
    0x840c0035460380000e10008020718510030340b84d5001006000340030045c0104200b00c0302d21000715095217074606088900f071080b8854003040260216014910368480d43c11200c3c2510003030303070900c099590a10864020100700e500c00e48119243e4010054085020424100300d000580207840d25070700e008010005090000e0820300e02e2000903101000080800c00034107440e0101c81c000082e5981004244002c0b40c441a020f03040d002c0701049800600d50f500d141558034070f80d0a00c0c001825886190f4007200c50000302400c1e03819406485001002080c54802180c1220400ca080741e0b01100c5801504c404c41c0c030107020281d000150b82006000c03ca42000040c6180c510940c000980310825032a0f0810390100c8440c000001e4010030b06100c00d040e818010344d4013904036080605481c010500000e000c1d2f1050307102c028040c580120b0700d4a80355940d41d055454030301d4090140e07000041190340003500e44c00d950300d0449481c040412040400710305841201d205240c103841e2040c40025642040e1001680104112 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 13514215 1250 13512965 13512979
    0xa0b030c1207020601030b01050105160312110d0b0102120c0706110c090a0923060a0c030905060f07090f050a030204050408070c030308010f06050c2d01090309090516080403050306 79
    0x20044032015070506206025503030141c460b40d411171404490036101a400141004020301038510003a00c04808041955030608180c03600100c0003d008025102d491070792000c2031000715400c070002c0311030340101c0d2f1000700903420b42c0c881c40d1103600000341c0c41c0941c0e10801256442a01c00744102805800081c403101c00250488203164903e078001081c800c0100ca00c0c030340480c0c907404820100010aa101802c85440140c2c0c1c1038410511400180d6890b001843d0603181502c41000000d802e001c2ea004400f280c0c1c101c1c2c1599200d20385003484010758981960481c000408521000640c00d0701d215120041c0e40004003c1d00c01240307960204001f510014000f03982401e0b04121050000d108000340c0c00045220f41c4805940398904804a0380045a5078403210a020040190194500c0041003500406660006031990340c0e0704400343c0d42c09030071080c1074290079603c1d020100c000e150f0400000f0007202e002d50404d00c07017559031300040303a400301a6520080c08100400b000c1380c00603016402441e40410b01030040c03 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 13515465 1250 13514215 13514227
    0x50304030b041b0b040302010f1706011b050a0c060807050c060f07050913090201031a010212070512030c0c070504090b04020d02031009030e0a050103060b0d020c0102040909031d030c0a0b030c 84
    0x1ca0554407460340700b01c413196000a0104215604140c07090845e4182d4100315102500302d0035850130020700100040d04002d4202c103c0040c15441130386d1103905540010485094140c285030042001c1c06078003440c1c000c6400700000074030843c459030031035113200084005007016440d40f50302c20800c900042c248005121091104000c9600d0b903000724211228009030102d000c5102e400050101c4031068924072404900b580c00900f1a6000204403004041d0310450a5480e05181001030400b0360395000750200140c00014003502801440c05000e801c0105c009545003580c0d1030b0100801c843c0e600c00000c11121080c0c0003e0050314150120310b040c00d0001d8150f0304c400d0f90340c2c801c500803100e100004a010517940c0050900d03c1c02d207490310002a04007070030f04100d441d00b0440036640a01401c040000b4090300003e4950000c1e0382074050b18028415444140400a40c62502910301800c401c0e14400509009000036130515000032030311041080649103828260a000702144943c0c0010028100c402c070070440 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 13516715 1250 13515465 13515503
    0x5070f03120e0616080304020411030603030906070204140f070908030406120209030109080c070e1b03160c0f11031b06030105010c06090c030303060513050f07050705010b120d020705040207050304030b04 89
    0x429071245c442c034252680e92500d80b0400003254448140d180c0e641405000b0070000703440c00812103004030b5048400d59202e5246100040c003030300121203c010444120003d201600000760840343c05640280c903030b407000c1c80c2c541c23903555920301840c4110070001c0c0c0000d03220f5210080550042c80010740140021070010107607281c090302607000e084c41c40c94943c401da10070401901281c02e03060f003000da1a5100020903c0561411945000140c65502e500c480c4c1800700c041580281c0b0882030a035800304996030031005a0404100e090f0407105090300034040c01000c200421040c0780c54584074503004100790b0840e420b00300116006071003540100c50301c942e200c0380714011a040398060070041d4801d66021483c40e007803000340044610700c0f00d9010401800c10080c08002c3c9000e01840b45d0100003403920648426031400d002d07014107007021800c1e41040b203001080e00207013000f2502d0341c203007041390702140c44940d96002807004900c41e1040291245e0801e120134000100d0031540d10390098000e0918105440d12901c0d = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 13517965 1250 13516715 13516747
    0xb030a0203070303050405030705010509030703030807110d08010311040207030f0e03070803120702010b060406020a02090604021908060906010e090412030b030d05090307120305031803040b07030503010305070f03120e06 96
    0x41900459000321b010001c0d1315081140f200502800e01e0420308208905010a94a68460000034280000c01000031885403043c0f1038004804100c40c103c401c1b81f00a00f0002d41406000c0c041620607240da20a8040203040c40d0080f03409980d415a1007052444032480210b4941001c800c00341c0d13242c0031708207000172090320420113800e81e0080d1551054040c10b00100290071100300d200c40500902d000c0c0003c029503500032a42207462034050350614525601d0780700280080c4240321140c014407240c50301c10164117070f0124009100b01d03800d07540900a41c5450b001514407070b01202241d0341c040303c40d07000a0001042c15800d00b0324040582000701c1d151030301c1c100280c24407010500420002d200414045468901002607400600d855850050b488525807401400c0740300c002d29403224140a001c5587c000c07501042160000d01126041c0f903200c0c6c40e50314008015500a00c0152154412800b000c200c44bd00324211000300c0c4c0e8010020300c1640d400070710a03254070f00d0382e010256104000340800002030700201 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 13519215 1250 13517965 13517969
    0xb1c05160306150509010b04090c171302012d050d0b09010308030a0c0f0c020f0d0803100e01090b0d0311070806070804050f01111c0207020d05010e07080303090a060b030a020307 78
    0x1840c0419040e0b21a00c0f004455401688590b100341d0341d560040103c1d041000454054484d1400003007145001c402043c0c403a8a02c1c2c80008841d00c00c031000700030164008403145200c40e8402da0b22200c0b14044110329050740c0c02cac10b1080804003003080030007d5481d80500700921500b1120200803030640840c90019075600e070245e0041d103d4000000c10004176240b10303c1440b901d4041401d260b00c086001c802c0c010164100d001c0001e000da0f0f81004541061f64581d2201110141e0060107a81d491403d401d220840f1000c80c0310b40ea010320000c0f00017040e41c40c00d90088100891002d0109040d0411640f0120b6203c404d4918585003402600e0000c1136884080c40020b00c01e06c0d40d41c540064908061414608e0240700402c114202c1c0d02d0015112011540541150505010301020030460054548004020700c00c40d88000d5002d002100301c7d0301042019048002808103520944800d641d480058907224841151620007079007100703680000251483c3c4c810102508040c04070740750014107a02107864407200d9 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 13520465 1250 13519215 13519223
    0x9180b0607030c020907030c020a0f0f0c0f050102010e030702030309011809050106020312090c01090302060a02100207060c09081609090c0503010509010605030106061103040311060903030f0307030f0b1c051603 92
    0x826200f029420300110984c0c1250041c0350412000450b424000c1d01c410f80da00008004821203400e03001800451554401d40c00c0d0803c88100c0c1c071564840401004004510920307016508041d0392450144000c0142c0741b109030040c0181d441e241c1c044004481d40312803034500341401502d0315804035500010f446081d02070019500110303500c1c680c0d411180c0103203c0041c2941469449801c034202240d0b4402c080388126541a40c4694840c0030700c2e2016424041e4030b9002c15030081c40814407200380895504034500004554a44141c00d40d01da0030300e1511420354290134100c11400000c10002e44909521801c0014020b10301d43c14080d442c0e00001c0c0c251441504c0d0a03103543c1d110b031000d104510b420b120700c0005103040d05082020500031102982c5034001c610000d850303422001c04502c455215201100e00314000241034a599152229400829400584260000078a0715010300c6401030140700d00d0074154402840c01c1c0c1c0d0881c0005104984041074801102c45000d0040c2103066500c00c00e003441c0c051445 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 13521715 1250 13520465 13520477
    0x114090307030311040b0a0c060f09050309040f060608010b0c03040f031406091c18050607030507050601080601030c090c0210020309030405030606060702010e1e15090319020109180b060703 83
    0x2030500405030b80c0040b50507404e4501c01c0104018615280049841c01c0c011800c000786009a40c1c18248010202c4031040340d003581c00c00781240104040031004004408040390100512a400401541150450700503c40030807105d0005001e0b5a201c2e10141c400c1d1651001200d1403d6150305640700051515401200c000720700b18420014840c083c0700955100c2c8410380103140482110950804e212001c030103144c1403014140c02080d0203594042804041d150190590369985040e1074000c0c4140c0c04001c007076405010b518004500c1c103002140d90f50485e03800420140c002800d0041c61340041c4103800142e402e5215085c10019444118000f8620402c018000b031600c0303130310704400c0c0340c1080c10040965118240811144005030b811080c0c0d0b41c40184140d6000c008a8000050035181100d000d034460b500030104030780d90090484082c02072a601c07030180c05071046080000a0416250315204000b408215045028820202810340303c1c61f090502c80c0000c01c1c11402c00d400700d0a990700c040d0040d000145 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 13522965 1250 13521715 13521727
    0x8040b04060215060f010c110909060619080c09071b03020705190302060d1e09050715020f0d030209040b060f071b030510020711090a0614041a090901140903 69
    0xc2c0501030001c040c9102c2599800e140303048800039490007040814141403000c1d019000060200e0b90500c000342030701c05000b8890504100341341c950b80b010100d414074030a01610012040e279410700032002e011100c0e000c00034402c412210040180441008012008110b585c0480403914007518400c03d030700354041c0d009440028105004c0c047c1e01000c02c102803c2080d142038007040140c0307401007225000e035054900050404000013808a1a840e0644007130113030740c01c0c14090750034000d000c40c0d6042160210500507a07507041c034460580c2c43c0c0300c001401150341c0c0c0200d680c0007201030190b002010170f04d50080c0001002106a0005401504549504182d06001180c0f071010031045003003a412004601c5c1c2090007043c81c5550740c0355038281d000080d110302c0c0d4020582e00d08020038403a1940c5003a10081440519181c840008001450385118040000e032041005c038100c1c1c03d041c0b1504100c2002e480390045054030243c04d01c40040805803080d081596140b02c4403280840d0314140e40d01070b169400c06555203203 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 13524215 1250 13522965 13522967
    0x40602160f0303050901020a0918020913020d06050a1203080402010e0315150d0507060c0503070204050408070506010b090d110613080d09050f0907030507090302060406020703051603020f0d0c0308040b0406 90
    0x51001704141c03113aa1040142c51001508079070880121441d061b000d0104602207150a40a401348000710764110381c9510b200f420040b4160080c0820884c00a400c214165555040010700b115511402c405140d5618007507000c03a1140f20500e42c00360060400a8541084401091034090054511904606c0140611132940104042007443c80d8003120141c503105010b807039050701d8141d0b51103035006102591401d00c4c1040f2040c41230702c1c03002c4c6c0c009100304220714150818041981c0f280604035064050580041640030500c0300b0340b01c0004020300f2001c00702e01c86588205019911001450344110140319903c0801d80240c014800303082104090150030f004102c1c0a450102c4680002c1e1140519020018440e1541c50031150b101101d4580422140c40709001561303070901680020350030810005021a840da00015503104491058080742d030201d001c201d1142908501c0c0c04000d60200c2041d4400c10349190907042201e400380a070918158043c3c0d00d5840c100b0a9000c2d40c0000c0139503601140800a503 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 13525465 1250 13524215 13524221
    0x30305091501050909010e030a0504080105090610050f03030702092a09010f030c051303050105220209010504090515040303092f0108100e10030605100602060a0203040602160f0303 79
    0x540108000d109040440724031851031041400350364011805080010500e0009410805844090400b0b480d80c620314080000c145500c02e0141c841d0b60341c205004100d0786079000079158422882c41200781d5505080204200140448072401a4103110034082c09002d40d940010700d40c000d440e0540c91050071000c1102040c1310804d00618210400300034800b01443d41d800c0300460786a80785528000131003140001003601c890007500e0030403041c2644c800000c8204081540311074021103480c00040da0b02c0303160a060040550350010000c1d040815030004000c01c2c1840d80003c1c140c80c0c8240251544040701e84000204601d085800b9800a0f0701c512400c2d043c00441024031040e604100d0400320400030f0248064006829503000e00d040040907800074800071000c800400c0500340d080c10b1880300381802d0b8000c251146141c08203031590f0b860700b03000c519858210700001c0112800c1d42c0240500303507107049a1030001d4000600507a491a020000407032000018036080e10000e2194510405101640c1001000c0b = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 13526715 1250 13525465 13525471
    0x2060d0b0a06080708040213060308031e09070302010c0209071403040b06010f030207050606100504050d062405090c030a0b040903020604030e010302091c0213020c03030106120605131503050712030305 88
    0x2441070380f600340181030b0f51004001e94003e405450800c81c3d181196030900c01864194030203032500401105001d500039004040c111198107010041083c1d031100035032a80c0b606218400240441e01c0320100e4030050411b48aa1a440852814848880f41c2c110741c2c000401d60088404a8010842904004c65503030840d52034441c0f4061850f0441c01c188240e03960a9a4002c058031880c0704012902c20042500d1144003140c000c0d10010f000200010590f14040300274010321608040c0410702c9556042000c0b000035080021500018641c0390551200d90000015034000b41820082c69110f16148800c3e84490069801c1d061003580206081d02d03140c140100164105034a5504040c010031060040303a40e501c0c202141c28200c0c4c101980b015009d880020400480360a4884200c0c1c0041129008544080050350480d030183c1c440c001c02130a80e900c800c084a80782e0103a00d520402d0314444400d5840307154002034089254100484646440703886292a0019940c80503260758429103006040503854090250 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 13527965 1250 13526715 13526717
    0x30706060b04060c0807021201020f0702090114010801030b150301090c030510140106030c02030c0106090902090705030705030712021e031009020702060703080606041508160806030a02040b0d02060d0b0a06 90
    0x304090610000609140c80d1840280010001085003401e5689423202040d0000c0c1d4030008560703490094003100c1c000d41007030409901c5048410300000e03c4200032290100503c1050355018110380c00c607600c02045900292014201044280700018942c40901c84c4001607030080c4100004585185070482c9440c820f49085401a81429460001c000980079400d05542903800c1c0412210707400c0a0491844c010351102145541c241500040d0301a4203070701c0840040e0003500c84402c0341c3e071000c40a985e41c0c0f1041e103480001600800001d00321074480c46001800d00c42c40c1c0400343c58800e41c560071300845400b000180b2091040041840301031180014000000c054401056003840215000601c407800313034050240038031080400140b400da4070b0400f1200548407007450280d10040a110007040ca0b20116034500a42c000c10404500d46402040c2c006e01c1275030024024111140c00e68240030142800301c00c1d054100c01841c40d02d200680d00d040181442202911380000c603641110100500100150303c024 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 13529215 1250 13527965 13527967
    0x91e010515030a02030d0e0301090b0a0203040506010806042d02040203100806090f06010b071406040303020a030c030212070f05040b2d0a020303010e04020a090501181a0f1207080a05030706060b 85
    0x3c001070320085207203200d0502c0390030200c52203182d10340070901614a81034010040d41004041210341da0340c039800385009a000b6001c0350210303a00da10040b0f54803007003550003070141401040061490604d90410035280032006034810005003842e40804c040c0d8105858840d10300d041003038180074041c0c0802109a1200c031140040c40c01714100360b0496214034044c054007081b2040000d030f500500510b02c1d42c1d0a52010b1202c221041440e06003070080080d0004a54070000904011068034643e119009503495100c14001c090b10a495215080e80d110214903020420b01c1000d200c002101009040580000221130081c2c0d009150421301800c11102d4680c5006040340c024003485403482e81c000b06403030565148000740000c40d00c1e2400090010a140d600914440c0d0916001040c0406c1c50f89142e20700420298050011500305c80f8801c1d8860002a40560082081e510a21080c541107901510187d0440292a01117442d8040b09050a401c050150360303541c00003440340b04011283c803072603006000c14001c036 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 13530465 1250 13529215 13529233
    0x1203110c0a0506120a0209030304060207030605060f1c060b03060901060608010b0414010f09030f03050703031d101d0a080403031205010501020c040c050c0717010e0106050d0b091e01051503 83
    0x400340e004040c0b04c0f103000780d203403000a101d05505504681c02801c0050444c1d46a564420000355185503074041180c0c428200f9002c25840e0500c000c0c0d110000500410700e213070580700b07642c412120101e040c009692054803041205e802c0c0d2828410035004a54910020500c2410980b000e007240c08181d104194402040004100b1035440da954600c0d10f55091900d110792078130b0104201c5103c05907400c0523015242c5404074608240d0490000d0031094883c0c0c505001d000c403207101c0c5080c1034040c40000f03440c0f5041765500ca9049417079588405c0d052000c000707103140940c0c3c2c04420f0a190a95181c0126424240014140b00b4141c01424211280d24003d600384200e6040000003500c0d0240d504206024a0b200d04510310003a014405684102c85014200c0c1c0000b070707482503c016841c1070801d41009551804944502400c81070141c14141d071005400c840d0310361074550303405032443c3e001440103a15024204204d054a0101c90180002508c40c0d8000309142c10711110017041140d4003020b5520a034081819 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 13531715 1250 13530465 13530469
    0xc070602031611030f0d0f0306060c02090402040b04090c090903080907151817010504030e01020a050a08070c0e011805060d0209070c05071703180414010315061203110c0a05 76
    0x210701d0403a036000d082040b034079030800042468405e800d44030421a0140c3c4001d41e403090ba20066202c0e40742266075051020590750740c42554441104503020303402c800084001780142c10035400c07110030764030094000200d2500e41c0e00d89a0b0581040d810000c4c0c85501d40718003109065115045607005840d2002410487d468000c604180b01c42c81106201805006080f250800d900c0c150000010820003403029070341300c481000d0038001d00c012101140800c1e100115200a5440000d81c130b5402e41d0300c0402001300010585401916800a050407a0841d440c0040840c202e209401154024000c0082100310006d42031410fa00361b920082001d802402040a0200540d55603070005401660302d0a049480352224140307a824003040b50000300248040104000d000900000140900f00e83d00070444600a40f41c0c2c00c03c0180c13520103244500c0c06036004014004035101107000819801c0c101400a0519074682c15000c0c4200000d1094000c201100001c000503d000d008640f5800c0382160414000d50500c0c1c0 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 13532965 1250 13531715 13531747
    0x5030303040b130204051501090801020c100f06050a060c0c0b0f03070c0c030210091a030606030103031214010f181103160905090112030207060507020a0e040501020913020c07060203 80
    0x4050302c8044440c0110748492624400d0700ca07030b0f40e0090414041031070030442140101c648020f1032800a81c05d00d0300014003001c1882600c1d40c40000c04094030131000d00e0104000900201c000d028420303946c844000070036135910103400f0010300094542c2c40d480d80203030410018182080d0712403030394040108062501c60034040110381d802241800c2c0060054201c1c10000c2a2229075000250090031341e0040b5031001c0d803c46111801c5800d02c0c0020703812880702028541030382c00241c66184d000351081c801800081e01884100300e4814407044009035038055481401d0b90102c3c00c0c1c3c010141040112014482540b4120321900360500c440d005100703036400d41c03250000d18440244a0f140503500c20400c13181e01c2d0311406202005110091005110756180c2c1000c4030110b6003150120003610800e50006582402007040d1400c142d0001c0c40341b00814900100c0405694004000311983c0d5401c0050070340e20354442c4400300000c0d0000b10010f03160341450030710703a1500d9510f800c40001e55109109280c110b40c1d0400d = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 13534215 1250 13532965 13532971
    0xd0f0e01080a180c2d0806070503040516060305040204060905060108010608130f1416030f02010c0c0e04050a05010501050103020403020d06020f09030d020c0f0a0302130507090503010c08090d03050105030303 91
    0x151002070f00030341d403000c4148207041881e002010003442d50030010f0341072030b540780c01c000000038500c40030400381080710020303c448424032840c119500088001410640540301860788540204281c4011424610807520049010b42090010958400501041d4206480b62130082c00d4107400400c010309008001a03e1f0280511a2000300941c2000041e9006c1d2000744a5400e980d100701003d803030042500d0715003815000d070400e4029078403a4061650204280c0003025003202c1c3c00c62a00000001d00c0d0300112600311031001d041c1c5808035038640000b0f60314059210248554000c0c0054501c101c404d180060035500706074040c4d0704250050000740090381d0703480303070a0410382c0e40a41d00698a40c1000300540c02409a10665a80b40c0100c04040000d150041006041c0c21001c49070f04e80e4450380c0c04100306215403640030181d008141401c10780305010103a0301054105800303040c86505c0030342d13030700000e400d40e840c103611000000d82d03070b005000310500200700d540a540d03032a080c144020760410f808290340780001 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 13535465 1250 13534215 13534231
    0x2070608041a060121090213020322030207170319020610060c0203010e03121806010308030a09061b09090b040203010b070b0408040914010302030609010e03041403100507020d0f0e0108 81
    0x12501051944e802800c54103007030b0403900550603501c4020308094006205441c4244d014030701c20041040314070000d100701e911031207804161828401440ea00600c280380c030000f0407015481100004541000e1341c280102041e08102c1c000c2d079481d4440c6c0301250309802c1030350014080d980301109000551a4951042c0c0c00d540c1c00c6d00c1c2c07072080e801045c00041d004d4440d20000b02c209010010b100c1c509040c140110301d11840030413640b05c5088400700350441d9681d6007440b01610071042440841c40d1120785030010701c5082c0c00b9200c04603540540110f801d21000b2200b40a201261010004021040ca03500540d0b0130090111401c604646c0351510314446445441402410141000c00040400c0a000e00303030340181420202c00c03c03900c10a0f2060032a14072081c0003c0e4802e01c650b00000d02c2c070200502038004142c1d0b40c0d00283d420a440c260600e000d2003c40800f50380c2c103014402500030451143d01c0784c42d2182c80c040d401004c0c0701d0f04096001c2c0030300725219040f1040003e8100c04111598000740441c2d007108607 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 13536715 1250 13535465 13535513
    0x30507061110020408030301060f0c0b070305040f021201020306131103131a01080d0e030a0201170901090b0c030402010327030e060c0109050f0705040b03061504020909090109030207060804 83
    0x460100703541032220002500000070300c0803401284040002003d14142d501541f155880c030451031070b007622062100100108031000f003400082c141840394103c5500103100c0c41d844900318805600040c01032080c0244806260340c04001c0000c00d150000134a0800c41205e6001c22000c2c6100075416910f2000404120055160401a01c1081804194000b42c032500e000e82e613a455840d074005a4485c92003060b01000a13254110513012817070041100310005034140c460350a908001c51802000190007460129035540c1c035100c500c0840c4e481301195204520710064156a0301c2d0910015080340c032030708082c078280e234560424118080202070341c142406815040403101500c848000855504c50440c100d2015400d01e80d1260400c00b000078080c0102103048155525140c03500140022034254071402c503890380c40034011403001519010030903c2500050030262a0400c2c080200d4040d8001360795510365603544041d214185641400214082d04c66450040d80da0304242c0c8a5a03101d0f240341d541c548003c11 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 13537965 1250 13536715 13536737
    0x308040b0708130605030403090603060602030307030b011101020a0504030b010e011206090618030c06050708070905090c0918070305150a0501080603070302041a0f03010902010203220806010e06040f050103050706 93
    0x103041e2010f564072209802091903c500e4020610340041e60102c022902c03449000c03a0b8103000c0e00680060301c020354011800c56482c000128060030380c1407a13050500c2002100c20765000c1c02070009000709216600d1f0345984901d07500d03203032014200c168407001e1226191030062004808410002581d1034000c880450310340741505100f001408400c1182c5500c42c0400d134290300300754208806c3c2c81218001c0404111503078400d0400e4403540000c42c0c00d41e000480b40301092009143c038242d0b140d08510f443c011a410010a5000701d40e940b144800c0c0d03481c1e107603100001c220b01141d243c02243ea001d13203d411b40e0441c030a088408a0840c82c018000c1d94144582a000100d65031000c0081c00002e54000300b0501c203070b0811003000000f0546102003070307010f4032980c03c0c54609030030140244480c3c513a069000714946200752048900b500c0b0f82c806101201c0329010b00003d03001200700300b00d0340a42025240f202e2942005010402180d0120903807200090500740100003049012540a003101e4244c00c00a05501c = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 13539215 1250 13537965 13537973
    0x1020312090f030301090c0305090109020303040501050c0c030d0c05161202060304111801150203070b070f0c080403050102030118090c0b0c010209031c0e121209010c05060a090b100308040b07 84
    0xc000c40400551902c808000043d001c031b8944c220901031245520200041d4580c15445401c0e0b501074100a501980b080001b0005940328400910b00215150141c03905142080d00081c00c024100b01e21030001000c3c1111001030101c103000894550b41510041c0c45400c1c039002d02c403040e0350a406e0010344070714004000142480054003074440300850003080d00102c01605072040020f02000c2c00341d041400d403000c0d90390280c1c43c00001258200c58020400b140c1d207564008045075901c040b0001d6000300070780c2401d09030004448002401c090362040001584a60424a100c600756000039941304019003011641004501c84500300c100755030103c01c849076100307000042c0310702920801042c1350f050710541d1748100000d40d40c64072414041207540e945200d16080801000344006070000b2401c201d03000402c0c44000c5002c0803000f4040d2a8060400015901443d1038540c20804221a8202110f480b0398041d02006040c601c920b5001e20303604a44064241541c6582980340198002c001034420300051010501c = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 13540465 1250 13539215 13539223
    0x2040b0a030f060509010606110c06070f0206040308030f0c040b0d09240203040204050603010506060417150a020c07060504120303050a02070605090a03171e0601110105100f05030105060102031209 86
    0x650303000540b407441c9403098074260004003000c03141c00080f54602400891558400c4e600c0300400b600ca04000c00e0201c6100701005103903848035000315a040c2014401100580b148405000254083c500480d221300d002070603180c48040060520108800800007400031001800c20f0352003c01120a00241541a91522034640704444048880307000c00d8813a0044500c0c03c54000307502c554800d48040c051510380005060a0ba403043d50b000360720000901c02031040c0d001480900c4486000003040700c0580805002c070040350382b025a0100405e54002a0305000040c0403c0305200a00b0545001131070946032400500450510310700040400d030b11580401c0b242d41c3c03240c060312815070700030700301300528140502503da031032400320320460100d40e010300c600b800390310720440d0740340310302c4451450414034503a0346120b00c1840c100070542c506100086008100b869403d00c6054407802c8034035078490143d814110503203043c8506030b0081e40300b60f04040411820b0391340401038401c007041b9810991038a440701030b13002d824 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 13541715 1250 13540465 13540469
    0xd030206070f080124120e01020403050114152407030503040203010b010207030302031b03040f0b040501020601120b01060e0105120a060f0b070c09110408011b08011508010302060d0e0109080d0c11060402040b0a 92
    0x51b050815070491103140d410341c000c008882c03044008000c1600300b0784441d042d1040480e21064980302c280b06415440c1810f0242428400140300f410743e49010029080011340c2144030706030005240842004114142449110606d0409000400c809403442e54025600e05c10392980a03861203c1d1450b09449003410008d49001d400780d82a0104401d494484030865034105204460051250750000036410018481080140d5040455200a0783c00c028054440ea4441c0000f181042010443c8021489040c2c900d14002c07840c401c0041190307840c0400800341c121051f004111100b00400c006400030304000e60907422192003400c081013030b5030203043c0054036018a41c4411225402c2c00080740c49200fa20f451511880e0b16a2103100090b602e41901c0381120000010801c0402c4200c80140054503041d006031014441490022a100340000c9405080d42e4041000301c0c4e005201064403c2000498001c400c551405454001d00b0358215180c04c60781c5290141000c1c3c000c565484109084d51a00c10300140 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 13542965 1250 13541715 13541747
    0x40b090a0c143007050a03020304020d0807060902040605030d051e07020307090f06060f020a110604080a03030504200109180917130f1206050a0b0d030206070f080124 73
    0x5101c0342a0003001c42d6005025820325046042010f4800c00350400d1110180214035550381d65040c00d02c405002d03002503001601c16680202288100800507009000800b10035200d1680030030307046044e2050000f640e003242c1040b031285d0803080c0c41e1031a00c0d6004007a070300b40c10203450f00b0700c500f0100311810b80118440c41e50702075054013600d000070809407502c1d04044500b07017840504005039965914100c5981504202e00401600300040b4400400c03500e1441d0341038450004c00c05032900340c1e540050b0340341c5580c0d04011004643c40d081004144081d40c440441c0f15446004403040c0c4010035400240440b005006070000340c141ea80880c041c1c0c8499600c01040309500030158210710b00044c0f11400150021000341c050000300700310104906c58a0031443d4104c03100380305104940d0304680c3c0c5e09000f40200030a04580556202d149066075135601100e600154080d8015002c18105464003c03c0d002c00d02e110341c402d01980800400c84441c81045000092030198288080e001466400f22600440b00f50600 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 13544215 1250 13542965 13542967
    0x105160609170a0e0303070206030a02030619120203070506190807021005010608060f01020109111212071218180903020309180115030b060a0c140313030b06040b090a0c14 75
    0x1082c0560751400070b29041e0742d0f68490b068042080070130144d4910034500005e420040500115103210506c0d0042c68220500401c3d0140c3c00d036400400316820a0f680d80b04000136810141102c040d82800d03c00e0002400741036410900d89440d0020207c02020b9401440080094440018800398030a106400148c0303c1d1070f01c24086540d41c0d010003007055002f40d5541e841244040c060304015070051103513091035503009503405c0c0e04540e41c5081100c084c1c00c0b090510428002c1c0c4c400385021222000040c50b60912407241b800c060242d290008020b420b100da5528044d0030051000d0042e800f10b01c00c80440e80350740e804003080109042c641281076004445000d50080c9a000001d042e500d10b49030300a060300c2c0c540043c1071144038102e40480a50344070301d44140c2c001e00104040e041c0d042c46403100c0d120150091140129080080e07500324615404407404000d0211103031303028070030088080a03041c0c01050840303041c00643c1401000550f0100c1c00b800c1c0c04196541c035002c02601d01e01814603c0c0103007135070241d01 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 13545465 1250 13544215 13544243
    0x51f050a0c1b0612050405070905090f010e010204060e030a05060c070c05060310090c0306050a0b03060102030403120306031a0103030206190609020708030906010603090f080a170705090108090c0105160609 90
    0x64024102c0601556003c12052811459070819502c5680d20030b80d00078000303211072031070107510307000903c009081c3c00e12078002d40c01c4800f100702d024098908600311130070005a43c0c1d413278028010440000c403040d4030311942000d940340d404180001000c03504212800440c43d55210b207440c1c50110109203034403040c0c1080c000700401801902c3d081d0608115110300806000303251103044128200c81d41d0380034695008001101c00d10001c202031003d564040030600460f880c01e170300d030f44130145001034030740740d210000303031118001c0c410810f021751007200040e51140020107a50659501a4848100070881d44c2a003101c0d840f0b1a00320a1a500030b44024901107801710740d40c001d2070803c0542544201d8812202d1311840c0c00000c0c00754403a1140d07032445504000e140d0454812035079090000c6d0301c0441e0f1b0b0703010804d10a010384260100c4e4880680910460f8507525650201c40002400036540107201c40601e03040784805500780d0741c00208031001808a0154490000800c0ca4603500030280da00000c0c004025881d88 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 13546715 1250 13545465 13545503
    0x20d1409010c030203010b0403031d0306100f0b0f040e09150a0902040b0303030c0901050a020708010606260702100f1136010e01110a02091609051f050a0c 68
    0x65a4000c0040034024002c8058045080d0141d01c02072096400d400410001040800e2041d1a001010003141d04800c1c2507054030000240340c003100f0784d261040200c900c041042a030103081ca4a03001004640081820a18540781070740c154002c92096001c51482103000424200302482010100d8a520391401014185000445d008202040c0100e01a502e001c940300201e180c00800e480c85010001062407400400300300441c0d481d00a004540150700c80d0b410045001c10f801e00a0001030b0403e951881d480414401d40c542c02185114140c00e03100c100c200504c01061f40c04282184022030411022071a03041d000380010080c545002c54814000b804984911f90221200b20a580101c50340c40d035641d0b15043c600d4590014055008441c04516056203018465001e40d51901d0a03420709004e9409020043d0007107001001c0032281e424034000080300200d0456040b505a0010704010b07105101c111500c10310100c8020b80307990040b41440004220079400c6442031070309e083c0d61540020131680310840d541e0 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 13547965 1250 13546715 13546751
    0x7050c010f02030901060602190305090d0609030201020306100302090f090c0c1902040e030a08010e0411040504050c12240a06080712170f03040f03030f0c0903060501061b060b04020d 80
    0x41130001035003450b80c001149440066500f100300c140320204400b091956a054840344d1152201c181c00201040548000c264581b18841055000340c001580c2c03444d041c01040300d030101c0020100d00349403041c81200c5294440c280d400034451750548460a8a460702044010711740a500c900c43c0c81c3d4401c40d070039015050b0300c1246c1400814401c0e5400d1101030407041c0065180e01500d0351402c00902c4050040202180325400c06403c94044c080070a0300138000030100b001d030b91085500f6240c0354811001340b0103a0501280c01200e905002d005030000b4111600640c140b1401400c044240d980c002e00030071283c0000d5440f8000401d000c0040740c0741c00d551400c80040300c41c021103003075035040c50722021071032001288402c41e18900170070019946103a9441e030319501c150380203600c29804c04d40c1d00d141c081c102407200c1c4140003c0c4200b40d16142101403441c0b40090a03a40d050308254104444803c03000458001030703907012003065204502150101418020500034000d2a00211601d800c040c1e5000203115440 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 13549215 1250 13547965 13547971
    0x3030b0f040c0f03050a020712030504020a050901060f03020c07080106030f031403010e06010c0c09050a0204030212010905060402010f2601061d0a06050901050409050c0306130b0a060807050c010f0203 88
    0x9038114030031000d01010002116081d050b15004180d1004141c0d24030b620950001e0343c8820480c2c40181010074a07140d086030b64440c043d450740480d6440c024841540740000c1a03600410081b40c503101d89605120009020140340c01d00c0509054020a8821604109001c0e0501401c00b040080001940e207042c41c07211410320342829800700d00d0303e0743c41800000120040328141c44002840e8040c9854003801140c9509400d030003a0707251448058040b80758401030007114003e008410004da10f0310300711b00422014050601903170707810380c0c90001c0000006138007181c465440b47e02402c0c92406409100415a00c001b40205c1c91182610540c0345c2c101d500035075904260584505544200c7d25980d01c080c000030884082280a0b48a411a032080105510130401010301c40fa0624006090130380c0c450090b801c0da0002e6458450010b000b01c20030126091400b035901880760050014010b020b034642c0070801522103401401c0410040c440021901c6008004940500d40400c000f0041809000c2c1d002c4000e41041d = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 13550465 1250 13549215 13549219
    0x501031202030901022119030b01020d0201061202060705070306020706020a091d04061505030601150f02120409050709081507020105010609050a09020903070812030108011503110405070e060703030b 87
    0x100303441108984004103807041080103030018800d00d80c9640c200d0040301c42000d4440d0300e00354100804402040160705402c6982c1940d1030101d01c51000100190034a40c031840f6840442e0314022040091091105121f1541901900d1850b40c074401401d0013030502c500b0343c00181585000003038940c00c2000c070354000c0803895075544d50050016210480908101d00bc0400c400e1071382c1008000c01d001c2105544502003203051041c100b0071259032600481e00b0300400f640304024444030803268145958000030400c07070220661015000103003010303412100d207000314040c000a40d6074071000584054000c07242036028140740301c205d940281080100411343c05044420f039006500340000020300a02400c084002d46a00400920401c1e080905c5900250072401d04c95515220b072220001e425a01400351844c4295031104651707882d0b040c00c807920300b90307204110900c2c082040d0f202c0400118207a0682d00215178001c58001c034098485400c1200c0308210074003403075805440001c0300c8003090b030580e125000c40002 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 13551715 1250 13550465 13550483
    0x3020a0b12010b070b0619050d1103060f0601050301060e0d0206040b092b081806030403020703060b01050405060904020c010603020603100303020f0105091c0504030c0e07030506040614010c0303020904050a050103 93
    0x200c1c3d034039007210702031010010014042c09001c1b072170500e060440e200c03803903400b8281c4a080a0f60b581c000b5446440450080c1c89903900c200c454001c0d81000e0201690000d9525040c0c1c0243c01d100b00000c142d440148240c1e400c0040550308120702c0e03554580f41c08035003a0014440f82d2501e44904150420b94428900144190310360a03c5520820402002e0070218240c04500300b07000c2c4072900c8400700f0742e020f1a036102d400d0205014900481d41c402000c0d50156000c2c0c0d000704082402c51422608a503a00142e45040c0042440104810741e566411039403441d00c151800350319421220381c0c0d6805000190002580140c011040041600e52203261a048a009508075440f0000d6680c800e800c030b56041d00c8017409608020504005c080c0406101c045e0781000e0315201d4138040c5c0e81d40761150241107581140c003603003029509202050713915005154001000715020001e2a150007501885141070700151814002140602c0080c94040da05407180740b18058001e008a14080715800010320f0240001c96002d04 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 13552965 1250 13551715 13551719
    0xc01020d0c030b030f1002090d0c030501090b090106181d100b030d080c031303120e01090b0702030307020d03050c0d02040e0406050c0705100209130f0c0e01021605040e030403020a0b1201 82
    0x1400060000c2c45480c0315006c0d1200c0d424140c1020040d503c86081203800243c0441c00c0030004501d407415170002c50150000141d000c0161808010743e0b13501502c0c0e0362603681004000d200e0306619900218200c00c201d500000d0400d1030900716407140f05101fa07134039107502500d041c583c88892130b40c0105403880012002d59031440482801550240b1094807100c4140e502400052a200c00c641c3e0712154030b50203810070300c2240030400d007071100707840b185940100b459440e8558881040007440c04140c01c42047d001130340c214542240025a03c80d0648170110805442c8d002142e500364142081700c9108280384401e558560715007540550b041c00c01d0f50116181480d0800050941c90220251200c03150702c44054400c40c038410700c0b140d0194110035074103a40301c40d512000e2100c428403845850703203170042208041003640a40318042c03c808001069507042d9040800f180140d86440820503054038000c490011782a900452254958015500001c1d000550490049034a0b50050b014102c81c0c2400810070740107030303 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 13554215 1250 13552965 13552969
    0xd021801060f1103040506070302030f030a09200f01181502030c0706030b06070308040606090513020102010f02090a060c051204030308010806060411030f150303180102010e07060c0b0406020c01020d0c030b 90
    0x70f200390404880c950001e0209005602e810401020524082d10481c1e0800c08a055030b4415548140c44440c9036035075469821042241c0b0b920303020020702881c496100c01c0501a0045100806189446410800c64402c1d8441702c420007208280075040c1c11381210707181e041c07161011750780b03a110713100c000b40e00d01c81c0c1440007a14034400d000c2d42000620290070b05040ca15155070035129400040c20403950355884140c04211140d00e4840c2c00d10a040c48101c5034200d003100d00019003100c1801d401510424010807102000d0384030034504200311544c40c54041802215400c101e41007020700c150203c21140005400000e00d42c0c09501e0905980304101529100d84034841000111a003804844080e548180000383d200c041d0740c2100b540c84541121031002c04451600000d0070b643c04110140c00308000c9485007890342d6824419001c4607115007005001050408c14050100c0f840c604e0010241d568141c0000e0401101c5e4050b1526002d441009548400311000c40d03001078032641d064940005c0c6000c502d00254 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 13555465 1250 13554215 13554227
    0x9110901080307020d150c0309060b090106081602030f0c0303070f0c0b0408180a170106120215070f0803070f0e0603040c0b0c010b120709050c0403051005060d021801060f 75
    0x703822000082d403900b800350b802c0c070840d15000003082d9419619641625064840c90203400881c2c41940d4000841148501e0800103c0749010040307409400c00b00d0040c400b00d0340000c42c00390003c120380383d601e210000112040340b85203c0da1403401d00c260000300302000914800409180901040d0301e40c91301c1c1245c090760488245211540291040451001141c046a00c0750018110400042d10550740a031000d40407800104059000013400800c072035203941246800e04c55030026050034009082108a2500050140348411a0b00055814001009410000420641c5001a502ca901582c4034034104001414070306400e241c40d004500c0700e1a1546840c41d208007124031669220204050719070600c40400c45980007a4030618003990b0351098030360940d84a5000080c005400c1004182d542e0805001390f0955801900880c0790700000d20092002a80c00300740341c685d640388482c00281e150f8441c4005008000303034840c080e4000095041003176002140000240c1a44c5084e00c2d071031100030000e2030845038 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 13556715 1250 13555465 13555469
    0x5131a0d1802040e120a030207061107030206090d020d02100507030209090108010212011202010f08070908010603080c16030803070507020f09070302070b16090e04050102040b03010803180f0609040f090b070309110901 95
    0xf41c8042101b10b0307a4500035400340200ba4050313680018410424400c2c034a05603c9103034264050f0340000208113030b810342004440741c0407030b50344082c001030b441e08040a9030301c5940b440c2c0314032a10b4a4600141680c0d10a0f819245111001860008596034581c6c00c24000d500a0303414031002c44901c00085900e41c0d007028520213207603041e5600301056a0b01c1c08215080e00d006010310040001d0f0607800560303c142400341754081d50040d89a00d680321096040b1929001025480040d81a4503400402c080f400080550f079001d0403c1c01c0040d03548810307200240e1603461045019901c9582042801001a41540a00507107441034100c61001d489507014440c01c00c080145c841c0000d40c041d0800d21002075140096904a407003080054242601d0b040c0071842c5400c03d80100042e60f2001c20030301c00340c0070030007406001d4000949500c03011803180c0002c07904c644188482c540c0240d4442441982e00b01ca681d1151036087e4001c80040282e04010a005015100280c07095600c0801c5190110031841c0c21000641 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 13557965 1250 13556715 13556743
    0x1b0c090708040f03090302031c030608060906010b0a09030203100903030b0a08030406110a08030717010b0f090607020310110d0608010203010f17190309031205131a0d1802040e 77
    0x198658950343c0f0381030041081c08044080048142d800001a2000c0103441c20b843c020310f01724103194030b8500005003120030301d6000d603190354070100074803006210104034281921a02a81c880d9518400b480964501020b648000d426109202500481103070551202405078401d0b6070074020006482c04200104010b400340140b107800c2003000f00041e50154112056149541d02910340d0054207484010303103900b08903000008a038800c0c49685420380c821b0219030140200c1183c0f20b0502105101e04040d900690700d80c240500780c005a905c09550301000740041450f40c0003428010070010103940b03481e0760041c4241d04080c40c1400c1010400c0c11060080c0c074161111804c3ca0380e2014030300a011404a004400c0c1050316010703246004100306002c14841007507900946440b181300e441d620300f1a880a5140d165482003103010b01800e40c1c1103102080c0c00c001c8410300c1c03001d2580c4403001981c61032507104400740c405040e480c0c2000920210b90b821800c404090003190100988458540e81d0346c2c48400216a2507 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 13559215 1250 13557965 13557977
    0x4080403060c03021309020a0207120602040527040b1005100e0406090b0d02040203040c0e090c03060f0f060907030f02040909060b0102030f0d02030c07020a0602010515030c0f060c01020903031b0c0907 88
    0x6c080c4070002c7d40506950fa16510480d1a03256403081c22040d010b0040e01e054a4030707500014240700c07500b440000b01c082090310304604070030001042e41c0c000c05000041d0008080665040100301010f000702e5680001d0103004114044070307101504081d0105580c1d40242d0300a034144503000405280701e10580e0b40d00c42000e803886440c9a039075030800000350300c02002150250320500c0b000c940385510f421400d100c0e0403060001d082d8039055404151901c08000c114116180c500400c00070701c4082c4045a035041001a91400302945418205034040c1250000d80c5403500e1000c0380c00610800386070400c0d00d4250190300c081043c40c40201c012a00c3c0d2094003d40c29079140100404501404960300842d4010805181c5605080d082c0e4006020b0701c02e00d50248006039103503018811107404100c110188170f082100200002809000440d1090049141491180202049140e51f03440290100c03454a1401030a030b035521403146481d0404c401400340b100c10103101e003544c0b451a5003000c1350802e010b942d00f41c9913a = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 13560465 1250 13559215 13559219
    0x5060910030506121603051504020d03030b03010b03030c01060608010f03050606010503090a050a23070e0a0207060b0d080307020607020105071b050312040c080d0e0f042304080403060c030213 84
    0xa401a1001420b601d401c2480e03c01c048120f40d600381701142103402c0052000c0003561a40c10a036141c2084003003890f000101c0c030000e000050b5034510000c8403096150038040ad00301c1e26080001c0c0144000da0343d10790103000c00543c0911171001948100c3c1600d032180c90b100501d0340c03100c140613810700c0a17010080a580c01500829060340c014030146034881c92020845251076025030320700d41030000c0d0b40005c45940e000c4a00e99800c829072030200c40401d201c5d5800074400c5a1a01800e48808070300940b405040350f03030001d28942405030782d400c04c4902c800c02501c4a010550b15107840c2d1380540c000c44d0000014003500303006c5801c84d031041c05250300681055844a881c6034044920302e203035038050700044945103c10070404004072581064180b189004002403092545008991750130200c035600c0030020805c0301e4440307102031b641e810202980440c080c7c8001170a00400b2500719000740c2001ca190f49084180f4040200b0400f40c040100140c9210740c5083c003e81d81a0203094059010b029408080e064041d081 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 13561715 1250 13560465 13560467
    0x170c03070e100b1207080606090d06020a0c060603080301060305060102070e01030213061e150207120b100b030408070c0501030504050d080c0412050a05070e070c0f030203040b030910050105060910 86
    0x2415800410310002d0500c600d41d100d442c02c0c650f911001e0695002080a0108031729150030407280340d8404000e4541d185040c0340c26001075900c03007003001c00a284035808908100c02c14071408031104015408202000300319140e08000006030824840d03000000d0410700000c01552000c10418100d5143d070955004136400c55082200c50450181454a0255603c00008140c03500b031b228900d03e01d1004201c080903d0810b0030818801407802d90b0241550301c6220300b0000200700d0303400000d1140c0c011850007001c2c2c0714040b5214030409070b42d02204008030040140b00a0103120070003031031700f00d21039000b0318521542d034401034054030f10482c0d015100b5004101540c03116805010102d5000381407102c45454951104034060a142c00954291065030101d1600000c0180800001010b050308111081607071030003802c000c1c21401e403c0e0005040801c08070700842094020010350700944040c0d04865101c1c81d00303940441d9901c4d0708482c003940d1203007040c00015040c1480c07011150401c1001e844c41020020300741c4 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 13562965 1250 13561715 13561739
    0x30303190902040507080f060a08030a03180b040308151804030e010905100203070606090e0309060a02030d05010e2203080c07020d080d020705150702100f090c0305010204170c0307 79
    0x404286050744a20030720300107950b03034415075214003107688510403039007414035520314980001085140a60f120f00001d109107200001610f41050031031401082610002c081c00c003411080c03e50090074044040140000c040c2c0248005100341c074000040c0201900301403c0107420b0180c4602100740c6484003000c030b008a84902c0129041c20418101090020343c0e420100d00035540c2e0600710070042c1c2000c1074100801040b8000c0c3d00c018940003e0500210503a5a8055140e11604101c0361080170300003150a240d500074000e95002079500d6004118039a500c8285c002045800c440400300e19020710205040c208030f00c02c00403500ea400d42d98902c2203a8070b82c031100040d54802e001c03c0c1d0b44140c000c5100d4000a62100090080c01030b00b900258460b922450301c149031407001000710045009140410044950000c0d01244814407101c01184803201c107103040000300302c02100540045910b4402000b8080305400400448038180b04480440d582c1da0401501e86001e10b2003140c2c19040034804100702c0762140d03 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 13564215 1250 13562965 13563001
    0x12010204050a030b0604020705070f0501020c0303070b0c070201110105070518010f090501180e01080f0c030a0f0312020d05070905030c0607020a050d03031b0306031205030702060a15150e0f040605030303 89
    0xe8001840c01e006078270b440d407504180350303c01545171060100602c400c0d40d05001602e0360810650095080101c0c0e81d60740303002c1d80350081075078070f200314003007419000d5a21130001c03803c030354200c200200010300780080010300c0d0745c1c00080030000c10024021004025403003034500281c0e01c0c1041c0e562841103404d1a0044901c0b05c030703540070321f1110f2070564008508581c01c0c5080354000c00d180801040e8a180c501c410070300709940448a14443d0300160713818004100401c0c4181419175061816408002400c48204003d0040e0340034090748616003410405030b00d400c101c85205981040301200e240302164001c1065500c2040c800a4201005420070000bd0070141101c0030028403a040c081115045545c0890420909981000020351a400100144908407010018149041c5400d40c55440d00940107582e43d18007030f0691489541c0d651064449542c405034000246c801444102c1d0120f8240c400188403014802c0c60030f04c41e0f5294103107a58146000e1050200b220f0002d00030f582181c1d40ca8072a410045800 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 13565465 1250 13564215 13564219
    0x1031a0a0f0e16090908040b0a0219030f0206090106140f0d08070b0a0c0305040305071101020f03270a03020a051e0418050c01110613020109180b12010204050a030b06 73
    0x440c50010640d1450090b605440c02000040000e800b10440344280c082d01e40d0302018241d45050308000101c3c2c0e6060880c0d082c0c8a14002d103a0b580c0071f00c240103e10348441c41249202c0c02c1d8500f103014003096030040d0080703081e1605034200c0e2036079160100c82d182201c050b0300c280804240c0c800000006400d00300002c0b408030b0340040601c0460320765511810f03001d900410341110561448010024080c0307281c420341d03074400d425240801083c50990f07000b50407442a080060100d20714403040704200c1c1c0c8200b101000321610744090760f48401d183d030990020f801c010100c0b41d4036841e003850581c0b843c2c24080401c03170440b40c000b084c14240928003000c0c40703140c2c01c46540c40d440c42c1e502c801c1e000c061600c46010311480c60060f0205450540143c0c00c000b4100110082d40c20304110790700b00c0480c01804000f400682050199941310f404610070720050b11031b0342540d8001003c0e810802c00d4410103401c0356000b03030144102641d060003003021212a06080b07204901985520425080d020b0000c07898201e03040d6409440 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 13566715 1250 13565465 13565471
    0xc05030403060608011b05070b04020108040516030b0a0c0e0f04020307050d0203010303020721021e0d020301111e0301081c030e01020c010c09090209030a12030b09040308060306010e01031a0a 84
    0x4a0702d524060741d60980110065039140c8440c008505020b403400a00c1c18a1450070703906050456440e40c0c1c440c500580040d040290764408102404414001b4140c40c17150001c0c40303801c8560740e19122141e00802c80d80c40300c032645000d00c00325815001d94508603c0303460040c12410500340c0300341040000c2d00042d00e01002c00106000350440c0780c0840c40114081e60007600140314051070003110102e03200102c50003081c43e078112440301c4d0058031001440781e90450700c6820a04900000320205100e06542100030f549503003480140c0220201c407100401c00810311104040d40d00c1e5441004103560303c001e22030184554011680c4100301e2030301c0716201c00d80008a05d8041402c0d03016116041c00c0e80c0081400070b0680e5036135100301d218650402e081e10024940c205096041074811b500007500c2d1440031802a20140a08504000042c07003039000710080400140a2481c0341041d040041400b0f0085076003030700a124080020804503d140b030306030304880d40850349207040003c0c03607000128000c01400c450241a2 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 13567965 1250 13566715 13566719
    0x40c080114011e0329010605040b030a09030509030a060603050d0c03050a03050411150c01050601020106080c0f03120f032d2208030a020d0b0a030816080904060902040303020c10020d0c050304 84
    0x4800c40b0b00010a140407841d201d1390520300010300d12410113074000c1c000c8c070608001c20890000380c441581d034805114680003d59510318202990117100d40460150b00d8060100e2000800140b51b202c441a01e0003003048900c07456420b8805c4c1d034405210003010740420000d000b01c1c62801e1090300419030052040610016400b44440828421821305a991038080c0000ca0610310040d001d04c101e640c8048244024000c00d45801501900c9401d40383c007090040040010b99081034604016281450000b0507440e5602c50118441c80d02e2500180c0700b600b101580d401501507684c00b00d001c0010b03040300100c082c008a880e4106060a4118020706c1c00410401028103000866859005580704444182c17015903210002c504403012503151585141c8030f8091800240045115070b010344103a0b40ba2120170100f89111824109041d000b404080c0c0d60003403c02001140e54001c98001d4411070f4460b07001c440442101c0380810042c160b03249410701c0181d2100044004c5103100d038295910160280c07045e80d14141e = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 13569215 1250 13567965 13567973
    0x70c0b040c0b070303050f09010b010e0d110a03030302040303020712080d0207030c0b0411030c030328020f0a0f060c03020c0604110f18010812070305030a05040206090603040605040c080114011e03 86
    0x3d000000b042c0c0100c2e580e14100816250340030300640c2e000c034000f0020000406000e00103082000d0071085223006130790b440b80f0348042061010503240740d00300003800b03200c03490354a01e00100a03500034042100140580500040c86540418180d003100e076010080c28100780e0b0091480d802500b06400540400500342014004a42c00001c0c09020302d00815106190b00303001c2013403500d000c0360900307218060750003000070322496504400f401c04a041d03030b800d984503000d0318a2000c88c0b9103010400403d45a018146401003005040c60321180001d100e40c1052124000a1205030220f0080000300c0d60140c001600060001d0401d83d500c103004c440042c01c21a200c400100450300c2d8110002c09880003144c41001409580c00420811102c219680c2025180041e0758bd0028610b000140104850b9910346010038119a250380903500c802002902d1241c580c0340c94145035014001c256802d1312a4410f85501240c0410b0600401e028842c028521070440e03444d00c51007001c44411620141e008151030308003c4001 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 13570465 1250 13569215 13569217
    0x70f0c08120105030c030307031e111603030f08041e0602130905010306050c09030307110a090c0509010905040b06040b030406060504050702030c010506060406090302010804050f0d02030a1205070c0b040c0b 90
    0x10301d40c0c0108070071956060000781413400c02400b00c0984a64402d01c03c080000794040800410405002c07100c0292202c416815514502c4100c21150640204c9070101d1204140d20355031781c1101e00a03503841c00d00f11301503101a80c3e1000706880281004120117203c00718454040e429a6105110392001817600d0900080c003001410b054100000254584004005000300c50049a81007040c0c0c14040785466801800256a032092440041c41d0404070905818141d481101c035000070310b4440400e200400005c2c000130310980c0481c5510b404504022404600350815214825250a01400092500c1e040940e40600c42e000100201c504523142c2d0720100c0c060700c1e01c3c050325025170400d800030758403440406041d40c25508000d01c02c1c1e01031982804100f142d243e014038107400701d85e02820444096100c9043c603604204801070050300d030303204100912000980c00401880c001c2e1160f030b504000201040440c1c000e95105441100010740369620070301c0801d084900044e00321b03120706551141ca607540c01c03000f486 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 13571715 1250 13570465 13570477
    0x5090d1104020a020a02030601050405060a03020904110d060b0102060708010501050307030e0c1305101a040302040c030e150709060203042301111b01030501050306040f0602090301021204080714070b03070f0c08 92
    0x1600005c40100860400704070007030141600b150140158506000441c040304441c2c44080d11030b03c01c100100f000e01034512814940c03031308054030714103041c41c2605010300908040c0e00780c54018801c800010758464403c540190688070165902451034441e40c00032000b61450385030705805406010043c0c0701d150f40f1050600460303480b40310702003003a190a4503a6011f1801e550f01c85404d02800f041516907040360b1b28101c4044ea581203c0018410310001001c030018101106000c81505c6000803882c414606220b080d4440c80590341c5200c0026101c0c50100d03140d01452080386000040305440c40c000c50b0f82c900d242d090405c810324000ca000510050060f142103a44103070300c1d90390b80e4410000701031940c5c0344c09594090442500248260708013603a680e0144000c0c524050191a4041800c4980342c1d401e40445400d11201c0760441d806c0d04044c140b90550342d100040448200b1201480b1010a0030041100c904039020919602d04507540d03d10705071003509a251555040009014052000541603400780c46 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 13572965 1250 13571715 13571717
    0xe0109080a0614090604030504120c0302040212040203010501080309010813080c03040b03010609090b01021c180602100c0c02100509030a08030a020d062711040f060c060c0804020105090d1104020a 86
    0x24007448103c0350021803550152840c0e4440e0020010032002c80c1d0410102c0c0c00701c45001c60b03d89040b5a09040001180b040c6800080d801400040e400e0705c9512500e9031a406a4003c5000f00030303690761010f400b50f5038492807a900d40440c2100b0005401032402100c046d400c9800b8a00851400c41c68000c500e0031765009411640d10b81c0070100040c44400d6000c80b4200281601d0b00d001c10010b030780c000c000703503454401c42c7c0703507000410b12864031000551040b1070f02d80000483c80c15201d00e41c3e0301c80b1030194540d10b030080c6221255250080744602103210b030b00c0300721055402404003492030010500c04c4602d44d00203120160507120382c4442000180c0c81e14025031207002548001a140e0107211080d005603500ca9101c0c1c5504040036030013070031844042d201081109084240000d00a0260043d003246002c0c1c2d52103900c0c07100e5850400501c0e940c02c00c8240d025188510300c108001c000850303090f14800801d8078064000f41041c03140382c25030b0800c0e54044141c0b50040b01840e0007076102c00d0015003a6131083c000b040c = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 13574215 1250 13572965 13572971
    0xb0f070f0b07140310030b180304090906050f010e07050c24041101110d0509030a020603100f170307080a031401030302031c0506090c0915040f050f0f09070e0109080a06 74
    0x4240d900c00140b107401c0050b10f486601d0b50034003054502c80c1d5070403404042e000000d2000482c0003010609090402e800301d00c41500d4882d03a42d5a4100020b11900c01d06907003139070500c0002440310303101c91003030340c1170b20780d00e85038010b8640b190308080362250403a81214446201e05010140c20002d13603010303040803880b6500380503c0c52409240c0010101243c072074050600c0000600b9150a04011402c0c0a030070607146086602d4030a2130000030301e01184401d01079085000001840296809014500d068500c10142404800da4481c3c1d443c024540840039180d2035082803055a0008003850300416041e4650714010805000d5030f403e00589800a80c012405030340005025541e05540140c0c0e891411880c860800140c5840780120b140d006001f0000316009030002601c1440f9a540031001c81030310178507062251196150004401e556406001740c510038002c46851071124585100313140a03400c000750218650740c40d00d1809170780c0c41148001c83c5042c40400e810207d03102d1400c029400d200f0740903000c04 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 13575465 1250 13574215 13574221
    0xc0307060f150905060109030b07020a0807051621020112020f0a1706030705150a0203040b03090a060f090807030c0204060510030b0a050301060305030a0f090506070501020d0b10090b0f070f0b 84
    0x1040c1c0b241001d81c840e07141c042c245030030001c1e6603800280c807004803600040984025911404100c0c1058400310b402041040d0100c0c11505010b40029007401002140030020406a20340c0140c2480b1800594010b8010515146075001544503001c48095110041c4001d42001a04804003900e82c00030418100051700407280c81b0340c144145400c143d0040e0090b405020700c41d08000109495404d942c841442003200092440e110354401c1045130000d09101c2c01e23454903800c040c001c0580310350f004901030b100e09041200300a0180090302ca0419985e603c91860351414a0780d590990340391700d55090507030348542d94410001c1c0c2e90f00c54061700303204440c45030382c0000c0d292076131020000103103007a030001c0c0d020380e1401c0e8050002840002c02c0750607210300b0741030200180341440c008542304126508860b8210300f02082d40000c0080c150050310000501142c10b12a069105050120846d80e01c3d402d440081e021900030088042140028240380380744c85100c034a0610692502c4407002c55441080707440511710020 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 13576715 1250 13575465 13575491
    0x1e0e060910030212180d030b060903010212010602060702030a0801120201030b0306010602010c030509010b010804021302070f0f050d0f08070c1103120909011208030411030a0b090105011401020303010f03080c0307060f 95
    0x4c0b984468081e40c0d034102d0846000b40c1c2c540d00c400c0da2030064185907482803142c071680c6e5482c0590700043c4000707000f55a103e0388010000040030f000c1c4110b10140c80b440000c640c43e00d00110030382c3c044074216607800195030301e000c4040c07859076485081607052680e41c0e070780380030030752800d00106029103100e4001150901110300020700b124002071221126900d0a140c00095a1f07000640302e800c942c0444043d842d502100d14807000034841d08070010711440c1444500c4c001c10013128610702d6518051410317600741d00c0c15003009454154030201903c001810501c0000e1405005800d082ca5090003500c007103003201100c030042854124171600064039101d012480c06500c0c50b00310f18241c05001302e042608035140791039030380126034000034200078100c003c0c64040380c0c5592000c00c40c0100c01c9070002509403550030009101402000e007805a004080741100791822523500000440c3c0c100c40f05401040130486c42c60701d5400740b42e0884440b0703290030f01081003020f005c1b4002e4003c0d918131b8052050001211008100 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 13577965 1250 13576715 13576747
    0x5030a0e03070f030b04030513030b01060e09060d080a020a060f02130b07080d090212190b0901090209060904060b0d0804090501050a030b060909120d09020a061e0e0609100302 77
    0x16060710951007500c0c2030010042e06400d0310304072640203869020940300d500e01514a40100b50034a0071800700021b00100b070020301103840f0f04848903a2107914003110301c1802e000540030111400c60b04814101504000904410000c00c0e070b007074840c4144e030501e0000ba03446800340d81180c0701444540e600400c902c80d9464640240314000d00702184000d140c00020340d500819402041c408286c541c3c1d036410751006540311524203054005003081039a0300150010f11181c10b01c2040781c0b00350344034802c42001a00f01041449802c6021b80c00070032168656071145d003045001c4030010801c50f0f143d5210001140b40c0e4950003040e800749403040c503142d81c43d54249500307281100c005a11141c42980052410004102d441d804190403901c140c510360300d40c0d5100c80714940381600510a40240590005551a0346202d03640328101c441e1088031555200d554618045602d00c1801000b444d280c1c640041c010401c9000703002e050b0f120710002c0e20003400c1086000000e1a00000d0002820129400040300c41c200a5488 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 13579215 1250 13577965 13577987
    0x4020f010206010609060c1b09020304060605040b130b1f090303080708060907050a0201150612050a020a140d0603020901030f110108090706031109091302010f020105060303090405060f03010905030a 87
    0x2100502c003540c035020300100802c1c0a0311805052002c1c442c03019083c031003c030a0000d40004079801c1c2c404100c0d600c481400007944102d4080c4c1d2114540b0304007207050320700380c0512011120000c1170706a14031000d04020000b00741008840e0350001400d040c5074507900304000d5290f400078481d15001c04080ca07504000d4802c001c020140c0c400c001e25038040090701c0d59050900364124a161401c0c0c2c0e254403040350180c1c0108200d481504050303441860000c0d0140d03100000b00c8111100d4074050156844080400040c2d024000784400820300040241c8100441c000152070700000c44040440c103a65681c0104940400a0b0019130351640c04142800c180203480800300b40d40442031030454070300d1410300c0d00c1d603407980414080c80701010707141d039002441550003200f81c40d0344071801031071244541006443c594640360341c0c500c12400300c1c00d03440341d2411250041c0300d01e5200310409000307580342c01e0411b02000000c110013404181e00c21800504051682c609200710b4426a110384025a43d6108060015103448451 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 13580465 1250 13579215 13579217
    0x4080d0206010627030305031806010b03010f06030e19050a1401140106020f06070f030e060a0c03050c0a0903061e0c08060109050f0303040b0c0307140703020406090501031e02040b120604020f01 85
    0x1340c8007140208442e4014008994062030159102d855100480e004400790f2801c1d01842e01c00c00e0000b09500900308001d6048542d4208080c01d840c2e41c80c0c2007a41600c080c0007807010f035500000050101c0e104070303102c1e24a10070720400945401d00c641d56111016909010382c56801a950303200000702401a55a500307024201c4d50000700b003a251030300003045d90307444014841d0007000f205161103040c0300d000ea0450381007540b010b0b081e22150b01c1e100b030f40e5800900380588281300090810300880d00c0d2860361000c80b091403040307030f4600e480b0741e05648444000d0700003500944084088110b080028030111b00c120a440c0d00e00303030b039031240d5030801200040c48100700b900594400c248040bd080c0c140c2c1c0e000022030701283d5204041980307c20300818500d046000d1200064010341003154096502200030070750f80140d83c4210f0b0100302d22a00c600d0782804844090100030540a841c40c2e111050700f0a80d0040132169100400101e044003211010407008401ca10080302c04e0341c48003040c8070862400e0035010344800c0003 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 13581715 1250 13580465 13580507
    0xf10050a0503100e0106081b10050307020604080c030708040e04020f0303030105011d0f0d0c060807020304030f2004150302040b0f2b02060703050309010f0902090a020f04080d02060106 81
    0x14140082e450380e401c0031200f80c0c4199140e40000c4042800c0d0840c038000c00d80c11040d1668103802c00a0035460300e000c0c6003428894400c065220f6a20fa02413000d17207000705407541c01000d960b551a5501f4519034400c61080e0303414070081c4218800240e1110080014002a0b820000107040a1060205c5220014900341c42900180300500190740c3c80094100d1404a038500184406103041c003081c58011a840c0e800c4d008100740d10380b10244144402800c007103c09656818807146d8508034200d80341c1c01140030080040d4840300000010500d200701c801000b5184103258070803402110001340031101d40707411382d641d49201d080c410415440c1c148103c850010060300c2580c1030000c03000010f600640c00c0030030410680400c00302c441c0d20aa552807913101d240e9015100503513502040c10081c0242d04205c448a40075030900703040a01c0710801e0b01880103056400b0300405619203031003401d24042c1d0011002e00401c04000c1c00b00044800c01040032104e0740b1145e4018100c0d95050140040c40340304150341c88594455 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 13582965 1250 13581715 13581719
    0x415030e07030521090301050c03060901090501030503030601110c040c020d0e1503010e1306020a020309330306030307051c0201050601050f0a0e01140a030509071a04120302030408060f10050a 84
    0x1000724092844c52510030381e9071091415100200060301864013900d0b015841c00041200101c455401140544400c0381c0b40c1c215680d030740c851941a22424040204144c000b44049083c0d9400303050100040d58958054450041e082c0000c07600729040f103c40200141d001c1c0742442c4a042d007102050714180340c1070792401240f02041b64807128620062042d080b901040100040201451060301641554000c205540c3c500011500a64980112020070310440f40b0812200d4988441900c1c0314400607050040500f200c2d40c1c2404403d41e420040c100340e0540020085840018000c1c8800d031118071801e40030384900c040701e910003800c4480003020241444410040b940c1e6090741401990413a081030300e0a40c3d00d0280101c01200d4a030302c98103200b040c3c154081b4007203440c04c2d01500f001f48141641e01c01c80b64039607a21444000340c1c1c1440c40d80407001040070041400405158160901e10034040e0044a2409540718003203440c08408480f074007240c24841003840010701c0040d04800044c4411200088894 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 13584215 1250 13582965 13582973
    0x71701020901020a0212031201030c0305061302010e0f041803080411040606090e04020f0402030a020306030607021603021e0307080f0d0f05030105100309050d050a0e0618090403020a05030415030e0703 88
    0x1381040e40041d101e2004103040840d18a4100304480e5030301d601a0305e008055030b40380f81c450459019400101d983e4012500020101840d1042d020000d0760160b51b0300b410084c409060001c40410407202c10b0308140c9070b01c400d0282d072042095070880e89220780d407103a0a80c502410801500700046d40b44620a40c01e200301040002d9028000206a5414905124540c0c82e540f0000c2d07586011201c00c50f0704540040200010702039943d01035031042d0300503000d4405981d0303011400c86c2c807132960015030a00915090780038405401c02d4800001036903100c49191140080b04000245070440c2c641c0141c07019030245188901505090141034414080c0e030515000c8150207090141c40c0380014080c06000d42c0c0716501015400d0b1003038004a5a42c0d800501f9184520f48420004002d5031008291a0201d4241410b0038001c0c1420002c07074000c0d0240380710b038002c0c0141c41001c211950130058020b404500c21038002501041d402e01c0104000c0032a072502802020b00c890014040e904442030054541e0000c1500700046 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 13585465 1250 13584215 13584223
    0x30f0b0f010503090102131401020610050a230301020c01020c07060c03140901030f09120e06071a07021c020c01120c08010501050f0c07030515180304050609060702040e07170102090102 81
    0xd603030300342480c035129520390500c54024002c7c2c0118051929004000164000a10300b0b1107031040e00070382c04d8440b1555001d0107104207044600c21181c1180135100100034019101400307403480031044141c0c80780c82507610006401e98000d80c80f106200e95002452289101c0100041300081ca200d08058103107600c20703140036200c4100c4140c080f014080014031440b844e8400d50002a5002244d80d0801144190341010500c1c1c02155518501141440302c0e400f03164588607047e01c410a0307000d040000c1c15034508551107c0c04001400b007606620902d00048ac01b02601c1d40c120000740040c0d40100503c52183c0001401c0390121012858114a060911142660b02c84802c5041da6001c0c03c0c05039560b90718040d808940d200d1210503001500a10340040108640829210700c0c0200c14030150000341c0700c2100d000c0300341d60380380c50b0060244d0081000304480d0820754042d04000000404550904803950041419a80201c004804a4100b00f000b0b000c8202d03500050031180004000840c1449901000030303580d = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 13586715 1250 13585465 13585489
    0x1090602060712060308030412020c0307030f020d030c020d06020910032903030c010204090509060702030c06010312090308030a020c0d020c03071206020714030a0905010e0d03030905010902030f0d030f0b 89
    0x2046800e95000030403c501c0d03082500210b5006072295904d18040c28031100701030340418000014003a07041520800e01d000501081a6600107a01c409001002c0c0c0c200000386a40e460202e00f0301104101c10000341e03a804040e402e0b400e00a18015a0740c40c001402c01800002c9044100180f40c41d004140781130308800613220241540c08080d262645c8280d0002034698003491000341807a40c00040d0216081106800c00c40c0103850f5103084403010744401b0828ae031240035812000e007240c0e20060042001c181c0064001c61b9182040c1403000c405501d94a03084200d03402200c0c1400c04940003c0c126003908020000d42500d0b540713078400b40483c002207400098841d04540300e0340e010403924101d528103020065048440c0c0700d90001a02001c504034207606512a0840002d05001c141e86010004165015448107920510001c0c02030003000c1266405a00504e4130b8441900d20f50b50310202034005883c10400c49601401620040c00109040c01e40281940c00c08510550203600700b0600d202941c44807414040 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 13587965 1250 13586715 13586717
    0x90203060301060312020c0307050604030222020d0903030b0f0406181a030102030702070509010603020309030a1101020706091104060b040803070b1e010605070b01080312010b0d0902040f0506040605010906020607 93
    0x1959485200000b80944610740019080868146081c003442d86c000800d6020b2031801d5003601c440c542d4860410909001780d12019402441e075401c5c03462000c0011690001c2540c0e0100d0060034030121050034000ca52540034200d0109a0300c144540c40e030320701500f21569890301228280000c2d424415600d04005500c500d0a4540e6250100e20344c01d040c41514014001d00090700031500ca10700114002d40e660001d1181a00540d01c41e400407800d03512a000301c9109040d1040113600d0640d150340101c0303000b0902c207803912140d5400c1c031101c070006102d4081c51004902038403112041004a40402044a000e0790103881c0c2010300b00b1003000380304008010749203043c2d041a0188800d54603844d48556280801c62001548614640081041600b01c0058601d4602600039201c0d40da0300c0f400641d03641d22400810305405500720004201c0304450400a086164003035802140c205a26404142580c420f424400401034036481001058103003403140d9402440c013443d2505803145060000303503c424001d04204 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 13589215 1250 13587965 13587967
    0x9100506010207051e01030e061005090403090305010f060e0a060303171005060d0204060201051005010804110310020a021b040504020603010303030b190e040203010c03061503050415060305100e010606090902 91
    0xd0120381c001d100c418000c00c4094003910329100c1018265070b44080b04140f46021030303e4560240b03484100040d840b440380b50b90b140c01c181a40d003441c1c108084502c00400c21400c1003455840440020400c1c058106082100310021841a0a000300c1903402c0800501e010801803030000700b04042580418800449000419005202d072035004840c1d103080700580040f50041d4001400018003406a4010070884850341c0c000c01040d00e5121821810720102e10406000400e10700c003160100f0600c2d0840e0074003450050449007448001b000b400260303004440c03000090303041215440d40d915441090212114012242000030385425800a04240018040030b010140d0310021000541c4a000309a61030502c0320003006070407903696034002460407080b6006c900035403c100311030208034042e0007600c1c242d840050108132107088080f800ca0007088010304c1941c5540310001d666010030302c14400c071005980510040d0494490084264041e15802254044181c0c9808010812940c1c0508480183c8900d41409 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 13590465 1250 13589215 13589221
    0x60411060a050f0f07080a0c3503130c12050c0402250302010204050d060203070e1503010512010906060e0106020f0601050306041103010b030d05040515090d030503090f070305071d091005 82
    0x12200303005d82d4800509060300020260502c2d41c102c1e06c0c80d440c591080a0340c46884418064490781e00c44090352405080c9040d000441c08000740a019503030224184800d20700041c1a41c9454650591039845001c0f80c180150241050100034090502c641006450075440c12078070205610882c2175881a50341c88080485200301014801c1d01250011b1070000c1140c00c61020342d0400c540294400e603003000220f0740400d98100700742001c044e00418204403808003802c581c0380000340301d103800c115a00c020300341d543c4860789400a8020300c01c3e10060200385180480560602c540a450316140b5030199a15900a000400c030030780c0c002400303952099018001204641881022038054020194900c2d4140603007113440f5641a800310240080f20005c98048003d50786a00d40c8000301d03c02c002120b5004480c0b88807050210f030003000103503006810841164610704900126505140c0a5001140c19400074201040b12003c1c1c80c0001040c000c0b10080d003026418905505507640c3c4041000f001025190800 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 13591715 1250 13590465 13590487
    0xe01020708060c19020a020315060f040e030406110f0606100c1406071e02030304060213050d06020711010306150305070e04060b09031504080f03040501090204020c060411060a050f 79
    0x840005208503000c507101d90402490780001c940100200c04c0680c420703045005005840018071608141e0068090302441303014a080e44c1d8408c2000300215080380300c100c0f041003140c50f5485503540c04021000510b84650800d200104807080c17042400304950302c150300c114907030040805e846030800c0c4101e8881e50982c0003100150b5804900d0b4030081c1c06840300300d666044000300400e0503440340c1e038039556512a95041419001050a0b144141001a4030a10008001403510760080c4888100c0022146081e9a10f00004d8100180706000b200c02e00e401182030302c200f00054040440c18102424180050b41c1464030004106101c4c10300e070000c0644800202d400781e4003c0b81d0007405410060400d118254503580d0324910741d8000c0031401e000f0311682140c140c0480701c900c8240c1c02b456000d8112460300c510321407500c10f1600f001d4410b54855580d520454010b0355140b009003610f502c814040c040300e250030b0619440c41501d501c1b00c140107800c20840461140d5110007182c80302d81d6440003140e107910380865 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 13592965 1250 13591715 13591723
    0x91209030114041112010c170c0903060907030c120f02040213150504030c14010912060608011d0d02071401120902060705070305060901020711010e01051e030907050108160e0102 78
    0x6800e42051140c005000911804c030034454800c07130302690491404908404010b080f5a40b4500400c00581e59820846100c43c0c0810381580040509001c5424030100b440068107054003624144410350000701c0030000c101c4140710020081018070f426400e41a00c44d1610b05001507002d400070b200e030380d0008049000d0751040030454081e251070341c8550180c0d0025a001b901d40c0e0302900041e502841c8260002858181052080400c0035042c1d40f100303002841d040e00c8001c50a03140404803860b03611000d02040c1c150b02442281004c0c41002ca41d000c0c0c0740c590301c0a060030100c030301d41e103c000c54021003014050307001814401032620000b0711f4840e80200e0080a464020400903000030361114000660300d040c0000040d210701542c0c00740c0c1c203554258950018182c204e110310b40000741030482d221400d944e55030080d0f0540c00808010f060491400e8244040d00007020881c640b58816008040300384040900e00304031190107008203013002e82850401d81d042c1900365088a08050800661111690b510703417085c0 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 13594215 1250 13592965 13592981
    0x50d1e06050405011d070305071412030c01050106030e0d0212130302040516020f1c050714010203090706031104120f0602040308030702030304030314010e0426070302010e010b0103050912090301 85
    0x40d404018a08040c90070a02a024804106003200b142600c040b0040c0c20100f16002100da00000916055107400505030303241c0c1c4601e2503980c1c004100b641c2c1d1050060207000401c5180c200d800000384542c14150050100c0300318070b1b803041d140d50001040780c84a9400040007142505007000c103540380c44454548154005481d00020b401c00e0400041c4074074031850107050740e404c02047d000d40c2c49400b0502a05a0356a07900032100c4287c0e84140d1498003020b0040005140b41400f500316400e242c0c005a43d42405c1e80d009540d085040d500c001c2d820048140d261155134070480201442510305850110344103010a12200081d105c00c03c00c0050f48108049036041b10001c560156030b090700d0b440d050b900a91650012034041e0042400c0c075044840110304003241d40c1c141c40405980400e285c95a4582000076650500c019500c41c1c14010403420000441d8058001144642d0000c54500c148288950941e56100c80440c1410700307280610a00050202c0d40000d0344105400c4a5141c9841c0800603000d04160 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 13595465 1250 13594215 13594223
    0x3090c050406080c0f040203070903060c0e090106020a02040510060903021c020901061106070c080f09011701091a030f1207050c04050103060e060601080705090d0c030507060503061306050d1e 84
    0x8202c0c006440304002c200b80e0440001210003079540440c20f0103001c00c0c0e00c000c80d414000a1405030701880010003d901a05110b030651900341048507404020490082d400c1e080390001da40700010100071407826004066002d0301d0098804482454050090b280c03986a01009200e5981d0b41012143c004880d0b0707445440c170f03400500317003031302541e40304030150065012401041c410701403e00001c1d1414025081d24044940c803c10340c616100108807000d1094001e40c2c180c40c10045107001c2540c4000494010301e0290900010000340b0310822681680c122915101050180e00041c0d1001c0c4850b00c040341c0240e80c220010449603595860f0700d02181040c10a00711140c9c0145004c0000c010b0184541c40000806244000c03510b60740c40e40740064a00a00480c1c2c0e0800003441003004441904090200d0180e0600c03c8990b03904d055281d0f501c003400d02c84290020000038001000b0030000b89808240c150014194840400c107060824000c1940001c3c54100540105411420715000103505050f1200f004c1e04 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 13596715 1250 13595465 13595471
    0x3121812031101180c0902070506010b090f030a12090501020c0303030c0307050f07050d08070305040b0103110a120b04020a0f150509011101180201090f050a15020f030301080a0c0e1603090c0504 85
    0x20384413549840c40309203038040c0c4a5040c1a0400318018003284203e402141d007007001054240c2c82c00e078000104d60320554450342c00c41344c4081d004109840030003540c40b00320302c1141c20340c000c9805281d00910900440c2c0c001d030704551285e10040c80c291004403c4a0300702800f120f10954940d03c110050b1007502c41c08040c900b12281c002044000e0290106070f6044481d4140c1c0c4112040d104c0b03c0003101580c1058802401031680d80c6c1c01080050887d0461040c007903c0582032083c81551035940000420040301c09560200c9040d0400c011450200d81c0381010304030034181e60030514100401941c41224010501c0306100780003c0c2c21a103a0700502920b001c0e030b12104000e000c0c052461500c0b00312040c0792035040b40840c00c88031010880c4a11185484c00b41c0740c024000c410005c3c680b034131085500301e10130015000e60141b00d40600760b8040510095010748660340041c1801c0040c0c1c6043c200c20180b0340e00180a00d62800184aa003500c00c16825000075150f18001c43c401c000c82c20300301c440344c1e40360340300d580c0c028a = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 13597965 1250 13596715 13596731
    0x15090109171501150813020102070b18040b01090803030a0f110c0f0d0906170a11030117060105010201020702010e04090302100e07090605030c0907140c0303010f03121812031101 78
    0x600000e12000300700c401c11500000e0f0f40d840c08000a03030100b0035410b1000c209014002406846c1d54100031160900510403581226a9205900150f5008044050398224180b4050040d424a4000c0c4007035290b0a29191f280c242c03909034060340320700028168150f115110000d0080044158101840b1003480601c46035594016101d11070352040040c645034040c1c014440b0382c1c41058001d10b0050121101a119003038218a4400071202094000307102011103561a5241080381c0d0702c05c0302850280128104800b50b544100001c0d901d0701d00141c0c80b150441e0300401940d00141d0303016a480012410588001c500b03c00603140c16400d1100203c41c19041a151060410201d0000100c16080b594610340c10845640c483c0c0526454144908406d60000c01ca6004034090314400c0c400098015400c000060800c1c1c41d6100302e034295403082e8044a50715110190a00500c61068081542503100d410a82c200c070404010b400e2602007240308018a401058010605250080400650210500008011a40b = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 13599215 1250 13597965 13598009
    0x3031611010902040f0b0f030601180c0306080a050a02090c0f0d05041401050c0a0f09050d140703080403060c0801170705060f0c06040605090c10090b03070c1203050402090a02040515090109 83
    0x1c0038003485210390107d0b0440216400d0105007941030391001c012a02191000e0301032000038088608801040558803040080c00a40a1049809161241000e0641c4d00d0072401005807000000c1d140c084400000c00c0030301c2a0154120460b40d161909400100300b40e5a5400e0111040c3c10a000d0325445500301410441030f11252401010544601d450f00802d00c81401811030320f0024900803150407001d04801c0c01c001c030380040e4050503c0d44d0804112840b407504c13607484580d20b0f00716a10441c0d050342c89038003521005811090b6903014181c00302c2030030b11070802e00b40c550303540e07035450722510b4011407002881c26803644215046611060040007201c4603030609240c010010310301112010403d0082080281031032420041501d801025950380c041120300b4182200c40039400507221405110620701c1c1440042ea1070200c03500c500016071030004aa29040c0140120000002c2000605a104210611182c0e035800140640030100c450000e484800d240b0050700d112486420286103c07004105144d048 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 13600465 1250 13599215 13599221
    0xf060615030501081209090411041e06080709020702100809070909051605010237120305100902090a030b040204020408010510140103150302010e04060e010803091203031611010902040f 81
    0x214071348812a11074a05842880c18280501d032100c0e5404802180454007040f40d030702131f00d0301e007400040001170008580704e040700000319090007840c4e00c50f85a15040200c60002d01031032004100341d00c0c05501d0014260300041c0007107512a524014400001e011451506040102c80701924421b10100801c55032410300940e00c1001420000144882c42e9000c510741d480480e50380031001c0100c034244c0003280c1d01c543d40e145420684070901509400d0050345130109010f00810461541c00d03490009660601044443e074101c04c90b0401c020203030040107412030300d803243c10300d98040744c1d040000c82065890314070003d0081e204560010201d0740c01e2405000c814a500014981202c900003041c490b001c41b00e00054040e62002c0310800301c802a150403c0015501070303645ea1225981c001c0000a5440d251002c491030002c0c20781100c90035a101140d031a556082c000d8401e10020b150300000d41c01c615050784c0c80188020034807221810016a5910b14070140400d40040001c40da000b0400c0c8070460030441d0010003 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 13601715 1250 13600465 13600469
    0x9210501060515070209090f01090b0a0507080402090705090d0c031209060905060304080901030902030a030201061401031505101202031905010b090907030b0117010f030201080903040b04030f060615030501 90
    0x11035441c0c814000340e81d00d070a01e18400c50300c0401103424140303043e54007000710f041c2008211903803a0080300d910082129081c0f04808016109003510401c0e42003a2410600321200101854284801001070001580e52000303420b80c082d00510b40641e640d6041380204070058103000d40240320b425104d5020080144254000041e12195650150111303600c18044454100038402d6a81010701000440e0106a51700b000741880901810027048140c0d49501091130914981c0090700180d64031602840511000b1301e009074000c1c02440c0601484002c8240d00e44080601c0c0301d2584524203102c500034055000c1c000e500d480b40c4040704219103030316000540c03060401c4500d0014000602d400000724a003100e082c1540d11500d13000c0e0400c4860350310b100d0f0950050405903125030501c4409090811810707640c2e90454064282c54050140030762031440090700404003e480c2519a4005001c180503000620055900722a00144600ca2404007410018001c0130903800003a007003850340090341c840e9901a007201341 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 13602965 1250 13601715 13601723
    0x8030307030b010c110105030a14100608090109020618150a03050601020706050f07020f121902041404031d040204030c060c050d0216061101060918030801060207050904060504030921 80
    0x310001c0c0b4011503a2402984005021081ca100345110f1540714102455105135910b0b0300040c411089400304c64850011182c030404c8078541301d020b001d8603078804d1006400c0143c00000b0b10490032654002901406150403000d540c41c091a40b12480e59203500c001010f28031211240c80e81c2e440d040000030050041114490701500c90392900155503072003002180d0070b544070f180c01c40b82007178403d5082011800c1007494450b4040c6590581d000c41403814842422500213040881041c1c04592041c0000e4941c3e1004103610f00c03040600704004aa04180241540e098000740e44404469030b400180c024021908040c00b0b004103042c000c214280c01c1010070410038011744c200c49081c1c290f40002c0383e54950b1041c4440120900500c20416140503c19203540150004000700c0d1940c1c8038861002220281030080407006118280a801e050b00714801a015200781d1000c2d0550505180101e4500700000d840181540d81e070f81c0000e02414443e60107840501000910140d1800e03940d80040c0c0504200402a5 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 13604215 1250 13602965 13602971
    0x60c07031a010b1903060801020d09050105100510080403021504030e0f092206020c010207060c11030a020d08040203010b1207050102010608010209030d030903021002040b0409060503010b1f02070f0803030703 91
    0x1048518100320003030485110f00009071400141c0441180b011600c1d81520050544881012904440a001501707d4080c1c1c0d0600180200e942d051440c01c2d5070b806001890302064114084c003260302e42e0000410302c030728a42020411910350349001ca103081d0b400252114000411700c05c2c0410158480b0040c0c10004c000c45140b41000392107810404003000654a91046241c82d6020340010318a40c41102d0505004100050810075020541c40c03c1e070b800b4200458003242d1311070166109a4010141c18200c00e8564011400d00d407120380065075a4080e1003814080c000c0c244005421560b09400c072222030b8101624040c0c12070b02441e807180e590322080c007030603001d035080407000b05a404051094031410030004005207070040a05905500501c1c45020540c11030040d440b95104601103800180020300004185541e1249030004103000c6540c10380104c2e1203641018240f151030703034401184480c641e003401128201003206080507480d00e42158410b9103541300c845400a01c00001101440c03148815407014 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 13605465 1250 13604215 13604243
    0x4110a05040509060406050c070506100504060b1201180b030307060b011d0a0e07030905030301060503150405090307060b060c0706080405070e010305031b0106090509030702040e0303060d02090c09060c0703 90
    0x1040c0c0e0821503030f0b408a40e00a10005000c03503a1030b000303e40c00500c0194078600d0040c840d110141000e41c11203007450f00d140d06440c01c20486c00c1512584005104e030110803401c002c90742407104ca0102c010310803007080c0c0840f80c02c2421030075402d41c880040e1080041c2140d5a40038140380850241ca5444150b5001c9100b00d0469403468800e40d255010401000b440300a4480c104040202d90400150101003016030360303c42c00300000d004100a6000e01880d4aa45880b0b1800300c1da00000d80848444003402141440103105807070f5400415501d216070702100114400c880840400c0d0a0f019050709030107a841002000249240c04c0b50380700e03004030b01480948203400d4584c1104006a01d00384001040c5600c1000b1a20246484401c0a030100101c0c0e400411065038684ca0007081e81d40c240d80c40b080540000400c00118a4144a421018802e410103142903241480004440c445500ca02034003c445800004042c2300150b01202c014240c010602600c0b410414009565240b05000c2110052032091302 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 13606715 1250 13605465 13605469
    0x203060105010e06070605041e0516050307060807120e010c09050f06030426070507030c08150708070e010215040c03120203030405030307030207050c0a030516090b0a050919020304110a05 82
    0x20050050f00302815032481d284c03040e40c9040003864010802e8464944202c541a4034105882c12100d80c14007500081208150302d00441c001c84606034045882988054403c02c0907980100300d141d0722030014144030001c1458081c800015003c1d0060480080d445c000440740c07101c0d0018a043d054580584608410349442c6082c401c9d18031080c0d50150032600006400d148684004119041d016095040380d400c003111030390b40c80e1a0840e250011611002e0b0304a040c802c864003048085070700c842a210540003800d0004001d0115240941100c080140100a14600740d000f00f05110803074200700294441441d090504a150a0b6540001c44520000655501e840340c4000262801141c200024625584400a060b0000d600444086825006820340e81c2e48039910018050015402070024124460182d1100c020002c0c40350800103c103407504101500341d071030741000e040648074140c1d132403120f54840030180c82c0141c064a0509503064000000c00003084121a0103001d09041514494162503c0f901 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 13607965 1250 13606715 13606727
    0x5010e0108100b030c04021309060b0a0e040903080c0904020705120703090501020303010806010501080a060b030403030b09060307030503030414010b0a090614060301060c060f0b1003090c05030a0203030403060c050904020d09020306010501 104
    0x1c00544d1503484001054820720b8a81d0060009004812000c0e107190395410501c800c1d1078090340818156000801d00202c410741201780e001000b1001c40d0100a900c4241c1c2e00540102c0001c0d2100c080c000d80429844199100c0340e046440da241c2100403110b203036070402c15031b400c0c59100204c04c8000444c0e14000060650001040d20306807035540c80075008681c2020011941183c004104081c2e031a01e07620001640e0b0391400c01103010350f01a650109143c0492402d0124071507028100501a900c450b0f4104040b40d4048144c076005903000300100404010b5807081e0340585070940e043b55200a001000050ba90031940c03046080702d400d5690030801e015540108502c50009129880c00f09104040003400220142d110151219261200161240b031150100c3e00170340300d0b1200030000c6643c1e054054103000c00d03401c41900400c411001042e1102255000c01e46900551000405450311482ca4501407806041038500030034001e40700715180c100150a8030050011404140d0081c0108400450b081d48100 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 13609215 1250 13607965 13607981
    0x19050102130e16020327010201020d0603030509191a030402060c011d010c0302090604140a0b030a0209090109020304051905070b030c1c05060a150309080f0c070e0f060103090302030d05010e010810 86
    0x388900d015401d481d100140b030042e06c80680b41113550800c01f40c400350080348141b00255005c0d503507a5885402400c2400350789242c4114940301c0c00c460760300800111030001140900b12441c8030810b0746a49803840410094060141242101c0d402d081155850320a01c84541c00c428000e18000e010f12118001f06400324843c01002d0703a040602040b0900c030018042041311598230018180e10300550f5200303e840801d8109a40308002e05400003406000382c5042d102c03d90140c210001c0031482c42c1000d54846564041002c012003141c5907091203031050110500c4090001c10180d0540da03507c1c900802d0040742940f00448040c7c0c0780044a281507500c4280b441842c0c031600b0060040c0c9002c2d400c0203100c18800c0200603c0600f090384030620b00c00000e248101628800080c48d1180f41c603914a0a01c1500308621904480c06000100040140e04040e104075079803c500c080c02c0001d281140307418224154851191a0080c0a0800000141c40c100c0c40242c01d048802900542d000d124035108104280e960302 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 13610465 1250 13609215 13609237
    0x150a02030702060105060307050705061503010f0203010f030b1e01030b041a04030c061d030f13080a03080105040b0a090905070303030b060c030301090b0a17030306010201180519050102130e160203 86
    0x3e180144074509000c1c1c001c5401800c43d0518504008940d40c1d050702d84082201c0303880c0d9000070381107241020b080c2400340c085030808240080d81590b05012540c0d160380d0103440701405440210300859030b11514100009401903240c59038070101c3da101e0511051280098030221007185200d451000d1000010007014011075141d80d910030144055150390780a400346c56181c040301c14010300d181511100410042507103100142c02d0544803007000c4800c41c10010f103076001c10095041050110000b80d030000340f8074103440044030006103020810001c00d008078625000b8a001c84c0c980000102804000a05041120305c25501880940c8200c0140300140c040c000401e0102e90050006210418454015828280c4080e1112100541e6120840c00e100160b641c03051058000006000195a081c050440b0000c004804100c0444169a455566524041d21203444210180600042107000e404451a00ea050b0381c100c42290307120581c1f5a0005400e8494511348400d0000703c030146800070045d00c21101034 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 13611715 1250 13610465 13610473
    0x20a150b0906090907170705030d0302030115050706020f07080702040e030903030a030b0f06040b03040b090705010c0b0403020109081305091302100c0305040509010f0806060307210804030c030302150a02030702 92
    0x1441c0280b03d0030702d02c0034001c041103000c0d034840418a250941904007602c500f00f0001c107282d03440c20092504207001034080c481014010001409100c0b404100f2a4210034545003080c0c0e03640c2d060400d02d00178060100761411518000510700140010800600500c42c000c94082082d0420303001220350ba03114000846401d600144407101d041e034041c0e0b02410220001500388524400c40740b0004071558041e400502c0e800c040442800240303c4000341c825804602440184442403d100010380000c0f044c0714000d03c40d212000018003058030030340248610b0707a07020b030b6410303128030f00c40483c0c9501c2c103481d00800b4010810b101c00280d2605070f4210680307926801903c0b100300e040c0d140305c04450b4441c40101c20f406000003004001820380b2282c0d9254020500400315180c0e036810b10815a04014000d040305100307600c590024007410f1201d40040568140d044d402c0c64208040c1d250001071401580d00152890340340020010a05402043d1009820000005402d0355030f02c5210410032400192040401680 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 13612965 1250 13611715 13611721
    0xb0301140109020c03090a0b0703081003030207030b0c0c0105071d0f0609060f12091b060703080c03060109050414010e010f0e040206030414060a09110103091110030603020a0303020a150b09 83
    0x7003180c3c02056459803032015039140c0340d05e160105108207401d45c840c2d15659800076050b428194820303400c0e50041207518030100c04525603100256925a580005000312403600040783d00111400112407070b101144d8024001494022009013000908601b901095075200008260b1850300610070004824010701d840d0401800c841803100e5a080b50341e200e0803060040180b0900183e05d58259441041400c0042c80d41ca010341c032140000d00004d510560240750140f02c000c001a81200f016a070207012051900c1d00c85d0b071000c00407140141a50300c916040ba10704040f0182c00008516914180c0e42801c4903020b407640c1e11400c4a1001049219041802519002003401407511100842c0c0003402002c1c1c55480d01c9071014802d00701401070310400d0344165201d01c001e00300003060400310415082420108104c0030107440c1c03200280c01540301207201e9001c2e05101e80b8980e010303901680240d034000c0c3c2549008c50312403030081d548c3c0c2003028003610b146621449044012400e40940a40160007400d40403960f1 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 13614215 1250 13612965 13612979
    0x20a0c060e0607060c0219060b03100b03060a050403020705060403060203090c0303160303090204020d0e0105070f02030c07090506030f01090305040e010b0412120c06020a020a020f03030a0e0d081309050601030b03011401 96
    0x812008945406c5000c0c211241508143d040a13000b01c0394000c010005800c07155a00b01442c00681c4411403045600304220038602e5600401e280d54030803800d910105041c0d039145000c03030605240d500140d902480214007c418411142d0256216849500071590f00420100070580e9900075201500f011072020010080003911a4000000c800d03c064405400c00d1f9150000300700303940010741d070100d42d03030b540d50104109264064103060764642c19001840c5000502c4c1049600c400307aa01440c0880ca4482c4040360142e102004030400d102c04c04802042090b1442c60003c0440d4803c1c0701e190000e0040900210311290b81d80203c4088030f20199040391010496a180e5003032965508083e420303c40751034410004100c03107000410003072202c0d03400b500e200c1c5201d104000c03a00c0082e1400900a070300510982c0e00071a000140c50341110811078554039088a21710706918a0b1066242210a10442a200103400002d54000743e00990090320300b8000c408441d0141403c07180f842c848420200c0403e00104a18 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 13615465 1250 13614215 13614221
    0xa150204090606050901030c0309030827030f03040b0f0105030a03030c020a0c0b0d1107080d18050d0306031109040323070b0907090605031605090a1b020a0c060e060706 74
    0x101000140581095510800e01003107620541c040400306500190b001740569040c0b15040950103e410308101510540d140284000c80060141c06070403900007011011070106001258941c01c0c1c442166500d22040103c4c80320b64205441c111544c40c82c0c0b0000c1200c0c0f4242400e05810781d40f0142c001c0c05852a182c40c00c601400055070f500c42580200804900030690116110000d803d01ca4100c07981e030003000c9145011618045d0100454000500c07080c0d0020700030508560311009109004100c44801c0b1901d4080050991402041e900c5160341a0704499019042001107030f00842d038903800c40c40620288030352034004560060004603207400c0f40c2ca480b0f40d550381562015525494450820400303641c0d0200c0c2007401d96100e1582c2c1e00207034040000c01c605014580244c00d003034015020300d210311018001d5880c043e0080d40d105401840010f0848003450f030000540306003010084c0110f040c0060081d40f6010b200405603014a148030001c91003900035000800c2951015211928024060b140c80d801 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 13616715 1250 13615465 13615493
    0x2070305060c071a0f1504020c070302060c1f05090105160e040c11010204090203010e0112020105040b0d110f090405060a06140f0d05010e09010f1a0108060f031207020102070509090a 80
    0x1c00c0c40c021241e80c001c1000400c035903204a4800107511038608040031020b0f40b12031b80d08150740c800da0040056440d80200810b03800112075040c0c66050710b83c0c0a0b022041c4c01e210b0000c0c1c502c2c0080305c0f00800d0400c1803250360002801001c1070002004281c0303c0094400401c00c0c040d1026021410f8203031500203078101a44483c3c2d0000c414503144290049800001d030a82c2c0c05039100707050007038001c0010b1207800815080240182021102c2d403400162641c0040e0a40c0180d1088010b4550701003444c81c40704a0b079804c815684c0d0782001c941036480d40269003403d441e4100704150f0707004920702300c0011420f007003404040e0140c4030161203614603a0f0100e654a0314130382c41003030300003511103083c020640800c24031f0042901a01240004030300c2454615492400c40d40c070f51a1148581d4100700d10502c1040d04000c141001c1c0e9000e2a00c12640c0d680e65005ca1580c4100c1c54a19415100d948426404808003001418505100b40c0c2030395403c950b0f5404202d0030500a40340b512072a00802c25010000d8088404404 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 13617965 1250 13616715 13616723
    0x11100c021002010f0b0306010e0403051315091503110306060706090203011802130204060e060f0c060106080a060b0405090c0901020f010915050a0c0e06090f03010f0e06010602070305060c07 83
    0x44160140d6001c241031001c1d0301c0010300980c3d1a0000d1a24101d440d000c3d40802c52410340c014400c80d80351100004030200060303c0a824440300192031948071040c51090f0f40a09614204411b40c0e00c00010028403044d050b101c0c81003800d40941040155034464050259443d000300c4419085071101401c1010300c0d44007500480e2681c4e60781402000580702802410a0a01c800c40043c44288c1c0c10700501030b0000e006d00300708040d00d1040009200507a0007010200b03100b0410782d20151900300c1c95003141d016105041e5070a80038881e2000020b501c07680041c41034406c046019080c8081e1b99168410700700740c00b07107004281e800740b084000a0403040420000c0c0405d081c052040f030301041c00760718a03d401c44050703440a03105072954004e101c0d01d09059000711074000311f00c06010801d24284a000500e844203000b95544601d0002449101070f0b6904203c030780d1006030045c000c214403008040b01c03078010041030180b403001e80280340000880700e002040d500200c0e6080409084a583d41451070009503010200c221 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 13619215 1250 13617965 13617977
    0xc02010e030114010801050a05010602030a050403061d060406061401020c150a0e09010b090f010801061b02060d020d050103060b0303030103030206070e0d081b010605040b10080c09060c100b0307031110 88
    0x3c1107880240015600074204400001200d003002403040c800d9a00580000c001c0d07501c00c0064912031035001e000c8504517a0403000000b0003900080706084102d88901544803075200d420140000d2060540c440000c65030031301103c0240311500d000590701d4001c0e40440f181e0011020600b1520f81c2d500c000140004109482d00b0210000501c00103a414078080e00000030716039002c5220140c5080c401d41081412209081a800070740c5080002041440b14013944034140c05500307036107021902d43c0026180701c1d0404050564440444d03142203402071a09200a0710002d0801c0c8114209013004022281170341d4060b0301500c466a511002035a25400703400c121074228400081d810089004403001d48180e50500c2070040c18074080a8041e401c0d541d854009612580c50030a0001036590742c4001c106000c640d82c2030035201551441c8400d581402074600703840d048080010240d24960001c90040c0328503d200384208584401d07102403640c0e91016000c02899440032029030041c0b0b10b4031041c07040d02241c1a05d00a = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 13620465 1250 13619215 13619231
    0x1303030e07090212072d0f200c011701080304170709020706020a110d050306040b120d020c090a1407030f1503030306080c0d0b04030507020d0c0308040e0a09030c02010e0301 76
    0x2460880e446031801800f00c00d0010103000c41140d00c128204a1b0301c840c0700b44034401c03425240c0614090035640c400b1005000c3c3e0003030304103c52409440075040041014038182110000c001c040c6466690411351140010804050501c104640d260300724181c811203001142054140489210000081c02031202913108010300014900d6050004002240c440d6202603100c1d90203d03030107001003805480f10500c0360404110100043e502070283e86d400881185c01140041002d00030441c1c1d110300190301c62040c000c1c862004101c54000030381482504042e101315800d9518114601c00315549500c204030301800036804279034964440c0c0c000d6a50303428002d60000d0000c130390007159031501207a82d100324046a220b880801920f00c0900403071114503019140020385500c5070741e8500c0c4134240140014288a40440d2843c01d546408203070480c40c6070720103c901c14040d1a4207103903c1e29041032058804a15203240020440340c00c0d401666a00d0341d15413505401c0300440d81c01520700d038010755801f5800d59a16003071 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 13621715 1250 13620465 13620479
    0x903020f0d02010c090603020c0d0e04060315060302030c01090e0403050706060815040302010b0d020112020c070506121005041a0405150a060903021005031b03040302030904020d0b0909061303030e07 87
    0x40c0720000c01c51900002001400b200b406040342c1e41580c042d0050602c18004000d2007000456814a401c2c0c0524118003d54000c80008000b05029080600490440071250010044962245007980e0084003150000040c400044495a000f4090305e0a103c1651001c100000e010300080e184492086002145043d00c03031500d140742c80380c0c10701048224041c080c1840241030b028030401000d55802e91b4036a80d04115500007074600c0360070202e13078040242e0020f01da074100703d07040c00032001515000b000982c0d51586011202a105c2007500e81d03010406c0000d5000456140c14821030029103e501e80c8074408100c44c40800000b040c000700859100e002015880aa560b02c1046507400f8061540302e085002d4118018070400b192000f9000050020400910245100407000e966184141d10451075032561103140403415406400480b0360041c0c00442d2096405181d501308400503030007035803150300640c0c518562642d6a042a00c4003000100c0c503013060000f1920941000c100f07651520110340320303203a42e016 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 13622965 1250 13621715 13621723
    0x70308030403142803020408120705010608070b0304030e0a12120309061805011103072001020706050c0403050c2e0c020303070b070809070f0501030b04090b0108070914040b0601030903020f 83
    0x6800e0380303180030a00c2030141c80018200b03a00b01084c40b4034003181024280050180c4e101201c0b80306001c0b0020124902e02048401d4203c80302070024101543d03107072a519408201b050b04103550841c041404c031301005801d402c0c000300b11000c8a00000000368280440c0d00d9011160707414664500030545c6a4021030045509030061503284845600700741000091410000c2c00c441443d610303210340410810038004040d40c4202e4880d801b6005891003420300c002c1c0c2c40c3c0c0314024401c0000080c942800c04d810030034084289800b5000701d034000c6082d5101000428100411402c1e01568a907810128405592143c2c44040342890084d00504094600c0699a00028510781201c002256040700e0541080242503020748844d0f0400344a43c024208281811078030300105025000e514109945d450b44040655540d4202869403504400c20346e0176943c4448900c0e490300c0030781c0500115203081160403440c000e90011640d120704d40120354140e0603118940114058050080142c0851085800103588540240 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 13624215 1250 13622965 13622977
    0x71a0705010507021f0204030b06060307050c100b0a0503150c1c0905060402030d080c0f03040618060902090907031104050a0204030b0c0c061006020d11160f18020c07030803040314 79
    0x24005204001740f11040341041d12280c114411031310300501c800c10000303848018883e00070204981e0b2984950710040101d440340500400450030f4031480381840d6640c2d03150352110502e254240c603031038006500d9000341070f580c1140100700440100003d0029104803841c102500f004200006410422207240d40c5c51310039135100400980d480e80010f41888210300d0108100c6031700e220b071400c00040314a0004840b0302c490103944280342100600000140030403202e54454501005a02d5000300018050308104004202e0b49400703d005010034800b1840728400060204101c0364480303054400394050720184130203000080c0404142d943c090102000050760740484610664071000d14a032201c5404400b2882d00e140079103015400240c20700b0a016145c2e0201c1e04c00101566410032401080f8241000c514040d0a9180424054403a42000c40c40d40e507100f0040d402c035011503582010171480c0c035003c030b02203104e10440c04000c0d0340500010000202c2d200045c65100703010b41040001d41104052804a59002d0 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 13625465 1250 13624215 13624217
    0x30210020a02031206041418100e03030702070f120f08070507030318050603010e0c07030c02031c0e10020a03080403180b04030303180203031605030d06060f090b0a02071a0705010507 80
    0x1084020030a4a10044c0c00c1d8486422501400720300329208807002c00030300240550340071081792255003a1060041020115141c05840c04000b4152102a420307200c2d0030942e403010050040b4080010069903001041064a280c0120a0b4030750499640b502c2001117017001c2103c1d6440c0074040c0d00c01144080c040c100003103000e511102041035001c10f90001c20100d40d00b115100340000d0006000e401d00b1051000c1c1d0189415144550b5660346040c20fa460040043c002541132140c500c26510040082c2c001c031400c10700b41d0300c4008000d0a040e040080304100020b07000010ba02440900e000301e8418440715400c240030b13042071248402d962806251403142c1d600500403d110020b0100200350f81032240c40700e4144804241d84a242c2c895000a449104010854290205c116451070600000f80119024443c1550040001e240c0e189000340c4002c01c0010f102d408901c101000007540f80f001c900711260401e0a40c00f801100e403c2c801009400200c0d800c40c500805018046600003480901c11107000e1011 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 13626715 1250 13625465 13625467
    0xa090f0902030d0906020a0b15090a022101030f034b030b0a030b1503150402040b0a0e19020708070515010f0e0402121204030f0c0b0c03090d030210020a0203 69
    0x300c0c01410f00d042c1c900d40d100002c001000100300b00d010760101e50800001c2d480041040f241d00c1e81248948414060940d4951010b0000140406035509030700030180d0b12140340d480202042042e008c200c0c814000d20010b001250131456040001e4410703242c01800c0d14417541c00707104641d10140d4000980d039001180c40c1c44506180050b02c000c0c0002c800740301042d200c0f480c080c002612141302082401881e0700c002400101da00021841c113111246141c081d1000203000c80700c0c90340728114000c0294505039002d07401140340402889150a01854000c160f60f40510100000c2d162500c81c1c4042c4031100410f2164280d003401303441d00107404400109820350080004161000d0300700d006490030f20701030b88140360010000c4800c0040c1c503c040e00702684180c040721044440e44010800e942048195145c440003c034000401100b00051a14148511806528221a07882c2c81e09440901c0c3d100300300350406980d0050000512902d00750003201c80d124030920541e013041d442d198940050380c00000c4944c0250704 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 13627965 1250 13626715 13626731
    0x60f04020301110405011e021903030504020405010b0313030f09030206040801090308010f06020c0402030606120103081c050606030f090a06020c030406081005090103080a050f07060506010206060406150c020a090f 93
    0x140901800341089030003a5611320b89854900003074400e03040f04030500b2007548071805c40c16025000340142c981c0c011103040655920ba442d490000d0080108660803480b070751034240040341c001055000c3e40e2040c10350902d95250f0030a65281500d0207201041d6240800c0800780d808001601c03100c0240009140c540004109041680707409004014140c01200a80f8000c81041110360b41c002100324000c3c20944005a03603441c0e8070046150361041003a80c001080d0303003400010401040c00f0041124040d007511141c000380d040354020302174071300a46060f54000c6007031022540c0c0e100ca4107005a00910800c0c00c07140240580d5a91f030003641c1141c0401407003904042010000160080e018a9104101110715413059090000161200006000c00380c00c1302c01c08140180c0207402102203809807030a5001940d00c031809450290003030303d41200c1d074034010701401c80850210b06041c011032040c1c8012102c602480941c0000480d45004201c50503a4001b1034a840007501403a0380c0f285124542840e400420048 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 13629215 1250 13627965 13627969
    0x604050a0c0203040504020c0c04021909080109030e040b0402070510020301090e0708030409021b030403060603110603060d0312021b0109020306070206070806060304080f0307030902010311040b070609020a08060f0402 95
    0x50801001160054205a00c200006034048111000da850860f0700503190000300d043c2c0d81c034088000b0500ca402038800a00304981c1144080c81d04020107580d80c501c0780903622002c0c841d003039410125004010803c3c250212950f0700d02a0021000d044015100605108480d12382918040404401205040c0c0c00401400304020501800301d404007040010548945401c007103581c0d0b0311440c4904041d03654086040000d80089003162505962004201c075207580c4c0741c1c10711900804042c4000c03112024090b000000310b09181040d2403007020010205140a00c440e1029a2480d50161401c1c003242e03820802c044004603540c1c5000788580000000159980e040d02c141031500c1405440c550540d4003030820842c80f0b44c1d2100205500c200107440440c2ca0f0340b12450300c03040c0c1c1d009a01c0050b040c5000801003003929603156005412480c001d0341d040c04030391501d4501c14000c1c03050b4081c581d0111f10421404003c00d00303a030401040984068207105032181d482c40c4031800c10740141d50b40c10120140038240004d40c = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 13630465 1250 13629215 13629221
    0x80a02090d2a0503010903080411031c03050907060905010203070201030b0a0b04090f0c02010b0603011e0504021207080705041202091b0309060114060315011101060b16020102070902120606130911030604 89
    0x3c1c15041d40200701c6078116440280050600900050280d0404d0306c00100c03640301482a08414030f0114214450240000c00180c043c100c11140364655128141c00041c06510400300c1c1ca0485006070091464142107400440c007a1181e101c10a400c0019a103000440c980404000e00080ca0121000203071021a0307000c14040d5180c042d029821603040c4082c1c0c010b1907450f4000c490444e211a02d0017010340c00686c11040b003417601a4416076006202188150110140302840b03841603c2d140e5070100c5039510280c0a0b00c0500450085041411805602d80018140210351982000c0880922400356050000c1140c581c2d00465107100240c0242c0010009030108000c4140c81c07507800c664041c207510f0808040d508804a0f130308100d041004540418000303e01c00e5014001524001001d15520842c00018070a5004220000c034010f11900d4000641c40c2001e20036500251400d44190040c0d403100c03420008a130b00300f01c0ea401d501c4500c0000016940e1542d204404c3c021410452040c1c481c64418100412 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 13631715 1250 13630465 13630469
    0x7030b0312090609090a0e030310030218010609180e03040b0c12040b12060609040603050d0906090819031e0207030201080903030f040305030a060e10090e0706080a02090d2a 76
    0x140d074040c4114141a6580c0f0182c812200b815907162003240c0ea1010550080d0014500c0d19640340000001c0c855640c4101d007410065a00903101e2a01c80c650040403068070000903c21800020300307004040c84401561080c0c070440c519000c8010136240d80c1da207a0241594401c4c1d125224248000034494561070341807040001c1d40c01e03114a0181002d11340514010580305501c5170700005150000001c0176582c41100b95045008042c10801c280781d1646009030703403141144031060208005540001d034082c0304801000544800d10044e015045142c600d42445443c074010403003d00030314041c241c203034501d00702c681c8a0300c09090780184129442c600026181d050054000c25981d0810800c101d4009404442c0c03640255142c6012556030342c400340d422008140a8106001608190040c0181e80941034813143c10307144038100410803003209003000c9954801034850000030a860780002035280b807103a40900b40340040038002d002420805d80c1c0c1c1c3c103401d03003186528841c0d690f201c403250011000c9082c04800 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 13632965 1250 13631715 13631743
    0x90b03030a020d0e01050708030a0f0b060703050d09050f0d03050708060d0b04110a0b0c070306050c0c06070507020112020309010903020706020d0c17040302030703050a03120b0a0b0d060e07030b03 86
    0x11500c0c907400e10007522180024404014486030a80e0700007181d10460448121580110304180c40741000c2c41e0720780161030640b14000301c050904a4441030b62520004071102c580e0705441c3c1a24050f410003000d0003505410009507a10700805600c5089203000740b1405080030403580d0000b955140c0710718081c107240c101400143c042c0c0c0b94800018001a00050450341158103d01c00641f409250f0000400b03085d6070341c21031040540040b880340350300a0000b4140c4260b0344100014850382d80d401000c040076019400f10b5240540c400004584203c7c025801020a1070040c03626410301c0194442c074905a90042ea40e507002e5a540e8404e40c418154144554070107003d0910180c5582c00148100924002141c80d01031702f0030440030504010b001e00142140c00031a40502540c811591741c3c1000794443d108060240c022a07081c050a60b000c001c0d5110740801e044000b04511100303410312104a089401200082e80c0c0d40c0d80c1c542c2c5c081030f07500b100b588440c4100065034005c00c1c4011650281803c0c81245c80e0540d07 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 13634215 1250 13632965 13632967
    0x30a0206161209050109170703060e01091a09071203030902030604030801080c010c110103020f070501060312110606030d08090a020405090609010f02030606090d021f050301030c0e0402090a0c180b04090b0303 91
    0x13000c640e070700c00308400c1228504e8074004a031000c900b50403402d00c4559031008010341d2410440382c03001001074200c01e0303540e4002c400100b0100e8801c8105d11040c0d0013100c3d410b0541e000f80c0410322582c60045040b03a4618001d02c1c0004810701c581c3d020916110055034280c0210301c03c0801000061410040301203c8036084c0f90103403651040755591f11000100c00034040c140740c1c01041d10501029003006440c480c0ba04207009000c0035a403030614880041e1200380300303400100c030001e000c80d02ea400010b002d406000081c0045c400c40b01024021a8144009441c1013401e0007050043d0001d80d813a4003580d801600c82e50061320b01401c1c1401c4031400c480003200180d00450040c0f00704841552030200350b402d5000103543c020040c2c1201e10021b05e090061078151007030000e0b4012901c21540d48000558181da1080d51a041c000b500c500b45100301150494009600240c0d18001611f01a4141c1140081003542e00342071105c3d294003244a0b582e50034942010401c4900810200102d00c6240030309003e44805401031 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 13635465 1250 13634215 13634219
    0x4020907050a022a03030403120f110a06110d0f06060e0a080a080703020312090d030605040203130201031d0d050d15030f0305030c120106030b0102010b15041202030a0206161209 78
    0x81c0d02c0300300b95042035141084c001403014000d004141d14541121008080e02ea0701e40d100e00d480015102d01c0030050340090f603038105001038a4003d80d640740c0000c0c03c0e030008004a22181c0e032801c001c2d005c03081d8218135004060040b014001d40ca03016462030114042c0d000300b8a5410110010030440341c0c0c484043c4a840200c10401005801103000711245400101140e40e810850809a03c0d43c81100002d00300380785d91004004d00b0441c0455248031900c0076580078414183e4403801c00c03040e030105445101128000c0248180158004d60200c403c04511526000b40c043c40641410704042840742040082440007803840c294040b28030032a500c92161416030403101d421902c4960200d0b8000c40c0003418000e000010854045100c001c0c4ca00220314404105225030311181c00401274010910550b000d503081000e90029442d0084d840340401c0340c000881401c1c58074144440c070b020b55440d042680c05000324035100000da15500014424083c011091200481c203034036141321404865161403041003441300302 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 13636715 1250 13635465 13635467
    0x20011202130608130f03021513031b0201030b0405090c0414090604030c03050702030601180507030b0306060d08070b0a0203010f0801060e070c11031c020106050301020418050405070e0405010504020907050a 90
    0x1c03550a0707414500d4105003039a2413203098015041820000b410a0300c0c0d120b0048101940055241c6070825030480207c034039265040803241c0e20710400381c0100460270003001d40740c20404520300d40e0303c0c00c1d005140225032440004d004c10115402601c0134002c03a0000c1d01d4410180c20940510810f4807040710020b42d0b50703d0301c0014151036a2001d800181040040203101d018144500d082c1c0e10b800350020203890b034550b92000200403500002130002c1e030083c240380c0001c0d5858000d00c280070501c840580580741f156104000c1114103d20303400704513190402440f82e40085900508400d2007101070010046e9254100042241c6440c140e6004100e260306210b0103012030101854070b40d40005881c246000c0f110007601d801c0b00750508119100d0b030984504003115401c44540c580000d84d803d0b01d50002c1100315151811705003030384107034003070130941c100104c600121000f00c50348103650190250701943d00c810f4552858a80b880e809850a41c2e850391204203020641c40d003184003a4211002e0b0511514203249903030 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 13637965 1250 13636715 13636747
    0x2060108011d07060516060216110609090f07020703050102030901060302030c030615011223060f0a0302010806090915010609061403070c11011e0302030f0702060103050a080a03060320011202 84
    0x24034401c21002003030f002004040e2501b00000d0350b5228400795121410768101100d400000d0b0f1064446009101c448041030804108550740510041c1a0440642e41d40d41501c1d045100503082604512501c10000f010070028409980601440790000c203d6501e180101454505148002403003070700500203001c2c4070708800a0039001c2c40380a0038058094900e182c83c17000102081c0e45034149400b091410801c0409441014a00c51070b0125000d500754600310061001c2e094290100070f000c00c4010002c22207605c0c3c60341c03189920054a204842c10942c01e20302c43d0240726800c1e400103003c907010f44000e00c036103070700b114505500c181918030540c19844c186400424014120b040500780a2032080302c0c2103180d20805c031000d100440c19180c40d0808100b000000d00035407044610618102030000031400c0d45201048040c101c9801c04001c1804107426107443c091030b80000d00107024140d45031000000500000c0f44040c0c00c030882030f505100301c074101c00050209040b000010000b284100a42414141945 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 13639215 1250 13637965 13637969
    0x6110303010608060103150e040606080d0e010503181204092009120705100e09010f030f151401030c030302060f0c0a050a0302040b04030804050307080604080403060b01120c02060108011d07 83
    0x1142503c042c0d140c0e20016001028a10034805c1c600034800c0b03010552840544042d4010780c4906810070050307565200850b102c0303040c80d00ea10001407001d4580d600e01c1d0f22440265400902c004220550081a0741406240c044140c041d5000c045001c941040320505c1c030320030070800c6041d515401c0340551070f03035040c1002031195020b240d00c0340321826040d1180e660200305000c0071b010301030000c1030000c610003405003407200b02012851160451900116483c003109180c0e900300d80d44806c200340c441070156940c0301c0b51210003500002c510303940e12809030b6034030b40101c2e1a0300a50007540110a40d9080d4100241001d000612580c8041c4140050051a204d010201c031103040803807600b56242d110003541100a4880da074084100018049004420700c030100b4000c0c001c03681c0490444503c1c0e07642e0700d01c42d070312100d040340c010b407c0b02c07001e2100f0004190203810906913400145015400485183c6d408001c0310f280440441c0181d02820051220f150244610402207400f586a0b10750684000b03800340d80c0380740e81c3c = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 13640465 1250 13639215 13639217
    0x4020901050d0602120a050a06090b060a0302160606060c0606090506090c030c04080a05010c091a0409020904020405040513030f02150a27050604051009050a03210e01060807061103030106 82
    0x41010302c1c20701c151541034484c80240b543e4001d0040c14200c1049000c0c3c5001d031841916540751010024032290644100c00340c0c0900605900e042100a03d8203074000e4000c07484269000141c0300c00c1c1c00008907144900b8015120a4403101d4240e9800d0402c0411142c0540010342c002c1d24000c01d0080603a00d10146a6201e403035054602e40ea0b94807116140854022540259190721502404204003e410b4100b00a00580350b034075070303100c0b96850380001d4502402c810032000744a0204404c0c844d41442d0b4000340740384c1c01c01400c00b601e8190b513880800c0c01c41d00c2c01c5a03080700641a82c0c0c501810598004006039040b05c1c135100030402500d8500c400c0014001c040d04000b002c95580480141c0966030127468204aa08844080710001c03d50521507180e040840e01180e40780260a003044108210b03204840790340c0d0300440140503580c00e1350b800762001001545900e0075075010811811540d055070160b00701c2100400004110f652606c40c81500d450602d401c42d00a01440300c0b800000e001000064038110381c46e03 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 13641715 1250 13640465 13640479
    0x20904080405030111072109030303020922090b01050402040506090f0307030c0e040c050a0605070609020102101a151216090801090308070f020a0c0b130504020301080607020609060402090105 84
    0x980c034000c1014440d507401550594202460003580c0128080038040c186d0196108084c4207007681d88208150780c01c01c050700b003c50811041032022030301c282e0191801c000040c000d800000303c0742840c0451210603d1840d54095242d00780c101c00c100e220ba440c01e006040694003507003841e00308070029141c0c1c054a580540100e1800008144e59070701040904015500581000d060035150a03010441c2641200d003900e4983d203172000000d840c1010140201186d140341ea400e420b000701035031880080c000422003079045114030700038003061000d03d1050400078990440584444d02003582884840580c3c000d620b18090341c1401864410141152100e520402c41d01c1d00c451260b50501d070540b0018059007202d8180c0d0300e800c42010030103400520060046000ea20342c0e41c100c20460030200d03524074600c403000700304000c94101049440010005822808040c402c3e840b03c0c01c0e06c0b0030101e012030300260700000030b0f940454140704906805000280e08404010702420b02441c3c15000f140702c026040c0b003214043c2e10 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 13642965 1250 13641715 13641721
    0x3030c0d02070b0106030b0a1a03070c03020f0f010b01090503010902180403050708030c04060905032103070203040803070c090501050604030f1e06020a0f020f01060e060405040501091403040603050f090a0209 91
    0x2032a8102c840e050380c81220f0701102c0d40c482d6001001041c205003007500840c1546008a903001c490405422410b0b95014400d1941d41c840c1800c5944082c400c0e02103007944144034803150b0501c000d014020080b1506400045ea0316244000180000c11700e0303100c076009034074011800e009a00c03510707808443c2e42608414001c254480746800ca5040c480c45c04041d00c4114040140b04540d82008010303c00c41d403c554034801007540342c3d0201a00d03400755410800003021100c0c00f003c070703000c00791020790750068490050300e060075604c007000ea08540c030031502140d40201c44e00c0c0c140002c250610805000d400150344a41c142404d5039640241481031200207170a04503c4170110000e51441040500ca1660005003951034810507000545050100c8120070301501822840c00e041e054148200822201908030140e00c54584109200003841d01500941e11307552101c0d00500850240301c1010886000d0900030b5541c2c80ca05040242280da000d00716007858081403060007120500005d6034000c094045a260010751 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 13644215 1250 13642965 13642987
    0x50d02010c050304030f050d08010810050601140705010504061506020d050d02090a08060402040e1920090108031e040b0f1b0106080f1009020d0b0403121104050111010501050303030c 80
    0x2022144004010f844000303400700400c504028081d125a2040c0c040710b110300c680303400075a181d417400d000b1034010740c0c480006815229115000b06420400604000c0c5120700e800740d00709001d0344030b040f098545a4681013400100880c030704c6110030201d034050340511080e00f00b5800075101d040050180040200124640c0558000e99040b5182c19400412039120b4554030039495032182411581a4455850401c50300310354030010078001a00100c007001c1106c0744500b5950a104c8104000070340d4000301c0400d01083c0740fa100ea81c81c0c6806003905400a40d1140390140c03020302e0b42d8401001032164002c050108000c4644a0030645103400c85402c203003502e0381080314181d1107108140842c00070b10742c00c00390300188440c000320b03176400721003c1713141503521200c0c4400b024802c0d5051210003d40103032102c056180841c060824013500113109141c40929a160312030540b080c2e07940080b00016651000500b00010b44c2c01c640c440c1d00e80760700f0344000d000342c0d890040081e4480c0402410000525270001c0d80c441d0310 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 13645465 1250 13644215 13644227
    0x6070501060801021b0d03050f1f1203050c06070f2307020d060209150c0d0e060d02040e060f03011509020a09030503040902030109062106020702060c06040b070801061404050d0201 79
    0xd0000c68000b1900c414001049030a1600251001c55171401101150072455119005040c422800f00a250780360791188003004a58101e0006040d0303510314404030100c0ca40301940461003005000b036440da40c58003125a1024203004018000c10700b0322041c030b80c1103404150071049050b510480c2c2102c206081041040c6803c0d54450700c2e01c001e40c0007021074490340401c4495406032034042019600340b4022400b0010180c0386120b09140010380c1d90001c00300c0701c4201e07c1800c400c0b00c00c0c2c401528050a1200c2911140107903001500402d80c515802801c00410707042424002041c3d0104900034440c840080350701039101c00700c07409120316854000070000c482e640289070b1040150751040849550342e554644100080d042801881c94980c2421400550030b100602002401050702883c40300500090352460025440708800301d800c060140220320a401c8140100c074852402207403018031a240c40c040082900c00160441706c14051001c9048400000e403000340c0d01551000c1d1030395000341c015800140c800e = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 13646715 1250 13645465 13645469
    0x60b04060509070207090b030f0309100504030b0103060902010e062104110d03020c030c04110a08100506070b0402100305160e0619050409060501020a030f0e041d0c01091a04050607050106 82
    0x2041d42c1d0002d1001059001910070200c2c0d40070102001018002810540c030f42140b020b00b40c5803076205210001f81894614541451070303016080c201c2c5081c1e504d556000420310240d10541f2500c1d83d5200600540d600700160101820048030120300d4003000c00407100b030421400008201501d0340d940003c08001021b00800004d14006040c40340d110f65a02d0001e56a40340315603001d0003401043c83d03d8015040501800d40e00c091022445400c0240c82c10044070740e41d80040c05200854040c550000d00c54482c1c0d4014600c20380950102c070480d2901d40180b11354507115407050701c101480c080400c1458406080c0007140e005143c90944902458000081c01a010f94800307030a22900d030aa0306680b09800400a01c11192403440c14800c80c2d5481d4016a21404009000b0380803034104045103480b1881010618105e00001304005444c0704038a01380f900803070309003807500e00c3c50380490304080503981c0048807440100b5400c0e6908442c0c00031031071003180c18041c500c2a58041c076070104d1000c04004080d008500 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 13647965 1250 13646715 13646719
    0x150e130b04060509250501180308040e10090609050a0c0c02060d0c0509040f050603071703030a0e0a0b07050d0b03030412110607051203010302131401060518031608120403050a060b040605 82
    0x940d4240880715001c2c2501c9481b03101c1c04144001c4c0003400944030400198100c80d00040c1040c1040e01e0030f02c40e050500310041030071007001c2c040c0502180088880c46182c02400e40b40c000006d0390b03c1d180b601c05c42150b00c040d6440d400e0002c401c401c0320043e9aa003003118045210540c012400a51001c401e41c0c5501170b5150850703100b828115842c090140b980d106512501044040343c1d141c0380c1d01e008003143c01510802849054104000017a0f0202d45a080744c400c0c06d802000300c0e07644d00400d40f11003120740230a55890f0002400001d00081d110141d005070419003604501440c9458645000c040440c441c2e01e0000b840035441640c140125950b0f2000d9814254001d01651801c800812641d40e070b540c42400104d125000d09400c00541890034130460141102c0344402e0389090342042000d81c3c060304942909c54031006501001324403a141808106032540141d03110065513030400041c5400e0900d00300d040e04810b8404d00081011880c0090441c1da01038202c1d078001072010000001c2000b502c1b01c0d800540d = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 13649215 1250 13647965 13648003
    0x81303120f09050303040c12030504030f020105070f0c080c0a0e150d0f03030c08070302090102061f150801090b03010e07060509131d0607020c03030901050d020409150e130b04060509 80
    0x30b0510101000852140c1e114000c0064019100c00644801c150410340180010340140030510002d00310101c0603400c20b00504003035003403030081c0c0e0700d541c4000524101203a4490607000108a401c2c8100300900c9981809c8070b841d10528140b80340500644001800550300e201e540322140c2003600c0d04450a003445801400012180e1034904001e400307030158440c00d100180d15000026040d074070910075541201e005070701500c11511807503035105d8524081100c0b00c009021310301000400581000030b05c1c00d00040f94544803950b40c500405101124688003c0c00c0c000d9040041200100002052140c00c0c0e648506040c1c0d147e44051010803044000c0c15a182104c0d403400350f4040251036643c031000580311484003290b0195582c504100c0c0c13507100c042c0f15240c259205200f07209840d8007076006480c0040080c6030040c141940e8020420541368134883d0300204e1820002c040c001900700c01c01003a880700020f03507255000c0c25140d0302c16041032001840502440d60741e50208507058014800401c08501e99100c3e4 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 13650465 1250 13649215 13649231
    0x30509060d0c02030301080606091003020f01020c06160b09031305060307020f030406090905060a050102120a050c060112050f030a0c0201030b0103020d0c110f011a0603041a0705040905010501081303120f 89
    0xe0350313030f500a02034050107202c0c43e00042d019180202e240c03403152a90102002241d0b103103070b081c0038118964040190540c02100001285500d4480c003401e200200c1401004000d070072420402c1d00708402900c004915002000400d0002410b0180d1800b00e44094502c00d603665a140d80490401c00d0404440702c403800002400076080b54000822401e403030103207808000c661141d0b420018503019034481c03203025070002113a104414103450003134651440242095498040711002c09414142c00343c002c1c00c1000b2044c4016000d00008009035003480d071002000314a0404000005011100f01c450001e0404d5250112070750264440d8050700c1e040000e4203400c3c04080030510028090420b60340f04140540f28031120300d503104005014041080c0b00c12900620401e440c20248203039030f0b00050064580d0102d050382c0100c60801a6000ca00c502d04aa07125a10343e4205840c5005603401a0720442c10000d41b0018001c007030810b0b0b80315080c80c540c54100401244621303c1454083c0c54909102a0b08500d01914 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 13651715 1250 13650465 13650467
    0x30d050408030604050105041802040c03060b07081e0c060402061308010509010903030b01090308090f04090507270603050309011206080d021b09010b2704050c120702070501020a030509060d0c 84
    0x14500034002244e0a00c410303030702c60302840119101000303d842d07008100c608800c00740c207182e070000101900518010840e603449a50f0f20b07229604c200011100600c0000d081281d5443c601110380510341440c2185103084030300f102d000d955101c080e1019106850020b207003002a0050034000005010810086c007203450545103c1d4002c0c0030005058020030f0030301000111940c829079018090740d070310008240c18003c1032000d001510150041c0304d0b800568445c0008080b4208100420090002107041400f0300c1074900b20340341740c0c24461035541240e410301e00e05100245010042d16050282031a11a07140c0c1c190078124000390079a80d02030600b41c0585408078000e1a070201d220481d0305050000760840010701401d000440f80244200b5280e003000723012242e51640c00519074040c0039498405140134200410004045480c203942c000c10030b80001403049103600c4201d00d40350b0b0000c60fa0019004403480c00002070b407100b406040c02401c1000000e813211459071a0302c2501d4480d40c40e25030070400c602030208 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 13652965 1250 13651715 13651717
    0x3061c1202060f0108100504020301020708070b0118060e0109090f020a060e01080c03070c081308010c09050f040504030206150a0e010305060106080a020f090f030a0f11010e040e07050f0102030d050408 88
    0x40c48014015600000c8101118615480c100c4a4100041801508040880c4004c2c9000b62040740c1c595001c20544010a6a07a0040d10b00540551108561540750000c03800c09526400200060181011010071080b1149070340c1a044400d010f6010410132071358a0040104031401134000d40c01809900089070071641700c00c0e4109118000e8039a02500d4035440d40d0521507000450b02c51000445003900500005c11220180801c00d82003421603218030340322811582540c200b00551000034443d24010091403901541c40103e0000544082200d8106510000d495410051000130001c07080c0182010f02e403101e0a82d2001054000580a29940c4a2400d19240c0200780309030400110024040341484080f8800c40ea000f4928828891400c0fa4001c14021008101c0c1c0c03800303515010742210303039000c2404100100142c9100c1c03816960b03410313840700005d02840181e00032030f0700541c94000301001e4080e0008403541900c4c17044070400007403900e20300100d10b540300352044200a11b003010203000070014810 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 13654215 1250 13652965 13652993
    0x130305031902010b10180807090f0b010513060e0303040518040605091204030201180b0a030c1805060f07050a081206100507021f0504090c0903020307060509030304030803061c 77
    0x100c00c5a002010000880c280c8110910441c5e1080828242040d5203000d804c40b55403564891144010f030640d95155907082c00300355030181103035a403941e210461094440c403882882440034201507007000e6010040c0702c24059a401540c050110308082950356580030002e640052400403d003000d80e2203d2a5440011b580644044a02d54100008100c6450003c070340304a0401c10340c21500e003001d1030f5400446442c0040e01600d81541c80c03c04c00803800d022080000c01000c1e2040e1000b08210080d84d0006001c0e061041c14141c00d214059402c3c025581c03540120f030130500f425054191140802d08000d030508519444c010140303080041c4e00100490146000c5100b00c208494840d0602544071040c1da142c85541002035105403040c0f0419491380c0c825503108068080742c9003242c1481e444110f0f800c1151080480c0f10003142080400304118a4100f007140c000e0700c3c807441c3c01802c0c40205408656079001790300000309900e40200000b11503440384203a518003450005051a0359903024140303001c800c0c0502e = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 13655465 1250 13654215 13654237
    0x30305040e0108070608040f06021204030c05100c050405040b040b030303041b0801020f0a120605120f01050109060b09060703030b040216020120030d1a0904030206070912030203030402060f13030503 87
    0x71000003c110b200803508004036805070301c41401070b5403599100d10246a44071412101d1590030b00090b03640804030744055200310300c00d403144105026a03040007032510348504e582995450415140d00079030f0f584582600c044440985020072080c0700c040015000d0410916a99010b11001c030801003407100c02c4101c0014551420b0b00d00c140c4a85400c0c61078240d03c2411780c07001c4103500030048500c0091041c041340e01521000707100041d40136212400120b0b003900303528420445921004038503140d02c400384907190041c5241901040440d00e04105a0f03814028441201d12404000c1059020325000303800c07008100c20b00510171552680c424480341600c494000b402c0e40015546072302c544d45031005a1038080703c903041c90025070406271966051406443d400564881007406907030303030414503214110054007880c469005081d06150818000784135941c241e000d5201c11050450b000040703500402101e4015030141c5005550f00f41411010070f040c891000d482c0307002540c00100109020022028204803000c0b = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 13656715 1250 13655465 13655489
    0x2030a060515040302030a140f010c030b010306120b010302040c12060801200702151602040908030106020d1701090b0f030a1a0601050f040506030901090c080c01020601050105070b0a0b01030e030403030504 90
    0x1180b1000000d6000c0c6001c000d41607071003c600714010410003c00c030a070711207040c3c04450040c054034400e2825103030304034000b50201b0b8030340c41601000d40c1c2601903040070f04038100c62540c400da22070300c403d8004101844064000c070340d20725420208910942c10709141c1400180c3c1444401da840210303030b000384100380c642118280500360b4503510140c0310781101d9155030001d2540c2e542d1113001800760b0007940a0880681d22a0444000d20016121030040b9245075004801040d01e0790f140c164040e0130a207004a4480401c508049420a9810080c104505584603400006046125240801c803002084100e40368544694a0b010040240441100040ea0250040501552601c1e00152402e000307041d0750b038107210001c0c001480981841d002451740041d181c4004980c000481d1074070034a4a1a41e040200144c006020420b00e81d601042514010842841d02d10306e002140e881c0c4000c107070b030041c02c2c15103581c2e22847e009006a200790001c01d07618182d84250390390359540c1d1034058201d500521508842c0d0f00c03 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 13657965 1250 13656715 13656739
    0x11070f0f0203060c09101103040503010603080706050105060301180b0a0e0109020d0c0201060f030308131a070207060c0b060f0310020309070602010e030f1204060e072705070905060a030f02030a0605 87
    0x200c008169201205d01900003a10f02003103200c151510101c45824065a10050200040e965400d00903040114007494216030b40740b03c40e044c484203458050300f0590042e402000100420461030b1040e1150040041d4009002c1100c04001030b8400b40561018070b0340b503180320000c2036201036580100048807070074500300100070000d401079090300c06502c07070030402c11070a01c02080441d0003004a954032041414449200548540d10340341068402c100b43c40e080c452107010080126010020719010b00f02a0814900d42919503840b486003050040032640508014001e041068404000c42c40e000810740b07034195264980280356954904403482694019803c0114618030040c0210441e03601482059515180c000425070310707410500d000d801218104d580d2031482807280024072944001e062101404038440358003040d00b4800164512080c2c145a14240c180180d007600002000126101075440640711011804c09030000e003a04001814142c2c000000c001046850354407030030561b44201d0312a61046 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 13659215 1250 13657965 13657981
    0xe09060a0620011404030201020712030b21010e06070503060406060804050601030b0603160803030a0f1802010e040b0a0e0906070504060207050603040206090616060e011e11070f0f020306 82
    0x800d6600c688030204145007030704409044a003030b050410040100010444034130a2a005250070720444050780141d6012801c0c80400a035500c00f590713502030914080c050224440300041e1001c00800402404a081c100301c440c90080a412009071618500103490451401e007001514a41c000c8405a100d14a84000803624074001c2c459540995002001424035030300350f41e0380502902000e4411540340c444c1040c8106400c0e8a4101500034007440c001440e200e05006810005440709031768481003039401d144003481c60b80c11600780700c242d86409103040101d000000e40418024000142c0141d04100100700216905054254041c054041300003100c15681d908082241c040c026405800d0060f0809142040780c1c5c1303040c0d0090341d0007034001020f6525103103503c000902254803ea0002c0e40d001d03900381010f02445140c0c4202100540018002d1040d41c50300d44c005503403809243c0c0060300699613a01102800300005023520002c544c0504000324043c41418a014190780708201248a48281c0300050401 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 13660465 1250 13659215 13659229
    0x60708010f050d0506130201021c0306060305070509180411060c0304030b0f040b0103030305090309060304060509070f0605160c09090515060103060609050108071101110a020c06030402010203070209040507030803070e0906 97
    0x40d50400054202c50701c2e928886c4c083c3c010024816811442041c540d109001c0d000c44001125900c00d880005160b072501ea0054160350008107240248481400f9010858413a003410800b80d400f05072071228160307290700d0003100e046900700030150801d6000c0b4200b241f010f1300100800aa82c00741203903144c1030385c450381d886201140449006000000f15801000009d00075000260031220b44001d0b2810320101c2400306413603400071507040c1e8001b0b0300d942c18032811040622030f1001400d0501c18811a4500f04980501540302d459584126910309203965024000b0464141c4058400940c0601102c10a410803964495084012510302c1e0308a0010440f1507000303109070401c0300c000d9150418868500300066038001d000400b00d0f0b083c400c40b07400e102403611007840b035483d548200310159030b211264508000c3c98410a0130300c032030003102d04000b4072000d82c1c3c001058400d034aa040781c1c005c000303503070701d00e41a414107446034402072030840003105001440e03030070071061a10f110050310b4001042c2d0b00c1004000c04 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 13661715 1250 13660465 13660489
    0x3070507230904080c0a15140705030c09010905190608010603020301030b010501030c030f053606130807060c030605040e010510061b050604320601060e0a08060708010f05 75
    0x46092203100100942054100b00d03910900a80c50071303080004070340f243c500300742c102901214a01039103402038540e00b41e1445061490052012071032018130340601c01619030311000c0c001196842020442d240d06170311603240c40014220180c0035840460500100328451840d0340120004601c0c20000401d4180c070a100340c80c1241d40121044400d0792170000150010f00012503908200350300e800c2c41c89038004582c0151401000d080c803028511010f07220801e403129443d41c0c0040b10341c020341c105007589484006015508000140b050005040d0103180c0b40c00c1c0e41c03140b19402806181402d0740380700c6032905940103400b1034805075820b004030f00022400b01d00f25681205c8190040342d1350035050110743e22030750790304003003590384000c00d8414002034803050310f0070030112421518014841240c1d050710703203003901000d0055082030303080c01c0f9150784585054a8840c140120f00400c0810406030055a4508111400820020090340c1807030031b1118008006038801d0240c00b15103c44800006210705046091141d = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 13662965 1250 13661715 13661759
    0x70e0d0c0e0a09080315040c030b06030f0603031b0705030c040c0f031a060f09030111160f05010906020d0506030106060203030115050306030703050607021509060403090e0a06080f03070507 83
    0x1424101032030300c4000000686508095039490710a00e00060288000303500a070442d203085000c0701a003008210584002104000809d8240781f428545a103a001c290f03504801c4450310074000d236650300c001c2813031030040000700d080f090490009451100000b00701d070802d40e8019001c0d03c1900b10b9071070511054404018031000051608121103901c1c0c0e03c00d80c4580e085036191000e007070001c0c035408006026034111a01c50b5403080070010301d43e00b803440c003441000f51000c800c1210b2414959543c0b4071006042400c40c0160484450500290812100313503c0f41103450340c040303001c64450100721501002000101d640500940ca007000100d0030030f0002007030380e0488110342da191441c2c0105a004803696000608035a40500c2010300110004900340300c954812015603000300000f9020a401212a11014000705c00d035030040d4062101017a031142c4200301b51121301402031080d4540b001204020207683e132000d0752038040c508412001381d0011008080d40c601400444074125101c01800d2482800b001d80d0385 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 13664215 1250 13662965 13662983
    0x30c0b030705041e08071d0123010f0302070501180506060a030503040603090302070909030305040314070210260103030f110c060d11040807060302070b07110c120c1305070e0d 77
    0x42042c3c1c1d01e031300380411401c0050000c0a030380700c803602c1c40c2544d103401c928083c00c0f4a42034042d490070714020701801040300742400e1002400c2000362100d1480b445441c18100100b040352032925074040e404440d1f949500400821441c075005404c091aa611040200d402c1c2c043c0c0c002080f118500b00d000202913942040c05540340c2031404409078000d160b000030480650003001310003c1e108201c0e100b2800e03982d0180e1000310715480c042ca40205280c41d01e1913070400c501000e0003050b0142c0c5401c107006030207002c00d040000f51004141d003d0420b40340c1030108441d850b407500001104042c0c0c0680903062291203500c4045041046080701d540302e0040c83d4100750000420300003030072003600d140c003c09106825106064a040e0311031036000d04248041e00608082600010341074200840c003000982d006980e403410f01d643e1070f5814401500c3d5150038924034800c201c08024450a540d01b80b048402821005003400f4038228604e20703800c007400c0122451000b117040398086540d141003d046600031554004484 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 13665465 1250 13664215 13664219
    0x6080303070206220f06020406020d050c07062f0a0506070201090f0f020402040f080c0a060306140112060f060c061b02030a0311090d050102120108010213050f120109030504030c0b03070504 83
    0x103007840c11010141d0380d846600c0030420001142c60801d441702d0f03150003004c0147c0d03120704000d8007903c0e080d01e0311460b004018040140c80c6d415040800c80c3c46c2603c9181ca008010750760601c6083c812900b62144400e6000780f0785005c0007610340001681e0f2101d0303205e01c0c1958150742d54603805038226000928003505c15810310a07894000382d030410900101d544018001418961615a8140c41d0392154201c40c403907030b2003260701c0c0034035140c1814000c0c000c080310301d003e000311030618100045c9000101a1203050203c004808034005402e07402c0000a002a05089041c459641100400840e005d050940d0b0261405500c14145510240b04038007182a0340c00443c0352007030107007045006241a14a0f070801380170a0100071a29924140d1518005000344d00240c1c0ba681c07240c2030780f0440d080603807115065078070402140340c06c4011302c040c08007200c0c4e0445003242d070005c42e80c000c1038240f800091080880c1d403034011007104040d040000b80041c1c0c3c1c0900c0741e405085031180315032a0640303c00c0d2003010104409102c2 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 13666715 1250 13665465 13665481
    0xd09140402030c0705011b021903050a0507050a06050c0a030b1806060a0302070b040f021f020c01030b01120203010e040b10050f0603040303140403030e0d0203030402060a05030402030703080403080304020406080303070206 97
    0x255001a8220100c628150031034171000e08450340c001c509071000b151408070000495040020b0690503240b16880b00340101c56580250041c41800c1c2d8000900401090401c01d1100034402c81c0411a00940c0c20701191400718240c9147e54010b0505001003494184d95101038144407041d41c00049464400e100b19465113410020103070443c040002c20181c08100361400a1020195103010720710480f03040c111000d00d03104100c6510301c40b0020a064292020f818003407241d0014003002850000e0800041080301c160040b2082844542c5905905000000000c0c242c00300c8405284aa8015003103004030b40c46101c0822102203861041301d41c08029000c0562051409400658106203c0d0400181219154081c0320b144a4215410340c046a41d640402c810394006000c080c603101c4051026510f50314140e400106a80030745c181020030007401000080854130200403013000741d5003000c06c03907481d0ba5903403801145aa0044800b00e00031802c0c2000001e107440d0000c02d8a0280c031054000d4030480d039600103 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 13667965 1250 13666715 13666717
    0x601030203040c08010f0f110c0d0503060117011401020106050108040308010302010503060f0301090b15040b060403080f0c100902040b0603060d0609030e13020301090b0a12060213030210020a050d09140402 90
    0xf0344008000e01000200c42c41c0034071030f507011060345140100702c08120180071000c561000c401c2d41100c0c1c0c4100030049001c21b0200c0c01e808008043d0901540b6a00e90000489080545520858180602100100e002110940e040004c3c2c40c0907130003409540e886100454065030180c5001300030490508c0140010342c00340e40955804030000d0b00c0020b168825034002802c0d0354040001781c0d0840205014080441c1030f41d070360041110003c0d030301807102c030b14018089586d40c8213511020700b0307500001c240b04452600c1071084407241c070340300c10880310402801083d440081500c01d40c228882c900d8075078082c8443c14110182e07446202c004002e500d40c3c11150700c8690150100920480820106450141c080d50321000c07607a080000390307200180c9035814840304004450050341494455508548100004105060881c0241d644150090785920500b14031800b4003d00340c02c004d5102c0c4500502803034142e80061880d88150051044404010350004242c0d04103015004142d85071029000340341603424160 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 13669071 1106 13667965 13667971
    0x912010501050109050d0204060515030702010f0c080711070e010b04090b09040803180703080d020a081302010207060e0a05040f0608070602030a1d011209030201020d0f02040b030601030203 83
    0x300000c2c002c040d041c0f1a4a1061806c1c01c0c0c40011502c0c1c580011005000c043c00342c441c00e09081954811640080b5a4400158601086030b4611411030042d500700700600e071660600fa4035601401c0740d08810050503810b82e072141450006c3c100d91800101d500801013040b4203502c841c00c00d403c9400f074440c0c28009900c10f030244403d000110b0041c070100c0307402040e80340d80c0c4000c07000700110460411400750310140c1484004258000c20f040d05d60010b19100c4120b90307600780156100358900406224000c0040e0060340002d00030303c4258003525404403040001086d502e01155181e0005099418074003040501c6501c5050400c02c940c82040504090078090010f1800c00212500060030550200f0680100c03036040b00364490143d000d6000c222110101c0002481348442d1070030040d010794800c10031104042d28010007410440b41c10710944040d40d10b803001e001c1c9142c40b040f0044010750006 = true := by decide +kernel

theorem cover : BRFrame.Cov 13489215 13669071 := by
  have h0 := BRFrame.cov_init 13489215
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13489215 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13489215 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13489215 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13489215 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13489215 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13489215 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13489215 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13489215 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13489215 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13489215 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13489215 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13489215 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13489215 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13489215 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13489215 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13489215 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13489215 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13489215 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13489215 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13489215 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13489215 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13489215 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13489215 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13489215 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13489215 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13489215 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13489215 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13489215 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13489215 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13489215 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13489215 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13489215 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13489215 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13489215 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13489215 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13489215 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13489215 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13489215 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13489215 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13489215 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13489215 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13489215 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13489215 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13489215 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13489215 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13489215 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13489215 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13489215 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13489215 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13489215 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13489215 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13489215 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13489215 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13489215 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13489215 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13489215 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13489215 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13489215 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13489215 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13489215 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13489215 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13489215 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13489215 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13489215 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13489215 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13489215 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13489215 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13489215 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13489215 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13489215 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13489215 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13489215 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13489215 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13489215 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13489215 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13489215 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13489215 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13489215 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13489215 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13489215 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13489215 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13489215 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13489215 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13489215 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13489215 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13489215 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13489215 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13489215 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13489215 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13489215 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13489215 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13489215 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13489215 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13489215 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13489215 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13489215 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13489215 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13489215 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13489215 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13489215 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13489215 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13489215 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13489215 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13489215 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13489215 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13489215 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13489215 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13489215 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13489215 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13489215 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13489215 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13489215 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13489215 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13489215 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13489215 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13489215 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13489215 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13489215 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13489215 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13489215 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13489215 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13489215 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13489215 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13489215 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13489215 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13489215 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13489215 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13489215 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13489215 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13489215 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13489215 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13489215 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13489215 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13489215 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13489215 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13489215 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13489215 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13489215 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13489215 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13489215 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13489215 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13489215 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13489215 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 13489215 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 13489215 ≤ n) (h2 : n < 13669071) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
