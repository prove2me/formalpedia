-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0314
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T19:09:05.526808+00:00
-- url     : https://prove2.me/submissions/190866ce-d15d-4044-b6ee-54103f859f20

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 56294967 ≤ n < 56474823 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 56296217 1250 56294967 56294971
    0x30c030303110d0213051207030c091505030d02010504020f0109030f111f050909010906080d08060d0803070309050705010306080c060306150703080103061406060d020a02010905060126030408030406050c0c030105 93
    0x14038106654030711b0321041054102d02142c260107582c00010023000021141ca48900850b003e100740421300c4142c0c1d0452100c030600c15441940c040c010144000400395040d404a44114400c555188407401c5410044070414402e00000b003450054030079680c0400c20b40002a030008900034114054803201e003c04001c0c2c4607441044a0110358040b660440fa40350948206016000300c103010030000749420b10729a5503103050080c00307003840441750114070079403100040e40c2c1280c2c0d040b801c0907039030307040c0000010002c0156900c180c2e03c034010a48040f43c2c640c403c1c00340c081150511001404580c03894000c0141560024003400c1d440742c841c201204e0700f0101d000c0600001402607e0703038405585141040310555030440108061914079004000c1c143e45c1d0f0300c041e1174801c1c0c1e0356400140c8540010310203a0052142e40030103030440c0b00d2400000fa4680c100414440d11150302c69803021070b511211840c0760317640158000c28a060b0024802440180d10440152000c1c42c0c1210440b0b80066400300420708480b01 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 56297467 1250 56296217 56296237
    0xe0403121a030d030903020c060f0406050d060b0f070302060a0c27030b0405010b0109060203090319080904090b1f120209040312020d32040b0603010908041d01050a030c030303110d02 80
    0x110b1742c8020a042d014080842c10040561301c0d980b803d03140405940d020711550040318140b0030045400b280603807165000c0c0e0042c080d1943d80030380c0c5035041400000d2a42219030110014030032000090000318240c000c0b03040d0743c1c2c603c0d05c6a6512682d5004038088601c04a107950703000c0b2514240c00004142000031082c0128000d078000101040c09800041401c0029046003055600802c161b09183d100011a5004100c10103920010850689005c02d40d40c440c00c540e03603901508010081c2c5c18400c1300900300b800745c2c0645250311034620241d042c86c03907407107801d01ca04042c11280503403c20241c10040900c99206100c2d02d001d900d040c4031144d0f00004c9800c60703c01c1c007801300d0b5611540ca241c001c009100038031a07468004100c3c050f4001080300310408a0040c402400382900300c01084150300c1c01d4005100c02980811102e498a88421902000c144d25a5a600c0c2140c840340000410b4107054805c0810341e6080155251042d082da1030581c058940990b0b04000341c202080504606481440a802e607030303407 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 56298717 1250 56297467 56297471
    0x200402030c0a030e0d050711121b0406120206160212030a080108070e01030809040f0e0109050606150406020a06050c040306060b030406051609060c020d0b010f030c0e0403121a030d03 80
    0x901c1100a003100e0401e889280145e1007101d004000b56000819900e410f0741c01581e40c4c0b007040740b220204101c6130601c502d2242c6849100d001426941550800b0b00c2c20030001e8501b0003c3c266126002040f02c01054406034001008120398044503c0411004402e42d0001c1d115030400f1080c2c001a500e5980400c00c1040001c1e02e203001407001080910020000f0a032445a225107035041d81c036820704c2442101c2d182442556180da1040c268141ea4100c103280d5907589000304241c004030700701162625002c444561049404148031009650b40e01c0540d01911072a40c0207249845a0360340320802814040c5c807014200f50140800030020f910340c0102800383c0816022580c5a003418503004044e02e03030141005035900b00c403009150304281d100b1040b80448083d40b5100c00c01000c9070021851281100c0310103025140268000302d244034000d03240e802124802d803401140a9582d02c1143c1400c4010f440050001d440d440300e6106c19842600700386801401d803803914088100b041c000a2a000c0caa4a80001080e = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 56299967 1250 56298717 56298727
    0x90816050d0305010905040b0a0504020f04020a02030c0613052a0a060c020102190302060c161203060315020f0703030e010e1507020d14030708091006080304030c21200402030c 77
    0x140e043c09014010000c0441c140114189a503c90950080043c680c0c00080e0741c840018082d0f54411551070700020001e0002c564071200000025200d0f031100c0300d00b4610340310710b2010410030301000341d5183c4170799041009025903c1181040d40740c04480320311116084030306003107059003d40e10320240308014440303510f82010500c0244000790606507840e609600021024410b0b0021030340100b071242d40804028000e6039a040001107601070720110160142000107a0b00900450725010350004003503900a0026003642891500b14400742c0c4a800800c80a51600340403100c00a402500f0880d1143c08180011030355011112030720303260400c150900c0100c00c942100b44603141da0140840303440c030000351800507500120443c0e49001844068468810081d194000881600c02070203296440c40520304140310b01c03075840800036074a4000d0300007699401d03690000016135501040c80401501d403200024990070752561504652030350040c100000011740280380c000103a6a030f20085200f0188a50403d40311 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 56301217 1250 56299967 56299993
    0x10b1b0304091b05090d06050711030c0114060307180203040201030207051c0e04060e0103080309070302030d0215070e011d04020c010c0306031505190b010e0904030206040303050c0307090909081605 87
    0x240f150110030f0901c48100030541c21a101c1b501c1004000781c204102041684035490201e490001c00d2203488480d02001c83c200081c0c10042d0403031645800140b92420072500c0300700415444202c0307407045940da9000d610001002c101c194001d5a441030050400500b421080d4035628108900d0801600a02d4950388080140301c3d000b6008000e00750342910100011810400444840c90040c0000b0f80349050200010701c411404100b4200550b50140641d043c1c101c145001941c1c4001e040c45100b06540c120b000a142d03284218120311107101c05a41d02c00c0116601190008052007889103150069004c100f42e5075202c0702402014941200c82d90002211480d40c02e01c40346900c5074110a010b0742e41800184401540b072801c64440c0000d402d280002d18454110043e00c0204802e00c2c5180c00440010802c018942c02081c0b0343e100740d0290f102403082d0341c2c4084000740b141c40101c030700e500410148101400300c802c00d0361001190900c6990440d1405a074601e8105084030150000c4820f988014004a04 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 56302467 1250 56301217 56301251
    0x905060a02010506100905100507290708092a01030906060b0c0c0301020403260903070306090302010b030109080301152c0114030f0c0d1d0105150612010b1b030409 72
    0xd94906d0110182402d00002030911a007003903c00f420800003180120074462003d00000d8000010003072018070b501c805e00a15140306c41114250081003802000680c80c4002040e05c1c00c0c0707040e40207164030080c5a0003024610302c03030099800c1ca041560310250400040c11301c1c8a61406000400180d584500758080118640741014459500a90040c441000099803030824411006464440f0240083e04039528410500400030030035414400c881000092151941c48145010700a5000b403203045e00b044141402d96001c07020040064008000400100d10500c0f0400300d60942c51912020b203c08846600380d40082c400c02012103e1302d990304003485580c028640c901040100000e1030306600d00300c148200d1030000141b903111110000611000b1201b400da2122040c4d04600d005c030610601020300146c000e190444482c0580015036102c03421328034110b0195251a0383e8200311094030780c00c049036020700341c001400041c01e0b440000c64007800305606001900103000038100004041c940b031240202 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 56303717 1250 56302467 56302489
    0xd1a030d0c051207020118030b10080d0903020f040612050c03070e131b1d09010b01030b1302070204060b030a1b0e060d2c060103020a060e0307030b070905060a02010506 74
    0x500c4000c0c0407441c0000d90209020b020200b44a45080c3c0741c0740c4500060350440880c080c00b050035101c0359008420001c040003028041d40b00000780100785607c0c0c440d21a9250f040a0b12003010400300d034400c000524003100c414101190242010918941e20803008d03140c071149070400c690980100e00861487e060400c00d0300d0042c40e01c941d4100c41410b00085070380d8004003526000d04404134040c0c16041d40000e414509008045c0341d100e044610007640307080011550290340032202c0303500309001e130905503129024030782c410100204a036110b815901007001c0298480c1c5400ca17046629090000395510011000d14072a03000d00390007240450740040030075042c03e041105841400100124001c05456100607142075008000b000150364500500d0380644121445500508030000d49646840075001300341c03241224801d48007404090740f07514055070700d14003801425070142d2140c00200080780d02d41c1c01040e0082c619003400d0b6038464641000c41c00540c0b01102d5140584c1d1a07a090250301d00302070302995 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 56304967 1250 56303717 56303743
    0xc09080f072103090b0702010203250c14010504060305060d12020f0706020601030b010302090415050114010305221707050d1d12070620030a0e030d08100501050a02030d1a03 76
    0xc003401c82c960790003400c40c0c031071800758481901c0f020070800d0031640200210380c1c142e082090090340c511480c071810703606084040d03000c440804890800148d4041802044c0003050f90507118281040e080500c00c400805004203219488884094440301055600c80b0100c0c2340c020507030290050a551076440f516244082d4081400c6500802c01003001c107492078502410759504036440d9042d5141d50402c20b03010310f40200c50048103490000001042c000a000185018100b0b8070180400c0e615860f402035558199084050054201c04000c3c000800c2040c142e464458140c40450415820303446061074401e840e00c1410106a03c542849800c0d820030035a5642c120085405441c80745002e4080703500d8000c0ca120b01c2050003130864042032031020319010501d00d07510b40e100b225150300640354018900e58101886a00070300440070389012141c801c044040c4608000c407800070f1031030710301001150a40c0c00b2500080440c081440303c00341c00d1780103000340b08c9561842c4080031400e540b004201410040d07864520 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 56306217 1250 56304967 56305019
    0x30506010e13030206010302060703020a1a010504060b0306030a0201260a0f060b0a0c0b060a0503150403030509030f090d020a1e0614070209130c05030d020304150306050906040c09080f07 82
    0xc040000c2e40010080e041d88d6040d5581d68030f500240c6400d9242403000600203080000244e5520101c800d40c910260403100100ca09100507560317a081d42c4c9003488160380d5140c05400804500c0055402541c100c842c83c03420221480340c1d240740c0c2000030318014045d138880c082c4a031503007607000c002c1c00c190241c230002c0c0030001c2e01d2a24100d107070711000c1c040114a01c1e0041403070035880d00040c40b55550f46402001407c0280a803203a0081030341c0080070343c600845044010a29040216a10000000940e01c9136041908068500610a401c0069240010104a0384508510804108030043c0038542c07510301c40004480e5841402c000b4040c00c0340b244060080340c441c00a001d040091307030f00c0480c2250058100000e107282e80880d82850921540c80342c002d160103224980c0c60f074210a41c000000d00c110789003680d13841c905d045901e000b2003d440c0c140c494994410640740100f24146016406a0039650300303410300e4500955226032050804080004103205500300e44070411070050f100f2000d09824584081e2 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 56307467 1250 56306217 56306251
    0x3071e05070501030e150c09100c050613020d0605090c040603240b0604030f020303040302030d02060703060b04060807050c07030c080307050c0603090d050d0f050a1a040e060c090301020d020301030506010e 90
    0x1410b03543d002c0c6c210400240c0c0c80d09804035900c620942c04482032440060101030112060b0400544041c840c1c2d0003c031000c7c0b2641e40000e485c0310003045d0100e81785600500c542c100306010b031101c0f0003a060151540c0064090003514002a1365140b007403400841c4540708040e5550702d100d994050695041102000c8982004a40324441e0798110460b4180c83e408405004501d20383e0010901c1c40c043c540000750148103c4031110b10040c0c00003034561080146a900b44605030b07d85801c0c40140c010b5120341c00c0882c094902064000340114007600d4001c11103001c0750000d5a6076250002d074194164450b516507080042c6050520100b4081103804101c142c400030714508040c1c100956644d0b00c00c2a00003080b03400f290604d0591815004416502d604c1007082c011410484c15050040000c44800c085801403004030b100719050038080d440c11001000040c0c1029916001c5505075507000090b0300e0340c195401c01461038420701d01c0c800f845c048c0d030080000b0b0000303606180b180000c0c2017001d003520b000c00c80722080f = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 56308717 1250 56307467 56307491
    0x12030e100e10050c01270215040311040906090510061502060c12060105160602030a05070e0f01032c01022d030106050906041d0906151f0203071e0507050103 69
    0x58441e80282d02c6161480e514813260310710500401032071503a19907880802207180510758008001c80f06c1ca40c0220740005001094044074042c078803c1c1d100003000d2001e071501d059940c3c54142e006100c0c1901514010a80403129665542010092075006c05e216584401c28013140d90714803c8032030404000d00040905050010303080c64030f801807100241c074501541c000180103911450550f00c5041074000816120f030070901d001c0010b900200c07607241d02036160a001a4030340740311304d02c2c1c038078508405000380d10002c0945004402600b500001100798021031205540c00d00b0030f20f103501c210030443c0c100060b00c03440074150905a89001a602007810079402d075069440702404411281164002c0c2011540ea014003400325500740513a0b40528240b100380c0000b0312003000d0b2003094511501003041070300c030b21360b80786150842002c0540014a03080440c82e24201411490340b0405080104940122814586c7c0382c2c2c0c800072081502d040802564000e070f515a402c000c001c00045c405000e00b400c0602189421392 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 56309967 1250 56308717 56308729
    0xc03090306050c12070903020118120b040305090d050102090f09010b030106032703050a080f10030308040f020a080f061605030604021b03030901060302010905120d05030405010612030e100e 83
    0x300015120640c0c85001c41e01c800c021100b01c0e12024134410600d00149040d17880500080998401640810200c003041d142141c40c42c00341a0690b46c500c455a04d4170307000703522040b5039100028801c400740710301000280020f50f22242c52400b0640b0400000d69500544418007148140b40300c8518007802e52072006011003c500d02c103a030f0648003079140020300901031490040703000d900800308060380510254840300b8190f111b0003e0201c403145464040c05601c0720036131013200481c1121054010480b20703100b40000f9106918040c4c0050003008201109041500003030064031181c1e1100c4050b5000303401c0e20312171680500030f95921081c9242c60415a828071440903041d07100003084940b0490f80081c1100b44500144051017203880b0030001c41c0e842c0c0c501002d48600030811400144c1c0428461080081d107454100c2c0d0250101b4181400741400e110a2241981c20380c00140044400d552a46000f00b801e1529001c4541c481d40690b48112140e100b0344c0c240000c0f4444588154204158480c040c8421b43b90b00b = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 56311217 1250 56309967 56309969
    0x12010b0d02090703060e1021020a0603090201030f02030f04140d020703020d03110f010b030708012a140a02030d050f070c03181e0801380d0213050f06010c0309 70
    0x40c2c4891010f940c03a141d04400404840d0010354650b5020018400c0b100c0e07000002105443c0640284012089048040200d109501400130740c0142c59540a00210b442a001141c0462040c1408589111044014000d076002112010b0359400708500704414441c00b24800030307000d4a42d030007826040c218104000e45a40d06408082d024445004048003094442c0c00019810f8103004183c136034006003060704d02c4c080d00c0748070210b9200b13104080e4089040181132080d860b604da030b4a22000002e1545001d10500ea0b1a2403466a00b030040280c000469514071500034480f500c7c281d8059551458840c650108482d0040d1801000c080c415003088600c4e904440007040d15034041c10a0380071805c041500001450070340c0c1051840026403c3c031581c018903a01000c0003074454080082c40451442d04405103c071801c4006038030410904694083c42c04e410109044890344050078044243c08075801103a40b260000c052071480c10750b10030030060703926a6054810b4004e002460308844001d0142c4000b0300c98005 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 56312467 1250 56311217 56311219
    0x403050904110d05090d030e0304081b01031d030d051b0d09060e030409060e060d0b1f0308030705030a0605090115030b0303040302090c070501050c190e12160512010b0d02 75
    0x1e18040c442c0103080301c02c2642c40c1429804018012843c2c9094115201c2c510f4104030004241032042d002e0b54908048160b4060712500001410344500c40d441d1f9450105414290303a040c50360700d0721402e8a14600b0b000c3d8070140741c41c0380021a9030320344507032281040b0f9200038080c04051800c01442c000146500e800c55010050300040842d4031f24490410301c2c0100b49200060015110004000556512542005003150001c4001c1e55095035008244945084040c9000f071006080400107104414160b40d160345406011118002d00e5440c0c1c2d882100e103900070340d20718021a001000700402c05da058040e240c0a8101601d248025500d44a0410040c0101c020500285034481992554030340b0b007081501d0046400500c0c0d42c000e070520703002d05410340e8400c42c0c1c10b1b40d0b10f50804c0006a203200905040300c10316110716800380144001004100c4160080c20050b603840040c6d140c101e0307042e20b0304104100d801c3d030a8040080e0030920f820200a5a21045010b005642e4107180c90391140d5030b140101c152070250 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 56313717 1250 56312467 56312471
    0x3010506011d190810051605040312021204030803180a02030c040b01050d09030c1a060307030201140c07080304051221130f03080a0e010305061f12050903091005030403050904 77
    0x1000c0700081d209200800843c02c41c42c100c0d003000a8204800900416030340942e05080115403552260403820b08000400e20001c04c80030442000010302084d4501e100c0c0d0307043c0c41681e4544050b0400d000c42d9501c40d13482910780303280100610280790001d4a03000502d0710403034010700c8881c00c903601090311540902c8030359200b2a5203034180314840e4060701c00c50f41d0303050841b042005060920700d0058442c1e6007104c4152510881142852082c400e41c0310400e0188a000307000f08456461940111407081c045e64840700c4500040c004074040000411610004c0c084950185850b18100340c140481d210394011502c1490b4840036207421942140c002c100350381c207280032000b40d803100c1c403c13087c0c082c0c641766910002000742005000014084d2aa0117031040c0050b55881a41003140b001c01101602c0050b24407030f034841581e60405408921a4414440c00f6481e410245041b1802c1c8501000302e40003200c201c00356420001d480200c0f8030f42084205a00c4d0760900b010750940c186a2001401400b0300b0201d14096a = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 56314967 1250 56313717 56313767
    0x2070b03090304030203240c03040503180103020919080f03040f050d05010e0604110103150302011706041b020a050616120f15090f1401060c1e05060705030103030e0301050601 77
    0x1001c2c07040314051034000d001c84003080210390004402400e06001c170640e50002c0c8000c940424401d4007100d000e035030400300850030000041d4180d4100b414400005050581c01c02128a01da1103e0310080c0c0c01d02d0008002c003083e1762074980d019041035a150a0118190070400c002c0c00b07035509590300305003600d400760341b9401d4600c850301d4024010100142c8103c1e080c03154204000401035400c6025040c0c20080c0da050101d464014000e85401686000080c04101c135800900c41042c01001c4c030a620010091000c83c402031540519004c4040e800a90001600400a4031040c06403c100a44d04002007078000750282560a0004200b541d174043d41c0075005480318580f1304c000030326802411717411810110141801e603845001e01d0052840030041076440c0d0500346910745820709061030504850741910781a0441042c1d5464218123501907078542200c100b82d0844801040c020043c1602ca02084d80300d29607254110304001e48403402c6503d13040c3c820b038100010411243d900c00d019280005481030445990 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 56316217 1250 56314967 56314981
    0x2030c010503190b2e030f0204060912170c03090405100812030712050109050403110c060d151502010903110a1e061404030315050d08070b090f060403030902120d02070b03 75
    0x40d04120780380401c26005070380d0301e05c1000380510080406070070b40c0c0c40c200b01e8064440f148009034002c62003a51b02140ea45d8204004c0640507100b80b0f00072911803485003d03041c1d0000c443c1d48440d00441d02140990384082110305250030184101030f005910340e004090143d180c40300c519912008902c1c110154171001c00803d42240c01038480900d100082c2100340001d6071100f00310f8004107000c4906900040105030440b07030403540403a1041c910700b00903003001d107090010b00201c000b8080410740101860b44205002540751030340303901107002040a900110b024070f41414002c1400340c6400c90400b494011210f50380025800101400b02d080c407102001000f1003890420500801004011440040765001000f040640c1603000d20700341200c00e00c400f02526120380030300050303010205004051890400168010072030b103c4156030722034004411200079201041c55a4142001a1011404030f40c0701d8074400114500440b00c00101c101c104020312100d07d2445000350344501c1c5100b05404150b0001c0880d404c = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 56317467 1250 56316217 56316229
    0x9021309050604020f100806010810030204090b04020109150509010e0414040506040b01060201060b030a0b0406050d0f060c0305070c0b07090b0c03030115020d0c0b09010b120a02030c010503190b 85
    0x548115240802034a0968201140c82d20001c0310120722a110b0361840100ca41341c04501580c11244590f1100070f01c2d50b90310010744030030340054481c1c21920307118000040140d4440c00341c03c0515100388040400350411303200140c14074100f90450100c0d11050b08040b5040ca500c08117441c408030707003481d00c81450007181001c540100806440b20628440000420092010020310305000d00d1091030400603da070385100072422038820703020742c0d02528400c00110b10910303a40c1d00040d001860080000032240d55800010f0000d84c03020b1401c031151020908220309005d4940702d4034546030b07224202403060b850a040010a1003a41079002071484c503456000c02c0e01c1d141310700c3c0010041c12500085c43d64928000103259542d400034440c4807210140100c3c03104107540301081d1071880545940701c02019103c0c2e40d640c00d00000005102442039075132800d12082603940c1c00401e801004e1040c0c003500d090900c1b4010305040c90658001941030250400500108142c8817040c2c0060f075803c2c144c002001e0040300c0c00540 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 56318717 1250 56317467 56317489
    0x81801030617010e152403121303110108100501110109080301120c140a03150e0109080a030b192102060d0605030f06060d080c0a0c0810140405030702040902 69
    0x4012860341c2c030014002c005512080c8070421000440c1c0072003000c06500034100a04031000b44400034201840d00201420700d8044c0448000107050380d00c80c500c4024095295003041c2100a80000d03c0c8104009201144030b0b0b40700140c4003840c1130445440c0803403200711140c1051080d02e0400241354992032080c4c50070741c4803801859000b1303451582d03965181d00844400d030b004001561015000030001400d000e2907a041c0d44221000342c11503010b00e10350344a800740da4001c1c0c2d00c00070710705803105007814030340c4020f124901440340306a800644a4000c01030080c11070314a402058010104020421807003012641070404942907440140c0104002810100780840155002508244d021402c803c01040d603401c08001e485042c2c5c1128401d41103041c0301a0317210816902c140d0029003240c403002c0826404001003010460504c1111402190b95440d00c0400206034040300c800c0c2c02100348602016210f010305141d0741040b01003076140e814143c650580b28450548001d205955944071002103485000c5105 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 56319967 1250 56318717 56318729
    0x105160f03080a140103020d080901110d0c14010b010e060f07022115011203050307030b09100f090902010207090e071d01210503070f170c0318010c0818010306 70
    0x9a030400c014980030b04040019030380c80b03d5007400d090003500081aa088854100c0b41c00903c03c3c8a466802d440d076582c00d9000c5415903041040c550303552520f0303003001c0168030b1500d0038a80d9103030042c049508040e41031000e10b80030505264100f0203c50010781e03102c0c0100900403011500d1698070091010072828074407498000a40011400d01079140ea640d03900c00e10100301145000341da00d2020925101e40f241002401004007500240481c0004607224601940c0e00000b2420000b4603940480c00040500904445200240f9aa1300302400341d5800a11030030010121640c05000f412020b50000c0e403500c006006255809603140202e007000f2070100540c40040041103142c441c1030f1008002a81d425100340110340c0c2420000300c001c81d46a84600d19021803030b41110280d400c050040e136549004042031102503170b101441200315010b07108035500805414440400550b951000c240300001400f2000c29014140b00c1c001c401c6d000442c40d68400c41d110100c2d0104801c0c001d01384000143c0c01040741c0d40001c = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 56321217 1250 56319967 56319983
    0x9040312021c0501090c020601080303041106040509010909030e0f1005030907090903020319050f070b0a0608160303020c03060103080403080c01090804060c0203062511030d091b06020a0b06010516 86
    0x145001e980e0f8000c1d81a58404c0e030b4140309419407040d0690f650780c070030300c14100564000c000040104c0c4090380000c0b403000e801011913290650318800500c0d4440700380c000f19011952800720b14202f41c0c21040c1156981016904c00c08030311b008000003401d19182030401e40501400000080413001c051200300090f01c0810004c008811030f81c28001d41c0ea0b040141c043d070100c0e0305d448101b041c0b18016000d4031040d00080315000c0c40c02c452a56141c4030700340b018005241058880c07201003024081808200705888890f08110300061a60500a161814800c00389010f508148018030104250200f1182940e400601c0981d494400255590051264250180005102080200300e81e503104415000d0341d4002c404a0724a500c5c0c0c400d41070103800c3e0141024010010680b078200c40103008519420481d4054801e881c1007528145c0c0b028141d95541c64229034009080b032580f85000c550041d00c501500c11403000b00014441607403071400040024042905000000c14040740800c00020820a5a9800680c2d = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 56322467 1250 56321217 56321257
    0x607110717060105090a110403020d030507050106180c05041a07030c0503040602010c03050105040213050f010219060b030f0f0703060917070302010e0c10090902090613151d0904031202 81
    0x140c075031600c00130f00450344183c5a4001007461802c43d8001d2001c0c01414003c3d29103061710399400c111000080e004c00701e0034801c00740040ca02013a003c0c8900401020107001a0822003504620130086071002d62804061000c280410b00c4542da01a407051160301c200c08000e03a581c0d51030700f0261120119054020076a200025000c44c00d281d040d0000843c00c01a600c06110341e90325031081006030b025040c09515000f100440802042c40c200009000c02e20701801982c1d2000003030f803200c10443c0d5480b0016590b06440c0c80d03203a0702da400d040104007084140c81004c1d002c880844104191121a00e05c406854070f51034070340c84420304c01003076104619000000426961074545203000380c081c0101018908542c0200b54140300c4500709450105030b40d2140381d9882c1d94150602d03003c00d00a4009095840d004001844801e5171401d041d8008000f034000080c1c0e0640940c01030031300400a400c2c40d0700e060310f00701310340d05d04094a03112a00113541042d0b042c14000c201020074140d060003401801c241c82c113a861a040 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 56323717 1250 56322467 56322509
    0xf020903060702010c021603030230070f11040504031e0e091821040b031902130e0a06151d03010f140105030307051f0b0a0609090e060906071107 64
    0x44810b20008584d001c1d41c11085487e0480074040ea99444054050307005200a14500c580d280002c481200c21f8901c00e50303407a003520b00b01e02c0c2c0070b80002c6400c03140c8820310000e0409204240c00d01d005031070004ca030309000620703155a006149044117501d8143c0686c889005601060080c004129548ea000d4426905803418140900c5a002c40c40039440b194090038107500c0c4914000031112081c1e0740b4400f892803070140382803080c80c0b00740d000a0420104403450300391018074218038002014100c0e0302c01d0040e5610b07410102c00405941b8040c00c03507841507240150400c48540305802034800d805090400800081c00f0001d0320800c4200e440c040e5605510303155401241b07030143d610070300c00744840c1103094445a80b903030b00341640c030321440c100030704a688184040b081940d8008500007030840e4028000c01d1241640003c22041503a64110102058a8083c14400400148140000069079030300170f04881c11300d100e58507103460001d4034070400c000001800d000840c20400c00e100052050061054a03d0408a = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 56324967 1250 56323717 56323721
    0x109060218040c1b021c1a0718060516020904081e03193314010f0806010311070c0806150a08070b0a0314090a02030106060306030f060f02090306070201 67
    0x90001c0341d22030180414406242000d128071000c00d41c10707842e8001c9000884548020b40c102c1d401040b03034030810641000042070200c0300c1c480c1510344039410701c00c0e40d04410402c0303804a440040200c002c204440040414a0040000315407c96105080039a9100310703058940300b1240f00500c0281d0001217120601040102c070000900310302100714111000320034001e805184a11080ea11500804200d00601e8400300c500d44c0807401042090b010354110741e055604040e203440d140c40304241c0090500600700008440c0c1042d00c1c100010034030740801340c4000355001814026010740710504069589441e0503d110101003114161034001281c0b031f0b091641d0b2039410fa900c0d01e0407100c407520302400441c010524109900c1102c291284040648a603034206100c0074000e80004550b90304054139029001c500044000c0ca10b80149642c0c0003605c08440940113150954016900c0302d0704043c0743c00400c20110340e00302a20140c4940c050004203e4540b0b48607094041d0290140360755050040030305000b0016015 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 56326217 1250 56324967 56324977
    0xc030e031611010201020f030103020910080d03060608010509010302090a05060102190c052704110312040602060711061902070203070515030a0e0604020a0303080406061502070306050115090303050705010207020301090602 97
    0x1880302044080710b02c4004900343d01070703c3e00010f41860184018030051030090341c10b540c00a103180c40060141e50702e480307451800e52405c2d820341c0030130b07604c003014809164011900c0d0301614081d5855421545036501103400550010b080c110344a075500f000c904070b60301c03e0015550f00c501d80300c3c00300e80100c80ca0919003a20055031003018815904064046407044450302103840044480741c04001c143c2d2151032380b0340c83d440ca040d03c45501d8025601d4120541c2c601c0b8003c0c0c00a0090380e4002d0225281000001e80345045030b682c085a01e40c080d50802039241c030000300c2d074001140100000341e141c00551011a160074079030341200741d200d02c14901c083e070000c0000002e14031517400c4041c00e03c200110b1a0045403581d10945000e504016084018000b10303000303550303070340d00540f180383e0020325a5a240c0030003035041e03129080680144c11041c400c2081c0106401014090002d0300d502d020500c40c40c18014210900ca4070005091003c040b4090f03082c04004c0d03041e03d0710a900a1f00078058441c042c07600700000e40c48 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 56327467 1250 56326217 56326223
    0x9020a09021c0903050909040609021e13330801020a0f1b1a1e0711010b01050426070806070906032306090604060302040f050a0c0f0c03030c030e0316 66
    0x24078101491516194000c01c48801e1309910782a241089100504c500e0346001002502c1d115181d0b0030000040c0c9030781507960345a120b072480078140a0b1180b400c20018040c20307450764110504040356a00c3c1402c032107180c1841c2c00301c03400481c14458249810564040d81c07aa00591407544081000b0740c40507081b1a0f02106601c4550740e10790340c08160520341c484d4810b01c00000e4a41a83d10104030f01e100d004c04100da400550806041c403a018410500c89200340007203801074005030000742c0c92040c0a100f4019a640c0f842d003420f0142c106410404140c80d8120004c1c0440390040c1e00c078215a0300c3c10300a209410160011400b95140b6240411014099154178403401d00024603141ca4a00d102c560303030585064400c03107440180f03e076031209000c00128120290040b9030160b03552600000682c0e9500c68640a000e60440c040350500d8510b07440412108005000070070f108203001c158010aa0140440c00c600c0c2d8181000299074401b107404a00502c600d0001b480f9611002464414a403c01c413480004148 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 56328717 1250 56327467 56327497
    0x414070305090d08070302090409140a05060a02071e141006060905010903051504030e0d0507031109010e070c0602040e0c1308010b2b0605010611070e040305030a0c0309020a0902 78
    0x1a006a80c958035010001540c0000300134001040c1482d12940041220000c0100b0214020031140c07500301d09601007004945050744250441020841e0a00c02aa406841010110300f040b115407139080c815480024a519041e98916103001005141e040b40c8104281c3c59040303500814450718620020300136401204046139006400003043c0d8842ea4961050f00c2e07000000d845d02c2d6a0105401c0036803200544100e0600c00807034480b501c0b0f9125207100204040c0500002d04040e071960600751070440c40b1241f01c034000ca05660040c0300c80c11104a07115040006131600011080303480c2400c1c40280070748e80040040c0c0149906028441c07284001901d08400140c03201c04900740d40f4080c0c603080b18081c0c10140c1c0c100816080405246506070003072501002e060b180d42589824a940d8042103500980180f00450501401c5104e01c50041107100043c1c59803510350b17503180c20240c401601d00e02008000440c10381c0c440700c441034480e00c00c0d0440c1d69015405010317514241e49480000000e50449414891806 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 56329967 1250 56328717 56328721
    0x9060d0f1203141320040f020a0801120302060f070c021c021e0a0501050906040e010816060503060102031c021c0b03011a0609040c090b04180608030a0e090907050414070305 76
    0x114030b08840501074132522000040c0d00401d940c4043e01080003221042e080d13111041c80b112591250300901a05000081006a403449200c201606400c3c0681094061690781404080000e800081943c1c0114240313000c05a0b95403014411511500604c40c000d400c0356940d801e40c2d84c181185147c080c0740c1407080b02c0d507c1003d4074080c10303e01c88091580d085680800a0f0104004035405240203208100c0060310040c035103030b01ca00040d00f04c0c140a03409800540e1040d4141941a1020780e2010f02519071850882e1850808000003566800b83c550224062140a6007103802a002e5a048460580214807000d590851000520004084807000540a5400d1040040c18060321300344501d03203910000c02803070400d00e410301444003c4c03c1035080f10080c0004002e0216542d100140580014458a990756036421662202041a9510f0f94801402c03540140720010116070400d400002c041010780381a1540d90352010802d10382000340d072005801514018007003002e007800c8149603114004544080c800c079 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 56331217 1250 56329967 56329991
    0xb09060d02030a02010503091e0a0b060d0b01151110050f010b0703050f0d06080609100f0608190c050d0f0515040506070305040c0312020307060b0109080a0209060d0f1203 75
    0x36080c5000035899081050750000660096000d51780040f401c604a5149e0b02c00c4a01c0942e0f40d010000554819510407000c5204000c00c2e01c0c4815400101500d0385a42046a03507624160100b0601400c80e01c0528a160454070b540f040d810054950142c404640803024088000c0e8002c0c02d05a88035040c1c0c2c285100042900e2510b14115200d6642c0342d914145002c000083d8004d0300c2c0c20450345181c065441c2c00001580c0003040040c03601442170320000e07000c0b04884031869070490312403039070070700540c1c2c20301000304440c2c600402d0181e0064681c103000d0200414030b00e8006c002081a410059100c40111081402e1040340d4594460700342c410002c6983d500c000e20b9441108070402ca40042660740020b0004501c01d200b60041500684030350341143c1555101d59a10b041b050002030200016031002c1040700510406008144040d0002e0030020785450400110035100c802801c40039005041d07800200709680c07180141d000040d904600c0a803221061882c010308003c42c040440b10002e81404295452 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 56332467 1250 56331217 56331229
    0x915050a051f06020c060310050d120206070e0a03030e011101050c040302240702060c030f0706050402030d090803030105061b12041502010501121403070b0a151a030c0903030708070302010b0906 85
    0xd5a80e0f680041480d0f08264042015580c8014200302e0000c0746200d000650ba00c5185045860314401c244014803080440002480d01c24010301000030040304d11414031503038035407000400a413501072400da10343c583c1e001d0040e1006c80722115203581c3c6600c0d00e0108070351504503102400c240c901c00c6880c204000c01c00d8031a2200d0251f440141c1300b13441c104001d1031005207000401000b0b0070320040152401c2084108440c0e41035008a07a043c0c41c0a034850040004503d0244800554450141044088c5c00d00f88818150f0301e0005006290142c80006840b2112841194144801400440440720144440c85801c6a04d403c148601d1a051200c000c428542c140103002d80d5044c1c0309802031321107070746000c0d4844040b40d600c40003016416000400c0035101080310520114414002a5004520407425240c4584011120782c4050104860140a07603050b41c0c181045a40210703e1182c2580c0719180d00300000d04521480c503009050386c000041403802c140e010742140201081c00c0790840306954410080c820 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 56333717 1250 56332467 56332469
    0x26060307050a030b0f1003060203090303070e040504120f120e07030c081203040f080409020307080105030f010b062706040909031202040513050405031303050a050d03020a120915050a051f 82
    0xd0000c5500052180900456490f800014546c401003034564a403100c4089a00a54004070160000010850740c5600403000401814003a54100440d00e07260300d440c4e1004501b01090010001015100d41c5418414800301d48183d5900c0d004005000881803881d40c0c1c0c030302a20086507080303140e0500145480c404554001600c41c036070300b03240ca15030380c42d580c0032000d8411b683c04681000d0140b00109203501c4a10182d031050f0a0740d1030390307082941400101442c1a180d00090429a0b042600c1242c8907122882070350701a41d80454520728003903035040c02c19203176440114019080300b004500022000d06c180c2000b0201406502c0380340c0d0404001c4000810f034419030040300e4100d50132458090100c1c11315400960311034014000da9080114100002094070001c0e40251403d40c003c08071101400014041c840600b0780b5070a0840c90443d1803140a0b0119542e141c0907440b90396070340c48040034000604103190510311600c404204a14000f00400c00030003003a58402540700184404600c191081c501c003030 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 56334967 1250 56333717 56333723
    0x1008041502040f0608100f06020604030207050f01090306021c0e03180103060e01060f0905060a1116030c0b030a0f09121701050105030109020a050c07080303070f0509090a020a26060307050a03 84
    0x40b15a07013040400e0740d0a802c0a00007201300410340a00107003030380040030036101510066000c2c040034141400c009160880f40e8000501c907140159280240780c0e006040342c1d0440f40c0c80000940c841c490750b0218810b4110480110744400c0c1002110111407034084024044040c054a0501103810038100440445060340980e8030004c0007030700144803036401826940d503800014500200d1068580340860b155411030b2403100046102c0910078004044180000718661383c01d0074403038132421b140d41c642a10494245c07003401c003003500000100e5900700940c0c200d81140381c0c4c511024803442c8228501544500c5002d2000300000340229440180303490b0600b442c074100e0780e05966030350841c0d0031b1860101c000c0d030242c107000003400410080d025102d0000e00449001b071036001d014548030316107140080c201c00e80798282c00c4104001002a402e00341e40d100000d42e0050108040162100444882035510189034131600c94040440c8460301100c051a20045110700c00c198165a100d903540c800740071040440340001 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 56336217 1250 56334967 56334989
    0xe03010b191815091d1606030e060606070201050c15040f0605010605030402030c010305091609020a082508190e0105070f0f0503011703040e0c09040b150d0f0b100804150204 76
    0x2009130916a4002c00c84007010340209808022401585070710b840c02811007050b00c54038460b01041201e800d4881e01d003880311008058007003441d20b2000030b050361080c900000e051240200d01403000300300800c004200118810504091030805003452405c1098510b0101c50040c1008000304069100d102928002ca9014008205011507080150050200142070204030311902e0307046012080c868000a004151007140180e07248901000101403800c02842502d034100e2486040c09075910310034814940020500c0c12009646464981d040c002050702488030015084c01c5903041060410350019029410545510204002a14060b60040e03081f4401c0070204005000410141450a2071703240345003042c2080e24601a1a6100502c110409450032803000307002040305a071a0400d8811020503140403500d140760080f003415038882e00e00c988282b102280b5114114414a0701d400e03000a4107801d8014800030604407110070080071500110b03800d46070155039000d0704080c900705100b15800d66210000e0 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 56337467 1250 56336217 56336219
    0x80f0408032b0b06030a0e12121602010b011b0c0b0418050702010c0909110904050916060c02060315010c050f030702180103020a0b07050309090421030507020304060e03010b191815 79
    0x446c00501d07459004050a001e091460b0b04804400790061850314050000b15019040c803c0b82017200307015040000301560325140b211070007680c210304440501400300f0285a480b0149160203006004182c1c000304002038081008114040c40400c0e50f4241c202020741008165100c0c0e03402c03801c1c0c0b88540c00b45404954400020301c81c0c52407035088140980d042c08103003441c0c500840f0100701140c4080f51940c00070b070003540e080440c28400c550780c1c0000f000286401d5220056036000a4014130010b0032220100c1d4001768070822a90103009983c80d0a500f0905070740c4000c069200d802d40303035401030320100d02c0390809032031a480342415070b000e05050b00c2d0050700d16000d090821a6a180c146c0c002001501c0a200c1440b541c40d031580c50008003881240309100000b01240f0100010680c0146090841d092504140c01c000c03a040c0c0c00019101181c00a00e0501050030688000c28010a0881703103c0d6040541500860301500100303456000f110010700c007103803103404080c0c501000c40d80004400000d000c00104 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 56338717 1250 56337467 56337481
    0x16050406050c1c0509100509011d010c050a0302010501080c041107030804030203040b0f070c0b07200d0501020d06080d090609140103062705060d030903080f0408032b0b0603 76
    0x400b500100e55034400312080742c3e00c081d081c3c150849032581c03040d000400009080020742003a03040171481c800d039401c10a040203400340020741400d140504850040d0040480002d07961b2060150b07043c07580e04803007915400c0850b424000d010f4030702401101130701c1c4a20307445500941414407410001e543c10050305c1c0e0034108940d9003168000406402601184020700000c00c0d26545030008115120305104495554403180c0750404140300c1550040101d00300500c1100301080b8038451605441401c0361409144c90440c00014000c804035400c050655803001c41e640b20a02d582c0c3e440700050b030324100c00712481c020b10104101e804c0d014a00805e00000c4e030441c401c02c007038101000c0c1c0c13000c0c40c48141030100d100758640901c00c00c4400005140c49418115031003804003082036200711034010f00d0076030b0704142c001410780300034149800b03912008050794000a020b800c8204414151800350025905980c0d9a0042094070301c030300c442c00c1001d000700300b4010701001280c00b054818122101e90150489003990f81e000 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 56339967 1250 56338717 56338727
    0x602150c0d0204050603010801141e0a090804180203060a080a0807080a03020405060f090103110301080a170904090b18060114010e04060306020a0c060e060f010b0a050706060f0e16050406 82
    0x181c6070210a036024007011980d66120301c09180030b440c14800000b50035064040005030583c0140c04c50b403104110b68500c94182c0d098004036907000380c103581c006c5204100c900c2c0035122417103540e0061203844180102415603c0407a0019401f43d0000c032980c030310068941c2c50058407608400030042044000f04070542c006584c44003d060a03505a04006090582e07c00103d06107512000c40c0c6651a40c0c0081d13030040940c0c15211b841c0c11000001007072429503040c21b2000f9544c4503910400703009081d43c19442c080014030502110309544000e4001d00c020042c40ca000c0e00c1d0000700365640070501c40c1e05800d03454400c0c000030303800d412913481c1c540b20314050f041c1400550f0701080c0c0c0801b0a030825221b0304040089482800103103800c04495450501104080c10020101c0e901c221410b0300300c0c0c0044007444140340c01c10340c103141074445a603007459607089142400c0d078135803081c240010b11aa0a1440000d161001440e0700d0b01120256001c460036a90f4011280001c10400318518010510034441400401e01c10 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 56341217 1250 56339967 56339977
    0xe09010b0c01050109181506030c03031119020f0607060b06040312020d050909060d0201111b0a1d061504090e01020a080702151909050129090108070302010804080d18020108010602150c 81
    0x120380022300700f502da864202c91542c590700241c2c04194a02d03c100d44811007040145014111040030f540c2d1090264002600305010700b10407132180d01c000c81d643c018401c003a03001ba551303020014240c07591a0b503685040c5c82c5548440301c8200260207000c1c6540301481c018000c840c1c06401c000d05480d403a666440030410300b5000200300364100000508911210380c1300708003410508400458200c1100d143c0c004109011951781c011412260303500c0210114800700c07544c400d801c528200c8103a2400f011001c0f1691080c083d96119965aa060140f0265580d1041d401440d0509190342e030782c2c00c10b031354803c001e9a480a03104104100c1c7d000e08000a0f804409103200d280e04441030410101f0340d042a9201c26081d25120000da0184c800d50030601000c005803e078405541d40400d40e4801042d600d060b5240341c40b100c42e0710020b41440107540c00a01005000001c03185808070745a0308020903104288445a401d0a04004a000c04e900100115195000064800900f020b12031424000c2ea11a0000e0f00716400c9 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 56342467 1250 56341217 56341253
    0xe06040c09050301050a0509010c0c0201050706020306040227030105070302070503070b06041107050c090105010906020601090c14160b0609010f12050c2110020306010801030f030e09010b0c0105010918 88
    0x409100401c4a607000e01aa031b0281207219030100d0907003040e2844600b155070491aa00500c8030164171500181d812205886c00e69820000050701e030303551100404c02a2103118000b8001100200e104c1c030b5a4550030360003120469050300208019910580c0c140d04910a0007009060351780103204030000900641202940448040c01c003107920350238403000e4511900300e28400c54280d0080d81d041d42141c01c00c40081da00502092030803d03103041c5000f2000c0e40b00d0343c0600070740a02c070741c4400111520501640304100e2840c1c0403180c0d40e659802e41e2180300789040820301d08858840400300403980c185005194241a614030440c403000c0e141c6020940090100d030801c04070b66070b008110301c505aaa03a040d4405503c0442803041002c1c0741040030450341000380c46002441000d03c140240011070740d0140c0d0290549601080c41c81b80c8846a05096448100c0144069841402c400000c50700140d40805040d040707011034020f0107640d8981904030140c4d94450758800c1c10001c0c48603040003043e40303807000400d1454 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 56343717 1250 56342467 56342477
    0x1205010f020c03070212151f030209150108060409030926100203010503060a06060f080601120f0e0d110d0516060606051209060f27030408070f0605040e06040c 70
    0x281000e410a03600140ca0030101500081650810340c03c0c01c21640403051000c0c0040c2c40c006603420003d01c16080098400c02002190030070a618546040240e01c0155030002d100007240c1c548403200902070f920761001c030750015034202c1c04105a41810300a10b0400c1d5415194400c000c3c1c100602c0d03c00ca03901042003894043c280342c015504925040c0040b0380c40321134200000d0b9036981060149803601e400505506a8285800c00c10090b250740114241d80308505881c14000c0e41e250300303004803141c14049080200f110300d010044050482e1300c0c2d02100c0c41d011400c1c03d80700281c5580b80c058403e2141d1011414081d00282070584c11144150018170341d60f5003287c104900e0f21340d03030b4036483c086031429000030300450310010b45981031602c508441644664120011b180ca450003000841c2c0c040f1000d0084e00c81480b0303000940381004103040c0311482d01002d030310840f52215903c242855440401c0d21130040b0b086c3c0205000310340300b03102d039048070709450f5421004e01003078542d02c0c00c0c0001080302e41d180d402041 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 56344967 1250 56343717 56343731
    0x1701060f020703080706140601050403081911010f05041101051c0f06030c030302031e070f1403041e090608010203091b01030f050a14071d01030e010905030304030504031104020310120501 82
    0x648284042c105c414010140002e00c9901c0c0d0076000360f8400e000c1e140e141448018030041000611040450f505128005050b1000920041e000d44000c1c120b035241c4006542401000c43e1016241e90045111314010303400c90b00c0300036a010043d640b502c00c03201001400d9503c030042500c0c00d81c00c0d412020703041406000c000707a255a26100c0e0b01a03da180e400440041c0c0002410702c00b040540005940080408060720745805003e603a103800d84158803200070040010300040c680440e02c180150340007070040c50b203140c59240300b042c90700c504807030140a2540000c0c80c0100104003007005101380c902c11102c2400034401300d54821508101040d0225455040548550740f02440b1030647c09164056101050301050251460b801c02100c02802409981000641c4542d28444400c214003491003160070b080000d50020291800f6002d44000440034142d44400400e1008041e800350080c402c8a001c2c030114886c412080e400c1105138482560100c003601541c0d1000d00900500d075881e5160144600000185c1c4 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 56346217 1250 56344967 56344973
    0x90e0c0c0109150510061205040c0302040c020705150c1f060b1305040b010e0a0b0f0d0c0e030f01060602030702220501080c0a09051b0a0c0602070606151701060f020703 74
    0x740d9441c0c0310445041042e2401d402518180d0301a0700d410149007080000203a041c80c400500a0748006580f0711f2441d19000802e0038003d1070800322000e0358000d40144071480c00c048000e55100c0143c0702e9280a0510720f40c1b91540300c01c480c400d6800040d03200010b082255041480880c2249814551004071580c0e81800500f00446100801d0398062a0300c0f4842818070302810082107a03e5044c5c0603051100310016204169602d01c02c0c201669038200a0503110410001c0c07100c1c840c00703a03040c001d241901e000368102e88240c2045044a0301c3c41e0440c121040c0707504034902c0d00d00341c602c20320404015074800c0c040d05006107131401c8444808000001c040c98200c0448800da0203640d400e034003540741c40d0411400b0098038203203c034002e00a070007429400c1c040c1c0d00300103040c51205810291040300074070700421800c180c01d01c01c4040e00351403134200c0000d640341c41103030601c1340c010100c610503a24101900e194a410380346c0a026151110b031000c2040f0100c580c606102070760b40d20b8105001c4421401400700200c00 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 56347467 1250 56346217 56346221
    0x12030406090c0503060405120f0c010204030c09150803040603180f030903030f020f060a0b010309051005090606011d120c0a060206011401020601050d0303020c0c0904110109050907090e0c0c01 84
    0x8200d004090106014206042440c0c1000c81500f1082c06504020100b001007038001a01d064845c44002500d0b40d601c02000c80341d5076a0186401040751540000342c00410310501201000981c0c4480c0001c01c14010b824001c071349071601c3c511556016400a1008000c5540607901c04032545004040c0d9110142c09651031010600d011442180403803040d080500625a00c20609480700c401400144420100c880030565038086c010440340000d07464485007101644650070259410354007108481290412101d144040c1004598401451280c04000f80302d0350700c86d01540540030314140c4100b201211000511030421103115500c6101e209150541550f9218043d041000740059800380040b541001002128054078103800780c1103511000041c0119501d80200c038404984c9400c00598800d181100c050078000c0d0300d61030391340c000d400f90100300078000d006040001c0b8a00036625450b10710381300d80c20000160015502d02000030803200b824803200b002d806a035a04122519017250601010030980d9007 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 56348717 1250 56347467 56347471
    0x6050a05070c0b0309010c051e0309070b0a051b060103020d021309020909010f14010303050306010807020124143712050307020901080316030509010c060608010618090803060906031203 81
    0x21010100004001355800d00f885141002e520b1231030558540300004503401d04036210000c1125051030000081a009441000300388010410126070584406a84001800a4210034103074850070b00001103035611080c01140050580354002c24044000c11150240880404811101c1d000d8613502d121581c09a510f0b1410760788110540c0001094038401c0c081c855054070046440ea0044950580042c000280c211080c1c9510107000c1c6020f40481d5111203040f030260401440c40410a11a00c12181a4281c852001740558002000325a509075402c01030020400341480c0000d55000710f8080c4414044401c00d000002c03280c91085c103280300fa281c40000d04280780002c0c3c1100c0a030700000b860800c40c10400041401890190040d609007540883c142c1d00074040c0d04001403c100000806910381d03070103507204200c05500f18804104164135642042c0c001d0540340982800c2c1d1302c02c80307102e2080381540e010b6012120760104906056403514002d010b0781143c042c0c4819410701560301082420800c04e03001c0c44c = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 56349967 1250 56348717 56348729
    0xc0e030f030406110102030103120e0105040306150e0723160b1302040506030303040b06040f060b03040f2003070b1303150203012c04120e04020414030c010507020a06050a05070c 78
    0x350b0340d00e10304903010308280d10040910002e640180010070110300281e07001c02c0c0c00f0a243c100111582c008400488007485190002048075281a9000e07d41c0c9003000400030a9824031183d0280c030340c980f818240c03841040001c2d90400652090f0b5000c60b45000702002c0c0010050203407292000c0501940c5011001e0012200c1c6081c0c080352a400409516007030054582200c003d8024500e1400c0c0303900c030030741d42040c01040540590f4a80d1400d02503003149921000060454541607503e03400c161800b13200345106d000054500583c80079107010308491001c47c2003080c039002801011064600710380c01c03019401810952842c0b209a9070001702268002400c0403080c061300200581da5030400280c41090144a100181100c46a900703c080d050001c50f06c0c0c0360401d03080070340c0400405005408844403514034010940280c00814005112030b602c1c0b1550345080e00403001c9c0c07440c1c4140440111703464012000c0195005114840400425001c2d50080410f1480d62801c0c515281254850100d80364596000d0 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 56351217 1250 56349967 56349973
    0xb1801060f180c030e0a1b050402030411030c0406050d02010c050309030609030a1d0a0905040203071806030c08060702030f0a11011b0219050c04020901170f01030b01060906120c0e030f 81
    0x14582e406861240e014030350302d039042c204600c50a400400782d85242144000341316070902c101148084541c201032100500c0300503c1550740749401d04d0b1804225000308034240c000d1040e01076a040c5407a06004400a4070406421741800138201e40045880e9103421000740c1d1280010040400396840c00d00440d480380b030180c1c2c01035544e4244860024485088003120344d0a5003065240303171010380d458840040482d00182008100c5845900000c2d00301140e030f50244003807420115030381b2a085519004081100e0007000c0c1c082009540f6114a500c60008554a0006070010406505400740b400c011300030041540c0b42048010550044072404c5400389440000c046410208400c012941004404a406010a6194050340f0203540712640c0d8004644024852074000c500c1d11a203901c6224281481c0910340c5003c03600d030520071110030b0440381c217000a451034a52180003185280c000c95001003110700740d5036140c80c506a0404814003c201d92403a220400c801d41c1c0c900e100d20303a41003010fa14000c10200207 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 56352467 1250 56351217 56351249
    0x1030309081014060103020705030904240b04050d02091b040603141501091503181407060203070803070f141306030b040c1209020409020d0609110105070b1801060f 72
    0x45031401403402c001d08542420869461403845001c19a02c0c0c11600a090150b00c40b900361801070300310302070f1107403680d0464a000f95480000c940002d8488441500e401094102915050a00224802c030b000f165007041c0d07860345000050801309400380c2e014054602c0840b041c000c82c03011001c5980203900c2140000d40368003580d8048441c455009401000c01c40c0c10300384141c02c000001c0c1c00b428440c800d003034041000881030070445010b50030408038802001c00c04c101c0e6002d1403400c0d0100117445c181c007030414403e4841c00300c1c18500000441d2405074000c4911402c541c3c400c0002c03900200784000d604104a51082c0d184c8010b90180007408504104a4015650070b00f0440010704403400c10010701d110b03500b0018100c0c0c130290002464541c1e4900d9000c042000100d84c0042005010b03070140c029000004060504140851640300001304c0384600281040c034804d0400441d0a03010700600a84024402c0002c584260b841010107540440c03404000b240c2c20741e48194080324000a5480600d1021480d01 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 56353717 1250 56352467 56352479
    0x7090219090815090c0a060914030d1209081b0a02030607140708180a0e1b0906030a020c010b06040906080601090c090e13060c050703120504031209020609040501030309 74
    0xc800d503603885007460440e014900d408000c1c0d980e4608003601e0f0003414055400301e0742e842c0c0d09118880400310081e0410341941e545071002032038005288201440602100724032180c52801140c01000e04460b40d0741d0096480500c02820000c20300034500703c415000420a11380d80c803e1090541e48040e1460000d000e41c41114010305084c80c01c01400d49080103102e03007000022072030383c01c15100e5260304007800507141d002c1c0440c051580682e208441340c5c0052039000029514124540d00e500c00c0c0d1002600c80408403144039030800c0c5002e00b480543d4412020b00008013503010f0f5034090919181e41d00000b0442c0c140e04008504181c4c4950490018551101414010340c1da0400180303006000d031660401200c081204000c04d803903034030b0150708140300c950400314910300741c0c0a940503129600090108000058480c005d030440e48a4841140410160007040e2403603c0f01b441501d2150f40c1503100c1c1c0c6850718110302194010146008126440a410702c0100301940303991203100d018510a89a581000742046 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 56354967 1250 56353717 56353747
    0x80a0c06052509031e05070e090d020d0c02030309010305060d0f0b070201060e0f040308070215070207090515010804030806210706020c030604030e1c150c1103160f020f03070902 78
    0x30000b0300348805020200700003000c042c00344401d104e5002030030358413035601d140031400d04c82c05911106440130007034244200c00101180ca1319007580c454081340c00203041c0e80815281c1c4052440042c0d0316401c20303c1100d00d9135001e40c1103158800c100034140203000620340c1da40159820080c905480c00c59044042144290302485a50b02604600b100c1008510780320242c008051001800102040f184002080c0018002c0040c07640c0041c2d01c1200c083c1301e141001c0000c1da20442c503c075090a042c14003010030000a1000160f25034410180d44601f1284e59584050710388180140c6000c0d000980b4407a07200021400d8988014181c5d0a10302800c07003603142460003480d08113014902c91294003c0414040001d803c80c01d140f00c00b500c02d86400f84441180d452411021107030100181081042d0401c100c0c50032429400462164229210302c418100c1d095070311544e0340904428007101124011810000c0341808031017454281c4001c0440d0000041080860305120155001006854001c1504940c40b4561 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 56356217 1250 56354967 56355031
    0xc0408011b080a0b06041a07050d0c060c050406020a0b100b070303060509011d1303140301060c0c0602010509030f0f040f06021b10080f041103010e0f010f0b01020a080a0c0605 77
    0x22075001c3c4240e03013484d800541a0300c500d1044000d003070340c00e4220001c003403802020f64070080d40001c10b41d0002c00c03800344c010b07040c0034a58104944152502201078030041c003c03c10349040d5801c039801407001f580103640383c40400d5001342c5864030b002c0c4440070015154010500902185210345e0700820180d00e41030131b1000603041a004541b10008044941c20082e01c7c54204950090b55a07405d81d41108240c10f040d1000400c501001ea0207480020002c0380d020381000310995043d2140d105031410542d02d8a0403822540c00341c5455009400400403c44581500d40207802107500c2d200d500e0b450150385a8504845200030b80c002c0f0301582110280c1c01c000503601840c503112410aa45410180c940403000800400c0d00030900100110303140045014414211800c5d03021100203002000f0502c144040e2070707a580640090401c030b56090225030101c8210301d0040b00311400041c0c0003401e030300384155541400c9070005582e0100f0090303544013503c0480c0c0240a80d40c00f82c0c2e041145140d4501d504841c9034082c0d854 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 56357467 1250 56356217 56356231
    0x313060605090103080a1d060403080703110c0f01140c010e2a01050304060203041103011d1e0d05070f05060a1a010203070f080906040308030f060306090a030210050c0408011b08 78
    0x42e0700404c0031801200c1100da14404a00c1c0520084000103d94180a4111010280c04c01000708000c02001082401030a519009403503141c400100d01c4891640e401038851643d4001c0e1906039010440d5001c1d400c80b20105181482c42410800b880081300c0c212000c01c00743c006140d000c1d5080d040100416044568040d40d10840850018003480010304281f20207800100400d03400000601801007000c4400c80b5410000c00a000d212030300361054107c005c101e001d07444140501e4246400304d60960100601c85030100c0d0103001e45204581040e229508860800c2c0e51080c0495a80da00040d07051043c0781c0b280541c003500144d80207904a01030003044040c1e4460703056601c200464408515400c2c0c00da0305403540443c8080d038440b206004907040c0c3c080e80c2d2004001200100910032851070450340d0341d21898041d0100ca1b0350742d40701514a95584414080540580c00242e079220000c50142c01c001d07400703000aa03516103016655103a075030868180b8103c030b1442d00c60f11b08200d10003c1c1d00200954205607 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 56358717 1250 56357467 56357479
    0x10030f020c0a12050c0a03050a0e1201060f0512060402040b040914010903020c01091d040606090207051b03031201090905010612050c01020d030c091202040b0904141002070f081e0313060605 83
    0x105d80300c81d441d500e07410f0702009803d0140c08150365495610a0702a851500c20103404040464120850780d07018110601494138004c5d503542c400700b40c44c1401c070740e254031240c2d0681c010800c5484580038800200703000d200050b0050340351100100800c240610201e15242488000a000043c5040003400c000c41600a0360410400801c1005101d98046241c00084078000e88050035440d2441c1150040c00c0c0380d403050201d50700103e81c01d02031140204401e0380120080c3c0320f80c0802030705402059203034814500c58030001c03a601d000501c1032550a41c454032046203e0300000a1440d100c460745921312090101c00c56440d40450000c101c20759040c44000c4580c25903040602140315508030103420345000303002d0856a80c030300c04034a03030540d641c1e40c010205844000d810303040030741407505200070368030808a5070055901c00c0a810250f000380314821282001d400901881c4204841e40c0c85809a80c0200600c10840307848482a0305200b09800045008601d50005080c481c07103140b50003000c1d0744071a407100348611 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 56359967 1250 56358717 56358727
    0x3070f080706060312090b070803070f02160902090909010902091b12150f04090b0c07020607060c0203031e0f01050906030a020a06050306030c09090309041d01050a0f0b041a10030f020c0a1205 84
    0x3e14800d0aaa404c00e01e14100b820700200b800d330b0202c0c505413a6803800020a8161170000862102c194014088132005a0303502010350f4611402d9230030380b2950a402500640c07408001010086d907003002c004a90700c8544100e02e0001540111061610103844c0900c4608102050029500c0d2000800b0b02c0640152420701180c00c4c80e850304020071500a1041501d1540014170004568648048a0245610100410401042000c025901c0e01308490002080d58149030b0015164002e0104074851041404070010981c2094140040020058040e40d0103100d0b14031148010b07a0b503140844040c000a42d9440e484c0e2414404161800307030100f034440e0150450b50b061002e4001d002c011107005220950300407a1004090910426128015a070344506520301000c0c41113004160b0425890700110b075105021034a4036100300421a403041c60b204040e00303d00941d41200381490351b450401c0d00349030301300002c40082c2c03907030020140e0b80881e84110498001400e66401c114070102c03011140c002c00e07d44513081c4 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 56361217 1250 56359967 56359973
    0x40606081501030b010e06030f06012d0c1a0405060406050c04030302060114030c03060103031106010b0a050d0b04060803071b080a050312101a0705010b0609010203070f080706060312090b07 83
    0x10071640c0c2510b41010b0f1a142c030a0400e9000e00100ea00540e0301811059991a0000008402d82801d543c0c560000b4943c02054020712000d43d013440001c04241e2040c00134481d03a203020f607075034522110122200100400e2000c01c1d0504019164440e5010b240905600d1420380340107000c40324000e103c8000e0b05414002400070a43c0003e41c00c0c191031180c01d1b200b60b0034010b0700000c0c1c5030807100c45a140e40f40c40b8840000c81090392041d85030462100c401e084801030303620749420890703a0050300503d41c005031041c80f0004648546400013a000030000e48006403454550841c00c0c1564004441a2060308400748101c20101c03014501c000200234020241458110540e103da0302d034401c8051308000740c4000d60104000a6006403150010300c403c09464076089800ca0010b00f8903000008161a1540303044000072103400d040b800c60350810b40583c0075600e800c400d541d418500314556101510034040502c07400340092024460343c00558059801710301071a4801c00c008168403116006100b491000384030b58400 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 56362467 1250 56361217 56361241
    0x4080a0f02071d0a060305010c022a01080c130902030c0a1209020a03020d17040e070e04050106020d0c05010204051504290f0c030c060403050c01060806390d05010504060608 76
    0xc0e499003500391001e44d10740c550090080c1000c0d4002030101d5180203000d0f80009e40000e0081800400c2102103504401d207014000c0104405440160104141c00001010741c201640108584604000c0382a01c0c10340750000c05d02203800403210402c0d280d4000aa903403005030021000c101003c3c8200301408510310503408900e402d0110b04c0024000c84480301c0d18400c1000400c0d00310110a228042d45032100c0d580c0550b0110503c00384c5171400801c094412902c42800c06004150503120113400070060a000400202c59008907690305640c155802c0c800440c16554586a0040d01c9102561141d181d0f4101100c1c249038a9031001200c86280020500e0400b41d540e020a95425801091129407101c00f031840300c1c4e003103104610302404035004034020001010f0304a070240c580035400300c000704115900c9501c100da9524055400b0b140310034101d000340401d030380314401000000155074160030108500115440c2250403150140281c00e803102c0052000f403e0900c03886001300b4071440c0c411000e0030090081c0d0030f = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 56363717 1250 56362467 56362499
    0xf030601141c06020a0309020f10080601080709030b09030909011d0403050f1c0f0501050f0f09100b0a020d031b1707090f0305010f110f0d05060d020904080a0f0207 72
    0x10044090030034603070040280c115482d55058000c10195a9490004401401000d022404174403500c80343c2c444041030f04066010914804260720703200e2807600c0c1d2800554600d04020115410000d07592008800114040030243c001c0017036400541d119103504081003c1c80d40140c2000c3d0b24500c40d000d00a400300340c1c000d0b005401036054100a691003000c500e203120188110346141c01d100312640032056403008161310214809000101c00c01140e40c89104101500303140c00c1089601c0407800c0000c899034501001071136044807641c186c2c00445030741d6003103101d0320b9040314a0410150300880c14a00f20710f41c050081700c80d81c1c0c410000c09801ca103000341e4040c011581e12060495415070520000d50480e01030740700f41c8050a5214600c3d50307019030b2481c0c054003801604040301e0b004c81c2458000070090f4840402d503030105a11072105800d10000c01c4041004143c01020b1300c1d40700d0008085500545c807041c850500881c001d0300d042d0354038502200d010741101c15004408045500072441082070f001201035400c = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 56364967 1250 56363717 56363719
    0x130507140705010908030f04050c030c0a090203130b011e050102060402060706090c090f0606090e01030c051e061329030106140c01020f030106080c0c060c250302010b0f03060114 78
    0x41c0e260881c909256005020380000102417880000510000e02c6200c000c581c49544990700316001c00700c8407420705460720605803030706400500b0030105202c0c2d49040d4000c2e5034411141c0840c04089807450700e82540301e180a0348202046540c80d0403d003200788460210340c0140c0303000e000600c5c503820588e01040091040f1100500381559544c600010005c9107a61031004000480003070044107081001d08005105620501c004502100070000e11600800005030499403c60070744510070f0319040520880845100a1009510040c4c0c00d200c82c50350340740080e0982c4d2a029a000001508000341100484815144c11000d1408003034481403525008044a06440c0e440c50800d00c219080c0220b55400e000f4441c02c45181e500108900c1040c460301c4001c2c41c103e400070fa80311112a100d2600c0800c061181d441c02800507000b0000160100140034003d20700701700ea481c42036a181c01c00160311511400550000c8005135103d1480b095240b0b026102000180310480144c0800c0d45001e4880700c10300b0300c0754040c03 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 56366217 1250 56364967 56365007
    0x209061c050105010b03070909060e13030c08040b0d0c080402100518090109020a08010e070903030309032a050c040b031b121c021b06070201030f110705010b130507 72
    0x120400200c0040808941075010300240082d5071a90813049444e007044941c00700007400c512001460440d00d0013100d0403603440d0003410341251645c0c2c09051b081c0c000b150058091100307661080b00042e42d0381009000820603070050a480380c00e5682900c054410340e41114041200711010300025035102c1c15600381c0d550301401c00c0c650b80c40c10305040c102d08510702031540d54028904400000e29025a80081c08407001c950b03107040d600da8076800d20031441c040c113540d41800221110020300001c0d02030b52204150380e0080c240002003c4000710000440302003002c4e00c02103212904820010820200581102c0d100c04690a110219505020981c1d4103c00c6540c01c082c807480c41924956910352040761529410880207645449110b5005643c00c0804c03040280010711461030185d20140e10855074100e0340750000c244a1502d1031640045014280320030100ca0400d40c2d4400c0e50a4200e0350100078241203205600100e5451004001c002d1800c400c441c4945000b0304103400c00c0050b980c003004000d900c007a03460355 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 56367467 1250 56366217 56366239
    0x11d04051005040e0109051e0a0807080d02070318080714041d0d090305150103080301090e100c0c0501110301030b010303120212070e2103090609040b040203070f080a0603020906 78
    0x18003050076045500c0180c00c81d150100840003450190044550940200d040b0340341c0c0040c1080c1d1500010f6150610701982e0030581e0307024005504107006201c2c80740140e001c2d074100754480302c1081c100d0348040411000b003000d01c0d41d1301800d07401c244214001081000094a141c0307241c00004c0e0090998104810f21455a0303140508580f17580f440310b03001003001c403c1115144211444042c0c041c02c0c00c0e0100b03489c01e100d001c400c0100d035400960350605a96000d01c03045d0035a442c0141860140c00040d90103000c9014441403802d441c070042c8121500b01034580d40d01e2000c0b40507030800754211400404480301343c2c1410030040c8046410410340b00e045036410301c0c248074848501082d40c3c000740a080700020f061103403d03080c880500c0d4440310401075a68100e80d8060140c50023600007018209190303000f515a0000d0000b10700750703e800c4010300035000001e407001c201000b0010025040f40d00031116100840c241c000665219540484110b0388141090000c20143d030441e0001554498000c1c1007a02c10801f280c1 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 56368717 1250 56367467 56367481
    0x50103050a1a040b0a09180b090102030c160201031407081006110a080309030f040b04090b0303070335040506070e010c050601050d030302210105040b0f0a120606030c090c030b011d0405 81
    0x8905002841004d80c10044004c15080800c7c10200d0018240d9040c1d0310400402c606031410f200b124040e0798a0301c003a501c0d180d1500d081c0c2e02d0818209400303a06142d6a805602c02c00004e4084040c800c2d40700d0740d140192458140b518030b034003110b0780e000344041207851142c900c0c2c0104002582d40c1d0080d08020000e840703030b0316000e8051444c412013800002d40600858005124940c000140098418990090101010400916581c0e00903440090b001882072440c48244040d10f100195082000710b01508030384000342000c005042c03080da0704a80a074001410484a40e500503800003a620003484c1c107019940b0551a040c0d590801800b03520711484030143c50703400701800b80e030403101c09504d00911444d540f094980c40c3c3c0c603084d03c00d01c9010301481c10440700c59011b01d80010032883c540c000800700b400503400c3c5402041e008250b6003040381c4080e035039103010002c00d40c045218001072400e288081007060244600a0a4500c000000c6051040c00d0300241e454100000040a03d0308040d2000142503413055 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 56369967 1250 56368717 56368729
    0x2030304030b041e210503040f020d06020c010921050a1e09030c0806070201050604110703030e0123040312150909060f0f0c1d09070f050c0115050103050a1a040b 71
    0x605000840c0c0c0d450658204000101110300003915030f0030701790407203080d115030262200e1004540050044021040d00710040c9490400c0c101420f000c0c40b001800c1c281398004c00750071180400803e403141c11880012003d280240342a403c01d1003110316007981001440f06e801740c0070034603030303940c030f1414251001002440b82e2213075640200035500721400d408030581c3e90502079150b200035280940154200781c00a807941c105401fa4200c1e000710441101d246c580c0e1030b1000c40c02400b0107040600c0035502d94059001c1c031104031418407084945c89a403a4181c1c10315180203040e030804003030384051041c2000d1a10035000713040e0410781c1c111000d00c00c01060241003498450000d0801a20301c14440d0310745005c0400d15000c5910001408550740c80c1c0c2880c07105007098612484481500d03681d80a0704400001c1c250b28422a2905102d50840c1003603400c000543c40c0140c255503012207146070340c1c2079900080040f5039260003900c0e08035840c2c1c541040320882c005282e92900942000090199468030140603c9803904 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 56371217 1250 56369967 56369993
    0xa1a09061e0409090b07020d090504020a0e090f060909010c020a060e0316050102041a040e0103170403060606031e0b010815011112040f0e09070303080c04030b070e01030e0a02030304030b04 83
    0x81c003056aa69840d00364040042003280c2041d40d110130000b0001c0e030050300000b500c0d50812483c0c0c88487c40245418204401b03540702612510800c40100e919030075075110500741d140291032600b003810240c0360580c01e00c000740c80020700c180e409078100b8030214455900410403820042e0050404035110b0240c20086181d84241000351030411680c0d220034042c00019800b60040c2c40c1c1d281001707107008a94100c50388040c001e0303010704169003c40200420009030030001d1000004503803a0420b0034940d80b521000c0884260381e02c000007194403004400d140344034804444c01010700b551700400c00c02d00040002818401e005020031100050003015842030380c028001002c414070003e00321000700200760680c0b0080e800034455079034001030805000c40d50488100c1198490a40c5800402d1460f141d61011a403c140c0a4100c5032804010400840414003502000e48036004d262070329240702107003200040c101e034940012041c8503002503040d038005a80110071141100c0d00030040c915180c136036007403018043c055 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 56372467 1250 56371217 56371267
    0x7060c030908030f060306090a0c0e1308040b0406080708010b0307031109060d1b0c0305030c03150a03061e050c040302060702030106090c0c050610060c03030c030b060310050a1a0906 80
    0x404020060f00e104d000c91070b640b1541c4180c0940e45192100e040f11991840071081c010006011400c2c02d2014a90031319445174000c1c50f01040d03600c0240f1f2503d4030a5168011b03002000440c1c00000d044c400190885445071f00140c140ca04a0001e6143c054140d080380405010001011307101c201a2000303070001001e03150404401003160b517613002902001c0004000f10881205010410500310801030701403030386511400c4d050744030340e4515622002010183c1d0300040c044c400c02212034914941c1e984030b4140480c090740c03081c03000040a0f0009100060048090000401214240420003294150031000d5400700c0398181d031520b03111803842c4006030240103160025003025252071080c240442d0300070366141025000b6410745000d034031030648661400c800c5000c0c03900454507030540c0d40c000a20035440f9003881c0c80d40e86400122070052400103a01c1c0d5000fa1640c400440110070240701d203141c43d5038010000e01210240103c62846001c4005183c011902c602c0c1c8208000f0509840344032010b04081c0d103102c8 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 56373717 1250 56372467 56372483
    0x5100912240b01120209031507180b03070206090c03070b070206041509051507050d050d020c12041e050321160602030f0106020a0201020c1302130803120c070807060c0309 75
    0x12071076440300700a0480c20107090004624040840c3d40130020b10880d80c03519000b60140540b1064800310310140080945100d04009001d2007001c10b86080315440405001107003c241d0f0f4908141500900d00500506a50480c0e040718400501750b03a400624581120a81d011030350b21003d150000505034042c550012031110007441d6800d24140d80a00d0f000c040d50003c4440d40c0c3c02c0c20340311030b03481d10502072a4801030480e80700700e0030070689600400140880680f44280503103480e240c0e44c032b8141440752220159000c0000800c0c2808a8440100502404d0342501c1c00019041d241c00e000a90351850882104000c0c13020b440101c100c11801001c8840c14017140032054106521480c145c4000d41c402c46000070003502c0c80f0300100f506480400c8102d08035405030f005000420154041254449a2b00740d100c0c1120780c00c010480d0b02c0035004001d24010510a000345031180340a45c0301010a08008080d0401840c01b0840c100c0040e442c44140c41030160040000600ca101d0f001081c1d006180c510b80143c00b0700 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 56374967 1250 56373717 56373773
    0x110f07030b0f0c0301030f0609080f0a08010305060601050c0303010b07020117090607120b06070312061208190311040b0c1504140c27040204061a030a050105100912 72
    0x2181d00c10250740601041c2d1003200c0702d580d407400004082e010a01000340840c40b00300d24100441d29541046d0040c50003200c5075071074042e8849141400794000c000d4440801e180c08010428064203120066000c0c1003030804e00c1c90700442c01f06442d280c0c80140601c420269000c01c8481c150391040b0340c645c01c03402c69541007080c1c82c1080c0010faa0f03280011242200065591004841003010a0190b5404860003078012402c00803a0707a800d03151910000340c0c1c2d0607078540d074030310000704210041440c040340f50040f054540d507001c1e44003e854050502298009c14103040c90300160760181240c0480b4110343c0701503805515400d80e03d0703016040061160700c1d8112800f500c3c0a101c01c0c03100c0845114000c1c0110340c12a01c2d1000d200b8244901c4888000c1d407004001400c0810b448000c80403450158414401000069855100c01d0180c072050341219002c2e02c0048027000700565000d00b445003a014000c07c450019112000175801042c0c0c0342c00d40242c10700b610441d05004100110688000005008201d80700186 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 56376217 1250 56374967 56374973
    0x708030106090f0504020403030801090518011802120703050705010c030207080706031a01030509031e0f0313020108010e19020a03021303060c09060c2003030409090f0605010501110d110f0703 84
    0x20442c00c0c0101c003001c3d1201c0c040001c041c035140c0b08580450341c0c5074a0b0490203a00c0c0005030700051400415188000803c0d1503210380c905403c1c401c0441c0000301d10800c1001c901a4014401c00c03401000a901003035100d11002d00109200040c100b01700c0f102440d00c0c041d455031501e002c030704020040e030100f041441a02400f160315905500007400740f0281c1e5413203080d5200c8510044080e50070a071501e41880e0000c011090400529a118062500d56a84060310f440104080e1040320740c4121103101044609401003000c6680c008540c900400041e00c5107407190605440000960301391940800445500040e410385036802034041d42c019104800122030303440d039079040c494040d01d8000801d0000a01c2c0100c0483c2c0507004401850b80c1d01e03004810150380150304a05085e0700354a46003020f81c90302c001d00000803c01010700426801c14425080403a04d2039041c0b8181c1c0030b4660682290781400760703600700140901f00c006140d210049181c41c0c100c40c0d119061aa4600345844071400e00a180103028000c424 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 56377467 1250 56376217 56376227
    0x9010c05191a0412050d02090d0b011a0703020d0c060608060906040605010f0605250510020409060b07150f06081218031c0c08090a090506090105030c010516080708030106 75
    0x2420701032012006903100a544000c1019003c42d030060049601c52840c0004c1807140b00500603860030a0001441c00445030001580380c2070300e400c1220a60000c00052000e0f881c3c841440d00304440c10030b115400c000d059034010307484101d48080320080100c5002a182400b9054110070000c1000406540360f500308030700d4182c3c664208480595285003050300024603400014141021120b4035901d0505000c00e0614100f4500ca5081c04030f1503015406401c1c00c04210148441d40d258406082d00582d15480c000e008015a8159800071380307842e00c28024200410b070070550014040303200040000c0c1e0500a00318480c0103103841e410000c40b52103482d40490f980ca07010070007012440700c8460600000d540782c104146c0d80e0688400c66803054200391241c400003a004614089c4600e21840c032150a25074080c000c1034100704039074820210b082d120403e00c455801d100307100300d01401c410360203021a840924006044d07480b070420710030601d482500c040014044640d040c1c411296104042c1ea540396520400240 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 56378717 1250 56377467 56377513
    0x80a030e060105010e010516060501080a06060f0608060d05070312020d0206010e011410121109040e071a0c0c06070302060106081302090c0a0c060f060810090209010b09010c05 77
    0x42480c0c142105046400094081e0403560141c1d5240c401000e580011142a004071850108110424252100107007075805654064010740004100210b0907041c00c009587c003a0f4480c14032810740541c1880714076800104698088001d40355100a40c0c020716005140c803480c0d44c00a03001c80c25440746454625404107a0440c22580da500300c514070303601d91082e0b81c00070500388505071000c1448488640b4605121042011700600360401e000c01c200403012440c1a240d111442c8009079a0004a030045407506104000e0741a4158000740445400d080403218048213500030386401c0040810030301c018060800c40c00540b20f202510140d241d264078540a5a183c0c400e0003008080390207440018003100803040f218001540041082440b51128003002c03000760310408503041008205da5520300030603082d00030328607900b4400b10002a150716020a20303081001644806903028105880007015964042c4150b0650300d00020701507950201c03e0040e11824645040241180145d500301031540c0c0700199003031 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 56379967 1250 56378717 56378737
    0xa09030e030a05031c0e060714220303110609101107020301180c08060f13030e09240102030c212109010609050603250f030605090f031c0b13060308 65
    0x40144031101101c100307880c2103069407440c9030f05c0030b0b0000780203a01c05e21103007100c414002700707243c0760500300c0c508800c881d00342001300c41c0c0494588108004050703008009994031400390b006442036080104900b43c540200e9041d92603150384404120460240c54012564101d60003002000000c441140240104216083c2610f10f071001a600041034a00071408621440140d0a06c14613075071040e00d00d00e0020742000307081d03080040d6a051100c1a80301c403c082c41c0154020204a01c4c668151100d41c800300d00c2c2c0710b10352411500107102c5002e04200028080c0c01d940401c1106020883c00780052003114005c094110038052001c0b8040071201e0404500240950b210348000d00c400c03500d8040e18020703200305071413113a0035a00400006100d0303100c4111403010141c00e241914403d590b204000d000703c0340d007500107544860783c640a0150181003000054084544603000d5800c08000c8110032210a4400d2038410a0a8030b03085880d15603554a0306030102108220020009603440307040001540d08040a40 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 56381217 1250 56379967 56379997
    0x1e0f01020a0804120c0b01120f0b04140106060914090405210409051006091701060806090309010e030c0a0e10030818010f090b16050111031e0a06030302060a09030e030a0503 76
    0x310013034031410300000c4098001801c0c00f050703440d145040040c024014405c1e128550981803520000382d5601d00580220302456100c40d071250100812800c45246502c00e00501c05032400810041c0b4503030301801d003c0001104d14110503034890034100c0c141510401d801455144d1408441401c21080000e0016a940c00c08108501ea40d0366012061400941c0130307100c08100d0060040004441012164400348650700021413420303030712501145012401d681840031500086410303034040d41c3c880d01540b6002030460051002d20b0a00703000c240321807424007413400b886100c20005595880e110a01900030350b807042d1802d0740d4103103000c8000241d503280c0d2219800192941940c0003070364400c21054007601c050b0701090346000d1541c0303a0800070300f400940c125019521900c000140c5100ca030701562007400300420841503c41445560344045100902000c0114507100050012990000da4075031702c01e400074000501000d803400d00303581c6040a40704039507040c81a54510810400040060140d1600a082d1 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 56382467 1250 56381217 56381243
    0x403050c0f0303070504090906182603041a06010c050d08040c0b09010e06030a090c03050c0108070215040b0c070b070e190b120c0906030115020c0604030201021e0f01020a0804 77
    0x225031a48011369072440043c00501c000d0201f0140d0780d1000c4401c912a050005400001ca48400c0242c01d41000c165491100c407010b0307010409440c4410350140048403000b030310f14070b465076516034148c0540c1210039002004400040e520f074000c80b81080c1140d04507040b140c0180e422480200005000c40d402c640e00d0343c4a0000050048503081a04c0d81120161514080c00c5c00b03060a01c40b06800c02014225100c0e03c84062a02190741180108091405000074200641244001400419000c0c0204045500146004040c00c45004103d41c101e80c5c000d0304800c00e40c441109000b22801040400307004a0864002d001099030822040b40c503055050b28034030003861498014816000702481050440300040007000d5203000395900469000d200c65a0403420204403001150694100360003650b4a41c07800802d2001031501044686c00e00001222400c1c034150450380001e4035224006100300c0390104204d40d01d02011814010280300e9880070b0021516019840380c020300003001a10107440543d113101c1 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 56383717 1250 56382467 56382493
    0xa0905101d09010605180402040e070504060906050405060901051e010201020f0f0d05070203130e060a08030a090801060905060f0105030714030907030314130b0304030c0f030903110906090106050a090503060403050c 94
    0x744980d041b4010450400f520382e61a001d01001d44101d41485000703004038a070100d00d039540c038820540600a14200016490b01b000244000c50341c001d00050300c60813441004200550318511030f4042c4040c0348000607079806c400001030380a8020070801200012011403454144551180a00340d42c4206880034000d903141c105059841c2d100b424060052100c07246402d01c070070005c10410319003002c405446103a500d0744c2c1d1001242140c00c1740c03042c000040d0408404100000c8240208006429204420041c604206000800c1c504511161906104020000a0116010f003031704002243e00c2d0201c142da20310300b0046064079805240002c801003441a40829610500c002c1950a00060485500c560310706155089946801c000e10481c20411b108110b903001580c00307082106950303c240c0300d140107103085207464003000182068050040044004028a84c1c1e91184980c3c11984181000faa030f404c00000d086401d858550807807505072103043c050000b050b03400310050000d203980100303607000300081c56 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 56384967 1250 56383717 56383729
    0x30804200105030a0e070e13030f0f02150403020a060e0c1305060901030308190606021c03021806030a0e01051602010c0c050604020f060c0f011d0c0a0905101d09010605 74
    0xa240d140003075828400a101103d80b0f0748600c4c00c154080c0101c0c3c02c21552500c00f1107107924201d8209080e0700c41400b41d24109500710351100007518a50829160350302c1c107608020360b1411501815654651000045400c2c940213000203074040d80c000206104500c05e400c0704a0365402c10383c142030f0107680301c040516688041c5200c2c0034090500144020321592a5481c2110216000b500001d000540e0600c0319900103c4e511a0750000c001d150042c210140c0e1b1842d20a00d2007061030702d6242814010444440703500c0c1407001c003070040a4101d490980f25202c3d2018800182610700080501d5842d000c10b2020654a40103512078142c0a94028015540b281400316000000c00340010480d921440104c2c00500e01500d10001c901c1d0301900302d81c01c028180c401d140c0380810000391080c803a5542c1c11060848020808241d40c60b0620f00c004208151440011490750485072080c050210358400100e545c200d20910840c0081032010403119440e0600d10072016000c2c4280e134016819881c001d00064103041c10 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 56386217 1250 56384967 56385023
    0x70627150e16050f150f0906160308060118050112050a0605030102070501020310060c0b0a0b01020c0901060c0209010801020f0409020c0304050d030203180406060c0210170c0405040f0515150412030804 88
    0x45e50709607042c001c01c009007610680050220303640c45207044c440c08214000c10901c400d41075010f0f503909501360400c04000340074815520091000c88000d4a41844166001000002d10340017440d80041c1070b07030359096000c0040a4940080e6815400062613000f84907054010750700400020b4240e0035110f40d07550b0162005a01c0600080031014000c0000d034942c1c0f01a84084580c6006005440d03001c280b00b800100c4038002600405d020407540424001503042515155002d0700d201c5000718030340401080040601d02462203011601600010410f016090503c02c2d83e0050101800301c14a48840b032a0181d02ea80180c0340c4001d0320382043c0c103128645e2805010b044111455901c43c205c0b100055002e2140d10303040034040070140600900c6400074626141c10540c440e52040864680350b6082004020983c3c00c00404038100a0603c0d007032002e1100d01c0708002c4103050341141c2c0c924031895900300300c145a000e594420702d011124840035605068116a60620403840b8007480c120f03032545c002c003909403c010 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 56387467 1250 56386217 56386249
    0x30e01061a030907030c17010e011103060f060702030708010222050109050637020d05180f0a03080307030504060605010503160e0f09040503070627150e16050f 70
    0x101c1030103120300c0d421a402190468410404c0d60102a226140d0410300c0715642c0c02a0300c01e5645c030041d004401c00a11407500343e44440002400341d0540c4040c01e030140d000150980344903101d00c00440e40b9640d240300458032140c2d03018080c0c4045070b9a0f03002c414000d40018440e10407083c00010710040d6106118510020b0701c0050b15223a220a0401c1c081c041c0e5501303d092554501003050204010b024030403811a03020010145804035040c005440c02404c1041c030520b0041408814000845a0261410004498601641c4000c4a20805000501083c0c151360014108120010038411705580c9074001902c540d0103000309022650b03a94004452510044071040900c016046a1f034104900c10140650f040c00018815050541080f0010b94400b40568003220142d01c0040e14200300300d41c5000341200d4440410222001d00c81020050001c4c1510760001003a00c0718260720b800840b041a072001c49044000d108480030b0031072038111075a502c83c050003603e22840300d440205d140c40ca4640002d00418074 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 56388717 1250 56387467 56387489
    0x2010e0d0210050c091c06180206030406020a0c08180306070903050c040e070504110918070f1214040506071106060609060d200304110406050603131b080706030e0106 73
    0x7002c0960500100406016980c0001081129003056a140e85041c0600c2d110003001952003c1c107442d080e0222180c094046140707165680c1c1e80805a40c4440651354000c2c0c02c1000581e841060a034200c82900700344100901400001c100d410513040c066103070400389a000e030b0860307146031100c410903284104c07035110083c400e5101441c40305644c01c050700845001d070b0360241110907141c1c8400000f02558640c001024070b81c1001f04180c1d80c9850410152039448064000b04545428807801c01080200f02445002c10b2090802030184524502da0000d1039140d4150003441007400c0a10701282c460100f030f900030000803501d0001c0407810401151a07401680c008002d5464650071600f0320a09401c1b000d111100280d4503050114602c000750100b00c120036141d84040d43c1d0740b41c40d191449200c641c10341010b00461a0601c00c1c05140c490700708a9401031601e100e000a076114610f0416a0351040d00810007840c0741001c1d0006a50000041c540107440040c0c0701800b034070043d00341c020300f02c9007a80700e2203003050 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 56389967 1250 56388717 56388733
    0x506060403110f060414030c0409020d0201050310030f03050403020915030d180e070302030405160f1214070e09100b0a0501140d020a021501150806190509040b040302010e0d02 77
    0xc03440114802e40040c094814a0054080000900c540d0444e07401620075a462400d500003c0c503051103851450300088030100302041040e004290b91028030f1200038140403001001c030320b04454482d04d80c8019a400b250f900c20010061a00030090742003440228060002d020108001d00c106078500c07200140090020072004412482c1210228804142d080c840d2040ba000030640100780386100d88544401d03100076907642072030318003d441c080c0e03517442ca800e18200c00c22081c0800d556041e507030412681d0301e01b24580c691001e030401c0024a0328400c06416644191000003540c0c2403110b040c1c511a0481c041500c500140300f100482c02d50719110b030700c10b0784414030f100c0c1800b15600483d40490074034070301980c0c4d40c10710000d040020304030380c401445440941c0c012112803130f2425010a1980c05000129000184120350380c50181c0410005005c040c070609645c580c40240c9003120036000005c140c000c06483c100c1c24141410000310304d0649058006500380220750851a600040c0401c1e20742c100c1c0c2c000c5c0b081c1c0b = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 56391217 1250 56389967 56389973
    0x5120109051b0f0702030609012418020315100905010e0f01021009140f071e0509040201030c110d110d020705061b19080c070e090717030d0203011d0a0506060403 71
    0x20b43c420044100841c1060022002507101000305034070844d00a00005191006140000500140103002c0003680b5000f80b014810703058440303032039159001e20540150701c80d11655007a441810b80301080d0354120351407030342c10f841c0e49500410413000c03100c081c1c90702001034189006229980c0c2104001d14007680c003840e4245100c80d400d9221a481d540070745088008445080c90103400c01085c44a46500343c0d201903c1030010703442d001c2040d0318502480f01d0f91005285403002003201e0803001000641495620790003030796100c0c007a07840f00309410200c00507a0303000d018052004e402d0b83c0b1011200d010501c034031400085000d00005101c001e80e10018841401d21800100140d40c051458213492940d02a0551a004610290510b10300f0a8130418129440d40c01015403a0719016096100210300f2040b041031110400c404209401a0703080c09402808843e840c078895032541c400c10080c0300c801480040001503103948900701c1d5500581582c1c1c00d8a80f61502c400403804d5840503100b90b60700c100d08000404c00 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 56392467 1250 56391217 56391271
    0xf030d091412060c030403020d0305011202010507060908030106020d11030906070b130506040602030f0a06060f0f110a03020c09010e0f0a02160611190816210c0512010905 75
    0xd850000b0b02140342000003128050400300e050300d0064041802100703010805805018861003540e1074502013006601d442c4030f030400306404120190501c0000519402030180e103400821045401c5401560349583d1031000a41d0394601c08009030001e69140b1600c00008030100c2250014440106940d04104e5151500040600040c10002e000580b0030072a000050080c004184940d004a03030040e2130346071030000d01921800042901203203a150000900035281c000c15440803a0a480c9464034100d029004180c039008101040701c02c1902c541c150107010945d00003002c400d82c0d0404d81d21500c1a07641c03113500c00300e003102c1074601c03900401d0031400140805030a0303406070000c03d24403885401440c10756140e00007140d41452900c0c440080014882080410291852901030224940103500340707451030881d2030900c0c203c600c031030811804a1410702e200d50902054a000070382100e0400c80c1c09115100036249500075a03c1404488407200005500700b4684501c9102c2c0420f0464131951080d075000c0011 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 56393717 1250 56392467 56392499
    0xc0506070f170a0609050a05070207030602090307080f210a02120f09090a0b0f010f0e0402070218010605040801060e01081b010201020d06090b040506220c05090414060f030d09 77
    0x81008200c9020342d5400554280d070340e003c0c64200500040b81800c0859030000c0d42e82c010b110b0864a8241000e01100079070001ea07440c21603811540042e04d90414500280c03c000050348001814807918005d440c0003800440e0307074007210b54000f4103080e40252402e0340784070354001c1501160258002c03040224200e840039000380010b003011a5810300c2c00401c000000c3d6100070a8a5900074a52b85c1e0940720080e08000c0c401100040302400e054030718100c0424020035140c0001400c0c0c0c0a41c0d0007103095411901e036038407460b41000c031099881e40a580c55403401080340c1c00c20700c9142940c2d03007409000070312a1501c110303441c140c07010903000c0c0081e03c402e011220303180080c3c0110681103660030491685150130764411040901a401c101051080710941040161400a05980e00c20780d0700005034400070300d01c5519002c04102c0c0a43c0415844810a800da07018000ca02c15250014103104407107026a481002031442504100c6c1d102070424440710605a865044941803c04078040d040107000780009418900 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 56394967 1250 56393717 56393747
    0x70c030503070c1203050612030301080c04090807020a0e1005090c0a110f0105090708070f0509160905060708071a0403020d11030f0a080702120313020d050a020d0b160c050607 77
    0xa0f007100002d80c0e64a9440c040304074980000fa9560050020034075100c6051245196500029411035040800c1c86490b104400c541c51b115554640420040207000c0c0140d80c541500180201142c030390718400c41d64804411501600700c07a82c0030101003050700c0c014007202e00805031091544d05000446d80c0a541e4a069030004001c1403044007280d10000c0401d0081a00c181c2800001c4c00080d807400075641c2c6001101d420055040e2280da405019a03242d001145a20212103129640c00040842c002e07228020650412900040006410420702c02014014000b807440342000013034800c0b03088450103a4410680e8001c0058008c1c034403000700584901426458000c1e000142c80c41e0503034101d140c0300260720411b50039020a0004c01086002601408980340c50310700c0800807032440c600000d03206000380c00990000d02c0348110200c54024030800b04220441c480d40541082103000f8942009c000d407040442e03612501105900c242c00c1528403400c10b0b20403090340a0b000b4203082d19040781c10343d20402e0f40c000781 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 56396217 1250 56394967 56394977
    0x7030207050c04060311040c0809101e060306091101030504030c060f1103090714120706050307050403080c06010e280c0216090509010b0103020a0507030c0201030f151805070c03050307 81
    0x140305035900e1041340c0045200f80c210080550302202030005440c1031802c03401c24025444204481000042408081c81c1044000010081511a044c9580d500741a0a1902040c90020048100080d56010041560081c1640f01f000781002c00110161a000c44e0b001f00003a5241d048840040c0b1550040720600b42e000c0004540219403103548149600115031400d003642c4656020071201094030307414003040b0320075501806000042820259119264421082040360000010328824400c27019140959800b29109a9814882e002550350f92800c2c060110768114000c0421034a1440740c509020b600c1410360a2001d512014541030300400a80349480d0643c00f418000b44001882040081c000c0c0698441c00100760802502082c211196140e0171414184100480f968164102082d101d507a5818504404c0e40d50491004074094100c42c04286145828680b000300002000c104602c10f440003c0c1141215209040100080c3e41c0155801400b144441d03040e02c02080c842c0004540c003007840d0900e = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 56397467 1250 56396217 56396233
    0x30309080d0c0c020f040b0d0f060605040509100c020303070903060b04020c0a1202060106170406051008030d020a140f040e180a0f030206062b030c05010908030f0c040303080703020705 81
    0x70440946a141c5480c600044100075070a045117015902011214402d0300c081005080d80c00c0841c050103540c0b08064000601c012081c400c11040d038011a0240501a10900c41070402d208441e540703041c0101e24110086c24050600c0c8030b10310020941e032180c07100f43d6612115500d5a1207a000030521a42c445400c1fa030204445400d41004225985401c0d00c103500d0070000d0908805c0007803e10038180c02036000c0000e251020718400000c00d103c82c3d0003a410540000c2c05454910209040c0001984143c8490001103468481407056a000e40030a40301c80e180e02062800c840d903100f003d4443d0204904c0080310900c000d021020007617640950041d00da0301d10340402260314001d2454495030b07090440d0a070200d56401001c042e418827040c0d401071000c0c3c034802200d0400d8900001101c20340032600442d0340903028007405041c840da000d40d00c810340000080162429900381048180e00403140c0c160460b0780140800d074407981e258210f404813a05681d5802c0d850315040c4045020f903018402c26910380c411058 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 56398717 1250 56397467 56397487
    0x10180b070f051501170c0102030f03071e02011a0a0513050618040c030c1e0611070f080c010f02030f09060a030902060d0f0c0e01020a020d0501140c0301030c05091303030908 76
    0x20003c501640c00a00c02c0781d482d894105901210720f107407000c1700341d25004000660b6503a41c001040e034421038162a40c0d59100d079100352040350043c0801d10b42c0301c050300800b091031001c59019480140704040240780d1b484103050010600140d80d040e4841c16401034030110000201401c0ca62019810410041c200d4484443c00c0441c00d24043d0107840c1564559000d0a040007044200342c10100240508010741048580c802e40c0d10b0140005031040742c081c4144040617a000100601c90b81010741481504200015141c8a400703903550180c0001d1800b15031195062010707503000100743d901c00d160100c42c0031320346040f11042c06002d4000a1860b0140341d12014007000595601c0b02400415421000000700703440a0080c103030070b694501d00e20750140010104a0840391340e000c40e21070811501621f110122411600e0018018081410100141000345040c8234080610340000d604803402001c01004c03071900d49007000b03200c6100341d92407151844500c6444001038042d03004042d1030f0303010303072405418149890303 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 56399967 1250 56398717 56398723
    0x7020102090d080d06050a0e0402090a0b1203030a0507020a050d030c0c120507050c150a0c080d05040b0711030a050a08060102070e01060c02090a0b0102030405060c07121110180b070f05 81
    0x64102c90310080482e08884c2440b003481504018031040740d20205a41c0b411010105500000d400680034540440c001a03010070140c1152541072000780a6038a00901050f4450300e9810a4071311380411400d0a0100d410f03244000340300c0303d1054000002d820200107841086d4002c0561036601400c0c00b181c0aa0440480c481c00044500b008260725000c2d5507008a00d050350400c000201ea6520402000c00321a8840355404103a0304165802d0410b01410342d81070a190505004a40c00003000a061004000c00c100100b066240201c030503480d01e40020300c17100c034159128060507905c40009901403001c0901e443c45041034a40180060040e540c2d516128001d20b11000760981041000c40c0722010850114180010f5843e1301c0320300000204400c1070315000003512071140f0710480d03100e41400714510010302024003208004100e10068410301401510740451940c86001c1c0c05480b80b8144100e401d1a107004000d81c0c545924103858100065080c1a01202c0302e4110381c0095031503c803000d1155000407420 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 56401217 1250 56399967 56399989
    0x16020f030307030218010206090c1e090a09030207060e09060d02010c020a0305031b010b0303042c1e06010c030807080702070b0d020306100f0905240a0f08090c180702010209 76
    0x2940d000340c1d4030941200c1d0700103c0b40081d50121b04540c807681c104060300750041018103c880f8120307054044103440d4074010491f00038176008182c3c08a01c00d002c0c07020041d0554400d4681c18130980075a541c1a41d9140c5c103803444040251315a81005800d0005001d03860b101c4c4200001c3e03403050600c440340000d10f40100d40c1100380c0e500100c441d03520010300d030203e601b8a4000056400d0100009001c9004d48402103500d80c003c0d4404d14254401c04038400040e250801c07908040c44507958448145803a15558100305001c04881c8807102003121804075a055201d01220091660103840e1803040303440f04041220580b030010411821805a000049020b4031284c0041c44103694000c40541c484c1084070400951503524035088045c80800d400610103103801c000f103002111412200c040c140e28031070202141e02c0f60312a800441d0480006800c0300f03095001100c002880a10350344001540d41d0344c10302c007a65400140310701d66000007115052a0003084a4221951021003840003600f820340040203e1418106 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 56402467 1250 56401217 56401231
    0x103020417071e05031e01180302010203010e010906050f0f01120c08150102060f0a05040f06020406050d0b0307181107050618010e0303010b0d02090315010f0f09060e16020f0303 78
    0x2c840800410aa481d1440d0b01e5001d10200816040d01d0240003941d9041004c08440386141001c0c050000c4e01c50a510000303405c40907040d01c0101044a1034000c1c000d500074040c80c1300ba1344a400012808112500c01d15066900142400700c0620303804080008001784802c070103040250b460b412031041b019a024645509440d80c80e901c05504055500144400c142e502040c11503200e84100b00512001101c50750300b01600b0b140018031900d603414004044880d80c44060a0745000240002c1d840d64000018580c58840050410400318040101905e4070f400e0301c00c10035200b03007181d4400d5849000d036002002555101980500c1d2801d1991200d0514204880707100c0c003011100a00d060300d10080c0103950006800c00c01951a560403c0d203040082d01909005100c160341c04111307162191402c0000001c0f4620411109c0920740e5200400d0138514040c0c010130028440e00000041d00300464080c80c01580c0b0080e658000d103986001c00301098524040141046204a0b40300c4500110203100460264403 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 56403717 1250 56402467 56402473
    0x3070f0c23010c0201060b0702030601030f05150c030601180b0328060e010315050123060d050c0408010b0d0f02060c0313090b040516090501120f0609090308060907050306040203060103020417 84
    0x3070f5060010b42100d000b80d100d0008000200320390b1005a501141050640c1e42c0004c0e000350302c03400303810603d1419100025400d0034000c060240b00d003100c0100c0213188251000da88051100f40700040540d80c0d401d00d440343c0b4109030004e0000c5031002c01204840307840c1c2040c10100303805a04e60003604d6401d481c96603001c42c1c22040500018010b100c54010b03102080359a081007806194034091003141c150309006103001c0c10307086103520714100e0303900c10341141c40010040300140030fa400d10031001001548188a070503d40e62800c00c4420701c80c1442c0c651500c900c0e4000f00c0101c42070310319030280b05242c2d1080790807003880e00081100c012402c1d0181e1451000d000340f07010004402003024103200403a1405051040680500c004412526034000304076000d4075002c1c605103201418516408000e040c0100c1d186d103001d410a0804140007802d5885800c085005e9501d403441919030106000081c08140c1e20300300021400c00000760702e41090740040d82c01203418940145016503900c0c000144000d420403004042d0 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 56404967 1250 56403717 56403731
    0x1d040f0f02030a0c050f070303020a0c0218091903020c040e010605090408090103140c07030e010201060f060c0c06050c0d030209062a100522020409020d0b011a03070f0c2301 76
    0x1440c41e200c0e48600c811382d41032003498000d00c3d03c82180c0781e014000000f0300305a0001303020101c0e648950200103500da07016004507a1320b0855031002c50071030001c40e8668218483d202050810940300104000401d4058001e00704141c034003014000581031221041c505903480d0000020203440b0202214840c2c3c0c024402e0703c0c0c44d1101d903c00141a180000c0703e00010741008000e10590000d07920441d0075407985414004648014140180c0c003501e40d541c00400500042c1100140094000c4c884846551059078030303009040d190a000d640030b009070059a041d50388503140703502c0e510b4041c0e4002c00315202d0003001e69007020b4140ea8065181c1c11a40c034400000640000c10760155a02005080047c00b80b0280c284428070b000c50fa101300d13442c1e403070b00400502c3c02da40340b452041d511150f0020060342d4010b050000688100d082400305904203200b00c0107442170003452202c3d8145140d041e01e001e6000c954405c051084130a40032a60045890010f0300d102403c0542d0710b03207501c0f0648402c0003015103240081852 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 56406217 1250 56404967 56404981
    0x3030e0a03080c16060e100804060f06060c0611030f040b07140a030204240206070507020f151b01060303050304080703050909090f1504080f0703050409140103060c020c011d040f0f0203 81
    0x500c0c5640440180300510030300c00c1e066074406101907c0c14056203003102c055038890500c00050207105c0c3d12056071510300070300882c400c5c0d4060424034841c0c0c0541c1040c05000040d04403540140f000f00d41c07542092600502180000e54940002500040180340c8220000ca5020818150303078400824800440e5001408100101c06a0114904801450030b0708045203e00140a5110000200408100000020402c046580308c800704541248081e0403414080814a0b0300c0403664800c1002d0301c0b688541c8a6103995001707050040f041500d60582d0b0340c84c10340d01c59039070302c01180c2c0181d0012070074001c050060706007540740d51120070702c2218070400603d03844115105140c100301584044c0d1202c1e1022008000101d58910102c9040600e600301c920750b16001d5041c1101c0703601854103c41442400c00301c900c804001600c2e0000c1c1600d004a5042100c0e04404405036687c0c0d880c1101a4040351045200c0f20107680d2460304207064000141c0040f800a41c0303031014204480e04031441807107003a400710501c4a4 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 56407467 1250 56406217 56406253
    0xb0106210c170112201c0507030b090a05070e040609050105090606041506090b0a05131205010b100f08060f0d0503030a0e03130b1804050c0a02010b030d0903030e0a03080c 75
    0x5080062680201d510f042e10b5000302d0382c038000c180f0051074071107003400c0c0680c0d03c484074052081280c03400e6845841d0b50a1409a490b05e000384012b0f80c2540e25400072800082010480307118403503000c4010105a8600200164034040040096541650320012807020410038015144660ba103d009003003140750240800c0111071480d00701e211400300c647c0d800c0c0092034000c40c0d1701301550317034414203035444110056046605209120a01c04080f400740c4000070400740c06403100208520800080c40750921090500c0200c0056004080000e100110102d0040e405081e50b03a0b00a140507050240c00000ec0004c00d820b04000c1c3c0048605500c0001040615003091140c0c0d4032a0134014080d529000480b5000d40c030010b6540540e03038100c080001c0548411a001000105289001d03100b40107918092072410726913040382e1003010155003080c54002d0346240c00b042002d41e08401d911465640d80c02c54408a03003502070b504480e50024103006010000c00c1411014021040000c0000d0880c401c4525090003 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 56408717 1250 56407467 56407469
    0x80304290c06043e042307031a0a03060f0e0105011502070f03080406110c10030207030e0301060b0301140112110403022809050a150f05100503040b0106210c1701 71
    0x1022203002c80c07040e0b0000f80c9480c8807841c0815105401e0884029840085c005000f51034490340c1c0b00710382041403442c20303103000070085c0b04201c191010019130010110a031190004030140c5580300e030f0701c02428400100320758400113007452100000580d103a210010942100c40a800c0802280d02991001080607810004000504203a80440c0c2016143da910002240554001c2e142441038100507070990310740070800c41a041a00802d0003074980721040c8050001c3d440a141540040e80c04085050340d8181400b9031310031a4140b5080f1440c5a28103950781c5080000c52007114100451101954070034a01d5005242103072001c1900540e031103140d481001104145c55a002c0c2c20314060010701d003120204100174000700d4181c2180421203688001d9000000d1581e4050851100403114000c2035200754080040c0a1b580107a4082d100c0d20751070042070300c05010481d002014100c1c24001805141e104003104805107030f0b01079000011511880d011f0098400c0c0c5203021000582c6a10004900c0c18410400740c = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 56409967 1250 56408717 56408753
    0x306040b1905040b03030c0706051902060702060619080102070c08010b010f0c0f0309080d03051b0408030403080a021911040501091103280204080105011e080304290c0604 75
    0x581c186107040a403a540749101d101d2a4880c40c0c0d62108407030ba40c1ca0a00480f406008141d0a45a00c285c607850080c00c0c9400050401c0011070244000250035800095414082e0702d0f1500205095a603007030800503901e441d0f2540c0d00702c1c0c0354142c1c1c0000b21241c003400a82442c51082c0c04a000803030402d64080d013102d4807245120f04001113050303122955504039003050350080d004014002126064241922410f2040c0c0c0810414420140d5808805a0651245025520b2001030514a00c122001c0e020305004038022031402e80c008200c104001043c240040c0824006401a00c028a00040710b1050a501d0440c007a981e00e84800c10b000b0142ca420300c507141c05031503500c90800c841003c0e41400302640c08020b0029204014900c0c0c86c01c030740c00e4140e40c1c00151200b1440155a03071a12401d850307010b40740a2140c1038002007415041454052220b41440588000c10001d605051030410400c40407039060200c0b8410300c000012242100c003400d802030646000b0341d4020b100030f04140c90311207100528540300ca = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 56411217 1250 56409967 56409979
    0x91c080603190803010e1003080d0504140c03100e0709020309070303110615040e0a02060f0403030215010605071203110a0815090f01050609210a05061006020c0402071a09030306040b 80
    0x41d40000f41000140d0b41900e040d818007402566858101801020040d040a445c0c1900400c0c004501f40746500b0032407089202da0420141194105006551002c9801145506401c10316007040c010741241d100c4101808032008440070640e444155400303d07842a554807080741c000900074424141c0001007002007480b400300520042c50100c0ca160800380c1c00060307451107240c03191680c07040c20b5410489424404d130000c00392542d80813558500a065030103072008078054010049621064081c0410060480d40103855540c604039460b607900710381d04a03c80c000018160703611030284051580c007000e0040002c45465075100c41c14030400038620704110143c000d10030080c0b00204801c1521001a0904403101035a04a07101c10303130700300010204500840c0e1a102095240c400000403040040d00410040c0104182d985075101e03d1607400c00c010050181e80c01590040340f800c0210700306640102461802501c01d4032080030081d80c031840f540400d48014072903900210901216113841d100c5c90000010031a44 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 56412467 1250 56411217 56411263
    0x9040b1608011a0a032315060708070803101e0603050c030402030c1002030d020f07110613030201180314010b0301060902040302130507030b060a09080105070e18091c080603 76
    0xf44144051560011803040f40045818910240250003020000780a0700c4600805100380781e0721400c03860200c1746070704642502141d10f80e203410014102ca500da50030800719841c0c0901c03900d4484d880c0c5e0001e0300ca4400010300407030000e214044910540400030380302e4040300102c0d02d000780080540d017000d003214040c5070007001448016031380001c1c01d0300c081c0d80c295035030103c000b140c1d00103a0550003a109100342003400000c583e84444610750040c10918424180707140000b20b10802d11500340218910b4049c1401c0ca52000d00144d802642405402510308024610a984035610164a4205552a4022030707454481448480c40c0a01070380003e0700414074210f04043c5035400040c192840c016008200c00e64980215100e10701c00c0c3c00c4900e005201902c00c50799808040700c0100305201d944a010082d501e044042210a0701c500009001480c00800000341210608045601100d01a00c10702c240d102e4400030307880c0da1342c01200e0580d85003000c0d141d028091800030145030804035202d5900b030298845000d = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 56413717 1250 56412467 56412479
    0x180d030815011d090406020d020d06080601090b090a0e0a0609050c01020606030d0518030106080a05030c0105010e060a0501031e0c020f0609030408060106050c01090203030301030b0a0e010c0509060d02040509040b160801 96
    0x4240d0f84400111208201500d560424031b0092190000e4003c2c03890001030003401048a03034014000f140c10a10442d1260f030790320008a000c84820200b0300354010611004034901c90030355001101c005002d041942c484d0b02d0507a507184110390001d4000c0b03e10f50042030004140d0745c0c05020060f880f00050303019202607415060000d01500c5031405560a15444c14014411134409510200c050f1280e4812289141c1450400790365a40100d0101c4401d507003045d00214100c60341da0780441c050395000d0b010484040c2041c00540142c808000c0441d07042c1ca0110f2451051400c80c0507281a011181d005031142c0060201498148100100b1034141070780b04100800c008071000481e1411161780740303089501c0d0143c1c88030b014091301880303074040c0d8144400300010084c4400140c007180038001c90b4604100400304810305a09807a40c0700c00000102da0305106803031041c2080c2c0300503c20300c2a0000014035054460000443c5070605940035111030110404120700f5421113017050700310003420f00340038405616242c = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 56414967 1250 56413717 56413757
    0x909030e030610260111031008060a1505010e030c04050f01090e0f030910022b1e0e10030b031b0f06070b070516081b0d05070c0902180d03081501 64
    0x2101078262010307004140c00700c04e0800e62040745003204a6040300d94904001d039070b0144420b010300440c0c50b1409100080b98692080c0d00c02d1103914004011b80450f118074201c0152402203080c0c1c81b09030140250024100c03640d40318420f41d0711600104031420001d50400341500102d5602013500100e0380c0c00300840c01849000001030f00c81890080718405201414010300300d042c505810221000a440703040c00804020905103043c1f10b0003c0c0c0d42d07980c0420b8220703100b181c1c1d015102120000201d07a058642103194181f8040d514080805070602003a500600d0313021070310b042c0300c0c2e018025202801814070085494a50200c3d1030301034048510500341320894962501a10018003c0000d11600285454103042140504504547c205c00e41c0e58a402c5080241d40c0c070400e07103071301e907008502600c51500d9035980144151461a60412250f5407070609040340f041c02544500b42c40c00340f501c4411251150b50340c0e080c03410405203100c0d9640d035041e810200710b92540a00da075030009050100043c0f403110b0004200d = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 56416217 1250 56414967 56414999
    0x703030509091003050a03050405011706010f1d0a030302070518060306180109021c0209010522020c01020903010608100f0504080307081003060e0309120303090c0105130909030e030610 81
    0xc903000070058903003c401c041210300c25070005219018004035607040c16002000342084600a884801101c0100310002100c11404c86513240860b1800c0d0720080b02a21070f114681002042050b0910320303804800018002410581c0120010382c0b00034800d00590500b1002e01032103201d2004c00c401c0c00d0605000007601c82d48002c02c440782324800c8444010303045009410455940340c0260104022a003504003040c6a08407110702a4000d02800000140e40d04001040c0d00c041550500c090200c0c10b80703000480e02035488881c03c0e60180d902880072a525680030312419004004442c01040c564070315000040a0310f4050488900c0315240c0000c0001182ea6142100e40c03101daa4038010b040d9a541e03050002d9140300542014024525100396203110384000001400943c0c000c49a0701041080c0c3c080d601c0c0e60b8030045891080175004141d8110341e40d4017031000341001c0508850548801500c070043e030701c12124411810350000304400c0001c001c40c101030282e41e81100700c10340103460303445c24a060500300d6028 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 56417467 1250 56416217 56416219
    0x230a0b04030c0b0f04032c0d1a0709081018080a03090c09020307021006051008060d06020c0601052e0e0a0503061509070f09050603190203040317090703030509 70
    0x190500050800d441562001c0007a58040d40b50f000c103041600c0a00c044001c2220100e01103642c038031008104840d942c044100c0d00032045426441c030448442406045801c111089600041200c80340100c00184524244111341540c2d85d071072094a086041e41c60040c440750000031040c507149440c1d0480c0c075081d81058401d42c22a00746642c61800070f00880051082410190a0f08000903000c50415440d4004501a01e20340e400c540d6982c401c01485822580948a4140d100aa46081c0e00c851070103043d403258041401040d04c03c2880990700d80d282a41d1065100d807909800040c0180310501d02484003240322450036194071075032800307810008510950a5902d10a01820444484180d607070100100c010b007401030190303045c0d418041e0607451b580300180011440b800c170b03144c00501e0a6200b104d000201101c0f55403100011881c20050020301c1d4400f50049c0b40400c0f00700002c2b074583c5110300065004038442e03a1440e01d01d1016611107203c00c100030701580003a400c081d27400c00109522a01b5a011840 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 56418717 1250 56417467 56417483
    0x20d0b07080c1222060903030f2301030b0c090604080a0201090905091b13020a0504090b0904020a031b090c12111606020f1e031005030d080403080402010201090816230a 74
    0x1c02d4104c07442d800010114014007681c18200000c0825030700d900314541002410760244902100c809240340310b156a010b803000c1c05907600c0c0c010404600945409508102c6210142c1c1c034140e038100c0481d10343d503c80e41003000d00d6480b0080700700455034481c11800c0100f003020340c02c100038280b044140340c8900b06041030038569000740c4007441c800e0303840400c1e00c100e02124402c119070700e40ca00007010b442c43d0054403d00900a00d001310305922810051080d5104640c010007000d221410b5540c0c00300c0e400e400386060000482040b10129201e4a2441401c1c1501003e444500c040700c0861a00c40c01d0760391200381c030041c283c41440a11148450b04001040c00c5600c41005601c6800030004400301d0f0003220600c51000000654840c01141d600c0c0046000718410400c0580103500d58041c169240d021400040010b840c00c0001000f1134803030118190014070510021540d18444d8640381c18036040007410030800e0038030b1400304041218108051100031f641e05c1d0a91811440381d110b29880348050180038080d01 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 56419967 1250 56418717 56418751
    0x5090a0323061509090a0b0402060a05040305030a050c010b030106141309051903020f1903050d090204060305010c031d07120c08010509010f0b0303270607020d0b07080c12 75
    0x40245286031920640380c2114942d203003c0540100616102c40498015030221001c5204010007060f201001a0005103d030103545a507400d110741c80e400109e2007410000203000120000f102403004183c3c0c046141c2d200341d225202c10282d03908554040340202c2c42a0314207001003014214500100c04a0700c0100d41c800d8001491a281001420744000c0c018114001c0301c2181a0000894a8505600d03010394200c400000c4c04100940d03484005040304071030310703455034203942c0003d11580c01400d00d20151100802d50316081d9000ca4155916130304203da01c0d94444200d80c40c0268544a480036022091050002c82142100000d44610300d074000d48124080c3c620800d03051042a500d140002c0c060b84000b0441032400741517542c001c04d02c500311103013101c1c2401200303d2586800000da922405403918603551694480740d00e5080c80001c3d244003034001c1818804180960b1780c4180e0040018010701c031a050504d0150b000400c603810040c001c0340d102c0c10038400035025a154403552640408880100e113101 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 56421217 1250 56419967 56420003
    0x5060d200301110403060501031109042001170f0105150708040302040902030115030b0a0f02190e040e0d0c0210020a03050307080603010605060406030e0d030c0c0f111906020d05090a03 81
    0x5001c050303110080203d0f0005001041010992101c4c0c100d038000e910708204030600c3c03020001003030025640607128400c07201c900d2040d50b400c014081c41b9580141071000e07040100f26044c003d880320840d0507006405800300100036500307080781c1e0b01782c804040c940303103030b03d00006540c4640c03c90041d404007901450b0b032211072a0864900b5400040014801d01441e500965a450003140240c001c0390700b100030303d003001000070109a16000b900c2558a400c240c0c4810802c20700000c54079540d964000c2540b2a45035920001d00c0da000744012406e45205954042680c20507006004502284c0703142d6200715030103104588041381d41305080c0c0703401080c545070010858840b00f0000303002d4404c980025500c0741d00002c00148030345d09944900d21b2900000181c5440e15050003080e0110790100781d803580840c0b100c0700c0c4c0d140000c02e41440a008944503980b003941481c1c405010404507132500040340e01c4101d6414003400043c0d01000f07000302906651a0007840d008041d1f010070070b060900c0c40001c0042c00c4030a078090b14 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 56422467 1250 56421217 56421221
    0x15140303071106090405160f02010b100e0d08160302010605120307030c08040f06080a0f090506190f090305310509070509030a080a1b050d0e030a050706020303010302010305060d200301 81
    0x1a008001b0f011600380000e0098403007440800b4100030907940c440e60a9002d006000d84241510002c14030700580c0a00c02c015240b16007076406c20380c0c1c000900980c00340019100c078050200c80c00002000b044545003480d0103821203600b500601d01c00c084909144448080020449005a40c0361402140e04a00380c5408860307405180c01c18190350325006404111158020707a1300e84956560802480404050311710ba008031f0715906809881a0070660000b54081601203614140701050400040d2000070103070510102d82104100b14005440010580108901600e942d01c4062040c4284412021644000283c80f9890311800c1d000300c0419001a411501030400d035185010090b082d280303042e00c145081002980000b040001055004220f003608440c241c0e2a086004e5100004183e4500c00c400e080e226608000701c01c030761503c10740e2040c0780018402c1c440400148a240c0003141c89506510001d0161100141818054000c407102c0f1804542ca6881d252191440306030440c846210840c04640 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 56423717 1250 56422467 56422477
    0x40e130816080d2901080907050a0b091008010602060a0f0609150302131a0618031504050d030504120f0201021605070e0901050405030d0b030a120315140303071106 72
    0x905410001c070090080440080c22880c5008404000780c0d102c0c0b0012190050b2200c440740320300e6207161850030040d40070302c0102e5000061402105e2141d40c1c1d42e00018250303402a0011941020082510002401c1c0488000130100050070700c0303c059810700d40020341c1c1d180c0003013104007201d850b01526554407041d82d02c00f002800010ba418410b599001c01c01d103041c0c0d13040d803104a000b000021401c5140c90070754030a0303205000c03042c0e51502510600108201242d0000c102c031651103084070101da050750398104108071174010f03940365515491809007046814880c1d00122201030500b0041040001080456010407540c4942481c40e110f1140c110202d009000b10b0b12141400d001d0404c140040c82000540c400845071907165140d49a610042498282c03036040d80c000340180d0050044400502c42e0341c2203041406d00141c125101c40d00c541d11000400708074888600c0c00319075035801c5d034a91541c3c98086100901500c0501c0041d211141020030740d00d2041580103000941c4090203201303542c0d203001c2115 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 56424967 1250 56423717 56423737
    0xc0f0204090602030703051b09010507110a2d091b0305071106010602010902030f0a0201051209030f030a09031b0206040b0d1803020106050a0e0108030a080c09040501060320040e1308 80
    0x5440e17242014018006000982d105c25001c3c08042d8003070400203180c030445524160603920300b801c01680385d5613590700c0492030f5400c0794028485c10f80401d10080b130b030500401d4521841689640c0c0c40c1800c2000c20291119002450114100740c000c00c403109190401c0b01400040d407070001007aa4601c6011561880a07014842082c02984c0000461590541119003001c2c000c600303480900c0b0240159030354600a42c04000d01291003403002131155235052200560090340c43d400d0b03914003500300c51207681c25802201c0d803d2a0650b030b00c0003c0f0905901400070f488001c8580d103220100882a00001c80c01d0150303204100740840b0020b43c440f5601003d030040490710030418402d64002d400d03803801034080c0c1200e0081500884440340006405020707c1d442c0e904942d2500003852034800c0d406803c031003d0b00014a1000c103a0300802c00c50314a600c0764424540240115500024034200340501c0144601c101c0c070034440c40d5407051105008103c80d20001d9038214030440216044800249841c4803140940c011503 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 56426217 1250 56424967 56424971
    0x102071709030d32041a030f0406090305070b040b0a050106030e0606130902030f0d0f08070f03020306010309020607150b04090804090513020307090501051504030f120513060504140f010c0f02040906 87
    0xb06000307140c8130b03024000b039850811900784514600b410511013400101d4103208010741c101c000c00e020400079405001000d0017450910314101542e00c0748a102c00007503408580004240c0100001c0700b01c18440d039400742071145800d001d522002010f40e661460081c00ea1441b0302a03414075800145080d602131441243d0140075030f03003006000100c40d0b41f1403041074142c80c003048100040c0022148500038007803046445403201d128030301074014110000d402c0181510305140d034410a040150b580c18000e000c800b0b110780002150805421002e20640d8008000c2a020300e0410010400254000703090314142d0354540c400090b1982c503a19045441c0041c410083d4140c0034040c0d0100b402d20043e00070704c1c1a2141a9040000d80d803000c004411644114880a0303c042c00d000c2a032000224180c403042c1088880346030090a00e07081210a040c3c40b202648440c0c0841d0f00010104962860114060201c00c801c503030740c400100051001910505441038010b0118401107281411551030340d01851890b6082001 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 56427467 1250 56426217 56426297
    0x80307110f10091a07020604080c1002030c190807200106030209040f0b0f070c1e0203330f0105010f02030c061e0f091903020304170102071709030d 65
    0x20040080000582c02e94100442c004e01d940c4606032503034168003410b0294001c00490741c1c0e540f0b601841e80c0009100b4840341c007807864165030700d042e1070001c1e60041060724800c564411b045003900c0982645460014144104001041b001070b402042020109541031510305911480c4404540140460f80000754000c90703c0040c0028040c20000c44000340f0302c540608041915609000f900c1c003041169503200140714a00f489002074031200c030550f04004040302c9180e25446aa001a08240300d9481050940e1030042224403011140005803c4200e150f01840e1882c0c00c1c20003c0c0351108505006003810322565403007000c2007030310070003c541d8003200e00402e441c0b01e03061003000034100c2000e074180d020200310010086107110724031844d51070040b4003181c014540850500da4940280d28100416010344c0024080003d00383c0e48460310305d4040040c2000145c0d50b155625098481300340c001506800d03003109000c08409034400040400d0040114149800841e401d080d007100003034070107a80007441d0520244 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 56428717 1250 56427467 56427493
    0x10140a0b04030c0e010b18120f0a08180a050a090b0a090207050a0b0906070e01030b0607050109080405040c020d17060f1e040c03021305060a0201021b030a09050a03080307110f 77
    0x500f507000e41c1c5014150070803990f6120b200017800d02071540642c00c40000f0310004032961400200030700381c5070601006d803211f14011403142820448800d50644100350005032220b00028582d4460120980444a20074028100b0022400028550060302c507115980d01c9030f40307203a0781c0301004100204076400b410341d65940149441502d41d44580002c60301e1114070408a10903d0000c2121032003004660344550020071f0150046024285c07440300c442d00440e0401002e40811000c0c001c01140a0064203003595451810082c0000c5820b190805021904805181d10151341e00c01c80791150050702c41200c00a9841c2c050002390203003c048102075000c0302d04204000c1d8003040e2080b591829408840400032000940b0041d000e900c101c1c2c146468060038031005102e00c1c0b030508040c01d43d4040703501c0010304104502411910004c0b4100a4032141e42c80460304817291940443c078000901029252400214603580d1070248078000a000041400a110300041032203504104a140c2941784800712003800d40805 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 56429967 1250 56428717 56428733
    0xa021002070b04080c240d0b0f060a090e01050303030f012304020a030b0f040b1309150204170c04060b030c180307140103050a0207020109180204081c020105090610140a0b0403 77
    0x50a01d0240c03110106c06095042440c06000c5482c1c5c0c1c2c1c6000300d1a01148982c0c010040407400520380d4052001060844161104000780041c00300035111902c034a420101503030380041c1d050744264480e610030020003407804040c41505045544100c5005900c844d002402034038803190b0803400c2c1d00b0034400702e0401402070f49900001d01c0180d040e506401c41c00310101c00d2006a404108119030854503400130a001c040055004018503070007030030384403400084070f1400c0040e030303007d94044282004041c2045003042814004440d0300b803404c41c0c00b000401d207000d2040340305000c002c0c409104040301003881c400c0856000019a0012002801d42d1740307040c1c0381d445107034141511050003800030f0b203800d002549145943c82240d41454050b1200d581d0b42d850a40c4407075801c0c1c41c03000c00c0303899141c080c0800078401808109070500e14000259031003842710601c0000b400c5640003000c00c69540c0c041010f002141050394500d40c00e071800300d00d501089135502c601041915603150312081c640e402c0042e000007800154 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 56431217 1250 56429967 56429983
    0xa1b0507110405040804150302040b180901060e010914010507050a0311101a19080607020a12081b0d060e09010204050a050108100b070614070c020a170a021002070b0408 74
    0x540e01d03000c4404481d02030004850080390300600510041000348030407510103041c0c000002c0c1502e00036103072a071100404056904100706008151010003142280e9252004645001d4480342c0b50a05a070b800f0000020b06901c9140714101c420100545040380c40c0c1d20034401c480b1415040001c640c0440158600246510442545074030607000703450700d1407251b003568020404900e08848240c031003099108100a40700100c15509004002c04590002e0516014000b00b44a08195000b801001c94942403c0320403980142c3c1d0342c400c020a00003001700300c4540910f19203084214041c110b880c2c03107041001070028855504040d5048150f00c00b000603804054000700b06032242655500c6049a840c3c0054ad01c58809a40071200308032400e0052104000450180a83c14000c600111714040b600390f00c82120b00096804200148941c0c8400c002c0d400c01c1c202400c000c01c212101500340342c03401101280ca802050307000a01c2450061a4104114030800406001d0040c140b40942c4e2156290035081d40c807445 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 56432467 1250 56431217 56431223
    0x50114040c080706050f0c011d070302011b05062a0c0a0510020301031208040201020102190c1a0c040306091a0c1c0209060a030e0106210501180201020d080a1b0507 72
    0x14224000c909420089404802c40368180c541d06d0400090b488281180d801910900203590b5075600002e111440408a0200b000a00c00c00303042d0450440c00010034030f500c5503007107500b05182c2c0d015040c0001e0300007580c5a03109c9209122800c10b00c805e409041901c1440750801d041d89440071805503d031071000700b08640183d02c10341c1180d021108141804044c0e000910014000d5200340d84c1c0d104c0168001d124003680648140300040c6002c488403c08864911280d80d1800010106080700d01089031168900d201216000300e2105d042c5480c0303051603c2d510a500000b004151206a070900b08440408040d103180d20104c202003242c03800c0302010b0b409410242a45424218003002c018840382140308440c044440034001c1890198446001c0d40507104210340351195643c1c0e1480000c8810790f920008000c0c0201990044400c41c446c00d113142034807010410440d8007403090303424000603031300003401c0b034107800107405c010256a4a261076840103052081041c481314080b580d003141c1241e8010003c081d0144 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 56433717 1250 56432467 56432483
    0x40e0d030509010506100f021002070c061d060a1b0203030a05030f0f070f0c020102030c0f060601170c160f050f010f0606030b0108010b030a020c030c100e030a080a0209040905011404 80
    0xa80d4800b030600fa04d1044d00c246412224184900f20060302c0341400405002d214012500740207101c0b440142240c1c4000c40c107480907040100c0c02d1082d1a400030f006218809660252046149400c000444c103106004104041c001d04601e084480489000c2146480c0e80040540b13840340750351035018019500403a4240505c500000004201800350380300240035000f96507600c04114840001500c0e20184242d01780e040d44018800d03148800170400800c000c049295000d02010b050000c005003108408040510964841d41c04110040e001e500550780300303070402c0780c00341030040c450b003007000c880c204000002d0b186009201031900b000d14150400819002001070400c4000c1c0d85041c120119160304585030f001507855001009180d030755802640d041407110301d00510300340c98005e10b240b5540c80500781d00304a1300569075034921008648201040b10081002861412202c500010900c0e00300034081640d047e40490165540d8075070b80c0c01801c0e56035200000700100c41c0480003c0b2440300c0122002c8076410 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 56434967 1250 56433717 56433721
    0x10501090803040501050f07050d020c12010c02060c13030f0812060a0303020c09060f1806030d030e03041217030403050c01050601050a0e040203130f030801030c1208040e07030b040e0d0305 83
    0x5442940128100c81c10600036600342402c01c4011101540000c41e242c0c1c0a500500078080410b100b4041c050341d11030f00ba00203200386c2d81e244042c00120005110420b01591401205d400c6035034000c50342c99405407485403c184c0e5010b05d221044640390050708013903e44000c00b81d0403802c104401c002400c4482100d11850030382e1f501e01040000404680c00020011b8000407444515800c0541040d074100000401400c40701081d4004103040440d000300710200b040080060118505003404040b0500d01189014024000d051060313550300e00c59441a1188082022000c800780a0301a90111a0418454406980342898140148140c01801c2c42d0702140d46050081038541d8000c10440711a42401d0302c80d03401c08600c010801000750401841c116499010000c4a800101c508408011045c03280e20381d40c400b0350560804190220042d081814840c0108410501040b00c50082d50202c5040300c02c0c2440c2955500c604601800800d090721390054200480d2020341c10010035402e07100e003290340d4100815 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 56436217 1250 56434967 56434969
    0xf050303070c0302040b0a051003021b0102041214150c07030e09071b050c06030408070302060a05040b040b0a150803040501030e01140c07081b01020405010305070c0c17010f1104030b0105 82
    0x1e114074100289824203040003040107082a41180e07250301030080a404503039541e000841d078103099180032000065030004031540d01c00300301c8190270142c5035108021410b050601c568803ca810240101416840000300e0540d06040c00300f02000d003400740c3c1c0d014440b003410003000890068118542c01c030003190190b0758000c014140746144a110341103540d248003030b44420b40d100742c58004000b04191400c0c061006c0310411911407100450069114051043d0790348854100241001d601038281154a810071080c01b0115200682c0c0301d030042d401c990750740c3c070715200c84901034028580480283e802015820b80040c5000e80030001d4001c07503000781c03030500007103401c00e003030a003200c0703503000c001400d074000c030740490680c00c91440078151543c40382c0d081074900200b200b1030401c0b47d5000302c40c1d0000c580d00000c0910043d43c0c14000d268000a00781000d007403020032944c840300c2042c09030250342e42d1040002c40d00006079800350801000070214a90400c804007201c0d1a490700b07940325000544420003004000585 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 56437467 1250 56436217 56436223
    0x10f0b070c1505040b030907090518100b010908250b3606280f02030a030c090b0d06080105010807051e030304031509050606010819090f0f0b010f0503 66
    0x385912008408425082140070300c60240014900c204001042c0004560b024140e801980940032240c0100141780c944092801038920080600300b040000362311056500800040200049520300004108621507030b00403030301c024041c0c0c401d000c1481125122400b103003c81048110b001000c1807083c40720f0740c0342d650f40341061040303030520f1451212080050440041c1a0070304120060030000765050003021310000345164102404000c13030054080390b448201c07040d40f03070441e10030a91804c1078070a003542594007079100d00035841010b00345911004200806441780300144080c0002d000034649034402030016400a1005001e411025031074a030010600c140c0009a00e07046030801030000400361420400d1058024a107849942c151109110100016070204440022104002000199000a410034034602034000d4030030f90610000d0310500c41c2612400c94205400b0781d20100126113148649000c0c90000000e04c2c1c007410410100e18214100300141071305504950030810b1444055403140209a1 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 56438717 1250 56437467 56437477
    0x3032a0b070815010e060304061104060807030c1e0305090f0d030e0f0c0303031f090f020903010f1116020a09050705120702030a0503270709020c0706080402030a06111908010f0b 78
    0x20201703c04010210321854980002d50384076124000106072006039a0b90150706420540191003c90b2641c4c08206c0865454400c6901031040c3e498294503440310f854024408003800720040081548407000103402c45010020741a0307002000c412501c3c0c545006e01e0080c020010030f484080c080c010984024a070110004c0e00c1a0810390003406586940c407034020381d140e12020b40c40d10844901990800180b0317100d541c40748214110807144050390701c4940f60300705402c43e030b61081084103451401c1f14045d8400b03011810759084c0c10209a610b88000500d0001508400c2ea9500c07040d10341d4140000c000c8200d40c4007000d000049821030210801d40c940c0ca1080e038480c081d1101040024a0610010ba22081400e2280000040001494400e42111500345007007040399003040140c650006541d2281d10002c0204000411380c0d07150480c5c0d9420203900098880481e044058041501e03111001078000c00d8800311134070f0000a402000c00d01140220180c01404d09200d00810705030321040000d0301c1085001190 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 56439967 1250 56438717 56438719
    0x601031b050a150318050a0b04030807020102031303050a020a0507030c170a170a030b0913050705010207180b0102012301060210181407090204080309030105070c0c03032a0b070815 79
    0x100e240d0f2181041103000708072428148141d4000225210f011550521264180740d004c1ca2101e0030b0792900e410080e0102030040c0a01c000c5a10400c100546080c055604450483c0e15152295680d003103007400328a4404031100142050258500010030001c40c0c09803041210b22414546c0c4250910710102a10b40051f0034014014082451600202200607002003082441ca818002440c2003030b5800700c1c0b0f401d02d041316101048000c0691041c1400800c10610000300000d10013003210314200440c40d41c150b0140c054010083e501e030204890542e000390080c0b49280d256041c415210151280c0b40c031100c46d02031243c04054083c90021043c0390286004a00c00c82a02e40d00c85004011180c1e110604840061083ca000d4007030b880d0042814002800204002e0000e900215101c1041e03504040c21244040d200b0000d001c1e62001450000386006105000c40381c15041402c60055000c50b9064070341c0c1e4000380500001c6e400b411220030043e0305101c560080c0d0b81d50346d66032000d0360f640c91640e41c16403005c1692 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 56441217 1250 56439967 56439989
    0x120102030105060d02090a0902040b0c012012040c05030319080106030204050d080304020f0402160309080304081c0504050a0608040b0703050c041403150901050712060311150702030601031b050a 85
    0x96403194140c1d400800c3c0a04020b07240c134111f903586842003412a0843d81001045440000d000f01000400b409800c0820f5440130003e80511881e400c81c5100d1301c2174002104680c401480080d050017000a1141e00601015066a17034625541061108442e940902d0b074000c07c00050020411910910030b44042d43c901a1079052144503d4460140c12f410083c81241d00002100c02084291214009860b0640b00501011460f20442ca80544841950303080840c50703030710074030041104400000c2d00c0d240181c21f8006148244c041d511040b01c1e544034580103030782c0060019000050482c0d014001f41c1c4564007403140d07501c450720381100c1102901c5065411040c512400d21003800407500c130140d1042c1030b80c0b00808039581d42110708051041c50501700d4030701c03107142d54810800090503041540d0902c0180441010080d0303604580d40d480e90310075510754160244500d52860005203246001f00d4102d50340040032203481c3d41e543c2c40d1061080b9140c8801e00030000e500400000c06050070071031603055071110180 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 56442467 1250 56441217 56441227
    0x30c0614040302070e0c09220903030506031203090c0613031a042f060c01090f0f030e03060903030f062d0a0b090a030f0f0803100519060f0c020118120212010203010506 74
    0x811112311180c18208000c842d000c1c1d8807030300c4540c43c0d1280c0d20441d842514049000e1070440205414462030914000742010100100040504045403070500b14000f21441c0b901c0d000c0c00905500c031881c5035000208440a888010040d1a02d1010018030652240c5148900400183c0c814600c10b00b9101d0300d42d49400042620a038285442c030b003e40809006a0000a0040800e440d080c0d810010110140c40008201200c8414141c0c44504401089002da0090645007010b440d056aa44401007092001b03500700f4000c9000c0759030318008a801b05901039404281d000d00004840480c2a40c040394a200c0c0c40000e030009120071901043d00c03420b501c02426050300d20f1554543c1a03100003840012a07161900c601c0500000d603445000d940941c01018001c0c40050038101031108241004524200074002d0403000c00209503c1019080003203a00c0c58610120403007813005032105802c010380300d03401d1440c0000c007042c0c4040b00114060b86500803110010200f90f5006881d01300e110031b000e00da03080141000 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 56443717 1250 56442467 56442469
    0x230403021b2b03020c0d0606170102120c09011403180705030606011202030901150303050a03060b03160509130c030b03070509070905010f0c020915040f060f050d030c0614040302070e0c09 82
    0x110b00750400740207006480d090704010001610140d0300c046c0403214169030b032009000c9400008041d5840c408400000c520701400e800601e410903900a01c0880746070000280c0c03103103036445104403101c0e4003c220011600c034200403005070b032010081040316682d0310520400080c0c520300011a01e00912043e1541d4201041c070101040c003079440146030450541d00c075448100510780d12418000110f0080d070311583c0302c40b1075081c018240d880e281c3c0904036400081c0b05100070121034a0620f2070210290a04599a03846400030500700d80c40140500502441c1a8242e11529010b402c6840c81c0c801c22400e0301d1040745c441c0c00300019107105981d8000040c10100d0140301550161030807040c0e01185044c032013240b020702e500141c1080c1040300c641221480400140703000d0300701401280506081f0302d9040c00581e04050902d0084074291060511911043c1c1c1e60409042c0510500e00b46c054004409001a0b003520807a07440c01c00c1c0a0750308800501c00c0c074100048110001c21304d00c1c059a48112001c6c03401c20154 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 56444967 1250 56443717 56443789
    0x150e090c071403030109090311030403020102100b0d02040e06100801150915090615030b06070b070807050702030303091c050a023a02010c020d0302040302060904230403021b 76
    0x4a070440c0c0303584507080c0c1414090801c1003c0c500811a41c400030944440d2032a005014620500d0303c0c49032640188020300050307801144070301ca00c1419000014241d0038440c0060280351052038040d4000749404d0140c2e00c40000401c420344100444202806010307500c0000c14203c1d100202d000b146009184000c0c04004c0e140c0e08505840701c03200150010f001d46806111040382e81c0f0342c0c881d81400e4800001185525010f02801000c81030495000d8103110030b0f0b890b205031010005105a040141e08000280c049004400340e49009402804594a1303291084600d55100800244480305141c0a181030030b0643c41002200e01d400155405071007003000000b0340701d03e102c4072002040141c007840b1800000500c0c2d4040314040e4090a94008603003288000c0010382405014583c900400d40100014070140c1c5890044458003003050384e00050340c01030b90140c0102d100f403180003c1c0c0142a40818001415400912518200d440400600c100c0b0f090038100542c14002c0c03109030070b680c3d4504040c2a141500a = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 56446217 1250 56444967 56444977
    0x30c0f01090302091305120405030601060801080a030809030412082106031509010207140606011404140f0402070501060605040311030a02010906030b0111010c050418020a141e07060204150e090c 85
    0x86040700107908042d40c2c50a0411a4200c2c47c40501400441c0c1008649410400d290060009040004080d418050042c1e1a84444480501131105120105900300b00401c01c481c010324075024001000456854481116480b11038441b09561040c0c100307414a4502c50900c81c00742e00d004000704500c0b0720796144115003280c024880c4d12555824019000811040f4170f60752114046c80b80030380000e207007031800502540d2445903001c1200605000030700c4220360303459030400d644074200c0e0303400544d14001c030000b4080e1040784d00c000d1941d401c0c0705000404c5600305000e0029203100741c10070212959400207260391540c6940010f0f001914681040000e98082d60180c0c4084806250040d03880c0e02030800a401c0d03c1c2e0b010400d03400110002410401c001070011140408804c0d01c4003546092010740c8000c04500040640c40000c0d900001c46151300c010003200e540410154100c556244d01940c10410001e400900c125801034540110034180c00c1d1007544200b1030103100801d0200b8549a0b82843c040e50b0f00302c = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 56447467 1250 56446217 56446231
    0x105060712020a0602030a0e0105070305161407080a0504150f05120703090203070602071d04023706080114060306010f030b1503040f060b030a1509110618030c0f0109030209 76
    0x7a80f41c600012850781d00045214030341440700441c071103d0b004407941c02c4540c024001c0b001c0500e468113008c805100e030408038612203a42e241405004510f190070203030302e02c01d4003401041c6090009030f601c0d0f01074012000d0001c0300c80482247d00420096079082d00c103044800c034070000141d4100004404000907a05842d08500549800201c00340e141e40031034540760454015138056072140c0001c1001543d08070441c50070300c05e8841421050308182e03000c01e00c918030095401c0410142c814205d03c04060070380d40c500b110303503940499950155950f8000b8011203422301500100300780110701e00718941400002c90303014807011b0b503074042101080302048000f80040040c66610443d9641d16014092056003e140181d010b050310001d40001803410311b04940018000e01e0103a00700d415881c022440c00c1114a031445450000805e10241915041000c1c107450000694011008510014090101c1d00c0c2e0f900e120005400325070918005400300117849022a0021340007035800c050620041c141088d100b508062 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 56448717 1250 56447467 56447473
    0x5070b030a0209120606040c0e09061c021305070210050f130606230a12050d031517030c010501090b0d061e05010b031f05091623070506010b03010506071202 69
    0x11a200003c0d80322413070111401035031740484207002c11303480e1a10030810485003a08003141203298074070200e003002500400180c421114070b050f82024800502c1a60441c45c2d000f428081008030304107a002c0107000503200318006114490340c0b00004940b82c4100c9000780d03d011450341d81e40d595141c2219081c40360510807183e03d074079400005010042104c050494007003060001131020050014041015416400b802d810b030b0b034a400c8000403503401b103412a00d55000346008201015040744c0e104121303007951f1100541102e006010402c8400200c05403020103200002400140d070388200c0324003a0707603142d035249910989883c140b0000542031303808162035088408081244260803500b00085030300c00da0000130003090000800401014101d004045030100c3c41915400754100b5010803000341d0001d1101030000305030381c03070602d5450190f192880040c4003032207031203407400b10f5004d00d903000d41003411b00b00d40e54848c0300c2c00483c4100119003620b040e03e4001e40540d04016a540710328407041412180c5a003940 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 56449967 1250 56448717 56448727
    0x1060512100b010c020d260a110c031b090a060f090606030e0604052e0c09080f01060308072901031202010605150316110102030405010911040c0804020907030e06090a051905070b030a02 81
    0x701f000e01405100c40d0300c0d1a44841d10304000c0c0b2650800d111006440e200c3c3c0c00080307108040100040d22481d0010060340d041e5080e070303a2502d08100512894110000bd012200000a0796071080c0d0425400e59040b80c1d001c6c443c214400005c29a110b0050f00d00628a0300280c0740305000610140880702a00d04224144000081608000301214140e02203417000481602090021030f46c05c01c20310000f80c8964008001c6145183c80710304d02030080c102e0040048214900c1d031034141c19014088184140742005458255a681c90b01400d20a45918a00095401c1220029452400c0b003a417444600c01c121040c3d207540d8030b800308084040600d0b441c25052001200f04d03841501000d00c040c500c41c4c0c4c4504c000007041240c6051000414400700411072295043c003000070300030359100b00041d820a9050318402c80301e23121100154050400f0400e0740201340700d8042086808074000407014485401801034031154001701d00201010415003002504131741c0840e40421401507403400569019140d444018141 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 56451217 1250 56449967 56450033
    0x10c0f060c030209040e010603140303040b0f180f0604110301060f0905070c1b06080a0605060703202b0507020d0311160e10050907090902030901060512100b010c020d 73
    0x6c0e50700420041035a999010140200a01c5100c0b0350b03812840d00d0000d6040d49800e0755040c00844004002808070000343d00031071000c00303903690044101c18490742511715605c0c0c4031041d160784100c2102c041d500b01000c128058000d003010312821066413401080460b40340c2c00c080b200c1c40276200240002e001c1242124441c00400d0952601c2d5100040c003449800c1140c0c5020401010180040d150180d40c030310300f280810442c1c0d035420440752420b030315040030400d07001f8483e522501902104490f415a000b0030300e240c0100c0002015004040e1407c13140d26807980701d0711070708540700d020360b5000940041c41c0c0c0c199a40402e005140b540b10f4032120780115603581c0307585110059050516440030749203072501c0003400311510007a134041000c2d005c1503440c2e204a1410b0540105544658881d8088880e03000011603150202900494003619019200710b80101c2080d012550b5a086000101000751400c1015411584558103a9007015001011400740e0151501c94041551150001038a0b080d00302010f4420 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 56452467 1250 56451217 56451221
    0x50711040e03030906060613060e0d0507060e03070f0807030201050705010603060908070302010b011809110c0d050912030a12020f090306041b0806010b07061805100b0a05010c0f060c03020904 84
    0x1e440003003001d15140c0c01e00150003482c00e0405000d052250600340501074140c900c0c440340e030f070032501a1b2800c510107108500200e40e03c1d5803040c0018042d0b000d4500041382c00c60701700282841001064085501540d41c440780100c201c010707401460510b0300030b000100055840385001c0d1441600800000400560765600c06040f280b1260040719854000700e03a480c1030540a01c0341501401c0c0c01c1c204106a41c06a080404030008103000da011074a590b0107141c45144194402d0f02e60144200040b81c43e40b0a03118005400c0d900300328402440b81c90038244503040561b010050726940042d5841d4a031107000303da464040030f90480480058040824003005a01d0307503040041c14002e030700070b082441c890f03802d42028042c540c1c0c1d01d400c408502c0c1c3c0b0450041055200802c1142c80180e0001340026001d02249400300a005c0c0e202c801520354410f42850009c0c0042551010140000480e0010069541c0302e005603a403003030f0740354050490b060003214031012a01c1138100491000c1c0074580185031007100f40018007 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 56453717 1250 56452467 56452481
    0x5060316060807080114030604080d0906060e010314030406050403080f07080706090c171b1206010905011514070b04020f040603050c03060711060106030b01021e1f0c090605071104 79
    0x700103881c103403e22541503004403445024190008183c07a81c1000b2002180c0d80300e03005440200300540000c1d500d00c100311190f0110040e181d000c0340c1880030558404141207215800e0000391003038840343d5801d000c1d05900004032401c8a1580c2c4500b803d10b85541c45a00c15900004c1c4054034080e402c101c1e000010308028000d00d0381038070a0b01c0000e2515000d00784030003004a00c0d0401e210807214054403500a410008000c00c40b811035400e03202c0c05003d0031012600001102060900501c90342001281c810100e8001e203041e54405403103c400c1e008003000403100d89124140c088040306081064102145a1000300c990142c0080e040f0340064207804049004c03200b0552081e11719802071507c4800502d014440c00307800003090b1900b801c80b41c40d00700c180c03a00e03040c043c40341c0300034150b60b00301a5025900901210300c400b004415034113030603e4402245a1610100c90000d0045007078110101000c62052003900c20030320300c07655207101c02410008240c03007036806840192540401c1440c803401c4c40d6260302440c2 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 56454967 1250 56453717 56453729
    0x1e030121050109080d091b0b072604080f060604110702010f0201061505070506090c091303090305010c0507110102120d150308070f02030d0e0603131e031e020f070905060316 76
    0x1840ca0150a020103907c6215142007010030186604008011566007910b44e01500003250007109034400161015984425035420580030001c01c00168480001c80c610380102035490943d0615030340d1a0402085a51036010a05034450034401c02c809544250015a107011582c0000140c2c140c41d0301d08460302080344450300700058000a003007000c0181c01c0c41440d402c4500c203c010b00c0440300142c00076440c070000400340c680c07032100b2103580b50915104a10f03031802944c0200080017503554290005015920480041e90844401101441c1c42d52002134608031692142040e14100800c69803104084e0203c1c41c60300010181d076003804804101550001c04a4a01c41c9581507200020380c4141070400201c00b0082c0d003400701407410300034180c565508a0358420345c801c0303d4800040755441c049a1406600302e214940d10549420202015008485090000d41840382e50181c0e4000a408030b81d5030612246e05c0c13103650404101001a4065a003107250070140080686520801500040c0e6581c100c5501c14 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 56456217 1250 56454967 56454971
    0x1205090d020f070f090917030106030b10050702030606010e0102150108030417070602030405012303040f050709020705190311030c06160c0305031918081e030121050109080d 76
    0x40d04035404102d51066000d8030030280800d5440c1401d02d41040320544500b01d81640c0344c082030030800c0507042e0910950310001854507140d51319032800030f00809081c6425405518010f402c807005501410550701580d034010024401542c4450045501c01c4e20145028198840c06202c056042c2c0c00022650281c50007200854540746421030b5200c54042140e1040341c82e800400090081c10303808801c98050780d03000c0c207001c0041502906c201111102c2d640300c5071240b40010040c00100805000001c2025000e003003100d08241d180d02800049200d007510041c166445501d2300c007079001d800f984940c112400b9042441480206090f10383c2140d002c400b464a164009200b000b212034000080800c0c1441c180c980010b4621141d940034040303200c090000356598442485103a1586066040340c180401c00810503110500d46180200894000c420403c440c40c0b1b980410354200c4941c036064904841d80b002400c07420040c41960f46040904075141604d10355258281480371441000040596603c80000 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 56457467 1250 56456217 56456233
    0x1060b04060507120903030f030203150402180102060c0307120b0609030105040f030908060708010603051005040c02010b090a050f130f1a040201110f06060f030312130c08010c050d0c120509 83
    0x209140700d58003e0078051217244241840440d41c0101c86920300c1100d4200180c0ea501c8840070401d600180c104c201e41d00a000281882c50a840722803148503a680a0f000c40e401c40d1911076502c210303400110786542c00500d68112110001c5110342160703540300c0c0060011032424445901080c292242158140d518030020400142015480041d1400811004025042904000c03400804014040c4034910415440e4001300725078000c1e4154440003800000c008200f4098820000790182208000145c42035030f0400001d0200c05007801400d10414208660701196560050b0b280c405030058081503512500001d80940064000130781d12101041c040182d5031a0f19007407000511f403241c100c440d41c070300d9042842c1d000c01c06140020342603041360381282d60003641500c04003c2461401580045450541c041d02807041c5501094421002d00c0e01400030200c629440d145c5041c2603903100c1002e8000034104005903010521140d02c42112440300e4503000031040881c0d403801003510f00c281d8a07228a81c1140003 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 56458717 1250 56457467 56457473
    0x512072109030f030f0e0f16060509030c12150f0a060506280c06092006070803040b0a06030b04141e060c0313050f06100504020702031b0301060b04060507 68
    0x100080d40e00c44603150522002500340d030300612608410101c00d0a0546541d00080204400e8018880342c0240004039212076441c10449075a822081d903121181c50310000707022400ea40703d5806c6901d848030107001040410403090501c03261610400b0b401050f0301400c4101d5080500714003015015085081c4211440c0c10843d81c108102c892551046106071010055401070080f5010710300e01504090b45d100f02c1c0a40321501c1070b035422480c800c0050509141c42050000c00801c54581c2c0c001203612085060134003100810b2060520864502500c10441400000c00140191814581c000b65550010608076540c2d50f8200c107600050300d08a5402d034015010010b000c0c0d00708642d0b402c60500500b2410080c4020340d86a4031100c004c0e02200781f07510000001502c040700400034030b81c10b5a00204031a50700071444001c0340c80303540644404c0366203040784200282520b45802598262174000740605a403440141e45040d41c44100d45445405540b0f0340400942404060040c0c8014400d80c0ca8150340d4581d03502d = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 56459967 1250 56458717 56458757
    0x100b030a020c1006031a09190606031b0501020604080a02010605061204050105061e010305041b080d080901060b090f030106152a03020a0b19150312030b010509010f051207 75
    0x1120f001000f031034580b04001250420700c5100d00800541020780079501d5481701181060103074450460b01d00200703090441009285d074440300c01c0301e0040840301d200701540310b0108207154a6201b8540142e11410101c2c000c80c601700e009100f20301c1180000900d960340c0ea0081051600701c0010700402281c0079040005004081c0282540300380211003006100809054401582e0710351801300f0b040550380d40000702004030040c0743c1e080d50f16100d10480d5219075191440c6544d00003182da080e00250350400480c001c44414040d031800c0c1c03004001030340c0c2840c01d00028005850403100841d81d01d50740340d04001400c18204003d040501c1c0141e035442c41a1040d280061089010b40c0d0150a104200e400003400483e40c0400c100b903a0950001d420203082c1c031585004542d51ba0040e0948441920780340140c071242d41524683d2042300d2203030401004202042e04180c0c200e800d48070b80c00340820020419003c41d588503030203102030419242000c5040101440d204142c88804496080104002c1c50301555010001 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 56461217 1250 56459967 56459983
    0xa2a050f0f030406030c0909090f0201110f0c010f0521090111070f020603040305070506010f06031a0907080a0906060b0d0608030a090b1c0e0a020913020105040e100b030a020c 77
    0x4680100618040001d03555943d2195225078000c06594411700403605101c1d061010050039100000c1c42001410f04181070319003118501203010820203003101c1000034000c6809845610032001402d0440c202d14010b480c1c5405d18641c1c0004c025080109840e0405481d032031061120450700b0b00800c5d0700d0280d00702c501310380661040000850f0240001d83c0040e40460f00c5c000410f5040c3c2c0c07215120b48a5107404e8519000d1000010301a001d040300105010038102400412a103541c0d03130901c801ca201442807003100d00610001c6810080e07080c0004c0815000d8111b1940108840100250122043e1100c01c1120007a40108500d00d2000030007400301c102900800c000f42c1042c0b4007545c500380c2403d03400340606116100d1010f07010004905041ca44d494038164169000101c1c00a00c00d40d000e00054549545203824100e20404030003000c10b0741c0215007649200401e5060711694582814055500e0280800034405150361411210100d8508140e0307000d140a044204000f607101c0d441a00c000741040c2c01 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 56462467 1250 56461217 56461243
    0x614040507050a0e0a1d030c030901090e010b07060c200a02101103042c090a0b0f090703020d020f030a081215100e040608060117060907060807050a2a05 67
    0x40b0f01050069000420000740c00102990000414003400e03400701e80072982c1d4084241182c000402c0d901a4848003000400b41800300f41c2c8d50610554a806844a500c80d081c082d0600c4840d042c0407410009045a01032030021009003401d0340d00d402030300c09041480313240b4060b15685802488038038045040c40072429a48402340d051101d858030707420303c20582ea07000e6489a00c1894040a08807014240720385070894601c07103222090607032441d003030301200d6031840d001e0012240380c003c2d40e00003801c4900d80320000d4094240107014040840c5160200540800e1002c816640f1a1260309c0a4403542d804104540c0000d104a283c2d648503000c007528560b40340002401a07901125403a12200c4640d0780c4503e0307510480c1182002c4909038410301c0810010091034000754900d206072070000c280340915103440246000c21404403511344c1d8800c02c00944540e924880ca0020a60803404540b807140a5800382007521098580741500625803803050021441c200004490b0204040c60a81440014010801d174050 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 56463717 1250 56462467 56462479
    0x1e04111302091c050312040f020a0608070221040b090604170601030b0f0402030a0b2707050a21030e030307170d05010602390d050c010e09010308030a05040609061404050705 76
    0x38040e110281c51b4802c0f0f1140350314261340341c0001010010060980b02e241c5402802184140e84c461b00c0c068a000000d0310880c0241c407500810240c25017100c0780308800b01111032005802c05203401c078040500c1d04049203169205109000101c0c806140c109151000d00c08440244000e514504000d64070b50304c06041078420504040400001d80c40000300000d85660005040c074445d500c2c00302941c7c100d40c280400035032291041488103001a4000f4049040e00c00464610080641d20600025440700151052149072250f081c5200400d001e0242c2001184000e01600c4c034151051f900c1c0504211003000f50758072004045400301d441d01c00c92085a015020360b000034200242081c2c244624000b04055051002c10809500884100c000302c0b80e200856010301030003070884e4907143c4203413507081d001c034071038001000c03564041c000b454070030640b504880c0c1092619295407a1040181c01a1500400c01d80d04180c403080160300041c91440345c100700b00c2d01000c008a0381c0c10546040c1741088559400a03200b00 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 56464967 1250 56463717 56463769
    0x1020a03051b0406050d0e0d030b09090109050c061303290a0209030c090402040e070e060315010e070c030314011211060307140306030c03190302010f051e0411130209 73
    0x640110454095130a60306100e5101e014840894020300b0b145075054580d8050b0700d090701801c1e905074110700001001110096215560f414080c1d013264400c600c09005580080c21408503400c1140082183d0340c030302d11000d05501c0c0c50352910089040c401c1c400d0340100703c0c21036080c07800b000d15a03805900000e0600d400d51900140500081e6a0100000684d11608105c80401c04655555008401403682c89003034600c82d80da01d00d00c00c0001001210000d000340280319018500844030200281690895502c184007600c82000480e4408403140f0100c06043da00d03a1808900b03007046201600030150150404041c004a1908517080007000c0700d40d13030013481c050050003043d83d00301c441c01000602e20361100d5140d603181b4001915096000c0303012601402910300140c10400c1800d140c00e00140260000e005102c4202e075640d0448404942c0360324114001c41a01070303608e050050103034105010303403440022000500700146114014049401c000d607070000301000c1c00d04201586010307621550266580e80 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 56466217 1250 56464967 56465011
    0x50406050306060a170a060501030b06040509010b0705031e0a030b030601061d0310090506160206010810020d0e0106150906020105010f090903051603030203040201030509030306030d030209041d01020a0305 90
    0x241c00301500c4180305480114500c114180f00f070395001100040007140c00c626050156440340281610300509002900f0440b4620300d80c01e1040c2110304541c0d001d03203100760710303840d0100380c400701e40110404480d103000420034407603041002c81c6100074260402043c00e644400c80c6002900310707800354006a0180e040b45004012094100d2100c0208181107840840b513a03500e900041e080607604060221818905122f940c18030500050152040141e0b4652420128801c8010303a9110002d100d188025405041015030390302c0075030041d00c9144490003003c40d5102040d65090309649950300800100440c03000079400e0302e03500608240c01050680002c03c001e5051400c404030300d009134000e840c1019125000002094851401c0324844241c40c001c49511403140e190060103540152400d81c002030404000c100034440200413a0302070b01e002030050540c0c901ca410141c004c2c1d0072409009500c41d030703a0344070707500101c0440e170b200808400100c1c0016034843c2d0074070b03018040715409451040b18150301c840154071 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 56467467 1250 56466217 56466227
    0x50601080a050411040203090a1407090b150904150e1509010b0408030304021c0c0605040503070e060f0103050912040e040510050106140c01020405060c01020307020106060f020307020d1106070b070f050406 90
    0x1444c1c1c080d24050b80c0d03135481c2c0c4c9007135152000d440002014110494503800e0f4007800800c40f0400c0e1032041c2010701022203603600f0082d540c17110300840451620100000c100b940341581c8030f820340f413506d04008001d4039640c0500d4030840f002204c0c4040401424050100c291038200c03c51400350000c07085250070305082c84030540d074074000240028014034220b80e20b0364680080b0060410360350b03401090b43c01d10b681c031a240101140c01c1882864068800c1400c0420000103c2c0d04880c4155005840704056110340b40045020b444040d01d100c401b0b00610f40013110701c0350608024005410140c80300002800c2c20310b029403801500003501c0412503d042c00521201d9401244c01c003410b00c5030701c10640c481082d106090700920031a4000ca0b40030a0001340d08050078019005035105052036002040b003541d580c0400d95403a5840c80172080142c1041000a0040c5046007039041e406000c0d403824015840294045260f55022000640d00160722070f003004207441d1f0016080c0c0000340907142140c1028600700d000341c4 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 56468717 1250 56467467 56467493
    0x316020d091505090301020c0634050a050310050307170f15060d0501020d05070903120c0201050f0705070806040501060302100c0308010e0601030902040f06060311030c040e07050c030d050601080a0504 88
    0x403c900003850140a60703007501a40c0721500740301c090b03404c03a042801c09145c17418640c001c4e203601c40b50311100038500c1c12001e4042c502c0700c0d412900c84e685080107140080710035510051000c02e1501044402240d192000c02246004e40811001d1032100200f81c01510325145880307403424425801080c0e82005c0c000f0280d06103070000d100740c98010011305a0719007140a40640c505007a1100e01c0c0108100c0d01c0c80c0e100c0e50b01000c0328040d40801400240a01e0100ca03990101000a0b0100301e0411604811824010041c450280280180c1d0059910307001c0083c1084802c1e1400c1d20183c0d1039260a1041d85403510b0615140e84050038207406130355a170364020706122014404d000c0c240706200001002d0b40d000350442040b00d54000c00030000c400188010400a00d120f00031180000c5c90151040e6909801400700c17409901ea41c0441c508007841c2520000d01450000d24500c1000414444000460000c00192583c8840c541010515243c25800140091001000c824156050409210110f070128074050 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 56469967 1250 56468717 56468759
    0x7020120041a0307110615040f0b0d02100302090303040311030708060118150803070b040b0a0b03030f0304030512040b0114060f09040902010504050a060302031b0a08010e0703110316020d09 83
    0xd0f44130390740c0b0201950109008080d440c0a40240010481c403000314044049811504039010000c60306241c80c5042265403c01c1e0558200ca0301d40e49807005442c1018071041e15100605c0c000d1f29203440c1c0000329003580c00a510888652029950b42d40403481d081c001c07000074050180080101d98034004042c2e911900c0b0801103452160f4030740c840b00c1c2e2030541800840180032100308581d80c8450340c0c03401101c4054101d40517146641d460002c2070302002035005138200882c00078015030801102130005c0e00380e60300191045040c03100c200041a003499800203c1c6101c1c1e4041c0c082004607616025058480c038800d40070b041e205003800c000003c00f4070b214005642c0300a501340c6000584c09820b10050300e207403140e60001c0c2d9014250a01c0040e0807030303254000798402c12468642d110401d01c6403603001810b004200e0381f14041014100140003101c40c0620f4181d100c1d075a0300d0045540c9402c0e0080c203280341d006031540391440350040442c1c60385d650108071b5540c82021510384403d600703160000130018000e00c10411 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 56471217 1250 56469967 56470019
    0x10204170a02060a0315031415240126010303110d020a020d110d02120c040e0706020703030503190903110c0a0b041203050708040609030507091e0b040905060702012004 74
    0x5210394141c100450296900008e4882c14413800152144c2c0c40f030400b4070b03100c0240440c100103040b4882480e407058040900308000800e9a40314401965504030080d0000c807503201103400c0d00e844240d50520b05c0c1c000c50098942111203460580c0c0b16050421a040d10006d55015049030700068440c00c60300110542c0101c2e10b10040a0410005410700001e044013035030000704040c91400c41413000c14945d0721040c0c00c950400c03501c51307035401d0503851710464492480540c0000c41e041011034018001941e019811880c2c040140040b40a407174102d51311800107500054040142124254080281c0c0b0311700001244c00d8002030b4a840007816047c45036010b049802144100d001003014055001da40c40c4070391080405445580312440100759988500c8251440d20400c840069083ea143c4500c041442c415010303000c4c1000ca0250400180c035140b0000c0b034000740e44006c1003010600034000c55016174429400850046403005100d03401c004103500500c603102d000c00c01084101070201c900881844003001d4 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 56472467 1250 56471217 56471231
    0x30b0306011203032315010e060f030603160303050406080c09151e03011202040b010503070e010f0c020303070b010501030c1110050a0204080a1103010c090e0402091b040602010204170a02060a03 85
    0x300d003d0500c51944002d03040c1d17540d02510b80c4105e0008000d00c541018907031290300801540c011100b00c045116525007040d4200f00a4003c2c401c10300080d94000406021103c0d003802c1022940502440d6038000c5d0002080842c0c18000654006070a1360003940b0001418100402000003980303c003811072044006050008480008004180b20154820f16103801c3c580c50b581d5800703007c80344250a1404902c10741c0b818035015207d40c011030942e40a516035641e181000c41000e4015546a4000404002031118900c580c02c01070f036081006141c42c5104456100c55549014005400d4460740072690b4244112108541501301c00000d10404154031480c010806403074000700030300288660b070404006406101240390a101c80004ac1856a50060b0004c00c2503105040d07044540007481d008426030314106030046400b6241200710749400950b4184146121030525080354546e5101e98401e80250350042400c005003484131951084000c2540094625058503900141d202c0c458100082d0625070340b250 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 56473717 1250 56472467 56472473
    0x2539050102033c0c070b070f11040b04020706020a09060801050d06050c160f0c0b1911010b09090a141b09100b12061e03100207080702031e060106030b03060112 70
    0x14041140c841003016610580383c09805070b4250b501140d0486010b00c81e140780068400182c5044942c103d410046070301800076140ea6081728003091828007603109445624100032a0b813584010b0103828820302700160347d079844641c0604010345c0b0790300c65024001d02000402080d200d4200c294a01035001c0d00000301075a078072550050902503003054078a0f16001501090030006d5002080580f540904c0041c40c50303c1d52654440c156210b642c2040d0303e00c40c684002408282d0088224016041c0084004030340000360001264040008444400e47caa110748070038000c2c000c192080740038102c1244d01030728155010890104103035641200d01401785c4a00d00010300b402c00920084ea015000d500c2406544600c2c80b46190414182583c0d140d00c201302c3c8140701031100700022030080400c00083e02500601e50340f6010380c00250003843c4107480e5070300d0130400100149e0f8248000034040b002e040328400809200012185030001c1600504241860b250220113242c2d40000c00d541114070034079001c0d044808900d = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 56474823 1106 56473717 56473777
    0x70e040804030b0c1b0601090b0913020f01020f01060b0307110a020102070302040b0616080a0224010e07030f0516020c04060b253905010203 62
    0xc01000080c8011100ba0f60042d0644130341d50410b4030703051040c12000c080406505580d04404014018846140f140060801050b80c10304000e182800c4900c020588101e00680700720160049407849030310805c40d07051f0302ca21030780090251030380c0c400b04003419800a03517103440030070160038010310a00c10010300c095802c0c0d0168010250310345940c003400018440e4004c1b85030005400c00607a03002a4008203920b070b0783e0303202d1310320701d0b640c1c50600707100a0030207140110351042c60858071000402c6540f030f00c1e138440c15501014020801511280d00c00e4004050080c4018805410407040000c5d02d500d070070300740c203e174411038003646c2c203c100344410402140c7c1b01c0e00a02c098850240800c40d05d08194512403944a61100118401601c16440305c41201480032100c540d041074011001010451403510450034580703403840103804a06080002c1e480340034813044120b40650000701200b400d00a4 = true := by decide +kernel

theorem cover : BRFrame.Cov 56294967 56474823 := by
  have h0 := BRFrame.cov_init 56294967
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56294967 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56294967 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56294967 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56294967 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56294967 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56294967 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56294967 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56294967 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56294967 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56294967 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56294967 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56294967 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56294967 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56294967 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56294967 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56294967 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56294967 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56294967 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56294967 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56294967 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56294967 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56294967 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56294967 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56294967 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56294967 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56294967 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56294967 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56294967 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56294967 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56294967 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56294967 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56294967 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56294967 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56294967 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56294967 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56294967 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56294967 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56294967 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56294967 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56294967 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56294967 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56294967 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56294967 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56294967 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56294967 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56294967 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56294967 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56294967 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56294967 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56294967 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56294967 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56294967 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56294967 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56294967 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56294967 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56294967 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56294967 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56294967 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56294967 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56294967 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56294967 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56294967 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56294967 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56294967 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56294967 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56294967 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56294967 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56294967 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56294967 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56294967 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56294967 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56294967 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56294967 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56294967 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56294967 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56294967 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56294967 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56294967 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56294967 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56294967 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56294967 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56294967 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56294967 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56294967 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56294967 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56294967 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56294967 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56294967 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56294967 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56294967 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56294967 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56294967 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56294967 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56294967 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56294967 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56294967 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56294967 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56294967 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56294967 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56294967 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56294967 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56294967 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56294967 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56294967 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56294967 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56294967 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56294967 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56294967 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56294967 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56294967 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56294967 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56294967 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56294967 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56294967 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56294967 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56294967 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56294967 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56294967 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56294967 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56294967 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56294967 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56294967 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56294967 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56294967 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56294967 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56294967 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56294967 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56294967 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56294967 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56294967 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56294967 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56294967 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56294967 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56294967 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56294967 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56294967 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56294967 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56294967 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56294967 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56294967 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56294967 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56294967 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56294967 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56294967 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 56294967 ≤ n) (h2 : n < 56474823) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
