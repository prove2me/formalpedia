-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0765
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T22:39:35.044909+00:00
-- url     : https://prove2.me/submissions/30c07308-ef99-4e44-9d33-a33eb1bcf6c4

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 137410071 ≤ n < 137589928 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 137411321 1250 137410071 137410081
    0x81503010e030a0807020727150501020703030c02030a14061b0a0e10020a0606090f0506190501050703110d050c06090c0312160503040902310303032409050601021014 73
    0x25411301c3e60408901e1045402280c4c0d60405604044004030b0480031030b4941d44600c07503800c4061b00404140000404805031150325290000c0e41c0e07003c803407100805014402c25480151b54040c03244260140e000800303926811111003031651102c0044440803c84010b414040d8107801c0caa2069070703590505600d407200c00001030402c102500421510030011449507010032000540e2500620340100841000403a42c00d80041c0c10380144c4400500c12802032501e4664803850080e03a12050701101e00a0810540d00c01c02414115060034a1807100266485a28403100346154070000410b00341d048203041d12000e80701d44c031030700b0f0300c0c1c1e10b07a07081c420340c55444440741c12010365068000b40000c40c1c09400d01440841c40f0782d01c00e42190030541c4602e440701c2d8040380c42d03055081015040606614000454900d9600081c4c09000504d960f002c0981010390310200149204070034415142ea03090003030145002c00d40c0e94440c08000c4d1100b110303024011700616015181107522802800c0c17590403e042e4850882d42c41d = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 137412571 1250 137411321 137411327
    0xa0614010c080f0f0c06010b120c031314100b091317070606060207030303141e1305250602030325030e030c0d1b0c050d03022407032003070c0204020903010c081503010e030a 76
    0x10140601e082c181c2c102133004000f6441840b10406030101c180a4104080c50010000c1100d450429242c0121101c8007001041c400039207034000300340d134050420b19840d05402c8070a0002d00659100820a80c5410000724860b600000c1d5801101e00c130740d5042c049558060f400c1c0e98581e1054401c05035060340315034504d059010b180e078282d03444040d20003041c4015040c0d4491916082030104803203412142e0307660f45038030b078040108500f020304004c1c0020b40c91803c000300705440c00d2006119102c00c2442800102000d54441c2e0440000d401c0c070350f004c80b51210018291203031103824030000b03140407540c0e024800c60a0a45c01c0c18a14000c3e41041d0040c400ba0300d003805201c0005445002102140141c41050380c0e02c241151509400c1028603034003040d1840c0c0054040c04850402c1640c0700d10314100c49802080581d49011694094800d00c0e064a2500c40f82c8045400380c0122140c5507455401d00a41c002c5465215618070b200350392043c83d0881751940742c010b040c01c0b9207084001001d0398204020f0a01c031240 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 137413821 1250 137412571 137412577
    0x90f230406020d0f0203010302030705032a0a050a03030f0e01030c090e040204090605090f060601030902101b08030a0911120304170307020307030312050a0614010c080f0f0c06010b120c 81
    0x4041d41000d071400a0304949101120811036906105940c00b10041c400d500302081020098203094005000d10542180d269254980000b150002c06030040c1d007455081e1074090741070700104800f40c61040c0041d141e140c0501010201c0000d48000340c034214910005621034002c03281d02109607206c1070440d909164481c1a5188010416a00310b42c0359030704480000e2103482203901c0369101001408050285154180c00c0c0724010f00000d04160410142c100035039600900140e440e4000e00b401000c51540070b185010b0b0b421004809030203540d0110402c010942c071b0b90042c2100da4828842d40803003010780300400403520703261500d01d007040c1d01c140000d1088401c02e14aa007120a1f45904a80c03c103550783d030000789020034541080b000a00f50b0030412058620900071249c10100da4442800341074109824401003840d5132010034108200046040e0601c00c0d42e00c21510300748200000c503a0355002200c6240407680c003100d09444941324441c00094503102003015900d059903604008041d640300d5005404841d0 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 137415071 1250 137413821 137413823
    0xf05070905100602065202030301030201090605071a06010318032319080402150301030606030c050303070308040305090d0b01031202120307020309040902040e010f0e0106060e0d081602030303040507090f2304 91
    0xa4600340e007103d024003186d203282e444185980115601c0d0306620004103d80d601d64010003d105041c0030640005803c3e8400c000c201401c1c040240300da03070360312004030085d2030710b02143e1078001884d424180c28154000c1c651106481071901080880042c4491841c0074469460360442000740042401c6085110300c0c101c41e0824001040b20390000e00c0c8030300e0140d00758000c1e441140c400c0e80d100003c00030003800511500003010110040c0d414244070b83c602400c0c45000030300040411900144c10916985c403001d0101c0ea154210b40401410342e183cbc07a00b191042c0c100c80c00000544600300401c0d10140340346049911406055024604002001061001406008004070380c065114075000711610400d205080802d50f03034840120310f0145224125007101c1342d54000000304042c03049000105d0b11000c1e04880701c3c6500824180d6103903100d036142c0ca0081030f5140025032500001060009102c00041c0540581d20181002c20242c01361132440011a098000c01c0350a0b1120382c03400319035940e18840b28940c01 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 137416321 1250 137415071 137415181
    0x60d050c0415030c08070504081c110f03070b10030c03110604030602030a0518010c0207051201060801020a050307020115060c030c030905122b05070f0507090510060206 74
    0x103502c521081085010b411000c0c0000b940e62403044d510315031321045003a0080a1418110b10f8141081c4046403100600204500c10611100c070341c000d401d00c03a4403140241841c1005a5010b0261443c0c0a52aa80080000c1c0c0700c3e4411100420981d41ea04195242202e6006a0384260305141d03584404e50780ea4441d00042c0d00c072006200000c0400c41500081d48030358080c00c070002e2185410200262081c01444410140360300d84401c90a41c0303900000c072082a14008c64040c074100040e1028a4050031440d001400d540d4000706100340c10070342040103540201e5558009000301600f0303503480c2840110074031031072000800482e6031101090081b91640b11031402031418070a419241c00114820340420020072507594805801a005d42030b040420304120650100000f850703010985008095000d075a0018010400c42801901006400c2010f81c1c0281000315041c8903a01e0208507500d0060711500c941c4000d03000d07200019046c180c520620040c0040b803140600348100304452030340030038940301c0519000 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 137417571 1250 137416321 137416327
    0x2d0c060708070e0409060b18161805030a0605010f0e040b18190c08010c1805040e101113080d120e250807060206040510050703020f030a1a010c02060d050c 68
    0x42e01c490281d441744500500c0e000c50041409024400510101c00c00310030240050380a200140464012803810000140790481c0410303044242c04802e5041d60344696494440d1a40410421034240c02090480358180d1421424554820001d0304000313040741c0082c100e00344000010f02041c2040da001e08a03981c0101210b01ca0031481d1383c00740007074401550554240004d01810810744009014181540085240030160015482d80b0041590098010704e44115220981075194000c1089000c144c2144d5002c01d2000186408440c1c80345d6200d0110450141e074800c0c0c0100c4c85400c00581c3c440950241c0c0da8200c40490070300780c000300600300194800114010034010300301081c2c442007443c490544821003585200d261850040c47d00d503641d844041590007510401c400b280000c590424000580000464a40ea600400324000d21903004401c0301d50401009008041c107a95100c006070164109244280c030068800541d04800c03d00b0700258004d804020710203802ca01a040307241c101010516440c2 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 137418821 1250 137417571 137417597
    0x103021e04020a080f100303090e04050307050d05070303060603020f07030809031303050c030106150c080a200115050613030f061b0f080106080c0a0f12022d0c06070807 74
    0x2d03644000845400a21840284100d0103083e02c3c000f0b030403081d00c4074125012840d50794050106d040502c15020000303810307400141848000d0084900079513000050301c24011820801400581110384c0540009140c290080380441c028030807150040000c0d4102401e203401070f60200e401213001018600c40e40005d0107002420001e85d80c66802440c031640241603528085014142164501e6000b0000f12204400c0c000c001500903141c8100fa58101a9031030350b804040784151545000c1c4d41d5a000c40e4600140c10706944841036101d10070300750000380803511403950340701003160a0181c160002202200c110040002410311102021820300c500030118082261800c101d00070480703400d81c5030105001d13081c02607a1607480002c8a02507c19030510051b0340c184551054001d004907074620042c004c4c869075a07508540901602007052034100e400355500e0540803c40c203843c070a0200c0c001c14100601140e11000000c0e1000d4032400424030000b00703555a11f408007200c0d0a1001b80203c3c050100701c4400c69 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 137420071 1250 137418821 137418829
    0x1302030709021611040908070210020109020a030c1d01060e010507050c0303031f15021018020d030504150e030309090709090504050a02090114010c17040e0f0601090512060103021e 79
    0x419048880c151000260000d0300f4890901c19504113010300c101c1c03070011030000040d40407040d00c1485806030303640d0341036941944c42079004000c1e885000e9440f070b0403e50300104001130380d10182c09441d00032000801700c1000d015507101e4424280540000b00340030341030085141d40b0990190400b0360045040361b2029054002183c04c6900581d00c240700700017a0300712003085c0a11241400700808441100e528039a8100304029181c540c00c0d481c00400303a4079200300800d81b0041c0c10729010307401d400034291000b55a0354500902998414800d08028605810ba148407150040c005040147e0010f009503240c5100c8004116000100070000c109201c0d2121001c00d03400301d1803180912441c490b5000b0640c003203080c010000c201805900c00c86050201c524400900d07644400258816507010005030154104040c0410301401103403c0140c95160b980304001400c840d9018603802a402030729159200350700c8005200c06030040c09000d080940c4684010001418040c080609070902401401e4202803541c0000d = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 137421321 1250 137420071 137420077
    0x40f05011403120c0a03140705100b0a080d050910051b030a1209080909040c051503010302041802060f1303231006180203090114040317010815130203070902 69
    0x500319007400c0e000e0480d4500b420004126a05079080700d03541006003402138580da40345201c1d4000c041140d9a0112100800c12905880e141030b44007003a910344940c0c00d14082c004050007840300c0c4c0710794184100024400ca01040c0341d10300d1100390b40d0300b03443c12080d50103101980702041801401c1001c100301c034691000403144003080030003052000c0c65840511240042c900d007105820428910328004008000070300740d4084915888040c0e985000a607034500303008805000e903600c6103400140305401c1041000d03644000318181c0340300300c0d410005d01c1c00c0080c1c40803a1103d2844029080281040364111100211000d00b4800e003140071105507076505c0340c0c0c5203103a0950031440342080004007201c81409107803e108060030400c4110342001030314580100a1100d00b1011000050a83e000000c9800c0c440c00307403c41c4070030382e0204607131400fa401c061074014400c0c1000f40c007c0ca13214091030008107840c08040b401c10309c604411890748115482d20440240391080c84e180807030303061254040000e0084142e00107 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 137422571 1250 137421321 137421329
    0x5060d020d15050c040608010909020a0f120b090106050102030327030a0f0206060f150901050f2802060705040303030b03030714010516030908030a0c0903050601030609020f060a0c0201050306040f0501 88
    0x4003407544800c50115080d2500078202c1e182d007900512086c000f103580404824112801d980e4041030060850000c40c5000c1203940014001c0311400300b0100e07083c0d440f48070001c4414840c069442180c0d85010555080b1003075402041d0058000300041155000001014440919200380d0302860281c04c1d14800d02c0d43d0f10042824001c00c007071017405400d0039018441154001d1068669010100c60b41c00000c60304110034410581d40540402c11090340d91103481a602d803854058421a951081905c02e0340d1041c11111400da688551201e1003ca20703480424890f00a80080d180c507030900703041d558103030080e1000c81c3c802c2d90148001d02c280004504e00324911050071b500c0340000500350804a8010494501c8900b1000625090005007030008d90140200c951040c9002c0740003510f20300c1d1200c2140c45040f01d5002900d24800c11001006004241d848050628801c07907480179030442c08803e118090142c00411404118214410400344d405500295484400240700007000d0604107168070483e102a00 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 137423821 1250 137422571 137422583
    0xb09062b0c0f02010b0f040c09050316081212010b07020d05031206040e1203010e09070510080a051503150606210415090503030118020f0f0310050a150305060d020d 72
    0x45008515600728000b210b01d14081d1000784402c5194001203101500d9074401c06000d0360361000c1549415110300000700c044d101c01415122401c80c1c1e0089080161600e002d00c0d04107002c2c1301c009030301e022038000032603030394441d02d6800f0481607290100030035050b00300e00010307a00001000078090020b0418002000b4469800d8484d00300360400000303200440c0c42580c4003000c9944090800300c80036664005407411034102900c0000c05903190014541448035a5200540003070b11141075185c02c07500300400c17a20564485004101c650385079907030180c849959540340c9d42c01da00054446252055010768003036202c08090f00e030516000114520501204440905110300304101d8140410400d0300e4611404a21488906000481450f110305440e48010720950200d2006594002e000e01019016100c00210f410080c42c0c858000004407001c580c8210384071400c0f4010460702180754a41034106c4426103078064010a0f4183c6a42000d400619004e02072a80c0182c910303492100603510a040140c030940316074 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 137425071 1250 137423821 137423831
    0x2040f0603060f15180f15080601031205070309031202010b130f0b15190905030106090e0607021507030c050706150501020d030c0206061512070504050a0605040b09062b 74
    0x26603c042150032019401e005002103000800400d05580c00740300712490402d4001402241c071420503c000c000e2032a281080c0d03004000005060781000c036100b812a0301a910035402c500c000c187c00c995a1280600c02000714400712410320120301800c2400e08500001d0000082910000c400102841e4100d514100c170662901c900816040c0705016284032030b442650b485c003440281440e0030586028960840c05091868010f903070740b44d44103182c81c3d002020040d000b0051143c5a46c17046002d02904c0380c82144a00c16000401d0380640f00041071900716600c0001034425494202080300a03051012400d001c114007801014085503903880740030340e42c40800340038402040c501400a403d0111190382d036420b040c03406074107a07411030300400c102d580010103c5d00003080c580f0017400e407140350040843d051000101c5604000b0030540200007441951412210340c01265500c00c0100c40324440c5001c1c3c1003040e08148141900303400d009000c0c1904007280d02d800c8400c8401601d010410b07046400501c081d4076220 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 137426321 1250 137425071 137425091
    0x6360c0901030e0102040b07060b06040e1003020103050601110703060f0f0212090114040f150e0f07050a050303180409140f0c090a05010b0313030905030a030e030d0206070207030303020702040f060306 88
    0x1840f07242e500b10301c034400030350a242c500b880c050994018804042c04046d00c84072408031981e9000226070152000346904440342c1403030005418120940d0204131701003451304011418941c021210b010380b9000322001031407000d080d82d55070005400403410200e1000c0d01d03a4201483d8241900113410246101011800c26140546042e800d540c007503681c030760540c0c4203041444081504c0c40308400a41e50003100d020b00071124a20500018024103e40c0c601e580541c0c4081ca1407148080382d190200c0d1303021901c0d40421500c43d03041546070310445080d802c5404400c0340040300c90a107070700130102d1140225030402d20804074121090810702c12145240150300607481f02c02440ca0525456500540d004c20f08018540c10801da84c500c80c0304c0505124022246020610101803140340080041e00010741903517080d8400d45006001030801d1001d80b403090040e00740b0585000d1000528a10403852540102401403658405500071b512201041c2d8106441d01884401030800c0c2c0242c40080d842000002a02c030710b4 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 137427571 1250 137426321 137426327
    0x30b030c13200408030a05090d06020304060b0112050c220512060a060603060f05010e041b050d051f0e09010e0106150215040302060c180a0e090d030506360c0901 71
    0x10008404902e6400d000901100034004140c0f454942d079428442d64580400c0000f030810304814a0040296000204101c1013200f030f5003001c81e100ca002e803900b029480f5288140000d8600848490100325003d000c2e44401c01500003c2440d650031310075905800b19102e80104001100700642e0401c140c0c8a00c052010400d41c0d80314402c001c25003464208402030502c2c003036070940c607000e203e0103040007e03404101810380c0d1203506c0707482500800b0b1040c00075040c07941005841c90700301010b555400c500e080300061218403903030860f1410066200e000e104450500007001d0003284040e000402e19940c0c2d41c0400d01091b002d104600c05403c500702c0c0c4a003036040441009160814a00500703200b07051007000d010002e6000a0915048018040c0560700c85d03030050200d921900410f410541d11114956000800001480740c55006825003000d4030b460544901c4150107440050b56216041246606601d40700000d5030038240b1101c01060028904003400e1005044202099030000c5220200042c0741803d503030 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 137428821 1250 137427571 137427611
    0x110603090d080906040305040308030a0209100e040b04111b030c010609060e01080d0f030c0e09040b060108010e1003150207060e06160906020c060903070315050402030c010905060307030b030c13 85
    0xf080e0014501840c207542d00a04c0d500039440b00905444001c40815040d140c03940680c1e0450f940582000c0035041c144000401200702c01c0070f00d0703000d0b0f4a402c240c9005402c09011b40e501169007000c1251408102c19800c01401410900d01c055a001c1800303d014510740a0248500410b05143c0c0881c5050800700680400b52069104006035032180271095056904803180540641080c2400541041d0440003901c540887c91006c2e58807008141c00c1104005407203010500841c0c0a0303030b480c0d80c1c60781c84064050829200b52007071304000d280d002003080010031541490304821a501c0015080081c0d0341d544006503560043d541805421007800c100f80c580d0002006242130b515842e1074a03040c0d01d450740180d110408031480030b0080b0000110303100306071010080f0308003d503446000000c00142103c6c49000418099504a10a0007000c044514a610070003448084d20801040140307991103c0006800802400e00c7e4550503010340c540c1c5403210740c3c540615030098a40003802090020301c81a00b031020407 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 137430071 1250 137428821 137428831
    0xc010503042a050612090601080307211b050a0303050a02040f060c05010204030507120c05010206040804090e0f010f090521041e1a0904050603011e09110603090d08 72
    0x40000d00030800842d18000e00c24600b007000e00780c010615480c0ea881c0701d0840c1c00d2a0459604142c0009034140f20070000300c3c0c0a03100d4035120040d680ca40c2d032944440350701d03486180f00250038035281c3c050751a2a680c2083c4e049441820a04003031680e8054044040f0300c41c141c3d04802c1e9455040b810307545041c541c00d4040e165100384026003c61405d400c1c0804405840b4403400344c04208502400d058041210943c11034020b10303009000c031201c4503a24001c5aa200c40c015004890700c020040e0b0009042d400014800e00882c1c2c07042c0f58604242c00c0c014058000c01542e104176000c0c0c4154654440620428800c4003014460f00001040050413030412901d000a55419108565503040400441c488100f060710295200607030380400d100c500c0120f411403524541c002d01c04cd501030090440d2211002401440c110308161000d1015030380c1e601c1018200ea02d4524248030004200d440c040074211264401450b05229849042c1d0400030310b0041252500100c0d01c074401070740607048400000360400b60403903003c = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 137431321 1250 137430071 137430077
    0x8130204060b03012904120f08120402011e08061c0b04110a050a0b0904090305130602060f0c0c100b03010e0102030117011d0a0f241a060903071206021c0506030c01 72
    0x180111107114046d100d1449545500b101e20200d10040010404045103010f0704090001d4480d100500d01c0d0601c5481a9400c0b8041010482110070f102c12aa510340c0c1c20510546600c01c1c02d6a0300006c0c001c40d0a50350341c9001480720901196030004100001c0680a140591414800d11114405010203900c2940250388141814181000a494020112400300c80c050310003040101e1145001d86c1c2c580506440f03881000340e055070204500b94009441442850403002e525180c2d21082c000354054450080e440c086500a000c4051204000360045d0140000207000010070340c080d950a2400c9801c2a005400c41d15038090000034002e07800d004003004002e950590751003540c42c1080c01940c0c1c201d1468010700307101c00754901c40709108060300c012100b401410080380c481c12a0741c032104001c2c00f0819141c00c0e0603003c240c1e000b04070f0403d1000d803100c182c0054018060182071442501c0040c0030403001702d544c10340070024800188814401c3d80c46910007000049100d05010080509045d10000c0f81410 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 137432571 1250 137431321 137431379
    0x60611030f0a17011d060423070207091805010e030f0a0c080d0c0809071e170102090604030507140607020f0913080a020a030201060b04030308010608130204060b0301 73
    0x50a0048122001035107041c04042c0d4450380001c1c03e8420081d491051a10b90a07040c00009000b04141c0815441c0d0801c415010745aa40710400c0108448428130b50001071840c401c080c502889528080582040b142c0c0129000d03030342d95028400075a800c3c032007900041c600c0441032804104007400754420341200c02c800340d070510402c07145107280e41c02140403200400480d07100d89418130140c101110b04010554006004e0102801c42c0a031507250300f070361401101e1150100000b0f00342c0c0c5907241d4032103140c00400b800709024540000c0b610b221000000035410765500700f0a03808195540b5008000948c8a01c000c1c1c031059141c00c04108006100b40c176001e0140d0f100b00181c90040c0d6a03a407000c01500411a021324403a1503012446210303595122004122600018109240940009042c900c00b8400d500a00203580c854012a546020b0344c80010040358400c0018000607001d424440c0e402580101414000b030b000d0f40000c0d041e13401035440803000d010008018002100c50010b80e411982c50f80c207280355 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 137433821 1250 137432571 137432597
    0x1508060f0c070c0302030303040b180c01050306010f0306090c1e02060f06120f06011e05030f0a020f0d08030a1a040903020c010e01030209090c090a08120d050403050708070c090606 79
    0x500c0c060050011200400c001008001c010314040503002454010702203a03140e180603d41544610000d41d0000d40b44410000b405c500d811000030f110380a1401a5240390031074841d5401950f1203040c00552409050700c9400c0492059680c1c401d030741d0724110b150307204005030494a940f01201a0b02e00314440031504040300300704500ca1800c041c41c1e00f01c0020f80b01603a150040e0703d0702c00d0400c5103094000d01035005800c000641504000808289040c00c0010b80000e80e03a80c00030182d40790105c040601c19500b08840090251514000e030b50f00f66007005d070144490b060141e0f00d060803580121101d206640d501d02040484025407100704801460030b1390104816200ca0720069690a41d07104101e04115001020080503446034040d40c80c3c0060281181d429820000103c0f03c0f01c2d0050807820b400754110034000140c0650000b406074103010400300080c60224101214800b401004000b981030040030025240017404120003031074401c2c0108200c460203810442540180c0708294001790400a0030b050800c = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 137435071 1250 137433821 137433841
    0x117070306082b0f02060c030705190f030f0b091b0910020d0801050d03021c02250315200f040b07050c0405010b040b04090e01230106140708040315140703150806 71
    0x540207d00244070a8a0f996850300031500c0344203220240a0821101c25400111034100444851840050700c0a100d040c522400400071a410000341507400303268a40407030008880f0310211052041503040725840c007091000455001d01440743c440005078001da40f04050701d40e01001c40b0f4050710088030441e00000e80c03034038000d50f10040c1c0b00010892000030055200464020016580141e4803038240000d494015440b6200350f00316480300380e40854414444503181d40b001e00c03030114040362142050384e12001c0481d81c0c00c2542c01450700c00781c801008210104910b240c4001518415204800501d00c06000e2024001502d0040e4820782030850144002c0c86402e20080903182519680c0c02d0014a031003030801203602404000300f10009591000144807401400c1100c41ca0503551142c40c9c03111060f4410380c1f20499882040c030081c001c1c0005000070700004100c1030611445080c2000d000c6011000911017124560041e00c42d0740200713a5a040707080c2c0c8404c0d525407180c02001154094526458410b0300b02d = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 137436321 1250 137435071 137435083
    0x80304030e01020a12090611160605071a040605010801140603030a030e16060305070809030405060a0f031e06080708030324031609020901030b06090117070306082b0f02 74
    0x2030a0100c0c18903100442e034401c000520046030040b0082c1c3d10140c1c1c0000140c040c580038061440003400c80140000e800100181d800580b00210340008030442c94801d04440325006010112070714843c1028202c80145003044c03181c0568020400003500d5450001c000e42104d0b000a038000d06440640b0420400d50b07404002d07980085070a050110b092025604e4007420b1804001403055a01c2d284a00440c44e1503059112501c146220b8547c0316081c0c4490b580103981e801103114260784070300204129aa03044c0300386601e601705016410040780e0400215040600c200c105900481025039842080060600402c10800244240f0300a1842c600f0909591050114007030443c1c105101400190304064030b081005428a0808101d22400c2e0707138507008850080d5100c107415a00007400e003500142c061030079500304c40d44000140c448280c01c41c60f0b401e0420701ca1100401040900d44c0e90800010075130014080394503903103684c4440811a13074110744022030900c4980840700400c0003030410006103580010f01 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 137437571 1250 137436321 137436323
    0x10f0c0314070503090705030132040816141902030c0d1a2e0504050601050903030d05090c06070602030a050c0702130e1c0c120201051501030902031c02070611010603080304 76
    0x12580c81da141742100e441c02e019640a01c1c2c243d0301e80701c2000c00c1130510034612034010f214084409522040f000802c2c010010907140034080e00d07030400280c0315680c48080c408807010b100344802840106d200e03101a051a0751028280045207a485140c0114502801100e205040403904200c04c100d2540710407540c212202d503010310805515002c03d511601b400045010b0007003145c1c08140c0ca030201071000396030000604c1068011410000802d032591300880503107692140281c010750034030780d00c0c0d00c03840e01a24001d08003e000b4010f48440c000d03644c9800004224250240d08096900d08084810000311038000703000310900c01c0305012031001641c804c0c81c410002d40c017010020441e9440c1c21005c0381043d044010001820003014000c0c0040340d008403008031000c1c014404c903045000c000300164280c2d5012507054511025030b00020f85198000d512144071903001034221100000902000c02900034490b02000140e03000305410002d0550012a0700420f001e608000d004c03e0b8656601c6031024000600 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 137438821 1250 137437571 137437577
    0xe031602060f07050313080d0507030e0d020111190b0a02250503040b1c0b1f030e030c010203010801020405030601090e0c01080a0b1302030105191406030402060f0408010f0c031407 79
    0xa40c141c5804446040d65041c0d40c002080e030755100e0243c0b9140c0c6c400c00c01c51241c4003581c083e0558001d40c0d24000c07030545041c150540c5600b9080707460342040044030174070408100c0c140072501c0e1a001500004000c43c0c1c880c0c40315030302031544888050030128a02c1c20700400381041d69004000290405040c030324640b003840a5021001c107031074950300e00981140550313049003250b64030220b0242e4003401000c01c5a04400d1078034004000029100b01840b07105240c20705042680b1041c0c29100807d10710071350080841039901402d0700d04000224800d42d099034802e922488060390041028801c5250900c4074030300502d0340d41802c002c0f004094200d036441c0c0160300103203818090844000303150a111504554003d0000400b5201e43c0313140c02c910000290401c0c06060300039003600080d0b190750070002c0f02440664500e03024120113646c07400c0401003182e00043c8200d030820000d0010b505500e51043c050000341c00c1040010a401c82d60030060390488005900c07080804d401c082c40030030708245007141142c03c15481e00d = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 137440071 1250 137438821 137438827
    0x1050112020d03020f0610031703100b09031002070c050405070f08190902060d1406120a020d030e030604030305091c120507032012060609010813050a0605070c060e03160206 76
    0x803e042e4100034003c032409040d406250108403904004844450542e07114024586050304110380100481c0001c650018024090410900c00b41c0e50200141030000d600078111340204d61074010f0b21302a40c002c0a4101c8004021742024440380c40c040c00b485500402915144000c003010000c010714001c005441034516070043c407000d040700c00907500700c1c0a4441d0090710043d6500030b035004034401010001c9104034201080304c0801d00610b0b05400a10344840030703800403d03468841c1d0b000c0000d1100904811010700c01c04544016050710180810f40c820381c001c6c0c800040394030313002102506108112843c1d2000404046804031400e420003c1404004ca0b4030000054036a40c420054006140f030b0005c64080b10341c68204400e4070020301d0000c2032200c0501d404030b005a110f4009005850090034402804140e02c0d900150102a000030000c803040d010300202c03915150141c50320001c440c400d41d1f1020014221448002c14800c00b80a801000000c500c011890080004071042c807003014450020300c0b643d000 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 137441321 1250 137440071 137440073
    0x160201022409070e1e1005041d010b0102030a05181201020d0c0e060a080c030403030204051905030f1b060702061b0303040c12020102030d0b030a0b0703020a1101050112020d 76
    0x80000741076400d4905014001ca1868003600d194014084078101d0540c8600302002c911515030340740c0d66000f64071800303590201c46040c1c00c9006501800401d00000395035a0f40d07001a59907154000c1000b00c1001160f20100b00c880ca4584600b940d40c40c50f4135505650040000e28441a4840f0448090b2103102c0c012040c024040000500d865820003050442c3d9800840c200800c180d05502030100d40900340c866130100c0b0f218000f804000d0003005a90070104409400144010142d20015644203100380340040c42d10f0f40310b50000d000114902004028448070210601550404002410b0200c011500030074400350340310b2011a092100010144c0102c83c045080000c548645081d10b401c3e00262603042036105003c00015540d0704111810340300030603102000250810001d64442c805030701030b40517600e08440111288023400034218513541600c10001121f012030401102d40740541d00c15600985d0b50700700c40000070f2040000660141051345031070010011300c8060035030101580d606441c0614681e000d = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 137442571 1250 137441321 137441323
    0x90f031e031209060e0c1c060b060409090b06090c18150d050109091208070801050411090d03031401090b22020c1c02060115200c100c120f0516020102 66
    0x940d0648070303030740d60030000c16804000f0260005d80a40849100f01c40c5a08921810072501085520040905d0300d0402040004a81c442d08514450038028003010300c1d242d6584000f104840300408240c03200d001c5801403160303625242c0012174103da0714459090a000c02c0e4045051250b003c3c2c1151403183c100709072078034018160a403d032090b401c030781e200030082981d488040a028002c1c464049542a8080c48804845801685003a0080344c09607030300c0045a003090309007c018601d40200e0100c0d0402441a03e1465071103400c11044103110781d17004181030654504001c105941a0810300000703050a101480c1902c030450b02c08849103401c4008414140c0b096417210080c070604004200380d00860b200260040c518140c0c03480a08840c0e400c0322420b81c0d90364070111709007000405002c00101c103040620f08980d5610350110114003520107a078200c540c02030000381c2404c0e07140c00600100e900324280c2800d001030078140794080086401c104280c5000d40000804e248030303040f1140e4065407d11615425644 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 137443821 1250 137442571 137442587
    0xc040e010f1508010f05040510090201020717010c020c03030f09011202090603040c1a040e040308070908030c0a060b0913021215010e0405010c09030203070b0c191101090f031e03 78
    0x5505000c004288001e5807002070381c0b140c1d000e075103415828446400200109440b440c0d2050303070800c018085030030201c003000d0043c1801c00c030164118418134402003500380303d030000800304c0722640000084c814103150020313003421509807805101c0c0d0028400c114141d009001121060742003480d0000c6845000110f102c000c0c01102007282e0050004010881006141c0c058a0265441d40c1606084848090b901000c42d11480c0180c804d0300e4440f8020500003401000502d8210416041c220f0302c4945580c01e103855508202c44e040c81c103511582d59030080c000c1510030100500401d51340d050b0986040e511003041c1d1030300c0000c001c0c029000303601c1020320300c441444680c440000802031400e06d13507541e80e0003a500c5041590241d8442d440c100b0040300300c5000b05000400c0300c0d805000362418030325055540b0fa080d0818071140d0742070700a06449001c1d070000f0b65248500244120360803800c65001c178000602441c1250805000c03600e4051043c800310f00000a400f502c441d40c2078910b5040c54151504442c0b5003 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 137445071 1250 137443821 137443841
    0x601140604030807080903060112020d03030908090316320607050a05030408060609090f0a0b060103020408150126120a0302090414010312170f0703090c0801090b060d03020c040e01 79
    0x20303401013018001c000a0300000d008000e003c800704c0d84143d8031100900075040f131118000350300840c541c0302c00340000c1c043d0f0404550640034003109424002d0000109046c604017000c01c030039400c00c0000601000c1012100e41708442c1c207403100e0794580700d520007034210702e10340e40c407049440f6810205113003003002010400d07800c000340c0c0402501d84496545254956916099801e544500c51410015590350800240c488641070035100510800b103441e21030718040040500403e040540030803011803049030030408014030300c11180e071203075940d894003c20211141c81c50940203404501d60002007006070780069880a200380c0a52026500c00036518154000d200759404103030810704000181042203495100c0034101c0e4020407020f8200403145400f182c16502202e019410546003002154104041500c01903010803036060002d60844991964441d8001d20b901106030743c0c0d107a00c1384604000380f81e0b1441d41c007d142a02d206c120321440e903401070f44400201540e240202d41d0303071510301440042504442122 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 137446321 1250 137445071 137445083
    0x9020604171608150612061311100e151207050a050418090302010f0606140f090a03080a020f120d092105070615050901031401020403080a030209030d0c0203060114060403 75
    0x1280e6243d1031141c40744451500d400090004500143c543d090440000303020070740c0340c80a00b1407903030b070f44648065a0321105820b60741c0a10609814205883e1804184021300b4141c80e080507200b0701404004400c4807000d07030007101c580184400304500d1650401d05400c00c0d460b0800313039160352529108462300d0103180c0c803240c0c026403071007106040501d1300d510200c0194021360007400b4107450f68a0701c0003030781c400e0312170030b0f00180081e48442c8102c4aa50003400c0600e0000e03120b00d01d4800042e00080090289030400d0314004800650b180c2001d4040003400d080400c60006000e846801c403001c12040c0c041c01400756101a20b03401c0c41410405001c100b040309501c1c1c400101d0008a046000a0054201d20411212140381014a5941760800901d030001c5801c000c11140703190782103582d40c030002d0600940c002030b80e40d000c0c403000c00042d4240c0b001d000c1c2c03001a540c0042c1c64158000405182c1007800c1a40f00174070284c10405805030f2004200309055648450307104180030b08000114642c0d01c01c983c005401 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 137447571 1250 137446321 137446363
    0xa0806070503040312020304060603120c0803071d1002160f0807031401230702160509010605091f0507020901090b090a0b0319060606030b010813020d020607020d0c0f090902060417 79
    0x420241d80d000405aa018a01681000d500d50074180c980b100337072600c045d000319030900000340000d12600101104c090101d0005944081d00300125203403090403038aa40158002160145059600001000040030300e2004c0d00d08403031801085a0711004103000c003804414000c200400c0d541302c25000701c13607280c0e000341d52000a00741c450051001c070581650f0503001805011a13156040d80030312002400d45400501040d140d901e400b50564159120341d00242e005240d40380664000c40c04844030301e61402951b11065901c40441c030400040e494142c004d0200703180390203606125900c0d40c01d2030075800883c1c940300142c18054040040c0c86d00030a8813180c0880d602411440003041426001b030412902c0b03944040c0f0240d0340d880d0043d1041e140031110b1481c1803d0854007000940307805810320541500280013503281c160a60081449081d00740e006540380d000103041004104640d5011600403c1c0074041041204410741c0081d02c5813240744182e08120542c503103c000340000038071141d54a000007140b8108 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 137448821 1250 137447571 137447573
    0x60c030908120f07090503060c1605060a0207020f06030c0a08060307050618032404030c060f02030a021207080705041418090f07050102060601090b0a020f03040f080c0a0806070503040312020304 85
    0x100c80421141d1449580307074040440c4c403640c090000d6005480700103020300026580c0c400031001e5900184035030004098492103941c0403a41c14800c00d801000c180c0400f5980e21024014006405407400d5030a0260000f0000c10249000090548801c06071521b4078100701c1c1c841c0c00000f49008940e402127035120500081c0110260076000090300c44010940603030342e4812031026420841c0d0b01107001d50000524000000e80003a00c94501d8620f4548180b02c00500e2846200681c422078108442c01450543e00050030a1241c0d00c0f0260150b2001c154503002d00d0368607150000a1040c00750340301d12448081040c4001105903207403848428560341044180e0114648800b040b5540c003403e40040a550203403000224041d480031501a104e031406031070b0340203003e00d0203500810945c001c02c820001c40c044d0650558405c02c05100800080000015800e40542007071111800d05071003030300d294410360510a04021300f180110304aa408511030906e185c580d82d072420f094402100d080e4903165480d03c0002000 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 137450071 1250 137448821 137448847
    0xe0c0312040f05030a030e060304081e0a1e090501030f021c090c080102190e030c130c0e0301020712030902060d0e06010608070c02031005060f0a1d06010c0c03060c030908 75
    0x1000700c2c0c00081052003040d41d960281901c6000c6500003a001800304000413406050003002550820b1191550504c0c1c00307860036070088032151b148290022110000380c81c4540079801040c084024a1410404483c440709001c050000e0183e840340d10305154495160000003515941503910a10000d0980003404040788092002407040d1503044a080f034024001003848601442a03503034041e20ba04901e0750380e00e985030041d159503900c01042540340c454000e906460380c40ea400071444482c00e082c008108901c1002c0301501c880b00b403009180c001da10600401000c10103052003902101c085040c00a120012070001c901184103000b841c11805091842c8000003400005000e07040b0b845035034903c006a15442c40c00c03144110007a01c06035141d1300000c070b9805101055445180c12040003040044204840700106180d000e680e13000244a09641911000d440807001c1e0043d07004001346421084040c141daa030000b41c00b040e00018040c281d541400070103050080c1d000a000d96005640191200034044241b = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 137451321 1250 137450071 137450077
    0x706141b0a030f02030a020d1209020301021204022d061b030a05070c0e07080412020304081f060b040e0406050a020f0d0e1e0712110d030f08090a030503010501030e0c0312 75
    0x4a000410140560f51860b1000c01a0b40c4590442e074041e1811050f0a503003229110910b030414042c0540ea07080d400016038092004000300710b0103080c904070910b1f0900401110031030000034420f040d0340840198050a11398000b1300203202049440c0c0740c6482c100781d1030b03146101e0200031410041c8070008103450f020381c210001c1c2158921421090508a468034002d025124090342e441010410741c10210300000c0c1c50b80900c0c012400c462040343d00b41951904001c3c40d090ad07a44115014100c007007032151954196004900203004000311043c6018a01020348414040080000d000030303549102281d110200342c0c04030b85801717841d49032190302d94080d801094010500340781600050303c1194200951803601009039541c0210328000790011074640200c2000b030501401e000c461495000d0320445059803420500f1458a000381c0d542c02124a8864001d007500c04054520100c1d40c0c050186500082c1e0300c10300f12419540d0038a030206000040a030150315001400300c659502d40101010010030310040303005 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 137452571 1250 137451321 137451323
    0x2070b010612060b040e041203090501020a0315080601030506060d032f191106090301020405040203010f15020f030901111e010506031207080f1e03040b0114010e030706141b0a 77
    0x41008201d60314684c0d00ca00c0e01c01c3d41329a40e81c3d240c8280005012940410b2600f40302c1c8803509011403140c000756109801c80c0c1c040e103041008290740e041402007010100501d0300c00303130004400408903541103844031560350600900280c45041ca10400700105440b5403032110002c00070640784201c070000c201c0c01e03224021451140030168468101040340112811300010309403900809800901e80c0818148200d60b800b08103442d8040d0f40030440014641c40d40e2000314024400070045101c5035041411f482030511004400a046611071440f28100002c0481250210502401c02e001425040c0021608050301400c00d5115100c10010b01948000c042d0030403407042e141203050781c4080c0c0200c0714090382e0b400703603120191a01d1400d200c0f0300003200010006007100b03e06042c000b0303001d1000b40040b002c19441140d085038240c1d1101c004004007002d460000700754100c242801103807000028003003a078480c0e00e803041c2c10810098072806180c4403a81070480303c0c035480c03000640c0c800c0304030390a5040d542c680100d0 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 137453821 1250 137452571 137452607
    0xc0f15080f0f060103020309010e03040306090606050604030c0b07030306090507080433020901140a09082103060d140d020f101509090503090a030b061201020f04050105070602070b0106 81
    0x20001e980c80300303041041440388101034020061900d031040118020340009001a0305903580388080382c9103001c2040074000441c42107002144240300c07440d208090f07811582c070840c080c80081c1b00500004000c19180c3c002e54050006040c0c5034142c0d03040880c050407969004466aa03e00f1062201165104021074072560141c1d941610410b45000400030201190308889a0920300402c500154400da800520130010145820b6040e0741030714081135201d9120b200300c030300481c61150041005100030b10140d000481c0000d030324140085102e250000501c4014002442840195100020820303c0c42401d031000035080120b800340d0025010195031500b03901d007090490710400304900e8400c45240909600700c00786009041c00c03246407103a180060445000d0440710340c0418041c80e0f0468070303400000b8004502540c01011142090000d00c0700400b052403500702d0a90040041400b802d051408450480b2401e10308113580b800d0700d0804400034021000300030540207107240005581c039400a401d8074031103e548 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 137455071 1250 137453821 137453837
    0x130302100c1205040b0901110a170a020c030a030e04020306280f0e041e1403031014040b1c0c030501090804230d02060705031b01020a02070b250c0f15 66
    0x180c0b09580c540180d00c03035924050410010101b50754442c1003d0030b04144404111a0121030a68500400d00016549040860004203c01079016410421080d00c4c810550203003c40082c00d440060240407100390700d9000d190000b01164050302c40e0801a504a1035102c5982e008508a039841c4da078260440c840c19000040d900000b2950340700120400b4011a0702c0210044100c80080400e03024007010765040da202d45a4466094507081e090008610034920301a074805040d0410700c0400e4191318001c200ca00030303441c20b4481c100350303120385018001c900c44d551140c21600d000ea280c4003001c010603800003070007942030040300c10030096190064000e90308140c0c001c4002888080c000101d462000500c550b01480c0102100058103050b40141644c0707000d030040d2440d040311008041c0240400c650209807a80d40010041e4007140c0c1400501c000d4102c03100150310f400a013200c00c00c42d01d408925222041c1445c4d12251b010000c1c4021414014400300b003413070428580da2420611329040e8101281c2c041086c076 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 137456321 1250 137455071 137455103
    0x509031b030127060b03070e04050114070f0f05130f0305070305061f0902180d0b1504020a1d041b02100513020916231e120c130302100c 60
    0x7403041d0000c0100c822030100b155921013802800d44c600405403d40a045c201040e40c3c0c0700b0f0f249051250f4000c40000c16408090703510701174140b0004005100700501c094981100c1903104060326504103483c0791140d00c4544402d900d0310700b00d4150f840458488032080c4000104900804c402007164001e4040d24240d681c1d40b0b0307007120354080c21030700c0b01c280383c41c0000c003405912408d5024202c15904070400100e640b80c644046038002d01a040c054895407032801c2002070f900f9804050102060342270310154100854001c02401c1e12341003001000c0c0b00074001c07856030215243c550280742c2130402d816550804c04011840691200200800d003540207003054000b0703100c1090340352941c0000b0360242030b001460741c8039400d0144c0030000e0200c4004101410080301015041400d034185542c4c1c8090b4003d46c1c88000c2a80f155096002070070300d288003103050260b607000440004500d0750194841c40100d40da5400c0d0b0300018500303505900000e50200d91205082e901540c800c0d03000030110700c01c1e407140b01d01c6294 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 137457571 1250 137456321 137456351
    0xb010504060b04060311070b0f0412050f041208120709150e0d0305070c050306190b10081303030e16030311150105120c0604080c0907110c040203070509031b0301 71
    0x20700c2c007548950400800c07081220a2003680250520707822221040c1c00c10401b03680340020044182e610010800016040c0018840c145500f101c00d50341d10305006140070440c600500550150f4030504803104541d140500c10f0240301000c4a803081140c6010840c103280c20b000113886035106001e404180801648441e88090141501c15061000140034107840d08007554210781a40c4400c1c4104c6000b103048500181300d44041104a000701407591091008211042d01a07013100c800b00075051085d1031402c50300001503081030240c1c1c0c001a010125400088450800741c0c047c1041d00b0a80e560340c881d0a0040742c01140300340c00001544d21950321030072919448030119550b00c000c0d030400701c1300d108050300403c03192410f01d001008541c01101901c170042e6140001070b031550002e50154a254100310240035541c034141d103901c1c1d4081c0f10381c102540761004e03101e2044c2d40d690a103010280140e6000002c103490324011020f03201e0350315008040302e0890410b0428407600c2d41507628064000e40c01d04c21031a600c455 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 137458821 1250 137457571 137457581
    0x304030f09050108190209040603080414091b030c121f0501020303040b1f0801020313060e120304081305030105160f02010b0102061f03020d06050108060106081905090c1306030b010504 81
    0x10b41692400c0154492241546450341001d50160129908002d251445d49031070007444029806807132141c1c0c44614050304040013008070380300540300e40c002d24100112140044103080e0440019903000c3d444ea500c140b00b0510030b2090b00c19201281c5081020841c40b81404614194035110b0407004080065580c030040e0b03903901042d0740040c01c0401c480c0004601d890302041001d244407942c4002d141c1d250340c80890500b2070340242c5665590500900d26003061180d02d0203021910001d0b04010000c2000000c0d002c0702c14080540b0003042d80c5800101508101146c42c07130b0501404005008022a04019000380081a01c0d52100c1c0c002c1000000d44c85002801803207001c00b5881c040c0c0203820036503914108610304441c0038a410082c10102c19002c405600c4404140d03204500c074010005075941407220700c03440e07d10160302c08020000b04008205102d40d1100e0600b00c42003941001040a03113909400710b040c41c001114094000a011074a00c420f40c0041c1c00400071240204445591a62100e0078002620 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 137460071 1250 137458821 137458829
    0x605040b0d0b041b15320a0305100e09060403020105061e13020c0111070c23010503090c03010507020a0c0e091f180309150e09060f0a09110304030f09 66
    0x11240c4009004180c50ba44c0c0d403039148110702e40b2601c07207a8641000e5480070000e510044005540e1000c005905680340300070100722102c20444540011600c6618001d0b4407070f4003010020580c5540108034202406500f6001600c46141c9110482c0b60020030103503501001c803070503001507080c1404641307070707082680c2131a2800c0802d2806200880b00c11042c0311040e0403444100f4102542040031100e03040c4284940c0ca01c00710304a420907920092400c01d04041e007a04d030843c84903488003ea1401e40e414209490aa00250070300f491074880c0e80f0850250f0038001585030141d00365084c24200581d1581c0800e00b922890b106000c8503450544071060103824910840b0b460780d880d0311240013a000030407064800c1c0390b05c54000c20003003080a1008120164541c04110132008200700c2030091082c1100c251501450048502d00125008580f02c0042c0340d00e000a030110b4040c8103c60020300341034583c116258080e001404091100c2c80c100c2041e0001907200326400e030001009150000c02d03e038032800c4840221 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 137461321 1250 137460071 137460083
    0xb09150607080906030a06060906051306110a050a0302010606110309060909060607060c080103020414060102250e040c03110d0b060103050a0b0310050403110106060c080d0605060705010605040b0d 86
    0x40006081844029400a4810b031404038090107041050399500000754803404007403802003889031401c1e101910042d441d800c9003050110a01000c02803500c45203240d4211940751814420001548610038207015011b1400381540c007925451005150701500414202d40381941c4440059850300022a00e9005006205500c03210400441540e4640010b041c2d4010900600062034903240369190011900144c5004011a006000410039480d09100307100120000051783d000e24907141000030b440d840341010840301c2c0044090b11030130001070044240007034040c01c2c0809046041c5400c001d5801e0326544011280154481c90030006400c1030417528030150750181c0704485c01d841300401580a040000e002180c0155120311001c81550100146441180200c2c4009034a0806040c010b09440b00e0b90010b8910303a04090003005110780c06151030090981002c07001d510303080032009400150286522042d0b2180002c102e41c011f029066008404803003007100c00300150300301101030203180901a01f0143c44 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 137462571 1250 137461321 137461351
    0x10606021006080a02060307031506030915090506130305040b0d0501051302070203070b07110918060601031e110d02041d07020d09050d0507080609030403050606030727020705010c0c060b09 83
    0x1411b28030095178104886040107d96030130803c05100c00300300144c1c000000691601690014400c1000c1005000c0700b509806101c081d0041c2c407115501c0c40058038050341d507000140c0550501d4403460540703000c1d00040a030745944480031211340024040c280901c5d403080d83d10040041000407148221501d00d81e02a000e4405030f4900410481590003009080e078404820000e09002640c3e41c03241e082c070812206440110000b0035140d554540385005280c903061501d0720541003e8148400d15804020500c220b02152307541c101807480c04140a45420003d0860002c240850b03001c52003202d4000d800c42d00340503404140e49500b022a51002c030b1102d0700700401e000030801c0c0001e0609000d01b0000900074400c4451990780d40824610b4140f040340c07030480c1508045001d00401500b0b0100640081044000302016410034010b01c0e410843d01d100316030711b02c2800a050400c45100d406891101f6080310007004004100c2c41d0140500d41850804c0343e4103468a10b120302c081c6043d040d40c40c00ba86400180280e = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 137463821 1250 137462571 137462573
    0xc06021509070f05060f0c010c081e010807050d050312010e090f030f030a090503090a0e010512031c050615130f05100e060a05040b0c0f0705010813060c1e02010606021006080a 77
    0x45c1070f901101055030104000c100401000c0700900a42e14141110b6aa40d100780c0f403c403420581116490359201c142c1c2c85541c0040210200000380e02081e2030080720a6402c5000f01d01d040351542c8201c0e50308d8032007602c110700005807140703101c81c50758820b81e941e0060311410001c220003280c40c1e03c01d070511420a994140081445070400e5030152080510030802c6030720381819203000072040700c03107507010500441703030340c1d0060055003442c81040c600c6490500c019410144450f100d14a00350144203400c141079600c1e00055510341d40c0001b1124007054661030140c0d1010500700d80746408441c1c1c0240703d07904007608000242800c0c8071700b407074030001205d945141108805208000c031960250100c442044030a020102e800124807004003443d4031620018080124038040460070007a403a4021414041500c0c03c2046080321400c034071410340c0c0d10410004140c5a0f40348180d411030480501000003d1802e5040940650150720580c1a01c5641d02251026005081100151001341c01501070300c0e0083d6030060 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 137465071 1250 137463821 137463829
    0xe01061409071b0609140106030507210f081605030706050105090702030a080c040503030c0c030105010e0c0d360c0f081f0f0c1e0c0f11010c0c06021509070f05 70
    0x1203c414811000030a100b1000d850b403002c8524a580700e00107596407040200b042180400c0282e0040c030a000c0361001d84110881c9540310074000c0000600b00b54a40100c10040141c40001c03606060600e0b06842e00300109401e01d10b5803500010404c0f00d0180c40d02e400412146008100103102d410307250300852508030132000840380d50401508050404206101c08145030360f00780041d0014a050000803c40039000c54100f501b52001a800040384c00c1c00e0744280598000c0000031191b618280c0f120105146082d241500e0050004400460b07003001303540e0801015240000d0f0140d001401407840018098803131920524a00091142d42c00540c4051301000c1c2e554188099515090021000004c030b010311480120203950601214000240d032814030705600c051800fa080900b40707254a030200500341a9912266511101c0c0d102501d185800c041804c1103031711410142052650100d09041e00f00e0b03803000040d40d901ca051a2001020140c4000505504c6000034142e003180c00307000b48ca900071403914040c0 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 137466321 1250 137465071 137465117
    0x170301030b0a02130e01080c03010f06080a20030307060209120105071d180702010903020f0a1205030901181103010c0507050d0804020315010b0d0b0102190201050a030b040e0106140907 81
    0x3551801e04e0030100064041c0301000c180b402002480023410783d403030a0308101405c4410107508070300e15901c2c0003424448060700007080103016601001c0415100728100005081442c02c11100c0d0f4507120000e001401c02000380c01800207880c0569505804401204141c1c0c00c0e10f05c00c40340000059028641c07040400d4441a6007448180083c01101000c60210008641d05008440c9840540e441d40b00680030181d04005071086c42400201030082e06041e590b4040b0101188140c02d02000008004900105000c0d40000100c9182e48800600d0f04c0203840d000c0140e10800b8503003407095180101031010103010340c2c103c6944941c40b10182142e00115201501c5100303000e001a0f80521400c071a00480f0400d8030212406084210301d180c0d111555120791009550b21305143c6c1d41103411030402d5684000340f919a1000043e03090800d19201c010144040b00103001c4503104071760060600e071564148000c10361107942503804c030206000f078101100043c040110001d4401038001a4544040c43c203d020070441 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 137467571 1250 137466321 137466337
    0x20d0f1e05030c0f07050a05060f010b0306010503040c120f05010e010c08040602031509100503010c0509031b040f06030b09010609021c0f0908040801050603060609010f050607050a02041107170301030b0a02 90
    0x1001c0c10491144484c0c803854001d0074040f1150fa020214000034440100b040d6a8850701d04000176086604000c9003800c1800301400d071034140310000c400f00c2d040101101101000e040c0c90b0352000d82da01c03103d0600400005080d031080d146546422003260450030180107103a06441e0319110305c482c6403105d07920a8002d45c8014422410328000501100b2199903d00d50280200d0401d40c0010f0350500301010503003143c4207a402031040c004200100e404584010824494400301e0750914400c400744031700460701401c6030b01c1d02000c44034a0300d003000c810440190076003400f490946000700061902d40d10380b80100d1042410038445880c25124040115440350880003a080c0c1e50080451150385903602c0007441d411541024002b6519002080191306040116507400f441c2100c00000360351404442c50302d0001c88e40a49030142e0720000703c100510000f0080303a190b056000c5c1c001c000f00d00301031720380300942d030003010048540b003001c001c1080794201e80005a90581e908010301030710545910000300000e501000f0 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 137468821 1250 137467571 137467591
    0xc0518060906040f03150522050708030f0703080603070503071205011e060302010e0906010503071d18180d050a05030a0e0105010b1b160512100507020d0f1e0503 71
    0x6010040d440e520041c20040202003004d1050340d04510786822822000c2c44102d400c18034040400000f50301c1030348480076070320203195180700604a60400e18140040754000305000e200008501c40903000e258000c0c401207000340c0e1f50035050349600701019100e900512403594564401c800502c0415030b00c840b2501d0841c4100000602c01c0f0a001c42c02080b0400b0904402056550300020810755070400d1050046c5113089410303100718949080060303d240005041c00c010840314510036075603071400903141c42c0c2c540f030000c000907402000d0500d080c0c2032030380031242c08601091311881d820307443d0000180340300f500415885036400d00903010411079403600020416001c240c0c891540b0083c1c1182881001d020341003e0003042d5a030f030403080c01c418010362100d00d0b00e203042c2d20000c7c0350b040c0355020010308404e5aa08031100c000b0400c490700007525010070310520078140b52518046c04091500054650b4800300d40f502d40740c0e400b50100105841c400c0c0c044040000000751281c030195598070a02c011540204155 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 137470071 1250 137468821 137468827
    0x1c0803071809150905060603040b04120909090c0914070203031f03080714071406040b0f071a060f0a06050904090302070b04030309050a050604060c06020924070c08010c051806 77
    0x41c02c034425603c40d10f8000792221200c82c1c0034442e010031401580d91055080e03610794514145a61603011200300100b001c3c1045084220070902948182201c10080c40103110601110700300d0306250b5524401032117111400b40c0780031070290040e0000041144140c04580156056549020101801f0850f13200d92448200c41d150004c0001030000028010f098081e6503802c43c2ca02250340307514941a20380d04405007107800654203410966420044a042d140c000b00d480c0d0700c40b0f080a40d4410140111900100503a484c840c3d440282880000c00e1403040c00102c40c080e40514403c41032140c149158041c0e000011410001c030308290500350050a91207101e4411100021390b13608102071140c0040d003080b00050f80f100001c10980ca04550307480003400c011121107242524011014005180d00e01004200c6500444c80c19402c2c3e4031120307840e03041d440d02c203194800c203024000b03929165806908211003000f0b64010106441c0014031595110841c141c407a10300d805038203a160b280d0501c1314600582d00c41810 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 137471321 1250 137470071 137470079
    0x8061b0304021912140c0a0302010c020f0411030405060c030c121009020a050405040608030a0c0b04030513030809090a050610120f020a0c17070201120b19060e1c08030718 75
    0x802e00b070f5000780010042d140d50030303191340741002501d4925440b0218a03800a0721400c0e15641d00c0b00340c54103e030f50909001e10301100c5031000c5820400b0020409a00c0ba24000a1000c0802070300c008502c00c0d40702d402990400d40d03d100100c0000d00003550340303514224040c0802006000700001c042e411900201c0c088009a07680c42c4500280d030300c8902d040b0300050003ca01000b441c141070007084c0250059001650400c1e04400005049048425002e03006c00c090b14045803d05014030121091200001049240a034881c200118150701414940d80606020400600e0700301051040e1402b894000782031a00c0300000881c03c840c00303007100324052165503403241440610742d03851000b03100940389a2a00c00080c551800d000160484596082d00d00c1d0808011400c010b1386d20a003082c0340710260010020710b0805030004240c0e06081040c01c0440115541c4000c0f641942000b10b1104800c0c1c211a405462440054040c046a81401004001441c00d00114034014046d903203459209100b0340006032090f42d2 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 137472571 1250 137471321 137471359
    0x21305040b191d010606110304080a03031104090c020106030c060318110303090618090612070e1302030a03021e16090b060702030a0309050306070f02030304020d080f0a1808061b030402 81
    0x140f20104103540c1d5030305e00420450b5005060b03501c80124020207182450302d8641681c1e207640303180c07000604155071900046024000103003903601402c0107003010064140b40c00d001900030305840c0805c0d59008441003001070340030b11a0140510500303980d00c5503480d0650310359038140030b0100260700c0fa43c14001408808050b403280c42c00fa0000451414840090580c080c081c80407209010300031502985410207503c1d01d407c03001400c64102ca40308006c250255452600542680da07102c18003d602d03015182000051503400905142c00c00c030204881c4101c404802d071440d5980741078442d042d00f80d0648a07400c00601c4581c1e1f0240f509000c0250a1600d441003c2e070009007041c6020320202c5c085503100718184618101088807a60142207810400084c40b050759002c0d581c0d003c001c100038448d5208000c0c1d002004560800c2c0c50030015020405602c55400c172401501d070300c21313061000002d0141050b002031405000074205001d01c04d031403190084007000c0c644441d429800100242e800c00d11001300e00340c1002c1 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 137473821 1250 137472571 137472611
    0xf09040c05040b070b010e0708060d1704030605010308130609150e06070c03030f0f050412080a1e020a02010e040b0609060d09080a03090210030e0705011d03060112021305040b19 78
    0x1100b0b2074145c003258109100c0c45518078028007400c01b080420400c12016461307003820b01403080d40000c03070f070300e043d40500790400d055100c0c3d504000d10640c101000001003042803c050025120065020183c454880d03c00319010001c0d8407540d640f10340c85000701002c4071b000741144452440090300350742c46c1410544884038a10030607842200090700103c1820340c201d51103a03e14008081501d0701900d00751500705811109004400041c046c040c000a985003801d011319188201880005003c0c4902d58038020040d40b10b41c041d4100782e0200c3d5105c0984560351810340300d000075041c40240381c81e007006000c078140025a00400411003155650300c4214001c0380c8600050f005071141543c000c030300741035139105119800002140c0e01042c1404c004070711b203070080013164007000d231042031900e2141d01c801b251711071104030b951b000d50740e801d030103204008502d07101c000c1e19000f9098000c0d900281c800140410040031500c08032005001411482e0115175403d02580c0ca80c10020305038400441d01c01200c507500f243d500c4c = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 137475071 1250 137473821 137473823
    0x1030603050a030507150b0612060613030b1803130e040212070f09060801051509060102070f031a011505041208040305060f01030b0a090203031c060b040303020105010306110f09040c05040b07 84
    0x744c0100341c2038100845889100c2240c0b1450b90305000c541e00d204080b031800d000361008489500010f200080300d5407112401da541c0c039241c00500100c40b40d0b036400e00207407079034098a000882442d4042001c0083e4000401c54420140310511050624908019101180c0c00540100d9012400411140e02050100040b001801c551034460b03d4480ca08090031003100c61680c02901541d06142c02c1103400c40451f44c14900b02c500036aa400c82d1640e40d100101d0415009401207103440da0400004404e201070949450725001030f4031002d0b82e55136244c00790301d03140c1c40f1340e42c5d150400500c08010610580e03c07900000d101c12440394081c14103141d2641e07215420310300101c42c0d031425845041d0040040c4601c1c20407090b0020790144080008401e290046600e0b40301b2021403103034030342500c16101c940300c02540c0328500802126400030b031110384918000740070f004280301c240d80541c1054070038810303142500101d032501d0303551138421442c10800c4000d1101a003c02c0c0450014030906110000e406841040289042 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 137476321 1250 137475071 137475077
    0x10207021f020309120c010e04060e070e01050412060605040b0108040b01170a08040e2505070b06030a0206190f020c0a1707050306090708070b0a05030c0304241b14041401030603050a03 81
    0x31b50210700050911586982041c1f140d400c0c071000300504c65a80c601103401440c075107024030765a0499001601c65104a50008840d240340461040c14020198040010b50700220380038090014007000443c0c0001c0d007030702d001e03110010420040000c0c0320141049403007601d5010690300c0c00072203038450f00e40e1303600035034810004144000d00b0031000400b100041a210102102114094840d0440c018144d0207007120081101c10720b0b00c040b4880d82e074108080342d410b40e4000c10340c558503500080d0440300e00c0c0400311900d010a4804811032052800441d800c0204000900b504100c1031821040f1000c2c3d028035212a662402100342c04034454030140720320340c400c25100000340030040c5085c0100d0725050490780a0031203d030042c00961143c90b848021030750000d074a05c000c580c482d1154281918104610305d51040d40c2c2040485c80d010306903054100c80c000c10407003012100c4101c1c110005503440b00311008988031600c070400007400390100b45204c007240f400042c500018040d03100d85e00d0b51328059002d0020307808 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 137477571 1250 137476321 137476333
    0xc042412151a130c020706030c030e0105010306020a091a070b130c03081e030c0a20070f05040f09050a231005100803070812130f0b01080f010207021f02030912 70
    0x402c0c2031441020f00030710450301082201c41105032000b51a014140599820181c94021010515201e40c001052020160008206550356490494025400982d640d0007040c0300400c0001d10f20407180703032000c1e0158016071003850145103030750706030900c1030041513903400260780c0400001250605000a015610400700c10f580c4a0007415040c41c017152022801d2a40c800c00c008011840c2c0e018030aaa00f1a0b0241c10150082400305c810030054400f1180001e440b48614000090f8440112001004699080e507003080002402203808056569001d400303031407944945c0503000040c0a45030101d0f842d4041e047d1141c400000340c503e850410f603115921441207a01e5100303010441e41500d42c000c1c01020b41000461412505681c6c5007050b0260f50599000d4002070310011b0031000d54125a803c4142d40800500100301c1c2c240740c4645103990a00824000e48102011001040b0051086540641d00200300c444614400b10803031000c21600025002140814003003801310f51120b08054400301840400351517 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 137478821 1250 137477571 137477621
    0x204150e1c0c03020603090a080d15060302091804020303040515190207050a0603020304050c04020409020c010b040c0c080c2e0b090c040902090d12020c04241215 71
    0x84103074144641c0d5000640c15215032000500d0030408902100d42c15188151030780c2d68409142d05004404d00090011b03140024049130b0306800d0740c040902a0303061400308039a103450316411812030096842254000c40c1c1100c00541000e9040c402d9507000e84010126880c098844003c2014001d074521300349a148000300711410b8069201c450714100b6001d03480101001031410000400c1c0c40b102d0312814090550000110301484800d204640310380b40003a00556890f551203650750000d40c000083c1c0c901d15442e11f003000348203250600a242c40394605541e035012586103511440e4456205000c401014800c0301c6070b4130310743d4208000d00304103a0107501c07491182e1001d5508031800d58420b0206240700744420000c200f91710511009032800e0310310070000147c039281900d02140c0d142c64a9400070746a8440c0d0074285c2d41560b8002100344d4440c1e41550284103180d030b4103030250141e40142507003416a59210b02e0070301001740c0c0c241050f040980a031010380103600c12440000c00b207480c507200348141c500e5510400d40b = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 137480071 1250 137478821 137478829
    0x6020706120507020c010c052103010905092e060e01030f02090a0605090a02090103092f03030906091002071d071d0d140a0b09160f060503070807030204150e 69
    0x6114141c081c04207000510f08020002e407145154280281400f60f14000d240600100300140c424004804442c1882c6a140e50103900300c40e04244604c120701070410002403040c0340d003c25200046852031100c55460051485400c582261840c02c10590031b41c0c81e8000107004c0c00d030410281c021400351000c000d038528240140010741e0b1000b072210303038803608212080101c0d4641230700081d030001d012040141c0744c0001e00d0041b009400c170700c100540100c407294000207044000400c00500000064000b0312000c41c1310090544038003450300718503400b0200b840000886e0030704110203821403881d032058852454440307020030310346e40300800c140c414800e001040041b0300b80c000340001d41c04010703100721a000d4090200091085130038044020084403201c1050a03228104004109516a002c03406554900e4800401179441160125030071070041146000501c1201c0c40207400c0c156000f9594040c0b56640303416080d1200d1b5005081242007550130040064000b8441c1000f84020300155249800065200700308 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 137481321 1250 137480071 137480087
    0x902040b0a03032a0f051b0307050303090603091c020d0206060a0b070f0201030e030c060406061208070305220806100603020f1621020d080702070e0a0515040606020706 74
    0x114014441c2240900210303410081030903206001c00c5401c11036000c0450048042421060002c11072450003082070100000031456050310b0941d04603c0000e030043c102095031b241000e100f030540540040000d0f40f0f69040130b8000350b034415014021641002410040200302000c201b0104005030020700030185007030b605200050b040b58089034101042414071596000030720841c0e000400d085801c412040c01c590203500508909003503401a25199a0450041911510115801c50b035172031030400045024080c461001c041650803800d06d50070039542d5601503419a0000800301107298008580420240501032824060014000504040d040ca0520611040401c1e0170240a145c0140181c424036035140c019100030b003225030110034560450f81002c10003181018042c0c03100181c407011160b4860f030000f0f05250079843c6540e8902065840803002c03a15103015025003400c410102e80401d03401c5000760070158200300004140840c17090700000080c22500e0350b038001c00240e00b01c280c08201c015000014 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 137482571 1250 137481321 137481341
    0xa080a0f02070515130b130905090d0203070f03180b070b1003020f0613050901031a0c0c0d0c080d0504030f02010f02090f0607080c01060b0d0c110706081810090204 72
    0x80c10030341d00f000001100202281c0400030004804a0089544105020000d000708039060702d880d60760103c04031200103c1d01d0f0303000713100c0385c0c60824004c60f00c405000038218100301e0751917000d141400080d40e10104410042d59094040201b10110780004140b1520010000c01d802d5540382d0b0b03606802d203842116204020802404100076090820268032070a80700f04012030708a0740c9658541d005c0300100100d2500360081900300f819031001104001001c447d40c8034900802020903030985d11201c55446602c980034459501c1e800ca05115198a030007251844c214074480ca0080d41000342c41c900107030840300201e4080c2d0001d00c400c00891071640c0c080c482c00c0d080e180840703010761402117998089698001c0b840941030160030001500400d000c40002900d0b540346e80c42d4024000c40d82ea402d40300c460380d004001492052450320501d2100540280343d00c0d100044868060142580380c600107682401c402460015040300419100b40015420f020308a079442504100041e140e241e030042c803048030b0b4403003a = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 137483821 1250 137482571 137482573
    0x8010507021f0e030d0606030e06010b0409021c091b060509061b0c0a09020901120203010e06040f1d06041b0609120807120f03050a0501050f0409060204080a080a0f02 73
    0x20030300c2006a03010402c0342100b4180c0080380940d4855965000041c680e2000420365400080b88000050400c0d421031401c5404030783d0244000c0200030545901c41c2800e1203001a00601003004102992107600907004401d031440c010b41d44d00e071024440d0416200159030440d905441c0c8800b011180c0040c59000010b00418949a4180013540c404103c952168120440c1c1149011840c40b50103c4200b0860440d0070303018180d0a0801e5490141801275004038a07001e0101d883d0b056102110b07040c903c00d490482d02c10710320708205504c2d02400e2000030a2403606454070f8548070b0318982020781c242400c488414010300d000700346915141c00c1191410f400001e2401801c924802c08002003039001106005607001a690801406518648001c41d482030300d2004103501441c01e80180c88981044804080889549007800503548800d415403c94009014941c0d1100040180c4400360416034000d8520f070f03104020062a05855081d4545083e100038421545e020002a608407840e500180050010960740 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 137485071 1250 137483821 137483831
    0xe060306250e0d050d020a12020a0c050103050604090803010810061202010f080c130b0c0d090e0a020a09081209100306050d030806012c010f08040803070c02031006140a0801 76
    0x400c012000c40d01101d0740008010100903082c4495032a0307003480d00e106070301104507030620b9610700b0b01030b44880c03130058183c81e441c1c00c200300a12228000708411010b503600140004030030b82068011340040c04d0203010315411a986e41c03520300028640a0085018201d458010b0040d1280300b121801a40c1c840c4e0040e542e1405500c5c0c4010040c2d0f0031988038a9565100c2c10f1001c516505d1103080c80b00f0b03006800c0a074a044081c00c1c0005540c442100050080845020986000e400e50035000c1d941884244a41c6090341a07040028615004a0f4041c1644c40702c189070034076903140d41d5020301e4542151349101303070f010b4400091512140d1400c070a100303800101d581020f0001500d450001680103240c0175015091142c540000f41450303104a81441218001318081540c0c9a0342c0320301820a01d2814441e039001c69040d0074502d422034020b8031a2803240d507000403802c0c5599038440080312010f1138131404030380600c07401c0680502c1100c0c5016030000350042850364545004064200000c1d0350480e400030400341d1610b = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 137486321 1250 137485071 137485111
    0xb0a05030c130207032a0303110c061f1e08071e03080304060e0a0b010e0a09051b010203040803030a02030f01150e2e020303040b0f010e04060b04150e060306 69
    0x2082c030082803148001621001a401c0669111800c10740710178060b0450341d110841c40d800b00021150b0140130342e40410903440000e181d21500c1c80b03600c81c1280b455100400040266040c0c04021782e100c4030302c2d24464401513940c0007485d140b242081c070070050001052010706c100700080124400800303101d00c548020030044091000394150b1400b01404c032140010004090040d150000030f90740142d00101d41d00390910b818040b0050b0350038090a1030700710701d04010403034001e482d00810003070f69000000740c0302c5400541c0100c0c0341070b00c951310301c84e048d800140300004a294051000d58860f103d01800940d80b1b01c1c2941c0c482aa08605802c64282074030f50301136400d1050303481400703960001015502a0340c50100402010005401c0858480c0d403190500d503c00e0407558040083c40c041c13440744015140d9a2074804030b0603855642402034400414182000134040303046c80d00095412000074000107111100442850302c041c4550300140003001c505d0052244c541020420640d02c9950401c0c040342c0c0c1080 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 137487571 1250 137486321 137486329
    0xa020405060a0e01170109020a03050601180e040f0803010e0108010b011403070302070606030506070203040302011403011a0a05040306060b03011e0308180316150f1d01030f020903100b0a05030c 85
    0x110b4005404003c494502d0500c164024846a25100a0701440154945c0d54180c3d00c2c020b940a1115000002d080c5070110f50554040d16800c4a0340f0b007852017800b15070381803001d4801c08050080013901d26190105031140400d0006006601804940ca2501607560400d208242518a01c2c43c04904125400c82e8403241044070005880c3c1000140c034000d0f0340d5440034200f03603001c2d080e10f400140c41c5024407014408519000001001224800c0c0c0341c40455100800003030030940400d205880c821540007201c4110400700400505001c00303941030242c1001d440307846103411540d0a0f00802188480040107121400d01403010b00c840c50300d10a980c0f09803600b1980c3d00083e41c080e00340c0e40c07007140c541040503040c280c1c0c040c446020203403141001c0c44c1c405680d5003989016005044201008520401a503140c60b03803040350195400b0540303141c0c821010015000440080c04040704251a0035170a21080d1070390f5406000503c1004042000403a004032070320100803004030103522030b034400d034441c08074128152030b = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 137488821 1250 137487571 137487577
    0x1409030903071202010f0806010203071b050f06041409070c0507060f0806030a050c0105181203030406181208100914190e0604110303040b0d0905011d0a110f0d03090e0a02040506 78
    0x6d040c40e1181440e1980c100507841c5000d4420018882000b030312042c00c40d030400d0348820b0304540088604a440014003002d02040b40b05074090344260100d00e00c614420780c2050404250031540760700c0c11b00c8070411152074460030034040d42c104000041c107900d051500c5c070742d20079480d0740c11050480281000000d1940d0301035071004590406030501001180344150340c0c41c50010300050b01006840c0441014101c0d069640300e92044808940b02d61400640a4903000c5c85a4aa03146c6540f2801ba03070501a10060283d4840c2c0303009202d078240000b203a401007180c1c0c03854003405940844011414980741802050309180004d82c814107640c00c5d1038a01c848910314030025003140c01c42d030807038482c28030141d200d00403a0852143c0c0d048100c07508000529103040d101c01d517002e101587c0c0100001c110300c28900a003080000486240c1e8009a8001c10032540451042460400d0700403005005a0007244500d021903942040207a0a401203074070030314108005022140001d6010700c12880842c030740f50622000a203d40 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 137490071 1250 137488821 137488847
    0xa03030c05040b0f13120b04060207080702040e0109030807020c0d0f0203012406090503030a1d190612180201050a140c030304060204050111061018140903090307120201 74
    0x1034489a6110506009004480c06048280707621980c800131000304c0e0314140d000150842c0018044003001030800305011014103259072120558156844a0f190040650000c000550740f0940c104090401a6a24403500001180110020500208034200a0041c90340140203600390f4100620003180382d91a040c407200d0317256214080c1030f020003650000c24010511501c03450b40c18800c15409103403102c1070034009021244156110a0010340300c409054503402400d25090100700166a00d41e507070140c000550042a40281c002d400209540c11510038640150b8840b43c003003414600003483c00182070003114a148855141f00300c81030b0355640020140d1240320941002c20504449040c440080c0000320303080c00d031400040b25240c0c20301d8101400258464070038640421440020304c4440040480c041d8400c1c035200700304895192910034600302c0c09464890300d07001c00c3c2d03031010100e103030459413401c442c0105030102c01140c40d08500c00605140066a40001d405100c0d1070b8110380041c4c0e400400d1b0050304e = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 137491321 1250 137490071 137490077
    0x60d0b0a0c0e031e120f0315010e04050a0c1206030b010b070309030b04080306040e0609100218030102040b0c070503030316030c0c02031f05070306050307170c0619030605060307020a03 81
    0x144081c0a0407200c0a510240303843d410b00640540b8a80300c2c00310040340000a0203607040e5031040540c0c14400741c00c0e22804600d80d40400d814030000e000c809090481409240b01070504140048060002601700c410807074201d9070840c0c0e10082c0560141c4c1c400c6501004142c0d0000c10002c09043d5217444c2c2c540300d814400c2c4850200f000403070100301440349001e5002190b02040a6440b402c00303142040a43d001102e040f07008a1420f40036580002000410a02407004032000d030040b40c5010381c60102941c808070b00503039170311030705244140180c0702480200000c2ca01c6448007600c80381d40b000d916003010169400700d8172070392082c0b0a0049050354002003411820060400050701100c1401c10741c2c004114200195150084225030158510500031110030100e800c07400700201c4ea41c040c01501100c25a01411f6010703401172006014004226680103c0c007543c0100319850458404001036840c1d100d47d404800a003204050692040d41501555010f4902228281d085107030418000b592140010b10103410 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 137492571 1250 137491321 137491331
    0xd0b0105060d14010801020406080f0105220e031b150702030d0b0f120102030402030f06010f05060705010212040309030501051003030e040b04060321230a052808010806060d0b0a 78
    0xe12000c0d44540c1015074040001d40d1150303545c10840303000703401c00d108440c00f2545903000a0001d4101c914038034180d0310000c021010f44486081400d221102e403c440650495680340d40140d1007030100040c090240940615086215800c40c0182c146103d0001c04220020300341c00703101c066500401564090004a0800901141140001046034130340b45200b5400090750f00090341c542206400840c8150300940868501d010358091440c0e903000244a000c00d090407560040c44927141800061042600400001d41400c070040d0341c0c0106250706480860125200740001c2042003801c0c003c05500c041c1c3c10b0b416404591450302c0c0a8040003040311102d114a54421442d55690348641c8410007464200090b0100b042280d110300784501c03060440e040102d50f91810030500803400c036408007403d468a4066a081094842068806070400a1107074814215082403840d410f00d80f20b0410710503001d40c1d1b6001800c0d40b4200c07602d030a201e405444240150541c0c8901404a030036101d10f150080e00c01000091 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 137493821 1250 137492571 137492587
    0x1e15070f090306050c0406030e2a0102151e0106020102090604090207022d2b120c080703090315050403020a110a050604090204090b100e0d0206090d0b010e060d0b010506 74
    0x15440321580000b000186040d081c404203035405c001920690389603881c00c0003c00c1c540141ca566840b0003e034507541e680c200c8130740800702c12007241e0301460341441801210980708543c40140c0140104aa040c0c070040d202c1c503400c440b14503030b0007403050060655000840c41d00d2030810100b55030b03200798007528841580008424045445000c55000d0000802501034401940701320714540c02800b0300361040c45583d0003c141c080c0d24a001548045840c100c4164400c0080da0790b03680a14814039401c03400a00c2079140485d40420301a000803c5400e1183e603804004030704614241c142e00b1010000d0290103441d0904002c0020340020303141380d0103504201d498005264820000f540c0420a07045107401000101e00014030b44865005030040e0f481111060100040680c00d02001442c03410104000901d00e02000f8441d0a00b4094042c02300e0000d01101d244c034000c4404144240118042100d040a141c0c00400407802a0444140c106c0011680350105c00c0c40760306c84200308401030045a224800c0044c003c0 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 137495071 1250 137493821 137493827
    0x1415090d0813060515030c010306050604030b0907150206090114070203091306050d24050f010e04030e0d0b04050d0206090d05030c1303120201060e04020607030c0212010203091e15070f 81
    0x8440c0030341c000f006002901d00a160340a0401e000c0c0301844c080d00c80c0c500010304540c0280261020344501500c032904203451900c0300e980c021006009504c050184404c0815080403810b500c0000c01d906030002c146508243c46c6003400c40d103c042e80190402c0039001400010360380402203a014100440c1d0f20504091019040402021141d100d264030031300d0034020b0702c02c01400c11101841c0030100074040321040d01d20240c0c070007612412a004102c411050005101118041e0907082d04039010786061091442c4080201c0d15420322414180c17020142e01040008000c4200019660502e41c0d102502030360400c03240c81503136020181c081c103040c801d000c0000703054000c100081c0ca50142c01c00c51100926541c07402d21101c510382190441005501300754001c2110301c8840200d80c09150b0240800780303090b0f8140c80803684d100344214100e07841002c0340c1c0144400b82c000d00156010f12200406403a00c08000407a204042417480510f600a03003201d550700300d60604200c10680c0c4030560b0b040580c90742c0e003e50411 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 137496321 1250 137495071 137495101
    0x30c062316060e0f0610051801050d03110109020406090501030615060516020111120717030702030a03110706050123010212040e0c070b010b030a0506060705060106050d1401031415090d08 82
    0x108099119001c10000341d401b640b80250200d82054592500f600181c9a844014400901a0a80106ca0200804000b038820107007074061089044c000105505140e000a09507071031035100b842c1c0aa00c2710018800d0001c40e10482400481d4045051121440c02d4405001c0e401012045004003460860800c1564015846240000308040036520a240c001801a015800640e410f5071015900e1511901083d41d01c01102e00911907500254148031407010101c0203030124055400b03049009100e1000000c2c428003865020740f045684000c4070046c105ca15a00d00300381100d0040c119800030441c2d88040c04c0300e2007201c068841708544030314981e41e4640380001c1c4bc0b15071b80c0c004080c0e0100200000f100890341000e14080c01444409100c0c43d25184100300c030500500c04064083d81141c001004100d0007a40241042d0a0412003c511509500d2001c1c0e84901c00340d1041e02e03804565044c0c002440c0d424041a50340348460042444a41460032880f5a81d04080d01303504140030402c1c01140e0652144c50003 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 137497571 1250 137496321 137496343
    0x30f0503090a240c020a150c03020408011e0c0e06040e0c07020319020123030f09010e0a0501021201170703111f0201150e16030510030c062316060e 65
    0x20084511000c12200f811640c1072002002d48180b60100030b60b1038a2010465500454108070020302e1509034079140c4c00140b503d0f08411040c15030801001402c52000c0c000d9000034194003001d02008181c5240708410b480041e01403c040041001c1200c000d44d64040c02c3c2d800381c0c0d810fa50040225034900f000034009108034500070b5454454100030b481258071400201032894405c0e0b03551000d5042501d29100700401070040710401c4103041c400280300344102aa030b16170140810002081117000990140d040c6000090191100d035000144003601e204a08200341c01042c0f0a40350000f0300c0710640c819901d8641e240002015001100046001540e070700d544a041c1d0908452034003c0c00e4881080030b030080c14412514411031543c01300c005076040c008000113100300d5403400910b545026a020482c01032000038040d050900d44d58402001007004c6035001000780006850360340018248200707040498110080440c1c1d003000030009078510048049203060b8240c5d02030004030b01c8216402007075050000c41d200d = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 137498821 1250 137497571 137497583
    0x30b0312121005030105040209040206280201200307140a0201020906130602010e060412110f0304031a011e0312050d0c0801230a050904030507060204270504030f0503090a 75
    0x30485818000148401d009a40e000d842d42c0941da520350070f150a0302d00450b4042c2d0f025256800041c0035003070000041c0302c884000054080e2404030303a0008288410114070140040c0c2d0768103180e45007400b0715100069400310f24078025055240200d0010803c08056200400540010030240c03501d6000f50103888004800401c015225913803400e400c2040a664803c4400543c00d010101c900b036007001c203446003c1d40d040142d400c03502c111050155403000c500c495034001449900400b981c601014005003015510809107854166803401100c1c00140060b00180750250311400c1c0300402d14580c2480d9411a940310a6840b2405441c4100f0b94040c01808640103250b0708108848145507032284519060710203405642d410030f071540320a0400002146031558012103400d4040c043c0780b03001e0050650240c40b80c0307895403904461f5501c3c6020f84e0003c0d4094100c6800480b800211084020358541d4500341400003007100b8a4181c40040500d4440d061a0050140c000049080c400040c014041e9081d0062 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 137500071 1250 137498821 137498827
    0x6040209040f03022b0e01050703090e0c120c03040506060a120b0c09040207062f09040e01090c030f03080606031509070912030c11030609030703030e010603020d0b0603061b0406030b0312 82
    0x1a80b06010071400005c1203000603080480004d46602440650380215095950b00140c9420300c00c56240c0341101034481d5003090414401201d20175110f1204034402c0c010000d05a840e030405151651a06002508491155442132824800701402d09002c01d52aa008860030b50207840303003d100030061041c65544c6030414000110281030100b2500000e840da81c0c201541a12020040d5000c406e049604000341010082003020000d107141c6038101c0514610b0102c000944148241e4890641d4802e590041307400011044400d0141034101e071207a6031114041e0713a524514074103009080034004807003408034854410315000c80c40c0307035204109140141c81001d0700200344603c2c03400c016111803010607080f242d40104401d10382003030030003040c4240074200f828010744c02e00400b84c2e0f00780c014000c147c103150708641d642c2400001680c3c8441c080094940520110f12081c00e0003005c0c50b00b000001462101c020b00d003401c005550b010a0300c1240c0c100d9450b0302e8005094172002e0006410080389001260000c1c0001c = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 137501321 1250 137500071 137500123
    0x30c0c06020d08090303070f03020304060f091b050607080313111908070b191b020405040303060302040515090711070e0109020c07080616050d1407020105060109060206040209040f0302 81
    0x1034000720ba008152940221541c841c191550350340b0080b0380c00030015000c0903801e000c51303010350003958000741705140c0495100c2d200f00031001150042c040a880701171113906142e81d9071000000e00c3c0e02070042580c405162001c19101c1c0030840c803026105110032246030a03403109110300f900a1140b120301c001c0074021800e40090112041c070130280511545402401c400007400344884040b90780c400104030410000500c08103003625030b81d80c101444449100003076032441c01030340c4501c21b136440769100e07450014045042d8014402114401000001c4800000710350440a0b40c03031148840d8030500610700000d040d2105041d440c108030207a03005040c00c1100400209a4210b1a0054031158800740c00311100d0664481c1e90b030341d8510707042d14a0007101c801c9203584003110348540024220b544038900c0104044020714994010726104880c1200141d54034814020a5a4440c118500605c1284020070183c20903400044480c00d01400041141d21100c00d031074105402481001e10280d80c24856a00e08200 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 137502571 1250 137501321 137501323
    0x1d0c160b07030b01050705060403030203071e03060e13051b060d020705070806060603070e1005040503030d05060108010911040e041a01120302010c090e06130e07030606030c050402120a09030c0c0602 87
    0x20380d00d070700200c2c0c02e008070f003c041d501c9502a40c00090f08040109032507100e03900c0c150000c3d440a414003041009000310005c0d8058214a000c0d074801103980c0000c0c001e85080703690740c407640000d040502c14049a038001004184d00180c03107000040000b05805880c140f42000a03503034869a402e07100b5207800451148140440030507040211032040d03041d1030441d07980fa810461180b2007100e420010a0060f030001c0c04034240603907403075075400050810500d860340f90000285103030405410240050b488404004065900c950b03100d00404d0705682c10b010014900e500c03001c240c00b0341d01038415801c180350005402e0156140880c0c2c61103020381103012441d610f42c904500072030462030b0154099070801c408c6200c038a01c106075100032200541d0102c2e801d80c68800402112560700c0d484030005a1312503224400441091028400541c03103242d00280c094614506a082c01c00680d1005118910600003050020b4041010b50750054003000d00107090b11051606070348803910400051f061b000c90010105001da0 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 137503821 1250 137502571 137502593
    0x9061e2105040c060509030a0303150b03042f010e150d020307020d020c01080103020d030c03030e010213030201021c0807052d03091009031e09080d0918061d0c16 71
    0x300840c1103c03820350715010203035111b100740c003621501540490b015a01003403190703108080c4070240748400303410340765100709100700c49c0c00c25141501c4c0003020110400b4411641d01800511514000c011400031071031500103440c280078907204030300900710280c00e9a0540f1805045941180d105c41d011522402d06010007581c810380c682d076000243c840d80680d41d00c19802007007518126a0300070300340142c7c61150b0741c045419041845c2c04805051b2182e9900c2a02c0c2028006407000040c905072420010f03180d170000a1501c03030213004040c850306108120300750741030b0b01800c60795000c03a640c184107945a10b541007600c949d422034000c0513003c1a148504c00100352442000b5405070400d48100e0304d040105169030401c6480c9650010080b540c0c105031340e100d00100280c6030450010904201a07240d40d03d6129030704100c200c150b0000000d5204609019044514405a642d80c0503803400300030b03c0e070901e864469a000040c00190700108004000303a62880401c04940001201581c41e03401828103107488690b00d0 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 137505071 1250 137503821 137503823
    0xb0d120309030f090e0c180a0816090207051513050102031302090105101e020a05070f090606050c0703021c02040c0306030c29030702010b15040f0609061e210504 71
    0x54505404036000760303c00c0e081c01003618000c00414403176454802d4a421aa805210082514a05000e6000c0103944020b001c20060900001416100c000071400c42446200b90f040301c1c820764818032218000c03c01c00540e4800102c3d8028841c1d15945404e905085c401100cae0300010410342c000010000300381d60141d0032442031807080e030b10110316988034401c00006106603d200c40014504e003c1031040384407011089210303c00d2900540d071220001e61034150810806800010419108410800c00c903102885910300030100d520f0078504080c04d503580c00b07403a8111403202a10840d40c1d0f01518101c1103a81819114050b80140100301b00720200c8406005010f41c0e10042d075041003041400507180102903000c030300004a0040d284000c41c42804041402c3c0c00191118045660398550025140c540580000044550100c4542c8440ca4440840c15400c030300d8014404001100c0010031005800c0ba00c40c4040f10004407104074a0360300010b003210b0003e00031a080d142c0403010194854001035580c882c074040c0d = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 137506321 1250 137505071 137505077
    0xd1505070e220b0d031211041805060f040b031e03040e070e010f020c0109030b1906120c1a030f1f0b040501020609010204050108160318080306010e030607120b0d12030903 75
    0x2110100e0411007803404521000d00400c26111110f806e1100c81d900c121034840c81543c505052540310315914009041c0281c19000403544ca100340529031400c1e04e440d01454408071828000fa00141c00465160110030413590084064141850201002401560090020440403802c246468200104165504079141e404a042298505641880480c8030314081c00f068450350110307443c0d40d4400880030f40003800b00e10745c42130400011102c0c01030750061100030440010390072204182400c01c500c15681a5000d840c1403160060071031844100c42003900e80c402d241c0d00c0a144950f8840c820010720311490072101d60003907540c039008196403c0700c10141080d9030003a800c0302c10350b550f44901e05080f4030a43c0074441c0856040000100b06035060100d9800300c0c0e52601e00400e103040100c40d0107414500603942203410301c0000c003c01815590008000080a01c210010021820001c0000c0d1501c1810212210340769210b40020f03a0645078024045100c1c0d601050f0646058034442d002001000950002c0f000 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 137507571 1250 137506321 137506331
    0x603031c1407350c0f070503031e28020d02070501060f06020106090b030c040c1101090f020f01080f04080309010e030408070f050603010341010e07050d1505070e22 72
    0x4a407042241801d81d0f08003c603608490354544c200401481d4000d02440060442e04125140000e101030021314082d9030858440c2c001d614802030412081d1900408056448140c002900044a03c13060718030911031b036940c00103036206400e80864000e03204032100603201790709003800040c1000346003030503108507681c030360080160781d44940b047c4080d500c00c03802d540e07416404266180f446245c19480b441c05610f403820011261a44580706c0d5095501d000d0050b26486000310100080d810100c5002c00e840c5801d00c0d00c02902c1c42c0040c050402450003420103881030784007100003010b4032425845400d41140110481c0d4070307244d80f4285150345004500904481e003a480400254508010054074140d0354015401541716003403242855001004010380c4490b250480d00c0c02100f0399440715004424120240003007081103140840a00e011b03001d9001c0d9020303040507000800481d0034984040c42d542c03d1180003044070f465414003120041884501d06078008001041c280c0000c0c03480000d0303402800f04801c1804 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 137508821 1250 137507571 137507627
    0x80a0f110612010e0601050c120a030b0a06020d08100506041403070f050315090102040e090102071b1206020c0307021005040602010b060703090e1b1606050f0603031c1407 75
    0x80340500b840058030444080d0060050310051900d0507130100042c5800d50904407503600c02454031a072419640f50340b603000181011450341c14050300420000549100e14420300d40300b0001d60f215890040c2004000c0010003007203582807080c01100080100404075a00c0316220310541c44100c2c1d200106501c68807812200181c904c800b8001c0768101c460040180c0702c4100044080b00043d140200300c082c441d5800c00011440c0c2145035940d50060400c1c100040c3c13035030941e02d0304a01000c82c80354910000c1340083c404000d413901c0141520060396201c0e80150725000d4100d600d9265018009000794081034404485000320f42c0304000d04105c030720f503500a00c218184001070283c607103c0c0303000c0a4006101c0d040b05010b07041400d582a904400340b0100c40d8011b207403140580d03100750440311910540301c001461407001d0110300e000d801e0700300801d000160020b00702040040d03924440d104402584648004107041070030029409941200c4c100312413400c00d441c040d14024418140381514020790a10b0403a041 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 137510071 1250 137508821 137508829
    0x615080f150d05030408010606090801051b181807030504020a060c050c1011070305011b020708070905040f1e0b0a1404031407020d0605060a08030703090506070606080a0f11 76
    0x1406100c0407048904100200e10a2048000c16498207032500d201c10440007801c00c0e001d104541c014202aa00c0002a90404030b1060130350342c01030180e1250b50001200744003c549517108580c400140d01c0c030400343c03404404000c6a1541a15500c1d80340c02000501001002a019045944100d10031034400034075a0701c45006451101c030400c03000d440c6034072200341d50400d4103126491800307405060410b80c008090f8210b40e5440d00e09650030441d01a511444090100315440c07e22100001050010f400d4031801d00b810280d5428462080310300f0592602d000c6814420315265140500d500440d08011840314994010350010180c0005c8410382e120b2000191041403034841c1c2015134603400d8103541191079a440450700160b00c903444010200d02040400700603680c0c0c41c60340c0c2c0e0b0184150300114041c9403a200300650b105481d4010401600108600e00000f0b81c49480802500d500b140d0264903a482410030a00a04141d0010903040c82681448400d10010b5030f0844210b6210b20040f40350800008240 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 137511321 1250 137510071 137510101
    0xf020d02071101110d120207050f0a060b010e010c080a111c0e04050f06091021020f060307021e0106120501021206011b0807020301020c06040b1806220c09061508 71
    0x1202c280c1c0052824045c07a5104034511300107402401d80c0982040959100d003810056102c10f070481030fa202c031240030100300560049240c002d0090a16074507140071900040d00350030040d00000c01103c4e001595010300d901070701d480e1284400c04006c07500020101c40d08102e0140c0318590700808281801c840c85c00c2c52070980940c510800442c00200e1040d2280d4040c49000000944001d008406d1050302017190384440b00a412f0b2a0700100c011184a2030a00521002c1d081f1800d0550040c0010003c000c0a203400040121400040b10204070301a40000c1c5103900511140c3c001d0b2450b10048a06a4207110054015042e0544c800300d4500c511f072a01c07001900d1a2100080e1615520001175044001c0f6082c0e03000740a040d400980050f103000b040803000307410b04404480840e04e44180b43c1c18041540110002600400010f000401003414512000d072005001807079441100e030702c200d4410040002e07074083c1c1da0007818080000d004258035015040c2c1550203a070303141400114440e0004020044985007 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 137512571 1250 137511321 137511347
    0x2430f0e0105060f0706060506030c07020909071202190806010e15030a11041a06070b070f0203030f040210020c041e0b01020a110f0105040b031e0f06090f0a0f020d02071101 76
    0x4940d1038000704c2803492540e500003100c10b03240942d03280400581601d5000040d44140d000b24202d598441c102d20420910030409400d42c0710b5540000c60601c0581c1b0407500d0111910b4040380c10707201d044520424003007800e5164001d190b09016040c0001200140102c040e801504070310756001c0da00b61803806040e40c400c00100c014007a10641809003005003020382c044503100c1464060410801c940c10701203100d070f91084008071020040d440c10014215030260b103c1c08603005510165185007000c2c045488110005003000e4800c000a0350f401c0000d900070071811b084070ba00a0700030b000340d202200044c0c070540040c0381102015400e10019840961021505846065110007800b46140c0303070102344003100d90748000c081e061290800001c50862800c2002c3d510036091840040c4100b140340b003d101d000e02d005011021010b04c2903080c41816030340d035010782c1c0e0300940145481c1d0059407465100710141c84d00c5c6c0c2c59880003910015586018181a400405030140240140300f0603804502c011211001810700b = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 137513821 1250 137512571 137512579
    0x201110a02100f03020408011b0f17060f0607020904060b01020c060f030a0203090102070c0801050702070603110a0806041b03051015080a0527100b0f0102430f0e0105 73
    0x84044030060241c0708115003c601c0c1d150041c1001d0b00e9075061401c40300c415060043c044407101145580550060884845001519103003000a010b0311440860f1507014045d248108100e5107000c07069124001a5130300030b41c00034210041403e10781480c0e0001e00420b0200740c014052000304128508203c5c048448205001d0000b6140d41d46007041d240080d0030190210110395001c101310404508860b5002c00a804400000249400d0143d8060320708040c03a071103d03003407604060400c103940d20b040381661190350803410075101580d2050001401081c01d80c248807a00b0586811804002d43d050340014401c0051070b402c0090281c40c0d1001054190b515901c402c00254041c0c00141050415006a41c216840304600b82c0c607103006599100c00407545828102e0213a00c103c2c184400c048141c0916901e500007903802070100442c400000b51188520300c1036a81421008103002240c040e05c0d1103000c040c40b211000098401a036001d03105e0f01c01e80c10303c2003428013410340c00702080758102c0c5142d03181282d134010 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 137515071 1250 137513821 137513839
    0x10f02030702030a12200a030f0504080406050d0917040302010809150103140a05030706050a0c1107061d0907050301032102150702031905031e040f03031116030c0201110a02 76
    0x1444c110740070614181d00210103600c81d600c510b00395001d029880290b100003e0b84070346910039184000c003125416900c4054103418030b0300f40000304507010112020b0790204d2900c00d90701d4540c0c1c0310040103010382010003095901c800d06102031544e02034000c0c0c401c2e240300742cae03070310003a501c480c3c0f2003c3d0f0b00c00141c00301c0c1d00d003503012000400c0010780c10400700343c00c2c0c00400705440c50b03241c0c1c5484272415600039074000d0b60356507224800c21100e60314920407100940c0700d40c20b0180c80b021482550507900e43e2a40a80020704c40000d91402c44400080c810100142008086c0c001074070740b165008002d90000e110490380050403501c000d490762489801c084481c4d006500504510010740400d91003e40701030001010341c04100281a41e001d403c1480400d040705907110995207040c8890302c0c1c072401d00d003030b40115801c002002c28000001d145c03040c4540420b41502d004038000340800742031f807220712a10850329001c0300b09036004400c0503080414003c0b0706000f625490300300280f5030307603403500d0b01d882e103030003e601003410 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 137516321 1250 137515071 137515087
    0x9060504020414041d03031e070f17090106030c080d03060b071a06011b050616050711060d020c03070507030201030f0902090703050c130825061d30010f0203070203 72
    0x241e404544000c1945105c11190300890b41c407241946d0054815034030f61081c1050358040b084904003d40d421410900c0c2c2148100301d0366200801c15105d92022800d001084804105074400c02d4000002850300a0310610300c0c103698003505951b441d100340b0800702207402c1c4200001c10003ca83c05a481050300b01d070305c050669010000c1300d03400a02c01804181880015818a5500e0012005881d80244108000c11030340c02e0080c47c8071070040c650000c0c181040410401440001d81c0900ca172018950306a502a4441207440200c01c040d01511161480742c0c8008514101401360021b0a42c044a0003078174100041e240c90a400c80503a002c015000e900011060040f8985171300c25071000780d0012141140303a0a103054200c051150718065400181281c1c4003040b00020310241e608070380e4220190b12058002c0c246000700181141201020b00c3e1022407000b1100c02c12516803d00c00380c00307120a04c214441d8201d00c03004207000c40300340032600c12240d2b19240d2040340114040c401c43c0c0c000c0c24190002e5047c0300c50 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 137517571 1250 137516321 137516329
    0x8070c03080603010f060b0a0806040c0e0d080408370c050126010801021b01060807030b0406060b040609090b0f010221070503070305120a09020109030f11030f030409060504020414 79
    0x90b0616030150750380c40500c0e19990441c410040500703040c140180c1e403818801001000880c000e03160910452610305000780700d03500705209074404541500c1151074002c10341840c1d1580c2c000c0c1d900002e0f09016040d00d02c0034083d50340c0380c145801c00b400351102c59a02d8100300842950250300314000c01182c03006000740081e44c022098040d0320403500c0180c0741c580461b0420300309203134020b0340020156900400d5102901454041100e00c03c074919000f081428640f0300e8a0b0303a41c038281d21010f08024101c00108050000540000b4007a0420092030395840b9940c420041c02480c152058816042c54418651514585840d0081c3c012070164010300040000d004054484110340d0103000380300b002080b030703a00060014405004018040d442c0e0a4440403070001c0301e1056100145104a4189003894500050380c120141d40180d079000296502664143e181650b5200e51340050701340e00d44982c80000f410140000018400c1d40e103102d00601c205660340c03090000343e0003240201c83c02e00618500340c40c01414 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 137518821 1250 137517571 137517587
    0x4050906060a1a0a11030d060b250206040905041707030216050402070b0703020d06180207110307082107050a0c090e010b130b18040f0203060c07053406110d08070c03 73
    0x100417080d80d2400d004d07400380340c08803400b0394070501c03e4480118004480803030458101d8600c2c110300340314103c090996800101284218000c1c4d2442943c1d82c0007040500c00d11200d00c10b4000c0301ca0392555611001814007030350300e4240c903a03081c406482c03102c0045044d09081c001c0e60704551744000c44840c3e94485800503000384d004a502e00b0443e85e40c0f4880094200466100c84400000000d001652500c0e00e080042440c54030f00711450095111001c100103a640008210030300080f00c800c8699122180c604084041c810604040c10510402800400780201500c8903411940b0182c000c10481c00b00c00255400e031882000000d910039003004c1e482ea441c201c0c0713030007020509800034030703c41e0091082015041c282038203590a0710354202c22540c89045007010000e840e080a1002d004508050b20f65032100d68400344450205060070144410f030502e040316020780444030542d503035031307562054503228000c2038190114016400c41c81400d14151040c0d00650240303008680507a90741310740d171391f0603142070740e44c01 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 137520071 1250 137518821 137518847
    0x1e0b090109142a1c0606030603120e010e0901090b030607020613111215070201140c040b090a0305030406030c02071406040e040c0b0a0504090e0601050f04090c030204050906060a1a0a 80
    0x100c6440b895003d04085401800b000d03041c403c504514041040c10306040300c10681003201414502202440443e00070900a003910a181c9042d5400c10031820049030b50555440c00e00350031011140011983c1c1e1403d03001007400150940850b070340d556403400100d9913800d040d00d02e620401c0d401c944a80201d6610140e26030785240c042c25800c0001c4602c07440500d00250325005003040c0224101380401564203000d03140b910084465014910701300003007d42407034416445034042e01c000001d42c00b03105440e0410600025a00102940d071216522040500540440144040140502d20000c610f01c5450402e00807420f00180c02c0d40c1c10142491345081c3c184401400540d621085c00e140010b0b983d00a000514807d546941c40c10b07280c0345009410b40c15540352844c000090b0300b041005000e2619440004402a4030480b0040340b411805d0420000d00b803581d40005c0e400608000401250322000511036008010540c0c1c0040c0f15980c944055042e0400e00300355604400c0301300007080181d40f1810000b9252 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 137521321 1250 137520071 137520121
    0xb10051507060b09040f050601150e01030f0f0603050d090f03080304030315080703030e010801060f020c0f1201090b011409010e0f0406060506030a0f0513080f0d1e0b09010914 77
    0x6541c0301800502c4c041e2013280c046640701c0302481c0e00740c100038085c4886401801a000c81c0701e00c000080002511901e01c84020130704140c3d80d6100c040d8070750456041070092040d49001004459144d0030003941340d0f0b081241d501e000c15124580040d050300c02140500c100d1707130440d65440c1161100d41d800c401404030000b10300c4200210601c03700d5a540c0034040d49004512980703800c02d001c032009001604d15a4140c2c881010f0200e91402580780b942c010038815000e030422550341c07490004100c0082d1061960000c07442d650b621f8241814208800c00034590f0590740c89990b4000c004040e40300300280c0040901a03100501c5c420001304601401000801c1d0b0051305c0368501103412521040410203940080f0b5282d5030554455005060315105449025004220502246510308154545502520400d601007203900d8000a4540c034800c190380c0702c25120780740741412070030088495841d5806071040149840c410f0300081d00010724121075105202d06010f160403000300700d0340d50025660255012105031100 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 137522571 1250 137521321 137521331
    0x1302040816091a010206060f01180e100504050108190809060c0d0e0307050a0b0c0111130314190609030c150e1b012703021504030b1005150706 63
    0x4a0074000740d444031500300c2031800d04a142100303050a641d48041d00080c90b42c440a440d89007640d0104c3e007240d0000007900c81d0610071045000480b0108003901c00320f5041100018007140b0004c2c03258055010b41800c095500f482600c920401c02220420300c101105540040c40002c06070744002c00101c40140980215030410b8184004038001d030b4400707042006c40c3d0b0070141c1c2c07000d0003580049224a0307210042d0007c22150341130001045009000303025100030480040340b4140c00210940006080708800c2c91045d07120031501402c00c402c42402d00045038140c049080c0d50701d1100d8000751500c8a0450450145448041d41d25880010108640c1c29000c01044144610100d02d280303030803400c0c8960a65001442904840e4058100b8034409030005a18080e20142a1180e900c4900b00c1403041c0303002400130310842000707039070141c4010560009400104010300c00801d2004074005d08200c1e4081c0030a240d071a9500800b601800126008480e480461450855002c0d00248043c0082c18440c1e03600183d = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 137523821 1250 137522571 137522579
    0x3010c0207180f09030c26040603020d09060e06040b18070302012a03080915040203060f10080f0d0905030607090e060d06050a0501030c050d0309090903171e0c1602130204 75
    0x2050b1a104c142c144d011420b00c1401c0410048085040240691210100c1c000b26200f2428008544124401c0720704054020916450180c4154040300301951302580800141c0c0e0310350303951038139000201c4082d60f100a1240002d132440a641c0c1961b2014000d00000e0104a801e540c0107443c1c0454a01c0b8910032640f1000b00c00321401840d0039100121800707915140384500d0460415480c104410308401c01142400081c00016100003c0703d0382c00c40e0000c02c440300650b80d01612200400c04603804100d051046110060140e00c0c0828500301079140c581c3c90016064454044c155250303c00c1c1d60741c1e1b00080540c40d00f0042c12404c2d440480d006a4014007000e40081d058980405451082d115521a00d0351030f0010400c009002580e14010321082e01c1905c00890075442c0500068018400c04a02c02d444104034010036208041440d40b441a20000c40389a090214614807110a0042c50390340c0c1c060100045401c0c1a1a80180d51140c00300041a40140c0025800d01004000500102c05001c3c0c00b400042 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 137525071 1250 137523821 137523851
    0x40308190c0903141216022209050c0d0203210d0c0314011401170702071701050406111e130807060807020d0305010b0a050c100f09050c03010c020718 66
    0xc50740d040d49586414038203003581001da034050504d0003050495403082c1e070302604801210090300c40350421020041520206400418003030b81407c0c142c1160440c03641c095000032040342c0e10100b14a030080c804c486001d20b146080c0425100008000380d07055000090000d1a0a066400d0300c207555100984142048d0041c0105402d541082a03240086500c59048051103061022000d0042c9100c0343e03c140c2e028494070003e0a604488500072484000303181c0040c11450007084101d00915000050f104002e15030420b2500800058800315010350900c11900e01c2100070030282d5151569a0f200e162000c8219000c03201c0303950083d444810200c21020002520540600100004010715154064185064a0004c0c14001041104000d151400d4014001c0c80105c005940e00142941003150380c50a400e0855843d0420b06112003488a0409410000700b1900343c0000c40c40504c10740444a140c03030300300d0816090702d400c2d078840c00040c3d0040d2030402400210309200074944c0f41d56140003c07604007200440e = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 137526321 1250 137525071 137525081
    0x150912140d050705100203010e0c07031103071a06040902010e0607020307181b0804050703030806010e0405160909020319050c27011d0102100b012c0301110a0804030819 74
    0x81c0d0003051000c10a03506100041c071890007805605001140340d907050821032903503010b020f408103100500201d00710040500502100c0f030a01000400c40c1e4030b4183c2840c00d013110413040386024000026900c0800c1c86401c0601603c0e48280e0305071a1100708001e518244075040d0420101680d051051100000b5104011010756003544002c07040418141003960083c1c801182c602441410400d400d0200000b09002003049008c5c1c1381d252800c00101e03111000121a4403c06000c4d042d4020b1502040c0003407452090219680045c0d5074844a4030156551101001c81c041202c280c010b5400c00e6000c141140d64030b506c0654070007018815282880c0035206180719041c802c0c1002c042034240f01004076610360b045440100c82c140c038002c00507055a040c20000b900d521031800c400d07a8017900c408024040d81e000e8818030071070001c0d682030080401c1903281d01007442807443c40d205002e9480d00c10024064904001180c00043d916211403890b0384666400b03c8050000a0102070042c2c900c41000656200600076 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 137527571 1250 137526321 137526343
    0xb130513020904230a030807140c0105090a05060106020a080405041d160927060506030c03010f0203060907080405070e0405010f0c0806030d0809070b1303080403081315091214 77
    0xa8803030107107002031300c22001200302c0c42c00c0c1240341e00c0100f03c1d200099010305103a07030100d40c0c1d2030142ca40320055108482c0a000e00002d0081950801d020084159000140320401c98096411a42181d0b070303a150503615840c03003900180c083c2c2d504000c20304c19400c01c0d4000010100f0840c08455511601044243c200502e0307075004826561841010480c01b00903008114002a8402041810301c00d8075429000c1c0030501200100544e40380c00c0042c0b030640d024042d20152490240c000d00c414840ca80111000b948100c40b0a480381a2850200f0a118031450707200784a44c0d03002004040c460f043c031814400d014001031080fa0659240c0d404002c111006014150131000a80c40b044902d003005410141448095614802081200c40800541d07074400a000b40032282d07640c510700e0740ca444031203643c2d850280680014204c2d50001074000b041282c4600240b02d0700340c031601000c2c0800d84803d27941c0200040d040f4004000b90248605024404070180c104450522513507003c0101200c1560300360815040d40c80c = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 137528821 1250 137527571 137527583
    0x30506040f0b06010203030c030403031d060a0f0e0705010c080f040f0e0103200f040908130e010f0801110304020103020313020d05010614010206041211030403050f06011401030b130513020904 84
    0x70400c0c040040240072590464024000b4500f5842c00d1100e90b1001c2c0801440642015212103201000751803015003015140320300000e4a001e4605286a10081c2480307030031101c41e152412900d1b095000000c5840025140140c2d228144103610f9100d0200e0303600080c104001c002010000001c4c03401c061b1a4810042001c4d5022010343d40c518181614102c0d100c3780321500000400201e0850b40d541c856000e19aa0001c9400044100c018141203085010386401640044245030000c221000e0007803c49040f508105800b0342d1b0705840d054000c0c00d1fa00d0300d0303480013102d550a0020900640c0a6009144d01400a80744506c13502560340000d1314038079000d030341501e00742d5407090140180c9014842505860500303000811076810542c0c0e4041880c06a20503090800510245c00050705509000700d0f002140c1013002ca40e05a0049500d0355207071042032143c0580c050b100d5018046030350190140f01d842040061803007a41408198000c4040e040c002d01c104464503103841e204005944210742180290300070703c = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 137530071 1250 137528821 137528843
    0x30a050709150f110d210e03030f0103050706260a090f0c18090503090f0402070c0801060e0105040e0c0d060b0d06020d0b0607082b09110316051c080403050604 70
    0x6001420400d4210413540598000e8030254001c25017041000c012070f084512035102c602c0600d030f03074040206800720401c42280000020b11115201c0814881c0c140c030b0013203050b10301003640e801c4107559904002400d24442c075286815a400c00c1030b01c085035580010006000f085a142c141e442500d5040030328000c4451000385001800390001c181403281042141e414200080c00d01a15007564a000d540200c61203181d03a900300c20825215501903905c96a800100320149a8603a001030740a049140980e5091108010001032185040d000b07a9a4411400c806054504182c005004995010050640da40e50f00e802c02c0141d140c4486030800340399030040a006031114000d8407500c0070b60383e040903104d1054800340703c40c2012907461012075501801c810358000285000d80721882685010543c0480c42504d0101500d00788102ca0301e68081f1050100c05030b84020b01d10004c409000d03d181c0c007a15820040740c03035104040c100d0000c9500e07c405d026441c1f890500c0c0c0d41c3c0d642c1601d13005040b80c0446140200c4 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 137531321 1250 137530071 137530097
    0x3030504030e01081504020c100203100305240609100b0d0c020c150901081806040c080c09040302070506070204060b0415020d02010615080a0f091b0501020111030a05070915 76
    0x2049110002d0142440d101c01d86050403a085944d000b01c2c104183d10440e4002010800c04001700207903074550760565800d6480c1d06d8031058140010001c0e11050340d0a005901405049512440301070102030020184840152035003c20701500400c0140301e410f0b40c1c000030301c0200d9105080360142200d40300c80103000c40c0c41d01040b10300a05154450f09150f0140384110682c0920b0010001512803111003071901032202c0d55003120494850b10704900710b0b0306c03900452080c041030100c1c54410005076401781c02105c0a8070003c500340030313840b0f00031200680140c101c00001c0c03040e890300100400009000400216542e0346031403000c02075900a41c40030040a01032140355500da134041c0700030a02d1682500003003008501d4092941b5240c911304440300308200c1d104002414040460340500d200180c420420803030695580b510356582c1c0c039040d4610480d0022400c00250071740c0705010310007021481a0025045840d40f0b1900c201610001e46003e05200c1c0054000c6500d208900358400d6003400c039600c5d03007841070754 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 137532571 1250 137531321 137531327
    0x1020702090a021803030415050c03040f090606030c080f060402090102010905011505100915080601170a09030305010f06020705090c160308340e0604090f05060312070b0408250303050403 82
    0x4c29680c5406504148010012620070707561020030b00030f050406076552030602011904511454002d60011640d00b43c0c08900400e259200300190f91068904000422800c8802e4070300c8031003110b201071f442e0407980026105082c150090b2170f0f90700041c000845e80f0011943e0721800c2d110080c0f1809010341c1d42c02800c01c603600d070090602180880b0750070044001070070241c1c040410440d4001500134400340e10042000ea911a28800005420b940080b02203030611036042805082c203400c0940002e820f000000c144041c0780e036010821680150003c0884031303c0c020900c60019802050054810418040d45500100e201501204144642d0741c000313881c641100404014071604080f00400c2c42201e09174580705520850340c0180f80c4041c01c00c51404001d8800290092040d074000036002414580070500003081034100078000d1b10220182da4400b584c011065110b4069100e0203402c0254120114001ca00000c00900040224290550501003c2d550843c0222241181140003907525400c200c1811340c = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 137533821 1250 137532571 137532607
    0xa1d04050606040509150402060409110a141c0f0605091003031b2a091e180b0601050c101407020f01050c03010504150806330604030b0901020702090a02 67
    0x50b045904210034142148040c0c1d03070703129080103102c0b2006044003040c01d40d41c918050310000c03c0030450a2041a8042c1451a1103402921402010514480120108060340c00a03200c0881450011621148602c0c81100241803602e01c8007100035610400031405440d00c48203117100d12501000d4941c001c2c0f4516008048001d10140765408508801030a00000c51141400d0a81e80c24000580702190303425010079000754195100000e068608070915011101114504482001000701001900e440092001e82c4081c10b03400103000c010030200150307256015402800e0300d40110300071a02400e50480b0128102c44404d048201408004070400102681c1003102295152155000b4407881c03d08092400e80c83c0410b0107454031903900c44040f00404250001c01500038102e4100701ea19509050001440304105100003d00c407130701007043c1c40301c2d030114101200b40001c40075082c0d40c40d00f440c6489400e0019409000114295002c000d0354016946403113000c0d01410003002d006995090512407264014 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 137535071 1250 137533821 137533831
    0x70602100608033a0615030203090607050c16060207050f060a0909330602060f01080703060b013b0a0509160c02060c0d090b0f07020f0a1d040506 64
    0x81c00c161003488151804016100d01080412050600044a8900c07800c0045050301d00506094024889101c12240d6001031040320f03c000341d06c0aa11030000f604405030b110880b0116a258030280216080503c01c04c002c210f986034031420b44e4010750090960ba04e000b05940d02480c0160700c003140500541c9002c0c2d0320100e0288007201c40c1841c3c101880000381a080b000d06c00c0100e420394416450a41031001400000003e40d41079400d91041f1040c09407400500c118000c1600520920340040e58601410280c00d042c0c0e0120380c020140c00b891540c0c2c44020700303210502e450420140c0551060360315601c080401040c075100c01203200c41c0000d5800c4000078000314480c140b0486001c0d400704951b8030b03003108003a0404820902102d0383d0b006440280c1d542d030080c500080d08914009a603c4c044600450010b030750320b0541e40c2c2e0202e1a80d03107410380546070160101c3c01801c00c40070031580d0014641a40b0300140354101130101c0c0010341c1e4520f64148040403c2c5194950049036404000c1080002d0280561103 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 137536321 1250 137535071 137535103
    0xc08060a0f05060d20060f0f04080c0406080a0b090109080301120302010f1a1201020915071109060f04050702070504050717101d0705070203030d020703030b030a03050327070602070602 81
    0x9920517445011080000ca024103448170301035409205070f505d4403421658064210408159541640d940501440c1d006105140c001c5c002d4018071540e0780b8107030286504642065000305078040b03040d120540d998501500e440311541d80c070002c840009c3c100034080d5000701042c2c015690154800c1c200039007035036004840c4640c0586001c21078071405403880d8400201d500143c46202c03141c1205200c0c00c5c02803007030107880c651024040f05010640e6940d100103180040c1314071042e0348089098000d004203810146c0b5800c0e0300102100c00d01c005414568841c69102b031003032040b03c035020355600101e002c8500c1030360444005811007003c1c1000d0f08240b80c249403c00441031035034450514018034028050b0000703405411507a01d50001c103050b54841c10035510019001000e8913991601030045070000d61004004070080b9003814a000400d02d004100c0e040502d0701074590920f941e8400ca0003049403030f005020740014170ba40301500d000d2050b04120f4480a414241c000704650b074186040030389052140448400b034 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 137537571 1250 137536321 137536339
    0x15010810140c07020a1205280c140d020409030206060a0b03061c1b0605040e13020d02120708060103050a0303052203140d020d0c03060503010b0307120c08060a0f0506 73
    0x441c1d450603008a620800405038280c8581e002e00c00101c4200155000203124241d40c2054030034040003140d01240100b05040030100009074622078103003401c0700c09024101c01005402009602c000b40340200380000c0081c2207000d03102203070b400201102c80c1070b4020350043e0300c0481001400d0078642c0200000c0c26906026501710325242c40020145011781158070203a5601e00c085c1c00400403041340000440b121500031000f5141c4038003000b0301c076400900c10f5040c0500040042822100c20003c600342c825005040c0b003c0100c299000d02c100e0480c034003406440c42c45503e030005509032092008a010714840d80160410310280d0030001c041c0c500141c60182000c06110040802e8003200f0400209203615041240741840c100501d900c0c180100f400078642540009025030401695034840d00048485860401a60383c0391014182202c0744590500e8040c1c7c0100070a020500d100c0f085028854882c0c4c02c0203645a48918a0905018041c1c4400780541d4a8101d41c510801c054040d141d4000b0040d9520700c0 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 137538821 1250 137537571 137537591
    0x10170109021b06240d0c0b09150f0903010606050f030406150833010f030609150204031203050916030602130909030206091504021509010e060406090801060b0c061b0c15010810 77
    0x43e60162880f80b203001100c0090803441d01d80b5001c40341c529101126270245d81380e03421908101c542ea800a09507a1080d46030034000301e826030150081d9100709000a01d13481c1596520750b04c200041040386800c44040e03007002c0000803050000c1101c91a0141441d000c520344034100c014134003c1310400c0803280d441c0b12840d8010701c598a41c0c900c0f00c0c03086075001720000c54103c0c550f040140a0340035141013265000d00014010050000034072034005500c0c515030701085030359540341c00e603034450095140071441e074107a00300104049034498003d0f211400141940c48042c1d5034410100044406108045000d6003101c4100001003009020f0101103408540308041c461500ea40000c0074084100c640710035051000c907024425910030404540c0b031382d00142909540d1a25004050941e00d0301d07100d60400d41d82080d0001c00c2d500d8044059807003070441c0000800325a2140b0074218890b140308001094600028051890f51032400c002c007508248001680c04825418040847d080c40300c0c103103040620070304118400e2 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 137540071 1250 137538821 137538833
    0xc15010812091c02100e01110609060601140c010603060603020310050610030f090507090f180f0204020c28060b01020a0c0311030f010e06010510170109021b06240d 72
    0x41c0b95150704442c1070f19214907280302016000d91030a0069000310940b00e4181040d508403918501100090300c6182e0f00345400007182d41c4e1b0309000c1301ca140d03464001c18007080e402d50168040911090207000b1141c2401d043c6034403507003118500d0340250703500380d1242001c0081d0705040c49495845e40c5c08006c18042c510b440d030007107107581c030079000c2d540101342e83c0d01d41898407014142d22450350181c0c0102601c00351a43c1d08503a102030071001c2d0800c4821850700e4002e16008041c0959209c203954030080030326120300d0383e4003048000c2d0032044070350b44180a52100c803614010300c1b200e40001d07401201020f425030002030034408100c440805059056500680c85000800c0c0300000040850394001e440c160440368030801f20b4102b507001407882109608041044c0d0340100e011606505844c0c05032402e039000001c00204842c4150740c0140136107603071030080051015051580041a00002e00b0b00d1070000c800310311000d00e203000340440f9043c586030002003401900076a001c035812200750044034003900ba03501f5601c1340 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 137541321 1250 137540071 137540077
    0x3060f15090f040605030a0b0a0e0106031703090115091a0d11240a0302091206040209160e0d08071209050609010503090a0b010e010e0112080a0509040b060c15010812 73
    0x2080c41442c5008080b8250798694002501824001e401e84410035502c2c50900c0345080c0558154600c071307090102c1980780050500c0381004485e001203462403000000d01001920703901c080c0c0480303800d5403103141d186a071803802003081c030084c9000840000c106080417006c6103400144455035108004140c2c540010401c2441160740c1202e0480d4400320500c62404401c002900c4a400c1c01502040032803214031054056010b044480300540d034a02000d01c803c40003a40b244021a0001d500000c1c84000c6840b080b0398813410140e0222900741181d0907043c1d5000a0090b00300300c402254154400103c1d40d040003d0060a0b6104c02d20a0402c036500c141800700041c2580240003000303040140c00720014690a000300403c503007090300b088042d5180d584490810710001402d004e42c240c0811420000101094109110000550012080345c00c1c440c40790350860390f0307600107100c072039100d5191a9508842d60702d1100030303da0580c80f403004003032990340492410b401c0001640110215003000c12070030144c01d041c00803 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 137542571 1250 137541321 137541337
    0x6050a081611070603020903060a0204260a020303130303110a082b090821060604350102180316050123030103030e1305060f010e0307170303060f15 65
    0x5403485485903210101e80d180107030200c080b00b5114100340001c0070340c0c0560040413800002d41c251707000c560790520404103912941c4607449404816804450700501558400b04908200009a50140c03c168000034515000700700603002e103800300c6404004264005c5022420140b10f14013818a0340c4140e140c240c010b0203095003600c1d00d44a19500ca06103840075000c83d00600341000703801c104401d6a0708102410b42c101c0c0c079050f5043c8420007880900c00007503220051086000410342840c2504242c1140f52926185404502c04031390b0740c42e2004003c940200945850035058001601c40720420900c00c0586030000d842e40c06504040810843c000400c1ca0b42400d442007820308000e013020300138116500e08a12003d9880e0010040f001008040e401420020072460440346070308901d131014030842c00c0302c0041e5030700b0380c0c010f08581c91380c85194050001c2c440c803850010309541100c0c1d5160b40b20300ca4454150714006040e04000100225450030341400b0016150640761510030740300d00700b0309201c1d910a440c8 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 137543821 1250 137542571 137542591
    0xa170c1f20030c0102040f09050f0424060b030f1f03020303030a0209010c050d090305151e040302190c05180c0d05040501110a03051b0a05070204020304060e01050c0d0606050a08 78
    0x3914512541c042040310703000f10512000310340c0c0790360303481d030010319801240101c00b281400e010200761001c00c00c4411a0141c0d03080a8aa86c0d0302c15040064400c4101e1072080c003030b48a4549900042c100800d501443c400c01e141b4003202c0081c6841d4210841c0d500105180d548042140741091000d6140082034980c0001d0100c40141d540c2c107108016030303526031140c0000f00240308442c0600d5280d5032008007541101c0c4242d0840307150160720000c4090b0300710101c50314041c0c20101c90402c040081a4001650014040c1c015260300200c42888100c0700c1010a0003950404400c010401c95401d220481c00b4603040010300c00002418141801400c80c4510640f105d615911600410305100c02076104084401c03e403040199542c03070f40040030b406003500300c0300c080b0340071600c1c0140104180a0011100f60544544d20245015907540c00c01009400242c42034505681e180740030326816400b4030455009a46040f1400c1d1075101c600c240e40c082d5103481c0c011030b04221092004015541d08004a1500030f1a105 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 137545071 1250 137543821 137543867
    0x108130201030906061203050c07050a0b0703030f110f0c060c07050d0c030e040c030b01110d020c040207030c0804030f1202010e06010b0d1407090906080105040b06010e0a170c1f 78
    0x20800c5800317440c040d00010020062141103008140c2c0040042c174503c15450141c4040d181d0710803c1142905d01d910900412400400140002a203c0c1e48000b505100100d070000b40386c070504c1100707020754020340240114071000290800c6000000c00c04d90764406400e60ba02442d00d019980c8060f01e80211042c64018048284036030010140942c0300030450344400b0703004011402600000802a1402d020320601003101d0801080d0b44100105140380c0c400090b400414030409005c080c0b0000398803942050b010801802d58250000b0000e80003000214002e45009041000908016044a203009880b406580c58010456100d020200c1d2582c1103400d00c80030192240ca02c03084500252030040b03809440008140204a10b5179081540482581d1250004000031500c1d403103054201d5a0aa501811316020840042c2c5658418602c5408110016002a0150f03540710201070054000da41c042c1901e400c080540039141c2001c140310381f81101c4d900c1f02d01f54001080a00540120710f0098030b42e250440329 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 137546321 1250 137545071 137545073
    0x5090601051e03010501030b0f09070f020a06060e100e191a1206070908012003040c0503100501050112020313060504080918010806011509060509011b110f01081302010309 75
    0x980199199150304022800030040311440010b49503209000c0c40303021918220a50046007000300b80203074403520190a0340d14544840034203581078040c1801000440c480c0340f102c100050110b0107050300500304240320503600c0c2401c02c5e8801000b1007030b4100341000d004600c00c200e107200074906a03488a030301c0b240300000c6280c0788450300d1030840c2007456015048004d000800280b90740005030030740300b2042590381c181d41c1078550b0400ea080e0341144a0040741b222004254004d44103240e001150801d20a49000c00e05030741d01c0380442d040c008040210100242d942c0f00400031540c0110f51014081c1c2c01000441c03075841c200080512115100001a00722035a51000070b0400164074121200490001c101d03e012204800101003121001d0060501c0781c09200000502c021030034540c40700025840e11081d403194107000c0100c8141e00304d000400c0c100610300c01000440d0211110002820b4000d0024941c0e0403407100620858006002160781000704042c1080f00512000d000fa044607542482c02042ca00d602e = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 137547571 1250 137546321 137546327
    0x140d080715060b031302090a0b01090918050d05040603050112030807031805060a06050102011116080c0a081801300908040b0c0619090804050d0302010e1006171605090601 75
    0x2458012840c001c034000180154680145180b03402c540c1300b2103041f02c00b07580d10f00740441644c0c0040c02e03c50209074204018001c0f022240c0010b5000c840600c81e66400151944400f8a441c81c07503490700001c82c200140501c8043d505008190242c41e5024200484038a107960090810800421a0082540d00c40b503641c80d80d569808002090358000c8200e4820b030804848040c004e1107240728050140d843c00503030450b2401500d0503200780e080400707001000081941ca48075a540d01404c013160783e5000309691503001580110103001c2c0c440c45d5400104441d80e4520000d803202c1390b440501c010100c1c00c0555002600940c40500c0e413001711498010446041901e4070102034040ca402580c90b41001007460f0035120341c00160540f1550a01241c406808071030b00e00001201e00c52003011746459800c010602180c00c100e079803103908030301c644000607040ca4100001800c080e13400031500e82541d2180010000c4d1110380c0041c2d00811901c40280c0b02107050800b28410604452003920701030801c07500080c1c0c1c143c2c0 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 137548821 1250 137547571 137547581
    0x40b09031011090109050d051b010203210402090c0309070b16150f06120803010b070326090607020d21020702130504060f05010b121008030a050301140d080715 70
    0x1192034040c03210141080144650f5000160001d0001d1080c400c00107051511714a0b5042441d0020090303c20707103006903158501841030908560640c401082041004111044100764aa64076a090005401c10744100031007001d002d00654162442170080c80051440030605004036032a19a80c0b80d03413a030750b0300848241d0410710b030000b518500d41c10700400c034106896000140441c801c0c120400103240c8032414070319045070a20000d02406014001132044020308001400054002d00380800c0d00080310130851101c18240c1020485605e02109202c001041017144c5600114280007800c1e44d208944e400600c21600080f259850480005440c444403280358125071a064010300b4403420008902c0c800c101824003a502129080c3c60b01100031103c81040c803078141650480c0040300c0c41c001108007142035044015081014a00b8103810005000d6003c100801284406403070b81901c2c2e40c9800c0b00c0c40c41c411a08a41d450007120503950200010380348408803036200303034080904041083c2d14014880144 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 137550071 1250 137548821 137548843
    0x1302010908010c0e091b0a030c1b030f0314070c020603061809030a1701030b0c0714030c1f140106050304031707050913060324020d0c0f0206010602070308040b0903 72
    0x2503e000300700d0344a95402482280390502c00d55a88496448079102d800e050216081e52014030001031215181d194401d402194550002c0c0c0ba141c04200c0300c801c450304601c0041032080300800c4103081c02c0340e0b000e03400d4000d0341d000d01c0b10080100340c0c1f80f5103890040e00500503408024032902000000a541d40e5681015905204140703034884214507150329000d90341d0380703c524140c01007420500b48a103210484040740341070784d0703201806100361389803031800702d855800c0710400311100461044402c0c1c05400c20009030a035204118024100c15541c2c940710b40ca4054808117180c4498184036815182424a0194030b04554040c0707051566583c80c0c1c10120341800c805030111414243c408180007a9590100c00341401b05c004075400c035003a840c0f12010008881d168400100f11501182c00100c60030459001140c810800260152410559007103039411034a6090840001c28034426546100300d03810406240034103001d000926080f401c544942146001d54810070b5440400000c44019a4505101101c40c1e1 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 137551321 1250 137550071 137550073
    0xc03040602060108060f01060e060c0c0d0b10140d030509031c090f09020a0f0e010c0515010e0708010810051b07060c02010e01180b0a09150506010306050105121302010908 75
    0x280340c4608009444007401e1203894018032403507002c0350100100e95000c50498081d03031680e500302446c04c4244a100c0d00005060388940c00764242190245d120b060640166521460012809140400e8040c00912194000d018655840c0310700d51501d8860360401d641aa0305400c00d59160141d01000900d80018940b05002c0602e20a40800b5640d41110064040d21101081d0038506925856081e00b2409140b40400c00130b4684030340041c4041c00350000d890070900605d0f00c00e95406240c2c450600e0406500c440d2502c00744094010403901d07111103041ca400c445a80790003c03079035240404031542c440701103114a034610f9640340400c420340400141902440314041c103041c1c551941d0308000c8024614442a140594249950340701700e90350612074400d5000d540e062030b0085040e2521240d6400d0401441c260303820341c0d245024000300348142e8050007541f0020001043c039240820004050394055401581800418400c0300640d1107080e400c568003001d400c0c0c1804084441e03000481c0c2038500740e0b001101d2 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 137552571 1250 137551321 137551327
    0xf0402060f070b160f08040b0916080601140306061e041401060c0b01060e100c0c0b04081e06040308040206163905030307120306150e1306080304050409080c03 70
    0x1c1200a2039250b114580803000c41e04c0f03218035071009990b8900101c000380001440d020005001a0f182c0401079000766440080b03501c890807041041c01e0087c02c0f034000031900c1e88000010820381038a1904100008826406000c1c1800d260b00032030704c547e010054495109112071390220858447c0c2d480f181d0949042c070800c2d07809503540d280151454046010986135030b181c0e40700200315980100000400c80b1005000c070303200b140222078200d0746c000400d0011a01d10a132880009078070b60101c1c01600c041c0c0045070150503c801c400700c00540c107468849029510b0b400010402002c41e802c0680c15a105070140c40c1e642e52000030034020f6448040c030810042c10200e5182c110503284003500c2e03000c08687e03c05200e0300750501003420b404d58079040354030a05605a204000b90400548a4118507080011508010807465140c02050101d5444148050000b403000000b4148034905801c1c00400501c10420130007100b81458001d613140d00caa801060701407915001d02c0d4081091810448021130001070503262 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 137553821 1250 137552571 137552573
    0xc04060b2d0720030c150a05090a0b09090106030e0a080c150c090406061e03020c0a0c03060c080606070c050f010903170403170a2a0f0c0e0a0e060f0402060f07 70
    0x1107010380450000040c1c44000014481d50a001403415003622004003800c4a800c0c444c18150156888a004101003000038802d420340c6490b0ac803035103006011400401070320f0350720203230502c009144141d11440400d800d02c090a449040049090180c80d504410b140d0340d1000013400c1c19140c011400c8900c20410500404c2140905004020307051551040380d0600c40c0c40c0e500c100403200d40740194071900c41e00383c500d03421011090207503000302540443c01c0103540c0302c100781d5101c80305429400d40c8251021a250f8540c3c8051a500c030000f41d501c088116945802c2c40c04030b440f123801c5184240a0303180503215481c4520040d81c01010724100070340d40a07192004d0410b8407010070459802c2848200d501ca02ca81c03409000811720b59082d6001d41d0400d584a0310300c98004c0d048a0482404004034000e401c035401190b1000c6003100004401480c0610440416949001c0d44a6401b03403000308903100346840e00c090540803070700102d0865000750002000501e00d403645d0002802c1d030301c2030040c441c1a004d00090b203d0 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 137555071 1250 137553821 137553833
    0x130e09010902040e0c0112020309010603080705060f0a090b04030809030408031612020a15021c0c0f0e01050c0703230a0b010e01090209060a0c030c150902030c04060b2d07 75
    0x100d2414402d440031303c03e600000b032845a607410000f019a000c80d08400c04003541074605c0d409150300809030310011425a40ea500c1702c2219620014082e074041e00a10100841c001c284103400e40c0100e0128020019a01c0c103884400520002400040070442c00001044040d8020030583d00a40000c0e000d803907554244c4800062000d6102000301d0f010041d804600360403600208038125025004861001c10301d08010181000754040c000401c200031980345000e20f5040d40b1301c94060410a42d0319070400101641802820030041c140320b030703070401004006203041c0c42800704140003180d51000c80081402402c0217072040862105450f113000384121103402041c02815100d90f4120385601c60341302c0040c0d880da40408241d200300e08280d60003100420104080601c6030350030600243c0170b440c0100e4901413541c0c035080c06240144081500302d450314445001c0d45401d00c900802050101c9040003018501550423400d4020581c89907030f02c00036140510b107002075a9034540704401c60400c0c03c943d100c609140c11 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 137556321 1250 137555071 137555081
    0x61b0b0c0408210301050105070c03150608060901090512130b03070215010f03050d080406022b0b011e0f02030d0203010602010c0809010207020a0b090d06090501050708100317130e0901 81
    0x32846a11403100042c078038000e183c054044024400c1a441d14507820038006451550181c082200d0300740d801000080441c600c0540070180031201c1c10082000782c0340006543c548000a031516141da45048101e01c0062070015401c01031032502c114198035541030b918003480031846544034000501000040150495010982c3c6030400382618603200301d0703620750904d01ca14035075a000c002c0842c1e008075064000140203600a9911511511002d8900f10080706005211580690740c0031108207100c0301c2500520103800f404036100c2007864111989042807940742c01201d215811312040c00340c400c05d4010650310038030884450340070300b120a42d84e07540c3d1b03484024024202c034010640082c0030140425040c0310180225a107054004040b100c01d581005c1003190705510240c0042d81c1b040c80c403d21140010b56501500700303918000c0c030000600b4a80000d0103801820020315034002840200024000121110100d038500000d000400d03071030704000800b8442007206908007034810b1000000300800d10b03205402c4 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 137557571 1250 137556321 137556329
    0xa0b090405150f070512040c080a0f03020105090c01080604150503060c030a06060c020d03120e01090305120708010f090e03071e0c0905101206090602070309090b030a0804061b0b0c04 80
    0x4910883c2c0d8030911518000d500c03d80ea440000b4808001812140680029481d00240500c004280c1203658a0780280b501c030544004035045001041c03180b09041e0284201c5602402200150100d03800850000341001402444c0d01c1c0700e140c3d02e020300305a02c1800c030040c2d00500406000c8440904100740b6110450304111459503106090030303400b094091040e564206c9460780079050440151070b81d0307001d98185c0e0395002d1170007034150784179204803c402090150411003400b9480303ca070340781c40f004241d94244400400c16014400c0b00c1004200b008040c01c84641110100b4400140d900d00d901c0072242184200400034003910900b0841c56801c01100310805505031007021440c1a099440710402d09031101142c645d40814001c003400c0010b8012440d0022060b1f10403000041c0c0d0130203070703510501281c02982080c2c00241d08408281300856136403141403003004084008044d02000c0b07603988041842607025100070402100740f00c9907140b005070340e0340828980c090500700f01032408403501841074200303102e = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 137558821 1250 137557571 137557603
    0x50c060601090506070f0230070803030c0906030c070828020a030e1c020607060b0a080c0618060702040f05071409100e010221030117011401050103050a0b090405 71
    0x1010480e5903008608034070843d00090280c500780700381d50700c41800d60031040c0e00903a041740c10050303503110564030700d820902600030b406007026001d40d084955038504001c1d0741100005500030401d0040d0030001009492156400b1522280d5940e500c07900b1801c0c0d07001d24140180300820104001a0a031540c8500000d507800c0b400c690489860104000c81e40c900507098080d01103000b506042e98641020114034008070b11048500007007035125030101d55a60b11819090b2051a039621081542d0301e0700300d2a07030000385900f6004008a40355280040c20a11811800d010f00a80f440018001c9031520790a840269030020b004100e13410000c401e200103402c0440c1d0080c0080d03a01c603040c00440d08540f0507103500408c0544010410401100d05890a041140030541988900119005100000c16120000e078128075081600c80d45890b00100810b07807080c0c00c40003540d05100340002c04200c0008160b0448500340387c00305680d16a088610000c08142d01d401d50481e121500b00030030f00c400000c02c0424440886 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 137560071 1250 137558821 137558833
    0x106060f0318060506010c170307020c0a0305060c0d060b07030201060306060506041206020306060f0d0c0e010804030815120708031e03040309060c02030312010e0a0f06080703150b0301020307050c 86
    0x105040702220310884540300d0140008a500002c02d1099001c25405241814543c069003104e0310f410a01c10707880b81904a41036070000c200000203906100100b42100c09032000b0214504681e80c0d02d450300d40041803005000008141c08140c0790281d04044006c12031040820768480035410020301815080c003003074801500b4400000b8071410200c00700d5013168180700a10911480ba5646c91010798406000310b03900c084140a080c42c0d04525000800c450018900c0000340c1c0170200c100601141104040c06041c80044004c01020a4003c100d495018022b40e2500008600900c0019843d4542850003032143c40b440c580840d005070004000e08c0e401484886410343c0d00603d180c00c8100d480129001000200d645174104945406441c0940740a0710080603a41040b01c0c43c08138003818a002da10621400e59183c0074400240a584142c00384a04044800e028003070038035143d070384d43c0d40b003520004083d0040302009031503500c100da102540003c0000e0081d07540c0c0c02d003c00000c0c0340d0740102004141e40d006034 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 137561321 1250 137560071 137560097
    0x50109060c0509061c06030c150210050f0406090f050d1d0f010c030503100e070e01030507030b0f0d03020f01060b03060a0b030103030c0f050a050f01050915060901030b07020f030a02010606 83
    0x10350140c0b845210000c15040c40d001c0407002c40402d1081e117044036107440351500408400a0000400c60024021350a48078100d010710301d070003d16164082080d84203861a04c030500c24811102c0d486641d12030f8001102245044080c5015440501001005000c50144804500103030703502019074078504c071215101c40d02c031124141c108a102002c212007240480c00109541002078002d03000303175030b220080820b101c4850327503168440110401e040f154600003481d03901100c18250b0300752107000c1d003110070307450304100e0f8009244c040380c00c170010030f800c0c00d10880721b00c1a11001c15100f008a0000808941b00030f11856642e02003d100316013007a00c400307104130700005d00030035008102c1040d00d040b203400d0760341c4e1200714003c0d803107450000046010903a4035000d6608030101107401000391b4004000b400380000b0f480d11f4600004c0c0d06100c802c5026001d55102601402810303951903000c0790540780c010030b0500030b684500c4810391526611100700c80c0035000100e1581500b0f034040d0700480c21038806480b660048202 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 137562571 1250 137561321 137561327
    0x804050a0f080a0b0601090314151503060105040f020c03041502070b030f071404031202070e09010903120b011704050303010302010906050c1c03020408070e01090f0507201504050109060c 82
    0x41806440c1d0b80d984800d0480c40400c082000d45070f000303d4181081c48604c0e481e51142c00d03010024080710400d0b6032180302040c20503070004980d50b90000300c203440a100400540300013074440c841031140324812601da84610400406c90f0b4111400c1034001030403a0b48d216505d161650300015101010170150140440010b4288042c00480e0320034902000500304640c0c42800a64030350541c1811450805018407003c0000340314861111305640c09500140300c0d407841d000c13041e100f40341e00400320f500341c0e41800203900c00290000b5000c1e0f645c100385080483e5603410f04004985206480740c003075420341d211130140410b0050210007141624001c0c1c1c0c84600b05521500e0988052082c40c0c0403600341e80c4007184031442c0c035551076001c550f000d89500c0c0140c40c007540e4000d19841c0451582040d4625490000108220031040c4a40b80a400d103030203080c00549010310015028031284541d08400c0303882e45802803403484041c403034589242e408011030b0300c4030b00301410401d000340001d0320225000e81c64280c41b6812240 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 137563821 1250 137562571 137562599
    0x70302030f0109210e13050a06170307170c0106150e010302040f06080402030111030109020a1b0203151008010903030506030d030e060105010f030b0301020315090c0a080c1b01090804050a 82
    0x1d0040398090811360011320380d10060b6070507000581001030b46082d221543d40c9480c0711004c40042c0c40d4000c5850b00f042904d40381100d8440d40018007140c0341d034201500c00c507004030a480c195508040505c20003070055000410501c51a2840f4425501e010300200b1000e05214114001c02c84940e1001141c0c0036001c01074040303103d1405003601c00e02082c4400c01c8003520030342c03c1c00e501034409000880c3c01c1079414445101500203802000b1800d40101d21000e40c5540851490410255940e0520305c6c01c1194001ca42c032100c603c00c00ca02e5039020344000a12540d20300c070248000b480c41340b0003000620b00c28103006008042c10f41d4018400d0240107191207040e4483c0c045c4014400c0c5003009000e8991030b0100644a503084481401e0034151250702c0c0c2e001a0758280301a510412585070408039500c0c00da0200144003200602640340d07020184440801d01d64041c2d002c6621140d1091103580c0d501261030b890701c0c1c07051440c3c11402150700b440c0040040110036170142007141c1003030385c0920b2950f88542c04440e0b005 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 137565071 1250 137563821 137563823
    0x91203040b01030b06030307050f1b04060b04060509060c03030103060218030102030603060a0b0d020a0f061e050708280e09150f100e06040b040303080708070c02010c11060705070302030f0109 84
    0x81c4400c0e00500119211510040d08040b0080449203801050b41d600c0b801c5c0444910a002c0d5031b00284200c81c3d507001049000842303000120313010001d641c103003c001102401140185810003001082c1014192a410110ba105c10041c0c01182d44039030303491400c03a010354002464503c80b00b224124001031070505000756402258010040c1040d03507118580b0000401141c9000e0ba408545d40040d100981c4503000302c04090801640c00110450800c18082c101c00d4081800e03121285000200304002d83d84001526240e1340d20500b180e640d560740141070f1a00e1080588440041c0d1012220b030700e401c40e0403040030401d14000f0f0300c002d64150f40d001c0b110b11800300c40007021034002d40d03045001c40851178214446412441681040910400858085001d940241e044000344880000b230a00c1855006225075511654916081c1040e24003014010b0101c410404000c2c1441081c102003010032010741200341c0300b41000341c4099104c207280c0c1840703a40c5a0051006a003c0d000d00c980b012400801070207000011 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 137566321 1250 137565071 137565083
    0x903080d051027050402011b0605010905070905030a0b09071503020310050a0b0f070c081c030e0a082208030307171308090607030c06021306030e0c0312090103020702120609120304 79
    0x50148401500c3c064400100128100040a60704031012941c00400000d014007030300c4005002d40c10046c0540c100c1c0c002405107418886820030400032580c3c002090745515a01400101d400c0e11150051868440c01c1e070890251104c034032000c4019598190b0103980300d0202c0311000c03484680c0e55014004107058601512101031000c0086035102c01000004045007846000300401603981c0307182c0b541c100034403000c1490300c00703408000004c2810380c580a6031100001c0c8001400d0011070960710440700e8440c503120001c804109000c807034940303480148010028a49030003526030361301c0c2c042001440c0c03000100100b40e80720b0400c0081259410300c0c1303204000311640440c0240c81c140c00d450410070b86030002c240031010040c1401c07448000a40500107002c6480c044044441114241400542903d20807100d0612540c08036824444644c0e001500b010442401e03019540d80e9403441004030041e202d88e01020350029003204219070508000500c2030312540817882a0750880b1072003d995000c0d8407081d100a000 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 137567571 1250 137566321 137566379
    0x609010602121602040c021509060f06010c050c03150901060b13090914070306050a0c02030c061909080c030703030501050d05070905060604030f0c030b07020a08070b06010903080d0510 81
    0x14581e4200d0003481030143c48540c48000721660b0340064107076107601c9084801600041c1040c45404811803089811441c1e55015082c0c51500300003211044034010026410403141d01d03508401d1003801c0c03180d40c00c1400090103603074004095140c1c14907040b03c15a00c1c0d44282d031810078000381071b0365160151a0000c9519504140305854004400090100607000751141c0131110303035103624162b0800601006602c82c41c0c0100342850b0810003c401c0341da0701c3c0401c4007550003c002c1c80180c2c80010400c07d074001c0002e044040d8040080300003600910394030000502909000511484000c0004040c0107024401d68040c009030fa03c51050080c0c0481c1d0500007040c4d80c0c40320301c0030b00c200780d81904641d03400b11000d4a038034101542e03a101d00c01e074080b1424040e955803d201c4030600c18000300f4001182d0043e00d50009105400742070351100400c3c0310f01c0308094113006003180815000c0e031141c030818004580100640391641c9844c11814000e00d4140c0c0c5800c140500500300240c490421942015010b113440d0030541 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 137568821 1250 137567571 137567593
    0x702011a0d0813060c2001080604091e03030207020f190e041b0b070201091a0706020306060403081306020105012903250e280b0a120c03050402090609010602 69
    0x80207100254100ca407510140b01d60340189201944110040140740e0710041800201c1c140740300d00d1141140c401c0d00f0708280000031880d0703907001f0001d41e412086c01e40700061803101c182007074409081d8941c4a6150514050342c40400c0c591703d5000742014500880366010824590400c120801021000300384030310780200030800c501801281072651040c003500780c01c00a04c680d100382d203c0c0c6050503001440d040380c010880e130065580c011a85030203403030840281d41940c1520b880303450f802d02820790010515600000003035407a8a4000584d00190ba100c40710f00e4850a0000c160100004c01b8001c42c001036282000004910044401d03002c0b01c0140c60440000215a00040c404281d01c010212110030010b200c106802200c030668446c6150025901d5102c3c5070114010040108025032001d100ca84040c6c4520310304404000c0c01000300c0d07a01445050f41d8003010001990a1900da0b61110246840c00207100d9205030150000d0f48624030840e0380e1134213982d540303081141c0e80c9400e002c0c0c000103a0080615403 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 137570071 1250 137568821 137568829
    0xa080105030607200709090b040b0a050903031503010b1e10030203060105030c09120d050307020111072a0e01080102040303030612030801060318020d050f0106081207021309061a090702011a 83
    0x1c40213001c0c81080d036aa9607120511641650740780e0f6000c07152249003d0400c4280001d030322251350400d0b01b0740002e103d01d051030341542d50f4038000a0200c0500c1c00001000c00c0c1603075000d43c000b6983d100050041903107007003002c50302c42d01da1802c0300341c0c10300600502c400702d8a680d12074422a48188016180d0505680750b800d48081c4a82080c6040c42d04502d9090081e40071010800c0190500e44090b84d03816920b140c1940d000b0b080d2800e405c0b04140c182d50034410540050000b00e110020140440112170b1000e005424800402c41d2603840384c0c034050807000c004580304034190010811360703000792002c1c000141d6500090700301c0780102d84064000b802003c014020a88290040c001c05e0140703600c804000382c480c0d000140b2040706101c088a01d1781c00007071903c810203000e0013240c0c0206885006020a0b04400b0b103202e03200d10801c0340c024450700d041c41c06819500203d80c081c0c5441d50b0041030070402c0c0400c100030312503005c0d5150040340c440c40035038000076145881406000300c00f08111404903040c40d0010240 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 137571321 1250 137570071 137570117
    0xe0f040320100914011b02010c02070810050705090d080c011104060c150f020f0301090518060f091009030f081b0d09020d06020a0206070906020a030e011809020f0a080105030607 78
    0x3c07903984d988082d0b0210b4045090150740240405e10070003003c5103407061800780c2140d000715011015500040130811004d0300100b0480f9000d100d989000c01e49580320202110588502582582d101303000c02516824890094080c000803c12900200000703001c022081501d4041c034400d03000011242ca08035400941d0300c200c4811240d2440740085114400042d0321030aa03005155008403071000031004118030005405802d4214a4030642c102022080c60171250300c40200030204180e8907003d401141c0400d81c1004070750708214221400300b003210781c1490000c0400c6501d040c503500044006000c00c0c0f400c060045810100d10980405610b032030411000707040902480c510680c0d02c81220903c6030081180c07130000317259070075560f400380401e40b81041026020b5a0590811411940800d80f10340c002900a00e009801040900b001040302860300002030510f441504181074442c000315042c400703202c030303940900048031701905c40c0703040c0f03a803120241691140101e50300c0c130005003c4a48407200d0641c420304 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 137572571 1250 137571321 137571323
    0x306090415090525050901060e100e1008010914010b1801030f0f020901020609280206071209051215070507080f0301082a0f0108060a0e0f0403201009 66
    0x4210301da810740310a418038807644c0c3c03060b02083c81500b00000d0199040f9040d009428112090160795042c0503000b4482c04002000301d000307a03a00d00200300858000c0c58840c3c480400100702072903c3e01c0f00c5c8001080410b081c8281321400c1e04020643c10712408e2010107505172103c410b401c5041c00b04c0e00e01c212000400c030000c03650505036503201c8103100305018000c0d61603400405001699803050100020b10b010320041051045803c4100503a87d07400c8040030094048010141140c0381c0c2c0114000607400b40300f814030081c521855403820f805040c0c2c004d5140000c503076040b9030750644052801066521b80340e4100141c1c8182000c00c000407042409034020b05941801240817900f0034150640d90030f050b0341300703802a0b034040d402035001801c4110007000c1020366502c40d00c44c010001c2c0c102c030b001c00e102c81c004075401030501c00e09000095250316450040300c024180c0c1411780703219040101490346010b0b0300b038409900240980c02a50040b44d948005c0b4882800c614000f00744069403c52003600030415903070 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 137573821 1250 137572571 137572613
    0x1090f0201050a03020c0604050705090105010c081603030204180b10051612030207081803011107120e040f060311031606050d0203070e040603060203101517040c0f060c060c0503060904 81
    0x720040c403211042041501c05d511030b27001402c1044c20f1400b040059001680050b04005c000c04491380054502029105d105250111700b8a0707078142864141c0c064040c0b504402030301010198189440000758000d030a42c010255030302941d40b0740340282210b052040002c5105248610140d4000181702c3d0340340c0d0b81259040c2c1c0740060a08055a8404015134030030229143302e180481c49a8504e07207400c0c407030500d8144454085c18039103659a6649100e80c41c00da03c1540070301500030141c000341d403502d80007040d445069860400c000344c0c492030000004161003402c00d000388110202856034180700700702d030801c2e21981c4e15a242081801e6007030a000e03520040002040010f002c1006c0300a0303c482c029400550720401003da00e0f442d00c134120f000c40030440e620003c90509c10107030504013281c002e013141031489207800317001031207a0f03542c20124504034850f803103560900b284503000a603e40c2c1c0500d2606945115900600c015108441c0445160102750b454650021041000c1000a80010606c40c00138003140 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 137575071 1250 137573821 137573827
    0xc1403181215130311010b0d060b0102010b0919061707030b1320031605130b010309080c030a08090a211e0806040b031207170d0207121101090f0201050a0302 69
    0x11001d40080b4000e50307629058158803861401099000620300c024005210700801c440740000c000200032002d5000c002d07068070f40e199502c0311030342d10030f401c01300358818003504100341400d1020304592820711080460009502c0e22070b0200740581036000030080781d40850000c0040074115240e404118101409540c1a0000d410b0440005941d404060703a105400c0010401c40b0b203020420305042252910303040780071400c880000d0080303550300d106402808000c4500019a49070344001a4020840721002410f42d0744040703000265100008000c0c045540180d5030000079440c1c4c94070352a9200c0000b1402498801c2d8070303046e160b200080170303900c602ea040b441c502034003803d003805d400d41c8070a1450702031900012840300c100304807810240200c8640c00340a07801000e01e5819586001020b0050708402040c00115910840c03411401e0030071b403120f070030760140119035941161502c010f903403038441180d5000c076014944ca031001c800c0c18481c0d100c070590440307050903880c1c285500446882e4092090401030640c04c0c = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 137576321 1250 137575071 137575093
    0x60e01090f0509091903020a1716030807020703080d02032a180103020f210105010c0528021201061a0313030e0a08070612050f010501021c0e100c14031812 68
    0x18402c0307000818047d401030003e50006050038400929420300141d0202410401c800d07120812010180540d40c252070055030f0380e200d0003070072402d01c0c0265102924101d00440c1c0b0340c02c03111032540154006c4d03046448824403481d0380040e101c1c0c01c05c1c0043c0b40d0013081c10300340f0103851141d01355a0821a140350500d001850b103610400c000405401950241e5102c82c00100760f007402040d6082242e01400003420941038042259a07515031354080f044081d502180f5906200c01c985180010480c1101c0d402820800c910b1800003045000309814480c0305078603092005280141410300342140e0180414550015031400107841c143c610201c0308102c20b800c645a41c034005441c01c41031000001421166030303146c00b03020081d210f00701510006840b21441350b1000004000c03ea80028800c180722201089600b40226108416202c404007900180d8108a03074904c40a0340d240e0090810441c0b074495402c01582202000c0c01d03d649000341030805180b00c61491801c0e5851400e5800c0d014101804c8003202c3c0d0003441 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 137577571 1250 137576321 137576353
    0x71d0d02060f0a031d0307031107030b041a0105040605100e0d0209012306121303030603050709020316020604030807050c102301080d02060a091a01060504060e01090f050909 76
    0x204039a11030b14001060702006aa8907000b40c14103029444801001c4078142c2d02c907152240301e03070380f801028080d85030580f5004500c00d2104400954008440e484985050308120019402034442c500808500c400041554682445101c040e0f03100545114580841018103031074018440401c294041d805440d2040140d441c401203030701822140500c01210100e40030b004c54103d86418040b4400c100510809940c0382c00156060f5222000340503602001880d0709090b030040001d40c01c00360a60083da01c2c0841c280700140c0045015203004008401c00c188041c00072038844034151001400201c0e0300c000704205920600c060040c0c0e00281d4140c40d540c03145184610100e4110710000c110101c0148407001c8000b80c96050315006100b06005050481601d00c4001d44405009103d00c54141d56400b82009200e40320041c2d4107090300c07810500c1c0c0b031540c4070300c4081c2958115104030400581500e2510300254841d041d40801c99862001000006080800300040000c0c010282e00c410711a400850300d000d01 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 137578821 1250 137577571 137577577
    0xc09011e09051003020c060c1b010207120807081005041a06040f060305060a080a06021602090f040605090111030103120c0c09060f2102040b27011805071d0d0206 71
    0x6001c1e120180392916000c01e216008800040d50b00915205000c00f0b11807240c041502988028141412552003840e044482c0901580082c00e01c03840d03101080070001c000d94a45001d8100941d512400d84d41e685a2108540c00c0d60f0464001c100070f815040200900d01b0035400803841c071455100324848048842c00401c1c410740165001d030324004001d60003000503d8040c0b10f1940c0089007a208941e00500345103020355034020034a07000b0103895000a52116035204c00702102c840c680d00030300608250900b58125810400151416507580e49080c01246a00030144101d940000c000c0c20f01c44d04503840c54a400480700f800c00e12a1050280c0b07600d041c1c00140780c0d41c00450141081000010703146040034034a050001c80c80e04643c505021040100072031a46495184645950440c1c002c42c8000388800400e81d103008500158800d0b007072898089055466809081d4140c50010500600c0f400f840012513080d0356081e0340200c04201d006100203021620306001520307200303004d45042502c50099010900d03030340c = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 137580071 1250 137578821 137578877
    0x10909110d0c09091a0406080a05030a0f0c02120c0906060315090a020403081c0b03010b0a090e011506030e100b0f10030b27060d0b06040902030a0803070e03160803030c0901 76
    0x100d11700100c441d41e4035142c0309000261036a5001408003450b1507895070b0380c1e48940d201303110034004100804c1007018800d88640f80401c0d805417514200320188800f02c0c0c0da815040c0141c600c01c00300100050594104003003920311a410404060b52607400c014240041e2042c06442118400d40030040440401c00701070003005407000c20300244400c11114000340044a03e1100c185119034104803040c0c0c0680d807031416400545040390350000e1144500030000740103017544e10340d400c86000c1140e00041c10540581c01110540300030000c4e60b450600312000c100c00c42e044491500d5028848514925450a040c5d50075090b003001800c0c0080c010203141c0000b1014a0500f21039208120300c06041c0b01c080510040302074100c28161801c1d810b1a007070f0340c1d580e071b11050020b04090256544680c604155a420801103440c90b400084a5075039042c00074004181e0046082d90720b000b841420240c00c1c03800c98203107481007101d00c441c0c043c0d800c0d515240c0c14500c55030b2000468a0401030303e8981081b201007804007480c900 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 137581321 1250 137580071 137580101
    0x3160b01080d030c0e0f130c0806040f090206071202100908040f1d0118020d06030609020306010512060f1506210901020a1403070201060e010b09010909110d0c0909 72
    0x2985030070a5249414120030030703101014240140c3d10040c40c0c005c9888621103104030b44c10300901e001d82c00402c8003810b5503051000c0c82400c0050030078495401404aa005820a940500010007852501c8040d50f241000094010a0410030b03c00400d41210601c2c00281c2288141c611040710780762031070152001094250f850f0080050200500b0001c141c0c0720b401003541c400c0380600b4034a070b0124160070240502c180d4a40d605d12400320081c88400d641110913480300144100076003905e84c02c140e0010181a00124000d100c0c504c004121450015005564900c2075401818a0b40e1071034100703804c440c0007410b5071900f00207a000c25440c540e00c51024000c0701149250305603800c549001c0b0304003c00000b40801d159a40b041000d0444507a004480010095000e4034043d41c948448004070300400075540850141d0000700b0002c42c0c05d030004e00040c407006074240e890301e110546444410040340d0080180914444042021442030b4038150082d0f01e000041d8104101c0507643c1d00d143c501503c9158580b0806 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 137582571 1250 137581321 137581343
    0x80a030504060f0e09130303020f04080123131502040f1205210f13080703080d05010e01060806041a100509091303090e0a0b03071401030518120702030316 68
    0x30455000f001012000c04500e41010b491541c000410362603503001d00100c92003071041e08030100745070080e01150b00d00051b810700c480c0c0c0c41c0d03514115940241a284040700700320300c441040040707400d54004c0b5940a480150503400101c911545c441e103004420040103181c4580030f001c000756008040c00350070010840c8819115800d001c61030681d04003030901440c02c0344d00c543c00441982e00601c4106403003030b041307002c400a9a6a80c00d0748030f00b000c50426501c8003800f4814050702004004c01803005d00f1008882881c140403d9807a4210300c03030100000d0243d200050003c50000350280340c40d800c0741c90b411602c00c2c8100c045221030000b10720304484039540d040c08500c1c001785825a070305000c0e904035440540d014000c5035065580d5070044c0b5141a5100d00c99142e50504003150115285501c500c100000080450380308540e503038a05241c40210009550100b85071000040340821011500440400c03010050a40c01100b0050f015031a000304405980610051003803c03160807030200820551401080a015 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 137583821 1250 137582571 137582579
    0x90203060415030b0105060708040302040c020a02120d0f030c0e03011d280305070201091d0a11090d03050c070e0901090606170a030e1201021206010207090608030304020d020a080a030504 82
    0x6a80402861142c0301d4024042000452682290325054131030850b000c030f54071000c80c101400140603541010354418504144600d0546e000030310503600910075107120768140c0e448440151205403c1810401080a0552082d009803103580800c118180030300346058001b0a000200e402c4402c20b9001245c040c0303042c9484450342c2c0f010070240003120301040d483c268218010b5081018010400c50040510401113031000c21680520280c40140280f030a0900da440c8030201c810010341420755035029028038001700c1e1031905910320308490040703c004e0010140c0700c003150350031602ca9000b4a40c0e40894050392002090950490004034010340c001000496186200d08042049517000d40c84034100f2400a0b03005c110403000440e203d82d060b034142c00c001540c480d010011403150744c200b480c0d06a0651001804035400d03103c2e80415401f03140281c4c22111010f40f0745c003070032007294118000e04030954018000600145090107001c0740c058409400814442d41d5400c4242c946a285034046002ca440440d00740 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 137585071 1250 137583821 137583829
    0x13021f11010b0a0b090d0f0b0a09020f010c0308040f0501060f060c0215090a090c140304050123060a030b0a0207020a080703120c0803070503090c0a1d09060106020c091504020409020306 81
    0x40d42d003a021034011800a1400d0318050981c80740045003401049a040c1c00010702401e020741c0118550080061a07940ca030403800d0100405081c0c504034810f0b0f41c0c002c1c200000e940b09800503084d1230740c56294800e60707480720344501440f0501c0a03c00c079590364881801144425821002000501c610740b141a4210308901c1000340d14286010f2004042400744036403907082c0d560644010480703882010008072010360700e600325000031880b00d0b80c1c070510000006110400030154400c003004070401c000d011681c10000e0b1481200002500c4260b44000700010600c081481804d92581014100030018a080d00c3c13580480c9141c207a40e80100c14980114008005010143c004940440054580f250000034140da815601d0300015180300200200400004c01c20b200c20014001d0388070008040300d88241d55040342d0720424111a481d002c1200c410400b040800c48002806c3c0d05032285038000d004160f0f0200140060403100800100b5070580820400700184c90f80d03c020809070041d1103015940c0d00c1d0043c01c1c0 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 137586321 1250 137585071 137585081
    0x90b060339040e0c03150d060b04020703050414030d022503050706030e101104060c030203120406020415050304020321041a040e150901060302090117130b0907030b13021f1101 77
    0x3405582400704101b0556101c22580422102401c03152080c4c04401400c1c10001081100c4229070407074400500b070310a0641100c0640100c590901c40c80d08428841400c2c1030315180d002e003889000d0303800004101c2d0603001c80c402000112110000040b4815660303100c0c6443d00e64254041310200365030710b5294000001c1480390440505401509010f082d00c80802c50f0014401d904c608000c205100c2461010103100f48115046801c80344003407805401d0a0428400079405481800114803d5403a10b0080d94040d1040e640315940041c0548a58046015480d03100e4002d4032403003040b00001c002c08900800540c58048103283d10201041d120790800d101441c504074058803401480c801c0b07494500140c0d0721803d100e410b58880740380150b159060440161114102201d603402e4903c50b110402c03000700041003902d100e090240410340c0c0719895003d2911307101d49042c0000ba040c1040c02c8000f41c807211312075000c1c0030000d10140c4170344005078031500d1582e0501d0700701c01800001b50000e061034420b030380b090140e = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 137587571 1250 137586321 137586331
    0x20c061602030f031909110f010224070903021018060c021f030b0a03051b04020405090a020304111e010f080702072c130c090b060339040e 61
    0x1942403000300d1500065642e00440d82c10900103200000022004124000158002c1d041a54144020030061802580850000304000d01810032810186110741c8005a003036200e5049982c500036580300200d9660400070010301003024084c3d0b800001006881e504d0003162460348954036001507403850b00c1e1520140116504c160100000500344101590352825802c031f0301040c100c204455502104000c0c2c001d0100707c0d0440d680001c550000006200700414440200912010310507640603204082000300d0055008880d000003403003001070b0005485034020354105001d0808094964041000624086041040f2100100c400c503408207995800a5400c0100465824162010301e00320700c0c0295188402d20a40c015a20b5040c0c0c45652034003050000c0180d4010451744c10346601c3c04000c05030380c490440c841201e81101140700020358444078030840741030b240d0050840c2d28603112f0400307031a0b4420388540c98940300000c2c1c1070004c040040105065000020100420341c0321443c050042c90750541c0201 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 137588821 1250 137587571 137587591
    0xc14010b0105031311210601090603050a0314070b041a0610050a18030b010b0c06010801060506030411060d050708070219020d02010c030210110414041401032310020c06 74
    0x105484682e0300301e01075035401540b601340c01c00c15078803c0c03d150040c0c88000b080c0700e030080d84ca01000300da0302044000250301105d000c0202d0b0f10741e9036150002c06c1103030554440a041c98101c82e031154002072140d80718103070301e1f00701840286c100012511502540d11003078030125101d0029500c029108030010a14540c0308000300e458103c2c01600380700c042e0151103000110400c0090300310305000d0b50015540280c004c0c64000501c1d905031360310381240841a6101504a18091107071400000f961481400313041c040d20030140802c0d085450319541e0000c1e00c064968036942c0850700b404400203040389446028455100d030380d10030b4500e04051001070b041c0760f902c107a1b18801d90300d01200400580c4034003001e40c41c0d1641c2883d044682a01c14103040742818003100d21180c60a01b0015003403007094866015100f41d45e900100406690501e00400c000c031036031507074411070442c003003001000884c020ba0464030080d010944400c8865048000352400c04403040450140140e01241c204032329001003020070362010800d2 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 137589928 1107 137588821 137588831
    0xa0510030602120109050c07051b0604080102160b2a09040b0603040501060501140a021e1002040b03010906050f0105040e0403050d0608030703020d020304050a210507060c1401 77
    0x2c0c4611192a0301b04004222007101c00002c82d04c0444e48076005003841105000c01d1052100320700b055a0707019009020000f007009007800240280556400a22807403621881c06c03003024800a0284000c46020300c11403070455420308217040c01529442800d54441040e680003030b020b0002c3d804480e130003040100a01c0700300300d0150405001e80390241ca580d42440f038000790710307480303406030082481c0181c1c04080000b40312a003101800600600031b00a0f070740854074100528041c1c7e409680003403503141002004000b1301d001c03845000c007e0581111020103107201c0200081c10303800b0303902030000309100c101e0114082600800490358100461081072203895a180c1f0243d480b901700344400d4025000380d01107040058404421517060300c2c4000d0452081341d00740342d403170401c0204080c10340340398503e513079000004207204100100050050b9602d140c0f0403561403504040d54100d40350421481c0e030500c = true := by decide +kernel

theorem cover : BRFrame.Cov 137410071 137589928 := by
  have h0 := BRFrame.cov_init 137410071
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137410071 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137410071 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137410071 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137410071 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137410071 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137410071 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137410071 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137410071 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137410071 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137410071 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137410071 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137410071 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137410071 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137410071 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137410071 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137410071 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137410071 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137410071 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137410071 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137410071 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137410071 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137410071 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137410071 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137410071 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137410071 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137410071 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137410071 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137410071 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137410071 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137410071 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137410071 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137410071 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137410071 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137410071 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137410071 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137410071 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137410071 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137410071 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137410071 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137410071 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137410071 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137410071 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137410071 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137410071 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137410071 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137410071 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137410071 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137410071 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137410071 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137410071 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137410071 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137410071 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137410071 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137410071 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137410071 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137410071 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137410071 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137410071 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137410071 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137410071 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137410071 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137410071 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137410071 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137410071 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137410071 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137410071 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137410071 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137410071 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137410071 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137410071 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137410071 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137410071 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137410071 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137410071 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137410071 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137410071 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137410071 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137410071 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137410071 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137410071 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137410071 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137410071 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137410071 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137410071 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137410071 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137410071 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137410071 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137410071 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137410071 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137410071 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137410071 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137410071 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137410071 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137410071 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137410071 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137410071 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137410071 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137410071 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137410071 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137410071 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137410071 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137410071 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137410071 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137410071 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137410071 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137410071 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137410071 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137410071 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137410071 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137410071 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137410071 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137410071 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137410071 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137410071 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137410071 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137410071 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137410071 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137410071 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137410071 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137410071 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137410071 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137410071 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137410071 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137410071 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137410071 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137410071 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137410071 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137410071 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137410071 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137410071 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137410071 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137410071 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137410071 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137410071 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137410071 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137410071 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137410071 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137410071 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137410071 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137410071 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137410071 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137410071 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137410071 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137410071 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 137410071 ≤ n) (h2 : n < 137589928) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
