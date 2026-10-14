-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0917
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T23:56:10.893148+00:00
-- url     : https://prove2.me/submissions/6020a24f-47cf-49c6-a59a-40ad2d5a169c

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 164748201 ≤ n < 164928057 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 164749451 1250 164748201 164748247
    0x1050d18080d180210030c020c0a0e01061b11010c0f0b070509150906040b07021302070f120215190906050112030e1009091e0905011a040c05090411 65
    0x16280c03200504501c0c0c50450f82044440595042e085000d0700060340d50000031071008141d4a80420712118619042e442c0000c4845400c1d40b0092514001c030f00c9011b03000c0c845042321581e40d00e894003182c241d020851007055480d00945100300e0071002c607038154082c10016000501c00c01000c42c0100581d21082036028056840b6000100300242511540c5840d1440b40490707891206d40078503102510000030298890307485545c1d102040411000259030b80e0a004130b0110500c030303078150341d139424500d00382d07041140541e800c8074000656150040401d1000a15030001c1c60010b8103c3c0190b01c038000984c461960f14182d12036291b484e02e4000c0d0004080d4080c250003011821030f00311840b0401d1078050700000003822a140070f00c080c440b2811920381d0044100040350035600300080c0804146040700050800603c401100038102a2104100141507102e0742c20409030480c40501800d2000c00c0000f03403141d078294540010300c00d12200380c41d454140d00c0300100091800d06a80303030020b914091040c445890507 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 164750701 1250 164749451 164749463
    0x181e1404050d2d09030813030510060b031503101514010302030f0f1e040f06050a0b0d061107060903090303140301180b0307080336030c01050d18 64
    0x5000c00c121007040384408441481c100003000b08503001c006086804071915600c00003c20b00701c1200d07a18011031540b0041c6400c183c1c4107075a1a42c2181810070001984012a49e61181d0320300300c030034500c00d8415070341074407080c076207441c41d5849600c4011005620710450541c107015140c0802d008070401d01c1640500d000c4038800c003a003107152002d82410740e05c440300032a06060041080141c1140000c4a02c0d030b1080001045030581d4480e00c0c5160440c0c90b0824580d2903006082c4180000c1c000c1040020340c015201d01c50900295407204144000d0350200040140c0002031100e249002401507000030b038003d0945c11169040401b19150042034680740035007900410f85444091082c15401441040c41203203041c0154519407400110719240500c408061107640d90b00d489100080d54280006401840241d0460b9203c01004c0705148802807404020f80300e83e01c0b4043c42c0d0102042d100740d05500300000901401d04a0100401520141e10203506000b21079500c588142003805e980d80b100618600402c = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 164751951 1250 164750701 164750741
    0xf220509010630141c0801080d0c0302060c0d0b15121003030e0f060c070603051501182606010b12070c02150a030605280e01181e 57
    0x1010041e802c0068242070f0030300c22040d102248a030760302a000d6102c115446a44071050894280580d810706030610041c0c0d09802c034000010f40c8040c1d10110b19070580b28030500381e400940e922101a14481c14001e002000760b0000400550621001b101400d440c200620f00854220400f20005d40d5010311040008680580414540c200700c2a280120b582700072402c403d1801d640c15524042d001c8442840344c00d20904030000a9041c43e25044145d51258220100b00c40146031118000360190008452248a0440314543c10000c1d42c816074066034040c02c05c4090b00c15450806044003503103010142c02007130b4020044d0560001d4041041010300a24070b495140b41c5868920203402a007043c040c03c140c042003108a0b0880151740e80700c00f280384000018201b50768400d280d0f44240c01a01444d4405a808110801d8262911000c0d200221401c40c0c0c010ae448001510752582008481c0b007809030420110031242c21258500030741d0f0015164407901c4541c403081ea031f0061101c00944400042d01145d2030100 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 164753201 1250 164751951 164751959
    0x8030304030e01091a070809030a03020607020c0307030b0a1a03030d020a14070809040e07080712171c200304150b12030715060806070810080c0f2205090106 69
    0x2000d006803881e02441d00401e00351405d46508543d9044402540c180000080c440042014480480c0c00640c00541a5180c031881c0303003406034440c2000c98560025011345001002c640c9070108421003500c1d40440c15848640311003c4820091840d4114280d0b0380303805050400099800304041c0c14025220500560364503100c0c0d40007050341d9000c03241180074981c1404113000040780f0170b05450f00c42006490004821403442e00c45850401c150b0303c5803285020f03c1201059400702c08140404d150700802114402607140d141c00301c180d205d0303002c0b034010340e400c68049091140c0e1b4680040500301c01003540802030700d0540700142d00c01d9205071011a144151240741c402d80c2035141c0180d1403440001c550042e01c0030701100d500c030780341d04c141180200260207076266510314407811b07407040d806010071204581e0741d03241c1440090159801a1303644001c4c0e02580d43c0015000100061400c0c4d1002c01500ca202d4101c49036080c01000070801d40840350340c1c0010f60b0340034503540301841020b105018410000c1585898 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 164754451 1250 164753201 164753207
    0x8120c0415030b0f0d030c02040c031424130f050a09020112050408030106030e070305060a0c02070905070516050309131a03030304080301030f020d0b0403080609070816050a03060f0803030403 84
    0x800d0480c07028103003401c1c404101955400a0502c240d01d007519012220042d91a0448210a01582c000e510a01d412a515403c1c1e034160301c0608580e12407a03001003642c8407110420a414405a80c0100c045c40d4075030030380ca081c01c2500c0403e04800440070085900c8400312408030035100f040b10411507440d6a03d051170305541e80808091703088640b500f02003016007095246d14503644014000e01c2c7c18142c40e160010002c980800041c001181c010050f60580d052800b668805007418941040c014070400a001c1002c04082c82600d0151002d07858961801d929003001c900445040501641c4a001c02e1003144102d0b1255110025248280800040c07107141c8a040c404c0000407040b4094000d074800d20400001407000310851b41543d40000004103e84920300c005041980c060f44002c04c030300c0d0311900b8801056000800140114001c03200100e81c0d40d00d8000458094104440b59031030302e000207400000362401003000389444240c03403a000c40e010342c8036048020704440c15840a2080e50000080000f850340c = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 164755701 1250 164754451 164754479
    0x203131203050708010e060f03070b03040b0c0f041404022101090f0204120807020f03030a030905010c0e010203070209060f0d140706050307020d08070201091403090405010b0a0c0f08120c04 83
    0x34007401c0c204042e0416100040c0329a030140119403603c00290085005a6580e6101c040b00350300c02002c0ba140c203910740525000350b070801e507021200314528a020540600000c03058030b0b5200c9112304a02c1c1031030315120340084801d04c24461550002d60800024482c000703c0d10100300d0103800b04050b5440303545001c1c280002c460140342c1146105105100c05c0c0600b07804403041e1070055400064190700ca499500000c1e0b0f040700c0505c9021742c984000104176918640641090f6002800f1f00f00800404404400c1507600b07510b030707a01090050300f00300b202000600d8086515030300a40003403d9001e0041c41807001c5201c0c6081c04030140c03088246400300480068040010300058a11032401c10300398184402c0207540c1320440c80507441400030303040c000350180c0c5c400d620603c0441e40104e01c21883d4181800d003607842e40d100e031013214080c1d803c100001c5040c1c800c030b10459072140400e40e220b026070b0b003444e19001d120000e003000459070014200260b4141c09090f4039900d002d54160340f00c40f9500d03482c250784120204 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 164756951 1250 164755701 164755733
    0x180a0f1e02072015030c0c010e0d3905100e010e07090603030f080c130303030b090f071e110a08030f07080903030106030b062a0c0406030206030601051c020313 70
    0x40103501e0200c3c03141d01d480c2c0300c5805806841109a0b101d48405078060312901402c4610300c1d0780e40c680a605a07030751800041c100d601005036101c80f594603010007820b2101d0091847d1074203c2e5a02d0121301c0000004c91a030307452007540240d01341d455051820350420305440c0c000d00e91601e20b0391111400d18000c0400d004450003000c51000412907a4a1745d5030180004074101502000d1200810000750051030020440d1403090490a42e4840036860b0700c1c5c00380c020005800e200b030240d0740f074900140780e01a6034517070f086c047d03286500c0301c22641a049507181c000c1042d280185040214030b1080050b1010200188182d40d071265040d19100d203803d004200f510303e0014058810810300c44203000380c2003030200440703041d10000d14001c580483c0d1600400d0181c0301e00019141411004c0d803080003142420000d00d441400e0b41402e80b898002d400e420003041c2d44003800b01942c05402000401c0046d80510021710480c007600748215201c10005000c5012a00100e6145084101036560801040b1101c0351070305500c = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 164758201 1250 164756951 164756993
    0x11b140301080a0b130506040b0712050601090317040308040b0d181e0c0512010507090602030f120a06230907170f0402032e0506180a0f1e0207 63
    0x1980742c070016943c0d401c071404015105100d258080741080038a0712400d607406802200b00c801c0342c01c02e481c0c10316050790220340200c001944407200300386c40e01182c0101c0e40920303070594407610424215201c46007407612200346000050010040040010042c01c003401c000d08107801226140c101240c80482501c039480440000c0c003c0c54000c400c0000c2c0e446022000d070240c0c030202405008154a40020000340a4101c150710410f0031204660418054008a101d0030306030b43e800b00c0721907031031000381c3e601c4c013074203951444000c41442088203940510380104e0380302e5444500881d407903554446641840d9903528610034400d56105000c20350382007888416411081d1444e1120180b540020b407501c0c02d550180c0208181d121010204003035581c104999014028044500366030b07111000005000248010340c58400a800c0200142840c070302401014240300496115503901d03903803010000020600510f10f41c450554415141c56a0f2103c0c0c104000741c000714903c010394442d401e0030140c185c150008410022 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 164759451 1250 164758201 164758207
    0x71701090206040e090304120f050d08011206090503310e15040504030c2004201b0a0f140105060406030c1406071a0403090b040803030105090403020f011b14 69
    0x603100d072002c407411141c0c4460071a80c5511491802401c40c1f141d540041120b246c4000c4040501c40440c985450b101d00c90070444498101c3d40c04251000b950910410103100c4c8524110b03000304a06400c60f80000d8440c8060300e161142d0018111b1801a010903010000890403080c440c0181f01600301f44042c20a010458505103031070900d40f1400380d07180c0c440c0c40c000d82e1580041810507000c1c0400100791035120140c07081d40707207200070807503160050000d95610850408003e201111200400251109195040d42d454445100303810260703803c010810040e1071081100c214085003d1002c2000d07020b00c1114544010300c1c0c3c09420909441020b0511031181d0306e0039204000040d4061a60012105200740040c0d84004020000e0381d18000d10304060310141d0b000c0d8003c100b0020794030f030f41c0b44030700d2280c0c44001d0580d40b60070300188240581c0c024034105030300c10401070101d460901802a4880d200313104a4555550000b0701d903003500d407008501a00b582044101051307880d041002a04c0000d0100d0364541 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 164760701 1250 164759451 164759453
    0x2070503060117070504090503120106030b030706140703030b36070203091f03020f04080a0b0108030708040e040213020c0f0f0d050708030402011b05070303030f020307020c01080901150807170109 86
    0x41c40c2e1350745124252043c1e41e81c055101c108442401580d041c40b0004000141a60351010060080c0c001212030328031038051450046a024011f440c1c103001030305900c2006e800c000c1d0b984d400344c0003000c0d203c078015801188100030049a031440a948003074180e0464626039003020001c60387c8098400039201d00b00355002400b0400d5551901d5464134081070380800105503045001d40150004e01c2440e00b6410080c40c00640410300800c0021185c2c41c181c410502e98003541e903500001038032400b0b07c0398010701c0307441d00304001c0280c40b55000c1d20a801ca800100482d5030200000503900882c1c0c4440000c1d030070b580042c00c03c0707004500c091040e21080710401c0090540e0151600b4003d200d03205a01006007110030100105c1c0a5901c24019a900106400488180120f03241071565035402244070407000241802084900c0302d2490003524040d0001f9002004000e54450040d9144480102141d000d9075a03042034401c05960440d0000040210a0140c000c45080c05004441c002c1080180f215a81c18407141c04 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 164761951 1250 164760701 164760703
    0x1090603060608160e0418140601050d081305040e010f0605030d050f0f0403080f120109020708030403031d03030a1a0d0822030203071404050603072301020a0203070602070503060117 80
    0x56000031314405040d0010000d030820350711003161807a0b60303402c0791400300700c0e40048a40b024121952401049507031101c480341046240e031090700340100c0b900300c4803000031403000a6020000d8501d980014415440c07054444000c03401f201c2c0041f04c5040c82d40e4490ec40d03192201024428607002e0031007a40a04912a40d403c0064046c2c4640741c511210101c00107100710001e9078080503a805140d004107180c0d6100520b118508146d003000400b138181c1c01414000040e848003a00c09c0b240e05603131110307980e419691140c90990083ca200d54035441600f200c0603101c0b20b2000240300542c818082d50300f00180c0b603d42c1c030300000c20300f0200c112031501600c081e101c00c0020480000c182c0d502d505940b4483c000843e10801c0004403400581d1000790140704583e00411406200d5001003e141d000780c0d41013000fa5076000c10143d80f48510300c20180788002e1102c0b0400421040b1540340b01c0b0a006004891a010003a0302191a02c1115445540180c120507000c1c01286428000c0318014184038030a5031008102042c21 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 164763201 1250 164761951 164761967
    0x1006140315060f0a050d03030507021204050a0302060f370e060405041e020a030f0b06090109030305091203120105040513112103180307060207030f0f11030604030509010906030606 79
    0x514400e070043d10f43c61840e035582202c4400038200240c030070101e99610b0328003c0d0181409032006005800b50200b0f4040c011090802e48003200c0006200100a610316002d000041c3c3c404580c040c40c0d52410000c07110f20340c80e0450344400549880c5444804140304c03d06d80c04105801a504604000c01f101070b03100345076500801e507003d40b0011200000c007a0826010440c0941160100500310b50001c150403640c030b60540e21540d071030307000c200080c0000c22845080114501ca074103170f451302150021030b00b880400d01ca50301800d04001e025000c561107500c1c4c40c10440c650f400100600c4845281480103001d1800c0c01d0003181c0d044013010b080350028102c25650030811007079074803c650003905506008920300c240c2c1016150f042810400303482e590010210f801c1030307000078941c1140c06031080e03000000d021440010b0b00c83c1100c2d0820130141702c605460b07880300c1c0d201e072851205562040e919015007803103981c2404040e01652081d2100755075140d408001400314111644240245480d010040203000d402c0a12 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 164764451 1250 164763201 164763211
    0x501080102120411060c060a09030305150102030706050c1309020304050c0109080a0609061d0115150e01051810020303010e16080708060310060b07060e03191b051006140315 76
    0x1400c0510b01c05001c0b917600d002d2142107000b181f1840051107404c101580c0a181040e000b0364003805155285662540c0c818060400c2030300607802040b05070081080741d802190005048480145801510100d044203d81250014000164000103020801400304408003140400303080490035285050461526002803c1001c3d200513100c1280e078080080300d130b01c03440740c141413482400390a0582803c540d0080c000025400302e2000e02c0840070806000714062003280c020599640d146800303c48004440780d4011310b405014401c041c29440300207030381d2451440b80448443d80255100d40c5050003130041c034900503101c021500030b580c0d4507459090380042c2044d1311010301d003000c9416403644000700f03103000070f01001100410f152a070b010a182500c10018907000e03000d82018480700c12a020301300c0c0c4038401d49152849091041d4003414a0030701429030014400c0c074041c1081c01c0350000c0e403166400c14072036641910120380d8542c4103002c042d01d440c1203c2c05085c0300794010b04200c0f10f003084bd136402e181c002d80 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 164765701 1250 164764451 164764463
    0x30a03150602031c11030438060d0809151207030603080703030504080c010908030114060c2d01050c0a1116030b100b07060504020a050d110d0c080a0c03020405010801021204 76
    0x104160000545c102c40000507000490b2aaa440c0c43e040a58400e0100e03e04a10b5210203581d41c000e10f0300048180302803014141c0c60f003c0341d586924040040c100800d41049441203810300602c0708030b59480c42c1c056150886440000e540700320301001c032017074644010190014141340010500100704042c003503840310750b03050034006403d48a41c20701241c2d9014000d0403806542c00d021002c000c00c9041401b42d412680c04100e001c118082c284104030003401070403440c00030b41e840800385002400b8401c2201d84008407243c1403005e40b0003c140002c0c02d48400b15510280c0c1a40028401c66440d07005c3c598403400c0160300302070204409034256111810013680b0015007450b403074001140150104030050b1006003100b681070703940c95030b41e460860050281101d090744a24558040000d0038200700c4c003640901070303014020f040c1d24a03122080148120980005440c0c00304211000300e89601d0400c5901511805820031504d40340c9184108001e4420503040f915103139006100036a03aa107134041420740c0081e8455 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 164766951 1250 164765701 164765737
    0xe07030b0a03060c0e040c0509090f1b070303150501031b0e030f012c0a02060403200d08220f09020d0207050105040b0a05010f0b070b0403020c060309030a0315060203 73
    0xc40000c014404540003e0441c51628001381005500321040d00303184101078400b8490080344c03032010307101070040303120301900200040002961480010b000d15446260502040c40c08400302c00148800e4200210441c0030a50300c40f01038001e41c69841d401001080c003403805200c3c0400042600c0c1a000300c90383d4003c24001e41c148038481d59507090225503c2e06194a0007002500c0080ba043d840c6d0002c281c40303402d00c40400103540f01500102152070880c854014085130700d0a0f00c0c1d560b03001355940005148500f00301500942505035959401010710780c50059000f91703102d080400080600707801544060050000c018820484415645015021114810300050305d9a5000c95002d0180c0b20322803000300345520b000700b044100840e148100e4054100f03005c04119503030321840c2e1100e0f41382d2a4040c80d403042c1c800303000721000502e41c0c0c002164001c0c424416900000003003408a01d40b07810556149000b0740000c070716928507503850303c511303e500d40da0f500c001241e02d85401406516442400d0038005412104 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 164768201 1250 164766951 164766971
    0x4030308010803281e0f0905031c05031b03010e0403080a05070e0112021c060f06030c0c02090c0d0903051b070302210f07080c18040309090203090c150309070b040e0703 74
    0x1900e01e905c148504500b50a44034143d401c0001c166003110001d010120b0903641000c0741d58100090f02c00e1810000c81101e203001001e8100680ea1904001e01304801a0a0f2a090441380c000b41c5c40654002c002c0e0300c400c02d1007402e007031802410014001709040c0240f0700d400c040100143c0d012035030003020042820061645000d042c00040640300d419200d41c0803203e0600180f94107200c540c400d10031203c4001c40003420a80b0f0311021070a90b01a411a9000a0410340d107a0000d450503241300f540050b180f0300e1080c034040c0042c1345803041d56400780041e808210080340791405100e4511280b40c0101c0110058400385080d84d000560002d110803528014019806980c085000201318402440c1011411a24015520342c01e183d078907844074003441d00616121a160882800c070f008124012540360315001451810b20b540040203400041050310240301d0314070b43c41358546a4144481e00340c058100200e03030301d2400c09900c602e007801035484040c4084c0100800c02091030a407001503001002441d01180c0c941e02d0b = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 164769451 1250 164768201 164768207
    0xa050304061b2f060c0a0209070203130b0a1101050a05040303060914010b0705010b1806040606030204060f0e0105130e040b01050105030c0715110408030d0b010306050f01080a021b030403030801080328 88
    0x4140c8585130840310004286000d0f030000100d9180070f0380b00b03c0c0c42911030b6482860490300d0b80601d803040c6414980d494001e100812030744010309000205460301007400106040d2407401d592060711880d030a19544c505000034140d06020342005010803400c18400030345441c6000e40d400405100740500003a01260003000c0080a412400151500801c0d0400003050103103071481d072040070350382c0d50300c034518201e0300142035070090080d01c0417118540c40b080340803000184282c95240341c40030210b040241c1041807640e54400e60380d0100281c15002c050709000d2805142c404403002041e00458140241030081101240ca5041216003040c1c3c0581c03400c1c0300d5000c03400c1050203003160007034480400d0404035000c1280b26001000d080106204034060058400c00401903040b100e00d4001c0c00d41001e400e401514103540598409500a1441c0c0341c01494800a402c40c035499a41035450b0602c944c00002e0108149541300c5a518007500a1602031454040869050441005401800c01d00d24815082c0c00c610640 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 164770701 1250 164769451 164769533
    0x5041107110d1a070e090f0411181611060615160c0605030f0709060e01030e191b08010c17040201050c0f071a040b04091104080a050304061b 62
    0xc0c0c00000d580403c1520344040414031011541400010420700c42080f5601c0c248807803074041d003260781c484007041d01c96407580441440b9501029810100180028400340c0c80c0343ca0442c414010f402c6c015422500500d0300400f00660221524040c0e8010400e2200a582d00c0e00521040500141615621003003400742d841600b06900c2d01600742c00d01414001400d503008001948155041c6084100725545c40009448105007401280e0000303101032400002c65009903c071031450710f941c404030b4070900064140ea4400c2349c08034500300c5092019000004084040e402e80310054030092000340024603155000a1508981c02010f00141845a0200302507902900c11242e80000c03440603501c040c118010340e0350751040e041c40340c040302105080316190072100d04010784040d10300e01c0c180d940c6054900315284002d00101120040784140030071000843c1d2200308408103903280f00340051511542b43c08400b030082108041407030740300c01e0422001e40c0000d64800e1202c2c4200c0c0b601c1303101d09004d00013196002d0608 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 164771951 1250 164770701 164770703
    0x3090302100c0503070306090e06040b1f030c0608100e07050a0302090607030809060601030207020d060c02070e040c03060b0a031101081f0b0c06011202030715020a080d02090a05041107110d 83
    0xe07103420b65500d44a5441002144640d40d540c4061241c0c56480044c007080311010320840040ea0400004034000402c4808021b0304003c650900d0080b0001e510003103100110117034011a501c6040030340421800303030010300135548061103154110b0407500c0c240491090041c01403039403041010015581c00b1060081c0d054640c1c150003d071226481d181c40c0e00d4064000082034070441d442d4405c2e070000655542c468003c403400c20340d0240c1001b4942c003040c0c1d00e0300050403201c03074450158015103002184803074070803210600c038074012a01013041ea480c600b00007044858280e40c00d40241c62111062010501851404041c80740a2800392030913918034110ba041a2480882c22111030340b17080000542068240241040d000c0150942d03c0a90740c40c0740550b40c0644001000350550804c0380100941048503a00011504890045c0d90551145541e8868aa4014441502802c0c0e01085c03a5070507042030681203002d04426103040218120655060000c0d000c0d00100030030008447c18030810356254945802111 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 164773201 1250 164771951 164771983
    0x10c111801090b040f060807051306030614040605070c021503070e060406020102180303070c050d110306070f110a05031c020d020f092b0305071a010806150a0e010603090302 76
    0xe50b1a000101c0182200ca00014411403c0092107880700b1103902c500703022101101d009145407880d100510015900b888403003040c03996142000404a4400d014448114017056950001845c1c10b16159080301d002401c0c800400100180d0f20005803502c925010010200749071241c1c50360340300d0000b102c211b1005510190001008240050041d40540280c00014110002140200c81410a060796030041d00c201420a094502c01004141001c903401001a80a100b0303030b481e200761040c0132a150900c15110980042c0252091050380c5621a041403030615010740075100c074230ba064441650b01d015001c1045403010088802d503907402901c0c1d0480b030100d0400c0405640f107061b02c031000303185604105281409181203c600c0601000035105000b040d00900040c0c90801d100c80c0c030110b41e0340e080650304550750260580c4d8440304103004090540201780003401440246000050044c4440b18081c42902904c0200c4d0244011205400c050b410b49555280003d00900503041c120300e800c1e040954842d403 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 164774451 1250 164773201 164773249
    0xe010608030c01110f0d090206040308070c1a070b04080a0c020d0b1e07020d1d130b040b030c06091216030606050108011205031812031303050615010c11 67
    0x810300070000d0040701e0316802c020440c00c800f6042c0c0d055a881100700e1440d100c60200a10b01e6049143c0d403000b4085070005d029a8145610723540c48003516440b90500745c0d1402c1c04001c0801100901d09076000c095507419102d00d04141c415a0f0b102030180010700020b000503000700701001c00a20038001c80d403185070001c0c1240780e008440d0804d180d15082c00d845c0d0101c0320b0140a224400c00312050000c2d40141d07070716801800c0721a422901101c2e042e0140e6188403510441c000940c010b035032014420011a400c80c04d000414075199020041214202080381740241c11400345082103554010079030700e40100c144d8244182040c2c0400f41807d0416a031548600c4145040010091000943c00b6400303072682030300c3d500201d03601e0301e645020181c0b05031300051255008106002c80001f040007120070140010740100e000c0d000710790500c0e003140c004c034000c4015010314880800500c00200001a0000341c4403000d100c401c0110800200755040f0210090090a13500c03140d9030082d1188450482046c90812917000 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 164775701 1250 164774451 164774459
    0xb310b07060c08040b1303030204050907020c0a0504110d0b1f020a0302060c0301120818120a0605180a021012050a091208010b0417010f02070c03030912020f090405010e0106 76
    0x1009801180050341d615181caa4582a8a07000e900303007900680d048a000b0203540e517118400c4094640e0b5500440800d074091100140640b200190540115030a4010388003500d05401030000b0100d29501c590310450516010300c50400c048411203004240c0c2c5880460811005030100d4481112001090400f1040004008001c2d81c0400c400c0c030403910a07401e80f01036807030351080c3d01400e000a02031200108a110b02000019588100030a100020001000441c2d090301001401c400314107440b400d400d800001c002400c00c1514450650700640c0c0003007030035a0f040c50010496542c2e8000d03100070f02078030148040203003041c06015034190b0703145401d07401d11643c5010440007014004401003295045007440001c0b001d107000341001030680e20500d100c281043e01d080c03441c10390300d100f10070206107655955280c807244410360300040081a00618810581601d9898004d100c50b81903800150942071030807407600140d544a1440211841c06c44203055079031101c0c103005004001c03204c0b600308590b00e0000009 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 164776951 1250 164775701 164775719
    0xc06010603020c1603020603060130060602160308070b060d0609260306011e0c020402030c040501140c030a0c03030204081c02010b0f150310030b0108070f09060b31 72
    0x4030700c054510084c0c0341800c10444100400035454080290b0091084c400030b401e0354800d04900c06403128900300006245026a0000010640d903200b030240d05455050a00925404200744500794480f50400b400f00352440d02c54000d00e002c5c2e02d200800d94450312001c90015038070754851b40801500120100090301e02442c03e0f614648816034008200141d544140c4a040680010f9070721541e010784960341d560300b52600c18a01002c6080503042440181c0f4119005a155440a544101d16800c00c00c0e41e00e60501c000900000c8142000c210500c034100440c02001801100b03941001009003088681100245001e03070280c081c54221002d03911a941050155100301d4520300300301c118540082003ea80e0703000c14040801008031655401494806858035080000801160300180c50024001310580b6945c80c035460003820380c028601980440414091190868109002818000010080e031860044040b0060141d4007660145412151a201d950310340c0d40260480c0005207944002c0386901c078a500 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 164778201 1250 164776951 164776957
    0x6020309010314041104090302030c030d1d03030c070602090f040218010e12072705070207030302150f060d0f0c0b0d0e0c090f0a020705011a031c050301060f02030c0601060302 77
    0xc540020305140e540c5041031030641c00a4052074008102d1000c82c2d80140510001c0c00342c280040301103200402018240c10703c180b010b401e83c19000c580c0440e83c3c0400d070824211444814030800000d070420030510002892074021100323160360100700076803a80b400c40c0000d00c0d216004105203400500000e112404a844c0042410f0004026207540a00480650034090b010b0300c41c1d41030003425030044100b406801e00e0340c4244003000c402c502d04040f8205280311400180c0340b0030b44d171860141c1d0084a00b40101074041c00b0400d14001000e03000704017881e020035501031548003c0c0445001c0d28084401806100265505141d00382e001a01d00a030369941c0c09001c54507030701c0401104042460608859400c00f004603680140315001446440c0075124800c00310581040a0b04991409900300119000034800b8001d403081e00c0508030954a5101d841c100b80350400d0748907540e04602005030b81005000c1a00881900d040d80c9292805852100020800380d1442c0308407501d5403003d01c110000060700c55419002 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 164779451 1250 164778201 164778217
    0xa09020d1a0f010b1e07020406270203070f030b010c0b0f01080c03030403112107080a0212010b01020d083402010b1801050603040c1d090705030f12070606080304060203 74
    0x300d80b540c684509241c02d41080c040c203650080c0402c282c42a400301161410b004040c42100b080c0f8100d5241d00040440308968000542240b8070700b8140010207401c4120304540304010010740c41d61814050007020a021100400c040c15070721b00c2c90030000c1c0d2140d030700301c4c0060f607212048a1541c1040481070b1b190b1007092007198a284543c0c01d182d507131030a0200c1034030304a03607121001064200c001e01c00c1015004101740c6030207440c001c0c5500c0840c040350801c5041c0041080c03001400003460ba40c01071050004c403000e048103031070381458035400ad1640c0c0050042000e03445442c0c5a0030a03229a1031883c1600b0648044000705000c1200450482024040e8449261351b160000c001440304541403105441d1100740c11003001c400340b00104013504112009560146c07162401c03003465a00c0b811041c4420041402d51a0449000d20401418010403c01000940b4084009205013015429000e03561303140740840703030701890001c2040300070046503810640251203120103507500c850329801d0095403030b000312070b07 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 164780701 1250 164779451 164779493
    0x1e0907051207050310052e03020406060809030a0804030e190e070221070f150b130e07090b12010e06090d03050f0c07050c04020f1b06010e0403080a09020d 68
    0x80c40c803500c0301c0029141049980c05405841c408852012400040000030141440c11894106480d8010105040320501e0f4032041c40000c1001d0a60046c08220307041c0e078000300705201c048400d0044c0e01318000250b03148906d0030b03e400e0001e40c0d5103103400c40d00c02d0000748405400c072813514108810552400040010b880c2051030012041c1d907031070403c0b81c2d51400c440407403144108081c941c4583e00074800c001c1020720702441010400300c0c170a41e2250a030040888080070300303507a0340c900d410052412030a20301c4108501e58040c00800da40343d0f01641c07110020f1081c1030b00c5036601d07800460b054861104040b1007450b244002c1044400b4a0100d94441101301d80310b4065001d00503910940d02d000344076240c01008000e50b2500b07681e6803640403085aa2140c0406d5600b0300c100001214296980d00080002c0070307001c00c0440d110b01c0322021500d28911061314a490503001600140400642d050340b50340d02035010701d0b01d1025a1150550000100340c4d6450180d0404059407540083c13080301e2980103009211030b9 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 164781951 1250 164780701 164780719
    0x41a04020924121605120408040b0d050106031b020601060e0411070c0810020304030903080a110d02010b012c01050f0c0f030a2d180e0901150501050703080a02031e090705 75
    0xc5004c0389010380110010001c1001480404412001000d41590080c40343c3d4100303140c652100c00203160f0fa00600b10f03003600180c07201c0c01030180c99410302030340c03000180102040240c1802e40b00041d40701d2405004072002c108040f1401c0d03035030b41c1c0c032500282c0a0503644041c0a03603a40da00c1c2050300b06543d1034003c1c07080e28440e59007202d402e0901803080700d200707030781543c1d403840c005003542d445c440c0c560f219901c2c620400845540b140c00011080c0580c4020741200d4000080d1401600000f5004201c542c40c90ba0307440c0c043e140480d40304c10741c0b0400340c0b00441c800d18001e5547d03c110f0a01000c0d5002303c54a40180f0300c12014040300640780040100110550b5890b03400b1002006100b1641011181400980a0001381c4070307150080d01400b04020440070302e81c6c11507001d03074507081c1306000c001c030803078804400ea9120a40360f07489511081d05800517040070b20303003685020400c0d100a0b000240103400b90000550000010f499410000d203000e403e1400301c0e100310701504107406201e0f03076814580600c5115503c1c43e = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 164783201 1250 164781951 164781961
    0x210180b13050d0f03021c0911030d0203090402090316090504110f060d0c030609090b06180108120c011503030e13020a21061e06020c041a0402092412 66
    0x840c0c0494003680507000f00100200100f00b11104100c02e0407200034180c0901060f50f041c060007030708690204140c50000317820120fa080c078011405151011f14000d0b0000c9281140311980030041b520007090989025a50b0010200480e192547c1144240342e102650701000c5034070303080c5030000c5003da402102e44c04040000a0200042248420341d800c2e4004004c0041c0040e00354140c103e43d511003624100090b50907555540001903401d1103d007103c0303116140c2c2c10002c6034a0310960f0542000400260811150b05140d405a65851400b00c040e8a600d8081001e000ba5902500010744030780403084000e2200d0368030710340906518080b4100c24400d460366072805c210311200e4403d44440000a6907a0201c07903070b4407040035120b414000d1118101c25119070380030910402e54802c80351810805440541c0d80c502d4000b009050035200030311248505e007000081104080e8410440c18101021280107944298020001d910103c4000c0c12840c801c01248001c070220417800d011740148180c036103182285035a0 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 164784451 1250 164783201 164783221
    0x3020706020c06090a060e0d050105012d03020306070809071a03010801180816050102040504020c06091504031e170c090114070b0103121202070602130b280210180b 72
    0x13403805030769046481c409082001521034444200c020002030281d46e5500405c0e12440d0954109070001486500a01801703001e03070080a20b018400f143c1c40b48900541811070340081e468107409002d5500b00400c0c08040783c0d54140c10710092008040551880d20711116001c0c40012a4109220b031280c15441c01012030b401e180003648a43d4038991201d00a4900903403114400a2003a0352502518290341c04c2c4004211078a844c8020701d9001540d50080c640c40c90300a858a1900200da040c51459030150741c00e100000f60040c14816441000030800d0480628200d0200d840811000c1100001c421013414840c810345032600902c19450203988407180b2120440031800c00788103030000200342c1ca030140010004180c042c96031203410a01c41c5040590000400203e1069801ca5082641c100d0b50004440c0500401ca00165000300107002400c1e05003103020001e808960951499462a00030f41951288441c1c030a1182484204110750708100000c00320903580f202c0131006404076a00c8444070042200f07a40 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 164785701 1250 164784451 164784457
    0x190801060e0a050712020c0c060d050a0e0d020703081818010f0b0a080a09110604090e0105160806010815100203070c0b0f0412020307090906020a021b01050d0b0d0b0403020706020c06 80
    0x250a44903c0080080c5c0c0e84c1480083d4440c0c441c511190045d243c0c0d80c515555400001c02c1302d1401518081030a040c29900c2104851601c0c1410100303030b02281d04c4207056500032600104590f04024029212801c0180e0711010310a05a02e8940c490462100c0d0007074180d51000d9a416141c901d0507103a0b40f1a1101400300e654131510007124042442d103400240d0070495501f01c0c154103403207190803c600800031008039015400075048030000c41d032556a54004287c0902c1287c0d4040c0e07452284640740141110040d0420a014025904200b204800100005004040b050f400c00001c0c041c11026031226200949a8002500864a80310741210001d0203812a42c1030f03448800001c0e00035850309103081c0c45044100500c400498040c0101240002c008429101e813510440c040d00e40580d4411320150024101108000e03405a480e0081070300d069641da0080c2908c0300507004080005000484000080944810140040c008112a420801016800304400302112405c0d000c94003101e0a4104212141c0 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 164786951 1250 164785701 164785711
    0x10e010905120a060203010f03140303010b16050a02060f0904050a0903021e0f0d050403140a0b1305010b04020712080c03061f11072403050f07030506190801060e0a05 73
    0x24201500038080c1d840c02c030b0000d11002e0000001c071002c1c1421942d0710026600260b000764859a403584081041c800741c108014007a0b003480e009549190704010301e6880340d004015402664442c61000c400c1008410002d031040030341c00901154032603c83c601410050f6101407603042c011414000802c140c110301d400342800165054024001040c51004545420000d101c1000c0b0240714a81c400d2151490a000c0c001003002d60780d85951f600c90440c28500340c11000c5070507a41c49076010310403510114901c4c20140b90481c06410211010820a090140c0034103c072220490b4410720001300e04e400c200c00400340d000d01c1d94403500c6000b810303a0340c2c0c0b120340c045001c122805c0390060200c16038111000040300d42c4159460182c10003182c1c896031001c07154a00310343d6030020340407502010440c5200980740c5284103401402441c052007503240c0f0012981c8400070180c581030a00d512400130401560310540e20201c0c1d400f020904503000c640d50202d05018196038400d49a1404094011440c840301a0059a11079 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 164788201 1250 164786951 164786957
    0xa0902180d08070f1a0403050301030314120106050c011e14060a03030e04020a0314180105160e0d0302071205030301090507030c1d011101061d0703020406020a060f060504090b15010e01 81
    0x460f441e11030312814031100004440e408185481122042860f48074140154000d076a5180c0702d605500d405402c03040d1541d289855441c02380400c0f00c903418245242410740d0382920306180c0702c00700d11910b00d0240c05007503068900c601403004101c0004602e9401424040c66001c02c0700700715210b68003070114100c114000900000c1a10003202c1e45401c0680041804c0c20300e0385400180d40340310a41150841201352044140c42010a5944604070340901507160080710320003041041c8181e2400c042d0110502e01c421030b005504200c0c200e020b0600a0100310000e22071804940d0020a203854502d03200c3d802400b0300f289213450500814030151003442003070043c0c22603032103c3e081412107000e0000d0103100325540c00d041080310f140800c60310100780a0705000f480000103441101280c40c80501c0c100c04020010010584144810001158002130503551190484d400040104141e6201800360059401030b50704035041268100800030807203909407084500c0b0680c5010750071741000450f001d0808251203400 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 164789451 1250 164788201 164788207
    0xc100f11030705031003080a080403030c0f02071205070e040f030306090c0504171c030c08130209040b090a0c030c0305160e06040b040e01090f050d03020304051b010e0a0902180d08 79
    0x40d40e4001e000441d084445c1c00d041e201503540c1c9a0b58040313181d00c66000c8000065000d001d00c8100354143c007901e20000c4407400c1061802c2c00740c040095450340a0700c244d840c10f00703254400344244107040c803448014000c1c10ba50b0300c426103414200540e804241d42411800680340000028a402c02403050402c0916107945187c600b5241c000d05000c00041400101050700400008104a0702980340e40003c400380c0d51800301d503429024401604140004009020f803a944107074610040c4e80d20480300d41d200b40c0c0840f80341c02c0c0303458006007a0301e03086800c44000d1850880280c04402d01c02495000c0044a00c41d200301c4504001c0e0055049070203405100d18944058240042096441c5c1900101d0020388050000110790b03120415a500b0345107080b100f074450004182a20f814441c0601880d00c18a413281015450760900ba512a070707480c1d12042c40800456482405a10f00d60701c191000d90441e48007c1001e4107154647d95104000d40c40068000701085000c0000d51260170058030044e4443e404c0035550341 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 164790701 1250 164789451 164789461
    0x2070806091903030b130e0106050402090306130c170313080a113d030606110a061a060324010224040305090913050118050604020112020f0c100f1103 66
    0xb001940c410000c805068440703560a0b9103071034032510070358014036880010460010410046007101c4282c0c02c1217019900410184000752000039a96030040155801c0d10070404090909150b07030b4000d50080c4078095030302d0444201000d000001342040854011414100d1603840340080d6a40344101c00013020302200805140492629072041c0c4100340b4402444580402140c402042d040c41c02ca200101e01015600c041c8502da51500c2940c01900031360424000132010301505980c0d6034803c0704001c00803038a41d80c400060700040c0108410411000d00b1407516405c2c0307000500074001801b40e4000d6400d28200c080a440d62001400301c04a03c0300310354881140f400364400c03505804c4020006c2d010701500708040801a141c09007020300c04c421185101400000c103107400c509444404030303c54103c403500213507140481c1c400308100c3c0c0c210307030f09003000c00d107506441d840c01d0040c0c058000d40c0c0000e09d0f07002c2614080e03840d0200c0c56a81d4086059000c100c4081d4500c568811900d00501c48040000c0500000d8 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 164791951 1250 164790701 164790733
    0x4030305040309050406180b0a12141c0c03080c270301020705191101090308040b03060f030318090a0911150c0601030309170601052b0c0b0a0207080609 67
    0x650058001c1c03400030201c9413600e010800303a44559005840c04e0340301c20704908810800d40300744940f40b40210740220b000b0349418003c4035242d80082025007048007252420218182c01c01c07074020b02091044d5020103070b244086001e02944140e620035004104060300240580360700108440d0800c0c41c000d086043c1c0c640c008100f036280d400d50142c2a426660070450180400c10400510300c1d44c0013207003800070030a641807a003000050480707590070f410300001002c2400028800c609a4043d6143c82e031700f49481c1d40e40c01c40050000f245001005405010000e001c140309640b80490815540c419241a00c031a101c0003c2c032800c0300c085240207010340b400c4003400425403502030121458410030303000703160400703481c0d101c614142202a40110003142511174108050111600c0540c030382407505020345071561407c00420824842488142410740030052041150060329668405c0241c2100c20207a00e19182d4200c0403042d8043c0d401c2030054440c0f800001039110001a1041c8607444050281c2a4021103a0303903c = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 164793201 1250 164791951 164791961
    0xc0e040c0e06180d0b040f030917030a03020a0c0b01030b1006020c06090405181b090c0c0a0b060a0b07050109050c100c0b040840030809060c01020c0f06060f0117040303 74
    0x76900c007200010b04d1022407070f00700701940558041c1028104144c010f2601614a0420f680147c4c1d0420110b00c64088105012060340e200d94131070b04003d85c1d65580070008031100541002c0003403102d0111000801070041d1002040d2243e481004450340c51621050180c2c1d4800c055407042c1c0d8084410001d020581c2408e4019a0f000410302d001100100000c2040b01c2c01e0030b099400102901710303002c441076101d00e000031040380c0002d080070106260014801c09540c132501400300141041c9658400b048060b12020764075001441d00c40c420759118142482c1c00b0f4064803e5070320a89051007180705034800e6280c840088c0701c001055440c0c0c0c03102c904050b039078060309110040040d240c0c03403400c0c0800382422000901c00219001011402240503414040400503545011030710251064500814000103d030007040f215000383c1150413a46401d8810700b0280684900d05038400b050003400c020f0404044001095802440212070415881040200441e01030024610002c1e03000744035000f00780400c0c000d6105c = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 164794451 1250 164793201 164793247
    0x20a0b0c0109122607081f08030409020405040f1e090501020f0301031b0609060f050306130204030b011a0702090a09031205010b0403031106070806190305010c0e040c0e06 75
    0x41001c1c20251035905601050500081c08a625107590701c0c4d101c032050000c42d0000e0340b5060701580a00b89000d0041c031031039004100125000144081410100325840d419000f44226400c6035a51134445010501070740240c4116801141001d42102031412540a580000311110600c80341c102c840001e000c014250211080d503203558200100c10b14401010015800396004a82110308000003d0560700603e0980d880340b020055014000d21007990700c003645411818461601070384a4440100096506102410200200d8400107001040022039900785040715170800c468851040625680f0205201c0c986000f9800501400000c0c1c9030781c0b15622a602040c042d02e480e6020301c01380c0035201304407602030300034000d9200040303030800070954086000f900d6840400041c2c840d5041813030b001b901d010f0000c0c0c0118455980c01d03c1500500d04542422001540c10500a0010b80b16254001d00b00458914815004034101202c3c0180c1c0c03401180140c01c0440c0150040e890700c0320a0501208010000c15 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 164795701 1250 164794451 164794453
    0x120b100f05090d080307020f16121a011410050403080d02160204090507151722152901080103020906040f11090a051002070902071e050f19020a0b0c 65
    0x211a04548415002e1082c00c3d11680d040c03036036806c0c0044040e00d440881e00102a0316800900710081f02e0000381c14500c110780d00804e400c00014003070b00c1d00300c820155a902001014010500000d2021180301c18660b140c50160342d55241c8001c0c01c14100ea0b07030b02c207a000203004501d00b0444103030f0181d207590080101c20b0708c06001f031500c52155400201541c3c0e040340b003070f03980390b0010005119a503448041c215520802d0308100140c01c4191161020580f0002c016480a800e050391240c12840c0d04281d403400030b1303407000c101c241e150940d002c1070004152059469151000d24600c0c1c0d25502c0078640000d1014078161201c4502e40e20b541e0030040007900080046410030703140c01a540c0050001e00031517030f400f507461501580344c413075400a10503240881d034003041c400c0501d09540f405003074001c035424041e22059a00540e4034800c6082007022440e200a00c5403401c085190320905101c0089045411036540b0002c0e9280040c0d0400400d5403800300c028081d6100103868820041d00341000010702d40224040 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 164796951 1250 164795701 164795707
    0x6020d0f090521070b160803070e090a0c02070b1c0e1204081b0603070c1e0b070818010501270b0d0308010f082a0117010801020406120b100f05 63
    0x21000c110841c04984079544200f14100c0c5074200304805000e81401380c0000705038a03090460030006e1035003007507440c4c174041d0050600201155995124000c050080301020706040007608200c420500104590091440180196200854040040340495081d0b15140d06400354510050200e44000e00004400c02590720a500b0100215400c50000e00010020400582052110b0040f640ea00c00000d891881c403500b010170410006541010403180100d411003c01416040c0881010041c0c401d01c1101030002410036042240403540315284d28031519007007000f5041c1c84030b413250441c00d990085c001d484210011216504941300750001200c1c40d01c0d10034002141c0000e10310301280480f441100c054000070310250050005c89886e400385401045030400038458200c42d800c2103915201406284100c000d0220b0100c9031982c4110455000440501a903010b42e5030b4400066000758040d1003882d02103040aa0300c484550458400d12081441c080c0800c40004207402084411a00034505002480024 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 164798201 1250 164796951 164796959
    0x6010905030d02070f080705010c03120605030102120a1803081f03060606030207020a0e040c06050f0d110309070911070b1e01150305010e0402130e1509071502030406020d0f09 77
    0x200240c0c400c0308101d402901403e0f0030311701001031302001c40d04103028907070251404100c541da02c00e250304003c40c2c05281c8103006510000601d400b810903a44400d50560000c508401c6480324040c40c0390154000080420031b0860034401d200405e80d40b100c02801180b00c1400192680c0001e1140030070804550314480c0c1c0c245c1d1a540c465080760f0550300f0a40009501040c000700310304180076202c0c0505448070100101c0c0c41e05940e6010690301a0054004200300030450b00c03000a0303500c007900c103013402c250401c0c42641043c2d05048070580045560030018803074104000b5440d556881031001d00d10300d0800c00703880e00800303807a010301d43c02e806044511140005912005e07d61003c4002030b000c0c1c40321092071514018180d00003800c0c0c41c01070f0800c0c0000714008041c040140d07240c00b80b5803000046d190300891582d001c04c0d003281c00d0010465801c00740440340000c0108074040441c04006484c9817504000600303821040403680c03070040d8014140941d1110a0860202d400380758034681030640707450800005a21 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 164799451 1250 164798201 164798203
    0x303070218040218010b04150509120a0303050a060807031101110d020a03030c05030609061203090607060617030a120b0d080c06090601150c0201080c1b030408071a040e0601090503 79
    0x600280e5203060101c80c2800210300e03000d050701c142001050850003881d410540c45c0e25503440341e8400d10641203280110341007414005c80035228542c20003060600901d0464021507210aa542401c0300000d00c2e20b000140e040b00144112000e590500c0e0081c0510350031039580c3c241d4440d9504003141882041c43c80f01301d500508104030001d5082c0d65014066078a154640070b81560011080340060240500410507941c4070a00d065900c0a01110301c02c81900400c90354a0030341c841c42200070780281e0005002d0080c003403580c1020084031000d03422469018059541d0a80b48c1c003513100c3c98000504202c0c002c550fa0020345c1c02410240000900140940c00c6555440b40940e00119102683d504408108000349030148042401000c03442c02c1c8540020024000500500c1381c0e520090502c21100e0200f600f00b80324000f601c5150034080d20340c40d18186200b00700fa9032504a482480c0711485614000314114043d5808480103403220015503007003906000c0301104442d00145400d040003c100c0b000141035070 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 164800701 1250 164799451 164799469
    0x15050307080a05151e06040603050303090102070c0807031a180712110301060e0112060209060309071502160e0402040e010f0501050a121709060f070302010f05010501110d080603030702 81
    0x340c008018882101e1501d009814154203014840b04000104c08002038a442403194241841214042d24410381d50b06000034002c0c82c03d41c101070503d11010041004c1c000b01580289180c0d4059030380a80a584e540c2ca84942d80c00c464080200080e1907018846c0c181d103070b10a189500659aa0b40c504020303002d09418a00c0c04059a0080105585000d401414020400c2c0c0301008214150f00a020141c100640916010018443c004016414070303007900500026605507401d58000901c0e00c0e5490502c0525076a0300d40c0c850160703401f1407003072182ca807041a0000803203840c9042000030119409207089030759912100e000300281e8210ba201c1c2044d21481ca806e21544400741c0700f0f0040002c15504220900a845035560003100c100110740c041180450454108100c20411885d800ca5030390251001080d410300666003182c407e01400308400d020950190013400c0604142e800c20803040e039a81004503018400c818010400340c00c14002440c14a12035450b280e80484050b040300c0c5802c01a601041d546c05c = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 164801951 1250 164800701 164800709
    0x10807060804020109030b0a1e0207021530060415060206060d15020d0509010501050102150f0411031c030c08042f0618030c040c17040219090b12010606050403020415050307 76
    0x2550f601914865502e80c00030004e49d4045000301142048500d0340400c501094480304e050074804042194800c0d4804025400074140321703900c0e036548905040a80c0c48240a095914910490910442c070121000b1515880202c40c402e81c000c10f030645800c814022005130304082542c4400c01e01042610300041d600051251413408100003d0f02d00e8903e0603e42114010780059045410102d08801c0c21000030302880d4003e480204182d4958595203000000c0114031000c2c1602f502030003803011203011004290b220a82c0c0a034400b0300504010390300840b101e13402183e008041d07903020b04503100100d0540c8110401c41220181c0741c0214481500020300c5074014503903e005082140201a1040c1002d2114030148035040d2814001040582000380046004a00c0c1c09420105400018259a2049140e16084462802c00302c4010f84030800c4001170030010082030b015150500c070400f01c2500511a078000c64400385c0d175403401c01d420769080001030080a019034038665050440030540d1b035414007088000b0 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 164803201 1250 164801951 164801971
    0x307060f1404080c040b01051c1802030d0c03030b1f031d1606030e010501061403040c03020d0b01060e01080106050a030e0307080a020303040201020d031a0f12010c080603070509010807060804020109030b 89
    0x856003030403c400d0380e0303091886c0303410002c007400190482c0b25070034003c0d90101c400d1200030404120504000d010b54496450282d03162050300a01040550440e1454800d503010355400d08c103c4501d40140b040315400d102080441e51201d64071640000d00c29030190480002c141c0034003e8202032000340d2460810b9a8044034201d2141d4082004900e81522403480004c0c0000003d100c0340d89000409013841c005030400304511080000018108400f6228020107164001e1203030245401600340903030134100134000d10000c24082c45c107841c80ca6006403040e5040701c090b41c2c0c03182c0c9003802400b41200134020f0217a82100030303c0284209400581948081d00400301d860b0300550300d91805000091030004074a170818103143c5000c99401181028041004d0010f500760b8140700c40c0c1354001c0c0030441f07141081e00c3c1225079510388072510b0102c952241005001c2e0328102c040b42c410030380ba102004000320081c030800d0800d0b401194104105401140c50540c40b90050400c2c6001580c0ca844040451030100c800b190b003 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 164804451 1250 164803201 164803213
    0x210603080901030e010e100b06131d071106180c181f03200f060d06050901050f0105032410030b03100c0507330911010302090307060f140408 62
    0x5540e1521890013412a030710000c1c07220921000040e0b890300580210146c106072600000c050a07140c403011540100803145403807028540d904040b003103071450301c0f503a00100842c4101140c1d40c584034560001d08518001c000e041151507028511140c3d010005030850640111400c425099072201020000c03c4035500f180c418615004103481451001540007250303105402c1e4091011442c4094155001081c41000403a22042003002500e9400c0d4120b60983c0200001401000900c06821000031514203071042c18450741c0394001c106070482c4010940740080c80a0000680c10000d4070f50806c3c01c0384812440403240310000021a0400c00000c1c00c00c00030948400c5c40c482141400c128081d0145d01d0075004108401440000804911400c03a01800703a00e803203004c09060140040044c806000144400c103540c4484441c1c10002e0500c401d000c2e120f4201c410b8001c400ca500a0084490f140ea00401400506080a2041d101056980811010445110218005015007070010b0000d44014001001 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 164805701 1250 164804451 164804467
    0x1b410d02090f0409050d03020c16120209150609060f0c010c051905040605070b0a0e011d0105180c06030705090405010311120d050a0c030309050a08031b0301060f21060308 75
    0x100742c2d1000c002da8080d600c0d050504011404c089078480364006546005681c5060601c0d016107010310380c102c0643c3c0001c00c240001030052810443c0d0603050300c00d032543e45a40d0317286040820560304280e400c0d500448100708403045480d080004101842c0b542030f500341400e1a8148060171101d015110314041000043d400194034203005100c44001e0051801518007810508001e286004440008000800c20400716114113980d8118a040b583c01900030880303c0c10f04502c610390a41049400781c1654a428046074120302039011887e000c950150040018400d0740302400420360008013900200501403025002d195564019203000f10b010b00c420103618081c4d1b10070030440d02d1490420a800e40d0003001c00840885e000b0081c1c5001c103616007002e0518140701e040c10b90282444110092450045401003810010781c40080d60282503d0051066203400440030005184400e008803c081100c640d0400c040c0386c8034545140740f03600d040103120f101c26a0ba54891055800d5500202e400380000720b00c1030 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 164806951 1250 164805701 164805709
    0x21c02040e041704050303120403110a03120c0206100509071710090b0d0b061203040f0803030a0e03040b0f070807060e0106061e0e12070e01091b410d0209 68
    0x14507001c0410700a94501303864800007039524450066840c80d07010762a0300080505001d80100b00000c0d40b01070654602230315500e0010102c0d500b0b0407180e508036107002071703800b070301e920008400d84a1812051402c030720f1030401c0d0800560f0b80c801400e4008014010b04100f25903500c1c0a940f41c00364002007807801041c1c0c24901550306840a51f040d0901405000309044081003010303c685030004010348600c1440c0c0301000354642107100310703086200c01c01443ca0740000c4c8031800100540c4503e8894904000d6401951102c1e9200e11481c410b0b01904541405050752020380b480080200f030740706841203464808242c0d698815030315484051802a5902c9000300a041c1e001508411000c0c3d8108825054801c2110041d00220340d074842c240c018401d03100106214a4104010f0740900700030741b0055070569440d00c03000050903811049a540148042e2000b803040e01840b0502d000d00030f1001c1015031902d03080c00031104010205481c0100b940b0580c03090314098650070007899210421030700903036214401e00c00d01c = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 164808201 1250 164806951 164806973
    0xf1803090501030b0103020708160c050607050709050c03040b2418041a090307030c020607060509060405071a0f21010f1412070e070507051605030d11060a021c02040e04 74
    0x3c13505042c01000210300150f0700208490100d01c1500d00e850900109040c0a00003900790b400042d04003000180c04010301000040000484150349418415035a5040303a25000d0b0200344d8008181640a0010441c0c034004154110500e8980d0305440f040c0e026040001110115480a0301151400100c180400c0c405680000e581000c1d8664070394090382006411141e0b40c0c883c8480240c2041a4410300000719503500040750140c0760801300a104505110310940d458800070b4400300e0305407144420010700a502e40f0f070050a12096450302501b40021409107196a44c84000c80203282c410a141255882881000c8036000e070003111005065681400320840c144410003031514400d05c241c2e586260403010000e540d07010341700d110700452865206c03180255414021084010190700991808004801c4104804c2c1c0455404808031103040443d000c2c10f1f6190819070040303107a00d4004000140503200f69400030008000c2c8009045600000500c80c1c80c100d03082394000751505011403080c0024841c8013001 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 164809451 1250 164808201 164808221
    0x120b0a06031e0b0112020a18140306130803040201030b0d05010609050a0b0d0506060105090105070507090c03111e0901021204080d11030a0503060d06020d0504050c010207080109150f180309050103 86
    0x3048400c0c43c07500084c252601c50100c9a4403d50002030344071909100e2004600918034038603030b118056454094680f5803041b81e80310507001e03108600c0060511003900794005429500507004c03a1a64030f9940045002d0311100c42e01a4100b040700b5041000114240b0451005207242c600000300c0b800e0040c000c40c00d03a9440050280b065010007a0301001c034001060080d0403e009080c5241d13940581001aa2140138500014103140210240042c2c0c43e0090313080f0402d08500c0356800c0004401c115090141c1e4040c0451030b0301050142c07c10309494480350070080641060500481d00c40ba02e2031070041c6090750140d0054034290f081501480704d110303040766044c0361019150002c4d5082102501000b0302c0e0780001890f0324400c2042d40003000500060340e040702d0680c04503007000d004900d8641040da0b0344d581c03040c2d00d960040c8a01d601c00585080184108048568000c1442180740c024a62120140a04c04528a45a42d0354901c405840f0b11100050b500103210b80c8640350641c1c81c5c400050112100110 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 164810701 1250 164809451 164809511
    0xf0f0201091a031501031e0c140403051507030f090c0806060303071a04030e0406060815060a090905090f011b02010516080106030c02070905070c0b160f120b0a0603 72
    0x903004148050090989501c410140c10307000042da480b00c0121b01528030343d08010280e41c02d00320781c1c981c640d009070030801404140361511399150300d007a8100c4845101d1884060a0b5030403120000180200034118140c101c60f051801084e055074240c008000c0f610405411518030740c2605c800c10819500740446540003504401540c1000c26a8440c0040321090003088402d01e04a140010205030044040103c0d100014008201c001e4843c14042c0c15081c054800310700c600101380ca1818a40b405204540014005540d000300c89450046244007a21000d000c103a528064080c490640326024803896159a2100041d0b41c0584000100a0f086910190100744c486903202c2d40b828074941c00aa2040c1101d42c14500020311040404049041280c9600603c0c811070510080c0320560b6403040c841c5a20318020070700c0180310f8540da40201800312206105201080a4a41400a1902411050703c0e0302500311004103568540c58001006400c00741c00850110380c1e01d0b0444121400f504009040340c1d80005 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 164811951 1250 164810701 164810729
    0x14010909020c071e0b1306030e07050f010c0204060b0c030406080703060303090b070501022b0e0c0a0e090a0b070804030e0306040b0412020309040f0e0d14030f040f0f0f020109 77
    0x204400fa120b90310790280c04600091000c450051400380c0702910000c00840452607100c40d06c1481010300c201e81131244600103820001e207000e805601086180850300001c1c500043c0d9502403006641d048482142641d00c0f03035031070f6000501003181d0350041040c4031000d0065580e5a09101019041c028007801e020100351070a002071000940196481c0180c42a10380300b0f94503021240740c59070280c400c5001d100c070754882000c07801c0924076100120007981c0d41c036010103108080d810411540d03503955000101c0e610a44401080000b8034000c1949900456014185e0b45000e049880ea01d0070380c1016600700e400030320f5503801c01060503803000d00e41c00c0440b4220082c01c40780c1020703252100c1003080500041d000c8a100091a04018020011900e2290010300244103032540c0a100800902c1005c40548480c0514040c44440e544518824003425405404c5541151608070000d40001001801240d20f0102d0dc120003010a981e20034141f0a40d10440884101030325520004088945030740c810080c5070225 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 164813201 1250 164811951 164811967
    0x507110606040b042406080a0e0c1306030c060503070e1e1e030f03030108060703060807031b05090c21011202120a08030103050a0b010515090603100f1401090902 71
    0x3150881d0024401c540200c1c8103035006002500a000c1c0c00e1001001000804000d14180340c040c42c108100d50154903010010368694991f02c0c20b890900072a514a81c21007400d0400c1c0c0d2404040f0700d0003611040200045071131f100d40e41d289001032030360002408a44040100080c55611003400850700c4816036a2441d030002c0e40900401403540c1c64001803295601c0c140800d04640d900300c17140700b1810020200c0b40c2ca0380005c502c0d99200e034800c1c001e6080c02c3c01824009030200c0d00900580701211215001064200c0c0782d0307242d003c004500b072404401458001000000d460b60b0710500340d4010700290700300555490100300365884000c1d0705510241c1c00ba0080300100950741194030220b8582d901515810b4000c0c5480c5481030401d8141070000381825401b100100900c100040c000380f88600c030780468800e903601d0308100040e4171100750085240d60700400c05508603042a10246410500b0f0848600019866141741d5031002d00940280d44440c824681c00c11843d0383c00070300d1341e0007800c02c284114584215 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 164814451 1250 164813201 164813203
    0xa2004380904261c0e01050403080103140102070c0e0105030d080907060c110301060605090907020f060a09050f01090305181503061011011b030b01050c060714040305010603060b0301050711 83
    0x900180408458903904050443c1c1c1800311008101580c1c3d156545060001c3c82070030808062202e81d400c01d113025400c2840c1c400501c01c4030f00540d090380f60041c0c2d0303a01c0c6a40f099031595080011250654080c0540d10000e2181c2c0e458038060034869a00700481d45c1003200341460710b03545400200c00c0141540a1044004000c0360303220039501076140c84000303440c06003002108c0c40326040f070b61a019817801c3d10002d1203d41c03000240c1070054044a0750702643c3c8803685c0881e0780701c41a05200e10203800004c0411021a016400105118841c4054560365030f60341650908450006030180c02164000135258912218a08042c4401c00d00b103650f8081c144201d598122503002c0100114000c600d00d5041900c22070081c1d10700174201901200074045c154000302031001700c07101c02860501080c100320705205c2560141003902c40a91200d0020315455459510446850a41007080441135008010120105800380600d90245000703400118400c441c003000d040c21520001e00240c10425010092044034070 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 164815701 1250 164814451 164814469
    0x8060f1e0a180206030a060303030b0a1a0a0c060c0c02040e1f0b0d0c0f0302040b090f04060906060b0d0204080c0f0a150201060e0f09070905090a200438 67
    0x884070400120000206a40c0a11090880010b584078402008004020600390000029240701e664180300103407a00302403081c02e203039500840400c0c4d00c0d241c0c00401c1c2c1c40d80e180090b02d0a11032030320b0840034034040d6484006c1250300c442e40034000103d022500c50154241802070380c00e031015440080801d554100c80700c0e40719051041036202c0c40c50311060001010365512005440040d0018241d0207031543d9500200c402c42001e1008900880c1801480e060503c0c10b0f8546030b100d080c1c0e4030044443c0c0d95031a5a4080101100802280c24540c1c1d250082403503140034020f000410888400140c1d80da042411061412496112051140c0d41180d5108820f0303e810781081c048680b005100c400320321002e18280d02400c650741002c0703e01d215000400000d40c8400322054045c580740b400b5100e07017035220101d210036500b080703451500036880402c000001030b0420340c4011720614113900180d22100d40c0f20004042c0c403050314102122030420004803440402e07072060b028000e00100900c5201c01030302c0e004905882c0f = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 164816951 1250 164815701 164815711
    0x80c010e1b010c021801151b030c08030a0f051816080309150c0303040f02010f030504020a050f060f0a02010203160801050112020d15090606020114010506040509090a06020408060f1e 80
    0x15158414011900c9825044c4101c141aa64503401796031649000062518640c800d0000502941000180029140800b55045030580d0380d5220306d000d541c54014180c0c1c0043c007010a5560350700040020b07503070a0312580d80030301d8004a8010705e40707040090003840e02800d0030900058403400308040150319000001c84602c0e44054a510001504c440b95a84c0140030b045041c0115000000030441000400081030242a04c00d80350b19a40e1310011360110207c66044030001d4016040c800103211915103124055a24040100700d9441c0202c81c0c00c9406450f0071500180015039008801d00102607004511005410b443c0d14000c61950316001c0001c0c500081d001c6a014003540c0001e03400c540d4030054001d20081105000d1007501c1c542e5a86429000f843c99205060042d403130301981080c178203808a0074134100e6030000c122604082c1440300700451200302800d1403500d40f0030407034800005969400604010101e0078050400743c0b610044255400d40000c01101c3e100311b80b51401c81004d016a5013540c2c0003 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 164818201 1250 164816951 164816957
    0x1031d150c0c0115050a080c010906030e0304051905042f090a030516060905060a35010906060813050d030507050c031201090e030a140f070609080c010e1b01 69
    0x5440301c14480c4001d00c07601d4036081c065420000529141c40390b00b0f48400417150300340d03902e480306650381641c40d8445015030720450014200803020000280b0039004082510101419a0301c2c00da5104001150220480800c0090001c00f2000300500d180c58804d04424614943c1c01503a088641c103180040900040c1090210303050108040704184c4481141c040616404403c903861181e01580c80d001c102610311030340000030b00008000c81d15060803820f40b1360440301c0d034543c0444151115020120380b1302d0070700494007005000c10400708500e038404145000385003a49002403180d08010006003c0840100701440c1c1941600070240011000211080b00d100e60746000680b40d111003504807610320510742420310920000c00e00e040803807080004941280c3e4042c01c1006a100300702d101030f0312402840c564801080038011203980e4a02c2c544001e0040c0042403210710301d000500d6031000101d980780c8209840f0900049a04200e0042c240308924a030310044004241702c074843c0c40c444038949940b0000700c1c10 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 164819451 1250 164818201 164818243
    0x8090d020604051e070b0409090615050105040b0d14040f140706090504020a020c04020307020d03140603030f0f040513020403120306050306010501111509010c120c0207060c140a08030601031d 84
    0x8103540038080c03d001b80c0007000030285d03201e0f9034a400310051301d56281c090f0b6003a031401c240b04100c80c803140d5552086400c1a19818100303843d190014569030070849555000c0d607240c940c02070310140c84a200328425841900741880043c0309040c0380300c2044032550170b004141c0c01a14188034140d003114040c03048034401caa026940e441101c2c0104c7c10301810100d0150040d00100900c8101500400c5100c03902960366030410a450310001c0c01d440c041c80903190207415410400400d0b41c042e00300001054084414182c2510345603640010030307114103a24182d45100d0307501007001c2c070401444072041c18031002e4902c1d007031001a090a000980b2803506101c2c6a05101c8405a42021a403060102069a0f8800540003c5a1805c0d030400d0f40a491400b0500380080c0320001c02120300d0a6a01c5000046442a402800da031030801c682525003480a00068410710340780300c21042901c008205102505210f1446662281040000036003501c80c4084c0d2901d8817044184030308040600041c03642d020f4609110f01d100 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 164820701 1250 164819451 164819503
    0x210f0609050d05030114041a010507021207030f0b0f07020c12010f09152004060305070c0803071707031e09020402070c0602010504290415060b040608090d02060405 72
    0x1080c4440c00100280101d0300b071402c05a4003c8007031412500342e00c070500c0e21001446c1c104000c480302c00c0c2c50741400410030190301015511403005402000d101500b0101c00d0f5200030003491910a8a5204480848030441280100281d00e1011504071003031001280d2103003006e200c00f81d00d07096510301c2640210825074070212510003d401526201d0340210b01084080000d0518180310001004103880705420000801042001c0d04207448107113a034a55002d06060501d1411000b800c00a043e1800b00039241d2203c40110f01500300441c0a10040d84604031030b8201e2203001c4c4040e140040000c1c0a00d440d01c034065400c0f0b081071400c1a4105007000d0300184030784561000030024041c03280050503200301102c1c003003607003030b0154405d5001e2401107241c1e02c1111200608070204503c00c40444030380c170300054045000104000a440e6050064900c0421080c0d01d49085041607082a40320340d00069200d03050090303122051045d894010b103648040e201e5480c16454840d960060901141c00c00002514500 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 164821951 1250 164820701 164820713
    0x120c190b340e030105100e0c091f020c0108060a151112040f0614090d03050307111603020a08060c0a20061611070302090a090203010e01110a0207210f 66
    0x60000712030401903440155009074028941c48400400c01c0c065883c101c04200c0142101000c10121204050009296034a0601400c1030380c00408031150400e82c180842e20040681e04400e003070205580e4000c0480e10340400004000b410082c042c24000c00315070005014100606055918039035003030400e007094102803400d584c503000900e0441441c031540407030b002c1000c24124800400321500d554810502240c0c03001d458180e03109121409a101c0b500110907000a4014170145034854180d04048a04000350540c4508201c00000d140078200201c42045c0f0031803501d0500e44000d0000c802c000c10b510b141c003600b10381c041e100e1200d9013414001042d01443c00101210300e28400c0700065019600b203424226040d5440b0f88602100b030021644421542100303550008401c422680c0040490b01c3c56240c2944d814000c0c0302412069070595220609448c801500f402603031400703058444000d41d560403136a0002d0800032035400c00c000050010351884003205451602d4091036400c140071806001d05032800c0 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 164823201 1250 164821951 164822011
    0x503061c1709180103120f0201060b0a0e011205040503030907080c09011a040b1201050406090b0a06201c0f08160f050c1f0c02010c020604060b04060503120c190b 71
    0x102003d007000c0400402006809011803500d100580c1f100c288040480f8000d0b400d81e501409501c1d60b100b0180305e0524058455007440b0040300060503c1c515190040e8130030401da510480f0195401e90000051266100382004801e0040072a131000c0c221600c00400090603404043c456082c1902c0320b40303911206448a00d003120001c200307601c11a40e450b021b6002d05c00c0d441009100b0385114900c1d05100040d94040e500403030740200070061164240b28200002070720444a000b03801c0c055440b441c5180211510204041811280384145803801c804800c04003c100c228102c00210821010400388014a82180b90244c00e60a0364101252030003600310048400d030140a006c07034680d103e450608d852000f008500021a241408000e016955080c00141c1c01d07201c80545880043c0e015000080104070343da8006218a40018004100d99070303200d0000c1c1c944010800c02400c205000140b0005240c42005401014600c5210390b4400720101c0d2120904400c0c018501603007078450301d451011214140c101 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 164824451 1250 164823201 164823229
    0x121080c031b1b0a0506030a0f0b060f0d05010b160f051c080619080c1e09010605040905010f050f0103180606081e06010f03080f0904020301060503061c1709 69
    0x2e0070141c210380469259030781d00081820882c0411507030080c0700c9051000c115025902c028000500e940c5070446181d000b0804891541002035580c8151101544c0b00001070602c41c07803001c1042d4441500310f024404450061f803052420850410103000052603810111601c10f400c1403046c9503001050038102c2c1015482011601c404449000f0445810703045040c16020390010b56000300c211684116800c040506402202d4040d4030a070010003513071405104031010b00d500e40c0101030505155401096103220203030480e0000c0388000c43e0602c0714800b5031080e94018224103800d01542c83c07078480459074620a1003546810140c44a43ca40e45841248412015203030740302e60308100d480d984581558445540307507041c824203900001324116140000503030030b041c0c4d0464005030020900d503070354060480d44450022640260b0070312020309280d0301c6101650085c56681c9626503a0b1a1100800031209100349480340300007038803485480400c105189000c0c41340316100d940ea40d62055500014040701034540 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 164825701 1250 164824451 164824477
    0xf02150c030106020114040b150f0310050601111209090c1905090114120f062701060f051c0b03030c0109060e0609060c07030305040305090603041a0121080c03 70
    0x10301048150000095048400c140d00030081c2a2152000b00e0281d041920060b10a02e41c10303000c592780300880c0300b481112140c000c12a04801c40c412010904080c01510341d080303015500c008010740c1d543c000300020007018084c000340842c51402c0c042c88104c1d000386c030400d40c0208603240c0081c41c0c00e062101290300603c001c12880d01882d0800318010003da000441e1640050b40341e890700031210150b402a901c1300550802c01205540c2c2d40c400610f8100300091a40781d00403d05d01c2000b0028a1620f2840d035078840c82402d0b4003c9605014001e88648910380072802007210400c1350403c40c801010481901c0f5950901c003040c00d1401c1d200180c0307980110084200d95501c0c0041c0541007050300d5118210716078000c02540c810b59903070070030551504c0c811528444415004c100000000f032181e1700040c0d000d4401c0c00c001307041404a1002c030307140c0d40040f1403c9a00122104409500c2c40040035480d0040c00340c4c0028241c40910f068849030400c0c0c03503120091a038030700800c1c40b0300040420300698445c207840c62 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 164826951 1250 164825701 164825743
    0x60f150708090109260d05090a030602030403140307091a0f091002010b060d090c210b0a061511010f020301140d0c03021008150108010302090f061503010b0a090807050a060f02 77
    0x15030f408000400f902101d017183d115612000038010301036410344a402c00700a004c24082840c584809000e50304c0100100d00b00050b030300c1c103950040c04003030186000740d0450350742407000d504260f60403034280041590a1484e400074000c3c4507220f0009021070f824500d080d242081004159201603002d400340c111981d82c400c4012800e411110841d9000d11125030080d0340d666100d9950b03440903501c0c5003914880000e030000b1444100b001c00c046402d400d81281a0003000034046580320342211100309413604410000385407280c070720b04902090090000641c26400b04600c0c46d45080d844440028228003454020300211f04c1384401d100c2e0006242c4001d54002e0000d0380c0c600e81c0100024600d00c03084446840c0041d000b161030200b54800c001260603654042c00f440a55110049e1035001c11800605050740005150103082201d041036014600900c4002045d07a00c484108070040c1c400500754000b8105a4000001040f0329524030070240120f54031420000003409951404070305000032642d040281340c03c04 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 164828201 1250 164826951 164826989
    0xe1f091104061404150806010e040812040b0108060a0515010f030e01020a02060711070602030306040b0607140d0f110d2a1a010504091104021c0f05060f150708090109 73
    0x4060724140f2407421141040120701070700c3d80441d030000d24010303c40c2c03070780c8680010b02200c10f1400c49240c10034040c0f000c0d01e0805a4a0407145444035048400300c421800e03201c0100030440080000079041448540107203c03914182112074545c0b204005e4640c100000d61603490003082c0294820045140d0313150081d90380c2e56002c003010755140c10590300740c030015241446d03404824501041c01000c0c0d60706907000c0c1d491034a40b101044043e12502d40429804002042220000360a60304249a100036040c084c2114409514025102300c224100640034088001900450300c580070541d45030355801e504001c0522814480c0e07840e4170302d070441500342d2980c0340b03030000764240700426047d268491038001201c905030703884e0800d01041d101003600040c910b9000c0808403059141179000380c405420180034042d1074404078061101541d180003c59019107039a041808018200100502d00d101d0b030507503250102d6008856042000d21404d000904140c00100f0682d400f1b80c81042081c1c010403c2810341060b584070 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 164829451 1250 164828201 164828219
    0xf06080109020f01020d050307050702010e090702010c09080f15090304120b0f01090b09060120071202030f19060b01020705060403240e0d051804110d0e1f09110406 72
    0x142041c0d100c1c05001c01c41611661001a0006d400000381c0d480c582141c40da20026503a41d006484100d050003040c0e040d0a80c581c594142207071064505500214034205114000ba111819a4000384a13640042c55420a0b034a40012104140c8030441c184880c0c59494040c00380c214001da1708000b0a4001c50010b00e42032040440a043c040d0101d41100c0c0c01d1a662851001c080310030b941503058004c144e000000e045503000e00c10110481c00003004a07030030810360740241b80c2403100382c0e08a11230301038803000e4603000c0d03050800c001c981c01e01d54500101a41e040e154070740d00c40d10102d0036009207016111100508141d20a220201c02040c000d4000307038603581c603485c0180d1340c02104080c103610303403055042580c00711329a4010b5010b034a0b1540d01505d041e42940d2411038644c0e110008252946140420501c0203444611804508000c5c18080c1611100c54601d504283c0d043c80840c0c3d13899511410158901403a00031000064500700c82001450382c00130f01e07208145d0380c408400e50380e220340b42c1000090302d030302c2d = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 164830701 1250 164829451 164829461
    0x20a170c03070b07120c082206050916050d03090513140103080903011a01080105060a030608070801021908100902160204052401090f090203070903060e0a0317040f03030b040f060801 80
    0x4100d0321002c0d1702e031448100e00c0c011a490700c100702c0f00240e03040021502071440d00c04541c4221044a0300c90a0b41810340d1128419140181c4410380ca55001d400f0394001e0442d80c50400000d00403c45a072031284179142c40c010031140840c007034684079022940324140c40d46016401488103c001040c40c1c1d00ca51313901d00f400d00441c1c120000c40c40c001d50800007504003031407403801203020700d81050b100d080f04c0303074200300070701420f41c100c8000081810758442000c2404901001914014520034001590b5618482c030403080d0f40c1d65640c1080b090040603c1402880d000022030801a2814030350010380301d520009542062403600300001c0d4100346450107020071901e03044c00507907400706c2c84006040701c2200c040c01140d1001300c6204500650b2803608042c0300c216600d40096800c16041d02e420301c00181c40e911900d086136440140e4a00a0f4008401c02d000c158004030340340c0d5052180c0c10501051701d031075112980d000c0800320340202019a43c81c1c607402a660f5075441800c1c2d40d01c40f500c0801c0810f0721401d846000740 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 164831951 1250 164830701 164830711
    0x70b0a0207020a0801020c0703060c1101050f0406060e1501030b061c05010807080d080411010c05030d021c020a0c03030c022523030d1103090d120f0e01020a170c03070b 74
    0x3c40500c80100d044030b41402110180112580141451403664a0b00c0005010340c014500800c0b642c002c0e580d4424409019082c045c90014000901e01d080510b8043d044505d00d0340703c840304000d10800c110b4400718100440980d184207081c08201780300d010300007581a00c101c280d0420311040e0100560019011580034034107980300081102d0342a51140d60150b62541f00b03069031000206114002030001c0c0e0a591100400007060629401c4002c05640f03c905503002003001e4012603a0100b981e0240c655865448040000c46400c114602000c50b40300070329071076500101800740341d120828984030310310812850720898503a0361030600e0034a80581200410300c0900c507001c46c080112422862480104a60300140c0e04000c0041c000c8000c3d171001035545041000103602c0700c0c00203002051298440700b5840d09110701c280d90392945941c4008000d042c41000038403241c00c1103c54842d10401d83d80018100c041150040039483d03501281401600d69841050517126080c000418100200580565858094 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 164833201 1250 164831951 164831959
    0x1021c1206120213020913020d0b0d120e0409020a06210c020f0111040506041e03020301090c05091305061f030c03050a0201090e091c050c0601030507051206090c090705070b0a020702 80
    0x80100c071410b043c241c1c02030b1907501c0e82c0500741f81d0b124034082c9090380c001c25001800010218041c0c3c1520005003030401700c6502500c0e100c106049019215500c9141e0f003811a208803410010103d143d0089080740d001c1d4003c04080c00510752010b16440b070072402c030b140499442c04042c490b803081118004d440f1400d0b42820340d000c0d0b080c16130060000721140305035010742d00d025205038105071070413410b2384a16013a2444500310350074290011025841c280607000c040f40c052642c40400b9841c20041c8070440d00002c2c41c11802c1203001ca0a0300003d03901054450700403e40c02c2e8018802c80b96030900514001603544010102c4501100005c20010007080300c034005030007621035210b0a42c0e0ba81c0c0e2800408403c584a500e184c0098885505900c041440943e400130349140c02420708483e84609131074110280c2080d42e80d540010420410f42c5840c198200c641100c0001800541c240700c07140c80c0e60342d030300c0060700e501c144075450000e950148a401968489904011481401d042400401001394030660301a401 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 164834451 1250 164833201 164833219
    0xa060903020715110307030f09030602070b01031e05060426121f080703020919021305090a090b011712040303030b09010b12160909060308031905040201021c12061202 73
    0x325000f074680740c1144d90900c000c0d61510184d56003c03071f45940b98040391003d0000520000c40490400d1020303010151041000c8001075045013801509903407030740d07030b180c82c00300c00030000c0400101c011585a40180d40a400500c040c40e44100d0124501400340c01420b00312030100d0560b031100b800d0f5801e80c1c0a81c1100c42284140751a00c01c0200b0a00b07114003c050065000000810040c1400424194003044401069201c03000c2e407a10345043e684410900e4001d0181400140328034906503010756044030402d0710402201c4d2255481170007044051040c8140c040c0d0340032a00386c0e000020f0141c0008901c0121300b03030790303038503181c0c5400340007415640c55440c000d10701d49001140b4802840c1c12940d10482c4690075000f2541c4611284c506010800b0303c800c10013000c0074000034800100e00940001d07520400d950b5031a403410345002c9481281030600b030b030f0a030350404d800d000160341c0106445882e04c404031040c442994140c802541c0070f40048000b00213203441c040c1c0010310001c41c00c01300b40c0454800c45070440 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 164835701 1250 164834451 164834489
    0x2218050a0606110a170409060b0a0801060201020a1704050705040c0c0c05191401030e0712020f0607020d14031c0603050f06070207050d05160305030715020412060203090a0609030207 80
    0x1d004071443c64001420303400040c010f00407071100241107400b080045042840c2c19125a080c00c00d86c1d142d54016451a2008203c8444854000d880303140500007902c02141010100c0000520700510744600e070700e034400e034000400d0612500344180d03000b070701c0301130010700c150b08005100a103441140c600683c0c989031500004551031600c3d03060180003c2450140da460181018401c007005e10000e41d68505140e580d600d08100d1007014003040e0f00808411680c164020380c1801072041101c031802005106010420519005a0b1a69036610a041c1c20002c05149069001c0f2007514511814421200111881843c1401a5010b4121200b900d00c82c0013078600d2401c2160640c4d658100a407004d03000343c0c0140d0300038450350a2281900495900400c21200e0101806a0320740a80c8066042039403940c10000e110824040140c003254206103807468210720b45032030007038015009a0b5a4000401542e00080840c0c054401000031051a507004807007000101b0703007450080e503114031921070105604500101d01ea = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 164836951 1250 164835701 164835707
    0x6040f02100e060d0c26160305041a060303070f060c120218010311070206030c0a090803160f0f02040c09031202070806160207380306062218050a0606 66
    0x24000d40e000d0411130030103003003221401c0502000b00c014030030045c1c01040c0a0002200c1d00000d103425211034202d1a032030409814030700d10b4040b00000d803000d150410342800009690042064580140c40040c5803d64440a001a0862040080140100c40300310100c5080c0015640003c19084094031141042c2d400c02c7c001000ba030007807420f80c0c0c0707000c00d08081c0c4e100f0550003600034030010808075034000c1c540445940054815001940c9241ba81d080218032017034110703001b101110141c442c0d60002c0d410259013504074000d00b02517500003400c3c036082e03614040400c44800e034101c100d258020300c18000741e00c0200004018490920051300c1205c441060b00100c1400418158241ea8001c2e01070862a80e414002c42c0304c4030f02d400034000440c400d20380700040880d03686450807443c00240003040c4440010080001108814aa1940709004100b051100341d940705001c980d50b500099102035000740b1480403400810131650720071512605c049202e0750701340740c1c650300c21803196102003020883d068a0b41022 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 164838201 1250 164836951 164836967
    0xc0a0e0d02060304021203040b0a1205090f0601060e0a090906022706041406211504050732031009050108030a05040b1b0715120e0c0f0406030506040f0210 68
    0x42e400400400214002d030400d6007460f4548083d4038100d0f8641541d0308998444c646c81011110300090b5a00400101c00500c0d004458000207194014519107081c0c194454480f00184503440070310204105011040d20f50fa2085801000310b030a081080200d50f0410034069440040360703000165581d1003000305200c01850041007800302410581c00e10341409944030107041d0600300254005020310071502000041c060107150f2881d4400400d46500f070010340c440d520324000500b90300c203604020801c068141e0004045c100d031078110108448a84d0401401c00a46001104400d50848c0000400c4504803500d403040c4110780b2011070800c0542c0c1c0c2e540c4565260300801c3c0c6000000b6208100c1000303019040c0010300450320180e11a0724041241d0909030349842c0d62a84180c503a040600a503c42507500648141c0c082107011000384500d62507511000c0d1161a01e40810344144111010401075031610381c00740000e50f5211040355100d08081c00c010080000c0312a04a02c52421000b85a400030303c074100e2 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 164839451 1250 164838201 164838203
    0x507061b09080f070b0a0f03060b04030f0b010e070c030305181e0c0402070f030f11010207060603030f0c020a060503090f06090a05010e150424020a080604060611330c0a0e0d 76
    0x5c0d0a041001e0000225203c00c80f40c0e100f001003684519020402c0710018006100461088100489440141c81e0030002c014050380324090030420101004001c9411920101c0310325410703e00050a035403500c035540340350f00c10300358000304911501c1c030b117070100e084403a440c40480340c4200102c5612a0701c00040100345d03c13a80900910006407104ca81c40028080d60441c14100b01a00f2701144000f0202000c1d422608501002d85645444800400a041e00617030f07440c4503041945030400300c440d050b80104170307003084500c510810171034004005038900c101840503900c049144400e803200c500340302d81c250350388600d01c18082e43d01c3d5103050089501554001060075080300e448844810710781d12a00c803100300440c5040c0c0025079055815040421851503c010220000f0a4550310307581d0614600344000c588064002c82c2c24800c0c03506404008580004160304203e6800b01c200c403040c600c503004509801050344171682c08814043c24450b0f21511800039154210440e81c8280404203800b04100b150312030150 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 164840701 1250 164839451 164839469
    0x4031b030c060209010504031202210309061314010c0905030f060115030908090603040501050a06050907020307150605092a090616020d05060705070203070e0c03070507061b09080f07 80
    0x20700d210000346681c02401d400c03407050400504250703581c1ca07a000e60161402403040160000e01d0050100c41002d64050f088401c601d010701d0440c074180500319581c40300588964440105101603004110340f0009002c2c84035014002803140040c010006840c6440da4005d141c4a8028803940f202d40c07a10000e2024122a460100d0001c00d8140a1003034004048000c801d80b00c00100700700c05140340d140d00c0021800ba43c401c50000849241c41d0070791604841c421307040036104e94400d90911803020344c000169034440383c11100c42c0c12a9282d0000010080c442c4c0d600c11a0401ba5050401040c0d8440301c1c3c1e4408190400c089a1107130a000d440280b40600c0740c01d108641c000000c0c80b940d0350300c807030a0441c0c41c046440600444806903564031060b00e4401c0454540e40010400240350b41181410300280c030081c0101c00c401050750030118110070950000400110130010b011a0060905c02da80d0090305250242c0d88400410030751440c001414240140070310000f134401c0344502010b09d44006a07850494130400 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 164841951 1250 164840701 164840717
    0x1a0c060618010e04050a020904080307030b03070e150d0c03030806030f0a020904030f050d0f052d221a0618041104050c0d0204080f070b0f0313060e06040b04031b03 72
    0x90f141c40c2e101500540740740c4206015003006032503040c40c0d680100d004441082d1a45004007004040d11950f86089010342c200c0d0904002104804140980000d883c005c400000307900307003022605002c0802d60142c2544a00d540000906810030b01c2e03a40140d000303400fa1401d00882e113030840e65819209030001c0d00a0403100014004c60710640d40000c8100079480c00c01d1414401c060a10103071201040c219000503070360300600c40d6032641800103080c2400c20710038607408410395541d8001c40380d0b0001c1680800c441041580880303412451044501d440c0d100c8501c55500580011211040340c080703408a029540e0729959040c55000d00c0000341c8900e60050300700341e0500c100024400034082c00380c1140c440c040300340109072400542d4000750018250440040c2166640c4603025480c0c2080c0f5409502820130400540c0784121000040f40e0784120855407050103000710f8a0b00d41c1c01881c01d0203403141d803806080144010403000300c038003070b020701d019642c0c050000034040c1519092012041d0f00401040301a = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 164843201 1250 164841951 164841959
    0x70c051005060f030f011b0311031602010207080a18050904020f010c05070906030b0a0f0605060a05090a1a03100b032202180705030109050109060522061a0c06061801 73
    0x150300500d81c072402c060540503540c402040070a2411890280004c0140d4603000d05180f840020302000c5a0710790a0300c1c0034000c5240b010381d043c04503c0701038140d1403441150004445003c2c000d40440e280c1950003c150756075100766100013802c030b2842c42517101d1124048140014546003155a581c0100e030001c210b000c105031910010340b80f1094a10088556001b01c90002a5140e5640f00700320055009015040c2e06292514071034044400d04075014121600c5c2070800d02c0341c2d488610640f0141c48003810500d549810420010b08040c000742e011484035280500d1000e029003012016500031007000c43c080548070b84582c01d52030907000841c3c18100000c0c20a42190403501c844010200050000c1e054504000980c5515249144100c0319980441c80c00801009069141d06c1020700401403a041002a0b03030801d07000403e010144001c413004020401211109041d159210000070040e625000400310742c10f400192064000b04000f42c0b11f40110380001c3c2c46801c04502c600441d50441ca9003d5a43e828 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 164844451 1250 164843201 164843233
    0x4112e05130b07150204060201020a0201050a1406101e0f120606020c040f0b0603040b0403020601092c0c131d0613020d0c0317030a05070f02061b0c01020d0209030105070c05 76
    0xf1016095074004418042e210280c1110710050001d46099800507035507500e14000a401c0d00c034060302c00c0c00e0307044c54000205180200380f0316560b04641c00700c03085500b60107401011600c0c185048691400513000ca01c0301c0c05c60300c0c1c00172005020644a81c9401c1c05e00040b02c8040e1080b260303684a0b040260308424440d400300d2420b5030003091800f013011720018101c1050408107480e6003040720112284856030082c8810306404008260050803030150521030190f0307081c052008900c41040c00d002840209940030016003040c4002c030200e12000d0801422280c41c1c11001000e4070ba90204024051003403020204d1100010800c144a0700c0030610440001c88a603081c0080030708040801d40d1000c0d031600012000030703004000c504440c0038072907030303c1c0c0c907412302c49031b203070205c50000d00382c0703c10b0200507480d9030403aa4010800e0390348a65200304c20180301025040100c40c1e445030324241e00e615480058014400311456001e8000780d04140c008210668070204142d80c101c0074400090300c9940041004410080 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 164845701 1250 164844451 164844457
    0x1d09010516030c0903170d2d0902060903010507090e0a0b010203160f0c03110405070e010f030e0124030507060c0201050d0504060b0d0b06090f0606040e04112e05130b 73
    0x1c014134048801690301d846401c0c21000d03024184c8013950700000e000e50f003910305009418000508004503003481306002203603003104050003041c00d9601d4903100c0e41c0041d5903c004c00c1c0da41e0003102038024082407903c3c49000700304003a18041c0d0a00360140b000030682076007041c13040c1c240369181a0002c41c070b04035090201d40a80b20181801721560508115004000340750386824200451180c000220303403051100411054400040c4407804008168860120a07a4000039002036a02c82e82000134000c031f106041396000d0300c140c038141c1d00040c00d120034200740901d800c1170f00300072079005070142c410442d11120300301c40890441001a0006505100000b14000075500444e0441c0c8501701c0042c12001c4940851001c8050075815510300d0224030411045007010300301030741d10003a58158401207251400000e0b481e80624020a844092104006010045420b2940c0c40940e0001c10340c009240c010100501c009941002c0c00b5140b8030318406c040c3d4202d000e41d00b55208003403200712200d0102d0030b00052003940d030 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 164846951 1250 164845701 164845721
    0x9033108030c161d04030e030109050106271107030503280b040c080f010b0901020a08070807120c050a1103010b0406080c01090509060a0303080705131d0901051603 72
    0x10040240080d44420400050004061076005003c020303201c5114101c0b011181c0d40f24660583d442c04d24003103281e191610041d4499410b0411004416118012900410341840d00a08541c640200858120b01000c000c20406007035004500c0003d208591031004d46030704010a0150312402c4c0800380c0028000c80c05143d002d00b00010071892020f8180ca803d44404801c000328182964540043d619030a290240c01c0b150450f80c10711481e80d0410481240d400c4105101c1c030440f5690101d00e5440e581e04c05d00240d82c0640e00f09512681f20202400d041d80103502c07024044030500d019144804085000b201288a5240c1000203007500d0122903e0b110401c0d0040c00c09550305540e40c40d68051140d5540c4a00c101400ea810000d00e10b42290030009003440815800c041d10801c1d941c001c00296507a04081e0900381d075414981082d094654203030640c2e550054100b0110b19440e44400401c100700e07010140101884903c07802c01e41c0b03440341040c403400c80c0c005503030004c100c03a04d54072070403030795402900605081 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 164848201 1250 164846951 164847037
    0x50a0f030605130f0c0906090b10050a030b03061e010503150408030a060806070903060b030f0309120114041103100207081605100f0204050906100f0315051c0302060903 74
    0x4081e540d0721304554101e1080e0440f02d4480c1c1c0141480a5032051080700c0183c14044410400010301c80c0010f911070501150000c10014000741d40000e2601c80c0e0003625410101500b110381c24104840c09800c2c01d130002c07441d400c40b4106500006298600003840c030300d10340d003085401e1a844d10f6544601c01c01d81d100900107c0681d071100070003c1c00d620100101d5200709001d9841110550031468540c1c140c4080b021040d20a601c46040c1031100407000c005c0301d440c103204480081000c6403206009000d4100c0900081c007102c480802c0006201451052a040407821403d03200000100545141203010b00360015210500078402c0329040003603044101c00890140b4100e4008800e07002688040da030b1446040c65482e60046410040e03818541070080d0440400c80d42d48507000800c00d0700401d40402c032014a8100b689a0110220445644a940e070140c880542540e0800c0c08800c800701800c085600b00702c0c010300c56100022045513000c0107680d6069040400c10101c15403000300800c0c1280c0e6007000c1821 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 164849451 1250 164848201 164848231
    0x5012d062d050c0f0d050901080406060906080a03020601120305030114220c03050603070308120a0204090f020703021b091602150f04020102060f0c0906070809031b0a050a0f030605 79
    0x10260011007a00462546030358490791580c049145a0404043d96510300740c0e0f40c40040300028480d005400e0b1103030f0344020b01e80100c003980c46081900c0904850b502003c1e074585000004525454082035100c410b50003078088800300c1e40d84101d0b0090480c04020040c000030360038030050044520240030030202d03c02c01028002044040482e2100324409400350300e451943e515281e80740d05425014550b8010f504801400b00140f941d02e99450601c134400780145480602400141a00d031994161005440e0345001007000e6800b500e00c0000030740c04450140c01502c100810070321400913401001011400c007900a4040d9158a80364114844409040c0b00a500810b00003411540c0c1001c8100e10906e03404166020750f0500d0300001e810054042c00c85400e4040c8a0304000400c1c0e82a0210345002205403107440d07507035640d810030060f40c7c014140c00b95490f0140c0012030140c0241980e02c115011000c45020400c907a9503810000c01c800103201d030041c005032140040021408950125034001c80b00350741889 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 164850701 1250 164849451 164849507
    0x30a0503041212060f0906090209030c040509070806040b04030305060607020a2c04050d0324140111100606020c0d030e0d020a030503130812071a0403050409020d05012d06 75
    0x240c58517034201201140144504024107400c50066800424802000314030b41448400401d07190f00d14496102e01558030f07840071a00031081007111400804040d800d80d0500d0806d40b41400c00f171542900d05a00003802c1c40c0200742c540c40c155080b02d120541c02002d00c2c01841c0340021500a080c01c040e10074805100aa580703184106003411020f100b18891005009011a50800507040b558000410300d0f40386100f2601c96980001d003000340c0c054484040188111506c41c60048402011340b0409500b107000d0072600700040ca00da074002c4401e80e0025001d5480c0c80d00300009010020320075a001400241440398a02c60b24200707060b02c130724182e00140104203815200d8548510315408800d03101305c0211445010080c0d2a8203000e07221542e803041f80700c9803610990352200550103810320044044e6100c1000817404042c06503045400910440b081517460b15002844a00142424418141d2040b0141000700c1c0c0d81c0384100121909001000411a1050410300c040350007820700c110450203c091a20a81 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 164851951 1250 164850701 164850737
    0x71202120c01060306051b0706020304020f28063f0207080c010f152303010c23070302120307032702040e07030305030a0e0a06060e18030a05030412 65
    0x105a06028070004900d15284d0702d0100102e50001b068071141c450f8180c140181010765000712419903811400250302d946460000941c0b40d207510b8017455112078207501c441e0100e1600e0368062103c0c00c0c01c4105420040c1d45a0050301c8607004140e0302c4560742181400d040c0d03e09020400e402d201826000b101003c0d84078a040241241e00c044403c0c0c03807030b4031b0120f44100740d040700b40140300c200d115480040c4070350740c1e041440c07800052160007090300441e0f1861640d959469050f440801184004009100c02c40145002403c010b0f000362420101c40420342040e260000c003001241c2e01154144d000f082881e1101070384411680020701501c0801d61500303e18184811001c42504901c000070004070324006c0a44108011114001158043d81d000601c0800119410505603940309800407400300d215906d00c1d60403401d007405158002c000c5443c004011440143c408040d07442640d501e0701c035041c101400001255240901241e13071000603400c100107400110100c045070410091810b040500405200c04a = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 164853201 1250 164851951 164851957
    0x1030c0509012006010905090d110a0201050307030f06090b010e040b21030c0a0302010f06050414060103150f03050604110111060105060f040e0a090c170304031e050706020a030e0108010b07120212 86
    0x4030310010349031f0f401e0050440092000c200520341c10b04100c841e0482d080703446600d1303941000e40641403220103c002a40c15010342c1141d0b050074030a003000c1220b19103924240000706500010b050004504842d5103030141414030920002000081c04651506010100001c4854941c40c45c42c2080c04188106400400100030400c10350784240c001007418040e00a030a4100c4585500144c0700e18200075905014a16081c001c80c1c0020b008c0c40d001c1140c91080341c2081c108001360384016104002e1003c0001070000110320f042c0954410303a0b2144ca08038000004596274080c00103070400c04d8108100410075032030400c0042907606080c0305c4250910381c2e60440800302c0d003000c60b0064161511074003280700b00100b0790fa030100681110316000d82020303200c194484d543c0c091804018440d038011030100401c021640080303d541c60b0301a0860300701940310f1100a444604600741280847c455080c074140647c0920b88642c182d0b010000d10701d0406030315440b6010500c40400a000646c0207040440f8544a020001 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 164854451 1250 164853201 164853209
    0x917010c05180f0d050303011a090d060b04020c030a0c05010b04050609160309020d0605070206060402211504060b1b0303060d0f020d120e01140c0303190621020f01030c050901200601 80
    0x950748940c5007012680b0440270414682d181044200090a487d648410540881c183c00c001c00003541908040428000c0c46640038050140c40041031a620455200354180b120a11402c000d00241200c00b050100b518003d440b0b07554001e0200c0001510016a1089441041e0403407802003500c052a80210b0381d40301c001c0a007910101c4d00c0b68100300f021501040020317040708042d80c0440c80c0c0301080402001c4400f044062005905082001c00c41036a022030491490701d200510070041035640307481d03242107540414100254030754140101c8491a0000c41070380c1c86004050190350019a0560390324060b209a41d608980c000001c16601c4045039411108505a00780c0e51180301704290000300144c40150b54642141c000c40c0f00300804c100340341000c130969801800c560310f6072040144642d00302d4050301c01034004103902d10400418562400311807454100ae43c1c000e55000340c0c041130850044040d0741c2c02c10140700c0803900401451015500c81c82c41410980007400c03c5941e52040310028500300707402a80 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 164855701 1250 164854451 164854453
    0x70b031009050f04030e031c03090203030f0301080c100f0c0b06040f0c0201021c0902100509011403070201050403030b03010515060912070806070f02060108070b031905070917010c05180f0d05 84
    0x4004c205904071603000201c10049000300340940e01901800890000c0704108420140c9440180d011500e0801c01d40310014181840152a9a1200076240c0d88001da40c020520070215990710b458400e0084640c1114840310b07641d0aa01c0c451161070701542481c018042d81e401070341e2512420400e1026115110320403070254001f40e9680b02c21400e464685443d004171032041031400349848010303a03410000d0324040c0c1060800d02c0d102d11080c401030b12001d003211081445181c002041024040c1c1c19482a0b01c52031280e10108100850401030500301c07101282c0b81129180d2a000c2404e051405001070801c0000041c0b40c20558080ca41100c0c2c10490264805840e07942301c1014442d0039504410005a80115440100003d40c94014659a10f101d40d201f8401c10202c000b0106880d55880c50070f80c811a400e0050030b0140d410900b01c020260300b01481444000702c0000688001900f06000d44c81700301d0042d0b40c809062866400c20408160304500350301d0360240103002a12610b03242d640300380c0caa59004074 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 164856951 1250 164855701 164855731
    0x3131e02030321010b042303011d0c0114041d0c0c0109060b09060d020105030c03060307050a0b070c0f0609170c27061f0503090a0206030a06090617070b03100905 71
    0x2182e00100e5045e040556000030900c001e200c104141c40026110b03420b4003080c2805c1c2c40700b200c086230042c6a00442414984c5480411544020000071003403018030080c1d841482c041c1d07940c58000400d00641c001d0340c0c0d80c1e00d10090010b43e40024031802c0c50304090300399000744c034280800f1101d40c03c41d050344900b1500181c075524122828500104101c2d40074500b03a03403561503000c00342d000810320721000b030076031483c4080840840c016071000c104001c041c04020b00001c0d01c1c10744079192520107800442c1d048800004120b004110b41122481800440d4803d895030702c00340f81000301018040b041c1315641c12640c4608800320b0b20a90300c05481502c143c00b2404005c108507459010151100c90080c05035018410422a4552003514101e140c4806400e91034000d03100d0700c0f40c041e91070400c101400f010b988182c011092090004e01e50b4469011118030300010410181d80d004c18a030010000d81a620031074000540c100f101e4900e4000640d807084034030854425441d01d034042e1004451060701c006082d0000c00c = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 164858201 1250 164856951 164856997
    0x15010201181106160f0c0e1305070b070510050f04150b0d0f23010509150907030305070c080a0302011b03140114040608030309060709060503131e020303 67
    0xa104168140c21008030845041c4400e880b00351505480140d214040e480c00a613200000e80d5201404451581c02001850060018180640d0b054198000d02c00041c002001042e6030780c8048009000d2a944100a00982890600025896084010103442034000c0c092104584051489035501c41c0c01d105916400606250500c2048140c9180c84402d91901e484507502d5166200159040b86c2a07200300d800d0b04490580c03803e24640740c05103143c1c655100011802c003001500642205118200700c0d4101e92180e4641028020021010f6420a065400246051000c01d10500c000c11607980141021032009584d0180c944c44e10034400030a82c01070f55540300c25070319070041e44500440380d0014607060003070481d0081d08082c2003c2c188140b060384948111910481d440700c1d0003980007020f41c0e0b015691646450b0b003880e0340758a021505034002800b50341e00491014000e0060707074060880e505040c40c48203955070b03452403140380102c070003100c81c80002c10000050780e08000428540080071450511f064007 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 164859451 1250 164858201 164858203
    0x40308010f060503160c050f010b120c01051207020c0915090a0e06070309021c0803010915060230040b0a020d020721022103041a03152106150102 64
    0x206800044841000c00360400c100340c0c0c01815a5000190544051410300d12280e058a040821080003040e9000b0b11002e0902c40d40103501c070f01039413101034500961008100c0b6841d920307400b00100b101c0c00708100b0f0002c400d1684007c8222540070009004a4800828080000380b821004443c40c00b0a0702c0743c800c15a90a04201b84996001500f1100a1002c0c60304400381e2520307031400030000c504040d0b480b082001999110394096038050071551507101110b6160505880035442405203010060402c402500d0410440078071104440312a030250101b50819008140c0c0ca00007000c9404042410768090700c0e482d2a003034001c00003000ca15401641c7c854400750041c8c02c24030748000d010155000b40000f008507010940c1d0b04030038079440c09101c00580b0400e10000d05420b00b0030000c000c0c05040540558100d00000000b03100751401140b036140d140300c04030580040381c0700440d0001c94815a52601d8562800e11820741c0710000070380c0c440c10001c0150030b503850345400fa0840d6002015103048400030500d5070 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 164860701 1250 164859451 164859467
    0xc0c0e160201140411010e010314071d030a02030a0807060e1f0c0806091303112401140105040302091503100605010e010203030405030703080c07120c03080f090618030f120403 77
    0x8106030f890620f038642a00c5100c01c4070000e04181c2e062040104a0356040d030311036480b010248441181400041c20302e03110007060442070440031281454401b051050502d800100e02e6001e9500500030426041c45556070b110941001e0750865029403244038003040c07132100340423149501501c41aa04c0860002001d040140d8403842000c20902000909110482c1c582030310080e07001c1312500300c01d2140310640c45e040326424620105090640100e1040c40c0741c00302ca015800b6003c20516500c042d00703980791444010301782c05406459012450803c8204010705141100560200010711510f9001d03039410042401e2408060052a1465481c04d080c00907681119000d900300348207200450852a055891540d203124803980a402e101c0d005000603001c0e40c1e020225009103034080e80091021503050009050f00c071041c0f8080f0003050000c0004ac05141444292510803006a8020441030b00d841149040403030207000c818142c0d0100300b2400c41400784e0710300204a0341b072002c2d180203118605403c2c0288441 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 164861951 1250 164860701 164860721
    0x7020d24141b0a0909060f06110712060902010c0b0a270201120902032b0e040516031a15031b0720030a0b1f0f05060a0c0c0e160201 58
    0x4039940c24030404011502c0780c04030700310703680380b01e0b035914031004a055691050591013540110300741680403510291020801d4101d07100c03900d0700c00d2514811030380f4544820785809883c0307019614488030382c00f0840903040690340302c1c0103050032200e0408a0b00c6031040403204541c00c2c0e651903114034101d159004609405420f1041c085400c0002c100d60740e00003000c076202401005036071520380e00200d0940d03a05000108091004102e09020880d150400803854014a40c1c0140032a401e070100e40354908042c05801c1c810080b00202000b01b962240c1c0640080004005a12030b900c1c40000e844020b45071510302c0089040010001f94888c070300707400c3d13070f1481504041540364034050038000040001c01c19161042802e421100c8111250100e03400700c0e140c2400c494003d04800401d03828005107100001d071180b003503400030340340c1d68503c1d0326104049060b034113510440760020001c00200078414031a4600c0302040f03201302029008645d984401c00c04800007560010024060204e00724055902441006620 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 164863201 1250 164861951 164861981
    0x12080c041a03060f031906020c12070320010b0906060d060b03090304031b0302090115020a06020706051509010807062d0302090a1409070509010c0c060f0e0402040b0f07020d24 77
    0x6c40c15401e0324001d024101607005040580115264098044c00e22103030000c1601c2514a50b00c441041c103005007206a044100c110b555403810203810a06010700a03c103092401500900041d101c400034003480b58800071043c1e200c507640741d10101c1d084203210000c42c00703140803000640e01e960071410202d0140c0003604111042424801c410030040c0c071656421411503c42c03425541a200c07402405030b042c1902c161000700118400544c510806c071584c2e019174011000404500b00303080440c828402502c4003800340781155404040100301c060300c100140510340c02c05280142000d461140d0f1000c84d01c0810fa001404030b038000c124200141014600007000341104605c080d0f1241402e008155070140c040c000f2000c008001031803540326400350110200859100c10008601a03507000c0080c645481141100000b580c2c18440b0402441c00b4002c0e00e06540e04400d0715403408208030107080c150b030b10070001207070004d0f80d0b4916040407420301039405200041c0c450b007841c540c3c03240c2c111042c11143c02c10854509 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 164864451 1250 164863201 164863213
    0xc100509031b06190e0703080a0c0b0c070b190e1603031701030c090c0e130501030b07021b09151203031f0605270607110f01030912080c041a03060f03 66
    0x99840840350400d080c4041c0c800080c40000f645c142810022160000303050441d000a424800c0c550000c440c0005600400300c0b440d02c1c2e164810740c0e140c240708041001c0c29524500740171071202012540b5000c0211007e400003d40f20130101c000e10308146c6010f01c00880c000d8008001c105168110003420402c40503403140841c60360640d502c88484c083d50340540c0212603074504d0312032025401202042d0341c0d240018414040b5081c908242c2c00a00024041144e0513082c050200c0c1802e40002584041400ca00144904201180c41800486500100016044021010000780075144d10801518550203c00510b03900d151084196140195850030070f15007410070b003410042d8a034000c095801d840c5040c01498501c2c000c80300c82040c4100741c03a100c0c95114030001080e03800c22040d40820b021340b20303080e28184251b01c840300064007201d0070740501500c01c00140064804941c4141861580700c8458a4420701b4039440380d0003001034003940c03441208000030001c24400d00c2d1510036165014400f0850003004 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 164865701 1250 164864451 164864461
    0x105040b0303070615050d050102090a080304052115040b090f0d05070303050a0e011e0510150c030338030d0504180902030109050a0c0e060906060c100509031b06 71
    0x6503910a03c240501400d9503240c3d11507801c503091313080c9001848003d1100f18800710700d080042c000d50200c1400f500c500e0440d840024440d6012040e40d0031250018145420406142c000090341c030b41c80b80c055003541c00352480390030a2600c0b4998182c0030b04e0207138082032554900200c02d42d00d81035500d051044a548090340c0e800c41940d00c4400c84011a525250105041e12020f03401d03006400302c40c0d19071200b5400c1504a0f40b03200c0c2001082c180c1514888410b00440d2a03005040a43c507146000d09420750082494070f9603114040c8882d4545c0341e119181c0022016420481c0882100d5054202069484941005101c400450070214003088007180074243e10110044098414403440c414401c01c41d481c8a020442c101c0030b64020340030307141c000d0028032500c040d03850000e4a40c991528100c2c0c00c040da5a801045450344000442c0c400c40000d0121522a00d6160400495030001000020329200ba104d007035070b03800c0740f902032a4003c81d03518000750380315005170034030070700c20040454105095032080c42049 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 164866951 1250 164865701 164865703
    0x80121050a050a080307030b150703050c1e06010302010e010201180209091e0309010207060f02070303030504140d08090c0d0c05090601020313060e030d030605010c02011206081b090105040b03 84
    0x204a41050854602489046203403003401c0c07002191010b801030144980000a214624000314441d14071990200281c8040c9010091441d021060116041034140009000a40904001e11885851000701c1d000ba490581e0b10451082885802501d95000070004100310b58025083c020202024002400b61600040e202c509194404401900c50300142021414850003401a41030021042030075001200104a941e40d40381d1040105a00510030707110000b80c00c920421003034181000540c060b201084c610f880403030240c04042c01c1035400b00a0220001400c200400a07525106c0c03e944904d4082d00d00800003e041181d980c1b207690284801b03144c0400003a4251003208141d820848201d41c00352641c50040349180900001d901402801740c0012464507086905d50703c0c0c006046049407002c0b0ac20a030114181c070304510402e408669800440d0340158080c008156440340b401d01d0029403180e4030101e05180c0b9003100341111038810380302013240341ca06000300d0550141206644c00c4c03046514882c086 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 164868201 1250 164866951 164866979
    0x20904060b011101111e0301180c05040b1210060305091905100c0c11041a060c010f021603081e0606030408070512091e01050f0d0204090c09150801 65
    0x388080c1d6a6601008241c1c082d01c2e0004000e501c0d00300070800035440515840c5a503004404204001407400f07080d011a02c58a0103c90681d0043c0440218604e00c2c0c04040c00940091042d80d01841018040420100c0e88007000e090841c56903201c0782420700f05180c00003003040d0660000010181007004010b40030303000141c0c0300200c903a40c02c213a41059000e410010b040c411050007001819003030944510007664020f81484805016100c48001120f014003040100c0702422503454640c0c821345030001080c03034020b0141c49100c9250780081400c0e8007499414080740c0c001c070810b07482c02c16031007482380c18035038030500c3d090b801424020b901c1034414421049140f02710000b171400d88590300c000001410001064241c44080c0d50007012940a000c0c030341010300d003582040c040280074110700c1d400107180900e03220802c0300d01340c4180c680030300d0044264080c160607400f8000c098103080d002c0000140c02c035418400c43c2400710540ea904070b1315604000e000708000200c10321040810030301c10018000d00c0d8110040e = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 164869451 1250 164868201 164868203
    0x130804150905040f090201020f03210402010c050d08010f0f080c060703091208090f240313151505180105060706060305030c28080409050901060e0915010909020904 72
    0x40104612112141210760300c0700390300900e8100d030030f2080700f4902c0d90081e00b002010714130076001d6541e28074408080583e03e000d5038490b800e03650741590060b1040b0100702070090f0080d0040c5000039100070307140c447d18684041c07040030714001403c01004104032504c2d184070710b001e132034546554104140742a1205958002d80b4590a1080c040024140c0406014132541c070020100010549040d140130704000b1042d80100748520300410132034001d202145880f01074901d041851140b14203a4164011a12006030401000703400c0300d003041c40042c0e0124103201528200044561030228480c8440d2104400312203c0c0d6000da03008080c1c0d8080e10084010358142c0c6419502e0980b03e458807000c0b1410020044d10b2142c2c0007402c18000002c801c0d88281c80070600c0310801c44640004103a000030800001c0300c1081e03415016010080600c004e00a030031058110580101c091000803415503240c0e111822001415134518030568007102c2c4000e8000e0710404a08e0042023425010002d480580e00403900342440144 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 164870701 1250 164869451 164869469
    0x5030c030709050307090e07050a081507021e1c030203010f120f060c050a031b0e04180c170709180204020703090803031503100506030d0c0302190303020a08130804 72
    0x40040e1090b8460785410006100003002c55070260f40d0341e40c1c2e040003880d000350038038200d00900c200490700d0309040340710340f0848180c0c000900580b400071413804002c0c00043c03d660214060203030300e04215200080c100405601810141038040e881c0110700401c000b03541046418140140300410581c854100860b0440c3c10014400303c590070703c8d01d0641c0b20450354180040106180c0f0307940401c2c1d240d1004c040d21101546441c02c106594160107a0001c0504030700410b0b00042c10405402441d08164001112408004000c010142000d0b81c510140407a1904101d1110350540000240658200a900001c0c1001ea0f4104000d020b4126246800d01449102034041ca800056090406104501800c001e00702c020940e6200d046c000502004842c035080c0003403092064081841000e54184a0913000750780090040607000070020f026640c0b000d0140054055001d140304605031b0688800c54100d100b4441d903001030f901c4130000c1024003201005400c044070712204044220000e01100e0407101038641140b = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 164871951 1250 164870701 164870707
    0x405060117040503040b0d1e060b04060c060603140d0807170403080606120108061911070f0206163f030e01060506130317120103062a0215090d05030c 66
    0xc1410f5295110702e0748141d0011600180000140c04c070ba601c07050903040040000c01e071008000d640a4241c802c107004083e0385030002c1004101c034600410301c20f80e820384a02c10110b42690384e502d035001c40320f203604106041c41c2c00c16481909407951000780c0e01e0780444203003800d4008804030244a0f9022200500c001d0600001c4408101c15545d10410355079910f004455818480da11250b800e503c44000391240c58940d22142045102c4d15005e00070703c14254403103843c4c0380c2011a0390304c9810400c895000180e80200c01041080901c41c201d01200054601400100d1821109040900200915407810b410810b0000040264a201203207040c0c0501c2c00307503d404180d5034007105080d4014951544141d901402c00225103c00901d183c070104126800b40c00e0900c41108035510023189071241c00c04240300311031100011320024189a008444a82c1c040344d0642c144205030722002c3c40d80c01840020703400341e886900a02c585603000200141c0c0a41c2680240c04c40c80030411000c0e0150201030300852100c2804 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 164873201 1250 164871951 164871953
    0x80d09020d05030705070f0b0c030306060d0b090c0703140703020c040f0e010608061603151502010207060614030c010f12020904090b040f06050601020a03050405010e0d0213021206040506011704 85
    0x800741c210000394100c4142c030f83d114810b1070310710b503240031070302c2110703104072621400140700048201034403480d0301d84001035442c690301d14007007045540c06008408205035a81104240607203030408054070074851807680c10340d24040e070308010382942c80300c0302101008201040402c000a40c049a4001100015140840d0210021107002b01400000f07900c07288640c03a2980000d4108000102c1707070b0083c0c0303200004003800c00c001c0c44103c083d80d00322068002001c10401d410080040c0091640d00b41e540c10303100040c2003071090b0b41d0b614240c904550182526209a04031310700e40f440d00b40b08044804009007080c122681d203070500034000411016145214030f9010400c1c4601d0348441c2c01075210280d111030255142c2c50306140030310848500e040300303442042c54100003e8041d40001800e5400c5038150b200c40d410980b0340001140c20410582d034a54100c22418074041c0140c4480c00302800142d1011030240c2c903455114066581e4480041c0010b1107242001c0c24400030342d030400c906007070f0440200c260305d6103a521 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 164874451 1250 164873201 164873209
    0xd050103031101060510120218090a020d150f0303110304030c06050712080403120b0d0f0503030f1005090103062a05090102010b0a030f060506180c1b0d02062403030c010902100804080d0902 83
    0xc09c0303230550003200810400c486074200360300420510820480c10020070781945040d02c012040d90003100c0c0da40320320017010b102080c043c0e02e903e0100700c0da040440345026103991b102d4507006003e038028408a81c01041502c100030307141c030a40b02d4290761403a1444991410313441c0240301c07000018640740b155680f0407000d03a003a112420500461a001f00030681c010400d840c003580d695004171907601c4101494804107061040305003507030044800041083c06140d085840b400300800c0514030640030700d6500215076080e010b841141510351642c036207405858074451000038ac2500c6030b4150561040344507103401e20006681c0001f00d50b190350007200009550351070502045045540c00310f0590202c2e100c00401580c0865400140310029002c00141940041e01c003815541e60200c441c2d950142e001304002520b02c401d900d01c510701f0001c501245850520118020908603030101150300243d94445031b41c0b1095041440d07200a40b0001e624112100c1e20300740d02d460500303001c1c0b201100541e544404012041d5a1 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 164875701 1250 164874451 164874487
    0x303270301060902031e060d0f031202070f0c06020d02031204140a021306030c09230702010605060a030e0105070e100c0c050603010e0f010e0705040303080c0d0501030311010605101202 81
    0xc641c41c070131540c0b801c202e102241042c200306031086114004500250b0302c0e0902840403c2c42c40d07405405400c61081e295025181502c2041500454035428003030f0310080f80b400507007100a1405084180240c6040500003400c00018030394031001c0d0b40c010401c6d0b110507181880e0351640300790440e0f0346581c03120011207401d0402c43c100720081d500ca080ca00d00c1d1584035801d07038080c5003181d00c11148040d00a0703407009070305d080d20000c4100900b0000c590349a500044800c040362030380720840c2d02c000100346032650002400340e00000f10b0980001e1b42c80d400385402040034450f46070004000c2c20301203520703982070b80000d80345040c803d02d05041000c10200b44041090881d0f01401501004042580325038545142042d00e060442e40902a050100c00001e1a0740303468030382d640070b0881661614075143c1551015544080040c0c58202113090802c02c210070340d5100d1165034081d40c0700c3d41d00c2003862405600c4c03040c2510560740203580f160300d01c09030440710207401c03499a101c0c90741d01d0f510240e1285c0c00d0305186a1059 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 164876951 1250 164875701 164875709
    0x11151b04080601090b0d080904020310030606090209120a080702010c1506140906090601090b090d0803070306151115090a02031b0a0b09090c1e0c01050411030327030106 74
    0x211021501241c00e441c0400ca09050b240c107600e00300100510503081000b071590796240904400720822100110713041640013160300030803201c4220021755990340d46004131141c0b540094031301c6a02080d01401c525060800040c034032202c0e00146041c02c09500c03410468491408024103200e43c00442034200880780c2c00b01d1004004008040007000d544840c00c0a50f010000c00c8a403081500303800042e0103140820f01540102c00603510303030011505040d0560300350b9100c50303413083d4041d140c2c400d80400034030184000c40c4039510030342d00800c43d90b20b0605030340d0044559040c00c0c800c0c864480408842d2001c0060b000d858090070b40003006103500c600320101d05004440a001e5018040c140650220b200c0208045840240545000c41000d90f64044003445028000680e0b6101220740c0c0031444450a200251803004031110030016040e004502c42c02c03c0c1c1d4403040c1c00d184c00e0b9440f08100001e000002801742c40142082d009580707000c0c2c8000300310203c0007000c504121900d441070313400c4e101c42c0c600f540018050 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 164878201 1250 164876951 164877001
    0x30c170405060f0108060f0402041e06260304030f0b06010c0f060603050d020304060c0602030702070f12020103050c070302100e1e100f1503030f03111b0d1115 70
    0xd0030035041854440d182100c0c03e072058031440000207a0036400040e443d1148403c4903907040c1e00d07207a075030801010307060203904202507181003c000d090300303543c91003500020304100321160019900607160344032049424200c81035640003403000308045280e22590000c80c40e84445002c1d401d40d102d100503185500786100180042100d5481d10080008903801304007928020300840356440f030345907005caa0301c2c071550044c3d0000502c4210a0070000300c4640281d9003042040c01034a21043e00d40070001c0072440c10f94407050703100c1c001004400c2556094880c151300449111280340c50301d05a070714040d40e513202403504072a132296661280300c0300348000c0c030480c225409041003100c4011440b00800b95a48015546080114a071074810f1449128a1150f5201c002041240300816480c545069a03e08002100d600904d40c540144940194520b001001617a03010701a5000100341c1c007000078a0600c1d18000c150078008100b95804540100280440c1840c12035901c0c000c2a40d00c5000816031a00042c2c144128 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 164879451 1250 164878201 164878247
    0x20a0e01080a020f030622060b03030c07030b13080919030501021303141c12060b040902040320090c0f07050a0b071e0807030e15040c090f1a01030c 65
    0x4240c0e804a0219401802101c94420740044d0358101034031500305403000107000340d8480e0044a406100e8107a60071007030055100180700316110300800d08560160701c1041740e81d00101400c2c020040c5003200300c0c0d00318500949440407071160703640d214031500c260400c140c4100c0903070303440302c2d142003110380c0f8000519071040c0255107400ba081348400412195000441d0088900b00550145003800940250844082403000c508500c24031815244407001541940d00c0c02c0e01d03204086201c10005004100601c1034882c0103035201d165041c03900504000d25070881c611000010a403410350764002d111500400210102a40c8103810303039076507410f2301c141c0c90020628043c03010300405112031030b4419440b460090b1140a1004181400d01c14a1300c03030b089003500480c440c41c020401c524840c0e4807190070401a07004480713131003080b4034040901540442d4200c44002c1d4203a424014400907005009040c080d0890034072100a041512140300622a1401070402d0359a808440c41a0301c102d40c0044030803e088420340e0 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 164880701 1250 164879451 164879459
    0x1020d06060819090b060d05120a020312060103020924040315150b030405150613020304051e03040f090207030c1a06030c09010302100c0311031305130621020a0e01 72
    0x2a02c00702e88001c0c0703c9041d01001c0e00a500c00d8040c038400e45502a60b801929035444040003071002d0480c005841d05d1003403020821040750310b6801000c0640d11500155142c0c2249403041c120300c0c00081030581058014047c0b0081900e80e07107101480141e012840403014060200e04c17075001c4c0a11360001c0c0c091030005280f00e107002003603030000c0241035100b00c801201d10345444907500c5c1840300b0b40d401849540b0161504480010601c41c031508290000d00715000d81400c5424402a40c00a076070070790312a081031068001845003007015404a201c400c0155007000c0c68122030418410041c4200050550005111810507108240e2959202d6110401d020103c0c00c140103000405411280b5601910500340000d569103402044541207941c020401c03140e90800d50409c03682684070304411411b0140b2083e286400b1b03501400600100860340389100805072608080203404d040304445030050602e011400d1100b0300c081044500440e04856181104102c940b001c50103c03405544894501190540049 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 164881951 1250 164880701 164880707
    0x30a1e02040308040f0807121101031404111002061b0306150a05030a111207030207110307060c0c0e07090b0711130914120306041503021203090102100b0303030c0c01020d0606 77
    0x8000d07582d20080c4c41c8140e46e11008140d030f645001d400b43c0030405120410300c1e0300051014065400251061402040420320340304100389118095404031548c040d81c0c0314080c11820444043c2c50300d25018070041030700d030404200303004450304e403410040801300c00040052940c2c0c50f0f03034406400301207881d00400c0c0d441c00ca1390f000403e50380060b00c0035000c442c14208050314190880d41600c80c0c1000b041603d54103500d6400301a0001d6120903011030700038106e00032141096a0920030300c0000c20494460075480344c014030b45000e01a0440e00304d0305004500c08207102c3e42d564441071020650304043c4c24655203074424100005c01800b1401d00740d0342304104500040c032a24182c0c0081300810710480d101e0000500e0043d1071901e031100801e201c1d240d41c0c0f0501c0011203619094204007007000d14107282407000c2c2c1e2030342c021034200342201318402c00c90340c4009035208940d41d041010754414080940200044040140065102c1c44050a00c00e84000081926201078200794110760b2030904030b001c2004495a55031001d = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 164883201 1250 164881951 164881957
    0x5071b06110f010504050c010f031503060501141e10050408061f050d05060708060112020c060105010e1801030206031b0a02070801110903030f0d090c030311010c0311030a1e02040308 80
    0x200c4034001c0241d02c0c0c60111050150030700440e48400039041c0c041e040780c011160060107025080c10942c5541d4205014241d0340c46d048041c41c0100130220300d43d0304120f4004100042c1010041c01440c1c0c1c00304041d240107007101c0000e500341c01251011400022402c003220701d40140d400c1a041401000180200011a603600605030a007030f40610b801290b031041002411001c0340c0d0041c003d90081000500c441b44521030b1181c2c410700505100b241f0050405a0604030703003104480340d94550105006007d20340e044003940c060040c0c1114040f542c0b0392180c042d14070240f01072000902802011003c0f8030340103101c80a2250480c04184059110710120400a5844c1e21910654200c1e5103414001103803840c2000448810306c1e406001545860f03400281d01e48180d1114441d119104d0f80ca0159800280c1c18146442c0150301030b039114001110309001c11800c40720f00c83d842d80c0c24503182405111340301c11100d01766580700c100003100048001201c1c40f0005803840f21000d000b48284001804000c011504c0c000d = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 164884451 1250 164883201 164883227
    0x60302090906040c0b090d03111009050102091305010b12090a0609060b0a0f0b1204060b030a05060708010b0301030b0403050901020c21160503061603020409090623040b0705071b06 79
    0x544c404c40f0755801d40424136104899003250000b11002c41c1c0400310303002e41809400540480308803440070100305202030407284510011141a5000a007041e103902d8444c4d041c8451001c00f400812455242500c0d80c00751348641c3c0006c0302105910400524250000d00c0a503031416041035040c08030300b000d49001c40c0140b0300c1c8028188250310110340400e03000014581c800584400c154131920300120300215100010000780101d4081303443c2d805104194501384841107646100f040249520300b40103101504006058001d400c0904041c001080031070a5001000e801541504107180da80b108000104d04000f0756440c0703075421800204c3e0100c08100e0038400054000c1c0e502d025581d41070f1700040c400c00801114031803194503910002c042017291816582100001080341001841c7c0780d40c510019040d502440e005039010f945da50484a084a03040c00783ea060080d03460703030704000e81c0752540d11a0315410b009800e5074100070011962000b008990716840090681d45c104044c2900c0d62000020132078000246 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 164885701 1250 164884451 164884463
    0xc08070c1d0a0902100c020607050307030504050a080a080d1e1b02010b2d06070605010b0403140a0f11150d0218010908100c12180308220605040606030209090604 71
    0x1000031080c0030b00b8803d0803000c41c0e0060601021110502c01110030f039000a90581e0b00c00c5c0300b0041000041e50810081650710322a880d1580c441d80742600700070310390240707900020054102030500d40c0000c0410341184d5101e0100680061518118000c8005003150002d026114524015003500001d40c40340201c0e9000f600c5900900c18075110710f05011201c03200380c03602c50b070440da9158503a24485640b0701c6030700305101c003408150406841703840c0e03103003515020380c84000f01a0002800b40705004180204c0b003c04055072004103080b1542c2c3d50390080030b115208018080f1628800c03241c8091f56040380768111040004201601d843c290500c2c2c400a6012000ca100000c103401040d038290350064410904480c8a0030182c501030398030020311405060580c0b1301c04200300944000d20109000b910034810f50a03003802180c0080d10a501e809064440e011707001c9500c0b10290301c035015070418482c0000403540d502c20804039090b1913601d402c9003e03204c1901700a51040d1380b601005180380000401da1f01c00c074003540c = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 164886951 1250 164885701 164885759
    0xb070c05030d03110405040e0313030308040b010b0705031b1002070803251407030e041407093204140c1201090501230307081e010509060907060c08070c 67
    0x45002e0302201c0e1303034031201c108401d400e1204104a00d0990301c600603103000c4d6002c0d01e142c1200f41010a06501c1990030403004603034154148410b1008600a00f4003410200e4051403806101d903c66540d64041c803405070303030540c030980c0c2c22010512081c00304640c0740070401002d548944840c509010b00e600100d418905603170744080d03840d02c0d4200364961038032940007a0f00c444108000d002000700d25548508829010700000c200030040c0c0703483c3c5201c0c620071a00036901c440e5040c1440c59000b0b1121076581d120311040300c174504140f40c4169810750544082d81002480e601c00c0c058150101d4042e040540070340c220500c400c010000c0c0b4281e1000280510101d00407004010b030780710070184080311800c0c000c178030100b165849030b040c003a0a006440f03403456000404a980460381c8100052405080c2e07090003003580c0340003125080c0b114090085540000601014280b546040d031881c60b521600c40c80f414040104074000c06061200d404101c072081c40c3c102102110664a840941451450903584031240724010307 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 164888201 1250 164886951 164886973
    0x10b04110301050123030a0518010624020106150915030504080417030903010c0210061202060306060319090c06080106081e07200a0203010b0102340b070c0503 70
    0x548034940c050320589420320304603401d02004555800d02d00c0345002681c107045001441c803c2c3c0002c042c500c01c580c20329010510349491800e4a00248640e020001076a041c1407083c0090341300190802401083c078603034405096141d02c400c034054240c0e9031108903091642c0c20f4080c0d08951201004040c0c42c035900402c0300f1480b03014400ca08881c0201e4010702003060610051043c0c807004004200c0140303403401241d04000318200040e08440c4103218030b00269100e800c0c000304001084c0511002042918400341c40c100158001c10b1403448020310f250722581001000440703a480140284207a001c041004200703c10307403480d0a050320341280c051800400c2821000080503889902c04500c51032091040d08182a2104246244004094204418400c4603035099840c0c206103a44503407074800031801459484100d0060508495145502c03504540250340200e40c2242102e00c000c00c500c0b107002d4003c02e000c0c102004002c6450203034100c80f2500c0c1e0006540814002200c21382400c1e02c8080302030b504c4581c40 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 164889451 1250 164888201 164888209
    0x3060903080903030f010b09060903030a02010603020901080c0a03060203040218010e010503011506120c03180605060907171501020c091e150f040e0a0206040b07030e1c1407050306010f08010b 84
    0x480c2d090031701806140040c40481d0001000d42a1000d0180080381030006200c0060300b5900030b855a0070040c0c0d581c120800075854801159070051a852000e4400e0744400c0380803401c200e40f00d00026121980000204d0110345074032120b405001d114203400400d40d61195030a02c2d108900388039480c400d600303004868181c201d400408404175a021384840d0ba030303d1074008480000c1c210003440c0909242c0d4900d0100c1200c00341c11207030710003184511000599850a04100a1f0003c0040c00c440304000080c5803904ca0b0604110b83c440e00088074038280d002c00003844d00100d20780074074541015080001d0f2401d00810390254001d1100390a001d4040c0042d40d5181100403d00c0014480c0c2c4d6648050301c5001c41180341080d500034806e4414500540352031081b25000305070780f580158024030841d00001018002d050344281e10b955803130380846001603003c03a1540d01898101da0342c48003900c0d0484081c1c100030a00401c002c84401882c010f0140d84056075107117110b074990b103018030403010036500303000c8030010790703e0 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 164890701 1250 164889451 164889457
    0x30221130f0312110a0c0b0a06090e0a03030f020309030f030a061a032703090105070510020c0a0b0a050f24030d050a020d0207030f0b0c0408031903060e040b0403031e02030103060903080903 83
    0x40f0b581d440280860042e00e8044001c680508502c023029507485010404504c0c07405154803080ba410000d0451413610301c0c00904031182d8003281020b8030f2044c03051009001c0b006c8101c4884500b406074154582d26400810801080c095002e0705003481540c101c403c40c1130003080a90704c1041c1407606100f010407907032025206032006416006454004010381c81045d80204080c2101c18060411a904080782401081c12a4131104e801c144580c480030503042007000c0d503981c0c254000c0500ca014801c0b802d0441040030700d0031001d042101e14408400b031050240645003034103078401000508035120406908005003e586c0310b00e481e640140a40c0b64211110b40c0005400705c1201d61080c511000148561194000b8200241450741c00341c3c010040083c100740200040c01070b50a00172020400d003c90503501400700ca072503a20400d0700b4941e00d42048041401100455401034140c02d0100300c20742e4150983d61218012000f4015081c404030011003844560b501814000e48039896002075606c402140c02ea40780 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 164891951 1250 164890701 164890717
    0xc030706140a1509020f04170705101d0103020f0913050123061c060b04030303050919031b150218090f040804031e021e010f030221130f031211 63
    0xf01a003242001002c03401c2e03004110503800d101c0e22034100364803040310780d1000c010b04000f606aa403021100740104e180013190040400e8035270810080c281d4012807a42c100f003d10300c903040c2c140340e8085000d81303500300354504440d0b18a0b401801c9091401d80e01d800c40c80108420f00400022441d202c0d41c28001050903900100741d1070740142681d040090301148080414581c4036000c40031038031204000b912800400140c4007651103628040703170a103002d03214a440c24a050129401c2e0500307811020010981014508034845035079070240c8030300c17405828105001130100800505c8240300160740600c00c1c01210f2045c0f03030781c80c049a2040e4030ba15152980040f85034155005454154100030400004103407551030340b00310800f071496409030b40300da0f00010341c0c1d508061035829114043e05070420183d070b40b01c83c1c0b506441c2502d0078214189075003c0d04103000c3c8400030400f01205554600882c1000c2c0c003542c00d4419540e400030b2058032403603c82c500240700201da2b0302802c250358100b0300d00003039460030042034400003 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 164893201 1250 164891951 164891981
    0x30c032406040b030a02120c07030f02070b04060c0303060f1404110a0e1003140708070305091c0f0207080d090608070c050604061e0905010c02070b040f1202060c030706140a 76
    0x90034020030f05420361000d06500f011036401c000c8600f41c0c1c550f00720018071501114501360384640c12410040c114404001c1d4150854220460902480c64220251002c0c3e841d40e260501d046c8841e4581640108900c1e0051041a2100800000c15042513842c0ac40b05e020182c1d014803c1941c003041e21121401307504003035400b10701c07058009182802d0101004848141d249800306a0302a00c00307952800d00c905482c1c035400100080c04005400e50540107968100b04100700401c003421848105102c20310980241004106e942828804402e10070080c1c04050a9401c059940341010760701c000d04000c01030700c203100114500c2e5000031030b514020407880168a4105019048176030b5140d890500400514503c85410890307511007210041040c8a4010210310650001480c0e07250380318060b103040141d40c06028041410042032010100090514007111849c0112030b4200c1710314030001d4110700401528506034800400e011040c44059000500e10800f010741809054480b0800302c820b5030300d40c604910380 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 164894451 1250 164893201 164893207
    0x30c08010b1b07031505060f100c06021e03090304030614071e0c08070b180a030c0b06121204050f0a060f140c0106060c051204050a03170f030c032406 66
    0x7102115010740301107a90400261043d0b25100c0d9907400140c044081000b4015982e8010055107003043e0524001055044a03a205d2641650000074601d0054034001098260081001c10050300b059007c0d01ca203204c00329507107407680303046d103440b683d650400d1105403002d0741881d0403251030b142a6001fa43c000d0754a9074aa11080c02014441d40440b2501000c01042042c00607007a4086100798000c0e106051140c000da00640c20300109a900310000c00d0854001c0c0d4100c103520000203500a01e074104415440000040b00760340d100000b800d00704660389089854002c02070038580c02440c0400510540c1c408952007000700344448207112203010039008480c0410a194441c1c20000c2c000c041400c403984040800a10306002c4403055030a44103181d1001c07002c21002c100100c10840309220b0410740d0120000b50380d06180ca131000280d0510b0f903501c0050b10307038110400039503004029107040b124141a0652861380d0b07070500c01100491984200e54490014640c80307100200640d16274851045c0c0a801400700c3c3c1 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 164895701 1250 164894451 164894467
    0x90a0504030905100c0b0603120702041515050409050f01031709030a0804080a0b13020303040509180613020f011403010b2b02040f0f08060c070503090306041101030c08010b 76
    0x90001a00540600030003040c0080e042e0740d00361900781307004810ba6454a02d99001d180c07074040e44202401c218442d03004071812092503482074040d9920b080c0c04480208004c0185890a0a2102103400c80c0d0813020f0940d42240c0416003041c0148101d4208407001c0081c1d40e688411504440003c1c003008010780d000c0303d0f5154049803003c01502e8a64030080545404044c43e03a64001c20b984260310510b01500501482d106001e039500e095a0700c002042d80003400407445a000907181d11079406441d206504140101e0800380c1c80c0c4403940030b01000001158020b007800e072108a504012404100c0c41780400d0421025035511880d41d041e102204240010304590078140c000c03c1c0d94000c00c108100000003154000103203560720400c140944440b0000513540d5040010f43e901c0380540b90001103901c0c0c1904030412105c0c0c00019156481030700b2060341d546454040c1b40c6241140710340700d0019030522a00707040c0401d208410f214107003500002d8070104003240710501c0940b900e220034804c900701800180580d00c = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 164896951 1250 164895701 164895721
    0x2030307120e0f0a2411090418240c030b0a090b01020c0a15020d0c0f02041a03100f0c0f020c120f030301080304230d0323070501270209 60
    0xe01882c2c6160903121000c400200261900b80340c0501030702d40c044200316507400400c40425041400b80d001c0410321891000b9204d2414a110314420240220355075004244180c01000c03401031490782c0842508c825410b44190002c1030021541380c003c2441c9040100080b40703010307100e04014004060a060506413601c5c0018009020004096041d401014501c139a2542d0b4240c8090150041b0380001045880202d402031038908400d044a040c0300303d80d030301d81c030110300010340d50240303a54111000306c0d02d036182c03120702c403140b4400000032901880341c20316040b6800f04a03048450358504500c0b040042c0e00c0c00140407070311101c048541c54003503081614015858202007120140440701030f02200d0402e05550f00052071540309a0041c07045800214003844240401d00101a041d1440e481ca040074440c0200041c000e01c550f0b880040900140304540007419148008102010042c2c0051580b181600d00700340b4007a0150ba04000740218980090b100424640180c10050321b802802d900c1d0103650300e800c48 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 164898201 1250 164896951 164896961
    0x1a030708060d1511040918080f03090111070302150708060d0605040204110304030c11011707110a0503031e090607050a0f020c04050112120806010816030b060301060314070203030712 80
    0x507030318000c41d10f0265542984900613000c0f0840c6401e032082c0c4d1a0f2034074a01800315480800c80c05107410ba145455030110b500c88054407124509046884d60342d45886078814014400fa0605104003540410508240f5401041408403900d1443c080243c1e6515404102d80040084650907405108081c00001040050340865030051010f00b0014065507802038201c0e1940040f0341c110001503203050008100700c160020800717450800e00b00134047c183d018031f40100701c0d4030040c080d82c208100e13070384410a0301004000d074003075894020081c3d954034200182107141c0e80325642410b1400d031034050301003004d0321070001300c251144d80c01c0c0d503580e0b08100029404560003013241445404601c01d002140c45e0b40d83d250710915000344580f40d0520071880c51440c204e090041920340c14000c0c04203000411410fa6003240c0c500c3d9011020304031080c113480319504264003c0c1480800560410302c04400880e4098150b4417103043c101404140c11402ea031448030403666444200c4082d40003030001c1300780f0880c0007a29044 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 164899451 1250 164898201 164898203
    0x110f0a1707110904060203040224190c060f020408010e030f04030204050c0c1507030b060a080708060a090501150905060403080405061c14040c0504060501021207030201060b0c03041a030708060d 85
    0x4000d030741c100c00320010320f50807810b60381035514641c0041403000310f2402196804400504005c40c10a48429010209150041c1c0140d0780d1418a00a4620071041c807944400f01256807042e010001c44a03c41031000081d000703030040e15090f40c40c003207040300b41e484000162001d8203d80c1c40c10625160450f4284006880003620303240205005000c528400e0506000300c21541e943c450420310f030ba20b84440c0003015642a810401e00070402002054402da50007600c00b0341c01005810104902d84641c80401c220070300036489082135a18120010400d00c82d01141d10448003499514501e80586800400c00c051013144001090800c2c108002c01450800c20080c1c0303c00201c6960000044580c00284c2e0240e07820080480003c400d040200004c1048204004024044c191410009a03041c800040d5450380d40c0c5030391120b00c00000c6105000c151007500f22030040c007078805000d5162000c0c070380ea45650350098000d04075000e04404014524100c0c100c10360b80b1032884d640d01c01c80c80d515801e080c007400c54140c40c8 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 164900701 1250 164899451 164899463
    0x6030a0c11100f0605040b0f0409212601080303130c030803150111012304020609030a050610090507120c03091b03020f030102030105060a050a090f06110f0a1707 71
    0x1440d902191040c016451140300c02c90021070349102807405407040341d100340c10480c440d0746090b0710104a5110001031031110b44040e6000580301405041408000307540001558002d1402d00c00d041c2e4490f44151080c1c8519451001400200750f030b1480008910310034000d41032180d1062002403400e100f0802c040210501032400a4806a01d0703031244500b55104554405002502000c400d15035603112aa2a111028a9008001843c04a261071802c04405074011205400c40d03c00700f001c1d0742d0390710215808190001d00f00c45441e145480c000340c1313855046a2500001e000c1640c0051420010b018031441500e441e40c442c8181c00c071000308403004020071081002016503680c0c4040018154030010042110642d45002080e0300e144104454210b1117078405019074010b000422194441c8415202d105040c3e0804544030015840100c80a62032940411103001d12241c0015509800180300100e51504800381c580c026a410741c0c69507030fa6682030006140c04259060307000d00d140c418020b0034015100f85 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 164901951 1250 164900701 164900717
    0x201090503010b092703120609070c05060c0702060405040624030b0312031305150a06051207032a060f03290114090301050114041512020402210f0f010b070206030a0c 73
    0xc05c0740c0303503130005111302c070810300764406002040c81c190b99032a034400c10926151801603001d60b03956848940161099481e1800030480808546d10354055602030040580104140b40c2c0d200003510741441e41c10141c01c442c10901c6c0c5462101072181c010110b2403c001f40c020220303100c2003003190081d0b6100a11030724a85140000c0840000c078103120980449840c24071590303803400c02c001c0711012641140d00036841441143c42c075130205203011031441c08503034020710742401da0464000d840418640c0c1d20400d503043e04213250041240fa170441800808841c10740e8003004803003009038030f58046810f6180d41c5500204800d040402941c820240745034400490f1f04c40a0500d0603020200742901c07000c0e0800f034103c0c1290b410007420f60810f480b030340d02c07c0d006045440400d60724154150070003420b441c00290140382c002521035040000403000c0c400e051100d400e00e000900c0c000350a25000da00070307070341c6401030342c1c5200000803803841c07600603030300055001402645962101c418007802400840c070040705001d401 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 164903201 1250 164901951 164902021
    0x11d010c020609060a090302030f2a120f070e22110406090c08010e0f130303020a09050a0b1801091401050c01141f09020403030c03030b01090b160201090503010b09 72
    0xc81301810080a45071514280c00d4150f00c1050308100c08a0303610032090380320340800d03a080385401c0404401702e91204500400788050101151f4200120603003100c551042d030350383c014103e030002510000c8074410000040e20741c484445180e090b0b41022908a441c0b44401c4102e00401c2c2008061144103000401c0061400c0d078420701d42098405482e040d6001c205c0f1040100310240c24201c945a01404255040e51f4600e8421402e01d01081890400780400d0390104e85030341c045000d5a840d0000c0c007001041074000940c1e50491002d583c3c800b15120341c1c110b82d20042c0624550081d4803800c00c0e2201d40b100040803007050f03001141d241d00081144000c030741d02c0d07240421144031542a041d009116141241c88460795403c2c0680102101d40e0080326001d204200801c0465800f02410303c01a0b410325001c19040c040303d004948000030398000c0d1065810000d05400c0c20562140f803401d005100380c031600204c1c1c3c0d86108050883e000d10a54940003200c0d0300000d407441f071842d490041c0112510741629400000 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 164904451 1250 164903201 164903209
    0x9020a17070c1502071a06030a150f110a02010e010902060a11031908060108010807030c0302040203070215070504050a060306050901031e1b1d060312030601020106091109010806011d010c020609 85
    0xb244034800b0b2450784c0090100203000c0c1101d07007102010418500e01503141411000b02c0c0d528500100050a00503240c00c610a6425040d008110000741203141402000c0d0740622a500c1d0358401c0d0301510243d86010300c82860302c5011300621010395002840b203400e000a8000c151002c1002401c26403540c04200114001c0c0581ca03c01100403084503034940c0c1003440c004002601d03924060b080b14840c1d13031000200f00f002501c07081c10007099a506950250b00da440c1e040003a0f1402007171400380c00700342c0c1c29442080340d8140d00601400840c3c02c210707038544105a4506c800e5046078800d029468011000380d00601c08240105605150409000302894800c4440c3c1c0341c2c0e4241201c846401d402900388c401c404c0011812010115400440000e803500f202d0800e01c001a507101d4201030f11602101e0b0100c00149180c2c001c0d0300c6800148808002400345c4075001210301c5081d0300103041c80f400302d2240301c00300b0300d00c2d4424079100649006c0401c084118082003001540e03c0c0300c481c80f08982c8a40104907a1a076911 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 164905701 1250 164904451 164904473
    0xb1b0708030411180903300403021011040f1a19030b04142e1502010f0f0209010c0b0402150c030a090b090102030405040504080c06070f0909020a17070c 67
    0x1010b43d040500b034101c41410009000f01007545500391448580501542900c0401281d44010315511910111480e00020324941080382051860b0764844030200030a040d008944642a08044e134010814021818250a1903005a0040442555480748207110344100104421480522002c1c0759050071080c40140c8a01c9007000540c000107612144134480030304140c0900943e034204440d90102c2403400003228404810f0703841c00e81c0300901510811001158029000318054018480c2000d10390b8402500a80a01203940740c0c184050b280006480f03500d034080c820394445080c141c0d0383c80300020140e00c1c5d01d02641c0d00900203a0380a181a410103662414010040190409107005991a0344040300d0241c86940c8551101215944c01c028038550b1380ea01100b15015150121400181603d481c2001e85050080e80e40ca000c0c14070400051020f140e0300041851404126980c64060b455241d0314194280d005400b00c0b1008500c68404d03c06c00030fa9203001c41940300c02d052500c00c0c0c0c1504a40c5884809003 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 164906951 1250 164905701 164905703
    0xf080c0c01020412050d0c08070605060f03010f020a09050306090d05071401090606092409020d060503010c020307051c05070b060118030305040501020d08010506030609220b19090b1b07080304 84
    0xa00c18007001017048420300c42ca140c0c40c045800c020305090710580307400747c4c1c900c50a403000b00203e98401c00521741ba9281000740e400444041e0080099101c4590b55100039813006811401007a003c42d000141441d000071182d00c035a80910140c031108000d804282c0d400d4005400403100100300c040c100c100c0401c01d108110445025080c0455028a040c21080c202d56803c1781c25440349162102c0d4103103c010710203001c004c0b19881d40c8016a9803110010420040845410103a855400e000000302071070f50010107003c1080c00f81c02038072440c0f21301c401d000304e03031445403541480403a0090041c2c40202d600c00b03020342d40c44201030420700d00305003540b40c524000fa1600c1e00100c001c504040317810700a5590402203210340c0074190070540619418980011001d000080c0301c20f104070080030000d45004024034841000501d2407107005035101d41803900d030288020403901701c43d11800078503001481c0c00d0180511003119400000c00c3c1c2c01b984500019800600c82c0c1310450600010400034500003410b0b64004601c22 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 164908201 1250 164906951 164906969
    0x706080c1909060908010b2b020405040c030212150c18030d030e10090809090921090913080307230f040e01050102030a08010b090d0b1305010e0d0f080c0c010204 71
    0x1c107043c41400307805808a0342041400782c1c901500101c0a403220007054101c1c144051401030f01c1c400d0400041c482c01440103000703421504200600c01084a08880704064030b1003102c040828615550700b00e0b03641c580c0309040f0b0708540320300d00105260700e421700000d04030711180040900052008001003442d08024620040003e44c6d1494010b04040d07042c40100320f1118244418020a00580c45500b0f1500486181c984500e00c800080fa1031a41c08000b40403003044610200b012841110301c840d6183d401a0b07070218050b00c01600040c41442c800d0183c1400c080c3d0000f0081d085480e4014100c5103c0c1e10a42c0c500c204803081c445030318003107084074040c0148102e5004581c0e980d40c1420035034400c228040c0d00440c10740d4400e1107080310300d17908814103a040d0f800130b40c2601d803588504000240c01661407403000c0c085288030310500c181941881c07440031034180164024048174030003041c901e42e1510700180c080001087c0000c403615440c0b141d100590409840b60204e801c059405101508983c003e40c400202 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 164909451 1250 164908201 164908217
    0x30a022a0a0203060a0b010e060f0c0d0f02060702010b090a02071104150f0e01030b040305031b0409020307020618070501120b03010c080610020a03050d0b130f2702030706080c19 78
    0x21483c0801000d070f802441820180030003100680043c1100000f50b110303621a07000480d04180c000312000a0301c0101d80803804a07245543c404001030442010030b010400140184030010b05128014043c0c08403400c030142a00e0025507558110701e0007034005241c201d80019010311030308030580c1c440c012242400620980f0b90b58044c502540b10038100201e500100c1d80c1202c56004002284410f01501d60058140c100302b0380e80c1e5210003030709070344842e08402071040b20004500420300703000c6540918466110f540844003151102030782c25512a038000a0350000d40d00081d030078481075101c3c649080140440420100b81c5d170384107200080c295003000703100c0e00014140300100003035890401c2c990004104103001510a0f00c0d02610018014414084660b5040d91a102040c84645440c12514524104510200010442854401d0240040c0c410070a111000c20414880901d440c40d18040742c07560003401000954036002095605c000c000740000d0488109016822204003443e4200380d8055290b41c0c0c1040f = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 164910701 1250 164909451 164909453
    0x10c050a15060608150d050f060412030605010216030201050a032307020d0507050c040c051228111806070206070c05010315290418050414010b0105030a022a0a 70
    0x1048078603952052080140d00313001d00110241c5402620000c15003901d4081400c100c0d4144145401140220b010091280c00f00700014031904040404112000d56404d001b070710341e500b004a0340c0340340826100e8410140440c0420056024070014070000040c0d050200701248202e0301c40c0000f458084001740318003522000c11078100c5d4144005500c404031814154200317401d945074155107042c0c1c2c408447c0a03654400302070840c1c5004a041d2582000090300a05141c0350411440325000821418100300c0710610b0b2000303010b110b0f140181503a0121085046d82400040c100086500040d0b070000f41d01b01c1fa08106100150301c17600000d000d1240a140c0f12000145060001421a83c203001d869444c010120f90900c041d080da90704c42ca03090745400c0d0400c1e030010b00c005840d001d24444d550007003061010143c0d41d401860541c0e0405403145008418492070b022800003214240e407100d801190001d142000014040d1805902502020320b600302e054214203210503a951518036a000760f00180c1d845800c14034 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 164911951 1250 164910701 164910743
    0x30a1b080607120e01090b18070e0105280b0c150a0b0d0303091a01090c020f0105040c1a0409091a15061b010f0c0903260d0902010c050a 60
    0x20003060100000e121610341560010584110340ea0303da0a00c0742c645858000c080425008104a9500612042c0082c100500c504503240810801c2070002d020b480707000100d000c1540d1403141220005811400c10b2a08411a062140e0304900c0320700501c032580d00c011986003100000fa121194102000f00b540c415141c106500c890030040000182606141503031005032542c420440c0310a41c9404d000c40c12029a20300b04a44998281d940102d49e1206070001528034415082600c240c2016020b5814004591000c1d07821717141c04031030250042030701900801103c0840040c82617005500c0740701a0610380c4503845501591107001c404e42d843c4841010004100000300300c107503088401c2c61170a881030700160000c2034141c021607245c0f89403a5440494543c3e403c5080d00a40701ca20a240070800180b100114040c203030700d00502060b603088003410310400310350040700d03401d60380f040000350a5814009035115181c060a40c4000880c1080300300009000001c50402607a4191441002500558850007402d5 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 164913201 1250 164911951 164912003
    0x7051608030705120c0c090402060909090c101806080612060405010b010905180604150509130b060105071e03090e070305061f0503040f02040605030a060b0301050610050d0911030a 79
    0x49441c0c481001405e0315007400107104902000d05907420081a5500d00004602d030240c0155150012640d01c02c0010700307907001c1243c1030780920895883c043e820050380d04803102100d070340703100103001d1440c2c0c0c0c00e1120501806020394007403801001c40000c6c00d04624102d05050098900b01c81c160345421840a00e580c2020381030001e0001620940d0900c2c03030340d500040309640d000d01003600860344c1da5001c03441740c2040f0100340054540900300050508028a13800c0b03842241e010b00ba00d2402c4600c0c0415219031049084400290f041203030b64110115404090340030032000603046041c0840300d1300002c0c0d450010700741144106602d880001d80703480c02000f48420f40d82c080d4510441f840034151100461500001520f8110350003c05c051880855440810000c00b070f071b60483d40e410300c02c46004004000803034002c03220001e0180c00a024544440017804070115803007420383c02041040c003041034100c0040e07200c610310600551000a400844001290030300018010036030f1580c1e0140c2050003004442513034 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 164914451 1250 164913201 164913223
    0x411031b0103140f070e01030e0a03020703050606010503040b0a0f02070f120f0201110409020903030903031314030304030b0a02030601180b070611030606040b0c0a050102040e0915160507051608030705 88
    0x1d29506444c06106444013a04010a85000d01040800840a60344250f001c2110440c030f00045682c032030113505000e5a0759038103200c22120f612410340013966551103682606d01480c1d00181a50311600c880a01801a0042c008110700040c1c1c05c1c001240072039a034810058855019a503040880b0010b041d00800a07003810b100001507a040440d00510380c00c00b03504403011039448140040e114000c4800281c11846060141c960500c804a103202d031203041c0342c14910464031842c540701c0000c001001410344030b0046210180200c10210001041002d071900150792012052404103100788005240465a10320780c1c000840c1a940840c600d820881f440c4034641d0300310701642d072050031481c3c4030000070107501c554018101c845901140184c84504200240388045034044002d5490342d480d00b202824440044500c002207210700c024a540720814400d205000f117092040620245c1240d08050340e40d544513881c01c03105480703850784180040026210007805003100714040c2d0f03581c43d000e080035880c0c144401d070 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 164915701 1250 164914451 164914481
    0x90b0c030a0b030109020306061011120c1e0607030c170108030910030e0d0c08040f18060b180609061c0f05061801150905120d0f14030a050411031b0103 67
    0x542c05c0142e50000b4425501c40d204507410081c1e801e0b40e510891340d403c483c01c41c015551080f07071410080b0050540289c42e0302c525010880d40070484e0060b5400c0c0401c0100240c40c5c0d56000200072812452007a00008014842401c0c42c0c210f06980c00311000d0b07190800d912a80154001061910203032400700b400e1041c505840c54240030b0468a030039490b80f80e060319610780040c0601688654200301c40c10050310002c00c0034102e0386170021b60790262030042c60410452181c1142c64400d010400c815084160740200300520207401800710b040007480841e90001042d540d00110a0040c9201c2109110220302c4103000f03402d0109040c504100c0e84415034002030050342c4140141503040c4000080c80038801d0450300c1d401d01d5680c0325401844190350f0250326400240e0001c0700c807004018400c0c40002c04054071403066460703426000740c248084440c80f0b0104007485c0715a0042020a02c0e106064201540241c01003d180907125120301c0001d207420406002030504120140c24010b0321340c0c152007011201c642d068 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 164916951 1250 164915701 164915711
    0x308010906080c0d0f0b010905040201021903080f0c0d0c0c06060801061208130e01060215150102190215040f080c0a03020d060c020f070807090e03040803120a090b0c030a0b0301 78
    0x50b00160b200d14071501060701880003680d000c1d051203180c8018034005900140e50f080385503180c11004018050884043c1d015209034104070740d40070007550001055035013580d07801100e81c484541204944601030302825010400b800401d9940480d0310501210b040640c0ba411650f142c540340c06411b50300c041d0b0162505034500602041004103e06444405542c03040042d5030314901741c410014101002d030089406049000c00108200b41c0000303030980c070b20300440041140c0d5075940c6460002c0c02e041003450350058002400c4002c030541582c2d29136001c1c0348000e046010b81028100a2903003070300664890312000d100d02400700607540c004c1c001000d06c2c2038261400000a410764000ca8070801880740000c0c007190341d400002d44400d100380b00c512880501c08055965440d9543e02c081d80d900c406001d01408903140c40c2030b4415110703001044a00320744501c4099400e02c401c003441c9852469001b011400c6071516848a100040d503000001407184142814040d26818011448400ca544100040c2e010703038541 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 164918201 1250 164916951 164916959
    0x30b1509030a02010f1205040309030203011d1209010309080c160b0a0e0d060f11210103020a091d01050415050f07090513020c060c1206030a0b190207020613030308010906 75
    0x200c1d82e040a550207007021044e101c01540100c4408108004202c011032800060004140e4814001c1045a000710028050752503102031808c072345607070a070000000b540841122101510f56034082c0407a0f9005060000f2031607840e4030b49684650145045061907000400b150300854685041000640304240300f950a048000c42c0c0600403280344e007500391040c200b0a24035020802c0e40d030003d07141030750310500911140d41850b044400340e070003952503140001507080d0007072186c924825040341201c1e0000c0000b249030346000e180c0c60040540210445c603252051380c00b84000c0e0024003801d4000c6106e000c0d12241c00d511400c00c0700071520094800110741171008148160f0720350006600341a00d80446483c1c0e02e50300350520400c0248a050440300c241c1c002c5400b0051010044000340c0180341001c06210303000e07501c01c2e080540b01d40041a0042141d1842408929104422026540d2904400f40014a040c82c250005203c2d50017a8540c070b50035200c9008180101540b1040e024010301695400384401c2d810 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 164919451 1250 164918201 164918203
    0xb2101140f071707081302040603020d060f0f020c07122901230f012706120e030a0527150d0b03030406020307020103090c0504060806010305010e060c04061805030d030b150903 77
    0xc06481c0c907100c081ca006e00602550380d41d03480507004550080100c4180080f80c601000504102c681c0e20645c42e2401010711404c1c0b0b003d0084aa1042c12000a810b0007030400f24244112007000d4015694004200b1685452342c288110019101840610003180e543c074010510311510403607158020314546802500300c20381c0341c208040042450900b00720015101300c2d418080b034981c1d0340508a0110400c0040043c3c0142c0104101c1901c8140305014403464954400f01035480c4103040c45a0f0000d4001c026004088070686607260300c00d405a04107503540f00340074002a0441c00c03119254841e090f00000c3c840d40ca40d0070ba104030b035403403a8240c024508092038a00048d40340d009130320002c1c2c103141c3c9034806a0200140415108080c2c44000d0080000f2500d4604440c5c0da403800740800c5a9030340c40c212880d40040000200b00e807281901c58551072030079007061001c40348089069284440c4202c40f07140030545076414094411140410364002400b2111502084829a0100300b520b950020030016500c054030 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 164920701 1250 164919451 164919467
    0x1206040506130b0606070f060614040e1b190801110901020c0102010c0504300602040609080304030f02040c020f06090309010e090105030307120c050a0b060a05040b2101140f071707 79
    0x72044544545030f11087c10501c80d2401c4241d03006058614041001c07a41980c5904042d01c40001924200308041400b80707020350fa03407000200003aa130b28180c1060080e529081c424440d01c0c14000021680b06aa54000b4a081d0388501c040111600c0c0045016580e9590402c600c0c50380a000b4402440b95141c1d540d0060310501c01c0f80168040c0b440002c030030039a102c03031040b0016903011203840f100e84614080c1c03d041d00250440d02608002820340030700040c40300300020640b1b00f43c3e034002c1404814500c5960800c401800d44e04010341c10341c041e040e05007a454106001d443d100da41101c010395503803200c030b400040644c000300c201540b040000c480140f003181c038001709a40031981d02c80e41803e07035000b000c801a40c443c2d54100c8020400d2103004581c804010b0540f0400b400b464003990480e0610391610208002c2c0d81c208844d040c0c10292961103421012000340064140c181a100005010010f0004030b40724032100321041ca2941e10004c040c0f1040070b074040c00b2a2001c1200e0190213030f250601c2071000f80505 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 164921951 1250 164920701 164920711
    0x141308120c071505040c0302090901020403050a050607030507170c1c050a0905010507030c0816090b040305010905010506100e0d060221010e0106030504020a1203050405212808181206040506130b 85
    0x30810400122b201009504407000746d40c00000711411032203a440c01654645040300c00a0010b820704000c1100c640c010342501a5004c00d44c01c2100d4580e1f10400030300340b29048080035906403031030107151070049070182c42024050481804040340301c0b41603080803030030741c0d5003e40074804052500e513030300e02e849902006080d0841d03141250700503500c2039140120340d105d000f90031144076540300040002c02c00c10154099041075208100a04c1742c0c3d40c17424100321820f9191149040400d0400c107024405142104907000840e1103600014203003c10104240702000e50143d0f1030103401e035160018805004034011003401084203113420300051400ea07001c2014410305114001c03016000b0b040400405004009440c003030b04024001c03114019005003600c0380f40003000c100c01602d02a20000c82d14010900c141a00391608044840c10041c105a44006450788450901e0700000d103150321505455580744804802e41d80c0b200014249400c00341011400c1050207850414500d0107102400c00061140c40c90f642e00c2 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 164923201 1250 164921951 164921959
    0xc0a020118080304060503100806060a03080a12020a0c02040e012a050408060403030603200a1802041509030516120b0702150a051009141308120c071505040c0302 71
    0xd5001c1121018021219800018043c0400f00f0080303207069016010303500ca0140390a2103485d06540d50704490300e540c0700360b5103030b44c0040115006201261809009101151503450280301120000c0c43c0c0e4030498000e41b03407040c001014a500d5030194a460700032800201c00f448002c20101e4412001e18090702802004105040100c00c00300b215917009030300b550300600c0110103a03440342c40c0601c3c0040040202c1c1c001107032144400d411100e41e08254040080e40b02c1405400a000503007499020202011000344555a080d02007101184ca0040450280101111034860958090861034100d040c03002c0d40514420300c89140d0b00c10440b101120762400d0029810000e10742091300e807504d080341401200007030700040c4080f62003800240e4440303a001c1441402d80303219078641281c60b0005802500c40c207208500d0401c41d02000b14103445941d086064580d44502aa03900e414010a54044000012113440200a00c0880c00e20217110303540550580000d0460810420744c03406685d032088a415a020107405 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 164924451 1250 164923201 164923217
    0x8101d180a05070902040f080303130813080a0503042402071202270f07020309030c0913140607020706090302061c061e050f0901060f0503040f08030a0e120c0a0201 72
    0x14140e0602008541d16045400d951106440e41340d0080039510a1280506c803081c6914000b40030400441503a006082c180348810402c06940c0b944122074000c00c3c20310380051052000003500c00b2042002600f4103200308091915680b40c0003a42e0210340d15615402c0c29014030340c1444001c949c0c042038100a480b04014110042001400800d103981c0d60345e524a010340528881c0007040f1980c03014110300c1949010468034103a96038000482c1c0f02d01030503c0c1e040c0c0503406488990782e2494008000395110703c0c02c40000020040715180e140c240c0d03961880030b060b00e4000006100d0300035810310122001d840ea50410300c04072455a4003151207442000c3c5000500c107003440d660b5039841a25040407008001c10000303141c506110b404072071040c034203a100d120302c1034103217015250141c10204080c038100c4407152100640c51990700f905480681c0300600c01c80b0040c0320110201c001071362090155001d84100703a0002900200c003000f091034074007081220030100105000c078000343d140024101184c65428601106 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 164925701 1250 164924451 164924491
    0x70507030201060b030c1902190f15020a0909140c030a0b010e041b03051503030f030a0b060d0905150f060103020d06030204180b0a0603050c09150901030308101d 71
    0x200403c0c0d981c10100c24450300105100d21003040401500520040c481d00d0040403103100d00513a03031882c10300124801c000c40e41e212900843c00c01100b46014900401c880032443d80862407002c120790000c0c06e03a402040301002c042c00054002c0c0b08840809081000c1c100d8107007440040c110040c080105a450801d4480c0300328007040c0d21603101507540c02005041400701080381510070744502011114440042e01e00000a010708501000e41e69401e00040c016600e00907200c880c1d07032100da02c024000d080700c9854545466441d12008010480c4200d840c100042c0c00285180041c01c280314900000c00c452010400d1144003d986070300580c06c00424240180e842032403c0c3d0b5040904034a074000303540315241c402d603441d5071441498008001c07841585c2d00261a641d042d407690032540c0500000d091035121068180c2d181c1080c03007006801115468101e075001500400003003c646090b0070837000100c0f820b041c40a600c004000100c040c0207850110414040000e8035985110001030104a828040e42c1481c0707 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 164926951 1250 164925701 164925703
    0x92e020a0c0b180c061911070f0b1b0a0b01060f0e0a0e09070503160519050d0f060f0e12131d04051209031902130608160e010e0705070302 61
    0x2a042a52180000c5100d28024015002240c2c081007600102e0040c400044294a40f02d41181c1c42e05003c014205c00ca0000e010003120b0039414620747c00c80c6840354000208032605d1034466040141100220503a03940320021104022403402118141e21b81d0204210100050a5241d8a030541342c807407807c0c40d20401c080202309c03468800c0103515074102c1c0000c00f0100701800302e00c00d003500ca1441101103a030001c0d0b880051640d10380340a56800410782030ad4405000302e1400300c03003601c48114407120120b441600c0c4c00c0007440c01030803854101c2c4c156528840c10030810000703024440046503600300800c80013188003c0300c1c0e25185081410903000000182c0c1c0d28808040d00d0341000645440d24480c400845219050301800c0310566068038540b0409108844640d040c01c100c50078000c000c0c014141c0c100d400000e96070720310100744049a02580f0204510540c0b0800e01c144001800007500815030340c0d2440003803601034012a08514003001d200c100500480c0041c190840c0c001c10903152191b40c4103540e050403 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 164928057 1106 164926951 164926967
    0x23106150f030f022506050105060405060a0507080c16060905031f0b0f09100501030509070302031e070504090b0109050a150501050c070e070305092e020a 68
    0x208004a102c0c0d0881804040c40a00150034400c03916a44080030b101d41d202e0f824104540b00214085c00303168010315004103800e031000780c0360a0030040454620700c103100400d010b1120015140081207a258100c1d20485401c4041d80d04841c104c150440100c0c0d5184615000035010620110b40c505d00480da010807101030b660704c002659940c0e00110080c0c600c000e0065440304070844c402c00c481d241c60010510034499030329a80301c658107010006d4210b98001d80b0000b402c0d13002c00700500041c1c8000407059900c4041c52450301d070705c2003803101461400c1d03840d410450f002424000484100705100005a041e1488800c003408142c0c1d0380310f03d00c0c08840b002d27900350045043c0050704220550145000341517a407402c105541a0075200d00c52000c501c50203844c1e6400003036440042200c2480103004041840343c203048402d0710000320403000103054040c2101c04061030340c0003030b950500714007135112 = true := by decide +kernel

theorem cover : BRFrame.Cov 164748201 164928057 := by
  have h0 := BRFrame.cov_init 164748201
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164748201 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164748201 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164748201 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164748201 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164748201 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164748201 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164748201 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164748201 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164748201 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164748201 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164748201 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164748201 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164748201 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164748201 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164748201 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164748201 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164748201 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164748201 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164748201 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164748201 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164748201 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164748201 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164748201 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164748201 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164748201 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164748201 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164748201 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164748201 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164748201 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164748201 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164748201 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164748201 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164748201 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164748201 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164748201 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164748201 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164748201 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164748201 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164748201 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164748201 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164748201 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164748201 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164748201 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164748201 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164748201 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164748201 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164748201 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164748201 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164748201 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164748201 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164748201 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164748201 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164748201 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164748201 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164748201 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164748201 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164748201 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164748201 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164748201 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164748201 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164748201 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164748201 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164748201 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164748201 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164748201 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164748201 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164748201 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164748201 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164748201 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164748201 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164748201 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164748201 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164748201 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164748201 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164748201 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164748201 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164748201 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164748201 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164748201 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164748201 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164748201 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164748201 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164748201 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164748201 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164748201 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164748201 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164748201 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164748201 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164748201 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164748201 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164748201 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164748201 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164748201 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164748201 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164748201 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164748201 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164748201 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164748201 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164748201 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164748201 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164748201 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164748201 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164748201 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164748201 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164748201 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164748201 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164748201 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164748201 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164748201 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164748201 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164748201 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164748201 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164748201 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164748201 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164748201 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164748201 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164748201 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164748201 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164748201 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164748201 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164748201 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164748201 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164748201 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164748201 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164748201 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164748201 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164748201 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164748201 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164748201 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164748201 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164748201 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164748201 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164748201 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164748201 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164748201 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164748201 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164748201 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164748201 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164748201 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164748201 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164748201 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164748201 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164748201 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164748201 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 164748201 ≤ n) (h2 : n < 164928057) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
