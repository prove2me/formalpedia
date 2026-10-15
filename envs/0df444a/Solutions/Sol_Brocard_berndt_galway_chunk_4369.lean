-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4369
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T12:24:02.436001+00:00
-- url     : https://prove2.me/submissions/c06439a4-e536-4610-974f-8fc85576d341

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 785611510 ≤ n < 785791366 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 785612760 1250 785611510 785611553
    0x50c040507090806100b04090b0f0406030f150203060603220507030c060e060c1c09030b040605010302150309070308090109270c09080604080d11072006250f 69
    0x2e450f00803060302e0100d0007000074884504250040000070f40e00420784040d60001d100100301c01f01e00d000440c0c02000320b411a10350190822078000144443c446221000398000c0c0e1001c0d400c1d501003081c010983c442070391007a8000c1e0b4200002030400340018a5415901c98078810050040d0039502d410f407403c49541c005031200e60741080208036075034000004490581c8280d502d54200b0401c01c0030f2940714428900b030351114403201c0d0000100244680ca9810203540d22559880b118107181c01e260340202001d0100b01d0041a10100000305864040242c0e8807034105000100029819596200c941c0e81107004c00031705021898202081c0b14550700c41d074540740311a009500c2c010701c2a41c1301c40c000703480c00340199105004c000c02c0240036055010070202d52050300174900903a0781c0490050100107050064909204d10f4001c16050100400d0f04044040621400c00e81204a01100d0400c0010b03c07030440350707051010203040c50010b04103500040d192102d0294181022440702a2184234000302c2c90310820418 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 785614010 1250 785612760 785612777
    0x9040b090106090b0901030b1003080f1c02070803061e031218040c020613170a0c0507150c02040f02070204090b0f070f05040603151a0a02120322050c040507 69
    0x909000d200740c2d4000c04141400780000008500840c510890600010306240782c0640060070014220908900540c0d0080b401c5036101c80f10408900a83c001541302c101c0d03050200ca038051449072030b00968071a590041d4032507145480f0707101000417498444052034600070000d0140c0d00250f80a1140340c00049102c01da20f5600e21100c50400f66180c2010300c1c50f40700710301c0d01040602548d80020b25541c0301e03184440d00703007451070107081200c0b0750309080d01131906000300007802c07520081d4810189441d80303105004840c46907803154003414902000e54803020000303045c3d020030300152a1980111512044400c0700520f0710040d81c0202d0150340e031403002a40c0b00c00445c0c050081c002c000c81016580704080380792618503060b02d5000180603124038400c4d4010561a001158540030074105024000c0c0317005180701c802c003c4031858038042c035003200036082c0143c085d0549008583e07200008484c401da494400c0002da00c00c86920380b64400c600b4107400c1e19103110b0480c11041d01e4445109640c0200142d840e071904 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 785615260 1250 785614010 785614021
    0x607090b090f040c031a0411040e0403212406050a030b011704051f111b0c100e0a061d061b0304120b0115080c1b100e010501050d0c0e0703090209040b 66
    0x40345001b454241d80500e02d014101781890f01030318192420782d030b07007110700e80203d48450404440403030484101c01d544109403c0d01d0f00c008085940b181034081d083d601840305940c20b0a40074a13420b5858807034040820010001d000c0280c1c4603034000d00503a081418603002c04e000c42c50b019924800c08450455003035020741a000c94080c10307050112800ea001c400280500007000b010f03180e59000e00074010300519991002110180003e006000401c42e000d4260400d014081000070b0a501000720568000c42e0704150100c1d0062045e0001c51007082d503290501c90600a01c000c1c422580e010059142c0129038000710a000c0a600380000c0004040d05185100752a20908101e849041c041e404290705c2c014502041a01d250800900fa03413000e48145816151100e00f800180a1621411a18058016900f00d0400004a1713402064072074004802084079070f03207600921600180141014112103103c000400001230020340b40da91204192801141803034880c5d020030f19040381036a088442200307034400c000 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 785616510 1250 785615260 785615291
    0x801060f171e071a0d270f140102161403040f0b0c0703080d09031d18150604090e06010503011404080c070e1602010c030c0507020609060c031210080607090b090f040c03 74
    0x280416013202d1401b1140c10700b814403516015480c44000d14203805503045c5000c0c0b007070a40020310003903101802035585d502248052640130000c08000c40f0100062209141c0345c0c0070000c01d171002e9807065903484880b6800d0030899040398000b100c0c085200d200744032000c800206090090300d01c0301d040940104030400540b078050042c1003400f00422841c000382c003558046035102d03084141111080750390a42c164a5400340c40c0031a884407084580c00840c0014009520105503010900c425000f00c1a200b1690700c03001014241c810180c0110441969880820f01180021004100f1040c410b800c44d00241d035980440401103404550440081654410580e003480d028081c2c0c0c4196001480d0411440f0b2485c14080d01a001e2014061300a51000c101d01d105501c80404550315040701e0002c13245c0b5411850240ca400e003034115240c4001107011800003840080000d0b13003900601c89a260350103610f013000c038420051340226502c40c0d0300442c100c40c1c1d07121640321441840d0003a241980c01280e020202c45020 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 785617760 1250 785616510 785616521
    0x902120a2009070e040906140106021f020c0705130b03010c080711010606021b06040308070b16020a05060601110a12110106080712030302070f0b010801060f171e071a0d 74
    0x11401085090100300c6404d80c011202c0c81e4418084800103a01c54080c03c2500080400c034020760b086100c0240042202798002494603210300984900403031000702448108164003c0c1e001d02085035011803000e11003403801c00301180d02c04000c45400502d01c812900004e003562000703034150b0042040d00b014001c41590000d807081d4803071100301c000e00031070b0301d0210001d645e0300c40d5100704003143d401d03101560b100342da03400200c1d8010f50708000c0194844c9400d0402402c80f90f0f00f55161113034440001c40c080c0300d4078008210030804076081005042680e50b00801990b107a5440f40d0440d00c0340c000d020740980010805020301e500308070903680700904121200380385800c403002900003004a500055040050300689c11400810642c0740c0741c0940c54a00e6407802c0c042e10a401c820062542054000118800505500031000c0f00e42c103400d1880040d80d00c41ca90012004c10b61000c3c2c10f9a00100c041c04101883c000600f807159501c05d080303a94440e50344400802c2c13254401c940042d90640000c650348503107254080e1 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 785619010 1250 785617760 785617823
    0x308040905070e030717121207030605030616080612010c0309050c0103180f14070b1905030402091305030405060a0e0405070f0c1b090f1b03050c0403060902120a 71
    0x72200342d183c2100090340c60900c0e02c69403441d0160a0b8504e0704a241c188680b0401e85901c80c2c10710b0300c4070f6280709400001c07881110f070040007a240460000d424540050f0082c001d6800c41142c003516182500100d0b80908001e1109400c030801c0105c080b1451001d200e928840c00e100d5a002541902d1842e2003400d0031100c81da40c604240c02d20340c1244001c100d0000c0c05040e5544a44d00808224051600f60b50200781004840241d001e203090000d55003005c040109251941348482d42c9004401d9035041d2210700080d10040e42001401000608402049408500142c02003003180d0a095580000500c01e40c06800d54038006072510301c031560380342410b00887d9044a05414020a4003502c00c4000786175288040d40134021089218041c0c80c8640882e044101034903500c1c80c14400240345003035800251020900070030307002023100c080446045c03080c403805006000001801340740c07914507229803000d00403890382664040843c5d640d080241008201c040d0031544100300701c10340300d99403102c010030b5103501c12075 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 785620260 1250 785619010 785619017
    0xf08180303091521011203171302100309050d11010f06150f090f121203290a0b04170d020d020d1b061d0c0109121713030804090507 58
    0x41500540c0d42c0d424000080c2c400c0c4040340c3d15841c0c0c0041032000c0c0025281130001c80709083c40045034a40e01e49005407006030098899095100a501c08010401030840c4c0413035860450820680043c81c2500305118200910f02d408900340c020303a1180c42c140141e415042010840e452207000f0026020f01031140e482001c4681005051f18050281d2941150b0101e04e100b0805170310081003005001c1c62000d00504084200c0c540020b131a2980a800c8514007101500c00c400b54103e0403080c28481c0c003035000390075599600f0f191401b00c84503c04025202c1c401c54150700c84404080440d40b000c41c1c0016200400143c82000c42c144a03405401e8240180d00904034210b40100309126812600015072207051007461801144106e00c00c02c0c1d02030aa080304400520a41c1001d803a9005081d4070503130420b0010f01e100559a6000040005451880b00d500c00c110700034030144405404905902640b5012070394440150780792030a109000c5451904582048504030404030782440000d205d80301d074680c400701904 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 785621510 1250 785620260 785620267
    0x30301051e030709091506030303050402090a092a0509040606050a0f0308160618120e1914210714040605030316060b040e0f060601020607050d0b0d0f08180303 70
    0x2008241c07075641d113004551125850b43d82c41c0c0c0801580a0100d402d0710107000080007659140d280c01006804250381c01d0303104094800c0030890400c1a07105403c0010742c00b0003070212138a030411b040c4040c0044c0200130000741103c0390000980c0d0b10740c0784100380328034440d050000d42542813404008400d08103070400c01d8100328004c02440003891420032a0040c07211030703554140624040c602940900701030340030400d0300d18404811f0000c0010303c61a14400c8429602c88140920f105814419145110143e182404505e20002c201d465441b4900d0b111070368015122501740010024111100906140d01c03170859030141d00104140341485c80b19001d200c100b1507081c07241c1403400703000aa503801050000584900d480c24000100b00081c1d009e8540031801401c184060040c03101583d8a40c4001018007609000303c400140d00c641c40131403d90300c034a50b60b80700d01e81072020280e83d410040064968003a000390500486c03402240700408100c04507031040c0ca00d50758800d42c4043c16890020501952800b80e8010b0 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 785622760 1250 785621510 785621569
    0x23040e060105102a0b0f0c0319050912040e04050601050406030f060c0903021e1521130b16020f0f031e0d090c030b10050906130212010803030105 64
    0x8054841c4074005150070842c070500e0418001c10304036059080310b56199040104002c005c801d508051003125240d040d01201d40e40c0380510324052004480161a0f14000440e1070000807442d8481908001480c044640e01078110500c401181d1294012800700d051040400c420040100242d41c09090b003501c040c480c140c80d40c0c2e911030003100b0100b402003020f40c842c80495175007031040035040d00640d0014800310310700c00f0700c0410444049640c25010b0041c030005441c1c402035128041100d1030016040aa0820400100a0314100803005082284011421860304000c162942e400318001d00344c05000c003200c004550030280c50b04032124203405540c1c205010504144402000b9101c1404031203111b402c0a070458881401c0350320404500b030302241d00c0c211001080c407803045564030a0307d1149030884038944440d490103034920300611400398022444400104141032141a01b09204440440541050020302d04040c49045c2604110155400800108018500141d4107000306558170740310a881e0118 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 785624010 1250 785622760 785622769
    0x230c0610120f061109031c090f14040b060d0e031b0a21090504240e090318010c2102060606040b03010e06030307050a03020d170903070f060623040e060105 68
    0x21140c01904440ea210420645240c00c0300840d4241c5d0401800c0e031b16200ca446000321820128000f668000440c0381c8400304001040003843c1c0141c40300402c2148000d5020b008000240c0001621660044420b01c04c011904e0700714012a9410b4041c0d4004e1601c2d0408460160b0007a1205030011806501410040020401c804000e101403941c50f9001c4070340c6803120405603107480c026849950024500401c0c81c10ba0921340343c000308070403400003505291607500c0601110f1420b05503110089034108200c40314410841d0300c8a143c5500060402c01d00d06a0303503440300760030482410094800c007002c0980c0c0c00d000079414008030381e2042003180d640d401c19080c2103030060385000500071100b04004107004100141c1d0200700341c61205500100b00c0d051511949402512202080795030008500900002691600a10190f038400c03c41d00d03000f182892495210034140d00e00140301074980641e03410000c5080c4005400168403601620a1400381140700f000344002caa035260300ca41d215401410061119544 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 785625260 1250 785624010 785624033
    0x30804021e0108062b0f0c080a0512030405161d0604020a0c0620071202070902040e040f0c08030c1b18160314071e030c0f230c061012 59
    0x2054880c030b070720285451a40b007400c001500185c0c0c400c0c00c05c02441020071035140e01d1901845d1045003c3c00b00141e840c504141c1c0e804200800400b01d0b080441c00d101107181420240d51301902580481d947c2128500b03514071811803c0e0060b1a85c0003a9000c20100741040c0e900081d00081c05070350440c9001c240f0300e00101140d001040c01046542c6990310a4101904d403180c4c4200d45808410150f07503481c02c1c3c900b0002440c180428500540240384000401d40071a10079a02210495000b0142e03c0d515581e881090003070222007207810b040e594801107950002040544812044903004110380c04200e20f5240b004106500401d104070701000030240c0030218941c1642d0001600480c40a003d80c4015050b0058900021000700c0000b04030108201c050740004122030902c0845441c03480b640c0c03025012415a0042442c4101049941030b403148034038810b90a81c4180601c000e00144524a00211801960700c41c01a00020780e000c08180603006010b10340840082c0403035200d0100301e404a0f41e1b00d0340d0810 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 785626510 1250 785625260 785625271
    0x70c0b0c070f0512030603151003060b01051b0d03060509060a060809030d14040b130c0e06120a080d05011203020c01030c09091506021b0a03020d1a0103030804021e0108 74
    0x14004500001003028800491035000d500100756007184000020124090300b01b02c0c0c14030304c40d22881d01c400714a1203544213035a008410514a80c8201400e5460700c0003c0c0c510510407030304200003000000a510300d8008c1c03d4000c00300c10001313040d6410f010f03000107040d00c2c000e8000314804c0c0d903440184a0107580301c0100804481090030003040035078a20b02e03a18210b024484102c88024107142c04864008149005035100e1489000407400548891170b0381400c881207040c006201c03409811080c07141c24201b0ba4585c0d40000b00800b1604240f110540702c50070801c440004849095003c10308000d0440c25000300c2e40035256480020f07102c40c02c180c030f00075621381020f80c10380d0505a549051500c11841080d82e02c02404101105003c4103402e03609103040c2c83d20901c100340060017500c810412a00d2203c1d582482c40200812680c80b00d0300716002c0100b040c1390b01c0d034105e4009652141c42c44c5d00c840582d502c02c0c000c50190b00d524a05141c14018856402164522841c4408414040000f10380c1c101007050b4109 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 785627760 1250 785626510 785626531
    0x12020708031605030f0c100c0807270b0c1c030207081e0d06170c090915100312120c050405130203040c0e090c0a140117040302010605190302010305070c0b 68
    0x40210b420035900714441c1c541c10b1642c0c45c0d4001240c405c01c203c00289410814581c440c100944004841c046070030b9081560324900041024078812000b410201c4240522103804d000c002003255a4050b0b80e0303003580459500d19690704480f00c078440d040c1d0300c209110081080e07070505600d00794481d9944840c5210f01c0031621100300044210031b4410104000780e850040c001c050401091b40c9980750303070062241041001d0040e1040210015490800d40c40e40c502803000d6070002d05043d144001440c50741d0f40010079042143c08500c40c00004900a03050300b11131800310b6100d100788249610b90310070650b80350354103002c18442c007004100400c0c2c40313070014030a0f8112a00401078403621645006004011580c2c44a85c009100398148845c6c1040455050300700c0d28110707000c03000141d40324440304501d254851900e01041c640e4100301da007254280c0c40300358090320900c00003a181d500d40e000104a040400d0107031103401007a400600031941c243c814190401e005085c6000707203046036515026036440c000e0400d4043c = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 785629010 1250 785627760 785627797
    0x7080f010c1412071d040914061005150c0325020112050906191514041409031602120f1501090b1f09030b040f11010809330708041202070803 62
    0x4000c9085021985d904018030501c00540d090620006540249402181e680902004a040940000340030000c54801805402c1603c06038100e03000c03290080080054030380006c0162410725a0440010401c41381c805134040c59141c40303400010b001024013060400340700c1c9060180107a200c070000d903d9a018130000002e06c1d0a891300e9901d400507102420200d11003d113000c1c5c011502d4580d82d11900501e20060b901003054002254410b031510034195004e1440750420403c001002408890b0884140c0c009005e40800d007440340b106501c0c0450044d4949040d4010f441c000000c0181c1c84c40c0e1500614022500740401ca14510004036460550601042948a4103a1241106000384e0b0010b00940c1c0000000d40303145881d081402c003000306038a04403410314071031441025540c012410913014201d10300c014030b1010808445a030094140c2d4102180300c0078001c07581800d048808250600c200c03410383d03d50740b190400e0328049183d569040010015034001e241d00b8131001c0800000d8460703030000c0b004106c45 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 785630260 1250 785629010 785629037
    0x7051206010c080d1a030318100e0307030c0503010b0d120f120c0804050c0603040506010303050715060311040f0b13021c0c0908060f0708010902030907080f010c141207 74
    0x42c40c0300030220040a00d180411600380800840d070000d1150304c0315400c03100000c9501006c05444c0c1c40b0392190174000540481d1a040c0a0070084800303a140030290900001344150b00d0002880e10b0190352086820340480042400f55080a004030b480c021820b4801801c80955a610116a44e0303555100c0b03020052008012028140702e543d5040b8583c602000401440420746e00081420000325425243e9201d0181e5140707603410000101e910550300070010b4078440e4216501100c0340c0c3d000341c00540740d02d00421003503074850341e45101d460000d520401c0e42d04455071401e800e01040e02c0900541c104498501842e40384076803280121421241c0b0f81704801070362000d26071116080c20070402000301c44a8680078060b1030040e00205980d0075070708003038201c2d5010f80d564241616005812200400041c80d81c500400014a40d0703005181c200e00c81000703548030305450345031491805003540411400d5a44890112805641196402035401a1514014900280144030070781c9007501400800402140c04100390 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 785631510 1250 785630260 785630267
    0xf0702100e04020a0903110a06091701020903240a050606030c0a020f010501120c0f1a091f050d060603020313020d030c0f030503040b15100f091e08150705120601 71
    0x20701950008108548803800b550000f04021240d000c2101c8908849070462214541110751808440d026a20800301034101201e00102140e54401c1c05425074080c0541c41c41582d043c081d4044c4402c0700404648011184654000c8601005d400002900e240c0020707c0f5550b19040101c1758014120070403103940e8001c0e154102d1030014185141d204651030803001080919001c41c005410500030000c0d00c4c10075032030301d810392208050341c403584060340c10404c6c1c600e000c6142e0601410060400402c4400c12104541c0750824481e484c01040380050f0001915512081c1a441031501070152440c1c218114607101c1d00e40e0814548010000c0c0c41401400203400070148100c1c0311219007640301c00e0408201d007003840d020704207400980301102c451080740c0c002803881d00220301030700c0c000b080100604001783d0286000d9030300f0344498448504008a4240204505006802101c090a03c00d46807640e031301c0c5032200c46d034241202c0c0c0351017000c040b08140600460a50040075141c4602182c1c1922055480350710058 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 785632760 1250 785631510 785631527
    0xc230a051824120304030b072a0606150903050d030e1e0a0c0b03060f1005070303050907170a0611040e040602090105040302040f0b0a0e0601022509090b07020d050f070210 75
    0x140e80c46000d0010b03401d20f00c400440600200d902c2041042041d0301d4009081d64508000701c0706180b03100c441240c40031411050300e100c80315180640e10010380c45480344030fa054801d09241c11000811262442003041040411407900e5114283c40d0400c11040756800c06078803403041c071210781e111201a1040c42d04070740342030210350f00d107590041c101c040032580c59001c800e990f042156140c1c420403104400014505102040821002c00c941c0d80a15280340c613913080c0d00601c0c0203450484d40d8480d040c00414a010b6101390072541c294500000c202c020f96600d001005d9034132803580c4040700e400520003080044400c0c011160015441800540c9030340e00301d00100c1d4140100c2e0300c06035000341006c000c01001d540710341c011500020169402c0d13070703995242c1c4c1400300d00c51001c0d2152030040c2d0010010b042d0640140c0c4000583c40403580900400302d507900e0325103068807031483d010b80e56001d00c1c005004000d6010050144a00d0460512500300890b01d070801406000c2d840c0081d000714115064042a2403094646 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 785634010 1250 785632760 785632831
    0xa0f06030915180b0604020406050f03100e01062309090601050a031103070306050f01140a0302130807090617060411040c0302070209010b040911070804060c0c230a0518 74
    0x800a042da040750b40000d0305503c12054501c200c0c0c18010074401c0c1440d0080318280c0302207407600e905e80b00e0099810f000c40e0703100802003402c0a201060100d000c0c9040e90340a03000780247da8502d000e07401b4140c41400d400e0760b021444030900310104610703407954950300c44031688821b00742021030712040c1211007030b0301902d50380704080d8201d0800000c1009254166100300c0540c0c1040d2000d115002c40f410055420501890f407400b44500c0034001c2590381d0b8407031340041095010413200441090761310445a4a8080fa41c0c005e0300e1041d44464050084503428038140000c0c200c001c1c0145011309281d01e88052070682e0032010343c002d0b40c4a4103200401c5000350100d401c425400f411611103903a6440401000f0340203030040c46c1440707040c060340740342002810090b40c1106811801052915140500a4a641504540c116196103065030002420300480c00d880c41400206407400c40d4800e00032040000e068070310781110744100c518040040b5501600480c042c4d000761a007144511040c82c42141034005d4450040 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 785635260 1250 785634010 785634053
    0x42108090c2119060c03090b040b1305062e0e010e0c0909090a052a0409050c1c0c05150304141606020f070504020708160f0609030f0206060a0f060309 66
    0x82c040800b4070020f0580c569004900c00c020108511074110103580184002512010b03202c0040f4010582c50040c841c0c000e54a8801c1e210041e031705540b200e0605804458000d8818240034503420301004511440001c00410300e00e1118580c00c081a403840c40d5010b0144012010184000681c4120f01104644808000800e151070320710786440c0c000e56501c4c1202c000c81c1c0700e006070f1280141e0f40744005c00b42c201e4004581c103020011038001e010300001300038518058a4a128102c3d8410705070304d035a07520303c02620500c4105441340060342041c44152010b607100030300980e92120090815143c0000f5207070400d5004ca0310407506610191041c2c40c003c40b019000c0e00640d081c103000100c203038000501008810161090343d0342c0b2545c0b901040224011404058145a0100b101c0080400030115400405104851950060800e9104c490441c5d1034920101c0200c0d03040b425400b01141c040004560043c81259400f002c1410052002c038140d11034403451f0309258440036010100002c0d41003c0104105807103 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 785636510 1250 785635260 785635273
    0x60f0106050903012021160c0503070c180c020615060c1f0c082a0c1f0204050108090a020319021c030504210b010614070209042108090c21 61
    0x94940d0000c0e030141d0f59103141c60003800ca01d90f500c481180701c1d56216920051f60401d00100491040d9404261108101da00b40800c00071000080e050540c103101238010aa00c00a0780d803a40f42d0000100d480090a0105540c018002c00c0403036120401000c1c1550810b0700d01649543ea95420207103007500304200e15a511a40e03112034465812154040b024085d01d542d9510810f440b9908025100c40e0040041803582840c003002c034800401d40401404000070103000c4a14250f141c0543c84e01c010440e900c46ca03800740e0001000c002540e0f0104d516904245000080c049490469000940c0c802d0050540000f207140f00706000f0541d41c841181b103180c0041c0056444032071046240050195001c0d0190800e81c203050001c01f42580941030001e00055402a040f45899007441000e0b50360b10144089450380c45810403101c4010707151140034500462107070498494603640400c1d1303a0301c028040e446002c100618032041001c03410001407052803981c001d45034540901c8100034030a00802c03404403480181d12a10 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 785637760 1250 785636510 785636561
    0x6090f12080901150305060106030c120e0a02011101020306011d060c160f0806070c06050a0f020712020c15120403050c0a03080402030601050105040e070e031014010f08060f010605090301 82
    0x1201d40b003881c1000082000c00d01c52042580503002c1808042c1982d0300c01c0c0014081da5010f0b600c913000136401d5003003007490220321200010580707058070340e591183d4002e101500304550700013885590086041c00250709601d844030000380f5284440700c03040721403081c61505407030580360b0000301d820700307080078060310500d003505c40b10160304015902c101d2051b42c580c8180000c440d00c0219015000349026640d508864840f6150200034040140c40012071640d030301c2001ea1600c42c544002d080e80c03481070a882035080000c3c5006807d009006856502501c00c0440000c49103451768111415064048400035191300d9030305084910340a5505d100780107111b03110101e820306070403002c41e521543c401c60494030107030388881c0119100c2c0501e00c6285280c008441c086454540180103821404102404a4070042c5070b40c0306020655019804004802c98205c0040c0801520b4011000251884c6402003006040500d514104202c05208600800c540800c82846a603000e42205180c111201a91143c0c03c0b01d1 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 785639010 1250 785637760 785637767
    0xc1e220e100203011d010303021e12040602100b03011e020d0b09040506160c031e0215070509010306121703040303020702030a0c060807030603030819060812032a0706090f12 76
    0x38062100d05102c0c08110768a041c5d100780400b0706899155000e882c0200350301c5010440041103a0081925004540e440203524424101500c000c00c072941c0204007000700d0061b64001c031904d070407402d4000d0341824540490f035201d07d000d50030783c2c1e0314540340140d40b0440d80580380c00420350240d80c5c6900010000500c820b02c50000782c0c4d0350250004001c140c8041c070100100365000045080d0040125107140380121a0403810451600c504d002401554603002c44c1e0311000c504418215114000b00b040482e112030075503454481c4c207002d09078010f48043c15610b2600e40c01c213442d0707a841841ea000381c0000005010584281c040d07410803940a012a03100010b81d1808100800d5030b4000e440008500900040051340720340074402c01c8a030591a05002902c4840500600c90086180681040e4440c500090200c004101c21a41c41d46c0910030b003070f120f0400710f00321080c01030020580ea0390b4402000c00e10342c690310204210340031240d21440001d010040b52a200c0740148500a010705000b02c46016400899017 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 785640260 1250 785639010 785639017
    0x301030f0b0c040f05150c0d050408070608010f0b1b0d0c020f090f0601030b060f040e0402030c030a240603050a0b012111060a0309020904050c1e220e1002 68
    0x30601144500355182a41ca45050141e889040d4403d8030503801081107062165803400e072110820030300c3e494a0407a080061401217400c070032900080700001c01b0080c1007030a02207040504401d15000f08654500300740f040340302d0340c64024011c41c4640094140e13109990300340980301620005c4290f40d451443c00e40003070140c03a2040f80990213903003040f1007904980f034958000791180c00807903e102140c0e12078400440003031100c0d082040e000380d410070010b2050035410001c1c1006046080c0404901d00d05481418142048000c50074006d91003101b841d000180d064248902d0b280d2101c81d42da08240c1c5c81601c1d20060006070744098801d005d0010036009100346010001e0585000368880e001031114070300f221401c1c0f140300d000a00018910009146507150a400030000900c20f4a400709000000d5000a4414281620102e4103a4004403415089080101903864001a080c0038400403c1200011501c186100f10518110303000d103141c601d885001551103403200300035134000c540140c6071030303c0340000951 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 785641510 1250 785640260 785640263
    0x70b07080c2e0f020307050d0506040f1a0a080a02130b030a0b04050d08011505040b1303020916020111130b0d09062d0b060405010c060b040203070c0605130309050d06110301030f 78
    0x3c0c104242100d514149000302c07800f500381981c0e250300d06207072007103080c0c02490090a400ea1058698181c0c000e0030400d8000c10440110640c445050b80e82c060003003003966080303a400005560011584003000d030356090365224001c001d01c540419400020400203050040d400401070424054005003c1808000220b14080b07610a031030b40080c1d079894001841760012408603150009100308018007a07280d0700405001080710014810604076100e81c009041d12208440510782d11042120440c40a50f09020b000c03402d401280f01580340c94060441e0082c900900d02848001200008920f0b203480c00f10350090340c07226008031040010310f4042011f05812030030743c420020f90100100c89094599030354880c5080f543c0d001040c03603140624080040d500740d24429000d81e402642c0b8a50302d035440d02c0d140000c6120780e440c0d6950b203100ca6020301c4d10302c2c222800982411130b1038141c000b4102c0001d40202a22082d00c0040b1030b441640c0903a4a0f20b0350140000c084602c400780c401000010410151110040049 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 785642760 1250 785641510 785641603
    0x140108011409120a02070302062803020301030c03080702031606020c0f0301061805070c0f05030405120a03090b0c03073816051b06040b010314070b07080c 68
    0x3041c5031085030116106850814540d040003031411140e0003c000100044161030054640700da81d00d40001d038031a00030b80507680d40c0440d022407240d0010641074a5100c1a02c490030704500315411600c61404415850000401040002038820306540c0c5c108030990310700e001606c04003912a00d55030000c0d12420b00311841401251881e036201511300d01070080205803200380c203001c82e66517090901000a010041c01020503c1110b6100c0c0d008203411100e8204258000c100556541e40303001e06200c03d0b0031603610004040d4000c000c1703c0c40001e50180d668070842c0c0142c0c0c1d00039220125034410509620462a00909404010f841000f03040c64025010390301001c4031300032103c0c1e2280d071a0ba046410700110384800d00b144003c0c0101c2500c5000e44040d08090f500204c00d012540d145560b00d901c2d00806503001e640460b44d0304010420000c0d5a12441401d030102c0b40036003013072483d1500c071085601600100406440010555044802080150005c40110100032070b207507034000010791400da6966000d10040 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 785644010 1250 785642760 785642771
    0x20603071718120720010c02061314041e0f02090406030605150604031e0c030b0f0402040e070b090618091602060703090803010e09070801020f0a091505030c13050414010801 76
    0x5034a034100954005076081100e2400f013170361452a0f80111035a50600e5418001c040d00b0a601685555000d001d5401034040c031908014105640d41d00405840100307607200c0c5080080d1008413003025a1041000405224080390440c44252030b8806800f80f8080541c0180c034100001061050790f410607401031101d550b8142d190300766181800060f100728000034010070303041c4199020302d14102581100c0c55006d101003c5c0d01c80d0316550b5860303200d9000e8030b20340c120100403003d100a40c42d03c0d11600da150a0504010b141c1c052900b4030300400c7d4040c800c0034a04c9400042100f82e005030045c84416244840105218000e140035440d0f842c40d012052024001442205c1c00281d002e402486042c001c5a008401c203410b580c6000524500e110b0020701e412920300818800180580c6e0034009400d0181e286208207444003856040142000c095900151324200382e03a03010009190080c0840740c01c0020501c10540d00c418911a01483e41c505900c0780d6006072070700e107010140d019080221410380d02c05030000e119 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 785645260 1250 785644010 785644033
    0x210f0405060402060c0f100501030b07210b04090b04060c08090303040b060409060e07031128060c0f050714040b0105030402181305060c040f0608070903020603071718 73
    0x540002210010840c0d4881d002103800351402d80084c2c140c5840b00405c0703a075036485a075013160404404510450b000e40c0c030340c0d0050041000b0100650360150701407502d0203401070103242540001f0160306a00c144255200300350701c0152a82e40001ea6460740100e0136051504180ca0210000d101d011428800248044046810520301108490040380c0004200c5c8040c2c4802080100420141000301e61487d5501c007180708800c002d101a0000718000c1c801d802041d015070b014080c05500b0108000d080b240511801d0310348403080e949407410b440140c5030440c0d401c03006141001c100f40d810000031344284210600000c0c480321f020089920b681d0155014484400440015030340c83c04295002940035a120721645001d01c0b41d440344d9980902201c00302007800c0c1c07880e100d0900300f00064490007101007000400380400000c00e45074400401c428502400203150011004289800b24003009204080003c045042c0e40e1040c807180071b03010050309102000f410900048007182c801d54044134864020741d40c9000 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 785646510 1250 785645260 785645281
    0xb0c030a080709030308070f1b0f120c03170414100b0307061b110a090606080f06010e0102060f07090b04230303031909080f0c03030108010b0f06070818030321 70
    0xf41265459250390490b901d075280240d0b07452a14540000c01c110308644011a00121065132001c445c0c091003a4a007403a0303c40c1881900c120315445840180146040840c0c0001c0e442141d40b040110700d075815004580b21441c2404c0280500c0d00c020249110f090302c0e2010140c1c840d031100343c0e04036040b811105121f079500130548100b03492400ca0001c00700b280e038000021450243e01840c1000c0c00504002e6402d4480344420304513030700e58000e0000545404100640340b03c0c0d4002c03050700008242454000c0c1c41090340001d50b580002070680c01020510004615070a01640111019144220003280c8441d11040c0c014605c01c00003142203610125503806034003d04012049034050700ba0900e9819500c030890344208090984108202c13140c0804101210074241c481b4081c00300e601511000c0e558075454105541d0955500c070034058805d4200d841b80440d140e580604640d2a6607015888540380d00f2062116045c1c00b015000c101e4140c0400a80305100c11160818600e00c0c3c41c4900c000b00050300c0e0b989000 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 785647760 1250 785646510 785646527
    0x13090b041112090c09012103090509070314060a030b22061820130c120213051228210306080d020703080d051018060f05040e060f07090b0c030a0807 65
    0x402a0440d0a441c887c0036448901d403605031a4003d007804a4525603490200b035640e08110794040009603508152a10747c24155455500003108a40c01d80003542162207018030110003034015000b040e0010218000d60307140304124030343c2c20340050703040140c500400b80c40c1d400580d06001c2100c0d65079100321041d407002040f03407041a10720000303851104803510018401e07009000d01d070301d4013040c4030100104441c60a414001440c07514607540f40d203102c2607d8002845035521030190002640c1e00910703203095980b81c3c1180201c010080c03502131072038a1106420042d107420a44d10500300c103d007400302128030554158200d4011a502e407412950240701e59034089841e29103501004212440402c4060044101380d00582d030004511560300d000527075588940b03014418008969988961500340c1000044480c184002c0180000d032800e02400e800b4a9610b5110003009003002c009014643c00f0a6900d8422007182c03003d400000d507265514003030340c62083e94a4000d8034006000807680c0c400504050f11480b0807 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 785649010 1250 785647760 785647769
    0x14040308030a050a1b050306030703060501080c100203070b19021c0e0606150301290a03092006090d080c010e0c150903030f16020a090906050c13090b041112090c0901 73
    0x102480c4000102100c0307c1e1f10203082c455051003188404001301c0e80314800c4500800c4000300a0048483c04800c1c0021f080401d003000d8195003040c131102010420b01c1c042a9030000e54491402007038030044071850000c3c069800041070182000b000e0717503403030300c2c05e544211911b5240340103d4859540d04000c0001088444403100c201d2030042c4010040840c0813810000040d2244845200c000d040610108081e0402e070190800641c949000360180001682603803080d41d03040341801482c0c050000410300620959a14a0107100f01c0383c41c0c00c0074801600d0075609003001e02c00003400b00c007038416090740d65070620444403482b8890400d40003181c00d00c0d12041f41c0080e92b029018604120381c4c143c001950f500592000d284403100c0d41c189800607a80c0070048006842c4102d0001342c8101c090a0103c2200d41c000d00d1829844420001c2105074000c0403000e9040350032503100420401071541c0810042d00307a01410300d025480124090102e00741c07009003035105500380c004449104800c0740400c40400c0d000e225 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 785650260 1250 785649010 785649041
    0x51e041202060c0304080d200c100e01032004090b0a06020d0c03090b0304031709160b09180a2003040c05100e09040b011a0405030304060f14040308030a050a 69
    0xd640141020b0000c0c01d07240341103200303403400c003640da528460510a0341c6030004001401450940c682461035141e034000d00368018010f005007c14400400c1071185c0c000300c1a424040001d184a585c0d0b8843e0300440030701c0c640c181d0020403644914491180c16001802813110541c10801c134100607003446510703802280c0980e0b0041c50700c401d050303109840b01c0948900540412149103404030b40e181b00d480003540070350b00c42d960300e41c0c03842a9001c5411a03010050103410080c0c1254003449801040c0d0359942d01550136940c408dc4d690403c0000003032895808103a0900c070307003840718100600e502195110740008000f4003090039021b662215242c03417500c82160001c1c04e1000440040c440c508001454001c1c40300c40341041d02100c2a010005001c100c0300300c4e800c5484204a0b801401880e0b110460703080c0c44043e40100d14182400c11000170707181d008034010300c000c019030a804045002d21401c26494a80b140a4510ba900c0341c9030305021600760700407501c1c03401540c1443c0c049003071b480c000e2244400b222000d84 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 785651510 1250 785650260 785650289
    0xc06180608040503040b1b060106050d1a130e010b12071a0a080f060105070f050d03111303080c010b1207060e01051c361208010e0106080a1b051e04 65
    0x10300090107500b00d1b910b1051f4404038041781102c60304080203501e001c0c108030703114a52a00000402581590141201a20156400f9500110513143c11100200e032010707241001c80c46c0002c00040038010000816241c3c1d01c80d240146054240201240030000d440c02d42003511540d07025956801c1e09031140198800003c3c0c00800003940c160642c4200e941c01200525219103003600e16103c603500341c6003e41041c0c0e542d80100c0802c00c556038040c0300390000c590048103010b040180b00d680c0060b00502620015041480000f160200180e00313502c9441401c40060548250940000009513101c41e0350080d0300c04928411003221722507000310305644c540900042c0d202c891002001c2c100f40a0701c08240e00c0c04e080543c4800c0034103000000d280c840504104030009101503c01800c3c6040c3c0c1d1503002518200740301f41c04005010441740c154107141503c186080c00d203043d445469042008243d4161040d1003503200014600c29298000c0051a8440920f49481a4100f18000d6017040c1d205601c5040016004034 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 785652760 1250 785651510 785651519
    0x2030f0106121103041b060e01021f090c2606010f12030e06160b160206010e0702120f04062712031106090a050d02010605030a15090c0618060804050304 67
    0x6142c80051150215408034040d40741c0c070340e200601d40054500f1908198402d040da9010b80b0000e42c070900900311842c0c204912200b560010b511080d0381c002d111822840c02030100c804c1c1825401104200740d20201d200851036079629a86100c0c40d100c00909070a41d03100c6070701e01401e074002840798140c1e4030b40d00200008519012072510401a141000c40a0100c58545901d4a9543e10064a155084040b00a00300031030307450524020240200048150003c81c103142c000c1590002d10a419503030502c0108086440385a026454401260580c660304400084d4030740402c88442d024008076642030311788440b4030613601d600490825811404040d441c505c4882080401c481c0a0762a081d280242070180a00640620090170044106d0300300c5d03416441005d0240410804001960b801c1900348004c100c1c507410303c40026141c2c01c0204003e041c40c1503003001c8110390034103980210b0429600c944200f00903a0b031404050145c4803d4100c111241d0586440001c0c0240201d0790184aa40d100001d07605e85802e0 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 785654010 1250 785652760 785652767
    0x93f0806360103030f0306080316080f040b030a0c0e030606010c120e040f02180d2f040207050f190506010b0703180305030d05060a1d18070605090a080102030f0106 72
    0x9880c44802203480603410101c481d5804400c1c034081c602980e180f03180704c059020050300b03587c82984440c0f150781c01008030209141e8010440b240d020303440310034240c1c1c0e03501d8500d000c1114001d642004200820000c1405110030a55002d00416580c548a10034116007403000c064a5242c00c541c51303404102d40101c8400020250b01d400c20340881c15040035805150a00c2c0401d04a42d80105404800c0d540003841c0081c0780c0d9540d0107010301020485814040c030b4156a03408141134461602c074442600780b001d5a60380c0d0040b84441c0e13080c5840240c001c40d2141d00c2800c1c060780e40d04500f08000b2441c0103501950002c4e046071403034020115009001400641d10700800e200c0c2640c4078000903010807104010b013071304040052465200441c000d01c0259114940790080342d04035040903016500c65442103808010030300e011030003802c0f4044016071125042c0d40f045145900c0b14950200f241d8036008000002c03410941100151142240039190f0410098950105a00700e1209595492804010100401c0a01d11 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 785655260 1250 785654010 785654059
    0x60d060b0a0807030309140d0f060b010c0f0b0f15010c1b050907110f070e0a0203060d051c1d0d080307110d0e0f03070b0d093f0806 58
    0x1005015550401c1c2c0d518a20342c1055516002100000c1004130204004803880040602d240e43c2110281d0440700c0035a40c0e1035a440c000741d00100b03040d464100810540e80166000708007a0b42000072207800100d103103000c507210202150304400c00c07043c0d032020414210a40c1c10140c2d9002040e11181c001d4440c41c2c4814084042d01010071305420588400030886494111a19018102580703490801143d028241c0382446505100c44c403075036108980407c5000841001e00f03400c003040180040c1d4903207a800c0895150030f001d50300035003184908506c1c8009800044206010141140e4850487d541c40b4036640505902c0d034102c05030312010b800058004164120021500304130303a410020740502510000c20304000402e0302000208a14144031007581c10442c10b030b15200724045018044150400d1200545402000c13100601e50f130f030340d4024600300100c821001010521100c01c0c014402020400c51880c42c080030703842c0e4002d484044410720554082d0038802d0250300c0c005d2201e80c4040721214100903100 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 785656510 1250 785655260 785655281
    0x9060d0206070f030903031d01020312131403030a060f0e06010f021f06031a1006260901050106090503060106080f0606091c060c051219111c0b0108060d06 68
    0x5802c220300b000080c0300c003560764000c030300c6611819201c6107503040141040c1d03500748540d014220b4501d0081719583c4c1c08412200f40700003030106017034030b5201d40220441320551200000c188a0080048444084000001c0e6106030184501840322503100da0200300a1540f0344555034601c8251004140303658010b10b503200f0740c413451b40704564038040d1906140501403c0c0d0340d4032007952a80c1e440d040c000e200900303900c455418641c6118803041d0801d4024009400c1961149800304a00c01001803400402100000100441a451010715040c81040580200800c3c0324070f60205011f4034001900d4140032950078101e440a0700e505003141ea400501c8500aa4001e1113560b000104000e4400c3c41d6a6085a041014034105000070140c0094540383c4219045030701d08109000e018480c1c00140d08408503a82e5201884008000c5001000c030700500c003900ea85d80014131080d1b008211701008401c2c58405450680b0b440c00305114003502d0b60011b644040c0250b50098204401c04150004581d154002c0414030 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 785657760 1250 785656510 785656519
    0x1112030d0504030c0b010306090510110a0309020a0b0d02040e0a0905030d020d0204120803060127060c06020c010617120a08010b070c050901060f08221202010b0306130209070c0209060d02 82
    0x12000f82c5e58040101409800888080c1c1d642d10070701061150821401031541d02519082120352980da2169843d40180d40e100c0d03007003646403420081152a001c5a880c0209095407850780c440e41e410b03544c08041d420902640d04888050300c00103440720614041e0860140d0060051450010b00d918114080d5010403e2504403d800f00720000e0708403054460211a1401003840303503100d00b02880010421a0b008442d00c680390340e914201c40007030010750121421036a0b1400c100b41e000e8a1032a02c040a40507103005041030b5440c080c40050b10001c4040000510307102c880a440743d03a8005410f8060034041ca800304000203260000600074118002c0040810a01824450701810b503140d00141380c5000907004030001803044d2000b51561604010a01c2d000401c040344102d1400c0131112600c5006400711000d0005065298407000b20760003036006203c6010084c041c0c454500e828039494003183c14110040703024103080e00003e150280310b03102e4210015801844400203480381070800c010240030071801d9901 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 785659010 1250 785657760 785657777
    0x1603110f04150516080403050c0a080d2006040b06240901030b030118110112020906070321050f041208070e0f061611030f03160204021e12041112030d050403 69
    0xb002038500b1072610141c8244170713640d9100d0551500c3d60030300000c004054042c44841c1d005100c44440802c210901c1c0c1a1490011255008906201d501140304091050341d800b030602030100b030150320741c44640300703000945180c6146c92400c0d0b03040303400200700103100140c00380600c05245d5070361080d084804841c20003400802e5280030704c00c0780c0e410905c846000711545001c03a00c00e44c0a95030481d84034030140240c4441141065500c00c08102c3c18400c0d118014100034084c2002112042c0150300d903516144440020082880d00e0785c041d0741d0303044090700c054071411524003000d8074081c403c50002c0e100b00620358910f48850501000e014403022950582540401c1c11701c4900d04c600780451195280a003c0d02a194101c1c401ca810700d400d100c0d0f081c1c03040020760001c10102e4100528080b0b079506a60741a03c00503940c0c070f440381480407541400d400d17421268200046120060044000301401140100d11824602a03202c08103c1030307044010036071407503400601c0503034400b070056440941d01038040d0801c81d48 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 785660260 1250 785659010 785659027
    0x406081e220b1f0b13030b040305040b03010326041d041412130e09030a0c0507090207060f060501090f1208190215060402070201091404060e1603110f041505 69
    0x8807030201c80340c0759800d0b003c100d12080d001212110300024801010354618283c01c81d104001060a40e000250401500002050400d4401c4044800400000c0c01003500c070b58492402d0424511002206804404140e5030000c003d0203c4007110308541071050b5812909000910412500000510944003200036501c1440c9040f02488400540c036008481c2a94905080000b1150b07901c00b40c01c82c0415214450400615180010440daa440700074100b01c0c510b6078040c0f800700c3c43d01c1c040c8c1c0c004685590000c038000c0e04200440e040031742c42411400c07043c003200b91124011680c9500d5446180c44855280504022680781645a80d4a090080d071441d890002144030072800501550480801a440014001580c203850610690440c0c4221000e515188c85600021b0001e2498080c5044810b22020f080d4881e9070b0300d6201c00d0051040220088551401d02d04e1410481400501d080c08681802400c0348a10307003640403101d8407400c0e50405400c01c0e00b0310a564043c035017441070040a000e0b08004049 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 785661510 1250 785660260 785660273
    0x405100309050c1207050a0e070e090c04030213020a11060702031602130e030405030d02070f05010e01120507030e100527120d05150402032809080d020406081e22 71
    0x1440888000000d14040707103040c1c14801f1140d0180d200405c07410021080c0006294002400c8070f0710081104c001182e40c0301c550340c3d01c449220741d0b40002e50080545241c1c8801150b50740103004140c42c0d503126038542c404152a03c90320f591003181e14070010303001040102c032400c0d0800c00030010b0305e00150004050b011145000c00450303a250015440b103910110f030400543c5002c02002c8084407451014002940c40c0c02c0a41c005e22005005107414002038500c00640ca034460b217105038440841d00e400340418144810050000d0503d00e58000b00d80c01040801c155112031402828002c450303480f80b81041c151200d074039140080700070011807080e010f90800040324081c04000342600d00b100000004507810103011310500c60350144110b40c0514014010420f44485818002010407c4150208461f0001c0300000000303002c601002405100d0100310401c0900b1140e02a0056402c10f40300e044854a0343c002441e002503040010000042085c0c0001d980542c44500030400c0b02c44c60100c0681c0c5402c50740d90744 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 785662760 1250 785661510 785661529
    0x106140f03211e07061116020d061113090c0906080103110414070807020c0922050f07090b030106060e130b03010b04020d0207110901230607050a0c06080c0405100309050c 75
    0xc203540e041c00310700c04c0300b800031520510340c4180d00c0366060b0345042951454200c2e20284860701a10903250704622500b481525000600c0344090607031580d40e41d80c1c500d551815a08454066000302600d0310301000182d9008040d6107043c3c1d1040d4446051680c61583c5890030b01c00360016050704141c6445144420440e40c0f00360a0180d5a140c4078812549801c40d0020301d0000d40859042c4500c440d0300900009110084007454123000804043c200218203003015483e24800c04030800c8684a50b0f000001c1000c41580700464402d0110002d02240b50b076040111a0a040341c1c00456000c014000d411103441460713401950031640240000c04c02000403000a01241c11040c0407154180e00051a04104164148107207001e8401300d40360015035042990140c030540381c60074086035100c180032110b043c9994140a0714521540f040480b4071075501407a00e003404601e01d21443d40801c8415022840c4213480b18255019030f038000e00645d06034600d42c50200c0141100540540302da00030401244203a4a555107003 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 785664010 1250 785662760 785662807
    0x5010207020a0b1e070f03080402030a022808060105011416081305040c03061523030408040e09031801050d020d090b0106110102090d0204110c01020c0106140f0321 72
    0x816440e03040545680070508268a045040b04c241000184005003d180703003140440d80500d0500e9280d529880030070318050320303400040e500c0140c040d200d05507020004400c031002e00c42100111042e985c0c500946a80b01c400380a2a804526042c07810000440208040e00745401e60484800c040f40d2a43c5612807070b588a411035510308802a51705020508040c0111652100a0f28003004170500c0c0c8203c018036012040e4061040080b44c1ca54080e4152000c03540081c12070030408060364904061500b003003154040c0c0314158400d4442c81c0020a10b00020080c0d031034249110010b071024004507001100d05e076000503c2c1341f0030b00d80c0c203001401015040e03128011416110340c043c4440765040c140c0260410f5a5270324000400c0e80100086005a04c07070002c00004190f05590100c1c858841c0144a01c50340034400d104074843d031000c43e01d040d010005401908c2113400c282c0c81e100e0050324040c180b007841c4407010400c41d010b43c404c0c22a0650040c040d05440340203440e040405003800e8845007440703c0c0c550308410 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 785665260 1250 785664010 785664029
    0x12313080712020307142d07080102040e0601030b03070605090d03050d09030e130603020109090e0111030a050f01060903080331030306050f18010e040203100606031a06030c09040905010207020a 85
    0xa50400b0031080c9801b210301c12200c07400405403600580d801202d01c40c1b403800d500740d1000825003034004002081042d0005460300c10002c0d510307551115030307103a000c01003110800e0000e4204030401c02030703041c0842c201e410703650940e851500e03003103c5a060041007680e02004500b00a010028807003011a28070410b00d00034401ea54003d1111660820400484032442c060141a46011000c07c0142e0b049036071241250f000240105000c440d00d02e105c1d0040070050841680200000200001e00d0519402184290300c10b1108103104d9030ad81100f11104600e600000740261800c00c0812900b00344084a6100b0300a11300c154030012600540707150005061132403c40100380c440c10280a04c1c50302174913080450000303885000d540108408030744843d40f010f21942134800351700001703c2d05644003801043c080030000700090041e0355940c1c6e0010010201d003105071000c440d90002000151030300b42c04407405541758040321411320081c003081100500c4142c80c03c6841d503600300011401a140d4070803076001800e5008 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 785666510 1250 785665260 785665267
    0x3070914310f05091902040e0111120703140408070606080f030c0c04021303030c03020312190e0d08180f010c030509070f03081c0212010f05030123130807120203 71
    0x80324815120b4880eaa501110b0030542040b4030480c000541011038a07802030031650504090010400400500500144550901035610102c1000d44c004060401a00c050442c4a81c1c854204500b1604030703a6008034403918480201c0c02240c0c00f10003410f0742c00c1c0109030005005540d02801850010404d00d1081290004074840008079403d21007007a140c04151020b62600030207903111015000c0700e0000505001c0480071000070306200704281c41c0010415182d465050074a030445520480180800f205c0c49420003201c015080d02c0480c55003800c1400d43c4400d0071607240c0c081540e5200e50006c401030940c2c4590360800190303c50900a915106019450025035030628001060600003150010003000c0b6400b4003c100003242e6100315440c00d200703400d41403003203200103010360060310640380000c516010310030001c1342074400311500e40100c070740880007002107a841450612007008001d255840100c52070340090789030000d001c08403003000e00ca94045841d100081ea501d21510080d145094010fa0010 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 785667760 1250 785666510 785666599
    0xc0f0501020706140a110f060114032a01050f04180605120102160b070e040207060b03060c040b0403150b100207060f090506160515040c260c15040b0f1305040203070914 74
    0x3030041c86433228110440c0b18000f00a241c24181290440b850f95041242c0080d14100c41050039050f07402800d0328990702104201c48600e0300010702080d001c0c444c410040b100c4130154864052085943c1000b00c0242c4d000213010b20b4a030403099401c010645000c0c4600110501c03603e980318402025160310540d1300041a480706003e052502c1c200500ba510389a070108010b002075203101e416941160ba2120315014184d9a02035088054010074090507001800c500113143c2e04d079004a400016a00555514820b0389550001250020f203d0b10401d034100e08108440741900c1d010f042414852806401190040302c00c441042c504a00c0807a000c0c2c42e043c0d40d000c02070200c800040e10500c000c11f40b29190207061841800600c1d02d4a0109000c04d110703001280300940f558141e5000d40c0c0052008007246512680d451102906550002641c061182100c8402082e249801d10039030b4080c03002a80d880034214204101c02037080300d040d4499a0100c1560307030703812080200d0455060314440590311408000c1d00e8 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 785669010 1250 785667760 785667763
    0x1060b040e10082404030e090f0a1b090b03040c0f030503071401050f060405060a0e09010605030105160f12090c090c0e030d0e1504030c0f0501020706140a110f06011403 74
    0x60f401c02d084a800a034003240002c110011042621030000e001d900043d1103615060b603005400303080f0700c0c2c2c001c082c000401c0964007039101c3c4a4132520080340180721213085e0307690810610301c030030b4550804580060024009100e01d80c0165034018868012602c0d056140c44030241e032802c00e544110780381e80c130005402e0104460710250400a0180754000e000d9824036010729030140710700520160256561360009001981c2d2a224600101440500d00c0110300f85091300714083c00c414000c45000f0740c00c044c0826414408198119640c1c200c550303c010015100040848001e44080000d40301d89403105542c1c0c0c0801d6090004000505195030001004048c420015102300388080c07019119411020603005c075182c10281c50f0000440403582a0f094803603141e80c41200d8059600040c0c1789541407a004101441c4071701c0c0b008242c075026000ca4164641c0c0f070408449900b40b4021030001010184440e0100314083c0301c200c07404c910030740252024204041000b40c41c081c030980c01410b100c440d4000256160a0 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 785670260 1250 785669010 785669041
    0x30415020601050105030a0f0f0e061503060103050d140c0d180e0f010b0f0705030304060c110d050406050912030d05040605090a020117060402040e010314070605091c0501060b040e 79
    0x1850014010961410001030100d01004002e03202107030b03d0392450a00009170742e00c0744c403003015464010051160a444001d070745000c02caa004058008540c02c0d0141e40c030300051014100d0381d1000c0180100100e5035000c4030511014141c0c034940c00b0003440a42c40300e040502c10084000704642d226048a030348880d503855806000e5001d1400d840240b000e00c911600608001419551030b800348039500c0da022941400c143c072580c41b0150103408007105002c01c024843c0c114084a00c0c842c2c1c0c030020340c400150485500d0320074072048400851001c200c10400540204042d1050340d0300141810ba04890507003030b0758116802692107a03c0703d0b5440c400c11041145901ca020340081c0f12000a128046081e40041d0503829000e116509903411080001c942e03036550b4044a0203000f08000100d22540c0d286440002d10580c000c03540110302890301d000c950203215000755102d0100c02807550240e5010f024940c141c9031104c1034150b482c2d5403210000304100d00ca2000802c010004120504840d00c2c00c0c1c518100d00d10b4 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 785671510 1250 785670260 785670299
    0x12030e070f080309100210020412020f04020c030706050c280201111303080d0608010905030729150409051c021c0504260a08030402090709030305031b040b0c0304 71
    0x3100c4005102d540030000a440441d003003074490224080b01c20005034a0107009549128400d0b000081c02300f0b0400c44100005d50301482640d4015500c6214000c02c0180e0180503119603981e0b00512850003c00c7c0d4a80110350060721140c002460000c0e08240512100070380603528070469210038154070840c1e424400c40f90b60341c1121f03401c1814540d0021201204401d14840034001d120f01049500c07941e401030388214010120300c1c1c02003200c0c81c0c030351030219203c0d001041c040d6145a10b11400e4030003007207807a2078100c8621045900304030541c1e5140c1002c40c81d0707028241d081c0d0481c4d52001c0c1a800203008120182600115011031110b40d01071000091800c0c402e56180c03104850002008040740c0d0308003060f00d0507140d031300e10062500c06100b46007107201b070782001c2044aa131140603540b000748a4800e00541c0124000d903041072403030344c03070381c1c0c00759180e01c4a0711004000402c10800074607105058240d40c501c40c4250005980303403640e54a09400940c0040d0750580d000e4100041c1002100c40d19184c2a03c0d40 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 785672760 1250 785671510 785671529
    0x1e240b030c0a270b120a1e050a0311010b030a0302010e0f0a08041419030609021c050a0b07051219051012020f0d021905040e01060302131812030e07 65
    0x1103081c03c00d20300b0441003824039140a003c0c560000b4050002580200240d01c1010307210210300910407116681e540a1034809680c41c0c22504008080a40f042000b10150781c1c05c03800411243c1039540e011201d0900300c40f02e02c4440d560f00c1a24016607942030002d81c104900960000c14080340d22606282896907412160200da4403002c84036000034130490039101100d0540c00007002d50341d6058045004441c006400fa40d000d40c4011000c0304001e21588880009802070b19524800607044004d140e81d41c640f102c014100d54003201001001038042c0c070f00c1c80e07846602072410b03e0800c4034804051000030000e60b11900c004544030340c03d44509099202e00d581c17100e100030282103c1440d001903c103442d0702903034000e8003c0d180b110b950721035a02c07028070448169601500c0708208481c000031a9110440d1401120b21a90500b00a20440241409140240d9400070310f0441883e0502c03403200c0c01021281000c44556084c840c2c208042140c0046801c44481c554401240385000000300900746442c0742c002a101 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 785674010 1250 785672760 785672779
    0x5030d0f08060d080702190e0a0e19150e0105040b0603030403032717010b1315050f1804080a08011d07080a0b21010501080a1e240b030c 60
    0x980c4100c9480d045001a1405501800f00b410410a0703442920302c060b411001101e51035004100e18a401d03000c9030100d000d003040540341c02020b40181d4a4140c500f07609640304c0c10324510b00d0301e13072019001881403080c28180b14524500ba01030069400c14941f818480c3d541d0f9003040240105489000d070b0000048024510341404c66802812491a6542900680f103008007000c02e0b051110a03080003402076000c0c5900e224103401081c501800c2180c980c98003440407007032000b032030350401c0c0900383c1509274a200c018490f60070001802082c60401c88401c0d07105440403c65120315010128a9008500031510241c2d506030800c40909941c0c41a8421009003415944140b02500100070040c0c001039180790180268445500440182000b882600d601015962424042100910010903401010002807020f60390380c0c101c0640b03808203140040c0c05551a403104060000410040f0544a03100781200050310b1121004940c1031003030100c03014a8190342e1605c8410910301084011a05001103602d03604 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 785675260 1250 785674010 785674037
    0xa0902120a182d23010608061603060512031e09100c0203010e06160f020105060a21080703180e1b0a20100c0903030e090c09061305030d 60
    0x1407902c5407001c003030310403002041e44410382c0c100c21039120f003484820405025040310900f010380c569071840c00800d00d560b52841c600502e20006001d12812030f01c120002c0c0003a9582c54035884901070300712988104160f550240071a80ea078030f01007039a40e040c154800131a2180c84800c1184586000468090300400c1e0502000029564041c030804817a400c078903001892140710300c0468054082108000d03418090101041751b90464450400f81c825007981e100820303020506000e074200c41c2c00751845030700030080e4071301030103031048402524014030422000707c00b6820868452030201c1d0032400c82100003c1c00c00002e10440c000320708850f4050030310001c0742449030400c40c490350341e12413010303029420408010400041070781c0909501501c040c2181810a120916002090b486a407111a1017500b43d1614081007452842080c0c000c040c0e95140d19601d44261070001003104480c801421640940010030044078141c03030f08406808401c8c03c290b00410458100001c250400105e0740e222402c0140042c003c04 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 785676510 1250 785675260 785675291
    0x106140f0d150e150102060c0c151b040602010f1505180912070303050405100915020304060204051c1527020612040c06030b09072c0a0902120a 63
    0x4514001c40200010404096855428a8220ba50040025003908420818011003c01a94000020907401c0e292540e4a4841550140c040c1d2100021a40c2c0007071820403950004982881d00001c4a403101600d10400c02242d0307555074425009100140d442e4a50568590b01c00d0140c00600015000c60003071030340c10500441c1c035504080101d44504035400001c03405d04c1d4070a001c171101650040b10160365440c05070902602401c0d098030219040d115440c00700f05200d01a106e0703102000d50112104189a42c00514400a50005002500c0070782d801c103c005800d0341e034880e000c0b941c0c040c004214109900a400c043d08600d68402c201282d06050000b000300000c0316100c0d00350a01c00440b0303441d20007941c0d800812214001c880c210302401110744207100070301500e03503490402c59496236030500001c450300c01440000c05c01a22508081480120313010000d1500700d085800c00e80c08242001c034403032400d00001c0c211041580c01511190350002c4c40700c04c41c00c0e2528503240d221803403e106101c0c03c284070a824 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 785677760 1250 785676510 785676517
    0xa081b18160906080f1617130c0e0609180309040603150e0c100f17010e04120201110d0c020109020d060c0e04090203100507210b0103141905100302090f0106140f 71
    0x18a1146d00812144410740600c0b14070610002c061400880f503d0a0301d000c5203600c1307030b95074103031031001543e40001080c5a2600440e03125a002900703440e00c9468840c41c901c14002a0050303c40f541c0418405540c4940341c1d44105402107000c1d604582111907000c855100711022809000e02680103c601d11036141c0340c078040b00070060006e01d400c1807803c9802c50101c6a1108c01004000d1805001000080d14010f20700c0303650141d030140308022454844410300768221101070b0f0a04625240600a43d40440c071140c2c0401003c0f00c181c000852001950303400a088004400000c6032126134031541041d0341503000c0c00101c58054151001c012240c441c2e00040d545030f214529024005864130f000480c41440390b003469180300c030040820034001e00941c00c14005050012a40e500081c03030508055220101e80700214050b0501c108180015480e40090f500507250041501051a400f03860006c010b807250301c00380c0c2c4202d000c6c1034510701e00d5042c180000d1a0b800540a082640001400803005000e550f00c00c4 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 785679010 1250 785677760 785677771
    0x51b0a020c011103040f0f0602010608030c0727020c0a0c08010b060702040c09080609032206080411061603110609060106050318010f0c0f0e0a081b18160906080f 71
    0x340210f850034090651652149400548605041500004060206070904410b480d0f01750004c2c8041521560566542c1c040c440c4103c11b142d0201e03804112003803480480c280240502141c403130040c042144044180d0b40f01c20b0f01e0714480c3e40513940d100305104c4c48107902d0b405001d2545c02401314807040c000256460188082c00780c81560b5a220b0183c440e8040c500c0400240840002d44265292098015890740c204605030046481016402120483c07900161010b1340c2d1103444411072900d40f6110351403400c440042c00d6820030320411a4100700c3d00d8009450b00210721179990b4000900301c1520581c1402800740a1940682c826401440391580000c25240d009000c100f09100080507010b07004c2c0074014040700e45242a00c0c101003000f001d82c0c054420440080d40340c503044507186e140c00521100041a105140c3d480c0c000140c40c4003503507040120003002d180001c100d80e032038030ac015520080440042d0341c104003601c20018041c19042d00890888000c1000741000b0b20189440d20401d10104c000814 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 785680260 1250 785679010 785679017
    0x60c0605100b0406111606090e070302280c1506030c0902040b0702102706020129040207080d0e0309031c0e0904020d0609030203030a06051504050108070c05010c03051b0a020c01 78
    0x2e41c05044002044500c021b1080424440c601e07980d0b4200103086074900b0700803610a01d0900001039120384c0280220380891302c694004c104000f0301d10307003003030b9100180d50840d400b00202c40206c940400c0800e4010b0021013121500018003528500e0b2280400d05d03641d202d4080300e40184020020301c074ac0c1701c0c00e031b0f202c46070103032080fa0800a00c880100d54203100c0c08404203294902c01c8005191600004500041d100990020000400201898141080040c1c2d18407444507014054560904203034028200c003600c2610450704046060000c00c0c00e9610051021441d6480895008120f00e001c11610368208800c440180070b24280c0140148103a03a9480041d0003040c0c8a40464115210f5010b424125504404200170010700d80c41c00a4a80d8416079140d101a401e2a80200d01d6241441031841c40ea50f28100c1a440c4c50302e04001584e4160005110409201c0740c0030800002c0381c001e00076113568a001c3d580000c2d45213410048400d13030075100c011542081b40d050105103400740c2c0000702d03d80100403d01703 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 785681510 1250 785680260 785680277
    0x406090603081e0d0f0c030b0102150712020f0c0a020109060503040b060609011b12090f0602100c020a050f0d0314060f040f0f0e0c090903120a05090313060c0605100b0406 75
    0x302111600c40c40c038404c141207291031003d108815176548240002c1d00f2a84d41403011816003001240c0d070749600c2c40ca01d4a01c1000d81c0110700390741d002da070600b035102e0360241000d41080d4006903c0d00e129040204061410b0700980b020004540c3d10a0081028003054142a07086044c9a02ca140c00b01e02c00030b007842c0c040c4400080200e481d80c02403c0e10750600b400e00040021820b0781d40340c81e180a0b05010788000100d0395015000c2400c0d2414580901900c81aa009003c0102030701d030300f50041d0520104e20b4040d406080e040c6000f00302c042c80502c0f4202e032903500034000c80e03043d407000a00701d8050401ea24144240d90040c4a05030344c075071800040741d402c02c5a010030356401070741c2c0d0714000300310285c20401c81034a032a858070035075140883c400440401c116620701081c0d580700350490712845041881c3c0000b200300741c0040c81d0303165180c1c01607400520b04000c59042054076800c50408040a0b0041004511206410002c1140354020b465104c9241021a841b061400300401113602550040300e0601081c003 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 785682760 1250 785681510 785681557
    0xf070e032b05270109050a0603020705010b040c020307081e0c0303040b0604061503020a12020310170604020604210204090c2102150a0e0a0303090e0705040303080121140606040609060308 82
    0x79005c000181800420650201d42e50340c40c042d0080d800712400711a00e508120300700525103850301c01d2100b1802682c000c0c0d40382c09003a6a8210b03031035014154603034400041500406120041801401400045070015940ea01300b074100540896001002d4900c02d0741041c038284a40c00b65015001e801c002c00d801c0260f295040c06000343c0d40010300406580d1403d101104200b50b5054118484040741c55244a094844016103207440d1548805c0390042d401c04401c000401100c1045000304803d40d65901d04802501d100354001816201002801e5680c002d0300c2d013082c0902502910164070403411810802c502c4d544603070218130000d48442c541d403480700001c00c5840405005032502a10314100401440c13545480e49000b4203e606e16014a000e10903a040001d030403c0d0240045500740c0b034040d220111107a20b05500903010710034201d06203010381040302000c80014045810264100c0b260006010070346061000d0204881040d8410301040c3c0c104481000400d05a0084851341800000ea021040122 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 785684010 1250 785682760 785682767
    0xf060f0912070f1e0302160515070816050d020a110306040201140d181202010b0a14150c030a020105010e070203071502030c07051f0b0f0105030f070e032b052701 71
    0x146004c0c46001401c0c040310100f540c0414000d1140d001d036950181b60a07244c0c010700200c04098031000f1a445010000d41001c541c0783d0004c1c1078050300d5041800c4e03848800f96a02e5080c00d282c960a03002680c0409580d2080111804280540301c80503401400f461074180c000900100300c0135805010340c040000ca1890290350758008031008001243d10550040032490640208241048034000551a103004602e0603d0884c541004480382030881d00707140402c100402404500d4025003c080b0f140c10408048801410701c054042201250000171b17556161101815465100502800440d081082040002118182050081d4018102c01a201e545158041156109008010b46984207500703000c858080180040000360301c2da01c2e0103000c41d03005c000900400154480f011070110740c05100040050240581155200450f03203840d280702c80306900440c0c146401610f00100185041c00047d0760b40460581003d60b407a05490414540b0880b90450760003402c0c940540504d284a0f5514007032144e10 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 785685260 1250 785684010 785684033
    0xc070b0a0f0807110d0203030f073623030d260c0d290f0609090403091e0e06120703021309080f041403011b120207050f060f0912070f 59
    0xd616040318085c9001c0d02c00656030744c00448603131020304481d400003000f280c80b403101440d190510b0300c00e0507072460200803207440307180f008030b024644c2c0e014100c030009440300c2000310809008080107034220451241000c1c14180400806140c041c0070140b914103001503490f00b540103580f004858030302e03880d441e0075200300301c140f1484000b5074003a400c066445a10341d50031404488840c51107440d40e045280b080040c44000b0125011075944007200744405285400d24a4020b80e100f48a450000348154070348803011800c003221409140305e000020400e00c4000d0300304174070b960001070850340000348918450000e0707924241800001d0080554400307001c68840550024103000d07078440e200c680c413010030800c44d1010390003910509180d050744d0105800e26080600c9180e038031440c0c6444001d00881140d40a442c00b00c0900e06d00d0840d280c0c01c01120010030740c00c0c4685803030307404210060045828180c02500c06400c0103403201c09150419448050380c0e00b003840885500c10741c01003020800c80028102100d00b0071 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 785686510 1250 785685260 785685287
    0x6100207080307030201141e15030a1a0105130b0f061c09051c0512010905100b030115080609010b180604090c02150109020405010801050402090a080709020c070b0a0f0807 75
    0xc4003040c0841010703019000043c41c4c50a0081c0d01c005544c40c0b040080c58000882c1d02c18548d50070700000309020b401c03000703011144902c02504484851015544006003900d01d40c00503441c1182c464014002803901d0b21860f110500c030040b0500c00c00d034440c1d001580341564001384c0d91185000081101818180e4001c0f01020503250b11300300400c0341241051501c40c80c60207030ba485c44802d2409018511030164003602c1c0c0e810103489800d02d03a40e0800380740c1001020b0251499026003a18580011401d2158004501820510040341d4000201520181c202c00020f40784038442c200c0a4014042d003002d040c00d8440c10198181b400001c21540c8010821601c115003003540c9041c01c18101000b005d400050001c034610308920442c8041e0303600c030705801c05ca005900805000440c824010812460150080e001e00140205030460303117580d07054660326055070f036404403840039004a02c0c4078400c1c40601c602001440150451440d00700700d80301c01080e20380078000000c1408003510114091500c01d030308450400 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 785687760 1250 785686510 785686513
    0x1504020a031a010303020705011416030e1020121e1303051e010203060f130212070c05010f18060905010f0e0f0f07060903140c04020a0f170705030610020708 69
    0x1d644a54202d84020342400107902602c501e040002d5954490780301d242d0085c1001011074103104264070004524980070a0580400c000e00d59014925900e00115045610141d02d41d90664000d01c03c0000e054429400341c00d0483d04460040310b01c072a8000104ca40018802000d9003480e502d4801d02e8001d40510a4403004074001800b0101c1008000205d01e070101410300c00805454907810b035070b9030a0344000c44420f600402c508a0094090034081346640780300ca8621009401c11040f101741542c001c0b000c80350703040020030440303503101400000c0c410900300c80c00094040c0200d107180304c507114001d5400304006200e251b03940e950f9000d108081d07001c1021000c050070240040d504404501ea0f41d40d00ea06008005400703044c08016000e280080c9550031610562544460b03140b035a2a0801c20341c0c0c0e400801820b6008140c03a8035207030350305d030b00c0104120182c40c0c8908488111045000301614504644800460010803d1200294014003a41d82c025000c44515625003801c500807803d15010f0f60083c44d49 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 785689010 1250 785687760 785687783
    0x1f0816120f020a03051320180412090603060b18040f0903080106090b0405280801090f1203020c1c170a140601020d05250b070807120e1504020a03 64
    0x1600507a400404070310309030355000c3c01140c0340d421550003001c0810f91b0003081805444018406d00c110485642d03444103009103060410354036400c1d5030034206411034044a011b42058ae84d807030b02075001812140a410320346001c2000904054844282d407080d6840c0f002e0030003007440110400c0d500d40d080f06240b000280401c1c0524400c0d8130b0042e00e403000138058130020031001c3c140440d055507820b05490464034018860101c500c130709404200c454054001440c0b0680000101040c900824051a40c0c528400c00c00340004c43c4080c00c103031518081c1c0384885410140104085584e007034000619050301071100c690b048520180702410f46244050b10440c105e40c801c440b040064064090384550044100d0180c0440140e44800049803102c18440542010a500344101100c000c840205281c1440303003800d0340e40c40f00070b840d11015170072482204c080001a803254100121194049001540201790100500c0880394200f42251135104224030b00f400703580c00c4d4000606640c0c80000317200003190082003d83c807 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 785690260 1250 785689010 785689031
    0x2060a0908071202060f011d01120602040815060f0d0b0f1f090506031b0a06050328020c07050a180e031b030c070e0f1302011403151f081612 62
    0x41750f070001c403025611980000f000007005540d0340a80f0b40648500381094480760309001410854400f010380a4845590030720021404000400c4400d43d141c101c002c0ca1001c0385131420410000d4140002254000c41840d5480c50004200480392a0480080402c8022941e52a19203001021001c2120b0028002c00c100c0002c440c03545900c124003414007501a2081014002d1030307034244201c0c555259801c1000310038100659480703440616041152600c00c1050b0030354401c002d1a001c2e84e034000c1e40304403030303400108030404690800c8650024602035600400d4503280c00c0503109580c001540c21a4403c2e1141e070481450316060044842c811078828400b4039241c101319410341e90750064070814115110701d04c004550104070003810f51190800030002d00c81c642d5082c4a060300132121100403410b01c84521a40b11820b021800518420301454684403c1c000c1150104410002004c1800c144214089020f41e000d0364010755040c0e00c5503580400451009401108030b800100011407840200c4c44c0810411 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 785691510 1250 785690260 785690263
    0x2010c080409060305070803040b120a06030203010507050405042d0f060302091e07090807060e03030c06180c01050327070806040f1703101503060504090b2502060a0908071202 77
    0x400c0c0ea00034811141b48070f0300c80124a90740d219a01801d02d80c01002d0060321a407401c0c20022560240c03103000003090340c0d90b49601213402e41d40141c6203440030550104050203141860f10403100e0120031242d6103004070300300200d070707003150a40e444000841940750b800680c5d5110f0141c000c03000840d07018011201d10324004001022180b40305101d4181900130704e01103800e95100761f603800700b510005400740503000e141c40000c0d28400349546100c1d81600040c0800c00c00000180300c000c1c0328101c1400c841c40303d110020442801d15070085052818840b0078011b0000d510540001c410b0308141942d4600c0c0300740031003010149422440d5002070014801c4004000400809540040030948103110910915143c00905402d80c0005c030342c619409070505804001000b45402c00c1e203806800d42c100010443d8a0b07401090665103030340c0068072421154800c0c011451206880103101b11034007a008070031504034150080d1510806000808115105c1c2c4a050a2000e84402c4480480c4d102000740ca0300388050710083d = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 785692760 1250 785691510 785691521
    0x309040513120503060a15090f0b070503070b0604060b0301230405250e0a03050307140a0201050d05040317180c03030c150903040801061e140904030c02010c080409 72
    0x602540c00c140209041140e0400c4044900750b20195900d400e2440c65000ca9094000600389075202a060100080804141020007210f1106603103900c0803030b00f858459607038600603a001c03000036041080380700d0109802200340e5089507072018580c07076661103041c0010060525070300b0802d4244000400000d0050b5414244084d0f00d829000d000300c0215030701e0401c0229841100c400000310020714410060300300c0c80c18180740d00310350f0741001c41140d03c00b2408506061a160402c84599100203004810310440030805201229114001c005031b56140e80020854050054104000c9854001107403c240c0030300111030222200047d407074124035041751503044458502c0540307050341c061400e00444070309020007250246810b00c0c00404011208044c00b006109000b4001705071408180000324120400303004042c010300b070425582000c400e001c07e45200399410303584a101440c003000045801a2200c1502540c481d800d0300b49031014052900060b144490030900c01095240d00140100e440d00040e13200 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 785694010 1250 785692760 785692777
    0x80f030d061509030f0204090506011202040e011b110a05030a03060e0a05090c06090a05090103050604032a02090606070b0928080301030b0702150a0507080a20092103 73
    0x780501590794491489910301003010701c0c00144030301d5051000c503602c1c00c4001a07251001d4000500340440791079142c2048000e8200d01c501c41c1c1e0440f0000c00750300c0c003400b80c401041e41e800003c001000441300c4103503100304442c0611083c400c00b2010900416804e1101089070740d00031041c1c80d511810404018010030050040303000c4c0c0c2d2038041c00b040000b2150b100380d910403a901c00080058209140c104100340c1c02c1039007000e03441225844d010a1640741c005d480760083d8400e00040455042030304c5c010b0400c242c400320008180b100c2d43c1600c400c00f02d00c4901000d9441e0107640d20307111a15100d010070740d107118400c405402e44005a050003d4082c00040b800d00100350040f0450b000301d4065040200d100a00d07401510481051005102040200914a811980d540115120000c00c2074241c0079000c41101e000058550b25000c004500360020b21103075002908100030003c0c54030000090310000728007419004148804168000c00307494181d49141d00700060b00e000b0441d403c505510a40d0b03580302004 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 785695260 1250 785694010 785694037
    0x1b1404030c080a30140c01060e0a470d03120b15040905060d050d02010f0b0108160806121f1103040203070b090d0b0f0601171905040507080f03 63
    0x2c150100b01c0c400240c18100031858045813040d8803941c0c504584203201c02400641c000c0c403c010f0210b080c0024484e81c4002c2015246620f01e52405429140440780c01c1217480c00804880660f582d00c86000300415482c2e06540311040d110015511040901c0400c007001480e041041d00300c2c0c8406054100161040c000701008080c00301907507010500c9803c00c0c5c9a6a240b649220601080c01411500d810440d0300180103801d040080c2c0d10750300c4003407a2014001016000d0b0350340c0c1c03c4460200b400c60080c0000304500307080031811410070300c07810804401c2203414041004030300404101e00799286500000348074626070454040c580070095101500c41403450302c030b455615089a9031243e450702c0341170302d210700d4005001d0902580761014246030359100d1208a81e10503003a40203600042c10f610314045c0514901020083c0c180390241c0050300304400d1107005c10992021008000328620040450f4007000714502021a06031075030f10b00781d0300c0d0041c0c3c1c0d00400f07003074054002d035285020000005801c59004011 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 785696510 1250 785695260 785695283
    0x30305221a091903110c040c050c0607090303080601030903110f03130e06010f1b1e0308070c0228030c080303190905030901050a05091e03101b1404030c080a 69
    0x400c030f40d0707001d407080304420b060840452103003ca4000c10a04500c0c4580ca0103031208080c810b40002c0807110b0f48411600131880104158003501000c010080d800801070515044940c00c58601a104841c0101141e0415440d09000810544142c20064800307118000f200d80400e14070b907203147c0f20740200f8075000e0795a00240b40040d6203460503425034064081a1034030700c644c04045100300c1c0e209001203011484103942d46503400002c1c104240800450041c40a0075144000034500140990300140551081200c88401d000140ea1080311803281400226007422102e08030590841c4040f590340e2016051403a07103c400140701c0c4010000b10721449216000104c1c50884450342009c0704e401100182c03059200780311400065010700000e0000700c840e070030030303d0810a0314000603031004070f02c0e201c0c4030017000548008e04d000d04042282c030084c524901e009100741c141410400c002c1d03c4843c10700e44108080c1440f0403105007481301c219009150000e5040401c1a00c45140035a80d403040c2d0000ca91148414 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 785697760 1250 785696510 785696521
    0x4020f040606050a2312101212140304020f1212030a090606080d081f0503030a02010b0a09020f0d0b060c34140f0a050406060804020406090204050d030305221a 70
    0x1405500f485c1c8500503003c2c148800035204481604008200c480c074180070360800305002c0b2100c00e00d4101300d03200744400c11a8500c4000001c20503404044140703140e071810300500c001607842c12550100001e003a100c001c01c6881800c0100e240c503404628500c0b0708240003091155a200307580120015038022740d0203110301c9555842e110742e54456604002c000030400008102c80c03460846140c1c0d083c02906107030040307241d1201c0000f401c40d4003e021903070150395500b04480690420607803070320007005004411800c140c19030884994902c00c81c020140c3c1c040d59458204030b10780d0382c18283e40c8003c0c8610100c034045800da01140c2c1030340c801c0e168045e0b500d210502000c1e0240e00004060001d43d071081c44c0c580d0039031003100240800400740e00042c1e80e01071010080804c85407100e01c00da00c018001940c031518030b420607005000854140390000040680100401e00c107540303c0c1500001c02d40da052800003101c0d515802c08031062900c241241400a12640c000c1c802c0c0300340455003280d8081081d2602c0d0041c2c075030 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 785699010 1250 785697760 785697797
    0x1090c02060f150a052805012307050102130f0303020f031809060114130f1418180a080403030f0201051014011103040f15030203040302100504020f040606050a 70
    0x40b180c5200b00b000240000d21604207a4403511040c1102800c41c40446407130350700107100d0031152451100b038051498044882c0b45100508000146420700300320001c1c00301542e4450326036198181c0c0942104d0001018010800c0075411540601036100400c26419152a491003800605100a8006100d2400564800c14020003200c400044d1081c1c02c4a039803980c3e0040c40181000100420305000d04407442c001003801c24801820340c1c0215130780c0a00c0311030600050490502380c6400c0100c207480d626410001c42d4544d60301200a51914004850703040da24410030b502c0740c3c0303022640440f06015208044c1d0401c0034502c05131042c2c91094441800008603a0012400c80b075046503911004100c0700401c014000950300a60340030103041c50a4104450360344070b140e155a109612400d01d44804520821140c803c0103050042da98861500350726500301510020f651ba940214042c00036030340d60002c0f408550791f90b100d41510742800b4005001e100d503a000c0c00b03095a0088402c090200b005942529114802d = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 785700260 1250 785699010 785699023
    0x10906020c0d11010c1505011502070e0403030e031308030301050f06070c05012f0c0306010806090c1009030218180d020a08131a09130c02030901211401090c02 70
    0x401a20010641e61242c59100c120f441e8103080c0b40c14081404440004144904d0f06086c48012641011529501d000342d600741084906640e1f1045401121050060040358149182c000e6010315001c50b000624141d09402c42c82008461003000c0c00300c07900040d0741c00000c070145048540c00c58045043c100901c1c180444c52007601c4006121404c000c806110a42c050f0310f103030044094181c4c2d1405c030340360007a00b4240d645891f03001242440d8010070340038450380f038100700f007c2c00342c102180034000300d0034800712032607079951600c2c06240b040510141090380140305500c50801150000e200910509080f1400104000203803540c0459524a0800d5000380d0030008150404115550040c007203000c65803910041d40c1c10940dc0800c107090b480000003200098500c841c0c100b4207100081e40d586400f040108030310445442e00100e03c1c2030a040c0b600b0602034010003500c4140b030342828922500240b203c8202d1045d0084030510004c24075041c8010220302c012640340341681c140c80301c204922030740786005030303601c02 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 785701510 1250 785700260 785700283
    0x10e01150507060905030d09060b10480602091018030f02240406021c170601120f09050c33040f031101020607080103030f140405130b01090602 63
    0x70350070030440700082c1860703000401980c011000e580c100702c5100020010780300c210005491254413500c00000500c1c0440e2072203606189418001214854140c00340c0015003032503075408020514902c201015001c40d90300c42075045180003081d114400341e2602000a41010b50543c0c0110881e11001034282e014541d0340d00c0d01841e0ba01c185100900c6c60703841000750400020101d030001441c47d1030070f851580c1d9907803003040408039940d880d465038100b0f42d008cc0b90144500d007145858000d401c0c0100071701c0d0081001c96490401e03041800c0b8071360314080180c80d151780d06005681d040c0d2920310010702181440d07000c109031520030002e40304540010810480024031545d810701440250b5203500803038030000551a04510301d03031080281030030f13558100081444001e5105494801d45660840d007650b90611580da0b108446080130002e80d41580c8004140d080c1c159190028050340000b200c804489410542c2c0041000405000707100e9103900c002000b0342061508079020564440010812500101e251003602c07 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 785702760 1250 785701510 785701517
    0x303050901200d0c0302040306090b0403022407050a0c0b0411010917070b0a02070308030c040303030b2d0301021605070e0f090c010f0c061503051b150c160e010e0115 73
    0x100c91601c5200034404c1c6070301c1c0b0040c076600b000b000001407170601076510540c0c010341119400e0b113042d00780a41481243c04d0001241440c9800c036408081c0034020042d0464000e2605907100c004058040c0c400c3e800151014010a800c2d001704000c0000e5880088a802d0080e69518440d0f0380e01d20f4160101c985180c600f22064006010074400c1610340000351943d90348900c1141c1d0219585d0300c502440d0750060f901d02c403103001c00040500c141074140c02004000072048c1c6140241c1d071406041c413170030520b0032644203090f10110700c851034007645c094058560305031281000c601c0581f01841c0660361081d9612926040140200000d0160721012290a2043d4143c9026020030140070300110380040b2090049014411b03100081400b10b405031154030152200d0354100d000c5141181007451800c081c96061640c0b1440418019205880380e07524204110b10b501c1c6896110f07080c0a564900300003107003140d030305001c0d119803000600651065000381250450008032910766200c04820351014550505240171 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 785704010 1250 785702760 785702767
    0x16030e0c060409091e060e06070903020f0118090e010525021c020a0b090102091305010b041703090907081f06050703050315040c02010c0e030106030201080412050d09030305090120 79
    0x700300301600f000300002d1150808060545e035040c04c4c3d14003403441810030381b1025034500782400c90690404c001600940380d410000a02032840d0f002444a440728601c2c41d0400801c21110021800e4100d4200041d1403e440c00388081c0d10b02200d158001d00d01141c046503c210521300c000c00740074880b00090300615080d409440c00300410024041c24207940281c15045119a180c0000030038403410940d07009101030000980d8403880e800802c000700d0191103038002d41d0f524003c0100070001020080750116851354041446110494407250304501a0058481e00301d01c0312010049010b034046480c920070102003924111140101e4803e8410318814011000458000c02000c0003090082029660180364003120f503c1000a000209040d100041c0d08540540e4440000c11000c40c0c011f050318050b0310040d40200206480c540000b00804409000500740c480825060001c5900c40d9045554120b14000184611852858000c0c0140700c110f6840c44a546048401070b103690401c03102da00c00c2e0300c110108500303 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 785705260 1250 785704010 785704019
    0x6060307051b03030a1b03111b010902281212031a220c0206060f121221130f020103020306040b03070f0609081219051216030e0c0604 59
    0x64680c082e20301c1e00340c001d03004040c0040e28201040154400c0708988004544007421042184c0c0484075507a00e0000d2604090011aa240f242d205a600386900fa21441020043c40c1c450540188450440a5048001c0e050002c0c40440907000d9104919404020390070782030750315000e9502507500100001e00041c54003142281e00c910035001000b085101010f003107000040d181c0041c0c405a50f24440000119030204100d80c202c3c11441481c95408160000d01071500c0d24000242d0440d9001c902148503142480810400c000100420b03401004040c09541e942c901080b0460780c1d44080402908c00100182d0008203204030915810610a80c4080030344000001e03a0f0040d4040e400081070301340c100350703241807000d8541c0d02040400001d08181c51010f04440c01d180000f80400e203d40c000c0d440c99405504400890580354040310084121440d501c0034406124100b19207034401c01c10b18501d480306900a02c41800c4008140c3ca04506141e201080f1f0311004905190311013450346000ca074012006d200401 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 785706510 1250 785705260 785705267
    0x302060307031e0b1e010e12070e010f030c0b090918010b0d150e06070807050f04050405160306060201381002060109151a2d07110906060307 62
    0x680240550a003c2100c4403070310125410035405032918400743c2e4581e803800d035403824000102600c025003121a14101101c0b4400070f8a01030394034a80600401100d1900c800c001420321403107002e131258408114803540d40b2007100c144036000340020b640503042003200240050a88080354111074020304032121565420021b0282e1860b50b4501840a54a8031421401540c2e03040d2214082c034420b042100d490070469100344101c0d820140e100c03005a005009000315150170900d040d60001707161420781d40d038500c40314242c2d04a000c0c80c0d100503045410f2000f44035003002e89071002a080403442d50b040100a9a40004070b081e2007000404c0c01004040b400003101c0f000081249404a2404c81e51180b1900c000501048401c000c1e0900740300141c01c5400140014000c40c0541880a0031091801c04c070a800c25928104004170144280c01460002032900b60100d0b4803404124140003070600d8500070004201100115803040800f100d0403032103e801442c9519084065a004e1b00002d001682555034802c2c066 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 785707760 1250 785706510 785706517
    0x506130b07030c0204061d06090108030306091e13060e1c050a050c030d06080f01051905061903240509100c0c060f06150e090f100503070905090f16030206 68
    0x19020001d10f140740a01503125805800000c104080d07101c803405401300100c050442006e851b00b4800c03890400100320020300001030341e402070b80450700e01c200394071003a82d410b094045071500314800b0f9500d4010046105440329401c00300c0d03030281e2018490481d01086c240c0d200c2030740c8a1100c07600400c0000301b0035460310410150041280d1801e209103440c1d042c085035460341d00954511918540c6404d01400f52900600c240c01407210100002e0100b42010500d4006007010700d000c06800b26074900000f03441e03648503040c0c102e000380903001050b2107035200c0c2030108204001100340d04c0d030001981d60003424110300e4491030340700e40c96407006002e684c0c00b2010200013410b80c23a424070082100706900040450454801d0040107440b01100158491a01041407000b119000307448017880040c8078000c0082d202c0000741988000303000800040c0c1e0f60303451340804a40803a9040550144241c0174040391003821540300c9406000940216030036400803519240d0b8400c00a950740d1200101341070104012309194024 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 785709010 1250 785707760 785707763
    0xe010b030601031202032206031b02060a0b0d020904150501050d0827090c0405030606040207020f0d2406080106050a0f030b090a0807120e0901120b040602071a09070506130b07 77
    0x583c0d00c0d000070304034209403c180c56141f8100c0303001b2100d4208a81c2c0c0e00740c41003501c2920310580c0b2008100110f000652240c40042a043d88652541102d100c66036608141000c1a40e00800115041c20079041078001d4081584003100307140e28080001c580e6150400d07903c40503c5d84030050348d20782044460040814110215850702c454080c82500200740da030950400d05c2101c103190400e40301c614007010103181800103024540110b20411603a0051307182c1d0301d01e85007002c2056642d41c003149424503000440c502507505c541580308080c0e0f10019419615000071045990040c0240300c8191070320108000f0054a1140c5000c0640c0b8001c1000001e2071242a40d5002010005841c0a800715407100a0ac5e40d004030350449050422700d02049441c2c1e00410a84080c89081c0e85406066051801c0c42165200e600700103040e01600c00002010425550120307031740070358883c0320001204050308202540b40b009035031221042c001d0840220302d0b810040e05450000c2980d2582c1044640360110780f8226a200d40700 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 785710260 1250 785709010 785709013
    0x10090605030615210a291305070c030f0e010c23011a040e0c091f0e010f0e100803160c050a080631060903020f060c0a0f0e0604030b18010504060903030e010b030601031202 75
    0x803031889030001485102e01c40c04c1c81341c488640c10891403034018020ce031000380c02c3c2d0900280800d9000c95981c80380d24810210360001c034aa10318183c28080502c40301c11040d00649135800d110313050848020346402e246055409030f4042c00b2241c144501941c441c2c4030074149a41280090340042c2c4000d2455003895a521694042200002e84560a0440040c4241c109100080e00100100440001c0c0103d455100303010300c0d4505006410003010944900c9140c0401209003004404601440003185030407001b030030000c2442c01c541e40d44026003074880300111854071030048000e003440d6407283c0c900b03c0000f507581e5424814802001c5a600e010081a8100c01602140300b20718050250305800c100841c050780c0350009080c4c07034010b1040010010580015107004101e81084c0712a403039200c0000344c50503254411807103421075450460403504c0c14111180f0f903940307600742000c0c8018841780380c1c003104c02c0358040d0340c045c001c80e10340408040c2a900d40b1040c0300c1d01075004c20010808a0b49030a03c040b004000d030710 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 785711510 1250 785710260 785710279
    0x204050c07080a02030a090909050705220608100507211104180e1c02100b01180e01060e1807030f0209040204032010090605030615210a29 61
    0x2290300016402240fa8100541d00000c2c80c600c06a80050440340245a10741d014000c50b1465514192940001d101d030034015a8181100b290b100007500d0707001500c00030a541007141c20780d01c1c1c5c580c6944040c0300c000003002c5441e203004562424402c1a601c000070514481907070400c00c88104030802010000c0350700464036014400810f00741c01c0c201c10580b043c0403d203804101c0311800030250f800c0904014054074010602100304c41171940206000301c0c6007020800004a86030a0360068803184014113026081c1030b6002400b284440300303646030034140c500755036910707c401070402c0610000001031260a0b50f194654000202c2e0144240c0140e24922041500942009201004603003070380c21a820032148100b84a014240e50980301d000011040c2c401c0318900110783c0b6007540a03241d1140d40c015882002000030000d5041d0300c990100240312104000850b590301101250076005403404009a60544281c8004c2812025140550b10020545c07031103441e6000c032041000e00d4014480a00180c000900c003 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 785712760 1250 785711510 785711513
    0x180906050406140a02031b090d05060c040303080906070c15110d0b180c120c0c03270a080304090207060b03030307030902100c1709180118060e04020d0204050c07 71
    0xd006a5004070720404000c941d03c5200d5a020300b640c0b600a0130081c0d0380f8414400c00040c1c1e0041c000900340701c0340841500b580d803090351000c54000f0f0310100000d86941f03d03890503c0000105d507170003401200d000356640050341d102e1503072032916240245c0701400007072070031409000403075035041c3d0308000c41c0a4500d0006449160391400c0079940c00c19862441010b59403038904000f820030000c03e07031a22508150301e00e410714104040010500440100d0802416084001002001c0246c221082e81c80b2260840f40c443c8110050080780c4100008a84484c0480600d4480c0700d007090f04000c400d50b14100080c45c1800c2c28014040025004420140c860719141c0340c1130340007034409100035030280d41295808203082a03030f0300500a020032002d08000422400840d0000420905003c1e0f14603844800c50080d9221842000240c09244a52801c115400441c000007003042c0d0b4210304600741400d1180512540d507880c14414a441c0c81224040d4001c503d4101c0c0300b00500d8268002c40c2e00c400c90035245410543e45 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 785714010 1250 785712760 785712773
    0x2090a1506030b01030e0601031a07090b120a0606020c090f071202160204240909080904021303020a0501110312180601090603020108101202040902011119060f0c091809 74
    0x40e510420200f5641c1c4100c141c1d9582c107003e0050600c3c0c00000401e00b41d45035545074403841c1d41c008400180226241c021a50b000d100f0f11120b001000301e400c0e61515504500b10349001c245050310ba600013645000b02c0004c1036130000c140c0141e0390340c001b0a201e80c140d541c0d2015003982c0e0801000501040008030000300011031600c05441d220400a581040e070b840548144411240318032001c0441c800d1218000c41e085c8512964101034030307202c0c84041031700615843d11719a03500a0510450340700e4000b19040d903030001000004400c890007203034002a450303524801034644810030b21a800240d0810095100640181817071070f0b4111a0b00c0c1c00c04109020a002c0c65418990203805c8842c1c050b4075103008001303669001c0501600010041100d500e860318114201248240ca160000d000b80c1d10f80500c441503a0181001840c1103868000340c40340c03011a44100001c1e418043d40445500c3c0c030301600c0b09a140068800d007540309406d034a40e2001b01d0f003840704c2c00c000403074613035410003080740c0f40c80559001580 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 785715260 1250 785714010 785714051
    0x50d0b070f1107030501090b090703020618010e1c02090f070f0c020a08010e07140f090411041401060306170d08040b09100c030e0c0d050601180e0d081e04050a02090a 73
    0x105c00003d0006540d2a1071180031102511240c5541c5c4040c000b803000d80d451034211540c4001d40811400400c40d20801643e09103c42d45c90940d0288001c200c8941409040b00446e00c0d492080b01e0702d100d540c0d203030302050000d03190a80c0c145001641c03c0014060a60081102d541d9243c0014820450140d030345c40e170142564104680004503401400c0100b003841004003042240304421514030320b26040250218000807401800a0300f09031000030504010789460f070000808064000d9070400b10741e10b688014007d803119200c1c180758010b8016410b00301080106404d201d085032540e07003010a032a00c0e15a00420140a0b100c1700c240d004010400180018501c03984005008940340030500b00045002641040b04aa00d800e000300100c07003440000590105200741134850070701401d01c0d007090b80d10380e0f0401088008519145c2d489103000c011440c50704424903520901c0012680607404201c65403200001000341c3d0300601590011215000502c4e00380016544130024550004e40c1189408410740e4031034 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 785716510 1250 785715260 785715263
    0x5070212070f0e16080c0d0c0905030d03020306060d0b1302042408160324030605010504060b0c0307020d060207051f1b0509040b03071a03060901050d0b070f110703 72
    0x6205900401403031441545070b400030060324140030f10a14100384040c40c003800610002041182c1c20000940b00803118040da140b40c041c94604004d1060000700140003100b00f409404d00c81d104005040c0d803a10720034001c0b01d21800002d08090b0411400142c00c00c0038007542d411281d0700500744111000d5001d280c0c80500010401201102803640840700c0506000030003d07602d0003001400b0f802c000c0030140b00312440f040300c1c2c0786140018440c07142d01440344c010740d81e90381d10021511003510700106225460704564142d81d001c50b0100840c41d9106003400c1c280c42002d1081995400c10f01c203500151420340c5840420358003446000d8500354256884d5814960241c050044034120b20703059a9000d02e06103d0701e00c1802e0704900d101184180d420002e816809641000c611a944941281c40305407000d104000c010540c2c0759401540030800070510103030b070700211860341c01020b88030300000301c1d132520018482d00c09d03400038010b1803030b919146421034501c1c1940c0e4101e0140501008203140c03074002005014000d6 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 785717760 1250 785716510 785716513
    0x303041a090f011b03110f0d082d15041b2303100515070b0106270b1b010e0304082506022d01090614090a030801050d0305070212 57
    0x56150310304001126000050040c104000e01c08200440041301031903a03e00c0d5010b003007141c29075040740e042500c0c0c000d0b10080008140128001c3c0340001ea0000100750003520544c00070a50b65403600c40008281484002c5003010103102400706d441d88036580c000c0409040e01038000b203880030300112025140d4582c0c8a0040001d80f16900e2021a402a50820183c1c40020303580b040c950b007007101c0000c03180b0344580980352280b00c440c001c900030040d40e441110411948111800b070381d581e55480207800310101403140c500e1400300e5400100940c000c003580106440c58407501504040200705551505208528103200c2d56682d990021080102040580001c00d144d80040c4118007240303c001c0080280c0c01940d80d08440c0c1002c1c14040b0b10340108400b0440c05500318201786c00407058078907041d1031010b550b0400c101d51034200c11005012840c1c000e52480d40d014242900c0c25101e80c4201c2d0b6030380400f020013500003901e0742d0050000e8034001240e00001c07800303440c081c4e0070050146c000448070740480054490a = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 785719010 1250 785717760 785717767
    0x7090c080f0f09061602030c0d0201050103172502010219080319050f0402010c0c032103050c0910050c01090602040b0d11070503030a0b010912030201060f090c020a0f020303041a 78
    0x204800d0305486940000c0c12865010641800b84215940b1840174140d031000c0c2c6401010030203842e10070015a12180d40707080071101054058880a4000c00013800706072104030340c00c00360321b513801e82d26800c840206000340070b0030040c90060b52500d01d0003612214224110300800101600102d04000c4604d085801224455038a0038500b203c1c0311f28401c1c1d0b80c0000c604074100001c1160250021825985c8550203007400310400341c640c50300102446941d00020114440c003080c0720019884170701004010591070320100b11580300c104c0d00e0b6111b80075440c0d906512803003a440c451400d92141000d4804003002200206506402c1d40c3e0300c80980e00180c210961001000c9031120b02c500711401600301014405a0491811042d07494503504c0344801007014600c507071581003515059108220400003461400c0c00401407808a1a000b400380920f440381d2040c0035506040070036074100d81d11651541031143d030020f019180442e9610030308814201c0f8143d034180814803002806010441058900600410740310380e8 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 785720260 1250 785719010 785719021
    0xb03040c0f050103181118090a110906030a02010c0305040b0a020f01060501031b0302090303040510050d050610050a180b0c1f1109061819140f0604030b0907090c08 72
    0x7404042d902480c1058103102d0260018132031820501c81142d0404000c3d002032040c403004c00d242600d403403000c200394620a000c00c00213640100b40c0c1c0f190541308101e130310086800c180070008002c0058a080d60325401c640d00c04030042d070103018004141e82c440d081031420107035541066840b5804ca02c01090168200039884203030030100303110785006400242400c000901d036406240c0c030b0f522500225517043c55400100705c4003c1d9800c1090310002e200050039156841d5001d0802030180c0c0000c40f4941a1a0401003c0707041490700542c100300c135450aaa03441d06086601c0d0084074101c1c2503808034094030101810100f02144070100034449403410100401042000d4154000160307001a102002d440c503095804840640102c00ca8007080c00c00c441031a1070b8620685403259250580c3d40082d4450380b0301d40010040711403103100d5000c59180d81184074446454a050040b5010222119a80030000b084103000103400110b2007034001d0200d0085410142d1035204900441d841031403182e0108413088204030 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 785721510 1250 785720260 785720279
    0xf07120302070e09030f0a0e0d0f1a0c160f2111030301060801060f031e0b041121180706081510140d0902040510140105070b1b040b03040c 61
    0x2c004101d500400c00141c9082544030f0b417070f8050320010a0304210000f401d8200b09110381510102800001c00007042c0c1111441c007041800300b814401c0750100188a00c288040c15002680c40c4a002d804403014500705044181038400985520b0032039040b01d480768480007080c06003404022990003040f80102c501c03850b0202a00710709104840043c558010801800043d520405150444425050403a5084500f81050b0040c00784070b402240103000c00051007903260015005034100c801d0550701000b0040c0d100c000003940c0c0c03242d03075035808000c211a54020035039425031b42d0302588000650100c03046d0002c101c034141e080035110380c454400909080240314480c1445422090354010031920400440030040c030181141c4007200d02c0d420341413008540551100711640103032101a07070080c03017080310303240103600606000c0c8140121b900210403940c100c03000e94000c1e4100ca001680010003102c25984090f2140100d410305903a4288a01d01400700061401111000d0f5001c2c2d441208030525480c140100030 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 785722760 1250 785721510 785721523
    0x519030f0b0f0c0316050901050408192306010b07021f171e04030804051009051e0d080a0e0c10050c0c011b0602030606090604030c03050d05040b04090c020f07120302 73
    0xd640041d0100280b101c42071985c120182045100e0800f65251441c2800582e0306000d2903200c0400d9002d41e0794196940d922843ca51002d20b4411322078407540d110005202d0303550444400112185038003200060051440d01c20260001130310042520b08900040405040c454008145040c00f03d40c1c461542c1003000e070501861b0f0391189128034403cac2200c0a0001c16041040080c00203410b001682c000f1030103014040c401250542c40d1003038240b00c8016030b46400c2d940c80030f10282c00100b13814403000c402d07011180441e05040781501b541c1e4001141d11030040c2e50f0300070209035420042521840500c0d003095221042050101c0c0300c15107541c0e03103c5000071051f0703051010190f44030f0b04000c64041452000552002079902d0310307030080c0c00180c490b504c40c1c01080e40380c840c0ca805103500800c080f034000700304000c505d40071058a01c07580507a0642000c510303080c4d4040c06140501c11a420084c807042c8104941c0e070b0702480c01040648101d800c00760103030200c1801d10380d07d80c1203440540003a0103803c05042e0104902e = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 785724010 1250 785722760 785722771
    0x60e0f0901051b0706061a1b03090a031709040507080f06011e030c0c021c1b0b0a080901020d0e0c03120313110d050d03050601080c070c0519030f0b0f 66
    0x70b20491030024140d200c009461500c410705140085801030038000b10780d00c2540500300b52000c1548010309403030307140e015411841d515031528240c4850001d02c4a40070082e92000740002d810000043e0030340d0f603001c094550114800200781014401a0510740c3d840c080c16010314400e0300c400e086030909164168070010b0003000030307060003c400c000090241440680c400240c140e441d0000783d466044000311103041044c0000313035025003030f1510343c0c2d41c00948642c2c1c0540607104102001080c0e104c0d4074a0502100039210b4040200d40070b100219101340101009640241c201d0001442d02d007141a404080b91418110490b55500c0641e24983c0d5060420150030b6000019041324194900111441c0b0f612200304e00091151007000026601612000303e940d5505a010066410782416250010b00600049600da400030b024100461500544441107032440740d00440c0484c102c50600091002403d040010640034035003000c0b000010512000d01c4040d0710f40b08121000e42400d117005202d4180001402c0d = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 785725260 1250 785724010 785724013
    0x160509040201052b020301061407030c2a0311030f060f060d0c050616060f1116060605090703050901050f0606070b060f0d05011509050946030f050a05040e0910060e0f09 74
    0x2c44cad004640c1207522150441d0f8400010851102d5113031981d40d8005800903404025402c3d50008020402030b00c11aa840030802e808481084644a102d01d54546060f2503042c1c20ba070f140780c0415441e04280c40005011401414082c603890340d1000840c1d040c8d44941c1c40740044221300c04c07170f20f0104102c23400b0300750304540d2042e01803048003042000714042d07101c0c001c21000004080e6880b80200810ba17000350000340401404d07600b40d4540348a003d0040c1c4011904201503510b4034000402d045c003c1c41a860150001418003810042142e40c0c90307a20b043d001d000c05030f000300f103007040390b40c0f555944580244641c410390022412806800e02c4900d0180341e6002100d0041c100002c005001e2030019090310b0b00700c001035001a5600c01c2282e00c0320341c0402c07510001e00c000f400100b1203440d03601a120728050a48250344050701802c0e1420100c80b90300958601e040040d004000070002d400e0100440e03034001c0b00480940300d9100ca055410011076040d50300501c00c3d180b00710f08000542000c030400c3c56001c11400b0 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 785726510 1250 785725260 785725267
    0x610180312020d11160605070c09090b19050103031b03021204181103060d08071115041715011403030d0c03050601110706020a030c03120e030c160509040201052b0203010614 76
    0x178034804071302d140380a9001001000301c0d082050143d40d2031120010104040308200d00021801c000e440d00c03c4c1200e00d100852003291042d03681e250b45116160480390903039640d4007044482d52000c0a00c0014050941c1107102d210031004c0f10004003401000180140d00013150101d005a8007901a58810306915109a10500c10840d4a80341c07185080002035005801560300c240307a181160840c1400000346400003058003101d090f101b004030040007942e00400c00401203e4665075403642d980d210883c2e6001c1c0030300540041240c1d40700701010840e07107800141940d00b880700540951084600f0424108002500c0e0003c3c03002c1543c00c0000b0440d418080c40103000e4040c28940d02a50702c40b986d0314001c040000c00d0200d0824180700e0003500e46214440481030060f402004e0102e544d03a00a100020340d60f00036200309000b0210307680002d03030403074401622103506503642d1340042da40c036000a40c24400d00c814021100340d1201c540260035510581c3c0c1034006880707504110300202880c1c1421244503540301d080 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 785727760 1250 785726510 785726533
    0xb09090303181c050a14040b0a030605030a17090607060f06030303050f010b03070e0103020c100e010f0b03070312030b03160e0f04051e1f0609050c030610180312020d11 74
    0xf00d03032525040340d080c20b1056440c41c0f101c40c00c8440b5aa00180c07111104d401040c04100b2800d02001409030b50807564042c813020b40c9600404d80c480e208000024204108490091030841400700074000442d13001b800c07103040120303640703d0b8000c1d980b03440c0c500a0603d6549005008042e014814070b034000d4000090300703400e90f05140d202c0e0003602c4041d207940103025101c00140c0f82d03607100381c0480f00d82c1201c60066500850141c03038001c0140440000b074030055400e204052000074050301c600954400014000c0000506c1c40d02c1e010340d07002c25514403a00f0992511803d0032551001c20107078016144024404486e54a84540020380e03110150500e508001d0030014000481c070700181c1d0390580c1c2c0b5400800c2d2407480c214200c8500e0139442e64110700032400c21141c90740e5541842d5103d10304860328058248219035a92200b5007a511046030302c41e5001d1280300221503003510800c0829900c100d032505242406850352a00c42200c02c2104200005070b0081800380d408583c4010a180c03a544814020240500d00 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 785729010 1250 785727760 785727793
    0x108060a1b111e0d020d02030918091e0d1b020607030815090901020c120a14070c030c090b01030e0f0601060c17032a030405120304060b0909030318 65
    0x180003001000b868200744810904240840099000032640301c2240922481c4401c0c0c0314199140008050b0040996030010a8000300c111180c00c2801010030242100c03505071240c500c503010b4540200361040c0c03180d000d1000e204210140610000d04010b0140701600400241440c8040000c40c51500101e18040010b8487e0810b4515065250a0800722aa01e00c40c0215181c1c0105103800d43c403a4410041c00000b132019801024041c401105030780c01203603515401c082512800d030100c40040c00c0411a5850700940c64090041244240d4850070804d03903a4441031084c1c201c0350401055180e030b50342e424299681501c9444060344c00c030000b0b421031041741e000c03964031008140700751b505008102c86510108501080814801c00b03940074003035241d0030712520b204002c00020050900441c4d00c80031a16143c2d502c50306030703445a9400001864032848014110741c05400c0944102c401c3d0351120302d0f000c900e55601c08071a1148100000441d04e0f4034040c00041e030034605407841d401c1143c020428a2500901 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 785730260 1250 785729010 785729051
    0x2007050a180f020304081309060b1209011811011d030703080f0d021201090506010c0c2d030f0221100b12060703092901050f030c100807080a0c0c0609020a08070902030108060a 77
    0x805041c1c5c00d030380d81c41400331805003610446078a85401411840010030041c03007800c40700c8078002e0360b8201103608550445012040d0890469070b15920450b800c2000803810001000101102000f5505240d0700c040d00c0300903a044441911070a00c5004010b11040c0840d124403030b8000000d2070290031080c81c94681c4d00d1007600a0080003401520101078058030b551504031000200300e14000d540041b42e40c1c0c20b20407101015505d0480c8144a46000030824a00b503241c0d04d1090108040588446401c00810307070010514000103e0b04000c0e040310f0b42030048424000c0c070b480f41885803008900d916240c0741602009521091341c0196400c2000424201040c202a19064074402d90794a0aa440c080002a14224081240d158464403800e07550780559480b11016010302c1064a030301031360b6114102200d06503a0304161030340c000b60f24050100c000c00c406420140311940050070b01a81c0c40e840c1c0c0980f41c14019a60407100c11a5000801004020810010ba943c030034881c4070108150300c0350020a001480 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 785731510 1250 785730260 785730277
    0x901060c0519200f061201030218040305030f1003060608030c0105010b040b0d050612030403150c08071b02010309080301060201091b06230f0a2007050a180f020304081309060b 77
    0x2031148070b04520640310001481e1884900070940386d15860000e807803a1106c5002d02080780101c082d030300091696500400c03010b00890f1315450307690031076884040803480414000c0500050010b01017000010514620911019002a40245680c2c4a060038000d01313648040e480300203040d0040204020400500d829200c4844507040c02107400e4440500044c049012950241c003103000001e0300204100040b500a19000108101400b074112008025200391001b121107501140c00340c04003850405920710b070103207003a105050000f8075260b01d0703c0300e07012500240c02141c0983c4d5100020f00a00c16040340b87c41140d0040c0b030742c0000581c14000002d000344800845000713134401924800c482d2499840580d224540074914907a141d11624000030074852001e11072030b001c803000c1d198000703950f4004102201915000341c40090907901c0d058040490b80c9460200b40c244a40c4c0e60440402c00c1010300085004178005e01800703451711404007440309070414941c01078100618006041240301c1000c002e0740c2c0d0741c0c17 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 785732760 1250 785731510 785731553
    0x70b06010e010c15020c3a090b0f09060d0504030306060e030109080a051312051609050603280204050c04050406060504060909112a01050703060311090a0b0901060c0519 74
    0x402035050380c9442e2010440d42e000491f480d4500f0f4210550a480c4c2c0104c6444509105003000048450207541c5110a8042d42d05100740410030703d0380818400300101581d00020b4511407420500058000031176400b541c04070006600c0302c9080041c1a8011034aa00062049008021407592a61070010b10f200301c030700380024001c0c042240000c0228040700740e00248407a484105103600d0f03d04c0d1040d183e00c815040c10310310441004c0042525101c0c3e125141c42400050001d0040c2680c4600e03a0910140702d0a10785034403610041d0250042c0ca80340a018001c00000e08a9612941001c04000030388045400c04800c000081c0010004698000c2c2490b003290a101c100046910001300b2010703851241d0048082d18200d0085941c0080e4003801811100c2c4e1070b042c00802050700c6280046041d07696510028212500700020b5290900d4070b0b0395083d410000c008400a038400b5010301151044038240e10020100d13a0750310004003400300500689c211440c07847c42500d036410b06070307480486002d280c2d403402145 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 785734010 1250 785732760 785732767
    0x618010510020c030703050f070f1d0a022505010f0e0604030804051518070504020c0706030f0b030105010312020c0f0d03032d020d06090b011b05010f02070b06010e010c1502 76
    0x1402c1c000d20105015030b0025042d81c41d0140c40c0c4c18007541c1c03000043c40305980392182c00ea00003585060706801d0000d8640d0090700e1002d0900940400c000102c02910726010346500304a41900310820620710001141c1009814402043c1c0d23007041408c541410501d0160241014241010404045082c0c0d0380315a0504008000740c0329401d2a600e800800d100c0326281c0310b1030400b4085049a008201e40401113400112040e03651940c0601c0280e000381030b9140f07000d9004d9102423100c94020f070440d070400039115400080c0c2c0007140c00080d09564082e48140c8040380310300d00d40ca404540c14004660813a00590f8821030036030b01c13000400c80303807070a20b0000b030101940da000c03440105078000c0310a420503811030a0620305d01c40c2c12000d04000e51101444040d15803900c0000100e42107036001b21032158105856250009030f4030f0100001070703401b44030101e600b55640d0102090041d16480901a4640290941d02091500c907001500519429030564180141038601c20000b8010b00d0600c005640c80b030700c001d40c8 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 785735260 1250 785734010 785734039
    0x3050d0f020a02131a010906020318040e060112201f0e0a030c060224060d021305040b01050406060215150103060b16050c011b0b07090308070c05030606180105 70
    0x2040824100258018818410746050b400380d50001c856450700170681d03090700c14030400150341c000e08a108000c0960402d101d142c680680c82809080c00390030240c030203d8042c0b03140d801903041607426048003022020750300c2c00300140b1140009403144180f2070010404100c0f48000015400c030780420484044003819a144000c02c0d2090070004401400588107100b00b41d168540010f5013030250250400601c244a03070038650941c1c032003c1348442d030311705c108400c0d0b15198101405a181c400308000c1e60130180070565400342d00d42c03d10405124600aa00b40941d65060100300400e4070380c1a030101c0c086600c1380300800c25002c0440381c0c0c01d8000d440c5e8258003414134643d00043e0081c111070303400076420007008243d0511039807442107020300f0749200341c091b10040c201c50300041d1642c180820308070500d051b4400d17816001800900000703812200c1c0e400c15000c015071703d948450203035001c403001b201e005aa000d4208606c0c1030400203241c0001e4215210020380425200d40c41140d40b0521900d48107000d0300c4140358 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 785736510 1250 785735260 785735263
    0xa031e06020d0c0e01080a14150604080d0e0112020c100e0111070303051f08070e0901110c0a0302060721202709010b0a080601021204060e0109090603050d0f02 70
    0x1029400701110603c500303268114043d200b8044552910b003c00c3c0080700142c1d441450b071294201e6964400d454640d19210f00c14a160252900e9500ca9000b00080102203643d1400700480c04859446a65401c10801c00d070000421404c24004d5030b002c0c03140103200c4d00480303680210b5900400b1001d03500008018044851060150034001c41c1c2c0071030540001000818150701d500301074803640205180a0400c205180d483e140d810f05403150360082d07086254148071b2940300c03860094000c90020700200355031009001c0940c10744c1c02aa40070545610050100080540500285601ca612030030079900d8a01d1113080c9a0910895140d10351b4065a10700c40c03d0499803c2c0302c40c1001050b40e03c92800c0e00e90140c5000c81000c072020440105c045103145201c07904501e090582241691508240d80f0f060a50800040d0b81c60340c0064105070550040024203502000e548018000500c1542da1f00f12003010b0740000909803c0702c42d00040700b99400d140d0144045500014480c40c00784440c40c2c1031001c0c100100c4102d = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 785737760 1250 785736510 785736517
    0x1803030813030215190b0f060301030b04031707090801230c070512070c030c090b0310090f0b040326090a080702061308070e061905040b0612090610050a031e0602 71
    0x38201c8410748005d001000e05154443c00c0c0ca0b00380315070200180e00c2074001700002c03240c080350f8940d1300040c200014000034401207103c54200c2d119042c02c0e9140340408035030302c2ca00b0b0000c517804000504800010441e840c400d002d01522032036000b01134414140181e030044e103504030040c26050102c2c40091f0300c004002c001c0241017080d180d000e0140b07445200914001d41007184034881a901c140d2419004948540c05100780c0000460090091032006200c2d0f080d00041e0a0070b400c165030341c14001a600000c9188500c20703a104911a94845008040d07002140074401911815114800e40d60000c1061401000400e14000c5070416001900c5042d5880001c400388625000301e26840d0222400103070152000a03820b040c0c0d40301525000b034654075a000c2c0415118000000c5241c00d80120040150741800d03400404018000350002e4540400c50811001180c0b068403c4562680200d040241d001c81c5040000c001d01402c650005440e03285484002e40c0d0702c039005a01400082c0c50900a00700409a03048 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 785739010 1250 785737760 785737783
    0x70207210510050a0e150106080a1b0f270509180a06091502030f1609050d050c0306070c05100e100e03090f01080919050c04140718030308130302 64
    0x49031503600359102c40201404007034415400c851300f0000c441c0c959034000700d02c100b0b17040c03001c0148031038a0b03103080030440380094007038a0388644580ea0403191446203400c502c1c0c0b0b0120034a945640800383c80c0704d6801031980580d80c41000d40026080c1e0540d028104541c00902164130440b010b02e115110442e0b0200030300c07416401d9040700c0c402c070003104040140700e4001001a90140c400c40b06a01036212600044c2d1204862b040900314001002401009460403001000070399844c00c0e89030592244046600c00c01c0012040e0341071b40c010311414105150410526501802d41d1624010150300356581607038071540c000c0800311140d210741862402e00010084e040364224506c0b0b0511000b1002c052894480d0310180c1240c0c00f90f1004901ca104650180140301d0040031010000c000d00203c5d844029404040c11310221224001c80854114550b50b500940304a031068502c00480d5040141014024071012000300c003640c00d904500700042a00646026444440b180c4610300724212480e089060034101002c = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 785740260 1250 785739010 785739013
    0x10e0f03010501080d082202040e0115061d030d020d110f0d0903110d0206090d080d02030108010204080601060f2a0b0a1b0207150513030c060804020f04050702072105 73
    0x1081300c00060320503a199083d44488080340c540e40900211960b0030050010f081c500f00c2150001030501e0382c072684983c20243e00004003040b91090a001c0d1000c25840840014580702e0800202c48600c103c2844100f0300b20000c040324501458060b49443d00c8003440010301a510b54030390b01d511014003024803040c084030151000484c0101b0003a1072a4410f003c213403103644034a140410704e03050805104c0f07040c0b6001000c03281011907a104010468441140c11280c40c2018011181d02c48080d00265018140f000009a00c0700d08120b842483d29105a000004108c52240c089810f5900070303210030050800b402c0342d440d111551488803029241c4c0024003c0402d00344004110703204503aa405840e00b0707040e02161000142d66030a040742d42d15801d001d014070300001540c1c4040c8940c000c0008217170403402d0240952480e5540d031980030560400354451030114051004100851614000e006c03206a0100c8003001a0700784298000d585036102d0094000880c02002d00c1410045103440704075009a1040 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 785741510 1250 785740260 785740271
    0x41e0b0a020307090e0708041410090f02090603150a05040201110d031409070b030109050a060503070f091107080306010c0602090d2604241206080a030908030414010e0f0301 76
    0x100c820000e500c216004000221602c501144010b80040580d00071106075882401c645c43c0c0d5142c03d21444440540900144a4403150314000721703e81c005c02c40da1a0152000d00c5082c0391500602814860040c900d41c82500000b600000c44220700c0000e94002808040c001f1307580d5141d1005854901c16001102698481c01d507058540c139901d50804840b896100113044c1c0507403a100d694540e40e94003801500c071401c0d0244010b1160a8565010301d910131408100407802d00d55440100e428169a9081381d114036010010174003441c0c00a00804c001d40d031580d2041c0c1e1900059840d00c041c10700014050718100702144c80c0640030301056406894803036000410450030781c070300e0307103024130034103141141c06c0b43d240400c01d003030603070a60107a020340c1c08890076100c840948440d40350b51030410300000d6031104140140c003502d000b50458544034101c05810501c000307160800b190b08004e010729132194030141407541b041006000c0104280c840c2030b00544203003004c10901c51007100050b101078030a40d04603055803034038 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 785742760 1250 785741510 785741521
    0xd120207020a120c0b0c03071e1205030703060608010506190c06051602060c03060307030f080f0f1b0f0715090b2b09020f2110020307090803040e041e0b 67
    0x3c0a1600b054071030203058450030340d9084048554014804110f9980c0c0052000d500810201094000003401c00d04030140541d1a41d80d5030b841c4081001101c0c400a007000c410000026050f128160141041c0d080c90241c070b40c03406000910b2480b4244028440600b0140003408542c02821602038656114400f44614600a1185840d103148040c8020041c0310354008264055100d0301181d00400000c3c0c0075001e00740c01d540320040c6a19602c9400c58400104200620150786980c010704240301d2040c0001d5610103484048016154110400c05660b402c07803074111840c0e80c0c0000c7c001c0110307071f03903c881c0e00c550607900d100958412076280e228002c000d0300000e07d21070040f201070200011598400c4162170840e9000c4403001190b8120400170b40182c86221100d10b00e2904940009202c1a05001d000700702a0146000703007000500c015000019402000340705200e50452251000b40804100035414103140031031444a002000d80040e00a007401081081020601980b80c41c68070380001c41c00070581001c = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 785744010 1250 785742760 785742779
    0x12103020c1f14090a21080c06370e071e08010507091406091c12020c030d0215040f120c0b0a0e0d350f1006020d120207020a 55
    0x64107030b140024107100c0b525010f60f0389600039150003d0780941510034607400c0070300d07403100d1380130600340700392070711544c3c920000000c1c840c1005114501104020b00b4860801812000c41600080354400e07203c0d2460030401e86003009120300c80744d100120326001c5205144c3c00d00160511a031600700214441e400504242101d400150880454000d00300030802c40c0d0700d07803100b1104d905042c01030a4298400c2c0340c00c0e0780113207000000f0b05001000140182c07090030500c1d01c0f20030801c4500390211400d0301e20800d0b4a51258041c892200e440c06e040c0c014200c0082026002507c0701c00140061248009500103d4203011641200480c961703407015019030300e61044400030f040c000e82110201c9108940c100014220031890040d41c6662801c140100001100b40310b0980d610f900300180c0180c0f443c805200c12211603810040056640389889160166050420400c0310382080140b152040c1c0c20729000811145500142001582c009440c200300400004e2400502a00c5500006540440d0650010580070003 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 785745260 1250 785744010 785744059
    0x10e06070605011403030316050d0605041d01050a0e0d1803080c0f0d0201021309091406150108100e0c0309011b0f0e040e061305070e01090b0a060305012103020c 71
    0x4108440d00c604e141e041080582e644021200b540350720343c0c202c144851203400360015003180e902411010591540380c1002c9421030300008084c050091000c00508200e100030301c11190050002d0b8005e00180c40c0e50788400d80d40b0f052140d0142d00700608030301e000031210380c2480200007469010301c07415541c04004a0f981c0d42e139401c250102e2202d00515440784211030051080b00c1e4071482c03110200c14201e14208106004040500d000d507040c031800b0081840f000c41c00c0c01820300c14071040d0358114280da403440005003081e40040a0b107100020741e03034091107524480b00c07003140c1c0441c112408175a287d0b2007000300f5000d4021005503803140c20030f83c40e1400781f0740e4004452a40c124499616801d110341114104002e44103541340040058005202264080920300d40300e09505000d0b108071400a540d078036032512404004d0b4040d9080325501c469421452800ca20410010446441c0a0000d54105a080411600940110924030350f50640031400c040c000d01c1031007114a0010802005120400707100c00000a = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 785746510 1250 785745260 785745269
    0x71502071d06090412030b031203160e06090607080706360b27100c090b18040536070b1c0c110712020406170318010e0607060501 57
    0x203041007030032800311482820300b44101c0c00188801c4032500ca81e11a2540a45110304040406840306490b00d2142c40420032540c0c82040d0040d684e0f92403520401e02070b01d071507010681408100300e40502c0701c410f640320015180d071401c0c11a02c46944034500c0c0360020035449440320082916080084242e114400710781062400052581c5035900070511079141c03045107603c00002807080d100c0502084c0b43e451140c040403003050703d200402d1014121258450310740146202c5034240c258480e050030540707940c0016403030010048104018200b01c040b00c0d50011804000c0e08150040360388500052941074804485a0a40000981c44219002500e010b08075410b1004000e401c512881500252808900003212107512500d40b14040c61041201c0c0b24010305180d101030400c2201100100c59002020700228002741115148000309007480c0c0706000607200313650701000407000d12809504d14600c001c0300321408010080c07610180031071101e005075000002008400e80281e80401c041c0208100c81d030000c1c5c140e9 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 785747760 1250 785746510 785746529
    0x30b15040e06010c0f0b09070503030d0225031704060207080a030e0f0313060810080106120c0f06200a05010501080a022b0b042612092a010207150207 66
    0x980d100d00c01904c1c20300150b240100909815140e04000c42c10042926400200c1c56084d141582c1d43d4200192a54205560340004141d000030090000b903010464080358860455812013890346584016013120394801c3e404500002007070005003004101e90490f50b000d80d100d1700140c0c41d582c007600020001c0c02c0b0041c01031303103a02c5044145034405c0c10000903201d4521008808a030b805080c04012107900801030821a4808119640803503402c07828041c0c40041c103d049051260a142802c01d0202000c0903404030420300c7d441041403054a83c4064a240347c40441400c10111000c0c150301c3c0c45c940000072602030019482c080007c18400000b11b80303408407500848201c4403402800c1020160717003490f51203410b00c01050b40c00c0700d400604d00c2c412030340c1d1142c0240c2c00c1c448604030700c2c0c503401140c60308080100201c1c1c00c0000c0e64000011010f200301d404c500c40c40001e006150302a940d2a000480884ea80c141d56001c0745204110385e8801c0046002812400c00c0c0c103200c044c0c82000103035403019030b805070151a = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 785749010 1250 785747760 785747789
    0x2090301021c05070915050d0209062215050901051c06060503071404180b011707050a0906081302040e03040f03110a060503090a0b0402040b03030c1b04090507090c030b1504 76
    0x9034454004403080c4c0e40c24800040342401e1030402918584d10002c0c0480d0023603000d010107045541c0313820103024829070703440019440c1207a4002c0500003020035044100d21660740000117669980c00000d8801144003030800030382d62104841080c0c0c030b000103c0c0c044504a424a080419140d50141c040d5000d01425111485490303081000b1030740c240518006d10038002100208402c111040b608080701c80e02040c144445c056103c0061003e0344881181d002001c254005144801d00e42e00c0350700c07180140a145005c000500b0000340b2a02103400c00c1c4070191043c0e842d804230b030444040620849000704800e605d07490245aa81ca0040a00584415024455884070750005092400b5204580c80b462180340503100c4c002090f580d20312401c02c09442603030020b5960280c11030b40c0e1410030080262301c03481c000402c0c1502e214109a070780c625454698501030b6040104080010710b00140744016a140c114010414104c455001c40003000580f0720180e01c1138814050200d250614001041501c240c1240d400340c = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 785750260 1250 785749010 785749021
    0x23160306050a0302060319150e150109030b0609040206040801141005040b180c0702090403030f05090f15041509150e070506090f040b03010509070512060405031c02090301021c05 78
    0x4074040b00e0300c0040d420900400000d0002504000c51200c00e03d03510b400090300c04035042c041d50040c107240d0450b0014100e403c1c02d100080d07070914401640c81009103441221141107a5905800d020003400503030050109001003401c41d0742e070100340d0b406047c002000b0000b559401194100315482aa407030300d0a07111749030700421641001d004250000001810404004c43d40e4691b03030342c54070b00040c500d03403281c5800d0021a006a03105600d060080d402030b078000c03603100844084c0a049a1340074018000d02d07400105149034900740810300101d10480034005403d140d40342d0900c481c4c00c21158401d0100305180000e080100305480800e41e443d46031184080041d600040d5081e540d80c820342c050641c1c0031b41c1c180044029442c007014000e42c0d01102a2021400d0381c1a080031a09503101030f0745072142600019418081400c21002604813564040000d0272541070a864580e00c1b4030444400c1d01204041580c21401c102554045419403e0041c0017155918140c45074051a1900c0450000d0b019081201081 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 785751510 1250 785750260 785750269
    0x33021e010903390b0f1f060e03070f03030203220602102304110301140103120e030a14100c020307031e020a060504050a021008090a062316030605 64
    0x40110398103488040c40c40080d00700c0e80b500f43c00e20b5007025100d541c511032484103090036503074084440b0344111058183c80c2858a2803644c2c1003c02010ba03082c201c0c170005000c080d414042031050031aa010308001c4003543c403a102090411055400100c0814040c0b1000070805500000520b0395610700004012032401c0780c01864070812a600c0b9a50059200d130194485c00c0fa0194041701da442420183c0303802c2000000f5201d8240d00c0c0c119800c4c0d03158403136400d8207003407420203000703014903c0e06041d080441e540c159600d418801d481d05000c2d400300203a50a0005854800300b0610506c82e4206e42224a0808599001580c441c4a8807903000c607607040000d1074800c030340000151a065941601c44120035500c0140c1a40c480c691451000114444d03800e00380046100c03403207910300480c00b407030140c40100701d40c1c0140140102d1440c02601040440390800409010220303200c98010392010b000310b00000c55806403520050000d500c500002040424007088014540c1c03180081d1501c0d4505020f926992030400 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 785752760 1250 785751510 785751521
    0x30103140c061801080c0705010c0206070905030a020607060f06080a200108040201080601030e250e010812070f022706090606030108031c090f1b050f060433021e01 72
    0x30307040f1000706032009891340c040e540d41a402161a4069801c1c0700f200d407034503401d480707081d84000090f03000041400b094560141c0c041c405090300b40c0c02011580da0540c0030507503078816880c014105943c2d820031a44018000e41040004101c540e0403034802444908001c00c07107000900c007440200002504a02076540100b0105108540584406086545d854015009002c0c3c0340d4a00c070b0039002d040c18040c2400c1c0c080502401c00e502141d03c0c90301032807d059008406510603040080390360b210140341141c040d183c40072500d03102e40c0000c03004200e41d00c500c00b0401a000a00e50814400f400e00400075610f0225142944252070464040459480c0c00f000c0c841588000c0c01900c400d40c000b084580070304e09070301d818201105800b000001b04054942c0b01c080e01c035801c409003180c90804010007014000d4400030303040d01402084440c0c91503644114005161803150b440f034000c508400c600041b520130390900d44140005914841d0003810880050001d4407045010700c040c4074207a0280242c1a0310700b05100d003 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 785754010 1250 785752760 785752777
    0x518062418010902070c0f060504080f010b0307030305130b0304030e031509031602120a0303091505070e0103090206130806222a09020d050f07030b0d15020f030103140c06 75
    0x111140382d0078103007418082c1d481a602682c0d08000d1600000340c0b02181c8182900030823181e03803803503141d0b410400400e0034461200c0b10250940c1c100040743c0c00555011600314120b0303906003000c640d18800b0070030100c2c00704803503441000d00030000b00c100014150421901100c40c6803c03000e60380703100580341d0b4820b10590b080e642030216038018410044030202c40304180140d50300003803155525112030400d9a15000310402d084001a03183c3e032506041241e03482c0070048150704840240100c0c5440b4100514001000c0c501e0b9040603201c218090a40d140c1c01c00702e8030a100c81c44c0c0031290031900c550704e50b55285030550301e2080010409640009003520310903242400e0360f207c800042003120f0407002c10307000b40840d50348440c030300e440b1800024105000d10040c019581c11a602040d5454624080c0003484001080a82450308005100c1400e40d50301001d170030308540c060070302d0406044101c020402030203400c2502d518804000008002e0201ca5110518030800b04011600f20120b00401e012460040300007 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 785755260 1250 785754010 785754049
    0x120e0a031e0c0b1512010b0301050f040305070b0a06150e0f040c14030c120f010e0609010e0712021e0d060506271302070b040507061d0405180624 64
    0xd41c0c20000e00305289444e048080029101e0850005100084c801203000402c0c0707440369520520359200741420f004185e48940003c002035100c0c40c0c584c034084c10921400f440100b00c02410700001c0c03462640c40c0d01480181800400a4003c0c4000510240c5139040c0f003a1458400c50040c80a012940341a001d4090f4038a410341e00c00c0702c8500c5e03e8410b10469000603002201a01c1c00b4041c140800303190784121407088008160420007549030249810786074030046d04090042d255040140302151034400c040742c001c1c000780b400f01414901c40701071100a0182ea5100c000007030661007200b02008043c80500a48849000100401c079618020000e00744908107c518400c00161000c403c600c8181d48545a650301c0079009501d070081a41101c0c0c100c1e48030500c12500311003000140000c1c40360404c0204050080d41c00c00c04074002c40c04400150b0b05044441442c891601c4400240d40402009203040301c94201c1000c46425040ca0040c206418006810f02c0c038401d00d41e801c4107805840c2c1400280b07600410580d = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 785756510 1250 785755260 785755277
    0x7050a0506071106070f11030105010b09130608030f07050c120c10020a0218010905130201020705040e0c09100618181119020601050f010306050916120e0a031e 70
    0x6000054109100640d0ba480100b01d1002540d10303500c0c010190305114491106121046185c8035030294484a8098080c9e80b5040050085000080c2156592101211040c24801c08044280d02410960300004410f0001140031400b2500d44405010441d209006458000c84500d06015030100004030146041c0d010605941050400026038a0029050310685480480d03e401003000380703440100328415204040b0041103480e0851185a030800344802c41c4882c480c0305500000d43e680c1060260510880e541c091418a08204111003100c000015200074824034240a11014a000c00c2c8903a02c040340f006c030540741070102902100310580b104440b480d01e4980d5600d40c920010000207030410003500081040c40b00c0c2042d0803208045a10721a4020600c0e9030401e006d029004400c2c0300700c0c0d0b06040c10080d0910182e0340e14241d80303621560040c0e40304001c1044881c2220441c1c10819110940c42ca000150140c140c0c0c0801c0c400440341c041d0f04c07882c90174802415058082400040501c00003003510 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 785757760 1250 785756510 785756519
    0x7061b0f0e0d0f03050307090f030c06170f01030602030613050a0606140a0203040308130801090b070e240306040902060703180605030708130c0f140909161404090f0b040501060807050a 81
    0x54014517004031f40c505c4c103080300c10384845008000301d45941040d29017084c0d000c420098079500184214000010344494540c0341040501d0f400020018080100036640210001d5800c0d1108411002425414071081c0140d041c1204500014031b414000c0d4000206500c1d140841d00c0c54081c00c81d50f442c2d00e00e5000798903092864440311403d801c00340c10100380c20401200056035139000d014005419020300c94080690a20000c054040840301086c24000c1541c88003d64401c080c0340400b10100e058460342c0782e9290b5909001130014040e840c0c00070362080022550100741039100b0045d40103080c1c1c08902070801a1102401c1c1c031940801c4498000180440c40021906d00c0b50160301b4041c14410a01500340544074a010500340220380c0080661a02d200d4040c03000d85440c030700c401c0d002644540500b03828840c0000070352901203540038a00006030205508050394540e035002e140041c0d0404071a042c41c4069240c02075081c0001c6c0e400761400e45c01c01c2008100c3d01c2c3c01246071300c00c483c0010700545100c0e180 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 785759010 1250 785757760 785757767
    0x360103150c0e060703031e0606050d020c19050604030e01020309131503050d0e2103040b1c1a2701260d020604170304030509040207061b0f0e0d0f03 65
    0x1d50182020000446001007180e01c400c0c02404e0240d11070703200402c01e12002c1c0c2c0c03101800721a0000b1402ca05007458003c000c02c5401c0000c460400c0140b50000d80d4881c0300c0d281c551303d000c4d016a52502001c1841005105021000c01c846004600c26651946042c0301000120303942e00544000940c0481a04a060454003c55002c40b4482000301722250003c1da4a8072040d043c00c11260351240807a49110b00d10800b480d0920b1031a07015802e5200c64003401c42e44808890352405140134090403000c0002c0d80d501c41440c40740c019100f8000d648414811542071800407211503221024050046507410501e5000700801150b48070404441c00070490a680780c0111a14080c240b90b031a5590080c041101200c2c001c41840011072590103500249011304151800482d115100840901d00081c10320921001940c808229052502c003213401503120740440c20800000c10003c00c0401c4045400465a41460307080f0400754008400c60b224807401c41c031420284040011070031802400c0038912900100020700 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 785760260 1250 785759010 785759021
    0x509010e060409050607050a023a0c0615141822050303040f0215070b0f0c0d020d0902040506040b130e0109020a0b19091211030c36010315 61
    0x401040803c0c111100e4442c2818401e06551150024800017070040c0056010440c1d22044030554010b820f80002c0340b00c45405c41002c0841d00c880e19070a008651200c00e10400240618039000881040300c4000d681440e1041d4845100e0315407044010344600034a0b140ca44205425105000d105011540d41e1803411680680c1c2c50101015011814140d040850000c101035885a445031168521415040c010040a042450700e1141d20540c20000c181c00164013111b120313000500500002c03aa82c981c255105594050b0180a8000b94804030f44070b07240180c4c642001030964000d4608110503110b41042c00207a54203000400c0d040030039101700722401251540145190b075100c03000001c070014241c1c00102041503d80c004000d0480100320344000c07c0043c459052159444c1c01c04801d0345144c051107181980000b50040d060031495080702c00140c03424000c021a88500800701c0d145911004586002a0114184044040c000c16100711100011030b03441070580342c022406498041607030100b07a000c1d00 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 785761510 1250 785760260 785760271
    0x11121210060f0309051f02042103090618050904051516090b13030b010f0608100e0f090a1e2001020601120606211e08030c0c010e03220f0509010e 64
    0x401c5d030160780c0c0c82d074806c01402203104407640000350365981780c05050b08640307c4c0e8215802d0400c01039504100069040b02c2850100c2e0540e0400450210481d0381c2c50012943c11390180d6003006501c1308120401c84003003003013018542c0c080c000c2c18141d143d10030400d100c2d0340020312880205c3c541c81001c0c4103064841d00606049018850182070311512036940491842c42030388100800d0409060910500390008445540020301d4060000040d203849a041440880502000d010840d07403000700b121400184000f4900341c1d0000c601003c0d080c05a802c916100c070443c68182c034100c04580a16aa40b0103d00e111580c03080140d000704030030b90900002c0c01700c1c1c0f4100402100d8082c0d0312030b800602c0c040140f8004038503041c03002402c28038020354204801200c10b01c400b00c8551007150500840000c80460640f9000716000003019168000b4803152030052107501103090b400e21001c5020711000c65080690045020503080130030806944004ca40412280b50081c10790054180c030041c4841800c1c8404190b101 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 785762760 1250 785761510 785761513
    0x807090f270f061d0402030d0c060209190501020709050c031f080f0a0606090209090118200a03060b03010f0504020f19170106050403030206060405040311121210060f030905 76
    0xe8184030262088407502040703001e28907220031080003e1200745a1034020340c60192603804d8185095400241c44891452510042c4403a040800c001c2c010b0f0382c3e05445480c40c010344188070b002600c40384442e0302c40542c82180d0051042035808100c80030310780601401000144003003411501e58004d40d466040419000c041d040181c61070001e490a0100206040500d40d075000d840103581e40d003894002c0d00d4094000100460040021030700c2e036182d00e203030f50707045402800f80b25030328003441442d40b000b0b090403211800071020061403255584910314000d1038001d200c1d840800640d0307a151103098041c0400d01c0f900200c08441d070000c00140c189074004094158041c440b03e0700e80300e0b100c01c40b80003240f2800d40600020f1500c203135091341c0c2d16140460700c3c09421107003031003806d140c40c0d40c3d002076440d8001004203000710784800214081502030000300054410070016904100c6400310f1604503500400d10607198490080003080408050760050030645030540d0303c0015222506100b41d010345004481281c0f02d = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 785764010 1250 785762760 785762819
    0x3030903060106030204230d0f06150306020c010c0e090412090b0d020c010b03121b03070c03030807030c0914010f0210110418020a1e05120f070807090f 67
    0x940d01030104a020340101d85005803100d050140b10a6480301d1180000c80f0010151030380416540c980c001d510b040d95000c1d03c64412481c07149420005001841e910700d244140310300d404003c00625030080c05103104980000c00c918151b201007180c001034015411508400c40e600403c010a505284c41070304140c460900c0310309150b0b10040209180e0242ea000410f155007c5034080c0505402c5c000d080201c01d084008004d02180350380ca5148d140710b06681c2403801c8003202007510900f0014002e40f032126400940c0c1d08607166980c06d028102400c01c8038010006450445010a0140107005200645600c902c144801c000c0900040d07620403400b240b000103501c2044288010342c105230280084402c940c1241c1c5403520702e00180041c81004190804070f4550050203601c0031568850080c450380c1c810315100e442c05100f2035200341c3d0107200710040340360031005510400c200c184080428034001c036015603490f000c503070300c240c1d040350160624041c0f582920640c507030070000000d8a140c5180b03214080c4020050 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 785765260 1250 785764010 785764027
    0x1170f160e09010f061e141c090303020a08010801060303050f0705032241191d160e01050a0908030d0510050a14040203042d020f010c0503180303 64
    0x1402d06090303000c0c00c001c1001d41400d00082e544000041e07101c40c4404900903040c424184041c2c980074070300f00c001100d0107000c14500910b03544007000070030308013248208001045403800e0084c06507104500b62800718005400000d0802014032600048940507a106130070321110004c0c84e050359104d030310b061b0b0303d034413050100c0c114100c1180207030022149a108401009840e1400030318031215820004a82c044070b10403011003112624000079141c0a05605907021a201e48001815500d02003039100d000f020a03540102d820116581080060f615420302170340507641e51f00905a28600320501280010504610003c01d5402800601808991030030964099034441c040c0c107207990080151051116102d106020b038254401d9604000b908058940c2138070759040c0341185404240c0703865118019a8008009002c1c080362160340300328a48144040c000608403e10400000074000c04140d21803207608680800c10b600aa0ba442e14030b503400000f5504000103544140e285c001c040343d400350580401c000d0b200 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 785766510 1250 785765260 785765269
    0x50705060f01230a1502010e1207020a0e01180b0402042d05040b01020604120201060b0414030c01030c140913020703050a0807020a0c031b051203070201170f160e 71
    0x14440c0200911403071566150101110582d0005001c24100111400442c1c10760388496034008240d42c0845503001c11085211303012030060030710700305284060244c1084806d04009110061108174001c96008031030688581c2c0001c4100390030b102c2c0108242c580783ca0b050401d03800d0f0308a41c8061400410040c141540c41701c4100102c00d2505004050322000d540c00c04100c402e4001100c080c080540c0d0400000041c100042c3d41e44d4000740018212404800d00211854401d412500240c0305240700750341c4465079429061440701c80a4a01c034480d01503c01d04402c0c1c1e5129202e0300c1c8811400c1d5031110000071803220b95288960201c1003494011005040241103601c1c00c1c00100f43d1644640d8401daa07030080c1c11001444000064890030071904244101d40101e000c508910050302e4001c0783c0010310498201103001e4103092035121540100306a80085503440011007c2c000480c002c0c0c0f00d600da403a20070f40e10890080003c03640c2c2e51088404c0004100025104100303006880007034207005400703004100024 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 785767760 1250 785766510 785766523
    0x180c2301180510020f0708011e060e0f0903041d0105031b0f0d0309030605010e091903022a1002030315030703050d050c0304030c080706030f1406012a06270b04020103020a050705 78
    0x25002e030346410304641103e401c00c040c40d0545270207041c104116410214104032040c80034040c0d0110420140c08a00001028002c6900400c95644604280d0001206a00c640c410910030148a8004c080410a00e0141d02112400308800102803c0c14000d0f418100301e201415030400703404001d40401e01000192441c07140e203002e03140440040743c1c01c0c901280c0e07141c9070241c0038020304042600034806c0d10002e0b8000607204141c44102c0141c0191403c1c03500440c900d550100e456030f50000d40081150021a000300c0218001e4100721031000030741041300149641c0e00c8461000030082c2c0e10441c0c580745039a10030800f91074010140829245803d81e0ba40b102c4d00b0707840c06070b0001900c90300000004c12117980c1501c41c090900300c1c109000c0c03105800c0308a911074000c0c0c0081c115410301180546a04904806903c0548a0340c2000c10032070254520341050380003808100c08208050b228641c134902401000e0311102203040e840000c2c03e45542c0d40d0b42c0110080c0d0404200b5206001050015100284051120 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 785769010 1250 785767760 785767769
    0x70c031713081c0501080a120f020d081b12040201030e070b040b03100807062105190c02030d0f09020f01050906031f0f12050c060c0c04180c2301180510020f07 70
    0x62a00044504008c80900130450100c424420160341c80e001d8a1b8010807040c1c0000750504052080395a905d41c140c081c00000c2d4004414800e00042d981c800c007502c075902900540c000ea0301000401804261b0558400c010301a02182c20341c144402c1001d003d140000b1903010980013034000d02250741c0e240311417078081103401c5440400d0241c95400e035070584450000300000040d04081c80700b03052280d5503a191359800d4510401c1507403558040b04d0201e0003001140c2189003809010040c1c1001245c0ca07000030052100201e1064058080001140d8441d005594241d20000c014074911b4481c10b105840b000e41042419040b10416100001d040c2c019010480c000c4c51003400d40301940c40245041070030117865901c0b40303118040500000034141e00020700c4288841c402d0724001460158004481064000a60f009043c41100381c0d01240362a001202468a4041000300c00301640d40c410054941c1005440079681d10f84481c4d00800051030034049113141c1030b140b801900d45a4035824a01e5007801543c0c2c00 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 785770260 1250 785769010 785769013
    0xb09130f021201050907031209050a14031203010b0c07050d0503271809011401142b11130212070305180a0c050a140f010e06040b03070c031713081c050108 68
    0x4005210020002040074512458140c1450b4140000200d102c5854060008800d4941068080038dc030200140c0749900040030002d6101e40e501e00d40e0000da42c0c040403605a1600818000003842d0904252030b08142d9032007405542410b41c2d040b40e05011340100b058102c1c240c03000145044650319030041c45070203000f9407140300301e96192601c4120300f540d240c52030035100c254840004214581c0642e10340b803240101181c03544096241400c0c41681112140004001c0815030074170300d41009441080050801021380b1750442c80081d240e014012401800700d09003582d1a134800149a0902c80d0744255400070309400c1002c102c4c0030400d03602e0300e0000422400c80d0320014501d03040c000392828000c200010280d2850051010a40c00c0105030503500f001c3d00c0c10705100800340002505d03a28401910090007002c1040c9450703150103d40104000701d484000d030082038090149801d840300350402144603050344920181e080d1251384d54550958000312074442411484498a0251241402518000c003030f060b0 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 785771510 1250 785770260 785770273
    0x100b040603020a08090604020d02011110020d1b1701140a150201060509150a230303070f1101260414070e010f0b0309120c07030602070b0a0b09130f0212010509 70
    0xb0013800b000e40140005415600071410000140d4419075040c8100342c0c280b80c5012041c28540e25a882c0c1411002c25480060010480c421103803055804130303ca400200b13904004611170807030183c1c4c1c454009811603905450010041c0148201c41280e43c45032300c40509406c580b1079a03a05500000fa88107004800180d44a01d41080b8134641002026040454410740600c010380080011350404881d1092030200061580120490031003040030401d140c102906483c2d17a03040c2c03490884480100040100ca5554810f94542d1195200b07030368074402c000300b5080e03950709130342c0450b030301109140001c0040f01c00ca00e44400c01c00808170140154001041440c0340c0003c254101150884400c2a83c0c00562021000b070041100d01d81b80040c070400000307148898a0368416605196600301840341d00050700b4133000050700c108000b007c4442e50b228280340b450070820740890004011115806584070078405580d038180c803000ca42840003980c0c4a030302c01440720150380d4403440b1050035501b0458500c4520340250 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 785772760 1250 785771510 785771527
    0xd0209040506041b1d0a060c030201060605130605030603010902060c0a02090f0c04030f0f02030d090612090b1605070f0303021b03030f130614010806090d0302040509010905100b04060302 82
    0x50046542105080f9410300c541004406094444064041c0c0d490400201000442d64814001e81401c2c400001500f902c040d00d0711100042c244c07002c20380d0110015031900000003445803207102a54641c540400500720300300d1600743d0450b500e420151041c0d5155684a0400005940c4c450041801640410142080341080c3c010499880d400509036202c40e0700500c104007010702d1081c201c505a0340c1c085048100880e160a24020704001014001c3d0144550941c100110303810024410884001e651913070200c00d210030152085d0b454a030320003000c81900c0c0300820041200d020b8811200302141c9411401d00900f80c40354840311000190035404a5030000341d812130341a81803104c0c03201140287c021803943c02c01c00014910806c00138540f92400c180e1085420400c1119003151403141c0d80c49094000c41e503103888005442e40780a40e080e010702d00c41e00c0c4c14200722a00030f0080e501180c0b40180420038980c40c1c5841080507040041c114003078055149404251229480d001d84040c11650350f0042e200c6070312 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 785774010 1250 785772760 785772769
    0xa11030706031806090507170c0a14131802040f0501060212040b0a1b06020304051b0a0f1502030906031303080114030a060b040615080405060c0913020a020709020d0209 74
    0x58000c8401c150030043c100c0100388083d82d03202c5140750300c5000025900003d0500a05041c119000030f01503401c4160031820000c800150005420000c440b401c407090f99401e50068400403000c01e00b43c10401c05030b8106e8880c01d030381e8405889044401d454403000151640001e08890350f0700c0a5140301541d0340010f121080d8100039019400071000b064a107031504044041a86000741c1c4402810400c541c40303001284181071482c4011154030a4040d500c03030a1628081e0f403100c034a03010907180110324606032040d0b0725091500c40111501d00c569805204e0500d10701c50408007411f001c0c10190312003000295015214000154420f9140d01031280000e140e07490001c207928410307401081d0541c400d43d900401303550080741c5e205c01960300210005001400d0741c0401c000e440c01ba07010302030b80380000d082d01b01e44941204400303200350f1080b4140c030f1182c3c1d1340035101207440c010450300a8000ca401c48910385091007642c010f1003000000d004840c0380c10750718803034401680d0124450505194020030b281480303042 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 785775260 1250 785774010 785774023
    0xc0201082a03040c151e120f0902090601020c01051e070206030414190b0a0906060503030408030a020111040e130c260d02010c08060d1a15190311061b0a1103 69
    0x801610170746050b4000e50340186042c2c0c1c1d90300c2c0c80c2a03450800048841d018020407504401c40d541c4001800010325000c91f5500400b0943d5059000b401c241001602c250301c00314480605090584415091002055449900c40f4081d202820000d03401c011110140c1c0e180c8028500c02c034420f103c055014001c001605042648204000c60f0b0f50f50310036140000544038900080e03200d01e01c0302000803100e610b81008005001d0a501c0030b43c15000008020a6030200440104064000350300207109200281d5110f0b0245e00c81c5115600003c003211002c40d08000b01a1529505a400341108900140d00c40b400c401c00140714441a401002c0c200c58680d0344c81e01c05000303100042030140001c0215404524014011040007003c2501c40c2c881d0040100c10004c0d500d02036081c070324260703020006c60f150000d104641c02ea00c5501252250700c22a038007103080801c00410360305032603114480e2442941e401c2c060041c0c5410001d1b06020a09000104145050341000818a440e00809294102040940c289401c184 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 785776510 1250 785775260 785775269
    0x112150302210708030304150f02090a092003090a0305030405100c03060317030405071404020c0114010603061e052b0f03140c0318030c03060703022101060c0201082a03040c 76
    0x20018000c00010230000250f819010b412070344007085401c01e02071300c60b00a01c62200d04a52082000c6400700c2c0d81045035000d0b803240140070010024540107602564100d00088880303000c41c3c5e00265818000a2140307000e580c22510038812190074290000f00501a1910010b2220019a40b81020001d20208600a00394880e540030b0940ca5400c054903403d8860300f160144003954040c42c9054030329500c8907812260081e10715402041075408101d528881058203102d4980041c1c00c00001203600b000f0415012092038540f416090254641011302400046404544d4100b8081d1580391881e20032070480040f140d886110a40e10300c3d4140e18004e40403808215090031031880900100a8454001003141d0703000b9099050764907105461000280b81400280d2007039054000c1100f4402d4860301030700900317140006081145801d40c2040c04442e0442c0c2c0903c03444001034502d190b1a009940102d10040d04080480c281c4100341d43e000400c0b1504e00c2180396460f11601002003040140145807480c1030140 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 785777760 1250 785776510 785776513
    0x20a120b090a051f03080909010603020f03040609030e060c0607110f0a0311010e01151406070b070e0a091d07120512030702011514010201050907050112150302210708 73
    0x60000c0218103a0036005054004a55444021400000040742c901c00f0405011034880c070701944910749070580390810350b4818060b4804600106442d8000d0003601c601c00304a6400a00f103030348a850703040240291030f0045c3c00b0b1140c89140400503807070b41c60040051a40d03510082403181020b400003060390941403841c03d035a4108130340305502001e004c01c0324082c80b501450b190740074964039103000b4010034010fa80080a507182c540c10400f5131000b450701da03045503020105900e80c65050703000c0c84254400d003600100742c001d01c500000c0d40c2c1030103011950440a00504501d40380c9840700c18410444804501d201c0180c1d1a002440039032542c02c010b204040c0c040601601492545940c5041c0e48a513404905c40510001200280342c0e40c3c402d6214142080f04500a000d12559540060303000c40c1741e01c07400e68015400e0000060010740c001419004491040c0d40d0864000000d6074040c0042030441d10075641804513100000c050f0b0f590000311100c0003079802c01070280401103403919250529990011044c0d = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 785779010 1250 785777760 785777771
    0x12d050402060409020f0d14180a0c090e0307060e0106140f1003050402132d05060f120109080f13060f02060c090a0e130309080304032022020a12 64
    0x140c880c0c03000d44048441300080981c4030a4103201142490040b003143c3c0424502d0039031100e01d210803050792140030b01c034004044c0c00e62040c011555078913140e0348100035128a2505004010a2610f40d0208100a6510003980c2c1004030750342c2c60206442c0c1c20210a081c580d120201809101c070340190510308210200c45a0707181c50001741c040b03480d65410358441d50600d90f41e800060b0640d02e8020380c0708800058a002040a0044a01c202d41c4417a403405032706c20f914020101400c16500315100703181c0106001044880b060a4604c1000305012401100c05155505d81e0740807030000d42d00402400011902c07203c001d07282c2080b05040d5580040c10342c00001003140800007807030322640200307001c2d8120303440a445075992461080419500160765115100042c0074000700b040b0110740c802c0c140d400c00d10981d6224450342e6200420741d500c0c0a280406000c05100c070708071540c08003514000d021035000103424501c19411041c8200643d0009540720203049070000360703900b89194001c0313024140d070f0701043d0100032 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 785780260 1250 785779010 785779013
    0x90c0901091808070f0206030103030c060b09060315090f1009061a0a03033f0506091504020c0f0d1d03010507080f100510050901030501080f03030708100503012d0504 73
    0x8190b82d080b1016244076030010f040c40512140110320400960060320785907580d6035a142c02021482300c1ca90a1f981589410800744c502c0c5006640d1a005000003001001d00901c58850585241e01c00341004049218003014800462018400c0c01d00703180c40560009540301040c00c0420a403180c3c0803e003c2400000f45810125940d500001001d0341c0d05480c084100641404096160a0205840410480082c5c45d8800002080c120250116000402c28030060712010b090158614060750075170810b102c1031412104908055014001c02180e020403a403a11120340d05180c1410100c03180b4800140f121312604200c2d400000d91500046020b800070011840c007918000d04405000d8200000201c1c81c002040301214080c00e4400501002412441080c600000142c00b980c01902030a002c40c4c1000c00005400c00d020825200b0b94050300091442c40e40c40c0c800441e0007050040c5264880892240d0205450700e00b4881c2c20000d80386074004c1c16003450000c08900000400d21030b6600b0720b03800c0004010 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 785781510 1250 785780260 785780291
    0xa0b010b030403051204110112060b030619171e0d1b02010c02090f220510021e0d020414030a0515070918090c08240606040e090c090109 60
    0x50440e120100c005072a500c0c0c616040340c45100b00c450b0031240503058014041442110304800c0c00d401002d0302c0d10541d0b04502c1c03000400384c402501c54141c18030301c1440041c0c42070805c1207400b000110342d42c0d405000b480c0c5500c2c0d039180740501c504401c9040e500030f01010720309005400c00c82d400008940010030380341c817008500400742d46044188405000c442208442164011995400c440c1d50060054106e031a10807a1481c6041045814144d08048078690b40c0582000320036000d21580c10a0140c0003d41428420030042d6021000f010782c00e80b00d60800b0351507101c0400190411020344100036a495107080c440c90000c14852020500c40c0d045072041c035001510000b14010f486d03180c0c03500f100180e42c0d96002900d000c2002d600664198400040c803d24100c09a4484103140e4401c40e00401c010780c44a0341c1da81d8840d980f00800c01245050040c2c1e2400c1e0390720400d4250712141c0104480d00d400d8a031907505182840c00d45013500e503a88010000c80742440c1045039640504401401000f05218104840 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 785782760 1250 785781510 785781533
    0x5090a0c061b0b072d050702091b040b0304061a010e0907110109030c1506030f14011b0203030603060f060d08030a0207140f01050f061509040e01050114010e030a 71
    0x4052140c8803140ca00302c0e403660b6540501c202c0d000030f019442c0e4500880d02800c00321102d5200125086000e806154070f0710340c60300d03810170010f6555425040601903070034400041c00207019001c0b00d40e407508801c00020746140c0103001518cd03407032a0540b64140341c5803081c180c0d2040314446c8011500981c0d807034001d0341e21400a5090440132109074401c0c0c1ca408805540c80100340c114090300c1e5080981c82030526402104042110748036002d8081c040e0400600c19044400324000140346100d0854110080780c110340c800460201c400e80001007000301415640400306001031060050381000c820001d0724034080c010f0380da22031101007145040303140c0600000c0401d084120000e11b50b410210200324900c020341d0690b9126903010445c0c024404e03042d002c09543d0300554000c0700701d070b60a290004000c8280250680d000b03640c06020398241500c010111013444d040b4090054001d96190f00d200111002401124020840484c40080c0940345000050404a0343c407049130090b48000c6031f00300065030000c102e = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 785784010 1250 785782760 785782769
    0x503010b06030601031805010c020a03121103043918050f0612070b03101e0b0a050307050d060b040603060506070506040f0f05032b0c0e010503070c0f050c0405090a0c 73
    0x8032070014503004000c406e0300400180c80c82d803031303c000442055000101c0c1488035009032941000d00d00c40414803000e0700c006490b18105090103001160008405901005136a1141e810288244103030b00403003ea01000e4806102060f50301e07031020080c10513000450040d203800e83c10309100303c0c0342c441e0741c6103540400900364a0054224082c90149040188000c3c405404415801680da0406852a420943c0d05009007980802d800c1e01c41d61412000c2014042100c0541761840e04010500c0020b13122500014449410702031b00b000148025072981c0b10343e001034200008960b4440d420300a00a003240c07401d8105ca4000d040422400010400c00540b90307500c107a005c4034801110419107031900e000984400020203610007c140c010615074000540c0c2c698410222407015544840d00104c41582c00800d0780c903010403401304d016207241d4484d00c000c5500500da0b0030855102200c0783c1c0c40c1041c10007540c01c16a50740c1c1200a200d07109203014012180c0200d204401440004440d4540301c80081e440c0c0308 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 785785260 1250 785784010 785784017
    0x2030709052704110909060702060a0507050408060a1d03120a11040b0708041e0501081b090307030803241e010c0c060f020c01051c23040f0c0503010b06030601 70
    0x3662003151070104401005403145a1407503001d41403500d88580c5007606a65603e20446170314001505841000903014840c41e2603074010000ca80b02c03445050005c0c00060701000800004000224440d801004118002c030b0300c100b400901d240020107000d900102007554048c2075042040320f000220020400305820006c05a8000303041c1c007030154043c9552245034060002200302140076014490004003520441d401c800c003070b4054104031a03c45650760f403d40500c0380401d140c4000b08845000e1503e0210414651900541c90154124000b80c6001459402160600800803c200300c243e441a04050910103030681103000d1010f900c00203150f505000706550000c00c4400c1e058285a105100300aa4503030020410001c035500d51000500401010702c1d004003502c592070800e034141d44207100b22100002031030340f500146151030b02e514015158283d0442c03000f400021928a180e1200c550050045200e41c9510840501c4c610f0110b024120785d9000a03c40d92609010790481c0c0c5034036040301d600030024030313 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 785786510 1250 785785260 785785279
    0x8011a1b030903151005090c0a0c020d051905120a02030f030a060e0c04090c0e0108151207080102120a0c02070e0c07050106060504081b0307030f0c0b0c1f0203070905 73
    0x900d03031071542c0180800c1a81c1441907402d4400b1043d00c220745140284a05210701e61a1911042070040c3e50030180c50303d0030340d01c02c100030250f5000c0c4106040064140300800c1c41d030f01d607070751034403410300c1c02d120f42d034000751050540c080003801c100301003000001500744802407504003055900c004c0d46900a800000070094000800602c010509a002402030004144200f01e2800e001881c0703052504a40520200d003482c0c0710301131b039509010704118800c8950523550f900c5941d80c1c503054052030b645400705007074000b001c010201a82c01c9042c4480c2c1c0141035240c00058a43c003441c0340c074029950001e000300107150702d4a0030300c00c1c4090340400c10800ba60018000310310710303807120400c0d99407078890701e00058565481d102000c150079920030010310440c7c80c0181181c018880860001c0110780c2005002503156200010800001c0c021740c07103490905000b58049984542d486d00b40ea2016440303d8000d01950b0450b1050080c11740d0071001031224120680000c6041d8904410064540001401a14030032015071 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 785787760 1250 785786510 785786557
    0x1212d110a030c2003120f1b090f0402181009120605070504170c0427140c06040e04152f090604060306090e19030302031905040f0308011a 61
    0x2d000b440f000369540445130f5145400c2a0280791030b5006802400f0428604a0205443c510141807690151030092400c030281e0080c0014403d082c0e00c0122900d410407100036000311181d03518030180821510407288001140c00710810005543c039200f200409103c07501c00c083c864105243c105407407003603110000040c103445050051744c0e24042e5500040e8145170392550340d0400706000c2845180108155402d02000c45150030680f1203800d6000700c1550980340e009050003280c41c040003e040805280c00713a548000d02c0c403012601c2030740190800f612074405141408200000c2a4030604200203141042107188503012495810b048a030341d81f1071103020b4146116400502001c2161b4400c00d000309103d40e5a41ea42c9005001ba28951141c1d0306400e2914000781844c503030201d6407002d400d0301203d4800401074540d4040c1c0094101808041030403100310850300e800030305407240c01d000c1c03805050440b06901c0c80c0d20740280300100507081000c0e04c500c7c0340074408008240c201a40c484406d03403800883d40200b503 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 785789010 1250 785787760 785787767
    0x605130b0c03070c080712090f0b070b06130203130b01080a0309121b15140403030e060d0b040204032a050f0f06130b090109090e060601212d110a030c 66
    0x214001c1d045c401c0000341b000810486d25029076003910551901c000030395071110040d800280c640700e121803d01b402c0003183c1c00101003061003070b88400d00034108170800d5000e6240c0412600200c3d80707040d06c2010b5000c50428007459400003030041c10a800200844042e90f540200700001c5480341c00c0c18080600700100c00c1201000b560081803040185141c20f059a401c05140b12144842c08240071980c0140103030460a001d0040310107880e01a01c401803d0b40c1401c082c0001d80e0f000c0b520503001e0b1507491083d01c030f40e81e403940010402140907182103130000c0c1c1401200400d115001e2000c20b208102c01d8410801d0351505c000781408100b04486900000a0a0021030898442c680036a800c1c55080f240115105406902074044c00c5020703600c0001d00742d111b601d00c8045803008040c03c0c0b001da11500010b2500e6105025080d40203046d80c0c00703050300d80014036986055440c4610a11150380490090307105807590828080c40c0c00c003034140c081c400e80c03001c905d100310710b80300d01841481096110459105003c0c00b = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 785790260 1250 785789010 785789027
    0x40c02010e0a0c05010306290903071d0a05060d230a02030a0b15010203040609090b0a090f0c030e0d051b070f080a0201080a0c020606040e0f070609030605130b0c0307 73
    0x5811042d122020782c2032400490300e10050081d40e02007840c0600105068020482c013a003042001d1171000d2071442c1004140d0007a80146040300e505200300c6070085a1600c00542800403510b94080400003424130715000d4040d074800030b01582c09480214a0f04010415010441000a01c403658406d500d000a82e0f00900b07049425001940512450b00031b402001040c2c489039200300008a1400b0512401c04012612807085c0e2040130000717044440103001c000030581c80501031000081501c407a055541404806588002d40ca030201c660340c41040003003464050068000aa00e0400501303e1000d140001822070700541e2491200b0000900c5181c0703459030100913185c060700403032454982aa1ba961400785c0c0d40c0210020480c001010603001c03c03400d1225004428810680d600a082540c0e035543c1444001c01009a14000601c2425402212030b81c06000100240c801640c541c001a410f42c02d0000c19500d015001c00d14410f42c1c00200800b0400047c00c0e6604001c0340340d14259179443d0399004450868 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 785791366 1106 785790260 785790281
    0x5060105070b06060405041b0f05130e100f080708011103070f050a020a140a030e09070801030803130c231f1103040e0405010606111b040c0201 63
    0x148100785996006102900c0c130f6061560780d50004043da5000c1000d0844041c0010700c0a03201a4404541044000e40d818101c0c509010014150303101c55461050100d401101e4000c210030b58015400800142108803412840036110550307240c580c0c2c02480345000ea98a00441b80301080020804e4a114034890b07124020000310020094030781e940a0325410046006e0a0f00380307000280c0c40d42c240500010520002d22000383c00d444d000d000410758814891040000b4410002107a40c17207403010307040d20362000c0c059840ba211500b05034408810300e08010801401c402020450000c1007001220650414508880000013081803040200c20040042c6210b0745400141c013807070f40110303154241d0741e40d0300b812645480e42d1001812841c001c1501c08441c141d444500411200307600814002c030702e95507030026080100c080c07481d05c5411040305210900030341d120215129018001e620080041 = true := by decide +kernel

theorem cover : BRFrame.Cov 785611510 785791366 := by
  have h0 := BRFrame.cov_init 785611510
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785611510 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785611510 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785611510 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785611510 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785611510 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785611510 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785611510 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785611510 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785611510 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785611510 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785611510 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785611510 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785611510 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785611510 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785611510 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785611510 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785611510 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785611510 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785611510 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785611510 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785611510 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785611510 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785611510 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785611510 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785611510 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785611510 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785611510 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785611510 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785611510 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785611510 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785611510 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785611510 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785611510 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785611510 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785611510 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785611510 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785611510 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785611510 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785611510 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785611510 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785611510 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785611510 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785611510 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785611510 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785611510 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785611510 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785611510 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785611510 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785611510 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785611510 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785611510 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785611510 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785611510 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785611510 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785611510 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785611510 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785611510 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785611510 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785611510 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785611510 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785611510 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785611510 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785611510 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785611510 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785611510 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785611510 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785611510 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785611510 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785611510 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785611510 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785611510 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785611510 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785611510 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785611510 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785611510 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785611510 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785611510 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785611510 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785611510 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785611510 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785611510 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785611510 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785611510 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785611510 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785611510 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785611510 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785611510 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785611510 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785611510 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785611510 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785611510 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785611510 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785611510 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785611510 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785611510 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785611510 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785611510 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785611510 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785611510 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785611510 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785611510 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785611510 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785611510 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785611510 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785611510 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785611510 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785611510 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785611510 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785611510 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785611510 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785611510 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785611510 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785611510 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785611510 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785611510 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785611510 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785611510 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785611510 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785611510 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785611510 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785611510 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785611510 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785611510 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785611510 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785611510 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785611510 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785611510 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785611510 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785611510 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785611510 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785611510 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785611510 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785611510 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785611510 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785611510 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785611510 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785611510 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785611510 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785611510 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785611510 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785611510 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785611510 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785611510 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785611510 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 785611510 ≤ n) (h2 : n < 785791366) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
