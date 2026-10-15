-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_5516
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T16:07:22.99942+00:00
-- url     : https://prove2.me/submissions/729b94f8-6d80-4d71-ab2b-ee96498ccd2a

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 991906474 ≤ n < 992086330 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 991907724 1250 991906474 991906529
    0x21c020a05130906050a0e04050c0a120b06030102120f0c270103050f010608070c0816050f1b0306062101050c041d09100231211703060604 61
    0x1c42d902c50800d00840800d881220344100001c0c0c1e90098412078280341401d07183e003804030010b07005423903a12030041409007035030f0b4501940e40a00000701819603140d1540c60304500302d14020300001e2099006125411549401c5038103039500040d428a061601c1d20340c036035030044a00c501c5900020700300401001d004400c50018080071000303002c0e60200900c0d51010014800201e080c05104001008803001c00d0740c0610405a11041d940103a00191509502c0035078680000d0402c0030880f106c1d04221840c1450410621a1800c151007040f02e40d9031480304040000d442d013000901036445102011800140b0429412400d01669840c100802a50604d1071940846030454454a00c0485526502117607104004000c00d000341400d0b801410b001e00120480c60103500034000c20b241d1280d0004805444505901041d008031001c0d129290b655410801c02040b0204800c072921114000f8695407400610402d641034081c074201c0182940700d80790000025a503209542c4041c0c4110b0b021041f0400d240d18048 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 991908974 1250 991907724 991907737
    0x5100c170f15010c0b0a0c17090a02030105090f0d050d020f130510030e0304140613030b040501050106030e031b010e030d02130501020705060f092d01030c02031c021c020a05 76
    0x215005120710b8400045030a01d4094034014200c8164001040c6803480b26045503083d48074a050030020400d85c04003003070b51072000f207488000c5580050307002400d5050030700c00c0540015000000d00500081401241d0b940d0b0b420140070010042e000a440444004542c1a80c10340c40c90100015135942c0e89c4250242c0c5c141082c020281704482c01e45e0001c00b958064407980020f21803240156041038900345030142c20901c060030340c0b504038504100040e010404404035401a610441b0701500c58102414518211041604120213062130b01c04840030000780002500e080340e56070a50303d6043c01400814901400b114810310105103c0030450001e5021150040c001080b41c145008201a03a0340d401241d540c8424856030343c00820803c491031101c803d0000400c4c0e62103000c6c0440f400b075030007441c82e500d64040281c00703880c00340c01080703021015603418081c11580340c04c1b92001b507003801d90b48080c8101302514031320703c0905603500103913200040e03901a40c103081410361460119100c13180d488001c1d150340c5c8440c = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 991910224 1250 991908974 991908991
    0x7031d09011211010810050f06040e0c030f090304060c080d0608011d0111040f0315110304030305060310060308030c21100602071205120d090f0501061a0705100c170f 73
    0x10010301c0401d52241e805c00384100c022218846203180b4240a0021401c0035020541e00600304000114040c01c1000754079004d29101840e607070ba24600070040a440304400360458080da04100070402003958000c900400040c1c000c0c8926030380e0f4413400f03041070080510b507006001c00d50904095802100c0c8600200b110724080500a01c0180c07180c0084046a11881c065143c8510b5144010301c04540c95140001c60003901c0341c0005550301019201030032641044408400003070b26107080010301e06040c884800e001203640703806d00c1040d007142c4d0794010790700000384009400500030841e00031441048182150340055107411503c103080c1240b00600d41556070065401510981300300181c071012010400c0701494020707025000b800e5050001d1001a030104110803046034580c408038000c11100d8641c00240c0b031084000186062425490061240c0030b1441c500360f2080c2805200086900032030b40c0903003147c170315a00041c8a4003412094807980d454500106911001d0070410280201030a02c25020310010f = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 991911474 1250 991910224 991910243
    0x906090b01050310030b040f05070b0a0e0306100506030a060f090219020a1101051305040e07031401060b12040819030605030c06040305031c020d0f09021806030307031d090112 77
    0x188001550507100035036118041404021042020404031b00310b5030303009171040c052044180400e450311481c210158221043e41d61000a5070702c044c80d00720011011100c002c2d401f030712141c94810f040d8101130f8100c0c0300c0d81e40a104000000b0b80c072076800317500c0b50340600600c1c0f80074405542c891070484025081040280e02c90000d00c1d4510880b10300004540020560291200803960181e100449550300a40c504280c5d0003e1a031001c0380c6a5200d0180c85036107010381e001040b6051441c1440c0d41d294056175451a80c6914000d002d02900c1000b0048400e00d42c4000d28202403610fa40c81c05900c00c2c8a0510441e580c52008038020308020341c0f580048089034012000c40e51180d100008201d250703c00d0f444010100d600070007108072801d00d0112102c189010045d0014240104c6100c0c04003070b40d495500c0f000100d5501c2a0400445c980b4a06030407003101105414006840c0c050b0209580307101e0800042e092000002c15014510b41c8894008080d070760281c904040395940718484120074203d84070840f6412030 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 991912724 1250 991911474 991911491
    0xa0b13020c060604110c0d0e03101b0f030b100e0d0f03091e050f04230a0f1b092d140f0906010503010603113a09020a030624090609 58
    0x34100146d0b8511301072000603088540900030180c0b005207a4040094141c003900c008a15602002e1191b43c01d1400903004e01111490505001401004004034200906103050030407a81c944400810303e681421034101114040058800150a90404480248808428840b6008040d8001855011503030000303140306220f26401c201c4501211503010b01600f008440c21800c0708c515081c0c010b541c040100d2012407030b41c00c03403007886240c66a608481003000f040d01e558684d40c000300607104218008940304002004070b01e02c0f40d001420301d4038070300c607c818400c00b542602080703c41c0300c03000c445078801c050000d904d890342c1e421800380002c0b45540782c0c0d031040401c00307581d00c003608084180922400303050b590030380307540e00b0a00c0540081101103c4500b0302d17401400010880081400900300200048494200214841c0442201c11207040c0c9a900902d082010540050301d42035400d205a0b81d00c14000b042401540321200c481c0810403801012600c07200900245a03003055010a0684445403000d2020b4030 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 991913974 1250 991912724 991912751
    0x81e0d0801060203070305070204630311060a1506050a090302130603050105130203060c1318020f07060f06140f270f0f0a060602060a0b13020c060604 66
    0x1034092103801c0c0580c108201c5540020320610003000e54610040c00000c04448601005500903603c401003039004404084a0210703500c2020524080601c04c41c0002c290076826041e04044144031032054003800714402910f0405d409000180000340d80351040f11994501031184801a00398401e451001811082001c115503115800325200c000107900c0c0d15004610b5030f403c0c0b10325410b20441f804d107003075038482020001a4013070155900500301c050001c182d0340100d004040c202070014102c010300354001c1202d00703400d0700c00c60040c130201c8a800c0c0d400317842c000700c180b036802c060b1090034807079404a8000584041008001d92000c803816052500410490351aa038442c4000d0510310300d16548110b886107885a00c3c070f0031641400580c2c0301d01604640c0030512103080803600c3c0c41a00d90070b102444280030001d49c541c00c824041ea03c8001c0c00401d02c08103141900c065225400035101c2040d441c0c0340da90f0011952074040102c16400710700d40341150b44003c1c400300d994952005540e95441141405002030121 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 991915224 1250 991913974 991913987
    0x9170913110a0f11070e0a0b0307150f03140108032d18030109080403051b030a1a060a15091809031713080403030f03050601031a19081e0d 61
    0x2800030741c540307842d20a0320b00003a01c40104a10343c490401031406580381d0b074482c1c20701414004282d81894003015013000c0d02c1079019240b108501d40e003ea4840c0314104840d912488548600b20748174180001c00340034000781140900b600302d1b0183c1540000000001e09548000010940182c26200600001072052102c803c00c142d40011085041d0041c13004a00e00060709847d10580703040180006040030469480c0704c1c29030402d81c01238805030001100c0c510000e542139a0200e0600046020b40580c00c2c543e43c42070f0202d00642c0c2e2000010452a0000e078451f141e0500e113a02130b050085d0302c1902d00e04500c0009091100c42c0c0a100e80084800c144c00310106864000c02403055815140e6502c090350b00c04030398000c0c075801001e040c1c1400c001800c400c0415100c074000d00145000342d6455000d641d076010301a040e03a40241c00c3da410140b520704c0540d0480d031800000f01d40c000003105c0703410000080e01c404c1689003140b50000d6100d401030000c02000350100140c00103286c00c0c48410b0f50341c0c80400150940d5034 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 991916474 1250 991915224 991915241
    0x10201050a051501300914060103080f070206120c0a03110c21041a0d0c1b0308090109021f110f030a0315030b1e15010c02100309170913 60
    0x1d602c000c0d0300b0210f030340c02404942c02103502c1c0b1310406050300089020060358a0000e203240240d90341c0344110401e02c100b1f9103951075049030180040c0860352450703541e00383c5445100c9203038060790004a00c1004564440c41101c00308141121560b03440d09090200c09603540c001d124803400304e80303040d00e911001000d40c42616082100007025240c20f8001140103524038007038820301100400f00304400705000018a41030500022168916620b48500c40c000000b111411450f5000b1300070248071030b44c1c03a00000416122141e074103141406981d100c800c0b40c28050b0003105802507220100f240c0202850f012080602d412074500c0c2d0b034140c5203001011042d0348440c04281002c01c15001000040230150017034200768013104613070b0701101210380c0d240c5910950010581d84403410b01c5000415451001c956507916400c0f900d10000c00c2c61000c1e0900019250194040000707001e000300150324a03a0600951000d00d2403070300a04441203010400c000d80300250306c4140514802ca14840060400003200d106900d41c = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 991917724 1250 991916474 991916491
    0xa06091d10020a02010e10060f050d15091e0506041709010c0b060102070909061401150c110d06020307081801021327020d0213080d2f061302010201050a05 68
    0x546148032440707400a075210b004644107664803030000643e058001c0000000042030240c00042150406000008d88092540500d104c0d03da1400002e000c1400012103009058a1010000d00407100340385c554069401a43c05c110134501754080c142c140800401d025100f03500c28100501000e002e00441a003900030072036180e0004000161903800078021441c00e50704018140120343d01d0b569a0003d20080d20041c450803100036440380300700716103800702c0c130b0f4064094024141569080c01140e00d0080c0b55024065020344900086040345455885a0010005103608102e081d0340c2c0749009900546000c405031215104108840e4580314909018407d5416201920450b0100e9515203581c0c00000824203178000600102e03440000c18510f1244014000c80507079450150b25000130320100782c80800c20340e1122410750414030801010030b5201304212a0f9a030f4402000140002071200c00b0001160120f50151902ca03031428003013985900b108848c8030038800d074000c0c0015070311594440700f41c42c1d0540c1d2a90 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 991918974 1250 991917724 991917733
    0xa090311042a0c0206030c0c01050f040210030b060412030903031709120901030e01051503151509090a0606060306050906060a021005060f03060c0301030302120406080606071a0a06091d 81
    0x40c0700040c04201c0903460091840c0c01c8480c003c2039000114140d2056402c503000040001d080300c0002c81c01e00582c0d03482144a114001240b900c0e40100c0e02240d490340d41c139810196181d5500d2910380d00d43c42a10046c00c08400360103201b44640c0740103000c20034903000980200f105039242900d14625044458803604070880640306181796050b003252583c00000003e414542c4030784038880703820700c24450244100da001030160f0010002605050600254500c46501003002c1010802c01346680003039035001000558903003110f03a407105840c50600041c07050042c051800c5c1a40052007a515030080c90554004640a1045407548410030007248a4104404056040b03e9002001076080b640402e90041015281d01c001803001d80003e420404201c441c6240020048010301c10700d0750400c04802620a1042d820340b91a040c0b07000a0f15582c0000c01051050200081440400002040551100040c42480c1046051082ca180068681801030441d034910304440444e00c44294102ea03440100c3c01000740 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 991920224 1250 991918974 991919021
    0x210108031e12040c061b0519030e03060405011512030e01030903090518180607080f1918051b30030403031e020c060a03020703140a09031104 62
    0x10048070078020480e440c081d105119a10700040c2c00c0480c6407145100e01d415060709414a00081c2882c0d00262200c0c00542c034100c00c0300c00207680058500800140000003080300d80c550320f011903282ca290084c1d640c060103900103001c200b21054002018001043c8201c03110281c41d000e1007408000703900d201800050103c41001020750081d403206010718042c0c641120110789440104942d04a0f00380b400030188426410840c0c40e042450426501c204890042c11150a00075002070070000302600d030105800c180303004102c54546000200c01c840210b070606115103408901d203903c500d1444101a5980d004400c4403c005034004101260641802410a802401c4086100c403c0700c0e03000c0d9400401312009903014403108010009000214802d03600c625100945070804036010035100049015580301d00080c003040c0d614102030381d25041880c540161a602c182c1800c450001c00e2481d0b043d10200001900760b02160701c414940c0549014141c90000f0a43e1107051008031002d600d00000c0505098442 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 991921474 1250 991920224 991920247
    0x504091223040e10030c0b0705070902070f020603071b03170f040506011e0f0b070c090c05030f09190b0a141006050901020f1b040507110a02060a09080a0821010803 72
    0x10680c00c055209503943c1d00a07226507643d00d00b256141c000e07c0c0b45102c040f03020800c102e003c01074a4003601c107403070003542000d4040e0340c3c2c1104030100d4807001348684c00100005122521800a5009034075042680060003401424080c000e801c1d00340030f00c6c000d84611000030301031015464000d80911b60140c010708890780b80a07003480c03802003c1ea0b0b4814440c56844800a03801010755101c9010341000c45400f13545840516100740c0301403040d1700a0480a0828041d107003150307001019298445150300301324582d556440703801070929000c002e400056081c6140a4001c1c000d02c092158407030812400304011402c0f81c03520500e002d14080321b000e40070301c8040c00180030043c82000944480a01070040782c0200c01c40b070a001e0f0034141c400c10b030600e42175000203501d4064a040d00806801100c00e0404049a554034282142c46052004002c0d0180c00005590100b151003151030400803e0a201130b00d05800d0300c4d1900102640c040510542c0d4009418003d00c103503500754804a048910880043d482c1c1340348000e2 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 991922724 1250 991921474 991921499
    0x12060c1707030e1501080d022103010b03040804120c03120504050a050f014404030c2a06051b06010e011e12050f070e01121b050409122304 61
    0x469400e03034000c443d8049031603c541300f11140a001d4100291411104000e4006e00c2d040c050705101700301c00380118121807205255811681501c02d541c542c15074a0f5604d0031310400c3c901c103540c03045408411401d0042d040c82481298041501c0c41200001600d44107440d0448860182d406016408410002e0800907840c04180c0601c60300310605261060b490240491504003c0242d800741450484801101840c55007101801286008095543d01030515483c001c0880c1101d8000412100c40c150bd0003034a5014012400035410101001e504400e4135002d009103103401c11105400000c07014407019540e03c40204c0c0190507a400e030051030650368642190b41c1d007070707062003d4132100700c0c80300c034034041407180c1101d03842d54905000c1c400510820f071100140d20319140c0340d54011402c1019010060060040311000f00030025000a061854404040e042040d25046a030101e41d0051428811004105400700000910b0022781c454449202c080740850455018841c811a135122040000f486102c181e0035 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 991923974 1250 991922724 991922741
    0xb0c2a061c140906160807121e060605070b090105010b09091003020415050909010606020d0e1207061e0e090a0c02150901060f1a0f0903030f0412060c170703 69
    0x100126129010494082c03040c407041c0e802d0b1200b42c100030100402c20030400b030707018806801498076000900d064040100401c0040a0940c54192540d2a000c0b00a440261885401840c0c5c1410000207030384040240840d0b200300d400315601c810100004858410600c40c850495500c05d00c02494001e00c0c90400201207002020801002404032020025031290f11a00e4521011207084004507402c1c2000c00c900f01400600d616400c1e07040071810301010341d021070314000161890400b82082001c0c10b001a110b015440b8000742d09200710200040c856501c0b800400418505200c0600d030010400c0c0d049a0364034000000903041480e000101c1c21042065210380c8622600e032040e200701460801c0306024100040c1d0b880c07105a9100c8805000001d410021940100304060503404101040159103000c1d00403003540301c0c80e0b4800841e00482948090082b00c3da440c800300340740e541d101d85880e515090410703c2201030316254540300f96104498096084e91220f2040240c1d0081c031a60752101c101c1c06044000d = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 991925224 1250 991923974 991924027
    0xf060b06220513020304171608030c030403090501110303150d06020a020d09050a030b0423030c010204030c05010c1e02130c050c06070c02010c1104060b0c2a06 70
    0x100040c01516903285031034010041d8004214841c01d28010070050107500300c1140603c4240304009110000d4085a0103410312807080400c0790702c4800b20b007410742540d8002e01c03015160110000c1081540b4013808001d6200c3c0e0f1103a150010600d0b1140011a50070200035200a020f80c000c00104d221016000d1811028140041c5409881c4045a48050a0380c1009002e2005070b48404542100941c101d250540901000d4924500391441d503216600701d4100600084c03c3c1420400403601d64071070201e1003900d051901300071669100c1d00041114003e5101d0b1000350f40d044964240401c1d29071046a680c1120340c0c0060a50307082c08814042030518020392903040fa8002c90144410562078414001d481103501142c86503610b03211004c4030242480d178000c0c80b09081240300341078100142e0300103051110ba280c201c1144114146064042001041d95804c03c0000280101e00160440000a0400303a1081e691003104061802203680e102030002115034240d1120090081482100741110500408002c4 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 991926474 1250 991925224 991925227
    0x13140112150e1005010801050c12093307020c22090507060306140a0602030f070314070b07030b09060307210803160912020609010e240c010c020a0f060b06 68
    0x1032901410403240d501582c05400c0c0c00a021003003080e080c6101d058010132460009100d2481d040c48a00164461040f07807100c101c08600120303040003000c20203040c005100101041c1e01864000c01c000d050103d0107201c5170901c03913a400195409101141240c80724502400c140f2140603048822403803c90b140c0888004540d60b801c145c808124200003480081c00325460018045080180d540c801c40a0b500015000704948001004031550000859000109085c0c990751251174915044481d82200958460069400700d42a018800d14071501c0e8002c0905413002c002e0121910240900007808441c907642c5504010800c0000c009031121035001d600044200e500c201c2465035074048290400c0d2920741d00000d03a040c1c0c0c0c1c0d42468001e2005400f9081d1541122040c248a6000a215200d00740030f090400c280218040c10300c2d1104a40c2a03052910481c000c0c0b64010f07141840c41840d001942245055802d200f2050f406034000301e200410550499140d0355030001c951101e601400c420040e0a801000 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 991927724 1250 991926474 991926503
    0x90102100527030403020f1c060204091b020a020f0907020114010f030209060105040308160c0b120703060b0c0a1719031a0406150c0819080613140112 66
    0x105218241c0b188110305465055031065040a91610220b0040b90b42507602c20030040c005a59001443c2c0d00e0745004030b560320001405c0d022181c500f0404500002e081034004a40032550242d15000600001c11000d003000c40100c03802c01c00ca03075640b203204010790014035145402030241800f00c5002d510a81c03e000106c1c00c8070042450800d4148241d0000d0b907003d0b0b8801b070900c03c514121050a8012200340ba000c0e0409056403506289882008407203901e5214901c02c100403c021541321034000d01080e98403948600741c0d00140f51010b03c040312640d0002780390480118450142c2c81c1681c01c0502c26900030224030410366250440c903901d01000304420707403080c800745101010f0790001442c040b40540d000b080458600c0b00c00040c1015540d41c480c421414104140710205ca03040c14014041382625084540000a040a802d0361061409070030014000701b90026a490700240d046009007003c1d035074941d0715442c961540c403c5071030000020028140030001000042ca101d5031140043d4001c0850000f20031 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 991928974 1250 991927724 991927753
    0x80a27020111161403010c140301150c02040f0207170f0f130e09030a080105040c1205130b01082a1008071209110f120304120c03150219020102090a0b090102 69
    0x2843e40c0410403940780c8005805182c1821f000e290851080c60500030403003110941c6052103070005008030005c01d00441f400035902c0e0312a00030180450780150080000707080003003030f52011f540070417415a0405454074041d6040104041180c944940741d107022400d1028a0712840f5103079009400411004c0b110310390116054080c1c984490081c0c142400855540c21041006012901305922140c4a14503250700d100e00c1a400c01c01554020350304500004180e50350700501c0c9800f04c000b050152200380b030040041032015000880c0c03000f813094003045000c00c0201100e0300c1c4084c145100b80300d030461070f01c10302d040d0002c0c0902e440b15000002410814002103d03004010202c07a012780f0196003100410300c0710004d50502c2100f0722400003050b95802011308008805035900e1040384038162894410240c0d440a00c6240380501d005140d1282c006032443c1d40c60985080a501320307425420606485407460800030f4014401c40e4290000508016070f058078007021444181c2100720028154040d020100c021007 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 991930224 1250 991928974 991929013
    0x151401090b1e0405091e0906040206070206031e01091d03031909021f1d06090d0305090301181202060c160f230d020606011110090203010e0706080a27020111 69
    0x380040c6c642c0c1d800442c4110100d9a04420203401c610b11504110180f00c0540c9480003180d40c1590150b588035501e80f14480c040d00c0302c90201c0e00000a8620610011661060980002d58001d0b4049842503218940c03002c0a038403840150345030f01079200200501e010302c4185401a040320350000b41a1b030303103a000707004510344405141e003055400140300510f4104c0040082d1503480c007a000540e816420b000741d81011986c0d1000401c000b070184074001c2507101e000c1d6401d4200000c803190220304d403c580071071807070b00c51403541100c1220f0016000f5a40010f0610f03500c00107a80c1c0386162040c5800503c41d5980b18060003885441d420740b50504402590790800006840c9103014070b072403030001d18803e06604002410500050402c0d41006255603042141b407100041002452035482000030f800d41d80751000030b0044c030136003541d004240910800002c13966040001c2074841d0702400c4040c08040903081c41d030480e034182e603041429081540840400075501c42c00040e243ca0703038500b003110b03204910700c901745480 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 991931474 1250 991930224 991930231
    0x60b04180912031b050304030c020f19080a0c0b090d080d0b120c10030b06041a041e17070303270e0a0b04110313021002030d151401090b1e040509 64
    0x1080c4c54001401c20300c1c1960141c070540540c0d0b0b01e001411400c0a5500400f040d004080c0a803003181602161040b0743d55114100002a07003000036041201d03900c0034025112030001d14190f50070710350250002071641010085a80403480100f0324050701055039240501d54005141600d18940d48203501c610039103e0091043c0140c0c4100d008114a0400f0400c000102000c0c9814008044c10031094003415141d0405690580b003144080103032009403a0710201003409140e11045141240d00b1802056002c541c03580d8042d81c000305c043c0b0b4403840c00740754055556111807100a00096002c0c0c020529800c40c03600c0d525440c620b120403610540e9a1312840c00000c403046c1c3e001c00c00d259642c1082d001034945841660340b1005140103003819072400181c10402c0c0014140b001c1c1c007034680f0000030030b1380c2031003031003102c1c2500c10761507080080c084244140c42c3c1400650141c2e01c4034100c511a003000a60141003c101200c00741d19110f49415030240c2e00c000100d50195401c1d0744a4400c0c0300208455039101c405034403 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 991932724 1250 991931474 991931477
    0x9030c0a0c03051b0a0b0d1107080912030c030f1b120309011410050904020612040b010f2411160902250b0c03180d1110060b04180912 59
    0x141c050075030502504002c110310f00700c0c90b40460715511094949800c0c8811003104c10000310107031248500e12105016288400345141950000a182420415198050003983d10282d40c800d811048202450f50390b0b220381e0800102c0c83d4401e205154001e4000001896540714a082104540c041810560300d4401100d4121002c03500c04010031030300c05024454600802c40c1d14003e0032880c188440f800746c02210030300502d4001e40c8580000b6056481d045c4c1145c0c1c032404111100500d501c0c0504105014910030b0045900340b20b0b000c0300006012401080180700200b40e0400252070501c4808180c64616818114008034040d500003815008191401c1400402c00c0c3c02015035941c40714541a00d50b4601900341c0407601104c2d807541400715500d06642c1d5403029001c1d0079503a40380c075010400c000c06402100d40190610034541d841590540c1304d01100d20b1841080116050f41851070f245000b500d00b98018128102c000344010042d5080d04408811003030460340700080e41c0c000d2520344001143d021940b420 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 991933974 1250 991932724 991932743
    0x105390a0b0c2107032901051b0a0206030f0109140618040507181a01030e0706032a0e01120506011409060408011409070503030a0e0d05072616030203060f09030c0a 72
    0x1c4880c606000013000306d4a0001001c401001880006080d50046903007207041c4060400798210340c01410406c21f404150002c00103500c900e080e4490b610740e03d40034041c440c015414040c0c4c1030000c02018120380c0c010031004203144c00c4d001c007039941101d90326402441510707148100c0a000401131040070303981c0a001002d2001080ca2241144141c0b481c0c15494a1241058034040d80344a002c03802161100541e45945004115a808008044c0d098250910751495600710400521141908402400c0f070812081c0c1307031101a002d88644800850303108a5410303011506d510b1241d101c0c000940c0c001c0181c580002c201c00c1c05c203901c8158450071030351600303004c44405001c00203000d02039208205440040608900562400c04112001050030109403640c0f40900c2d5440c5003941001001d022a0300074002c169a400841c1e8402c3c000111400500041006207000d10380d40c56084211410144050f25000350080145480e11402d0b400b41540c02002c54105020a00080326400c0d400d01c1440300c0e01380500b503402c = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 991935224 1250 991933974 991933991
    0x22080a0201121e020f09151303080c0708070b120f0c090d051f0b090928080904050403020313050409050c100516051f0b030a0305090105390a0b0c210703 67
    0x1000c2c11300202410887c1803c00e21a5141a803642a880003e0b039501c60380d2681c48a840c460751a141c8002900614042e0103460408691494002e01821241104042c0060181c0f0385001c0603042880075a40501a640c0810031b100702ea00348040041101407080c0b080319134480c0f2851030901c803501c40c0d0411104443c0c403105a40424688490225000035016000d00600301c00e03c1d560802c418111f800300040e4480c942d9040052010324019140c840704090300903c5186031a02d4000c2d100d40c09008100803004486c040071845007444c1c8503071100d05034010001d00c00400c03590200400103801d03964030030810004000360b2240c0e40c2c1203034404143c1c51240c030041c01002400f0f040080c18403070081d841d4405034603242c0c1d03001241e076000a18066258160500d10b81d1540c1210048803107214a407801070329420241030b8010840032198054140c4500c0004076041c0c41225540c071a02e03a8107140c8007030001c0901c0300202d05c0000485009101c072800c2c10501414152801c034251800e0b43e002c546601c0860303641c0301035 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 991936474 1250 991935224 991935229
    0x3060b0f060c0c040b120628090c03080f09030a060921020c0d02012309041413030810050d111e0a030308091222080a0201121e020f09 59
    0x55240024100c4a41c1d0511168141c0c4560b503002c10100144070710345802d2407026036260900c403041850703454801d8804904c4d10440202013004146250501500044000950384c0710901c20340d80c0701d0358041d0040d843c2d42e04c1d40d260112990014111414620030400140409503010071071400b29a114800100b040d8005e41041004283e04000c0d03d09002a0718882880107580442c843c2c4464104035034204003440d2034001210951450805030114404060b80721074a00301c007030043c0c0516072081700c0511500c0710344803113032810340b0058036102405280c1c914040000707409240110751024562038280c04041d51000085e43d1340920780e401761842c0005030400099400e105a64480c20000c2d001d80004c0c44d1120000b023404211144405020005100d0105250000500040012031a041951a00e80414510041061190451003d00e401707288000142152010034890702d00d94051710381d2040855151880da003d81507202c20740406400b0000d55071101202880a080c29211103600303985c444030300809 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 991937724 1250 991936474 991936489
    0x50d060506031612151506050a0c1506030510020f0a2a0f031706031c090911090102070f060f0c0201020319090f05030102030c07080a020703171c0902030d03200403060b 74
    0x10028425050401400c6c034141c0700201a000c0340c0700ca103026680e031545808203c42a03600310070010407101001c14455030502c52600700c130055074021000c2d100d64044400c0948124400c14503442801101030118200490180502c0415000e0145030000e0003014184091500d00305224121108912a80c4c1c02c020725600c9010903401f8521038006d12000d051040020781e03a180c030543c0c4145e50f0300e01528101c3c0788910540300c410003010300210502805035900051203c9401c20541d503801440399640005e4088d000320941c20444045440306109144071080445038641e60300c4d4103030306510082110000380900c02c91500302e09001940c1d450216400d10800080c1104907a2003d03200e6030060062002c0b446084046403c0386034003901c49503a1704e4110380207074108801030380064425120b04c4034000c6001003010040201100c46070130012a000510100c130101c1e90100e0000e90035500c0b004480e0403940c000d602a55003100350300d04070302a030003084055003a0340d8403580084030610345443e10074031207040052 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 991938974 1250 991937724 991937753
    0x120206010f051909021804050c0304060b010f08060f060f0c07091508060c03130b0a02030a150311191e050f010c0213090305040b030408130501050301050d060506031612 74
    0x214150f030070211400d41c580841d030060280c900020307130020f0500c016002107130881500c0c07031b00544144114904100c0691443c1c204030b80a6418509000070b2540c035620030b0700c0316107403401035484410700e07038131602c040c001402c8241100c02c3c3c108404100c0b040f0040e030003001604001480030010070150782001010170075105000010400700c0c1c04148140b00902001c00c130b0701e601c1220301402c9a01c035901c1c1a01c070601c19074128400741140c8215800d000c402c401980046129044005c03042c4100d4080032003200321030010744405043c4017185d02ca146042e1038585101441c00b0408030008618544481c40c5104e0541c62042011060f07a444100300014100070011808031002400d01c0440f43e8900e4002ca80c0c00e8000c074621281c4183e5a07415901014018401c1d20b002d8102c90b0780745070701c032714041c80c1010090b88206260b110405100b440010298070890849040c0c4002602e03081d49841e0960f6134802500c406010560b0600521502d5a07212242081400c01001058031425042e07165040800341548001c = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 991940224 1250 991938974 991938979
    0x209040b060423061f050906071118010303030e030405090c030402030a140f06150d0f08071220011b05130e0a0603140a0818030114010828020901051c120206010f05 72
    0x111070f26245e26048010344d0003144050303031981c0d6a1013162a010440d480c4040752998014a44883c0104809a40301002e0580f880307074608000b4010707a14074403a540e00441c401c10707a101c91001c001850454404014580042c800b0b8105c400755092540c81000d0406000322001242e07001203c48901d0101c2084500d03000103140515281c4086440041400d42c88030003c0030700031072440018681040000c40c121f5141c550448000c400015203101d0081221145a0080590426200030503c2a040620641c0500c0c41406c243c0304201c011580c0c240d410b90060504640c072400680800035080980c1c250f868130540c140e98000540e1820b514210740f000c3c01100944019902001c0d001001410040403185803803280104000388804880c002070240520320041c41540c0301e010f00000e5098000515030142480030301506507a130b50741000c05c1e48050796045010f54003d900400421407800c120034140360084038084982080d144549036a40c01c00440e14514005030700110040125803001c1480d5809030404 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 991941474 1250 991940224 991940269
    0x191d041b02160e07051b032b0507120b0609180f090d0c03140c1f0f02070c0b031e13050105180307110109050a09050609130209040b06042306 62
    0x1007440f8099440b400a106205102c1c00043c8101c1c0340d2550011028020206002c40e03540e007003050034600d1441350308060581c022030300c41103841e0003640b5400359510440d00f640c0d510640e0003064114001404c2a65421504200100146242611020800c110f800c01c158040e5170b803420700035020300e02940e004100468607000b42842024240e802491840c2c1e0030f40518001041000f40182031104e44100c6144074228856410340c0c2c42c0d5410051221030411a0500b4100300780070f4020072101c1a403041ca03c00800740381c0e0410040c03259040c480c01454004d2080074041541d0b4010412800702902d05407165041c6458612003c000c00009018a03a8005855074001e1000500c5240241d92800f5280000f840b103800c06074465040d03482010811700034540240104002e994030398400d0014002034400e01d01454041000401344003001d00c0d14550907601600007810f5907219200c140d0311036030140031150b01984a98607000050150340c0d81601c0840f8245900700303a41008000c005061a00e42c02e800c1e4003211 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 991942724 1250 991941474 991941479
    0x10e0628093c0c02070909050d020706140406110c0a0b0712050a050a03050a151502060f06030d050c100f050919030813030507060f06060f020102191d041b0216 70
    0xb070001c1035802080000c0b008102008040d0050341004825040920880d10740b0b025081404400640c010741c8544c1d43d02603c4005489503c00c0fa115a40c3e00004400e5240400042042911a03803100c50400c101ca02540c130414450000181070030613a520107030081002146c0501031001e100d805c1414501c0c5801c000d4541400c1c582c0161060180d18034410900d9070350307000602c44a070a600020403100740b004014292a0f22100f055401078050044c3e900103105400000703101c692400102030040c1c10060060161351141f5030304950944c04181101c07510701030003c10011110250083c1001101105000300341482e002002503d0700442d41505000b504030302c00d490003c6608201c25035000620303035002c00207400c1c50341410764aa100b00c131001407000d4585440342c4284400e95201c00140d13522a41e50341c8080394070000807400c0c1e000c1e4201e00207030b03014901d15040610b40244c00c03041403002c08440354070403082240000b13811166940c15122071520255462195958180516070100858504c421035250 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 991943974 1250 991942724 991942811
    0xf0f060201090b0c070f020a0612060603150509090f0106121103030313080d020f0c0106030c0807150f1103130e010906030f060c020316050d0806040203010e062809 72
    0x943c06802d940251400090305018000c180d15180030554001c1d00300c640441d41c0c1d5000401010142005000b00d501c0c080b00814102e202e030040480c00072001c1c0740c0c03000503400e000801a02440240aa00041c80b6120f03020028075020b02401c0700070b00808141102c095203d040030b4600401242d0414465041001000580b019204148806680100609031103500743c0345820024826400ba1141b81c910104405408200541081091380d105802d20b16849036202c0006544150794000c03299010214154140d00c58414248101c6101d480d241600e40d00344000311550035a404041191031441c2e4144003442074060100d5118018030b21074404120b44c51039500c0e00014186581c6000b050142c5071005038941500c204180c0d40c842128920a04080b0002e180403903403201c8402004010a03016030000d03a0500d01442900d040310101c880034034080d50ba020404c0181c0000042d8202c0c05009200d041207110000c11964019241c05480040d0364110007185603140c0d9000b201c04004142070050441902 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 991945224 1250 991943974 991943993
    0x609050619030e0a1b050901050d0308070e090a0c0e06250c091415041b0c0c080d030c080619060807030605040203070504061d151b070f0f06020109 65
    0x7031000d1a4106039280280c1812000760811040c08055445201420400e100050341c5c0036900e82202c500242c800313541c1e04140012100244219940501c800f03070808042400348050703603803140d094900282c0740d1841070009480c011040c0c2d540c0d49815a1610300707828080e001810184084421150786080c49882c83c640d400a6031400300103465100c9140c0740c01700b00550203111802605d0000c43c140030003c81036409950000007154045040c0581560f9901c0d182802d11440c2c0c00c2d81c070100b8080740c000802d2041500d1a100c1c85104841120348040f00150011040c0222610865165804182071010310b80c0100888000381083c0d10902910888c0d4a40c058801d412804440036820500290f550781081540184010307408aa000380c00082048040780c1e0140080060310b4031078a4a40ba183d10014a0f21900411000d01d103070000000c0168400b0782c000103005c0c0400d40c0c4600c1c08907143e0071025080a0070160701c7d44c4540200c45180a042c001c01390b442c8d44070b03809072210707100030084150b0755240c01116 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 991946474 1250 991945224 991945237
    0x120f0e0d0c06060b0a020c130603020d0809121e0f0c0607031b1e200306040206030a090c0f05100203130e10080d081b0f09100c050a05030c0706090506 66
    0x14007a500a82104000054003e60010900e480c40d04d40c40342c2d0480000b030f40b1620004003c87c410081104a15a43c18581c440d42027035a40150100503c00d41c2640d40c950a5405101c40c01c0d480320350502c50030300d007030410000346002006401c0800c1412401b400254501244036091003044d400505002403141c980ca03058443c01a054607001780da42c0c80c03540240300c00c8000d05802405c0f031840d0714041c40007075003100f8406410510032103101032098203040801da007004000d840964035400403030104016241c0f00700a582c000d07440242c0086c800c019a41c401501e250981c0c402a10108181c40030041480c00440964080190b40003841c81c0502c84110300f0140311031070041e4001c0d281150b01142c00d102251042d0005000480100d500d03201c480b040181803000304441810b400002c00318400107a041758801d440d14010544c002c603050204031070400c103902480248620410003a00340b0030000c100104031226840e80070b00c000d9aa10f092250401c0d0070820150403020920800400802c600d444000807a0320307 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 991947724 1250 991946474 991946477
    0x6091104050a0c051206040b060a2606031e0106050604090605040605060f16050c06030901050f15030a03270b0a02010509060420032b030605090c07020105070c090507120f0e0d 77
    0xd5691b560000c2d00030881001072640004002c9140d4005030303040a90070100002d00110707c90201c03950085001d401c40b08486158060b0084032000e00607162403422000400325120001c5216925403010454a41282e4044c819458480c070003040386003051302c25034020380300942e0501d01c1c2c0548a0629002c502c5440c00c0c9640e22220340300c40d40248002400b401340d40200c024030f2180c0d02e05042d111030303002c1d100a59951880d104448085560682c0c03880e40120b030b030000035025090f44d054a88040d190507201034aa42800740314100500b1602c0c104240d0000030780340801082c0d458a10141c002421101c00800c01811548403009010120307584000318160050000554501604e001001c00d0520a0f0040d05030039810941c80c4444000c401103080d45420541907508101c0155900c00b0010188070a40c1c4405c500e1900704488005075105100620301036000386d1281e103500d0b80d1058110308035002141c400001400801c03148204200d140074140880d200110309101060346640441d48410b1882d500070b0 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 991948974 1250 991947724 991947757
    0x30e130c141e0307090503060f010302120601060807051804020c0a031d1e030124170a200a0e09010f050a0c021c030b04050c04030204050c1201090903050706091104050a0c05 76
    0x504d030070b01c90b40154000d03040c081c040c0e03803a508226040c80c0c0c2d07401081c00102d11450241801c42c54001c4005191070488200d9580c580e2207454110042d00c00780c0c80445142c040c14a80d041e072200d9a112400101441e400110090010040c2400c008001c54110703520b031480361130382c151641040d0342d6000c03402442045060070020340c42078031000a0300500c2c5030a09054444014021004010f0207412880d0413110180150746031944d603080500d0303c60140213002441181585484401c10400c44040003901d0005000340140310b4680020401040f400c581c0954103a442c1c0207003039180c81c958000d06070003000d00402403080840d0250080d48503502962006206969055110100b034402e4200506641014008011604045406406640c081d0009900903402e02006c0340f40b152900c004c0b12014034111545200590030b181802c80504611003064040003018014240840e89502c038131444d451145183c551300722494020301041e140700400c2c1c000c00c185844070240c0c0c040e070010115003071303e0110360156 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 991950224 1250 991948974 991948981
    0x809040b06091206180c0102101a0603100801110a0206071404091503020f0f010801031407030b0906040c05061801110a050303010e0f0a0c05070f030e130c141e03 71
    0xd510350003a510490760001c0c0d0307480482c0c480f240c08038100d4060300c0c0b04072044094240c203402980c1d07550b01070a08103006034442e000d55420040c0c540e00138802000a01d0038401540c031007100155180d00140c8240c01c1c241040d84040021540910600e9a69803408820034109018841c01a444400040100081c011243e00d20713030072407103480101d60141001840401c130508c120700d62803c1c080084d0008900503121402500c8103450805842202184141d488018a07821aa03c00030780c0040d101c6804018854110040005408481405d214940c40707402003180e403409003029800e2075101c0d40214052941000b114141c0c100e80b160400c2d40140a0818882843e0641002840c2122054002c1c049000100012400990440c80903008500c403d0703c02c0441e885545041003266030130740c62000400c2c020801c0304006181c0c0401d5a64a500904021000c04841000b0070307070b40000007020080310340e42c0300c1d0481a055003042507000b2904510680d41c0c00c00454580c2100c495182c501d20a00011011000 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 991951474 1250 991950224 991950229
    0x70f0c1e030b0a0b0f061b160e01031401180303090201120e032502180601090806011404090201020f0f0705010216120f05031309020301211109060d05121206010c0809040b 75
    0x400300d5000b4081c0c0040d42c1c1f1585003010203840196070f0000481400360510311500c29803200d83c154103031000c201240515074070f140c0d60002c02c1003a0041c9141155210381c849402c4030f4140c0c0b22032074483e000740c5010070365103040d10005042d00003403000035001625004c0a0181c3c000c0001c00d9450301c1220380300f0303c0c1c103010001c0d00000700c0040d00c00000390301040d079040d810704050310642c4440c090700c02038950310349441e1034580c00d6803240024041e000c0c000c0807a1031400c84503d840e0304001d211034018010380d011500980b2141d4140400020506015400200b0400c41564100021014080e1403848040d8480c02d180e0800d000c2c0c10718120207001d0000c440d2104040c4403050007181e030540150102c2090b110b50b2540d15801a403c00d10510707511803154003680080030302420b030780c00320103510400035481d803d171a0303003005203025010b07100d0340d00400e140d04c4002c00030b00c04209048101824124482d210710110301c00d040700b4080204800d041203500c201401c002001a800c0d41c0c54104201d6000c40d50752581d001 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 991952724 1250 991951474 991951489
    0x9050c0307020d3e010509030406050f0f0c060f07110a0c05060d11161e02010806040504050727050106090b1c0b0a1d0105091e0c070f0c1e030b0a0b 65
    0xe0820754452001c0464251100a10054131402c10000340302036903e0040e811340364041c1d84110804100100481c1c0c501c447c0e004001c00b804921026002c0c102241a050a850004101c400050b580050018480c002c0d81007100c10070010703020300c02010790003103690310087c01c60340c6031040301d00410340070a11000c1c4da01542c00611542c49009043c503120001d040503205d000400820603111640010708500e08804000325003000c20b82c0684036001076481e40c074284001014028410707540d500800c9400316a0120609185406a0540400171490181201e030302040395410f03071068041c45262a810061000c02c64245c036074004005068500b101c0041d4005405003115008407a4402a6260f0201e00b80000140c4a41c2c00c2d00848901c111aa8a40084c001c46400c01d50790020040c14140d14004681417850315954000c590011742c03803c0a03400d503915142148604012615030342501414008110700c07a4584e524801920681220185141c540d80094440a045207110711780740ca481030125100c0d01c4 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 991953974 1250 991952724 991952777
    0x90a090b1c050a0317011409090a05060901021b06060f090a200304050115080c04020f0f040b120f0402010e090403021c030e120306030d0e1909050109050c0307020d 72
    0x1810400c070501c5240158860418003411400b06040c20180d8010700c500380115416078aa080d01a40c0c14108a810410b034200004c0031128244511a04040002e009200f100e008000e11400540c8650744400c1c101a80c1040c031442045a80c003060400890356183d550790704452030290b030740280702e03140c802e03842000d050807d4991000340700e05555006400c0f512801903204a010340300030005004d082441e400c04407458416001181d004588000341c62401d607005091100700405ca29244c84520041d41a05400c0759100b1101d00354045201034800c51000c0109074012610121954035240950000e01030804c01081c060140002c2030000702090300800c040603a20708203a0b003050130803001c19802005014903190350300d06402014a840605401001a68010703c801030141080058040080764000d43c082011035005802d01d0310008000880110300c2c1c042d0403d0b481c08030302c943c1445041002d855019000f2440240c0401c20410115408190001d01d0032180c45c080c0f180782d00c489a803000062140 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 991955224 1250 991953974 991954009
    0xc0f03230a050322050a0308091515040e030f0313020d021c02010914090a050705040e010303091a03131104111206090f01030512032203080406050c090a090b 69
    0x303490607800d03040800382d4854002c40c40c02024100309501c00b0308034404202c070b00621035480006107000290092105581c0500e8000440342d000e0b000425079950300f0380c1980e8018001d011400c50282e1030030720380110a8800154801107141440003030f520501440014424050411041050030865a801414424236900201100021740000702c07010b5411280d200228045120400c000580087c54211500c1c010801001c00e1141da40b0fa10200303020309001009401013003c00c00001c070309641603441c40d9000e180680c1d80c50415505080f405801c0d41681404032030f44c40c03000d00400c110000840d000380c600640c0041164840e045520105010f45050301d1355a2054901045001d41e000040f444180314000440e51052541c070303124402d005c0f403d0280000380254200f1032118a00856140040d0340080e02c503a076442200107900b07402040992031840c11000140480e00380002d0222501501e07400c86407084030755152080001c00103c18118604c1103541081d00c034190741a19956040c911030300070030b22 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 991956474 1250 991955224 991955227
    0x1020309040e031c0c3501030302030a08010906050d1b05040f02131a03061e0913060b03010b100f021f02070b0703020a0f0c08190f0f0c0f0323 63
    0x18030825441c1d400c04003200c8180501c0c1300f030001001c0c1203030241c510071104648800107680c50805410614003150001210440c2c07071381c0000c5c0da1406031840307014000c50003940510b07241d10350750740d00511000d41039020350861420418180583e582d8582080f00747e55100740f582a2840c01c0d0320607450b048416034895039105183c50780d014004150f9030000d210030380581c2201100d10b92030700c41003660642a000100b402c50414000182a414061010350524400e20040ea6189400d000081c000c403904441180118103800f9106e0b0800009004100d1040b000f10300a0064994441c0400c03400b06150312040b00f0003d03000f0001c0e61407130085c04007000801861b00c0311601540c401803604041d41c00001e00f140c86041c4440006d4025200f03200391402d5610f181e5899000c0503030604200c4601240844c19034220b0403c2249114a404494100001c44a9901c4100003011015400b030500c0c040c0c2d600e41400d02201c1071620b40003405000c07007007032940c2d414103204d051841c0358507610b408620882d91201e0087c00 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 991957724 1250 991956474 991956491
    0x536010902040920030a020c0709020d1401050d03020d050f04240f090b180a151d01020309090a1d030409060302030721140f010204030303060533090102030904 70
    0x200c81c1c00601c01e5410144040c04460000a000703100c0f40c09101007003442c400b00744003141d00c66565800420710700c101c500c00c8940a43e150071904049a1115810b9145540d661503104e68188a18003500e00405040f1080a500c03c1140c03006905e4180c9280740b802003100000d01400b496032020140d0b0080c001c10800d212489070100c0d240111440f0b60700c000703800303d403007031101d0700f501846040c01c10b06450700d0354009414440d905441881e0321034954102503200b5500e00010829610f694403010f0040015550b90140000e41c40407420b001504403001e504540003041303110b03a952036100a454002000e600c000401018000c0d00244c401c00340007004045c0d0100140000e41414150444402c0d01d00031019207080c01c0ea5140031000803a0600e02c410f0a54590b1031416010500e0882020b0800200328140e966071154102400d0899110781c100710040384e940d80040c0700718248a120904005c01d07580401030b00b0041c528040260b40201d03803403402ea100c40055443c620782d10a0041e20385801d00600705001c3d506 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 991958974 1250 991957724 991957739
    0x31d010b010306050907020c13020408250e06060a0c081e030609012412090209010315050601180b0304050c060309100e0102030c1b2401060e0415140103060e01030605090f07053601 79
    0x18004416030688401140001c130f80e40303907813b401500440009140604e010030f00581655446c0c6004c2007510001d03010b00c002250700402c0000d400001c40d02d01070090ba01d01e00501081580703901a000421211700d5441c61078004508100511b4094086082441620561554407005000d46d100000d4000e1402400002000748002035024a171980d07440034801c0f83c0e201e00044603081d20101d2602c6070302e040b5110402040c0d070340400035a0058011404d903050210080d000c03980a80c01503c0c8501c2a40c400d2030b00c0081150380b0722a020540c0100300c025490350400540c2e4141a02840c44480005800d41e0b41c407a104c800d04000f03a000e8403180c190030301009191848880c00040b02441900049943c903144807860745040d2045101010070b41c424150740a00b80b2000c0340401042403045e905051b40e134240440d02d07040c07840c00780f802903100c0c000104061401405140c24110801e4494005510a40090201d503813200000580000c5c2e50210364109146041c241d1003218040000d11030701d07070343d5a0010034420b = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 991960224 1250 991958974 991959013
    0x20d180305120708060307171614130218060903070812030402010f0513210206131d040804060c11060a020d020609151303031d010b010306050907020c13020408 70
    0x90001d588036102551103c01c142d521000c1250785a40c1500314100a2280858104580945140ea84120ba800c0c88a0100c00840c031a5140c0001d494451240e0511003285084450507c581103051025424079114007403140e020f506011000d40b00e01d9002c0380034102503c0c200803080003800c1841c00c544240c20703400f039021701551045d90160b00088245583e502140e0192003103c0d680804410304203d4a4a480703800000850100c411200706030700c0e6a0f03510003590b0354078060030b1803a40e0521403080c0b2614100c45d506408550203030680ea02115001004040740c5000207881c203d503c2814483c521f41703081c1c98001c40c19450100c0355a44503802052004100c2c0d800038514100020340d800302c455984540080940c1c8440c16508032080040300030002d0b64ac2c0071076421200280348641404204c09c100c0e10710700e408460310b20242c030300c40d60341d079102a50705581e050042c2c800404043c0e82c240e0040c1804040207480d00c0030500c40724003074112004083c250001d142c1c100c0c1c0040c101c11082c3c9080c808590500e4014 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 991961474 1250 991960224 991960237
    0x10e0d0503010305010c0e090a091407080708010506031603140109080d0c09090e0a0f02030a0c17060601050403020d03030504230a0314160222181a04080a03020d180305 74
    0xc0c5d40c0b8150480042500410f203000c15820003c101280a0740d49500000142581082c12038070418a1214074100c4101041128003a1031540c0140c418282032010b011b003101c00080403103101c5d0703100c09000c400e811014074602e01070380e401026440480745514059400341ca0701d9140200210000074898520f0070702584640500d910540d0340340e90031503a07990441c2c01c0d07421008209100d034110045980014801d0030654900364070140581c2d11401d00e0b51203080c04042c10b5484105511040c40c0103c84105042c000709a01480c2424118203141c10340e0045041da0a5444d03004040c0342d901e0001ca010311800c01c04850801d1031444c0031001c5480343d60b070182d031600410725003100070608900e01441d00000020070b49109910240200d658035089408114400907001480751140345452400310200041d80a811406010040c1c03480807520b076460710f080a03101d0441840181d50074030050200095030f07401182d500d11603a01d0302585807040c0c03840319801010043d40e030040600c030b42d0b0640b908054200c00034022 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 991962724 1250 991961474 991961483
    0x1103041a0a080a1137020106170601060f0f0e030a050c040b01030902030a081b010c0e210607110102090d050106090506030a0f30080a1d0a080903010e0d05030103 71
    0x3031544a0403050b2095500c0c000120410314003d020081da082049511180424007280d01149803082800305da80c04820040b50342e4005075102e07030b002d101850910a0320446004944014040c035850a1001480340c4c0a140c5100200054440308031100c0384116a031a030740540040a5540c14513080c5411507980502c1e0075180e000e6401c140c60700500d90b0007071040c4510190007a000d0400c0c80060764500c0381c0c03580100c1070f450715100051601c44c031041c4244108110898240c0b070380c100d42d03c8920300300642c0018010307080c0740c040385401c101032191740b0206146411891600f07212501c02240e81c00a030290060701101c0d03401000001e284000e010054200008551252504021701d0300d652044c1902c40d0b040340c00103024031110780c90010000302150315421101303a1200201c02d40728640810a82d050200b4480c02002480c28814031502c1c2d04a0302c50744000e00300c401070419010b0211982a80c4800484001501c030020224120725280c07000c2d003085911004040035107200d0709803104003400036003083c0019134 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 991963974 1250 991962724 991962737
    0x3090b09010c09063002040e090c0f0d0201200f101d0313121703040303090506070201150e04210903120c0327080609030702030f010b0d031103041a0a 66
    0x710303140a030401109046945e80d80d07007020380d11103540740b000c1014a220b49032016030800002580081c13014103d8012030611014090300d4441300f0420100380c9042d14410f1180824800400050707070000312440b02c2c400d800c401e040f0300c02d070451a0715040408884403080726000d90402286050744035404020b034081c01301001030490002d1040e15030382c1d018070403405070340441e40c40e428015994184c03419854980b0030055813100c030800b0000c3c42402e800903581100400d449030140002c00400b80101c43d440022807000300004019200c000c06007201c036200302041c1040040100b01440320a030f290010800c2285000e50020301c030751000030064074043c4020351b9031a400c0d50318410407501c43d2180300020f0b070b0155101844c2018290300038001005446410a200d2089040040d54030410b1001d41d100d080c400f80919201c81d610b0040c5401c0085105c0302507481d916011400c160340c0e440c0c000440c0388030780514012180b03840c080d072110300d58813868200a64016414a4640d001e0740800000d0001a00f99079440 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 991965224 1250 991963974 991963979
    0x3100e061513030c12230115090605030d0c122d230f0301090c021f0c030b151608120f07030c17071d21070b0c0a0b060103090b09010c09 60
    0x417002003020b40014440080341542c0100d000e21a40340034840e500501c000a00c40030000d8190410b43c040e544004501038641c01c0420052078284900400b0552609003141048060750340c203203110800074044004d100c0c1e2026040101070707002d11400c9417440031a00d200c4040300c10031405401d0380e50640318400d200044401e0400c803507940030b0a46044205a000c400d0a40c1d0030058013401030056010010708500c0740301c0c0c00e03010f0035901d18400d80660384255400603c5040c8014010203944524003d0782c003400c1c4e14448500380040840032100040e48130034204040081901d442d83d064801c07481000021942c22040c00042070511502e140548203d4034200003004295400740e5100070248050384c0010790600000c0d03115030055030b001d0781c00706d03040d1010a519104000001e01e6500d020950b0544102d9000c00d58106450410160028000c1d001040c2d040a41115a8540d07a00360820014404405400441c4484e4001d42060300b290b944403a0b4018030740780c40103c00f4000c00c88821440700240085900 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 991966474 1250 991965224 991965239
    0x20405091509030721050d1a040c0c05030415031b0206010e0604050601021903091a03090c19031b0510021c090b0406180506031003061103100e061513030c 68
    0x46507240c0303a100502d05c4002d0795210602d6648842c40700e884d01482010000380711122036502c42c00c000c2459850611204125076000c1c402194107500d20758003404061304e91440410760010507a0203d0302140f10741d80050000e040e048001e064245e003400c2c00d040601c180319045c140c001c200d060586242002903107607551014200000c2d40d03025201540580c03c0040348200f000001000c07406241d0081c2405600319566100988614018809282d0310590220500c07001e00c9003030040362556042140c10440b2020000d030004841105031000400789610058032103940c14061307004000814005284401403207000381e010b52151510b05680035041003811483c0c0445008000c00000c0c0e031300324000c0030300309403c2410035030300e560104110444602d80705d600000d0564401e4010f500c04d0b412081d000905a2841c60301506481d00c48150a0a03140d0074030402c00030404200c044401c40d102401c0121260300c5030004150408801640541500b4000038036100440b100c04400040380c1c400c3c41d41c0c42c074841e43c4044 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 991967724 1250 991966474 991966477
    0x2150606130e0615041202030601050a0e190f09060603230607031a030f03120703020a0c3815010207082d03040e160c12080a020702040509150903 64
    0x6a40045000e400144402c01405682d82c1e800000900040c80c00c0d046000503003207030742140d8468070305490071034503a00c11030405101a50050200782c5418440600b40905140c10f010000d01c041c490115500a0003a00f06444e0446400a600ea1004000303801d45030804c20083c01e2907010031754919403e00d01c2c1403404e4507282007105640111030040d01c210384911404401415503c1401c00d481d030040883c0c41510794007409000003060030800115900c441443d010504500014910814903105100c0d1803d55500700e000c1d042065440480d4441d5035940e002d001e18000b0305007481c24001c007400f142c0b043c2c0100040c0d03200b9004000c0181039a030a81c02480c01265124141c2c092440780d500b04880c2542102d4818610b1400c60240005078006500d80d00c0d442d41c82e64211f50700c1034002c1c881070700620140301d504009600500c420352404402d40051602c400002c14400c0d0101000c00140341e001403885460350307069803d590b034002c0c002d0040b4200040c00c0ea6a4101650f04100702403485404213142800c00030 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 991968974 1250 991967724 991967737
    0x10905031605040b0109090216050127080901170907080f0a0c05060c011b080a0b04050f13080903010e070306060e07090b0a0e120a050d022109030a020a0602150606 72
    0x8071181a20381040c007404040c00e070031000305040c007044c89000304036805140040e0840b000300c601d0a000031900c0782480390a440242540740ca03198500e480380300d0038400320442c090f8041e4000c00d017160f5840700b010040300d002c0104240c0503210303a041070130302c01240800700c0d8141c115641503044429280d0300010090b101c07032504d07200820310030361024100902c0c1000c4001d04000e001c180000035006c0380050320312000d09003c04007200000c65030300030040c1c181a1071040506841c401e440400142c501038069002a002c0600141036000d0311110343c1e4100001c0804460340041c01034000d00000b07442c02c6402d40c0da9515808121515400c10a0204404c100b65411520070056a46c51540041c03401e82c000201d5440500704008109890903400025160798030104c8159440c00001c0007845180c5c00c001d4101601e04015a045411000c070240b095900c0c0000044000200444c4a5030354040200007450b000920600940040001c000060342c2600070030aa03d030303141c100e104a60169a584c0412000744a0356 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 991970224 1250 991968974 991969003
    0xb0c0d021b0f0321130b011d1b03040308040f0c08100e060f010302060c010b10080a0c030b010e01120603050a030302070c06030b130c052205270a050c1b060601090503 73
    0x11040d070b6a04900780a200d1743c00902083c944001c02e00203440d01e0070400026002105545404000d0140c1600725100081d400941016104681241311080d00241c0c4405803000d01005142008202406420700400190540c4411814081ca550385081621007510400c0103126600e02003200c0900f06c008154248588c0c101c42c40c9240d81c3e82960300f0031215030001c1c4940d8405640c0d03501d0704c002caa00ca1000302d03c48000c007501d0b0306e801483c1550b03924041d603515104a008141c2004c044070a1640c01000070f00c0f400c0d03800d09102c089540f0924840000f44865400075055106000e07100007890741650062903040d0041880303c9505880311001d03015140707256502a0440d400819011051501d5801003001207200c0ca070940c81c05d11211003183c0c03a403003110246042e113009164104418a0f04c104440103882c0f01e84442d90480d0f40300f0340c41c5121407c0040c03004403001e4075031002420f660400012188800a03031020084000341001415986020403511030b07003c64600f810118185c81c0000d4041700550342c0 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 991971474 1250 991970224 991970257
    0xc0409020f0603190f0207060b030f0c040506030f150f061c080703050f0304060b09010f030c0e040501020408340302030a032a0305090307051504030b0c0d021b0f03 72
    0x10340074850150b200804004070001c808910968130001405003400390b203030030200940c0b2000b1601340305040b20380b001d040d54801d03401540056500300c804140c81e14145011500010580c0d90072012a00704103100701202100d0007240c0c252500100c440b40c0c3c20713000e04410341400300709a4800041c0821004403407440c2882c000c034041c92800042401c0001c0c030380a482850f1003428000302109c904140d4100b52422203c06484500f02203142c00e205002d02c2c010201008508030071491502c17102000c2c1494014981d18041c200001818408250112802001d0003070071564943c144170385001900b510b4840c5004220310700500d013210210091300000680e500140586000146941c040d030384c2a85044030b00e650112030442c0701007141105003003a00e1041c007a8440b207035a071138250100750400c05181c0100e440b841e80d4001a9000748500c806640c00d80340e01840382ca42e551569000c202d054041d01c2d83c80b18805000080003445c1c07030301d01540460a140410216008240802000703612809107034505958070a8 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 991972724 1250 991971474 991971499
    0x100221010b0f18010903021e18100506070602040b120a0c0203210612030c010c1e0e060c1501120302210910050c070b0c060703090c030305180a0608090c040902 70
    0x19483e50340f007840e03c0141440b00e4416501e0b4080380c002409a00c130041c10000c44414441d00f0f05181410b13460401151107941d03414a003002106105103400e0003086c1c003a407008134065040003100c1d8110780c0034251009901c2d485544410b110003100c14105d6508003c1c506203c1c55845150002003038485400240c22001c014900e1a0030f444100c0000038001c95006840300051064084107100520309145020000f00e504801b40d180541424013540400b1844280409681c0304190700c2410034401c60b204544855803400e400620030310380784060703c107080c030854003900000b40b4414164100992030300c02d4082e100c10381071034500d4065008144901403590041081400c210745042c0c614441c58000c2c6080190400400e003015514084640c0c00c00141000c001584d0500ca850800140c0d030f0000c0d0505c1d091040c0c1080343d9070689514118400107090000118054603012071029040c6040d20016240e041640d940740d500a018240664501a003409040a51000790805001e9421400d40142038602040c9 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 991973974 1250 991972724 991972747
    0xa0201090503181509090103060f02070605090129090a051b0406230307120f0905030c0106031a0c040b2809030303051506251401060f090603110f03100221010b0f 71
    0xad21903036502402d5800c000d1880054514819203002e40d908500000c0c01422016042c0d05010381d01c5416031452180c00c0c190314050b5184008a940701281c4203011625403540c14503050318281d1002d002000d250040b40229105038001201d4048038000c1902c6e0f4100c013642c0316010002d01c01079a0580006408a80c00a6034155507004281c4001003a8400107150185885660941d0800c420500460751540802c1050000c01200c0380b1450000d400f1580a40c20b188030401c445102c0c0d80300748030201201003409a007140345c0e100a145036a0400304e0b10310b540c0ca0f8500c0d0040800c0001d000c110003003031805010504c16941310000440d825405001d051809401c0350307042c3c050102101c101e00c0003481e58042c1800241603070341191000083c3c0d10012a0341410600001c3c49201250001b05042e40360a00400104200d0704e644c2050f1181070390303100c82c030310002000300c1d00701081002d003040748500010300128969898a50300849a0b8190b5000400340d80310f0950300c6945c4141a0004c2030400f0601c1581d2001 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 991975224 1250 991973974 991973981
    0xe1c05120a0204080606150c0a0c0e0903040605160c0b030f04030807111203270f070e04120f0905061804150605030118020405031f051305120a020109050318150909010306 75
    0x125103845450b04000503059202d1030b04112a4040310100712ba801c003080703d12800440b0540107905040558201401e004d40201240103040f8140d000302d0003410410140018032801d02e019010301d8841540e00e01d8240b1401c10310300c82c00d41d021000100700e0702c00070b890140f00320450f851100c1c215010304540442c090100190303403c09810070003403414990041c4840440c1007a00007050004901401810994006040c00c1240543c07000c03001c0c0c01c4842c200000036040c1c03440343e00988814102407081b128824001c071811011600020340100c40016101c011a0130003001c80c9204108803001c0c0002d003500c003441038400c4414820000443d80900c01400582030324003060307071280c1c814400181041e42d1000002e180c40c3e8403a00c456007000386d4520f52007800141d070050507030108100e1341c1c000a5142503680c190340c0c2c1041d50108007841001065002440e4402c4d045030014640000403240ca40900c0d400c00b0b01c1a100385c5070300301c0c0300314000c0450a402c00b040e102951050380c00181030100c1a881c0d912280041c = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 991976474 1250 991975224 991975249
    0x33108040b070c121407080c06040315021b010e011116061d07091a1915053001080a0309060e060904051e1b040302040e1c05120a0204080606 62
    0x289880c909001c102d030390404004c101c0781802030100d840400c001030106801d060094004e0307800d6412209440d0542e4540c4021103080f65401480d4034510b240d0003051800a015911414004076202480e1402c040415000b03111a400e08100030042c140468000140d00c0c0700e070107081802210b50382420408549580d100310002d59803404005203814003c0700c0d5908000e603d40211041541e124994202c0c1c00309a51049080c0d01c05a5583c00f0b4000822500160801e141c4206080c0692405100b55498030600568103d02d0034040400c0d46085102002c4282040d40300341c110380100380800000d1540780000d00481860b415440d503010040c14404112016000100340d550403550822807072580e0f4441c4e2141070321a10400a030a81d402c10594030f16440b40c10003512100c03084003001c4c180c20ba11000355080341c085a50483d0001145020b12151300c0c20000c0d003d840003e0180c01440c0008069007200041c80300b5408580d1802160b41d40c054000f0880c09240608102903000000080090a0640e120100c = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 991977724 1250 991976474 991976483
    0x204090812221a1503060106110d09120f0201120207111e1f0203070b01031412090612062715040606091202030a0813080f0a0503070b0c090303033108040b07 69
    0x50400f5130700860315040080e0300020001d805050103040a200500600d80700e1040c6141c20195580340c007901500d50384038107030081d0018040846d0001168040d509024940d01241c20640d11280a800d11209100030f108a0a00581c2c00d004c03a50580a03210468400050004004140721001e106a9a000c10070084005d410352100f0000d10001c1202d45040500852007034903203d80301a0b800e08a0b900b4060b52900c60b18041c841444044040d0340d80c41c060307070b903a00341036070f00903110f40d8940000a056148140e01a0800141900d035034062840d06029103228200d000201c0c9514008441400708540c0b0502c12140041c500714802d104900f03030392400b5440140002c0441780c1180482c0c6a00c200c581c4070300c1000048454085040120400c02c1c042c0b1070100c0d2028020f06580700080d203925444c1d100e03015009040160b603000003903184041905807441d050010b01280d44a01e42241c40e0b4503a1103142ca8409044c0d14450703e55215456100b030b4298056900404803810240b41103920410740d003100500700e4 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 991978974 1250 991977724 991977751
    0x10504140417041e080c0d080a0e01020c18060108070806030c04020d0b040608010501150207030b18120d0501140f03070603051021120f0504030f0204090812221a 71
    0x13611038101d5010601c51030056109900c80351502901600d020b0190814070b0160860403d030401040400d0141d90300c1c201181000880810b1141c0100d0a105000d6400759015100c111045e02d142070043d80d0b144103c1c02a2104801034890201c00e0701c110000725002c61b40359000300c08021003400c00350040c03c4503a079400004240c4903c4c01c0c00003030076030340281c20141050f990b9600402214103018800440154240045c08406003503451724195188014000482c030005584611190305007081a121100c0c0111159500e0b41c2460b0411b401502080c86030b42412841c1d0b9040004d5032411040f000d80320240200107003411843e068040d40039000080c04140c0f1201c0f16900080d035507810707241c0d2900001d850b62a2a88003080c0c0d180c8450504c82121245081107051900c1001447d084000c440540f5000080b0700e84501c400d20000d0083c2c500c88070000d0070344030b011895162111000c4c003100c0c0201d040100b01440f1908a5500000a02002001030540700c800c12a1013682080c0d007040039000380c030455240 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 991980224 1250 991978974 991978979
    0x207020405040f0501050c0711210304031506050625080931090c0b09130222080105090304031415270a030816110106080d0801050414041704 62
    0x2a003192802c980946085034140390700c01c2084000c1c0308480e44a0b865034422424490b607600c8003102181d1301200369005149030505140083e0890421030140c51540d000c03680c0c1c950f22840d10b400c6101196100ca801c80d400e092000ca02803903c0400d803103d03102e9054110340343c01c020709980c031101c42040308246c0d40316908010394400c9403201c8401c81c0d441103440d81d5686103441c5038180c000e1958500181243c0720b40c6003c940381c0004030703540341241c2103c00c03148a260303d074840b040c00184a07c0505244940d690b20014800c55810307070400300880c4a40011000304041a07495410034241d5500301c0d208001038004210600016a0301902d42c1c0300e560061003140d600b6981001031114009007600d43d80c18403100744e1504420420369460391503048643c0c9000e40510040396502400444e00504240014003008010400b0340307102d60104a940403040c8002e010072591805010340b502c1110150000250742c840c000328003400d180c0207103c0c01140244048107203550391384444150342c0c000d08086484007000c0200 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 991981474 1250 991980224 991980229
    0x40f1226060f10090f120c0302060705011803110c010305070206160302040f090522150203090309030a03120e210a0504030f06022104120e04110c0709050c0c0c1003020702 75
    0x500c43c03005629054040c50400390802c04074407807903200c03005070303151500d2440c00104161f031948212607055039140e8a4417120318002d4054000703500c0150440240c00c013824180b40d03015a804096004189c1502d050116110044045d114120380724800340e4007502c04107491060201c20405c0c400b003149401414107171200000f807611481940200300b2191600b0138445002014000b0001a001c240402c0040810b255540302c0d9026124082e00041540440000c25501d414811606918401420307162401d803285006000d1040c00007031307041154644950301081580000315041294003c00013114402c0d554450a40954084d519080070010180000400246408007a2941600ca008050f032100940a000454458070206062244e10100240004980544800301411900345010038800729084041405010040031000c81e10744005104564030f10b0224011080da02000740a0086031641c007038080301409440d2500d000d0383c105c501c1c812003c0c548560f0800d003082981c2000b50030428981c00 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 991982724 1250 991981474 991981489
    0x609030f03040504180f020609040f020d06090f14060609010c0b01080714040b060a1103091c0209072f070902070f03020609160302041104030506040f1226060f 70
    0x1030340001e600125091010b46864000d14021803410540f80c25040d02c641c8030040c80107540d11010b030090740f0000d81d40005858980240050f031001c0d0f017042d540c400100c42c40303c00500d01341c4100109545841c18110003038207140118104008042480038a0782c0f03a1038104a103a5006000050503c03900c0d6490714009440b07000443c0c006d00000001c1d0a40341e284c02417094420b0344081c0300c5440786150444005e640d98800702911607002461428082c89040940c0c1580345200380040141e0045e1083d8614046140b9600e594420718429105807040352075030182076070540d00b400d0312900c1e5482c0c102c40320401a511001c429040800303030421035200030798031000c0500300c0c0d0004000303852801210444800381078040203a588c10001110003040079401910007200595800c1c00024032a0392611420380c82d0106d41d40555000d140c10100307441450034145809034030a000110704944905e000000000b04c540541040b94201d880100c0180a858102001c005803c44c0141295030291455900c8805501c9850 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 991983974 1250 991982724 991982743
    0x1203140c0105100e070c0c060f021f090303060e01050612040318120b07020607023307030b09010e0403050327100501090609021e0708040b0705010c03050105030a050c0906060903 78
    0x440c03070799a40703090104041c3d42c40801042c080601045480040004041f5048802181c00d1442d2203030000900705002c81c20301c9101030280d80c070032805940220241005034441064a407107510204581a0344100c40e2408000c00d100d281d038408820b000c0120004021218254041d00c03920b0a00e40300c40c104441895003d103107420943c80000101c040e14200060060103a400260a000030700b01858003480080d640c00c2211000512001304481004808891a43c1c02d00441e202c01104880c030f240c0710600600410b9080c000381c2c881c079601c000000c0c400040c20705c034600941d010341c0d44915503174903c60681020040a10980d03408031000460901ca82c40a1001d42c400c401c00d0354020403694034040d200800d8510380e170060707030640c0c2c0304021a900803a582d03001003068460b0100c40c0b07a150412810203030118040c0b45d01007842d400c0300107104010003106500c281c0c41103030551000c10640c1d03210000e0541c0c5401d2110000e023542c1c00781e09a1a13840c80c001c058950300000c0101098586816100400d09180241 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 991985224 1250 991983974 991983991
    0x150305070e0f180622060e010b01092408060d02090a0c02061006080a2406020304050a0b0f1b0c150c010e0d081f12050a060606091203140c0105 63
    0x14824482c1401c20400c409810140c80e11a8076029509521880e443e0980a011200400c4652450708001180c4120b25040c15170041010892100c413061101d0107001400f88050000e4140d41e40441c10780be43d82c070051040850f0341c1400c02c2c803c1c40c103c001c0c1d07040100505402e0344109003480c10700050f95420340355840303084003660104417440303e00c82c06460094043d080505240140b20103202c4583d019a2107a4080000c1c0d4011511000121201c03100301c80b03802c03101c0c40032041300d0300205405130000b0007403044403400d072015595030ba518840220b10303024100d285a201c80e000c00c100031010002e4001080d2200b801c000f655401c21004001401c48145506406075055000c240005030080a2040c44200b07201e01015000002d51440003c1041d10000d20140b041610303001251030310300040b0441d9001d800e140e02c1c0088400da007410078650347c0008000444080d41042004a02c0c14480c2440000311420444254080000c03650160380401c08020311509002c1c0911a6a9001d9401d0081078040c45a4 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 991986474 1250 991985224 991985249
    0x61205091207120305060a150c0602070b01080a05070b0901050f09030c1009031704030515150a0e150f031f020f03040b01080d0f0906300b13060311010315030507 71
    0x214403000d005d859008041c00e2160343c84138000c100310300006000342000000342c5000407190350103140610080c010400060020580c01001164190f40000e1202605000300225001c90f941c40c051045213100e100e00d200e0025000388610034a91910001600d15101c005099616068017100070821006000c40000c2c005100d0b5401001804018002000b49680c2d0031245841d040c00c1d51a8640e40c1c140d4040c0c86ca42042c0b40d4000111200300c3c0380e08040303040c0c0b001000035941d0b0b1340d2504a042c020000b500c00c081d190456000162040c5880390854180076000b03800f40480d108181918220604101144401c1503002c003d8240b0100d200c0d401503104510481640300c03994180100c191800e17083c4100c81080c820380f002500081c540048200c4100e502c10b10b0040f42c0b01260500000c061002c600e03501c141001d50100380b0651108a400c40001c4540c15590710301c1e05208011780405441c07aa1202402ca20003801c00b01c02c0b154400c0d0881400076080041c004d0030701c0e0303880c0e42d80ba18003115a84604c040741c3c0c2 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 991987724 1250 991986474 991986503
    0xa0b0a052a030c07020a080d05071101020a0b2d040f060c0513050405060105070b04030c030e010e010507140f070612050109421d060901061205091207 66
    0x300c0307800300721240007101603000c04a0030303107081c2040310710001d4511000207401207403040843d69040c404030003826010007a1001e0300c40380080070304190480c0b18121507280101c600c85203154400201c1c04201030f0000d143c040c0b6600c0c2c049140204000644000180d60000740681d485800190002d81c0030340d20a4610800c10003040c02d001040f40c0700c070341c141000c00c04100010640c41007e106010190f480884000940c0e84031000107031124480d9903c01040b01701d031901004103142e040342c4010a03042c0a40c54050078045d0000044032900580042103001c0f610900c20342021406105000c1b4640e0410801c0302d8542072001a01c5107440c032594821000208080954104013220780103c5004040c4d48806028115050b000081c8801040034241d441d0f40031302c1001f002c45d050400020000c0042e0081020070320340c580e810149990390200c000c0d0058140c050118016050002c9454121040740d80c0d8003000c024025202070182c100a031540f001445214a4140354900308801055920310803014207850341b0 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 991988974 1250 991987724 991987741
    0x305060f100e1b070204110913110a03020702190312091509120c2601060e0c04120f05010219030c030618020708040f0e04020316060f050c0a0b0a05 65
    0x108010003855007014500410004400c240e01015044000601c44610160079070b81400918000d209010394803500b414456110a52014000c02c102e040541d8840340050043c1c002206582d80e130802840000c01c200b181c01c0144d48268040c00b0900c0c8000c1007440300544888041703058070207d400541e030484021045185103a006441c01008021112490300c6001400d0405400036442c2c2c4076040c164400420000304110038695010042c1c050b18a86100f11646c090600000d0034124001c140300b586049404104642314044043c81003520800d110f02d058103103a428201846419011940d0308040344100c0300041e000c0c00074081260600740003590060003244014155600b419485050600d065400d002040d40102d48414080c41c81c00056038a51031403030081000d21842d404a20403078010040800ca20700c45810b02c5020718006c900b15550305803007840c4410341020030311401c00858040e40d0051511070103071014202d01e8070507809403a04016aa12803c05400c01121030408042c0d030303141080f4007070 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 991990224 1250 991988974 991989001
    0x8091e01151d1302030c1509030601033905060a120c0518060a080103110d02040204030501020c07050108010e0627040501090308100e0c250506071202120f07030f06030506 75
    0x2070f080354101d14100c00c2500800c0d1551a903a4406000d220310701c8188042c440c8806c02c45d994608060700b03d9102d907940e4148040c5845411a40d1600c86156442002140d881114900d00b402168141901481c1c604802c1086d0346d80f0003007181041c0708a00c410100000c2551040011034801070301d42c5030355481c0303a01e43d501d50070b6555001c480c0700c0c1c10180300b40b192040c0d00c00001030640e036000c44c540810a956400051311084e0301140203500c240002804405c000301034029044140d401c4c002c45501c2501d4100548030b042090040c2d40c02a0603a43c00162540b808800c222440e440f6010072032903540e04104d11540c0040b0403181036a85a440d10b400710105a07220314a2030340322400d0181483c44c60706200301400301c0300c0c002d0001c00340d15001080c442c5070b441444c607090120406820202503e0030700c900d006600c41a00b12035410218200100d81c812a031428002c499503401c007401c2401d01c0356143e000d81d40e5540805000303c4205a0382da0403410b00380c0100c0c41140e0296000d01e00800305e6240003580500031 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 991991474 1250 991990224 991990231
    0xf040509060405160305091e0a06050901020325050906040801091101030b0a0303080405030426010c020721060b040510090510080a030c240b01030b0108091e01151d 72
    0x22440c1038108038050845400044001804d440c000c07442c1e0312840c07130706450309503103608103500c00c070000d20740070301c5071000003001c000341031140300c0c240900c0e9a000300d014200e000483e4041440004100090302c00303c040a1203000010517410b01e5410824280302080c1d040e00580c1014076103079924600c4030305021030500c0c80031074642c091030180408e08541022800400d810311000f0b0922040c035020400f001024402e5030040d082005402000c4a07070b00d0710016444141e4841220b0f21b5103020a0b054085102080010507128200c6a0009118180c13009890710101c0078019134045945039010360440d0351318010349004403000c03032041d07a80710b042013001300440b44081c04078241c5184612042008c62804141054040d4042c04d200c85800c85070700305203500b04207906640d58803404170507031100b07400400d07403110902c1c1c4e60070380c1e04010620317081d8015594000192034084555001d050380d08550180c01c5802641d40d442c240010070b200c3c81d41001015007802d1038022884000714071002003400040643c1a550 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 991992724 1250 991991474 991991479
    0x615060f251b0b0f0c030415020303220c0b0903031b07050f120601030f0812040303330b1602041b1803200a0521010e120f0d0905030f04050906 63
    0x200140307040e01c011554811300550050030340d400b1856442c2c3d0340051050701c0081400700d0040c08100c4440703070025240d50007195030703030350f84802d500f5103061b585000640c120307465a00007440c84086061007200d140a4100308101d0b42e040c4401c04c60503c0c0302103841c54203504103030f070315000b000007a09007010042d0040020720000d00880f102d4210440c030036800501181184e03044103500c2d803c60401d0810410910810340000c480d46040030600c020151300d54880a50303100503c02d2000304113640c10076028203486508994a11042c24807040c03000c0c400c082c005112a020350070301500c401c00d46d079002c80c040d00c10710020b0360040c40f014a244841c803600542080031110300d0103204001a421541c4001c0844504440c0b159051307508004802075407031b43e007489800b4100080c00900710801d00c50f914140107281040328242da50a00c7c82d50305601400180d900540c5004180e11405c0c500003e04c00807072600281e05081c3c09503284c02111002ca402800146a205810500c80e590f5030700344428808441c8010345441d0 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 991993974 1250 991992724 991992773
    0x151908100b0c060a05150117040203070b1306080c031e090c2d01050c0a06270b09100501060c08030a0207060c080a0e2a120d02010e010b030615060f25 66
    0xb00300303a84c40391101c202242c81040c02802307602d903400424034040282d08540c080313910005042c4081c05a40499508461155484404660329010312001c14081502c6003006400e55080d03640160484114003a4024440e000719404009120002240c16600041c0302500c00d80d224500491000303059584401802c0a081080c50705042c44c20700da603500070b2581c1c041d180701d9651241000f0515507544000044120000029202c40b207800c19081114003070740c0070708040c0310300c5411158555140c00f03200c1c102c41d01900c41c080002c54075110011940d00050441c0c848503800c004c0c2d04e0004400e0b10800d00d0500341540e48540364646052900101c81d00c000000e010365111100b102a482c1c1412940c5250128082c498041d405001011894120b0100103081150150380b1504440660550241e0034000c00c907002400010100c600341510f90320b040d00c0744a0191707801048001079060400003041c0c0c5454555149203011400c980d003100342e8000d0942c803034440070340b2000c003000c1c0000c4044a6014074030301900c45 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 991995224 1250 991993974 991994011
    0x50711090708012304060b03161e120b1804030906021b040e0109060e0d090e0906160512040b1803031003021210020301030c0302151908100b0c060a05 66
    0x1901d003a070b0501c501401d90644080040500c0740e040362060381e83d0800f8100b446201e4032290560140e4004581c0c92113156980240707076645d54415007110718006036101c4040d01b080070040c0e003120031110003010901d00c1034907029000d035681c40b181c20020a01c11a00d00200d0107040a103030007889055103a00490465200c0075400c81c5043c10750184c00c1c850a012600007034542502182180542141d5001038283c6282c500201d030200f81c041400c14829000c0e035907010040d0f07102d00b15207014120540304078110703600c420002000c1070307034640c000881500141406c5040c842d01c03900e9400350080880b0b08644511200d018410202103000366090b4051031000a5403c40c0b914600400d4240301c0c502c4080d100b800007080f4504408010300001900005892041d9604c0d1784904241d200141144412030003800c0000781c04803e8007004042c1e412a03042c0e1f03000103c0f9440c000008450082010b070207041000d441c002c0c0061002c1d52f02c8020160030381c030365000c0e0016261030aa142c08540e4010403072541300c1c6034800c00 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 991996474 1250 991995224 991995227
    0x3201214430060d170c070603060b0a02071401032403120c21090b1206030d18060c0203161806081c05220b07110301060b0306040f090b070507110907 65
    0x11264003881c181d420700000c00c1d280c20865248244076032400c0213110001440b4144000205407103050b11303582d8505202c46660388142c56001d205100c03802c1c0051f04800818000d0214010319244039100516022401d081c180c116421400030091030420101c080c1c110810800080718000c2651007128148004100b2141d11912003400c018a07490040a61020f540d50a450080403c1c5020303043d00712545841e552015144540041c090b00c2c0d6512034400e2692041001e48103891980072a804103424015032441c21500b0b940c0010044000c0f64503008100922050950445045c0000c0048204000808550902e101304585c1c960700007660036009001c0c002094910345003103081c508094501a44c0c2c50703125006040300c140b10200120020b540740040024211540d40c00f51812030300400f0045004586a0201400c07226244a00b0b5000f580600010305286000d500c0086030360079103c0d010600a500c0c6e6141d821000003100d020300821030102d001018400243c90300f02d02e4620541d0031107141d0501540 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 991997724 1250 991996474 991996567
    0x3140115030b041b110c120c19030510091104090804061202040905070804030f05040e01230409081b06060d0632012144 53
    0x1500051640782c1400d0201621241e02104505441c0c4403444444010703003800a0a0441c1c400c84805140f1a40e50060700b00e141121040d881008820014540346a80100f80400c10700c20445000d120255188000b01080c401d00c503030002801c2a00c800500c0805a280088074012003400c0b1f03038016442c12000e40000341d030310f208a405881c003c3c2040c0350204c0f07000000801a200740d400540b5030358205001d00c0580d80c0c003c0c00d001c0c000c500c01d0301e41c6070383c51303082c010203d40c14000c82c400e01c02c1c8648114010004005240120051050402c0514080b0000c1d14041029646202c5084484160018104030500d030440034040300c1c212410007500040c10020006485025104009003d40d507031150308540f01c4020312a01c0101a11803180c030308034007009141c8107000040902c071304410721380c1c040e4a964076600315005c000403103035200440b40f02c44c9000848501e40d00d100075081301b03052005500c02e011500140903150b080002c9043c101035403103c48441c0701040c00c40c0b034030548024040c1807410342040100d521 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 991998974 1250 991997724 991997759
    0xc09090e0705210304030c05010e09220c0b0a110708010911090c070f080703080a09050a0f050c041d011104030309150302120421050f1c06170d031401 66
    0x261a142c900c2c44000b2921603001030b0f00d140861621000800000300b2041c54020800c603242601c4448821000b001071009007076040314003040e14826013640e12885142000c0e03140c16140030300001c907444c030307241c621584840d4009408100403420071500f00000f81001c00004001d405100700902091031213540b90b03a404000031004611444d82d2000083c0c01000440c107640c0940c0c4c0110512110707001d542170a0003107600c00a01500051400c60000e82c100c58140140342085501c080148184c0116455090341149030036011107050088502c5003030f441d503c40c0503041c100d20401d22044500040c04041908603045000341e0a1110380074041000803070b812010340300882d451280c0301090014000b808030001d115241c0c0448183c180d01003448140400f080301c10748980c890b0800d01d000780e0404001910f050084d2009100000e4042090403030000c18200016600c101484010890035100e6002042405940420050301d6010400d181c1102e689801103d0351000348115151442d41402e220074500e05518 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 992000224 1250 991998974 991998979
    0x30c07060309110306010b0d05150603010315060e0c091e1f0507200f09150f0109080a0605190c020309010e0f0405040503040611010b0a050907020a0b09010c09090e0705 74
    0x400c801801e0003441012020f40c8800182921019078690b61940310315001031a03c243d40500c1c0000040c01c00c0700445820454680080c84075041d40c0c6035594032a060510702c0903d480054031075030000b840241d203510880c040ca01c43da075266100d80800e014030280a0301902e450701010008454180e41b80c4035480e80759843c1d540c0000032400320624580c199068443c42e80018100c06042001d880c19520500107030810090845041500303038801e800700070250740251080c030410070744110b000c0070900e04150008440c030f0042c104020925a50b03001a0700305100442c081d905d09407100c042000b402c000320005040421000020484607000c071500070f42e640203035501d0724180607070b03070002c0140c5940f00c0c40381c003440c1400104103005e10701c2e0500d442078903900140f040c140410507c1c8900b0103021018001c1d41c4d508040503100d895481d14100401a140b88058520b10035401424000b07008260a1042684500300f070400204129003043c0f8001c14807912607103d402e0481c98884401c01c002070100c0d0190495404 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 992001474 1250 992000224 992000231
    0x20912011401140a08030a0306030c17120d092009010e130605070306051f0e030102041d040c0b070303051b0304030f08070216121a0118021c0c02010905070602030c070603 75
    0x43c1d1011139500c6405810800d4280700204e41810f603180d254120380d0030b072445040d180c405150768009040b41050015003c0700c0c990070540869281625003c05889e9584042c0744c041442d1055071075840f040b052510140702d0b0302490440b4803040d8180405030394014550740716008040d241c440c0c0f0152004178122002030104e5118808211100e02c02c0d04000044d100041c00e520358000003e80032000000c0e54581c98005c25201c6140c66040d02d411310030355003102d0740c4441b640031030a02000e114520480084c400c4036841c20700c40011420340c603044045d01400d4843e031000034007030a01d01601021a1180070b058104610100b04020019078081020203902c0403900341240f590312800310590038511210b010f12240119804000360f00c244004402507194000c0d51600b1141e0841300803503082250134000d01b41150311440c1d00c40345403512070340101001c8100c00400040308901c4449a002d407400e01a0000041c2e460380405030070b122083c080072005010340d000a43c07400c03000c0f010300c03515a001445040e052554 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 992002724 1250 992001474 992001509
    0x1060813140303061306120219030813030507050a06050a050a0c02090c040f090c0509152205042a030902030c030106061709030909040b070c15020912011401 69
    0x340d2450880c80319888081d51090703900818496a03603400441d02d1034400c1c04c1840100f9401a21841114241c511510b0005002107554082c070107002c2c602c0407105050854001c00102045c0290041c00e03001c0c0e204024883c5882c0b03182022490309049802252061540305010042140c00c1002c80745200c80c2824038580f01c4401420030749908011a5000c0c0d0454108003c114801c1000d600030710503102d4030f12645d843d843d00c6440710b404440d0100b8448010031001c200f03a8844e031400001c0852009808900c0d94a08141081c032031454195060406820911162091240b498107002c4c40701001d07101c03001c80c90031180c001c0300042050104041801803540d034a0303c0394150b450601041c00403050140080c02000d0340c40000a009400c12140c16103d520b40c040400c5141d2004411107150510040007400705448903200c4e520301c00c401624100c1800404059580064035402110a1003940140c0058982c3c040c0340900551483c42181041184d01d45080c5e0040c2d034407640261815100049091980c010 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 992003974 1250 992002724 992002741
    0x8070305090a051e0f0715050c0f070602151e0c0f25050706020f0709050c04032f1815010c0209090a17030702060f040305040510022112010608 63
    0x1100101a080d4025210810341c1d540e000d4041441c2199001c4c00c0b1915008501105500c40300341d401642550f4006c004d0808816110b8009003149050400c10b4030841d601c00300081c0d2074100198804005038100007048004540b1181c0555400801c003c0340c4d10840b124180200079603280200300400281d40807507014400c100f04803c1da41e9408038112106c1107201d90b900e030f1188000f10000c044440d03103d2020003180980c804545258510400070091980078103240f400d8000c2c140c02495100d07c414140800400301d41d41d11a0070642402008a44a5440300082d121345401220f40c004d030300030408200c44110002c100e10041d0707481a0440c6484002000c21001214441c40000f0060350211034901800304018000c2416440d0920400500d511003013840710b00d08680c0022102a0056003100000426844e480751084e54818841d1401501e030a0303d4030300060711068000000c000592081440c00b0b405e05080301d225020f044900529030a00d412803c0031542403405005401c10490310b0004160900c = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 992005224 1250 992003974 992003983
    0x319091403070c05031e12460318080d090803180105150603071b02060315031b060405060a0e130515090405190305210709150807030509 60
    0x800084040d6580c0744110308200c3c003103500a002d0b0610074040ca203da040201c030014103041742011442c3c013800c7d00130182e2490300c07102c0d0030090600b80d003106150443d80503851852080e00840300341410b100785074800c03802c040268014002d08a000c3c140340c00e840203510161003400305001980400c1c56580d40005450140145c01c00d0030000b008004080184030006200c241c04144481c0020020861a03440048400080d01100c0d20341e40c0002c010408900d041d8420010038106180c0030ba91001d12072001d60101e001640110303446848007007a000318407000d10b001d010031100017015101104c020820140041d03941e115a00c0380d10b115880c00104170b00e00c54040e218030350010000034046084107085000e82c0000d001c0440740c48a00300314503c0700324441d01d070000c2517601403a000740003050305080045510485849100b411b40c144a403c0c050381c165490101c0d02c0c81c1907180c01c40c440c40158103142d4009402096149c018108841c1f080c81c80782940d540c0004550342c01503080c940483d56443e18901d40342007 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 992006474 1250 992005224 992005253
    0x130302010216110306070302071109180a050c03070b040308042105070305010606030c08040c0501051804150f0b03152b060b01090f0b04030813080f071a031909 70
    0x140070b01401d9510074801c9242c01c076825880d090b0162212070351910300c00c400300e12500700020b10711414000e0003d06130400c19500c0768051184c0c049240c0c443d500d54401e030715086070542c048035940e208160302200b904080c41090010310742100624206400e42e070f11106a4017550142102420400b042c00c1c0d035109461441d40c2c42c0a03003220507200000e4582c20154060b10b00d40c0140c8010904042d5400d24183c4180403080c13103107400441040d10305040100444d626440800b0048203000f000c032942c14950750381c2c4502c0c01d0a440c004041080a071819084009581c6c0070b41c40f0821000044c030070400120003003000d04404e80700c01c0342d0024540040c011034000c60103160041c00340075286520141c08202050303011041102c02621111401c035a104a42117954800d802610100141171008000154107071000c1e2440780f0020ba01d03590101e44030b00741240740440d080107003081030f170105e641004142004901c0c120000f456541c0a07185203072203107069100c840030740c01c54803c0ca5074945900301400f00790a1360681 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 992007724 1250 992006474 992006497
    0x1a16020d030309050c09040812102312060903030103060e030d0615031512030c0602120c1806070b0f0a090c060c020a050d0c061b080f03150103060b031303020102 71
    0x38030303106414001d00038610301c802156a80b2804101c4801480e01050750703413059600c80340c1d684c0b421002000d80320b50350201231326910328100340700070200700c0d044c2102050705030b2020200a003e100d901001048243c08844001060035000001071001c668404401c0b81e06482d0055004200c3c5980c004400745588034001240c9566483c14001107402c15005200c024806210781e001d00140f07a010b5811603105119205000c1e8000d1003200040010b4011912002241d015401c010304004001440c5440c004048810920502002542021000c040900341c0108001912110700f09512550f40320030340301002d00b14895602241001448400c1980c200101481d8050b81c0c04c10340c03541d18003014190a2100004900c1511540404102c13801c10428040c91140c00c803142c00b54080c50150182e0303103020008500210200c0740700d01c42c00030449590091043c040b208103003668070b24041c0c40b403540d803c404558107130406061800030001500c036079040d2904410300902292880c4001c3c03805030300910604403c1e44 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 992008974 1250 992007724 992007739
    0x406052b0c050a0e0a08072303100b01140319020c0f0706030b1206091914030403050a0c05061305010f2c0907020d050d09060f1d070f1a1602 62
    0x2044154007001810603964144c868441088a803000c2042c2071115000384070060340448070070048500484041c1007000034064116a00050180c04079080c00c00b040081d549194072050325140c0c0b964820b81c05150095a200500d045040400348801c01201c0001036205654000c50680342c890411311070303005600891021104140d54400000d401b9003111315a0f10306c02d0800380c58542d003020000c6101072040d204c03103014101560120b4400002400b100c0020740360b54008084001040300d0410080c0701a60103a0028005245103107003151071001540c0100c1c2c0103c2051010101c04440700c1910003d58800342070240c100b0100340012280340d9070307101070042201e4041014084040c007102100c4008a400e64140c0441c0e560f005090365642410102c081c00903000b000324040014480d405100307400d200314000301e03c0005009200d41503e03404200111000704031a4940403400c0704011100041121482c2c1c00711040c03900c030040c11040c20b0f50140031080040000e14030500a03200d1071104900e41e006041c00c = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 992010224 1250 992008974 992008991
    0xb040905150112050304030b071b0b0906100b0a0806011101110304050613330c020c040f0b03070603090f0614040308060f1f12061d010b0406052b 64
    0x540d8400201d200000d01010300d00011821401d8003c1140c031690f0814021480c3c10300c0c1d582c030f00725001d10040a54080007401e252101034509445000590710303000b07a010282d80d051107600c46051070800741c04d150b0542c03180b040030030440103078009640d011004ca0901c420305565140058800c800d041a07070341c08075441c00b05044041441e80001e10301982c0900110b4015035600342c0015a80e84038100701920103041c0e2901000300b458400c41005001103001d01044180034945010b10958480c6103d0001603000740340c4010080c02c1c03030300c105030034080080001e1104071244e401003070300c80c22207018001c10181c41d4008001404800320f9100039883d840842002154040c03002c03d03410700000d40d000c9000400500c01720f0341c680340256210078540301c02001d0058082e14448200b142024140003003041c4400c05100803c40c40d00b0740302d60303002010b800c0c01410b840040c1140d0100c50580507084001c4042040c0802e01c2580c1d440001d566a02001c0d46c1c03c4c100d12003640c01d00704500340003092103184550428403607 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 992011474 1250 992010224 992010233
    0x305061306150e0a050f0607080d05180f1b040903031104080c12010207081218060106091a04080613020a03171c0c0210020a1701080106080606010c1101120b0409 71
    0x103010407051658400c088043c0300420011803400c18400c1c103500c0b030742a00e9902c0c00781c904100108039551094103514038010041d640d160a846044903001c0da08144500c1a450a0030b0034425035000040d21009400c0c0c030b14405030140040c030508041b46001d20360355841e52080500a501c5003c02c201c0e022074883c0c84907079400403241c0e100d003843c04040c01f881110341000300403401402501d48050f030059889007403402808094031f07003002c001c1a40610449500c2c404034410750504c0040d01074000d5613a0401081e06080b002052004210400c444440c410801001840700105480b40c00c0200c45401080002180c00008c800040642015103c45034030714064500e604001c5c01000e101800d40c66801581c2c004807103100c1183c0c205201c43c005a000074444101110340c43e402040d02c404035007810150741005030320303c0540304001d807c40307034641e907441c038090190a0007003240e180e002c1e03001d03e010100e40301d180d80c1c0c100f04114a002800c1c10b10501e644802c030400080c0c0c010001580000c0d00820081005080 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 992012724 1250 992011474 992011499
    0x5061617190b0625111822020f0d02041b030b030c011412101211120c1c08250308090d0525050a03080708060108010f060305061306 58
    0x4035040391441d06a00c4541400d10324252100520650340c00700d01348581e02c00549024142d403800f1203180443c2c100c1401c103641d4109132908180d042c02e9056920346071240039a50750004003039441440300c07180c40f540001659080401011800c043d103241c01060013a1000ca0060600c0506010040350701c0c500d5000500d5140c1d00c080c450a6040701110300b000006401035401a620a20740e00b03602c035007044600420111155010742010703201012032031042d5520b0f000c03414120090012540f48100f11146003007072800e80c000c1e0381d414020102502c14038508800045414012051a81e2020352140e0301b60148130b000800c1e6071030600c030094800d0403c46181d81c0c007940303c2102c4408801140e4105c01040c0f81d9400001c0000c0b600b01903494503031601010003008040420801c03503c200f0705100140d40c4000442c00d001c4605024826242d4020078140814064a035201c02031103181004480d500400c602e8007988504e4044444504000940f031f2140c00201c1e071038200c0c5850900540d800c20388002441c0d180c42c2c8 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 992013974 1250 992012724 992012761
    0x60c030f1b060703051005041802101d060306010c0f0c050405070f180506031f03170c070b0a0206040209180624012f03210f010602030705061617 64
    0x82920b40c1030342c80344010340c103c0d030099850f06d2101c40c0e144401e0045003405d0303100c140310442e4803030312003081c0000368000740310800060f10110008811500a000040320071200c1090480115170710f03815880d020000074030400403078030301918203140c2071608003d011610380e40f040904400790040c406454980d030040c042d404010100340002d280d901c29000c4003c1001410f00139070304018103c0780307140c450301e6000c1c40509141c00c2c3d01e95001420360b40000003505148001c0c0c4100740c3d554a49071103903c0c0303401c11410b20000741d2124441d118204401850309a010501031360103641114885455114001190303902402401100000d12446043c0710300f403002e01c0354450051150074215a82841c80b04e004443e00d0841d042d0000400e40904140b0700035940100100d62994000c1c8100e034200001225805881d81d0000300b1505100d008100b031100310150fa5681901610030342c0019407030f084042e074a003991410002c20102600314a00140c6030f07540d10604143e87c80d8011011410110300709000060640c0b032070303903 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 992015224 1250 992013974 992014027
    0x50f0c070906051c020d110303130f030c08070e01060c0609050d020a05072309090c061305011b030813241a100c1103010209061803010b01140702060c030f 68
    0x10300070a02c0c00003891041136405030340917005103910f101603a40c0c0481c10030146405649400203008070240300300803d48104c0200b00046160140c42d1841c14001c0190205420000e41c54000c064140041ca02060707043d811983c05242c00020300306c0c6410030704014150a1401801030045000d0300000340d5000404010ba240664141c907030855803548005a80d901841f4500818090424501103a1500e0b141c6960710012110954480d2a4542d0000354183d02c0601440000703001c4100900035035a100c0110703010302d1000040b1755001201c1d81c4000d404407100a00f0040c000c150785040004100c0c0c0701400c2180c0030700e00000b8010920581000d0405040720406401e20554404801c519520741081e100602c044143c0360492480c00b1a12106076036640d0304c545c41e800d99001c00c10a101922038500404410509010070442c0d4820301c010142520814140a410031405061001401ea102c20482e200d4a41c1203d01558032800d01034076034154060400a80c07940b0401007502c80c064070540c80100021101c5 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 992016474 1250 992015224 992015239
    0x30b07080708060a080a110406050a030c090c032a0c0602030711120703050a0f020a1e1b05030d030c02070e04050d091e060804110d03110724050f0c07090605 69
    0x704010300507941300314410f4002c150312064200000c20501c003607134440350078047c0c00030440a031103c004c103254000c07580c0f01311000c0e82000c0081000240b24030520f8511201480c090080e0f8002100d000e0080400e0030405200780b25000e415401c982c095626080d45540c1b112080d0b480e03280c50403001c0c204182c00540c2140501414a4080b11a59401d045550f1264152a107506000c89044225080b1f10120412400c0d0310440160310080354410b0b0040745d05c0082944901c031850441d10b46010084103d103210a401c0001310030502540e503002c1002e240e00a410f03e0b00017280f80d0200c500f00e04c1c0464980c08410590302003414041440030100b440560b054154540103107450340c90b0108034406124440c81c5006602c00750702480581c1c4a966001d030801e0041c5604803071585504002001c00740401c0c001c8010819998003d40500c0c0c040c02050001c01900318503a000300741100150030000480c00003002040b000080300200404000151000081468200c030401c1d0b49034206a001090b1500501d8440d500d03 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 992017724 1250 992016474 992016481
    0x3142104150207290d02070501091a1029070c080c091e060a2c130804030b09071a0307030f0522020112090f1101080405070618030b07080708 62
    0x550328084804100d50441100321071020551352038086400d441d200c40c800c002c040c48000070b5001a10402d8000c20001403074507214038001070550031100f00c002440340740c4c03002c1000d5868000280c4045404842d400d0300080000c02041c1c00d0292001d51844220102113008020311100040324000d90343d0441c101c45101080350200031140c9021283c14201c00d090340c8949051200d400075550f00224050013801145403200c0c01d2024860880c0c8001c0d250070702c0088800701d074130f81038268142c02401200d1b1909505009403a01d01d83d5101d41e000c0541020700c5003022500d10302e03081005400820840f24508812005661140802d9105540c00e00c0007034103020403c2a0841e003803007094021480030003e00e4819549004504e00c1c10001c40d01a03041c0540800c4d04002c2c00743d503004050000d4800c695111140c7d02900e0301d250381d840b282213100d041040180401000840024842094074003030f081c00d410042c61020751801081032600001d01d0055044188040c007034101c402a400360855440d01c000320394 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 992018974 1250 992017724 992017727
    0xf01090b0a06050c011103040f0b0105040b0d30090807273c050a09032c04060f090b040903020318120706080601140c06010314210415 59
    0xc00303501106500005140040001d00e0058005140c11507912002055541483c2c0c403031102034004940a030f400348110041a810071440d2142580500030480d01000350001400105446610101c0c004003800a4400d08107a060359250518010b0030f4a00104400718100107002411201e580c4a22081e51260350804212a00c0d040c000740301041c80701102c510341c000c1e0f460341400079000d0010103021402090507480c2040c00e69442c0002080c0c00c003c02c4442c01d4051003180c00440d02c2c01410303003600c14906450440000d038408480e501c1c05c0d030b44504981060142070b40d0a980296018901903105103004e40c0094480034000c5000d084903201c03001000510720000502043e95202c110090050300704001c0c900b05a8135280c0b407a03140407406007842d0656114400e89030301d410160381013680414000e80810166603849501e1f09821441103c00c1070504021441c0c840c0e8901060000400504c0382c1c250f0300c0110a42000b10010080c0d002d42401011800754442c032005501600540740658014409083e000303 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 992020224 1250 992018974 992018981
    0x6080f1504030e01140c06010314240c03041515030204050c121b07150203041704031e1509060b0a05040e060105040f11070c06090512031801020c12060f0109 69
    0x7290952030700e83d6003040e51401110b07441c00c00941c4654040c0180b18040c0c5071142041068080c5100351007042000c0d440c0b816452901100c2800140710343c4150b8001a03001903003034181034004452110a507203d4645107002e41078805000c042d606a1450007000f251840e50310000141128020b80d001c02aa4407100004d0713800f881034280103141d00382110302181d609003102c1e950f50000381645020310704182c1503643d00035505815103280d100403a004024001403204030040121003592141c0c10500d494a10740e5800740d00b42040009403021540c031701504061007090040c1a03000d0381030a108201c56152440c04400900d107044145004007181c2c50081601e0525100c0c2d15141c0b5070440041c800c0303070300e48800c000c0500303c03030401507a007a0344600700e48901220710380c0940805445115161140ca05040c0001c2c0700210b680e1010740b20382440b07001808008808011076100c60241c4040f030001c20410030050b8034183e468203019803c00c0c2d118104004800c000316036a4010402003c0e20012a60303650026001d8 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 992021474 1250 992020224 992020231
    0x30219050915040b060f03190204061d06040b0c0a050f0f2a1503010e10030b0c0d140c0d1107170a21020d0e060108030f130906080f15 59
    0x41c403518003203510107407402c8089102841c0144003180c2200440c010800b1900664004100b0800c040203104c21032035000032681501182003011400e151038008020140108960501e111034016814200151641012107020f040088040c40d928404050101d64071044a80103854901888010001e002e0020807120388174a0450020803e80800384009030502085c403803205500b0411040c1c08186403210008003140c800452a516182d600d8402440e03029080100341c00c0c0d184c24000c60910000703240140030b41c0c1008200ca1156200c1c0c002e980044002c000501c42510080f20341000c010004001038000e05c0c0340440c070481801900d0682c025140b0902980c500280709401c8640d003030342c101c81d045000d441d03081400c1c54841c1411044000c0c03400913003060407140f0000d94001800854120503400741100c4801504010b089640c0342500c0280c9034060f0010a00c01010002035401480c0001e1001070007401d81d1034010800c0310b694403011540d80400400300011801039040c03016030600c039a40024070 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 992022724 1250 992021474 992021479
    0xc0d141009022109010e151b37030b150403260301030b01032112020906070c08010605041b1704021f08180708031602030f150103021905 60
    0x4107410900444040d40202041c0e2806145032105954040201c00503035001e104140e0000903640c4100359a20f0412032130321282c1c03e681c4840014000c40e21398a542c10b07906052000542e41e218120303292001d40314100c405400c002402484c200103004a041a1004180c11458904000a482d03200621281200d200008025894207100800200b8030444d071b8480c0d080c1041c100755800b1a802030304030105400c207802c15119600000018807c019100301c1412020f60a0b00191600410450000300240b00003015044c2c0d036a000300b00d4056a0712190152106140d000c2d2590503010b07100e0101074000c062606c9480d2056080c2a00d00503a044894680540c5000710707660010007030388512840c641c055000d001260080342000c00020307203140d1550810380700701c059640d03071007a800c00110f9032030400211150254140c10522082100d04000000c8541c00c0d124455403141c1d00c111400002e08044010100d44820700481c0c410b04000f4201d2400181030b2407084410207004102c0030000074852405014058 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 992023974 1250 992022724 992022751
    0x702071404051b0705070303030b1e190911030f06010302092b0605010b030403080609071d040e03041203090617060f03010b060a0c030e09041703041a0c0d14 69
    0xc460510b80c02c01c0e54800070200003081c0c540e124250540a9600c5010142c03140e4006070400d00c10141d0501908400c54812030b4034030f4419412044a584409071440345611600072000707103503000803200d48600020030a2480400589000075448141d0f070f882141d9010924140d04001350700c542c040d100355a0b0b0707003201400791580c1c01001c0070b1030661104886042c030b42e040100c24403180010040c0c0107140c0078243d0b0380b95258980c10709190141c280e4601900242c0300f078460304200014141d1210900c04d0655107001c04030b92840300080850000c065000d0b102c07500d4000007401142d503807d035100b0840358034825a0b44032400d0307a81e82c0040b01c00101c0d020507040d41040c0840132030f500d458800046905030b0b2004000140d204903500000c0c645901101c9982c1c0455244020070b028940c208010740071a280c2a030b4030001901d402c0d0303103a04c20408104842145802c0c040042014040c2400d205544090201200c85041c05d20b0203d9500f41c1c0c20009034011641d0521a407012002541010b1502540e0b1000002 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 992025224 1250 992023974 992024009
    0x29030c0a03082506090c030204050a0b24070818010f0201021218010e010f06060909090c0603110c0d12051503070302060d0b04020403060203100b030403080606070c08060a14070207 79
    0xc0f40e1807040d510155010862480c50600460b190307200c2d9814580c8280f0b4200e6689141d80305000944400a041803030103071500100f00002d03290409191100340800d2220308000981c2601000540546580580359420216480452003210b260040301c80800742c0310208010100c4c40200c2c00d034464010030307004080c128408070321003941100766000d4907070599002003565600c2c07106050850b900403403c510b020307803254001c120803078000008401820340d055085c81052000e40b600c00c601d00051143c0c00c20175641e1443c02c8260794403841078404d0030090100f41c1d084010000002491002164001001e161405012900c1200c1c01d003500f000c050000342c060030310245141c0800c0710f10703004200c0f800d400e15107444c0c070108156200d20081001e507110703000c01600c0303080100b418109038203a0740000c00c00301c0e810402d00020a4001c0c10302ca5106a01310b602d580d0354440e6103031008031403c0d143d1150001e403040000340050b00708603401005400e14910709031451552404c0003243d549038144583d071340c400c11010740b0 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 992026474 1250 992025224 992025247
    0x80a05030901031503060e011a2b030507050703050f100203070c140f0d030501081501290405060c1005150a090e030c0f160b0a050f07020429030c0a0308 67
    0x1204c0c0008214a4418034581e80d450311010344040031364140b0540d40d25400c0d806a20100900034041c54020350307101e543d0f4160700201e02080e110240d513100290702c1854039070082511581c212600558001d06407081182d076403404680c0c50300c0c0c80d109205075004000302e40c120380610b03100f03070b0344281c920340d482608881654480a0f04501c02950000d000d000314840c00b000d5407010040710140711544e0b60005620741c985a000e41c00c00c1c85100b058a014a0715100400031040d0f11080c40008102614244103105046a2072400500c2240d00070380d00170314041400c22148a001c1201448034062a07014000b075520b600c44c0055039400700c418280d00c1101c01c3e1040c41720021591240011003402d408580c078280211910310b1901ca61515111855803000e2000c060012058040328010092a007926007408040d0300080c0150240c0302045040c010003007000005d658598128020941d42c1008000c12282d0f0b14020103403064031404114000d01c158482c441043c00c2030340d04101241e41029246041c032044445 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 992027724 1250 992026474 992026481
    0x702060a0e011701060e030c0436020a0b090112090210200f070f0f0b0901030b010e1816021908070c0b040f06030605010c020a140d060f09020901080a0503090103 71
    0x1161030401c090304503e501204810590b103406070400d51516500707807050300c081515005105401d24052800c08820041d2122401100c52840d9494a50540000f14211000c01203c80003400a9031000b80c0c0040016424402c40c010b20170350200ba40c0e1301e13040b450000e0141081c0c40042030025081020700d18000425071040329082e65070078070800d041001d50580c1003064030b00301036003c0a01254120710410060b0085140c3e0040c0142081c28903840c50910b404035119850040700311040c180f544420346a940b0341c0c0315012030310104400905030b0003c00741807400c4080b101d2040312500d6a003101082c60031800340c00055010368040c46c011160790303d20074a945004894104410855017107240000100780c028190001e00003a100400e000074000380303007100017015644aa403280303040c0900031a00c3c07009604e500e00b104041e84c0082070783c00d00483c01c40001c40c1c011b603c0000b026103654034042c65045074114981050034054000c80d6941620390b294001151600309a07a402403050340100b0244003507501070380 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 992028974 1250 992027724 992027747
    0x110a0209010b0d0e0f010b010809060f042907090510093c030f060605040c05030402010f050c030a0201021b0111030f1009050901230702100515060c060f0109020702060a 74
    0x10003003120498404c04524100b0308807028041139440d83c42c03024040d64000c04160740501040010503a908103810314800e2081c014102070140c0c010611001005a0381807004001d80032141540d1005203081d0307100400c854801d014040c4181145d0920302e4416100c2c01c01d41094031500e120075000003500c0580143e50404000d80c22801034041c00c5081c480e1403c240707072100294020280040040e03003500d844411501c554111510a0740f43c9061411020380c04026282d02540c2800c0a6092145841c400da800307000388006201e00740b100140c3d000e1850713419006008030046814007070200440d941c9000303003a207554a41e80d020b800313002d1000501c02d40b0402812034004550180720302581d6140e510503402d0382c030101c40d1070655030f455130211300b03d0300d190300483e400790a5012341c45031460070211002503d51401d20703c09451603840f10049418940115180d10304690000e00c0541e4401c508450030740c40d807004450405d052800b1100001d045232160084807905a03005108603e0604144015183c0520302c1 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 992030224 1250 992028974 992028997
    0xd0c061e0f321218010204031a130b161805032d0d17060328020a05090a050423030403030525060501090605060c0c01030b13060b0901110a0209010b 65
    0x3080e81049040b0100208011036281200b41d40303034544802900010b598030542c0c211035078410030080011607c420004104614039254882141d181c0e5030100d143e01c02101e4024280e0200ba1080c0903a200080c00c4003902d161044d120300c03c5001000d406103030401144d02c14107416800c80840c43d070301c100305000014010a07034002901d151320255500e8500d080c2d011300c4c0360130200e48042c6656809241700200a80d12190440051246100f161200b0448035482c0143c410700400402203d001c550b41c0c1c00d008000751001900b880300318135200900d80702400c400e50f415610009180b51400d60105003039449510a0342c42e000940c80c0604d541d43c1182d29510405901c0501504002c41c84070000c1038110744181d2234022a40400c1650408401c00d04a03a04c1e079101d244554420411407a1070440404c000200c80c0003402e00007482c048070808500400c3c0c03d802c000206c40c3c0340050101c5d1381e81046001d410740030001c0e80c40e41000c3d9039601c0e003d5603541c4425000396000a00100400410040790300620559062 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 992031474 1250 992030224 992030297
    0x3130f050a0b07030b0a081c0509030c03030c16052e0e04020a09090e0a0b06090417070309060806120303040b0c0d0e060a0b0d0807060207020d0c061e0f 67
    0xc1d0b00c1e441c0345070100b5180040080d480d05060291842e180342001e01600c01c80d4054459807880c1e002100b80440780f003503403005108000c10704020564043c044500308810141c00d8a98411440401c1c6c1d407540049e405014550700710030008902401c003d285003920300441060701100c03803103015103480c000000200c250100641e801c403d45058841e4001380c041c940c055103450006070308000c0210203907064456980e50303690061340d16001007411482e07c260010415030395084940c40c0c80c11b21441132101c50788809130800b800a650800c243d03003c801d070303c216942d50781c0d03aa80a458580806c903a44841824101180d801800468040307201d1081c01504a580101030900e0002d1101c418802d07138407206109511508480100700030000c540c0030702118441c0490742081001c40d16030f98000c190144007005000507501180260864499401455506400000c103200d82941d400000307120000300d554980300c2010f800c0800b00058003e00c15a804c00703c2540f00c0c211000404804084903005407079160040512 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 992032724 1250 992031474 992031493
    0x1508040b061306120203060108061012050f16030605010e010b37051803123408030a0c030c1e120203040c050306160207060e040e120d1103130f05 64
    0xb2188240c000810515401c0c120b4040103004040c00c022050f4010718498202c1001c110650940581210513682c20900d08030f00d024a500340980303044180341480b061403140382c1044512580000481e03040340d21540d014030a0343e0300c400711030001500a109207240120280a0074070442c112007001c900600540790514891a1001748446048080c00d140b40080b41c400103149a0000e9000304414a500040d4024498040c401118085520030107034001c1c41a02c441000200c00c880c5800f01c8100b104607040051440c4100d41010000c41c0c0c0199a0402d0035440e1010016180d0700a002e0491400c0680c0c5501e91442d100440d41c02030390b0841c007003103410050208010815400588080e5000710302860070451120b0811060501c6c01c2c0f400b0300304020400c0d01303011013480036a000079101c042d00c0f924580304003912100c40200d800f03010341040500042c0a6101d10340c42c0121080d01401c0c15010b41c103014009a9850140c1344803a120540b0000b00000c1600e840fa40030031640803030881c000380700c0e1088038280c19 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 992033974 1250 992032724 992032759
    0x30906012927041d0d0804081615022a060f06060901120906020c0f03030903180f100e01020106050409020607080c030c031b1002030106050d0e070b070c0f1508040b06 73
    0x1100340350b5014090240c03030140a41081c04100c1d5041c5c0c94880d040403001400c050b240c0e0a4240100c2203003200c03210280c01c41c10100b02005007103684030079030703400c0a640310f02805200024204103100000320003808440c0d000c805103400103165014a4104a10b228203072070f04000e00520341d02c46010742c1e0604c008a074480711448001d00c81d4210841c0103640041c0c4911801601c2030900c0180348240120313500500500c100050301008441401c11001c038292000403101010603a969600c0310f09962201c1b01513031121000c0d802452031400c10009a0082140c640c540081104440f0070000c0690880e038144a40d00002d222400102400110340044070f0504086070140c610399440000885030f81005412403116056003004045620034859409604540c1884c1009160b0b0052040c1505c6440d101e03101181108820b201400140080b00b03040d6680c1d0303010b170502c4480d80d101440342c451282e000c2c036000105410100c1c13804d81c0079406656020700d1a202e6880388480070300090710325a40a980c10104044c00c2d03 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 992035224 1250 992033974 992033981
    0x406110408031c06053a020a08010519050702030906070c050a0320010215040b040f050105010b04050a05120606060f12010f09180506062403090601292704 68
    0xa501803461900da04401c505a401a00c1080c1e01241c0544440410030003c91585914150325146e80116503469003c11080101680c0d240c65010750000031114000c05c0c03500040d004030344686d4120b90003541d030144c803141910481c0c4088402c000182c005002e1010a4580039004111f518020103e0380301d619251000510525180d903c2150388045052000c2020044110406040d100074009491500040075a120f080f0380e000b40014490103100001400300025809100905070f0884000c000968598514a401780c1c40f03401007034811151840300146078503109180b95224049040941020b8554000740560390b00990841c1003120804d100c051500402903203054020300e030300380560b210246011900001ca40c4600e0300c5180f8080200c2211004c10744c00038070303107401c500305417940c02e0303c403104a00740c4910481d06000e406c0035a0000090001800b0300181e06c130f05076004035085e1656481d89500540d2142c600c0581d00e46507040c14801c405441e0002d40840c2c2c405100110302403031800040001070105c = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 992036474 1250 992035224 992035237
    0x11508250e16110703020141030a06050f06040e10080a15060608092d0601140306060102030c0c011209020405070c030908120322120206061008010e040611040803 71
    0xc1c0500382d2441070b21564002ca2403109400300d84064400d5909580000b0700b00490700044100781a4035403820010b208d01848900940e81112448120300c00e405040c009550380283c0b5154101801c00e40701040134945070524160801c0000c218514142c58200c0e00308100328000c19940104202800000b118181403001700b18051081d612100210f010000c0141210a01c0d00020304001682082010003c00051041e0000307020a4000381040c003052400400e4016010490f002400f818000052010049582c0100d8081c1182904c14958400c0300490340d0f801045000915544405400c580079402441006e00c41c0180920110701c0c0056a0040303001e680088d02d448000803005103250f002c0c5035205100801925908000d0300034103054540810141c000070b07294645484819903c5032848054908642125500120450101081a40c0030b91624011501c19005440108158024900c60300390070303040e18082900180c85480d40c5e03c07608020f20a00111211800d0f00b0031002c00e045004101402c00c = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 992037724 1250 992036474 992036491
    0x2070506041509060f020c01030902041116060c0e03100e10330f1802040f080f151308030901060b04080c01140c0a08070606030c030303050702011508250e 68
    0x2c1c420040c40061040d03880c2d5206004104807242c04c0d45045a000c01d204441070350134600452410802d000050003040704c1c030540f0f5207012000903c0389040d1100e24040104030b0084904000e101c1c48803905984450310058040d506801556180000e00e026500c01518084400100c2d449168030305142d0085554824419941507400c09800e014070518681c0c4002403504d600000400350329105022820100038041d4840000038180c0b0100c0198680d4140d40040110212010700659103880c0a91604a038400c080060f000389107440b0502c203445589907000c2c00c00c071220102c1001160b00c4a140383e41015040342c00342e540b1844009142d852410140c00a0441d650203409a0b02d1520000741005104001d2005001828040c10145c1203000c55500c682d80d07042001d855503510f503803400c00300400040d040104031385000132011083c550b00d0380c400c600c110b00e40d030000c100ea4100d1b008410301440b840e1141104540c407034100d4400c110349441c03111040345c500000d600d02554807410046207039030044840c5230 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 992038974 1250 992037724 992037749
    0x17090a050d082a042603040308030105031504150504060b0316170714011b0804080102071505090c0616020a0e0a1103150613080118020405061219030207050604 70
    0xa0011141410b040d03d60104414290211501c41e9240c07425014a01c100e100015108000040712101018040380c0c0c1040d00301525a1a0b45901d0150340e84d810a016150081c4510050382c030030000107160440c0115007024040c107107500c0034403016018050007001200c540740c0354840000d551702c080189101d042686024043d6075030600c210203500c801d540c086110030307500181c401c01041141480107079544200b840c0411021075000c0224802c1d0b190b129005001100000e00040c00034410341c003524002e4860031084800b00b00c1c140202c01170b518140c1c0e1116864011411005039403504000402011007010a82c0107250042d800140004000fa400100c030f8164038010030182803150302c82e4a91600040942c1030450405c15a84001e0701c1340041220302900d00003506e2420180c00c1e40481000f008204020700c4051034026423003070381c2d000e100c404030b01441c2400c0200ba41d41c5030085000220f81d00030b0b0b0050502d40d402c0b1901380c494140c0404140c0960282003030200b101c0d228035000340080c0c4054513540 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 992040224 1250 992038974 992038981
    0x60f010f08030c4306084812060a240e040b0301091109060a0f060e0d0611070507090204060c0201031508070308120703090b060910090e0109020f040b0117090a050d08 73
    0x41c0c19404010f000040300c1080d03a520460107078a5500305000d00402c0080c0da01d0307c0240c840600d105909100701c22165000c0800c1c641039425004040c14820001910a0394009503210061032101180d88500980d034090525440f549600c24641c15114090003440810080c00880c0460300b101d56205c415500704c454202d400645d810101d5803207030000c200361001d0030b080d841e1012044525425004040400990000c00b5003e40d8a9690711144035800510802042d51401c240610a40c888802141c00c0d0060010004403030400788283c40803500d403074807022405c0c1407076801100200078a010300140b00304a640040b030b4001c810400701020307520848440780c1d2280709101000e403000c0000c0c00d410402d0709007034840d0f0000366210f9440ea003300042d40c0120958442c1c00e02d102040364a0342056507401c0c9899001015044150803106203030740207403500d0700600880030601068402c4028400d000c10700d4025001c11007195026600c3d804018102074078003003c100e80d9501d050260b0b121035440002e1025052 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 992041474 1250 992040224 992040227
    0x26105010e1507030503090a08031303120911060f040b0f0a0908030901091203020f01090c05040e06060a0311010c200a0b09011d03070305060f010f08030c4306 70
    0x8034003520080721680300100e40002040303543d01c20032400a08001d00880031900311442000020308a681c40301c0550780304e03d0819042580e1080c2100150009100d60160410007052071042d42c4455400030f143d1007002000030700740a09075009040b0f041d40803904000000e0444002c01c060820001c0c0d41e035040350780c0d81080c44010b001e04009e41003a08030760002c1041d41d01c07681e0061008030485c0c408880c0150b19102030705082e0b08005410494103015401c0c000d12000300445a031010042d100100c0b010030032213018080081e581c3d401104c00a4010302d01c5081400031510038181700034006014503101d8060500d0b90340e2220700040101e10b80d1181020a200d25160b0702c2c101c0306075005801c40001c003504101450000030082c81401c110106401d500d0310315100c0784d490a02c1120003554102c411140a030400b0805a0080b2100748100d2901c990601d102041050307000c01114461040a4024000c1d80d6118012111540221034482c0007052503098140d0000081030380c1c4030303500000403e682030341803800f1070 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 992042724 1250 992041474 992041487
    0x108030d0c0915180312030b2d0f19091b17040b0a02040b0c031902010b18091507030e0c01050405060403062705030a02610501 56
    0x30720024001c80075420f10001e81050004080140b0b00c2c42c0800001554084098040d101c42d00054007030300d01181069001505034000f4504a8803e56607503901204959144500070b4440c01a81032001041c80a221686031008151015a200400a107400b080c4004008108203155119a0301c1580b917a0f500040c0103602d0200040d81030240c104000c0e140c0c08460062242030009100501c9800100042101c22059506a82c06807007005106a51403407410000f950360381040090241304004003c1803207103180706005645100300e000d80704c4403100306c6020b842024000001c10b000c2640c4100300000070305d01c021440c030500039880754800040e9000040c0c2043c0c00c201c3d110300700605014040008104a171140e4007201c00312500304500107130f202100440d503009440d8850381c044001c0c1c42000c0c0f9600b400800701c01000341451a0302101c1c04801c4011300c9100401d42c6608054115400340700c41100b1200400d0800c0001132120601c403810044085c0a94000f8001008444184403644043c81903581001 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 992043974 1250 992042724 992042741
    0x606090c0a030f1503120816080a0903030e070b04170f120304050c03060421090e010b0c0c19050306010f031a040501091203021c02040803040303141605030d0f0c0906080c04030b0108030d 82
    0x7240030308400002030117001c9c0c61000c1c0c41a04095a43c58600d001c1c14480d038030200380300c0c41000c251100c0c65031b942d84c000801c0e040350007a003400c20803481086a04490001da980030030710f111800b609424511030185070850b00700420a441c0c500950b0220681b980e001c3c400b481c440c80c0704400803844100c451111103440a0000342e01c0062104078002406030384091000181112400030302960354643c5071891904009000121542010000c1465060078106a00440c2984d205400f1612240c0c0d9840700400d814200784030140003d50540c005102120740041c1c0e20f03602501035000810b0080181e510608a04018115040007a0780450075144a004140140d406003810503015402d00d070038070740d41c01d0302c0c0c2c8590f100003030920504021296101107803400740c442c040f03000900560201e5040c20510749035444545144c40340c03482d01000000951051142200c59002580c443d000795040031030907124210301403c07854008030180320000004503a289150b01901c0c051028507240d00c40b2404800540d40e118 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 992045224 1250 992043974 992043991
    0x1021603030b0105070b190906060e010302041512021c050a060f0c170604020c010b0628050a0c0b0601140a0324030b04080f09100e01020606090c0a030f15031208 71
    0x20043c1001168030200c1c0c00c7d400503555900761542818102d42a0001d040b40c28008240c1c034200500010102021503a15040700c1c0240d40a102051400d401c88111560a0040b5014481020300c0d08016052440d006601441c480c0d80340742d1107a201d074a51350300d80903100302e00322000c645808244005d04418055101c034040ca908140c2209108c906084116020060410f40101c2e4089904080d807003094001046140c400307068039548070044000509000b545c1c404100c5120710410718820828411b400b180c0c40c207403080c3e8446880450560722712902840c01b40910303040000303e1250f181a020300c00d0050204052070746001440c58485100241d00c03c01004144010329062002040894a2103000310760095200140c4c6640d447e40510401e0346004914400343c01644100e581010b09070008c4911200300c00c240c003290025610725040003080310048404c080c6948003446804030720760003a00002c20080090b640840c61f91641103407030030100c0980e401601c1031407481501d4417966401c02e00f26504990b25 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 992046474 1250 992045224 992045227
    0xb07110405090a110d0c060906022428020d1d0c03030a120e03161e1101030f0617030301170c100f0216031103072106020a0c0501021603030b0105 64
    0x221500d95281e00f55040081d003000c40d9204600425a15203400c4a605a80115541a40d580f5904d0040807500030303006400c00f5200344400c6108001e0b00640f160400d4040b00c003082211740c1c07a0b5840e0480c0c42c20001c40f401d00b010781103080202c0c0000745e001414060321039640018601139140d24a400482c03040c40c1c0c108050300300c5206002607440100444001c1616810145d400840385814440100121200308007203000c046034a64107014559001031000e0b001ea000054420b0640c0310500010070030b03290050485440b0707500207000d940250403407004240d100e000000c031715941c0c406c064034104140e941d064003608000011f000816081203d240302c801200020800d0b800b9190100380c02c100c02c10070301760034480c0100003480303030764420450129258242003151407130554901e4903140d46443c202c04d9620a018038400031031480c0c0600600040751502c0c01408020f250320343c42c1e0300300070f5210406550070000c1e403c0c00d54010503070900050020742408000e5854400950a004045901d20109581000b00 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 992047724 1250 992046474 992046481
    0x110c010b040e030d180c030303050402010906030b22150b070c0e0403140f04091506020d050703020604060c0c020a140405010533160b011508040b010b0a021005010b07110405 76
    0x80001c151030f0840c07805200064107050340903000046002c801780003131040c0386c600d101208143d850b4009600444c801e8031540080d17030301d44200340c3c20348400030b91007a00b041d4034549803081400c1040c00c6207849110306c08005000c00084018904031005038000d00c21500e030002e200d00c01c020010072044010024010240c01500341944c00034460303141e0051885030807801141403154415000f0440e40104080e20302001040052550001412114071401016000360b545101f41030780510121b80c505a8580c0c09009159580e030707502d000815202040204100e0200c2d031510040c0c0764802780b00b018002290b2012a40071714801000180c4805803c528050300f031004290014521b18800c91465258503012109011180341011495008070003001400d585079020071001c1c0408006228140c1e0482e119a501c50b080f80501034400802c2690001d140900340c000421041507a44094801c07050144103581170302c17012060b5801602c80070303044045119000180e201c10001e00301144414860140e5041c0074a18 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 992048974 1250 992047724 992047751
    0x50405010c2a090f1b0f11010e0303040b091615030542060c03071b0801020a030e3a1106100806070216060e01050d110c010b04 56
    0x90841c4010611010711401e5201406007440041140140042ca07a02940e91914881c000c0c0c041c0c2000040a0717450001a00f0180240200402e1510826103e450b520b0314019000c42c0d8846c196400030314035550340c1c04000d21031403007170000318001c0d8040c0080c0d210034180140c4142c01c2c80402c1640c685001d40c0b40404000000014031004203000c02400c0004140d65014085410111010b480c2c103400020000c0c104606500c00b13200d1140684145403070b80300c1041003c140002c501c40d6042000d06648180980c100040416400205030529044442027070359032404080d003a41c02601202000c02e448803801c0082800c10000c541140410441031361406001100321020300c0212114804c2c0200c8100e41103500074000d1009600360101d80701101c0c0f00d4501043c94188510107070094158a007d800f01144ca02440022009034890110620400032851b2540c10b86140e8804030802e411301400748502005800706100d200521000b40c003146542d21040085a401c441c04550002c1c851850454143c4041c0f = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 992050224 1250 992048974 992048987
    0xc11210d0201231f090204090f1104090b1507050c0f010c15020a02030c0f0303070f0c050c0d03030e0d1e17060d05070b0f121005090f18120c0d05040501 67
    0x700140c00d000211500d41c101242030150802d081e0400012070308900151740305080e4010400c0340d0706120100300e400010f0190005550389010740e2071800b842400140240c0e05680d02040c00c1a40080801010141d0b0140d400b0782904101c0060341c0c1c82c1c200c030a80711450308260a03000364030301c02480c2020048a0680c2c6120700180700e2a87c901038642e000c10500089ea0082044904c2d80c1345c1401280c944140310802c4a580ba401140d0301800214110401e000c041d01540e070202610b540701d0702408186000f5000d0041120302d210b070030382c00c141e200d8060310718941c401e0280c807039680d1050390b600c0500a80801e07030780246000f86802104121603e984d030346030440491822500302008894240c005500f9003811854a00d043d0891904000c000031925607420102c002071504001d4080036009503941c2d080c510b807181d6603a200d02500003a003140002d20542d41e241205600012009140e0b0010001031000761501ea200140300b00200e00015241050103020000c0c501801e405191242c5050304200000300300 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 992051474 1250 992050224 992050271
    0x9020a06052502011803060213050103020910050313140a03080f070509040504020d1a1b040f0302040f240302010e0a080c22020a050702240a0c11210d0201 68
    0x540c0710b41a5403000c581c4510030151941c4242c0030710105c1c1684074240140254072900c4520b03d04a840d00c0700243c194024020754040000c000e0201490380b52803801698039500003011400004840440c610010b558040c41160b50404100148181c08451402500e880f40140401c5680070100040007011a0707c4011250081000d450109854580e8030104080c0648088001c040f050300f041240292007622501d10322a10541e008e81004001002421965109502500203c007891500c180050b0415030440c4104064101c00090302e03070524410304034034031440c22000e9400070643e00100f0540d80c4c4810f42c41035061085610403526890441c0e843e90720706840540d98002d6401da034501c24a4800c0b02d031000910340310700c5025982c50b102e004004085a00c0144124410304e5601400b0b000300140408070200c1900c0c80508528101c0141003d80d418026400d0850700d00d00092514070b00354490850000c102e26103451804d00c00400d80c81340320308044546030048110387c5400f018215030aa104e5444c000d = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 992052724 1250 992051474 992051527
    0x30b0105130609020307080f010e071707180b090f06030c0316110303130309090504050c0103180609080318060f0112020607241d0304090c02011e09020a0605 69
    0xc1e4000901244041c20a81e4450301e41d0780c0c80030040055158200c1038851207140600c0c8071184e50307a222050b9400b9144103440200008900102c000070742044202e041d90031620320b0408194009030340b000382c18000007640100c400b2000c0403914140d0740c10010100c02500384100c43c443d05614040540a81c0760000030032900c000300c10038105286260007001114a2000218141c035520301d00401c1c01c0080c1860351104400090a142c40040c42d01c40c40d105032401180e200000d080d201041d01c00440241001c14424403010140903d034000284061041001440c400e00605459103040c01010f0810300443c9001102508035800b08a44400e4082c191810740e5482040710042c0015130000c20150700410344001c003e500d50341000d1075803104070540042c660012070811f21640000e0303501424000d6407503005a620386c0c02440180110351007070700310720110030051000103281c6400003034034802d000d512080185001e95800c40001581001c1180780068241c9007495403400c072080c60342c41c026200d405e44800c07 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 992053974 1250 992052724 992052739
    0xc030b0c04051327060614090c03130804050a1d15090a05100f0b0304050f0106050109050105091216060e04050c072a0b0c1903020703020915030a0c08060a06030b0105 73
    0x1210704c80e02ea41000111800842c400030814061400700d001b0545409115000d002d040341d40149460030300511031149203040e001908507141d0300c0c200d480702080d07488201c49101c0c043c48003089079100d030044a401442540700504000c50005c01c1c440c1c0e0400c0c05419916100c00d04002e0807001d484400f403454110710410000103480da12868030707200180c0150000c2035213014001002030050010005540240d004070207446160b000b00d040306003200d40a12986004c9400f042c0100a00c0d0b010340c010703081c6400040c003015159280c20090b0b0b42400f910b2032802e09070f000c2d449014441140c0c002c040d40c0d01d092094400b04000d0a0080002039540034019000300215a2544507030001961801901c44003686480d50701070071916041c000d6010f030800800500c0503c1000e51400c40204020b00b01c0c1ea10b07035016005041a24215000d000c40c121009054644030442500c00c891143c40c20026a04914050356640c0c1886081480241c1810b20241148900c281404014030104882c0000716044403811034009 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 992055224 1250 992053974 992053991
    0xb04081f0f021b06100302030c01030906091416290f070f0605061c0f0303021b19020406171b0a0e010e01081203150d0215070c030b0c040513 62
    0x25014011a4007240c0c981800030603180c40d00b00002c0c1104868a0040090f0340141d6984c1700c1811580c0035510010b90b140d402554204c11f5540203038403600b1021b00800c0c01107603101550700c036010143c82090143c2e901d1760169103c1e040780c66800130307518064903142019440c0c1c00751001d60682c1c00c846d100c103003440c1d0035000141591002c11000446500950001c0404160401030034001d00500f030459001c0d002d0340043c829085010400184442d0407903001e01d01c851121415202100250403003804032905445055070402046020810489140160303c0040f00112407807041c003095640c140d01c140012003004948119887c40030907401c2d00241500c5d04c0348007030100c04c40014141003080c2d005c0040c00b0210360010440000c01031409058900705012140a034006405107141c0c0e04c4110307034000c41d1078aa00b425a00910b84810032505080c001400c0440c5020707040c00034440caa001d80011298052010300820400404519159000d45404c0025041600d020040307421124024110448542d0700c0030b10 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 992056474 1250 992055224 992055283
    0x60b010c0c140d0f03020708100b0d0f060b0306040803070212070b0f04170c0105160905010906140f030c19021209090a020d05130605010e01140f01121b090b0408 71
    0x3ca00030940142c494210501c075030901035101c15035801020354030b00840807251030140c0c05000d002c824100281c0301040d02c1c4125216113440d40e010341c0080303c0c81c03901c401c04d40040740e42c1003111a0049010b001d019580f420007120203407402d41d00c112201070006080c08060007080ca5816140e91001d07010f1400031300c5582e14604150440308071200c1d8103130610049034a05609605521462080812032540056500045800c1e1100d80300391140c107002848800040c4205441202a40c0c08030040401090034038034101020425600115a490031004c0041528101c00c5600021030843c0e40d12800a021105d0313001080c10090702c265215079016189250203d5080720003039040b22000c2c0c2211000f0031060500301e00403d002214400180e4225040c07000214804d0124210541241d81c00180403100c0c200e68021f22201e42c3d080c1c0840341c140f00040c0420b910f045800c2c054441c40c41c2140703840e400c1a82014901030030700368498001d0550b030f0506000a104c02e10002461107641c1821000c40080d5100314000c = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 992057724 1250 992056474 992056489
    0x14010c080f0106051c0629030c1b0102040308040303030923100c021018020108070806030601052e1e02011a091f090501140d020f040203151507060b010c0c14 69
    0x118101458010300103000d400e1100801e61407d0364040240700300c1004001100c06000980708d8803500b01c400c00c02039000c1c40c0196000703031034004a02c001505143e52522000c2203604158030990110391600a80740c10003808092412410401180c07031200c40748100c0d035445c0d590700b0300f142000180e42c2c1e40240d05841c80c001c02800804122008090050792420010303544446904141240400c6c00940480d08940c052100c6622618018006110580ca000104046100c01c40100e5032001008000c0154410b07800c000700710190131a031101c041441c008445090005038404080045916000341011120103104040c1c029070f000b191003404a07112a01c032001000c2045a883c5101140303200002100444c9030442412540a500200b9040142509100d80780030700600095100c0e421160088051030298055030300000c17010001806c1d041c0c48000304564000304044c1d000307061004104c1e0420800300740145801450300f8a821384070400940e40e100c00f8130200e40a480140461114180c486803294074 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 992058974 1250 992057724 992057767
    0x5010f11070b0a080c031501080c1b010519020906040323100e011407081306021306092c1602010906050403110601080c1e0f04060314010c080f010605 66
    0x40584003a150740b40314800555100500141c08501c0380c200181108005200b604e100300c00c00a4407140e01c0400d14011190b00e04010845012800184076045401100801c0d411015440c200002940d0628100848828070043c4100c0b48080c0100180c001d1a1200b00a490880340d0000700009601c50340320301c00071015003200f14400d941c86005180741944690b03411408032107500b50001c10a1180400481e4000d0348211020307070110b0300600c0842e09081d048802401958000c44006080689841c0182d0150100382d20400002c1d400e040113000698094600488200000034002c044401c20042d0b2180c030310000340075401211110f4072641c8107a0003034000640181d8480002c0000e4501440e01030a2aa0313036131403c0c4020b104410000c50b9031b000c0001c003480780c001c0040c0268000c40c1c0d4200d250407500010382c010382d00008045d0344400903032103e000e42000ba61107000710300120705000242c50f0131113150b05604400c0140160a105038200070184080c10360700a0b25241e81ea51940c22008151020101c = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 992060224 1250 992058974 992059007
    0xf0c080619060c06110a08013f0f0b100501021006260106030510091104060302030c131d0d020d0302030c040608090c180709060c080313050a050105090c0406060203120105010f 77
    0x401b1540c540d40031100d141a82c1a10088000007440b2040d548004581914000402d1007031000074004403946040d00ea5040384503004410200415944000d0250b00548000c50342c01d5001c0414445580c051100b038071312640c0c00c1e100304900c2d450880201080d08480340d51f40485034a1003050a481202074000001a54210382100c370001e0348800300b280140301802d015a100f04606410803150718050180f201103c1d0010000c0004003581c00030801c015080000740141d8070303603459a030030b0554441c00b05400710f440b0b581d019112a000c0c03004041d0810346184c1504040510400070040101e0420082d5426030f00342e071905000a545841603140b404a081c8007035070b0301003880501000c1918124445a214120300c2c0e5030502c0c05907803094240da440f419620020b1600d8810f100107580d08650303034003181d41240a401142c20b0301500b9110a0b003115015101c81072603030001d43c8520351606190260310010115403008614100c020001002c2d950018042d05e4100a00701072000340a40c0310b0550030000a100 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 992061474 1250 992060224 992060227
    0x3072001180b0901030b1f0503130f0f02240403030c0309120f0c1a04090b011b0503090f120d0e0a0902040b0c060105012309030307060f0c080619060c0611 68
    0x80300030414040c3c100c0c0c02042e0000703080c11044041420000c2d9000c0c81c50111003142c800112001f102a00d044d00001d00141d050802510414042002e0b0006440c1d864050500e605c030880d206d0052101c030310703032412601c0403075202c0356031800141039030104440450342c1602d00011701c207881740b80450310550707680e001003075941010b1040000d00c8250451008403504c20b01d00009003c5d40c031085000d8032541036040c0032851805102c200f1807200c141d0001760201205141000002040d254010090148410240d07410f40c00800c45851a06109110f0030f040a003c8543d58170f007031074181d40030741c0c0c2e82c0540c00e10100704000d1f101c20318015111188002c02410040c1020341d01c03240c0f1000b900189401c1482c500c0b90610440c0c000150a5020748160750751501c884010000e0701c1e287e180c0d411000d610001c59180c2500c01000400c0110b03602e48511500d0010b030500200700e403c10758034000e00981c0b01800a600c01c9a5101800060040114001c4110741c2d290400320500c80542c20500c0003001e0070407800160940 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 992062724 1250 992061474 992061479
    0x9010216051501080f0a0807080909130507060201140a0f06150c050105010b16030f0504051302040504050f06210c120d2003030105010c11131a01020307200118 70
    0xc1592580b07a0107605014645a0340c0310059650f41d14204210420350b04464080350100307892000412840c1c1c010956a13250554020104e100700400700d58001c011909501d0120401109001020007005903200034010801c1c20315240022200242c980980035139503d000307900340305068110710020b01545500030a0303040c030644050a2520705c1c0004490725460140089045500c020a44e10010140d0002c41003d40d01e960701070b03400701084e48100b0180b1006002c000390640d41e0024011144141e20405a1110f103080144000e968010f40740c00e00d1006110308001c610b0310760aa10039a10750041c00814100c2c84200c440ba41092040c0903501e030030a01d90200082880d20020355503400788140d9441c01032119159440312140c080c07403044880d094104100401440d80f10304541114540a11400c040001035040000c001c00e0122040c402216140d000b540902200412018448a001e00246140c042e450b03680004030400746130141240d02250520358446c0c0d20a2144252044402520444858 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 992063974 1250 992062724 992062733
    0x50708010516140f0307140301030f020901230405060d02040e0c27040b060f061b06060a0f0e150901240f0e01081812030604060509010302090703020309010216 70
    0x200850700c140700403450031400c150203807080b0040f25a40c2e440071941c40c201255400e500c1d006030303c0a800f01081107030b0b8841c0c1c810f950801c440154001e51260024450a0a66105200c14901c059000032844404d610a5045958101c0034000e04114111000a4142e40304c0000544a41c100100650403500e0031950303008480002179640c00b4070b0411150611140318558032000303100c003030a507203404001c6404085000190f000c2a8640c100000908540700b1544900100303007036411407031f00700070349181821086004c44d00c01c1c480103420200c02e98010600604284101403203010603c101d400803900100001c06600d4504144500300c04000c02c2d4605650307403442c081c912146966401d5482150074490a140c40e1301030210080c6078252522400c0301100c3d103200656405c2c0d0020023841d40d802560415000400c02400540307204045241100d0300c90a2203001e203c01c80c0c032290405405450510014000f6907600c0c0c11a0b54481c00520b40581d490b5140304c03010340a070242a14002200c0218040c000421 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 992065224 1250 992063974 992063981
    0x1427040f15140a1d1009020102011121010609210f020406170c0405390f0d0b0328080705010c031a0301090b071101020f030a0510080a030e091305070801 67
    0x1070b4424641401801040d000782d440904981e013442c00140c1c04050340f8807400d0059000b0400f914014000083c102030280d803003001d598044004801c001c10340020040d12142a219214054130481c501901744034200703ca420f00c201d60300050490008100c1010104200404003507907181c65014100b405800e50383c20603840040303480d8002d10b030280a44e4050f03d980b81007a1180612600710406000100031400d915140e406141d00300c4404400846907680f0850980c8030003c1c005154003800c119513a01a06c0300b150115801480c00503c41d80201110794030400c007400d40403e0311203005000650000103440c00d440c19106035034000302a5420042e80c0600b954050b80003d15041090030031001409600302058225403000705c000300045030000214403018440e992424080500b1000149400c046003161041e580044a107540c40c25126000c009500912080c0c000040566030010884401d650b41e000e421b5062051000d405158041e00260b800b81c241b1056041080c0c002081c0c4895549681815000c0d = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 992066474 1250 992065224 992065231
    0x304080607080601080408251203110c070b090a1503050f01090510140607051504261c0b060324030d140a05040305071427040f1514 58
    0x5402803200003141c542c025100144600416034807502c075640c0700d584010640d000403c003006030720703001c484c550040180685003d040714060b00300a80c19030344040b0001c040c1c0314180c100b0405041e040c8070390a88803400040c0d04c001e840c2440c0b1481c1d2107005100216480c010264066070740340e002d40000c42d102c250507034030140c0034006114064031030b41e8840b41500140c502c25100700904032220041089200d9041e40e03c0180d0070401485a0310b03107c460344900d441d009404140d88034070380300c1205000400c6810822110103a09040c03200d20407000c0c8142090b200d000b1030221840e0f80f03065403000b06829005030b0008a100741d00500564032409c02d01c03034940c4032030a11350445030b851210f000c0d9071040d4900016041b20085465490b800502e0250803160160340000d040070052010900000c00000c000f40055005880781c240410740c0d8410080411020403c4045e1000112000031060780c0d501541d10f480301d0307202c0e400a11010b040c800e1442c1910f030201c40418826003c034540101c0490340342d004200303d0300 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 992067724 1250 992066474 992066489
    0x121119090905010507091401080603030d1d06010618060318020405090f0d090503190f02040507050a0f0302090f010804050a06020f0a0e060408030405150423120606060d0e1006080304 80
    0xe5917911002c0d0781034182030103080e1201030711100d0748902c1d6102d889141ea0100b000350a582c03d06004841800c203541f00ca032107100c1c00001d448507403101004200003050040500d4548a82d41c1c2441c1500c2140e0800c0134040c440130541c403400d20302e03900010007101f41c002907400f03002009945000402d030364645010102488550158480d0300700700900ca01e07954800c1d030303400030080c08a92031412001c2e18416942c0504580c0b2040018201000d6519441054820741403620341c10380d0780f4000704004000d01854450301050502c1440050216182d121104a07400000e00381204d150b00d0b5400c109280c007501e164010551400001c2c080c00025180f0301030104001141c80e01c11441e41d01c0e070204003080c0102d000740c01c440d82c4240004c01035032034141c140c80b4804600910390340c60b15445801404980c681c110651302d80c01e088851001080c10302c1d612400040000602900007405c0c8240020f445128005084420b50b403100041391407a4028060600000d0b043c0c141000301a40d9640c000c3d8032034005204104 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 992068974 1250 992067724 992067731
    0x10204082b02151501110a03031b08010f09020a02010b10030b12031c540f030e0406050a081e1b040908120f0414030412111909090501 59
    0x6801d0340005004418030501e07018404003580e07481c0c1540710000c50000054100001041e41c400220414003400011900130b50f00821550345080c101c100504617030a20104100c030140c010040c942c0c1c20001c82040e0b40041802503915188070703504034090f0100d96280d96029250220140e09507405030712100c0322001c142c0710511190901141141c99004d10701b50310050300404100d241c80c208481d40200c0b00b009000144680030411000c0240800912544241d4200d1030008800c400d45540b90b1040c000200f103c100c2040c62000f0340da002540b82c402400202031144c4d01511544540c0c5030b80105018110113802c011480d03948461599403030001540c2040d414113072081000307090501085621004046820b824802c0850800b400000e000b0903406449010051020394540c17954051303403174040c90543c0d85001701402c0c603040c400100102e2141c12101a0f200300820824400c61003038000c1e0254008400044e94504003002c03444480c01044000541c2074807002c0403680c0c0036144e00c819201c2d8001e2000300f = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 992070224 1250 992068974 992069053
    0xf060303020d05121614070803270309040b0a0801020706140705030708010627090e070503030c0c090405010b0d03050d06050108060a0e04050c060a03021804060e130501020408 77
    0x1a603041c130490524090b103150b5013002404990701030b811030405040074944100c041e101403650b02c8150301b1901013142d03d80d40010911082132180341c00b440c0c2c2c04104c261038080240840746816901d01c01d50040d28081d07034450040c141d160359854034580040c01d0716802035503102d0b26440c001000300f0081200d03c1e6104000c201003440316200d00203592041d282511141c4145e420818241d644c80c40c0b005481124109515962005840d800c409000400c078019000c03031400e6103e503283c0e00b8050183c00050180d40240f04204010600040020f00303800140c0320805141c07190700b070050150244d080071a0300314451413002e008059100004101c041002c01007006581d84038001103458042c10740740c00343e10011406091001c0c3e0016041c0d0303504a0b1280c4202c81807021040c022400c00d410001101000c2a40883c1d1034090b1501c40e05500c0c0780100071103081109504211851411f928003410900301411440c1e800b4040000c2541290081d100c0700045500c0e40a85083d403a900402c00d0440304489100001e21 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 992071474 1250 992070224 992070227
    0x21090f1009060513020d0213091e02030c010f091e0b030103030203090a121110050d062d05100f02160e10060c0203060c0a090b0c010207060612080d050c09040f060303020d 75
    0x44e4900e0a43c0244122545041c98003001807010614a10340060b660320030040c400240610314101030200c010300c01b0201c81e40d06004060070000d1000f0800c0c14443c07040380c11002a94400b400d1801d60b004142d43c0001c0c003403040181054645a504030341a40140000044241900040a0300c02020200c8500d000140c403640c003404a4100010001c05043d8150340c001203910b44514407450ba281c1c2450041e08241080d42c006054504a03440210304504186c581100341e5850032320020f20316590200c1003a0503207018007088032b030b00d000521a010840e07143c0203940c17500e209210500103c0c40f00c070000c081c0c607034940c0e040c2000c40809413407400030348003c1603000540600600c0e00010143e0000d0151401c0e64071665444041c0d880440042d0812841260208000d00b4940c00750450080c504001a160742e05860148210307940d40e007003c5483c0310003070038250020703040c2c100300c0300b0030092400c001c00c9503129410315074464080c00b040380343c2c040e0505d54110725940107a8025001c03030f40250f00719070741682c3d080c10 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 992072724 1250 992071474 992071501
    0x706060503061006120b06120f0a0c18170a080a0e0316051c080d0903080406050609040b01030f03030b0d0f020411030c09040e030d0e061b21090f10090605 68
    0x5007070003017400011502d20a480d61750114070b2012024150902d407081c11041c140c003042c401c455411003486545d0900500300c50f94880c2100070b01c950b0400c08030380d000310280031030811560710640c01017682601c514600d0410074000009029400144191952070480340640b00008000c8800c0c001d00c40c4035645a1481d46482c0c0070421114050000c1d034802c1074541d50a83d64078190302090311700401c01c0080000c14580d921a0450700c1e0b00039641e120302410203140c90000d440c3c0203014140f1400140080c0000320306c1c0c070310680381107952145a0805404240c0740580107804203121a9a0141e4581100c2043c000990321000e04076108590070042107411101490b464041911000d4418106124034080350801c0d9024510070210031003100d0501c00c407060f074071041d01c00000c00c810f8950000c0c4c060144000000854405002d80c003880b15052540c0010381030640211b42c0c012852071003245d8045040994240204614003481c401600e41c039003146084500a03121806088859900d8140058001844c17200d = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 992073974 1250 992072724 992072729
    0xc17130b180d270f0b030604090209070e0f060a0e06030718030c0608071106060103090302010204051c15060b0304020d1a1f050d121809021201090c0c02090402100504090207060605030610 82
    0x81c02c0c8004c9500f840300c000c01503000107113003e07041075443e0400c04c09030783da40311368030b20500040e40d90b244030ba1410021700100c4552a000d544c06201e0a000401081c0d07040381007200c05070400d840142e180d69840c0b8044640d401c030340d282d201d8491380300b001c0031051140c0c100c81d2400355400c507120404240c41c0c105007180c503103074600c2041040f504418003103545036110342c0003221080d000340b001500703040c2c0f11000500349a20141460504c074107050034110400c4585c3c204c940d814440540c0421540d0700d040b041c2c25840c8001000248603c080c80c001c40c042080054410050791000700351000d007850580da143c002c14048182c00c1c030b80d500f80540006014904042d0f14114260f0142d10110741041c07040094501c0314080f40c50a201003c01000425803401c50b1028106100000030600019454a24610708440b00c0042c14020031401d014264050303141c01c19125045030741610800513401c0c0d407600844141c01580c01c94902c0c1800051060140200c0f0b4115401741c40003101a1a51502c0e90920f100890a052 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 992075224 1250 992073974 992073989
    0x120c050705060c0304090501090c030c0c0b010612270201030b040c05191b0615120b040210090503102c12090a0302040f0c17130b180d27 60
    0x1400c050081d410b2150242035400b4118003120f00341912440b85009680090b0070001c441e5991b40c0744c40302d0003580360061401d140001c0c104071f050398069480e4100c41d0b28050040700c0910000b031114454130b00003503005501440344601c800080c0350b03140c0705084071a1081c1c0001d038006824100c4440d602c0c0303402c0c425800b1401700740e01e80501e403070400e50300c0c505608a034114103400d20940203440c00c00310315001b524036032481c8103840004021030f40141e05d00ca02901900400000b01c699100c500c0003404071a070f01e43d00a50116140008883c44c00411591102d103a00b1440d0940034124582020900c0c0340c000c0c105d185041c92200c00c40c1c007501e4400d5180d1408500108500340d0040c4042179003444840b0040c00c2500010300b0141e001e58681e0041030130348600a003607101880c0d070384410f401103030381c044030b900c00ba40c0543c1c2000d01da03801c20b07869413a03101000d01070240c0304402401c0850801e4060107117100c0c203c01e03000192207642d280c1e0f460240ca04032070016080610031a100d2241c61001d00d401981c01a244c10307 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 992076474 1250 992075224 992075233
    0x20a080f1306050405030702030a0311100b2d03100f110708191b080d050f09100b030102090d0615080a0308130311070b0a0e030a080d090f080c0703120c05 68
    0x60b511140040e000180c01030b0303500c0c042003181f0009a2801c0c030220140c5030182e1100ca61701003070346003a98a00100700f8403a03d000c514080c1d5841450352000c2518450305030301d01c902030307a008091286501240c08095200d81c0741c0715007060712911482d19001040c80c841d41e083c0c1000780e085601c06040c5e2500c80c50800800001081001e0384d407840640070905803803000e600d07101c0c900840d0078030030440349202c005080c0c2c3c10520104880c03030100e40034000d0a601c1541c09921107030300c0c10304a03c1d0a0350740341254a8100001c0d100c0008900c50b40f02541650781c1d01c00000c01d01e10300d0640c075084c180028000030a15502e0706c0940b00300460900c800046181102c1e915a036075000c3c0d5650404a502030348035901c000c50402801230602d00c0358440400965002e059800086903440d1800040030b4202c02c00c1e0072450780650071401124011a407a40141c0f91981c58103840480e480000b85040341c56600c01c0c01008101c0301e030110322100110800541c10055900c502141c0340418000041078403d5524500000d10b00c3c1d10 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 992077724 1250 992076474 992076511
    0x102706022409060601351005030c031c050906030a06030327091d030c07150e060f09190305030301030b0c070b180309130509060a060e07080402010c0213020a080f 71
    0x20500601e00074041e25100c06d280740000c804400c00c01c40500e031420350345440701d9092000c0d01d4200700650000700000c90003402c0c540c0001d80465140c0f6103500c01e202080310013940040c0c8060041c02210490003000f040e40c0d41d24641081710000800c40c1d0302040d40080c0705034030010b80e4002040540c0e000d1103640315600440c0d9241101000160500c0809a0403441d460034090180440c10400351031100802005045040e08054005620f10be00a5041c4100b0002102c0580e40e41ca5000496840800c11910386030303500c01303010120b002c0c000c0c5850400d1040c040140c0000a2050104c0a103050364840c200c00355050300d40954580c080d004a0001615007505034020603100702c25200892a9142c0ca50142c07420004840c0008845601d00046079000c2c0d07031903a0820151200c01e0220980c4840002d0080040340d0030321041010a400c0100044244401c91011600756030180140354401a4000d02000c0d00d50b1000d034103400070350012001c4001140315200410021994500000d200f9400120040d81c40b22 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 992078974 1250 992077724 992077727
    0x5120a050706112104060b011d190e01120312020316080a11041202091b120c12010312020f01090506060d0606120303090b0a0902102706022409060601 66
    0xa0000120030983d410854501040034904900286000604a186252801c0d003445800d41d01411815410009000400008051120040c0404ea030080e01c40c1e6941a400c0506d911840040341c228000d60900c240001039a15482c4440e01041c2c0e101b543c82c801031507500b240079416400103940708504c001070199801e011504c0348803407a0f0310456908020402281e40d0004a100c4e500540202a0402003250001c041d410106a95a00503e480140746403030340104104401074000d9280d246110b10313003500401c031103103d42c4041c1c1c0c40061508210300001d580d41c0c0740c021069101d4810a001602443d520141d07525018800c1000b9a81c008000d004280d80b441e0402000015140b02102d92598807080416040d04a0403030780c1c000307482605d000950408905100182100040070038810f070341410480030042e181c104040328501c41c00c0c2400c202d004426980c2c522510303812000e81c241c0b007191040024419500092a02222903c0c600f008188440d0654120724130001b00e60408072503100c40040303010795 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 992080224 1250 992078974 992078981
    0x50309101209050f07050102160e06012021030609010b0c01110706063b2d040212010204061b1a040803071d180a020c0d050705120a050706 61
    0x629103241034070501600c0019001120018001600d403a0310512840c040c1c0303102000640d001e0002400108804024000303056820040c0740110910320340e62601141d050707401403111290b00c10003422441a00200354240310355800c10201102d4140252503c1e415075490380c40e04030780c0a02070281180085d03071309060076a001d0368030003600d90303080b1b640c0d400d810b150b40404071000d00156481504085041440c200200c1014402c1903101c88451001500d011075404039030009002c0e01c41d0440180a03103a5402c0d5040907610b19552882c41108036041915080710440e94425204901c00c50314458118441101d2a00700d002d00c6c00381e48007080c1c40800c401d000e5640410392044a41c4190684407500d0404440018114401d55048a4104000c000d100c0c0c1c05821103040032940409860b0b003162504003c000a5107200d1841c5804140400d40c400b00c0e110102c260100c401c071692841c12542c040d80e03d84001802540000d01c1961180520007000d100001c540045911140c4156079284c140101602c1d10300c0207 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 992081474 1250 992080224 992080249
    0x4092901080a0b0f0a0602010e120a020a0308060a05040203090a0203061b09091b0406051305010507170304030e10050a140301050d170c2d01052a0f030109020c10050103050309 77
    0xb1000100d002c104e43c0d0b59402c08400a40070036400440c0c120070340e40510745800081007010752041803d00100101c2a40060815501c076054505000c098503210b0120314000903542110341c009000000f0008441800203a442e0b80d54406c1d401c554035a610300c2e00c0c44040c526a00c50b09120300300c08014002d40d07446c28030007440c0c00c0000c600321040940340b9030f990740e40c003a807291f80031f5400f1a80c0481c43c2c1c4003a50880d1541002414207003407842c44c2c0902c0303a907143d00c0c40d0b158081044004c40080041002c2c1032160a071744020850107006216080405030b03020b440c64002d1050303a00022014040945110543c4094074100e841c0074105020307190041e03039641030ba003242c01d03500708249205209400540c4000c00200030f1030348101110910351014007411544406114000301590381c14401400220001c11101c1050100c0c032650442400f151040703c07415510980d051030800078001320002c03428a034140d00420001c5200000c0344c442c00c0d0300302d00a506070740c4244000752582c4c100f40711034802030600ca00e841c04c5 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 992082724 1250 992081474 992081479
    0x4170703050f030f090f030403120f2304080c0d0f0b0408160b040b09031e0c070b03040606050f240307030e0118030809010b03030f090a050604092901080a0b 69
    0x6001079402d10350303a99002200c250130701c0310751403003801004042030041c0d00c08080220099850103056454103156500704544c4201004184e40c032590409105494030000e4803aa98006403a81c46101080e1040c1d81190051074900d00940c501080305190002002c0c0e02550f001480140031940e42e12035a25842e0010025118050100500e12202107449a10a03a10344500c5040f0840c1c00c0c1b0381013039180c07030400030020b00c0c0680c0200040503884642100f0841c0d0b050241048079a80d441d03190465042c040300398071403490744801000307002c104011900008240c071020347d440240c04c0520b1081008807040d144040c4004203c007031800503001881c070000c1d039008126040200c1c0c00c58401c9511800c4515042e006c0f84841d0440108004040d80903103e0340d0050104e1000740714031240d480000352288181c14800c0046440001d01741d0103a210b0070003c000408006001c0e0b612039503210501c002400518030070302d045e07042606914480358522441540825010780d5800390503554024001c0003052104001780c0e = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 992083974 1250 992082724 992082727
    0x30a150e16090b0f19060f030e1b01020c03030d021e1e09011704150b010216180e0723040212040602090f03010f091a010b1c02280e01080417070305 65
    0x383c071034803911540d2030720141c0d03140f45d507090740d203001d500600b0021404002c50030981020044441d485001681400c840d21000c101c02c0f00c0c04010700140c0c41c181400405c950580008240707500e00702403903030148c0111480b03030089005d2038448105245241c850316008840d9581c60400c9480315964900151102c214181000f03580d040d036425000380c02000490b0100c41e550440051000c031299180500c030070100003800201b180601361107440c2c19135080e50050540705a08140c5821070950301d03401110b000320110081d15107a54841d40703440c0b1059a40380c50000c1034400f0050000c25414548201c074000f211000b900c3c001170b201e558412010354011504103034002c104192000e180d603020b00c6003880809881c800001c2d2284e43d46032000c81c2ca4040b841812420041c803004024140b110b0080310100041d05541c900060701d40e0585800a014050f603010784034680514207041842c004c28000103100c00d039100e1610034001c000045503020380844004052031a102c3c0c0e801e40d0139810308040e03c08d8a1180c2481d9 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 992085224 1250 992083974 992083999
    0x50a110c0312040312031109060f0f03160906080c030c1b150a060b0309061f0f030c231513050303030415150e060d11030a150e16090b 59
    0x41d1030602d400602c01c1840c040010100204120080c800622903510b040a11010346c06112009260151213842ca01907200010414003580d9a030080721149a510780c200da0b100d040078104034448a050400110114030081004119140102e007000e01c1003424a40d0107195a0324a42c42035911340280068030080c000008480e40140c5080c007001e802d0705180c54a503a00c620f407034240241920745992001c0c00048080003480520280402d60540c0044500944e86100c02c00100d080d2012000364407052464442407004804c0050f250212021110f10024a40303200000340301e402d00311340c1018001c40d4040d80e00144d004090b40c4880c080e013458000d0510032654603a40320040b9041d50b10454044560102208851164215074030540641d0440720359000d000f2424162003003131b8110b015194901c242c03000d03c40e0000300440d0b241c2800f19550050280c447c6080d05151652010750035010032021103080407603983c82003600041080131851545d010140d5603240c200e9440003800c82180b4030340c014100703103c0f4 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 992086330 1106 992085224 992085229
    0x1425050d021516080a0201020304050c0402040e0609040501110d0603060606050304030c110f13050a050f1b030a061205030a0206100f140a03121d10050a110c 69
    0x1003c0d60f0300b00500c0321500d4805403030401007000d07a0001d44100c200ea03064001e036004c1e92140084505041d841405c02c0242c0c012400746d11341c89840700c00014924a0008115904240210000607955000c150203565680c40400d0b04c410080e22074204000304030107803203060010860351070f00c40d0550420341e400074100002f05e40050100c2c000c5406110306542c48c90300040b907104004006c4545180c07044085009401c3c120382c940000b03031400700080c07014401440170a1207041c0e03140b0050a180f0b0454109080c0f90000740005451582d2a03c0200740b1601c868002d60015004500075910341036043c3c0000e10b403800041903442035003ea82c10400c1a136401c112840c1c180d404d00d141c119000c00904010480c40c426603400504030b00c4e000e01e07060014540144a40110b0807040c203040412008100a1018200400a030500000c1d020090300d00345a02c1100e41c079910b5541581580c4c0400c0301c4030f00 = true := by decide +kernel

theorem cover : BRFrame.Cov 991906474 992086330 := by
  have h0 := BRFrame.cov_init 991906474
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991906474 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991906474 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991906474 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991906474 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991906474 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991906474 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991906474 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991906474 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991906474 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991906474 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991906474 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991906474 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991906474 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991906474 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991906474 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991906474 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991906474 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991906474 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991906474 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991906474 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991906474 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991906474 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991906474 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991906474 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991906474 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991906474 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991906474 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991906474 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991906474 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991906474 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991906474 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991906474 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991906474 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991906474 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991906474 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991906474 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991906474 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991906474 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991906474 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991906474 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991906474 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991906474 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991906474 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991906474 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991906474 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991906474 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991906474 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991906474 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991906474 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991906474 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991906474 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991906474 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991906474 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991906474 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991906474 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991906474 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991906474 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991906474 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991906474 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991906474 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991906474 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991906474 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991906474 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991906474 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991906474 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991906474 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991906474 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991906474 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991906474 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991906474 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991906474 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991906474 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991906474 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991906474 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991906474 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991906474 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991906474 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991906474 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991906474 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991906474 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991906474 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991906474 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991906474 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991906474 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991906474 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991906474 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991906474 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991906474 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991906474 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991906474 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991906474 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991906474 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991906474 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991906474 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991906474 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991906474 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991906474 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991906474 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991906474 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991906474 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991906474 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991906474 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991906474 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991906474 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991906474 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991906474 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991906474 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991906474 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991906474 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991906474 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991906474 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991906474 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991906474 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991906474 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991906474 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991906474 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991906474 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991906474 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991906474 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991906474 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991906474 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991906474 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991906474 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991906474 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991906474 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991906474 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991906474 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991906474 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991906474 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991906474 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991906474 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991906474 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991906474 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991906474 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991906474 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991906474 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991906474 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991906474 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991906474 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991906474 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991906474 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991906474 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991906474 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991906474 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 991906474 ≤ n) (h2 : n < 992086330) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
