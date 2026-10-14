-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2313
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T06:20:03.883863+00:00
-- url     : https://prove2.me/submissions/a243d432-d2af-4dab-909c-40f4f3665beb

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 415827338 ≤ n < 416007194 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 415828588 1250 415827338 415827343
    0x1902030d020c0f12030c040303210207030908430512071805070c030f090f15021605010915021911030609070510030504020316090e0f0a0c0509041e05 66
    0x200b00f102d01203c0301c000c402d0210115a000c2119595800f21041c403041000c80c1c800e48002d41ea0001c0d11200e051030240203044501640d20141054020034039a100400024030f0800c11070500710303a6002c12a40c0c0e403018070410720001070502000c1d000039400c81c44041b0245c001c140d2070001800000c24200745c1310071019003e900c81c0010b00c00c042c4810b0f03010290500e051280c0c02028403079002940d6440244043d60780656841d454151943d04200d02c8100100f441c1c0440444000644410b5400f40b480d031035042c400a190501e81e40d85401c10008421003000785981007128107003a2052105c503103001c0c580c0c0c8042203103020a03030300002610700143e01c407820611021000000d09208182c0580f106035803241c86480d91403089109030380d0007403d40c00c0d40388032441c4642d000d690003a2005094488070b00001100034000380030703034106509481d510300890715050b0080094240c16000003001d800707043d01540300c0d00d8000905114481c000c9010304000b404000412001d482d140343e440104818090043c10051b0303 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 415829838 1250 415828588 415828603
    0x5150703150605120f180304030302060a0e160308090112050f07091211090a0204240801060c11120c060705010212060604030f2003030f03041106040602031902030d020c 74
    0x8601c0c401000046110307881081215810360f524001461a42c0321402c01151849005056209800092050405e40102400107000a5000307900404550a0800903242116001c600d95034480e0300103019a1070000000c0c2e040c904403600071034010785400c0c130940143c840b44c81a00354171410034609003c01c11442c05ea0b14486019020716074941e42d0003611480f0503a040081c0302c4019110b00c5c441080003215140100c00141e101180800242c1090380d1071480080303400490f0104401c52800d00003018010364460b15440c01040c44c0d2400c0341c4560307019150411000070403000340303016100346035540301100380800104032004d10251045948601900f0558000d40091504507846040c50b0040352080c90201c041d9402da80d0480c40560078109545d48864101a507001d140c4404148113403c401d01c3d036400d2000d0701e040c44078005495031f2480c203450701010705814115010311034941440103001e9258000162640240012001488046070079000e80c03460056404013000d031400095002c070b98130404280078 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 415831088 1250 415829838 415829861
    0xa030305011410170907120809040b03011104030b1e07050a08071403070507060603060f0b21030910170a02041503050912210a1b03020901050301090905150703 70
    0x410030403807400704201002c40100f4101000440c5180705030000b442c56010f860f000084281240d800c5940ca01454000b2216a0020341d0030313030000b04092505003060301030302088580481c000c00c0b171007101c4801950a40030f240400ba00c001c071500009158000d040c804520b41c9088505242107515000300020720aa010394480d9000511781c80104540314080c1c06c0807280303424425030140c00c40e6a6014100c9203600602d8042c0c403411303111103000000c64014400e600d88075104190100c1d201610509000c0002c02560340400c00c0c5d800c6c04e541c140600000710070340c0c0e80410101c031a003101060380c10040b00c0c540004030540c80e80307100d004140503040400c1e50007003003290407030010b000d2960100c80068045804c2110a6a480d07088902441302160400300280b884110841120561101600c1c140503490421140400d01c282d07100f0b00300c42c4000c940d44040a0b900e0181c034041d45003050020000380280070601c078010515442c3e01e5800c0404c1030074400514489000b0484c040d8900e04030300c0090147c001840b00 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 415832338 1250 415831088 415831109
    0xb04020d1401081506030705010c081b0c1c1e02030703060203011202040c02010b031f141f0506130b0d0920011407080414030f030d0f0614031b010509030a03030501 72
    0xfa51130903601629103100d414006c01400c0349a1a19005403401c005802085070300c140104584420210410305030300850240d84000d2114242d100705008807400408035541202500d11b443e00001104030b442ea4442c000214807940308144244042890100184c0008142e24000700001c248200c42c1d05c08181c0042c022641444007201041d0309900b203c0100703a650750560404480d07540e159290030482515002c1c4000000f0f1a84406c0340164100f0701c081c1d582d010384c2c030301c00c01c0d11505101007122100040d11044034168030302000c1e501f40042e04845403191103546000400c7e0340108503184d038403801404d50401c040e80c00d51895a45648190f010780e120f00303030108202100100c1e20940ea0b000380e507a103a501030141480e02d4140104000c950f0110340d001d135414407840b108044a410240050462035806d001d02103114000108148103031280d58101c282c601e18101d003483ea1540e000200140081d05420303614201e1303201c82004a4062041c1802030f60988202d80c0300f4170807d0f605900650407118030303c84 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 415833588 1250 415832338 415832353
    0x20904060e090307030c020a1203050301150504061b150c08040204050a0b03032d070c1401020d0f030906141008010b0301020a020a031d03060a060e1302090a0b04020d140108 76
    0x210401c0740d002614403030059401400240b0010380902007840c48a400103001290942e6204035071014070a42d501304500084000c40100509c124558020f00c0b802d0490900c6130415007004002402603010903a0031000d510b0107000d43d4240481c40c82a2100400300003001c1c00300510141002d49001019203041740071f985010006030001c0028800d0321003420004010b076241c0390740d10a40120810018032801c2c03070524899401d84084040c03400501c4900d00c2252200c802d9450300f0310308000d03030007801d40c40c80c155084140c0e0b12800540c040666a1715603038901f000030f410161030602d5001001c10b0010050a102410148040314a186200c0403c40e840759009110744012503007410300307031300032111100003603404441c00e800001c3c01055113420b061645c036190301c40f441080000a1a080c0107981440c0265a10034003030000c90300c104070301940019110b50031208981d8550108640320402080c05d03003140c0d51143d661181d507459030112101c101c0420001c9c800310b80c0140000d004a0800e00c281c0d4190300c5040c0 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 415834838 1250 415833588 415833599
    0x304090912172706090607020f07062001180c1a1e0f0c1902040e0d0c0803060a05210618300a0c14120301140d020303070602090406 58
    0x80314050101c903507407021162501910320b0f0b082e4064245800d01d41d60310801e110328042c02044003034450001c1c04020641414544000f07814000c600c000e41708603400c489030600400f41c0154070060b01c409010058203800b940c1c25a62801002c0007505000c0004291590b10180062844e1440a550a82140c581c46401500302070040b8401c10001030306040c021100220350703401d00c4029084410743c00360b1803881c00300425400350501d0044183d0a41c54018110980d0560410748164103a10070004028a103100c660a000b400b90b03000c050004001c020300000162030391711012030800003000c0203800200c0010703186910720002d0703948500341000ca00c40c00000030341050800c1c954040b640000000b4240200842c50140102c101c0040d07943c50505c1031400185800780b141c001052050000c0d03580c80c0d10100700b072401510701595041c24600d590b1018580050a02100c803c03281110011400e0300741c010403003070218040d01400b00010350b05001c04111102402a190024807604500315802c105541c0c845 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 415836088 1250 415834838 415834847
    0x4052d0a060b0a05060d0f05010f0302090a0506040b0d141009080a03090807080304061a0102010b0315041b1e09020a0504061b0209070903060f060528080304090912 72
    0x20050914540c0319001590100d60326511007416044003610f5081c0650322400031945c1e0b5440b01c100d01044a949085c082c200d5103071442582e01406044e480d55625500d190006091541e015059049856031080440d040fa0b6840d401140c001c00d01620302c00c500000d50510381441000810504224010300d00c0c0e03408271201e035100b08070005a014900c1420a844104c0880041407030040c2140c03030000802c018804075120310055403103135100d400041000355018959030340080303907010070505580c10322000231840e0b039010608000c1d0922041c0100900e40d224106507554030041035082c08148541c4601168900c44070804070310301110f039524421416070711b4142c00704900c1600b02d5400000d4040c0014803040d0710030031031013000003000c0003140d045d51020b40015144500a03130703046020804007140ac1040028a006191805481d48401c01c112480c0c50041040b0107a80d00040740c01603506071407172902c809494418800f80c5140703400c9913280c60319070080030000c002d04802a6240402d144507051300700d104 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 415837338 1250 415836088 415836163
    0x216060504030f080d0504111306180905071206020307020f060103020102070312030e070b180625020d050109030e120a15020c0705030a0503030f0f150d08120405 71
    0x4696510385040e02c2c54940301c810450182c0c0484424504003d080b95113441c031b00940340542c1c05400304040c05444402000a007140814616160b1400c0210800101c018013a500b01d0030758a215010800300c08034600303a800c1240c0c1e60002c0c5400841e22030102e0922006602640c8280e05640072204030503801d07007107a035841c2c0b806d110007030050344011070030b0000400c58042d540c4140d910307040100b92801506043c5041414076040710340401400710311200a4110310b040a1007103031341544c80914101c03040008a20400700051081070b0fa4445003074100864445050b45c0c880140c01100030482d20b015403900901c0c13281048101d0384a0300c60481031110507400410741510013540b04100e10b43d11a0300381e02c488065004101200301c07034007540c200062541c4041c07140d8226948904c018607603906d400c400316803901070041c2c100c1c807298200100300446114105003450480d034044444c030350104940e141c80740c0b0310311580c421060392040e007c0522040120004540c519800c066110281d510098151030045405 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 415838588 1250 415837338 415837349
    0xf150305150103120f090b0304051b010504030c031202031b010608010b040b01121e0606110105160212070c0504060b190806030c011206030602031008010e1218030721030216 76
    0x101042212445e0050040c0c240180c034908003011502e6071109101d0740303034204076810b4640d5044084003c62012401010301010182400c080d82802d0454681c42c10005c0540401010100e0b010b0004424600030000c0e9070f11200c1081400c0d0744580400d00c024049c104ca8818141c0c198203040c0005014585030003500320842c01a9924010040c4850307021002d40303007195041c0b10182ea0002207980f050014007402d00030713204a84921600000c0080c0c85400c4460082c10040c288035907070718444003c3e031301017181e4404410910b207240e2103a80034101910289074aa02603640035140c0900003410004401c0034003089007c0380c4991004001c0c902c0c0589142208403149074ac103030885641c0107410b40c05809150300c0e003109500000b8440c0d40f00d94505c41280d0090b1001440d0340340100e0100006079090041e0070400340a88043c0c09a180440700d044413501032040c9181d0f65241014001d8013646040010074020b00300f17012100c80c0b20752a081000202c5485480940060042d01c82c103030707030010050700c50300126072 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 415839838 1250 415838588 415838603
    0x1722080703030827060a0b1c080f1b01020d1b03060b030106030e030d0e0a0209090a080904050702010207061a0f0303090901090e031318060602010506220f150305150103 74
    0x44e14440000041001d00380d0741c50031403501c8442100640300800c00203200d00d0542c1030000d103682502007009601a10882c008205000e03a140d00800606058141c1d5440c0800103516500ca25090340341c000e1369034550503404e0083d8408034640186500c40d801805040c40782d00c1c001050810013600c214107940450040d00300107a02040104207261103540000d054443c0795003580e0800c0400e0340c1c140700340c6041442061240e070005c106c9100b54600520031640108481005140c682001d0755408418041c040c42207116556500000d00500c0c004e40440c0c500715030108040228170030007000c00c405906c0c1021014041c1841c0001e540207810300104850620720020030302c0000340e107031aa0b400054040300860b000d10740010300803804070703515511180340546518209440d0800700c400c1018211603981d444030f0f04681c1014240103098a86030041d540d054405209800e4a03038a02180c40c01501c00f400030312118034a0010308000c0e0300440c428074020b4a10900940e00615100290111711010a000181859 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 415841088 1250 415839838 415839841
    0x2107021b06070f0b0604021b010605030c030d0c0b06011e080a050c04060203120717070302120a0204050d150e030f03041401110f071104110307201917220807030308 72
    0x1803001c02180e5100f05d00600251070000040e881e504030380c10498040c442a0344a0f4418802031800b806005510030301540200000740380d0940080940c481184041c0850000c00046259030f40f2680203003c01c9254022000f074001d48800300240000c070203c80c40c2c5003075480c10011403690713030744d4404840440c1e1150740207500b450401c03070100c04580e101034109002d103c2074142000c04071100c200d145119107031540380141c48019820300c2c4004800018401e03805c1c40e104000a00540c3d8500a103070f034245402175140805a14a40079035401403400c015685058480800c40d0544030b0b13480001107100d0b9100c0d4440c40c04045400d0745180c03c1c0d03241c1340700c0701800400038008250306000100c050071000c2d000f6484600c4131100352001c00c0c01c40d000d0340700072500f21100204100c2e100d43c106221102c01618004500707090500c81da04036444815990410600004a60703004007413001030b40d20090141200f201e001e5a441050407000001c0b0640844051104d01c078100c00540e59801140c208100c90b0503440b4109503 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 415842338 1250 415841088 415841093
    0x105032103100815041b03080a05180604080a0203190c1503020d0c0302030a05090606010909020d09060e0601080708072303100c052d0703052107021b06070f 69
    0x103a03000140500360b5100d42d5000001d280b8410809145000e101c031313802c5a01030400e4145155862614400a0601c071755940080001610480031607100d80076a24000d0b48541038026154201040c6003440350b401040410701048511000c07031280340b014400c0f81100c40c0c2050250382110003510700c810141406042d00410821090b40500c0d0070a0265585001403030502c805c000d1004683e0043d0f0a08000380d40030040140416451140940066211004000e1b034034110303000801d0301c2d480d802400c0301d403500441c882507020340c141c100701c10899126800f0311043c0d8218440d10b44c1e5500074490b00404e84540500024640760105d220703004c0d140c1d0324882c0300142c5a01810901c9007851041d85d42c5e050700c20346510303189044680c07054010104d0181d4406694075180b2400241d007122408003100008415080b403514048407804980d10740354141007007a240d240d441c1810417809941040b04064511000c20004820b60214400155401d001911001c00081009101e824007400c58024001c8020410341d801 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 415843588 1250 415842338 415842403
    0xc0e0a06091109040e0a0807080310060c0530030a020d0b0a060207060f30061401200111030405010c023304080d0c03090506221403090d030806010305010503 69
    0x1100d81c3e06034101c5681d1b2507240e542c0e10543d80900007e50780070300040103201da004c070010b9840e8024001480c0c0740c0750101807503d449440321944c156641a100c02c05a0300c401c2203000301c2004040d4002c00180079128a40f465186000e5804450346680c014600780c03540c0910302d8801224410358245900030011035043c140d0645880300f00075407210601661101d00c110100c40c80e94044845401c0443c004602c045a03044031080d50b01c43d820104982d0300141882c030069038800000e07034550310303c500d52030310309510720940a0040605004641c46550300004000911005400600c9a51019801c03600f0048102c00764070b1721812151200f500c500496908002811171101099030024090038446240582c0c205110080303c00318140341000c6610b803030b04201170040500241d40d102034509110f03001400c0c034601c40b0151005404004000201c50400341c81800383c108190b8000d000041d00c040301003240360801500c001c0085032601d00103130a0200128035410040b46e04803030300d40381007440020707900020032094 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 415844838 1250 415843588 415843601
    0xa14010312120b06070f151e02031b0c03030129030c18031906060b0a0509190504050411190602061303020c27070e0f09130c0e0a0609110904 62
    0x1c4495858071800d0000e551351400400501e4441c02c0315103142000d900d408100360704c078044444980e52500903450410001d000c180c105644d0041e400507501d03550010311001d00c0d46d498000e0b501885002c00c2c40a9041e5002000714161003a041000340101d46854583c4401700c5618100b004100c0180301188205502401412003190050501a10041e1410100e8a001c0c0031450503518286000400340900400c1e200d130340041c182b5000210300d05503001102402e20b00c00c13400c0360742c040c241c4da0f5a9031610994071080d08000c4e20000b070050101e402c2900306040850303281310265100388266454030640701c141d440c0c4481111565009484243d0307804440f040d10840b044005c0c0c00b540200c55000b911556607400c251350640310208100c1410040120b0700c1020031004100c5818418500c80c010115a00c2c28104002d008048511980682e00e42c44144078403100208010000442200c0125200c205031103694480c034688441049182d582c0c45610044d40c594481c50200d0080412455415040682080 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 415846088 1250 415844838 415844867
    0x504060f0c02181e06090c07020d060216030f050a0914030106080102070807110109080a240c0e03060c070305070204022d0901090b1c0507090f0602060a14010312 71
    0x4881104440d0003203101465662800461141c0d0340d41040b070354039800a818590500c001d203200b24146085c602040040d000a05051159503001c1a40002c555941c0d04c0902402d03400101551101640425003410080408044020031840c00e44061224441e10960b503404e90b26a80fa044183e181050040103014a03115080e015501c0310400f182d00d103001d00060911318410307110366503035075500e06251003d240044951742c10007007031034410400c641c40001ca207400b00790081d6400c1c610352045201840042d2270701d100a4422800c003183d1032086608000081e001e164207030243c0d1010b98031038842c150f00307100750b58006010504c1408041e001d814940d026004142c00606604441c6a008102003041c20720111004d22a6400060281d5a03580c4101044001c00070500c81c68105030048002d0400c5031460b61401012542c0c1e8000141464030a44501c2d0040090001c400501d81c1c40e036600940f5907500303d541c0300081c0d0618103048008200c110f5118102c81c0c210b040c0380304082c0086011641041a00c2d60b4 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 415847338 1250 415846088 415846097
    0xb0c0312040606080f1b06030106080a05090114070203090109060302040b07060e15010e011406030105060d0b0411030c0a0809060c091905040f0b030d0c110f1203030106052205010504060f 82
    0x410342d130740200b00d0103110101100052a400c05030307803409444010391340f0605016100a0004003c0301e500121419045241c000300481c9550b200300e1580d006041440d201880b04840000b40008140c01100a048002c004ea0b2910181d540b2403000754246d100d184141c050101c0b00700100d0002c94401e0b40030006000c174220a07035041c4081c520403c0c103c44002c0e0003921825283e8001080740c06226020482c4c040b800361081811580352000040c8540140214001e4680c0c13602c0c4480b86680d6140c1c08407c48189009406032281020914022181c02018001d40070986600204d0445030000905621070710001c51441d10b001c2540c02444803454410081c0b00700c04000e404040b0b404d9442c1d00070743c10058030540c0300003102c0741607034101403400441a0303880b028405111071000c08240300701480850044195051001000d119003c01c0108081e40564001c03130001000100c0d01c039500c00000c15260820308100484181c5a03200000084100e00c900d60218000708001c101003801910b20100170b003071a040 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 415848588 1250 415847338 415847351
    0x5070216060c08040305010f0e0f060106020703080f0910030b100c02030601032a09140a09022d04110c0601150807030b01110a03081902210402040e0f06040c0b0c03120406 75
    0x51b840c1c01d46070740c50801d800707441c1c07107200c1880000b008014148603851003034014207036941341c110040e4683c24280000392191000107014510380c8582e00880301040e00192204044c074004c003c0090040c004d1070f100d0f510480300200300d030128621031016811001d80041c058442d913480c5680360012250481c2c1104516480c0c013a0007210f1006c0300101170010000c0329408a45030000c5282114051030080283c0100d41c54001848050388071420008040c90150800080010400445005508810000a82c02404c0922403180d0911450240c80d1a2001030102d0310aa600e41c68514480000c10701c1490006800e100020304503846a04181c20090041c103061049001c888030481c28203986d2a0f090740030030600003e100c5140c845040f030f88001e0344914000c40c01d2107400348000d141424148003e010f00d08032040403409668695221425601e68031084619511044070610b0315101d080303d050720b00704040500010078000303100441700403109510156180c1305020a454914040140007960655038812 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 415849838 1250 415848588 415848593
    0x9041110020708011521060204080714040f0b100c0201030603080304030807021b010f050c191208090303040b060d3801050a060e1302071703070305070216060c080403 73
    0x400d2040000d203140d000d442050300701550709013134030003120058404503c40c07481080001e02d45443c0411a1206081407500b0124030705013138020340240e4100f66114081d03840d00040c0b000599007131360105a000c0d01c0500600b0b08980c0524221031001503240e170030460250341407400c14070500101014900c1410002005911b0b51500481e540040311704401046040341801070b060b80400020401102c03101d918401280018002450f42800c2a1148144600480c5d8090b00510034009580c102459001c400f00034043d500301200d24040c0c1c03050301d03c040350070300b40864504040072045910507a0442e00f00c26451300c1c2d10303080c822101e4281c0004c0c0d41c1d410b80b40c405c1c081046030041c400d00d04014a401c0e40d80001d24190381c41d9038800d0042c2d2085126814184080244680000841c00c4510b0100d1300a03165084025941003c0e08c5030420080c910400740710400700307031145100510b00504aa55082120303076201901660390380f01c01390f441c1c030005e8aa0001080784a1103040b00200c8107100746111400c0c981d69a = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 415851088 1250 415849838 415849849
    0x1111903030f05090604021309030302041e0612050124020a05011a0f0a0302030d1407140d030c110a1106070524060907091503060b030a05070305090c0609090411 71
    0x9860440c00a40c544421600e40485806502d4011099101810f000d0803da400a00c1c00741301a100840d030306844080c05010706001e9419600244403101d0090321440c0310120f401419825800b4501c042001e45442130145030813803084605071201403200d594281d02c007074449003001e080c10004c2402c40c400c124420000800c203000304020169007102440c115064001008010703500404101d004aa003000100003607079000810720812003813410a200c0070a01000c52a200d40304404000e03040c08400550785030720b40c40c00030744040318001c256820002c0101e4030f0800c07a03841d03180c0a40300c40c8541c02046000045408011003c501043c02062540fa02d00d5940d6058204480380020229403072501d010009441103484100358003440032034051805241400b8040c080e4101c2d402107404803882400412086030007944005c014040d2103509a8403427502c0390700c038400b030002102e00d600000e0600010910404000030200d20b01c01703000344141d0030209c00f0814800203240003030080e0b0b100c2014a6049442d5101c5 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 415852338 1250 415851088 415851133
    0x20d060b070f140f1203130212150c03060f22060b0706050916060f0c06060803280507110a030803092506090303210c02031b030304050703020111 64
    0x9803002e01084985051118000200c6108407080b500140c4110340580c1c00481c202245e584200e0b5141d13100c2e16101c03044142e00b019600000d4111003128642e40b041000094180340714000c2c080c0095180c0d86980131000b803800282e8405030403003840c2e044082903203894440c4410154072803001ea628108514003403003d844a641c010a4847d40006a540034130880d40665035100d42040f00030705c101000b020035682c06000303902c240741c00c10901c1c00851480034402d400c8014015007200c0c062041e203464030440ca403aa40405220000e0385141038510119146014a0f403101d4595a280c8a04100c65500e81101c10380500c3d00265000005000100006041c01c000d0740c02600688000c101d52407803020301d481f40b0000080c0803201040c000e0f004100056100806005807a4103140c04480320310204550b21407091145030307141d18541046061301d81d440c0c0c004083d00100b0309071031000c499100340306802c0d40c0b41e10041e14060002c3c0c100c80c00c140050b5014442181400c42c0c504121404100c81503d048030f244107 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 415853588 1250 415852338 415852343
    0x80a0b061303020102071a0324040f0e0606010801080607050d24030b0c0702091b190e1005070c090509030f03040b040b15010c030f050903010501030804080105011e0504020d060b07 79
    0xc1c1c1150502c15960304201003400303481e01e1140344104d070403030b402c900400d400020661152810284840e803010048002c001103010320250082c00100801424107024003481c2440460510600b0002801503109140540c104c500a60142c891512a0803040b24541c1c803440740080d040384c8030008182c092400e8054091601c01d4a00b21006c0c0a007185003044c6620340140c8500f001560501000e00942d0381d81c04441d800608242d00c0300c10005801034245001e0080007101e00e6924108107410125680001c07000440c4502150054418110b4041c161118040e40102802e540744241007400305500c942c1c0501c0d003001d8240c04590030a02d6110211500d9801224101c4a00f00f2031070a2008014020300210f80000c0954814994880b00100092001181000c050200100000c0b0100c115010b4003c451010001500a000c59a142c0c1000421a441803107440b400350318202c00018011503e0f03010309000d407100c06000492903d80020000a504445050b05005a0780c50000407588081802054a40d1 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 415854838 1250 415853588 415853617
    0x2062a031905030c040605070309030b0a05040507060c0f1707200109050d0803070815030a08091c170a030f050a09060b01052505010902030d020a1e0210080a0b06 71
    0x40c10124941c0c82242410145824008240140305808541d4000d031000c2d41c00d6440c01a407a100d503811708941150b0160b001901e4140082c0070310494440ba80c10861084d8082c800f00c9804c40d03a1600304445c20402c032000540014000d50b100000101649011034042e2424404681024590b45440c10000c108159502048190000800d0076581050360000202012600c450040d032032900e410809100003003003d0308001448000940380304c0a000856aa980050300701e6544426034500320405a0102d491680300d600c040a150302d91130440111004901d42c49010041c100c4010360004039542c0160203000c0a05849210111412440c0c0c4601441003209500200c0c100f02d203070400204482e4494200d40c10090100021309440b40c09011480c46c010f4031540c403001000c030714100701d03004260204000790315014600e8180380895001441d000c6d013501501541001060070f10150144060701c08009400c03d0a800402c41e1aa02688189511600004003c03c850b1750100c00540707180c0c05800a0010319 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 415856088 1250 415854838 415854847
    0x7051e07171c180210030510030602040801060602160308091012050f0f0718140f0402070b0718030f0201140706050c13080f190f0c060305060f04140402062a03 70
    0x48028010f601c00a40c40c2d41200c84128402e4001c51844d0004039600020b050321800071890101c41e12056030025074107d030f02192220385079420b15010780114401c510041c4122900030302001e2400d5420401c0340c1d8000011498a8104400d00030804c004039002c8041c88940c1c000b07030b00e03211054050148240d80c02c800c07007905494003c0f955a581c40000c0d024a0810100c0316030750307110100301c1d00780800751140c203035401c1105181100000d00140c1142209504240042012820001071408040c05250651a42a412940d00c0140c1041c28030500c4054200c066800b802005035014014000f8040d542c503024a06d46695a00c070101a0360083d540c08a038200001284003045104c040e52030043d00c03000000d821209000a60aa500c8100008440500f09410461400c02c000280c076a402154000d400b010410f43e18000a8024081103600c18080d400780b4032000e90a03d00341c491058002078040c0e82c860940c44507000d215a039048002c44a2070003d0920320607440e02420041c10084481c00741c000c0d60348 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 415857338 1250 415856088 415856137
    0x150c070b01060f02060604050603071e090b1e0603060d0813080c0a080703230615010207050108040201050307112e140412030207080f04090b040507051e0717 69
    0x2000c050740040300304800300418062031540481c4180d008041140e011500b03481d410002402c2c64051b6000705c01c0900380c40c920141300003000e0030b040203c2e55103203001c000c82000765080c0303d1105600b03a038a05a1a19100010b034562078503201454001002801c0400e06a83c51f0399005207a91242034040000789040c03104024402c0200481d0440380000d49080004a1500090a94402e8036010003440004580840b05100012140b8903503652110401c5a0319403c0c001148141c01081051280c01405240c42c0442c20f0350180004500555040e50380d11701d560756032602202c0400080c032816015010f000b00f94210401010310003880d0006050682001e03c928216450454180c1c03400000c5240030703501048041240c814059003221900d080c00350717980301c403880c10021078031801506640301d100c08200402e0302841c2c3c0d4130010100d07400303842c1040152101030054445001e4100000b02c10007a9074030341c40d1445410800fa090013880386800180102c1c0424030709403141c1024961083c42c5420720180c00c1c1c0d = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 415858588 1250 415857338 415857353
    0x6060902120a0b030307020105031e0403170a1506120605042301051c0b070c0f030e01020d080c04090c0e0301060b1306090e0c09030a02031518070807120203150c07 72
    0x20490b022640c10809035003100f002ca03860340184000603041c4100880060022508404101d40040541070207844500c0c141c94054401481030b03038450320070481100000c141280b94804d001d00300788644c484807400c03032074100d0850340d142e003111000d552103807141c900041e29103e601603114958501c2d44101c600c81040c0f29480d00d07524059001600c109100c44008d010192b81b07201d030038021a0030a00244140d030315102c0545042e00300000042c11114010030303142c24590700c400c03910b4895401341c2c25110849152102111010710980354021182c004000800100c0c00e182e1010000e01014102000282c2004d000a402c5a20a500c820481c20000801d2040034581c458100e0180c069420200c08482c2440f0082c1100d003001408814401c0c800600d5840c0c9a800300101c20200b6401003c0310368503a402d080d02d000030f41096550603610300c0c4880b410a44980c01007207603001d403a0403074000c25119141c101145450a4a1403060342c050064024510007100503111a80c03003201d4007075201c2d5496038180390209 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 415859838 1250 415858588 415858591
    0x90c0e091005040e0318040209011713020f041a090711010e010e070f0305030307051308010509010f0b010306050105120a150602030403021c020f090703061502010e0c01020a0b010b0a0203070606090212 88
    0x8560406c02c8100207445640c6030303480c0f040600341c40068403480170310016141da11100c2c0c071400c0c1400300071003084036003015a050500124403e485202c6800080824007040d42c072000201400310901038030040881c180b0425982e44900319241001140317203415020390840d00110380d0001941d4503a09091400e030000c00445d001002c0c0030702541c82261540d104c2030384900008c2e0260341041000102406070440c82610000a006c00320300030425420051141c074020480c1450480c9406d041124141181d03002e84191412620103031155031404031b0b071110a00c0840c400a0142c50003950300c1100c11400c81c9400700100c05003c00c1e40042d81c0d46c5086004219981110180b141502c06459000c00010303100c10700700b541503040540700180e00b40c4a4201c140c028048941140e0209400d0713030000480c080c3e05402c03440400c90354200b9908030380822801240c4031204c8880c050035007104800100403600609009115450040c816a4200000c0341d07107640940d400c0e80e014101c000d80124080e04800b20304004a03 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 415861088 1250 415859838 415859861
    0x406020f042c24010903020402190305091b090612011b0306300f05030d060e010b0313230a0b0702190c05010e0a0e0c070c0b07020a090c0e09100504 65
    0x10207285084800a4039110140d940a90809484420a012130740a000440d01450340100199210501405110791506061b40d0010000b420705000c5408400040b810416071424050800b0b51401c264044c80b900d180050205600045044e80707030301103002c003071081d131042c6101d84440350f01c0340d14001ca0042c21b540780e50300031520b00200d1000d081c00000352020034207100004182101101c220f40c0c14104d2001030818405400d038000066a4080002143e00180a5500b40182406c40b82d0f01c40d5550b0712103010031500c0c215021036902030f81c0c010a41050441d904070294022000d111008840c010f801e00d54030b1181140c500d04420288590aa0140f1154074840d07014039290702ca4030400d4940c0c5541c00b150340701d12810321640b10401350391074817610341c0c40018040c0c04101c2c0440d4280304610310344a030310492080e58180c41d04070010920b68038901c103c3c1c07081030300240138041c45c2e0304010016009100c600903090034880c24400e0450b0b5a110888080d109410040c515201d052518080c001034448103400c0c07 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 415862338 1250 415861088 415861169
    0xe090607020f070e04020d1b091109030c01030e2e0e06060d030f091a0c070b042403090b0f0403020c0102121b070819050d030207050a0b0406020f04 65
    0x500110740400140382080396581041105651031780d00110700021002035020300f509203c152800407001d0401511030898050500030000d0007420742c110780c054007403291459810f4020111650140d07100b42c101c000803804000a8032742c01844981c3d181110304449600c00100e1f80074440d5580381e91010311036000f903420320b00080c160360302e06030000460042c0202c4006050115040d00c078816240700c2d070807180c050640d004480690b00000d0031034250682050b1070368200f610584901088500254054408a43d450914002c03210100301e44185061400c190f20800c2555540501021800c0e4071140360243e201c940440a1504160130002d0400304202000c0d41503601030000703003001c40e111400719a184280201c688142450001046040c004282c1c071450480c4a64100010391a04026000800b94410001c480c1c5142c00b0480c16001c4c1d0051000190880d003003502c04002080c185070fa001d40c02841840300600e001911640840243c1154000344542e045640300c0c01e0b42684011910982280644007 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 415863588 1250 415862338 415862353
    0x20112020306011211090a060203070528060218131505030304120201030906110403150506030d120203100e0a0606080a0b030601121104050c090420030610090f0e09060702 75
    0x18200c4802024052070302c1c5e81d01d207084405403608030180e40107090000c110744000c03640c86000a50340d4101740b17401e490901480341980342020342c400428030506d2246050f03458400c016201c0304025005540413081c201044e05145940f981e92001e0441c01c0400117800080c0300810041c60702400c411078100a009030700411084c0685440045001902a8246004100340910703203840c0c4060841c82c1c7d1090000e500204004c030030044104044020307a9039040041005a8514003015a03407111819400701088000f80781c040450030b507070000c5130b0040800b00c80c440e826903a11042c2040d0141101c0801003aa9a00410701c01030740c0c400c800d1504032801ca1414086041d07994001381c0c9942042c401c280340b032040c00e08400e040001851300203011b1070004104016074900110700f10540d0b03102c0d4080d20301c120f14140c1520b019045480100c28401c2c0e4940066080d0369480c400e000307580301040d042000788112a0800206000b11a842601401c45011010010f08284a00c18038208002c0d100c2c40070f5400468 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 415864838 1250 415863588 415863601
    0xa09140a05090613142d072f071502070e0c04120302190303020a140c0706030c091701020d060b031e060d080d0501050f060a1205070e09070c0201120203 67
    0x40b100c54210f0b40888004000c02d04080c640c000510400702c90f4610301070080104414400d04607035214030015107540e2440d2131100c81e280c16100c00d10840342034000c10032044264410328140c25540030103002a09142c0d20244030101014034003c1154400886c00030200c500210855050003100010074444140280e103007000b00c86000c4501503405402003101e505105103080c18400c2001611240c03000c00f440d00e810100e420020082c0d4808500b61021401e05501180c5020312201110500301e800000384c40c4840c20800224007038907050b40e80c031003001100480860b034070100a02c40107000000c2d02c00140d4030086c00600405445c2130b540400104001402005041a000c80140c64202054032264500d69a10300006044042d1a1005845400302268866458481d54003a506a0700304a0300d554030008a0001c00c402c900c5920400720004110b00a10303134141c003042d0050398002000e4207109000c0620200454003a4508851b000b00040c0d58024500642d41c03c203c80c1003032071000303440a51841c40e140 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 415866088 1250 415864838 415864849
    0xd0e07050a0b0a140d1401060306150908060a0906060503070605041d07050f0708130b03071d03031218010222060e010516030311031008160521120a09140a05 69
    0x15444014080c100180b0203600c2c0d4950b43c80306d5858030508002d40c4542d6194080100201594000c000704003403084e0b81c1c83d9442e40124840e000311482c1000502c480e503103c0400303401420301d0f81c50880b081070f00c0d0390011401d07a40a200c104090151a038880c1d4a5514120341e46c090068110307841c214443d13003003052043c1242d10404460844607200d0126540c0d044500c1d10001c00d1044088181c095040c0e10804141c540322a40150b0191070700f60350342500700f1400d0003070f40ca01d15a03208902d07a160303000708400c003482501209650360100a03c03c80c40102c0211020040c266809220018a0083d82480c12420120380c4000c0402401c0c1619240940b1690a4000390082c80b4400071000b046007074182c0c4104043c0f10350480d001103a046074080e501d90404001d40310403e4002d014400090094140b03950b803500400c01080100c440c000e10003c2e41001030f616840320f501d1110941c4045000e001c509100075440480100304161446c0d88002d10b803440e0002425228500544151060b04207090420181c0e0301c4 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 415867338 1250 415866088 415866107
    0x3060a0c05070f050f1f0c0305070e04230a02041e060f1d030a060c2a0206032508150405091002090a091e05090303071b0204020d0e07050a0b0a 63
    0x1030000e601d40f00d02d0741803851808040c80b1626845109092807091806c601c0f805a42c954008a4010301c1412084503042e0240d6004171001000241c1407041d00b0a070340f030b00d03070442d840301d1018682105140705128500120030500b00d82e0a20415000102000078491f11003d5007281c0c1400010046c049080c10001005d031205043d019042050600c04540d41c00004040304504400007001c582c0d0006162600c00007070440b14507a4004035503000504141007003c6401d00c8200100a00c01d809910b005508000007608003070400c004507809001150910703020309025030350341a92629160310b10b151244030410b440e01d1141e60780740110300f0841800030a00d000a08840c030700c1c09108001d42c596010f00003140801039a9403004403014144146030781c82407102410001002080f59041c01207035103103521075540c6d100603141b50000502800700384a484181d201c654420610052001d840c1c60800700b0f900b002c1e54411000101c00c3e0304284002c0000e4600704c0301c00c80080c025412102e091046032140034091520 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 415868588 1250 415867338 415867343
    0x6120b0907060c05121b1504030206011203020307080a090f030602030f010b0702030a030c11060d0e0601080c0603010608042303090306060406051018080616090b130b0c0f03030a0b03060a0c0507 85
    0x1804100c915926440713061030129034444d0001c5951f09902460b0701d81149400b55802d82c0035008038400452038048501500e40c44c039426030004c2d0b1601440d60f5428110754480d07014001001054800414403600104141000350700440000da20f034209251390002c1008103030b2251020100030448000181c402040300a0710703a4141c1008052410541400c0c0604080212000e602450002d580d010300c088a6021450b00703603c48048952507a00c41d8203441d540c24400004542c40305d81800100300603842112055481485100c0c414031400c403000140b40300407072402c00c044150304081003035076070390030304108080d4400b1089500340304075440d00b03010400000911401508100440d0f51031804030b002c10031500020a00324048402c285080b60002c1c10800c0149901d100245541200160410051003607a82a054013440c1180309482c007540d00946a20020382503105000310110628118000d101030f5104400b14100400c00c1b4112408050030004028810740310940b40c50040c0d040c0c1c540c07206c10348038004d5 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 415869838 1250 415868588 415868623
    0xb0402070c0504090c0b03070314060609031c021609021c1406040903020c031605030d0503091c11010608070618030506041b170d0909050609160306120b0907060c05 72
    0x3001d42410106041705406c4040300c980d0020a00c2540380c1d00d507000207168030800c54000469161001000b1a45c49000c60b0b05916a01c940d10000002a20820010700d40507940102c810b04c08942c106007580b10646d500402003507a022401c2500380d154401e024a840440030810004d00e14007a0b640c401356000030f40780c2030045540d60181801c150003080391a508941c002c00f00d071a030305000d0000d281c41c40d2080c05085d001c1e008005040c40424050029a401004400b01808500307040c01c01c010702410075002d45000300b110081102502c00b80078460903014140410207050784074181032001e4281501114001260410b140303041000c40c00220781c1c43c0d00180e0003e4075941d4650a061001c081010940210032155008140caa20300f0800145034564101d941c0c44810045507074280c00b001b118811070b80a90490080000103240044a402007204051203090000f48907031074101106e036040000324100d41140c0c0e1001400200c0701b00308481002401c0a1503c180558241d40d40c0507141e03201c19440803080d0 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 415871088 1250 415869838 415869851
    0xe06060109180b130504030e011e0305040305271009120204051008070b0c010c09120b040501021b030405040e06040c0e040f02133306053a0b0402070c0504 68
    0x10440c640009140e04001082d403002c10070031041c0d0700005d10055404401081d0900c44904507940668010807018920795100d950140e04c0503405d601800c1c00601c100c080120420072481003c08150108020782c0711200707900303d8610f2001c280044140b0a00106003444240c0d00308010b44041900b040125550554010480d42c030303803107801c182c40140d80c1c006244078060398402080c0f54281d5006407648801c450000c1c0004c02d0120f0068901d61090701440e0800b00016500c1c5001c100c5c44207030190440e225000041c83d28559840c444031a284c4445000031540000030304002d58941406421303140040c0030701414190515a45d2030701d1601340c910814001d03001c080001414006000004884990058803144d195210510218001e0041080c607141c2d11000c09a100d09030440c5160407100c1181d00da03c4403151a040c6841524541c02143d004a8600000078109602140c0d0000104840001000c6650030092896280068032240b1040a002e1841801000003050711000d48070201c50f82502d00103030302c = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 415872338 1250 415871088 415871129
    0x40e03030a3e190507030e010806150a0e030610030311031801081008011b08160518030717030705060a05240607051515150304020603060d1704090e06060109 69
    0x2e500484034000101803103012480846074000008009803846940c6007040e135601c0e0310064644610a846c610381110f06801060384501030b940003000e0701040b80c00d1000c030344000800006d10705032040b190700d000d88810400800030160420020300f04d07800c54002841c10301d0780007400500070008070003595040080f01d02c00300f4003404410f8905030180000340000e11207840d543c062170240300300c0280c042c0700080d0340c580007034486c0740c0e82e0b08c071050041c4640d91078616200440c0d02c031052401025002a07418003d10000180c40c00e0162001e801d190820030155807592043d040c0541442c0000709540303401400d05041040011010603c0f00070105030317040c00c003a0a251100802c040740501e0200408034420800340b0421595400d80541c031a2660a1450015400c0c0c0000c1c801d000384490b02e00301082d541807010800518261000d143c1c00351300501001c1c48800c4c3c545548541d4208178003e1444820300280c2030000203498043e141d82134460700c00410703690400d5400200a0029403103110350422000d02a580c9 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 415873588 1250 415872338 415872461
    0x20109080a11101706040f0609021201051f0c0209100914040210021603060506040e0d0e0a1202130e01062c070207030b040818040e03030a 61
    0x9051800100c400c54540c030301c0e1514450300150760700b510408090003810f420724800c40e41c14004004494800d203e03078440764180703c0680540d882011060340c8400e000300c0d960740c072031000e00300002d1040c0034042c541d49020140a81012414950191181e200c013966841f56040350800c0080c0da419102a40700d85c0da8054100c81031071980d000100800c0c20403100c001241c1030391140c14003460081b50b204100b40030515050f6652010002048180d842c41001000031070450b610207030303020300080d102180c017121a0b501141020348070010f800c04121890740e1202282880015034014020280d10114190b149800084e040480420708000841d220031684108542c01e40110000b8045080f01c0024642c02c41c0545000c075413404210a07a008185001450580c400a02d000c02c407604680d9864003916a0b88404d245030b40b290a40707005001081001c0d910319222889200d464116440c059a01c9050100d0160182c50708601005948403c0890014044e402207a01400724541d51420786151442103440d40c0c0d = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 415874838 1250 415873588 415873607
    0x702090106111504050c0f030f120f0f03010816080d050910030b09011202030114010b040b130503030d0207052b200a03021e010908040302060a0c0f14010b03031c090201 74
    0x84000f482e040c14081000400201012514401ca5a0424580000d0103150352050b50b442c030003d07190701880b085506100144001e00100c0d038a1200a8548403180307076020460303442a400300c040c40e403000310444030030744059155801412402c030140c401011070503802000c500070001124401c0ca002c2c50302d0300b21540254001d4003d40e80203403040c0040d6035907001070b040400f102e01c000e034040d50030007005515a100c0300c40b85e01e0585000442050a160500030011441e4000c1114081d80202c511000b007282e590400c040c154052208201580e0341045107841410003854242c42d0003007041100c0e00c181d40c50844002502100200e01c0c3c48a25802402043da807001406090744803180915002001815400726000c0c510351402401200c0030685010360b2070803202c2c9242c0c040c00521082c4420700040c5000c00c01040a5000c6103044101c49400351a003600c84000ca100440f00d070b0300c0030042407038100300a02808040400880145040092a0042140c48400c100d02d40500541c7d6401c5c00c0d04581c00741c1d0411 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 415876088 1250 415874838 415874863
    0x3081909140303091e151b040b04150201150501120213030f030e030d0512040305120901090b010f0b030c09040917040306060b040506121902070c0e010506070209010611 74
    0x4004401c01414035a0301ca910580e904051030080001050115101c40b442064682c0c155000f4070341d8804880c0d01c40c0c80f043d4090b0480105a4010041e81f0701b22a4020140002d4002450ba60750b0b08d61038540302e030750402008180c07802503905181a00b00700d0310788011000c1c119002803d280086031140c041c1e0308000d03c540c2602244441080c50302200b8840009024801789109450741145d401c01c20003010750300c8503103072850400500104005112890b0709102d29401c2846410600e05003070344201c01c4160148220340b05034440c0e558030662001d0001c0c0503015030040c507120025680c440d0400e590b00d10103210040c01e500b059000010f14900c203486a6202c00310507070300310907640303c130408200e55030159603c81d03c81030310010b00f05000800c4544c9900c00700d80c1110f100400f441e14050010740303100b0b01240c000b44a001d0721a0740303500c042504e50184c0000c0c205688070340741e000d038054101446041344440607040140106c2d01030124600586034240c9440c1901d02c0c500b4810707101200081d2191800c141007a40 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 415877338 1250 415876088 415876103
    0x6290a030b0f0301180c051903062a0806030d0801060e1203070c030804170102191101060f06090f090b06070b090307020d06020301051c0507121a042d03081909 70
    0x150300500000701c0d41c00c4a20480114015550710402c0111005c8c541c03501c401200402c0c1020800503440e03a11507400e0f4a500c0c0c1d181010900f40401424401c00c1e5a00f0340d90205d00302c001040481d240520640742a408603040c01a000e50410a004058035480410076000320280e03590b210000604000b91050035502203003040b0029140c1c0340c004000d40103841000741a1183d01400c200ca900103009907404000901f0016261100310003080b1511465408828615580d8941c00300b0207143d49411000a000c41d500c1c1c1142e0280f40c0088c0c842111500c0c4e00c441c00e00f51400c18000354030342d01c5404880185411000c802106e45400c0026410b521a92400130350241c4024121400c008407500a14101c45c0d003281d0080c03203c01405103015400800c400000c0c510307040f06000344107c211036230084800318001d4992000e01650a080440c1c14001581e007a20818440941c500401c19062041204503405501e54005402944e4000e4010310000c1c000c4031801c010040c0304207000ea45548065401c90300720b000d = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 415878588 1250 415877338 415877351
    0x4060e07020a1a0903090409150903020c030c011422080604030e0a050402130513180c140604030c090c05220303090b07051b1504080106290a030b0f0301 67
    0x4000e542c481111104882c0e0b40140c036021809500b03005400c03403081a515001d0740c549403510b4100f00041041c4070703080310b8802c1c85605030501d0400d18401c41c200244690000c03c804136081c0109450101d900c08014104181240d40c10f480026000c01e84502040c886051161504d903003180c60941051908030154921032203003084141070380012000c0042e6410307100d40a4840d21803061000703038800c06c4110620b14a865204125038242511407005500e20f00d0400599540a1a030030345081d001902c096400200281040c81000200c0455018040040f150f052526245a4500d090090b01f881a000d680340c0e43c103114050503015100303c030f00c0c0b0300785001500703e14100c81d44883c0500040d4001540010000100440c071407904c01d044480841c0c0250041103010040840400c0e840240b608141e009400c09803d503400d00c529a024001602d0000c001203106070402d40182c140b18a5502c41d1042540591581c1001c0c1600900719041a1898500440d0700c44040d40414000d000d030300e19081c0c02d0f620701070 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 415879838 1250 415878588 415878601
    0xb090405060613020c030a0f0207051003021803071a0304020a15030207030e0a06020709090f02040236010e040c020f1209120a2409020306010603050403030b0414130204060e 76
    0xa503051180004503091202d03d1408540d450890054070103078401c6600403c58282d00d5400ba40000300c0308100c0e1310440720415110000315801407404050000442c0d00030610341c00c411200c20740c00104e0034040d0300070701315507150051950040c0c007000c1440085810000c08034055488007034424000d4030754205c0c00c590400440400500951042d2805c1d000200030036001c4d080c0f0720b8001c81917001c85503654010b142e0741d42091100342c01444500030880c6c189030071704e59000046e02e46002414840012034849400034811969012940c1001c1a4071080022a42c0c64840c4583c0c1200c050502080203075000110101040d8003a0700d810868141c400382d511501c4201148000310301d00415840400b9141c004400300030403113099840b91580c4000308070280403034103418800481c0900214803071550348003242800c0103030042402c200003030f041000080c0c0c44c1c0040000303164042c011004461000d940c101310303d14002036aa0b103400400b600c0208003a840030320410966441340c102d203015003c2c43d0710f0240c80d0305018 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 415881088 1250 415879838 415879843
    0x20c06010320090c27040c021606030212040803150904140111030112141009110a450204080c010f0f02150c040314060406150b04030609060b090405 65
    0x165964802c41510328409007030034800e4480f401020007045803824103040c0b03458040398100c2c41c400d00d0180d0322041d5514403580c1c3c5a0052204c842c1654006e4103a203036811048401502d865081001070500400030401c08030f0080c40e1190340942c01240300ca0b160340b24503c0c4450364200a0b1030199010300c03480309020911000d8403400070000110002003203485110b841c8103440303000912422a4901e0304159034000b18401d55084c1d4020790214081e00c80b00c400302c0161608980303500400750340011ba20136884d10703e824011841805000200070a001010504c00382200d440c504c141c210311200c40c81840e6a0070352802d1a60031030080482d14055407100c0d11038820503a103540e032040e0280060800d0075840559405408409400d5500b42c0c0500041040c094041c0b40b650350241044540440410000010a501c00316101d01001c03103501502ca1414141028020380710400075071011814a88001c00c46c3e0081d40c000c5a00b141ea00c11004a40d40c009810700800801364100202e07040603c001c00c210400001 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 415882338 1250 415881088 415881113
    0x604031206030b1e06030d0c0f020d020603070206150105070809010e0103290420030130060c02010606020313140f030109030f11030a2f010c11011802010207030305030a020c060103 79
    0x110030000800d40d5a44e000c00d560740b2030300c47c03260000c110402c5501003c9816808100c560a001908d9002c841d0381d05e6000c96907941c0100c902c000140c10034010702209007140317910601030748801d280883c10450b664440005600c120b580e6103050103a60325080c2140e900a030088080490322140784034a04500c000090a590010400b0906c204c3c03500401c403090900079072803480080698080d00e070030b42c1c0c01c000d0000390348007034250035060700d005546505040303546500010f1641e510400010580082c0c4860203400d40312550407a50075500f040c05402c1802128161600c1107921162000001c8011480030403498070050704529015402c101d0ba2a05164011065122480903596500c1d002104550116200c0c00f520034034400040211035620f030514032940009003035000e007200403c0c00ca58122116800c403114407407204049004204091f46280c8203114030301e18842c50f4101064800502d0340001d44854180c0402000d00001202044c2c1e40000c0d5030640d0700c41501c40c0c003100c903156102d04000d10354080 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 415883588 1250 415882338 415882381
    0xf0f0f020702032404082b0606081303021b0a030210030e0601060306030b010909140708070510080c091002070b0f090a0b19030203150a0e070f02060106020604031206030b 75
    0x10000311900010100e00c80f21307861001d00d2518143c60b16141d4503542c69500040c00d8503c0500707001181c0704003001103442846c3d00505281c00040d010315202c0081d01d003038030003410202172914154203240800d4001c60100b00c0c00c107032004464005200f240014a60664540010350040c4807032038a14000d40d01640403490303400e02c0808440084e03036114402c9003a00c159010040c2001c2102004100d8804140c000307080340d9120303c0181001034078182e00c103468a142940403604a0b070100500300150b081c0104080b40c03484051038140003d11b403002d800d00c858890f48244a003c4e01c1740800c0c20034118424040d5001400e0148a0180c0d16540240e0341d04503608400740031031050148220000d0307030600c0881200e031441c450700300d001d10b0400450380603402504000d04021030703161600801640c039a00ea0a181014004843c8040003600700f4200040c5480744180001f000d642c1b10500600800e40c0000703d9a900941c513180425011103064100340140519520050103186d5980520484000346207810501e420b = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 415884838 1250 415883588 415883593
    0x1003201b030a17060409021e1e090f07020a1202070f0918020d0206190908010f090b01120f0803090d020d14040302120111031305060a060311040f0f0f02070203 70
    0x2205000115107030300c11100140c01058100c1d48038500816002c2440e03a010310010000141d107400364000c64074840c0c1c0381c28810760a2070b0b500e020892a1800044500c0322002c0611080c5031010074102180f01280040d100140d1506050005070a880c4200300c10242d0a5024018400a031008400a503480c2102e0050190045d43d51f003011819400c1d030b10030243c03190940044081000403603001d000500380030480c1682c00680401460100a25421040c01c0d204016034405660601d0585001c2c01c41da05620104259410424510007258030300700b01c00e041d900d0002091500e09424039041c2c1c1e1901d51400c00030300048000c0704110000300d021501060305550717038007940c0140c00d920b201180c0700d103032499a03864030640510090001d401e1003103a8100342c4010f0000021215510310000401e030b00111090754000000007151800c01c4001c2c003c00f078102100da06e05102403401c540e41c804440c060035a5880c0541e070384001645140700d040e0840400c0386000e003000c00103031041e00d10860103944010803c1c1d0091 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 415886088 1250 415884838 415884877
    0x2042c060f010504061b05010c0c11040b0307150e1008040b07080103080f0a270315020c0706112a031b0d02120a050706170105010206090c100320 64
    0x5042081080e04010700580d62680b03001e09006007a038000d00020201c24a10340f14013004e9000a609125690198150752519004464280745c105142d0b8036140d14036005500f040302d0442a5100000e070303002079138030281c107444010100003003c48002d1a000c001607807004060b01842e0303526401c29110350082d40200d2100919070707a00001694070742401c1c800180010820404000704640c1e2a001d446d04480f18982505120801080c60310ba00381c03440340310709801c0780118040080210101ca03800e8100c00c0b50714151b081ca1910030010752915024820041480700081d09400e401c9001e00c81314190041d600030743c403840054500c040741c00711010b8015500a1103a100400c6d05002c40b07603541d2100303200081904400001a60907c03180307004032401c6006034425150004002203003404114050201070341c0c2c6e0410110000000c01807207106030b10550654000d00107000c00c81c0c0e00415021014003040d00c2d0100804000c60781280185418030007580b4980458101a52104000300203003005050901c00d007000 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 415887338 1250 415886088 415886101
    0xe04020a0e0f0420031e0d0f050702011409040f0507030e010b0904081e120403030b091e10050a060305161e0f020709060b12010b032802042c 62
    0x10328141e424450b48039103140010002101c00c0005280c0041c00e2070b0448900d0326040129103464249040c110b901c0760340c081c0d0b40d544c45108000c4482c00c00f10070700d0012a0002100c502801610030240041c0c1080040111f5504007440b40d012114162409001000f4a0f60f084003420000d0105581f030000182c103081903d00e9102c8140540c080042c0000d141c0102030b19103030354000c070075800038003041010160f039041c040e1010041c201901a000c02440851003034030341840e00a003180c042c000d105120700e40300d03c140400c0140c0441d100c0b10703e032404101400b49881e2152040c05882d2103502ca2503204102140c0480e0640d030540010b40980e13103041500d03c40d42d4091000341e40000f181d81c0340346807400051400f4070b20607200d013106000c012594010390322003a86518640c003d681264224100e50b62002031600c0e90b00001010f40c44c01003c01d0f000481c154203040342911481040d9000345d00000182c14409030b440340031903040f24018196459172a0500329008020000710b42000000c03000a941003000401 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 415888588 1250 415887338 415887359
    0xa020706050c1515040509070e0f0f070c110405010803120a1a012706090312020d0806010e03030903160e1b0306062a0102031b040f0b09060d05010e04020a 68
    0x464520400c0070f0203e8003a00d683e03405070480d000340303e1221050b020360102219140c92255034014070b26500981f0542d82010280b00210102410084d0351450041c10801048589a10300e07411070210301d0720110304c04003420325207504d01c0403482140d07100345001300001e4214400402024415000119051b19984581c02001220700410311a1019030748021101099032088555030340081c00031100c03200c100032900104840f030255401010124810f00000d006114400d48c01c0340385410b0f54401400c1310348041d60000d200b4400a400503061100100504440399000e006448030b851010b41268180c042e940d9501c2c007105e100d07100c0d50b500c0600a00103d030940d4121041d50145807105010185117803251011f010603640200e54620b40000c1740c01c207000c19062007030302040080a41c0382c000f507281d0504081d4105841c240c002c1c0070030b04031820001088200c250400d01000c641900c86401c0d12b0b10060343c0442c4007403150b0402000201e00c6d200000c502440c070402540c0c01039000341c0c2c80c1e1070804c4e02d0365440c10 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 415889838 1250 415888588 415888597
    0x207060e0402090f19090e0a1a07020c15071b090b030708060f0a0605060705010b01021006051c06060803070c06030c03020301060816030e03070506060909190303111606020a02070605 80
    0x1a000602803143c5000d900f061000302e02250301405041d504c07155184690b908a41f000707240c80103250084034001d0148601e08440c07594021840c0c500c030b11281003015000c0d654504801c0f02e035005614000030b01014000803002d07070340d00780d40004d6854008a801d203a04280c028050068480141c68004001e94604000400c441540c90100040040703031241c8124910400001b4000840070b5219100401da81d03c8040250011601c90000407915141e6a000a428810303800c510350a0141b03412400c001c1070360340c003003100c0d1040707844c1f040c041c021001402c2400103415540c1114002c0e1000003000383c2000040c41010b01250029603081210106815086040e0310003881100c1c005000d2102042c00802c241e451080901214100001c186820400d81c80c00e507080041c040d1200c0d0807000400c19142401c520a9a01c44640006030486102003071050315050030418010301003554038000f05581241200407503001c0e000c4101c0b4a01d600e4070900d0103401030f41c00042e406005008421000500030b000386e0541c3c = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 415891088 1250 415889838 415889857
    0x50a050f0d05040603270305030f01080606010504180207020901120605011a0306100201060e07031d0a080a0f030b090123031b0f04020706090b04170a02100e16060207060e0402 77
    0x3c2c03815250500c00c80103454940c0e070100b000c80c1d038035050200d00781011345030070303004d5200380c8543d03031240381a260102001c3c00503400603910340c2116042006580c1d02a04a07010b64008403c2c100c0d401c01440740200c000e004002d8001d4020a050300040f0394542c08114101c18140704003c280001c0c0c0e25545800300000d10110060054030051000c40d8403490180a0030101040380e20000070300c0c654594001d02d0825003a1419408a50303141b204c4901c610040344061310803d004c40007044102d00c076a9130031256100700c852110170420b40c0050544194440d40103144400001070001c0c1a650311031102c2c0e10100038408081003280200c81080340941004220740860001c0784d901140608510300070b0080c01600b801017660300c10b500300300b02000114148219104a400380b14116514a8141b41c1407040c0d042440c413140110205000c4481c0c41640007030502040047e141c07002c210240201170907860089804041040340c540e4060100d1703066070000c0c40300129031440d544c19640455000500c4102d10400c0c480 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 415892338 1250 415891088 415891097
    0x180f21170703050c1b0a05041107170c120d0e16061d0303030a0906050c070b06060a110d08161814030309100504050114181e060403050a050f0d 63
    0x14250308104240c05090514000d080c40c520b082d201c10726243c1401c80754601851459070b841e42c114242e0a180315040090f00c400d0718100301218020304081d1050044400c028030001c080b1001080044828003658507030790f912002c541501003064110502e540080300c1c01d9241c41d261252140d0014400648162090319045d5040010360810104940c0c50021407185881002c3e03004e600f503038584007040290711541c00c1d14400580c050152030325206448003e45800071083d03091103003001160401c10721740e401041c11151141d5890b10b064054882642c80745042085003e41d281880e42c4030341101e5250b01c0380303510a698040c01ca0340c0a00544e11072044640020082415110910000083c204048007980000b012242800d41c100000f500c100d0f180140788000510202d010092540c0107160345c0030702c41140070858104094598442c03803026030081040c0c403505424061603206403c02ca0409810a0081c050380da54a4880c2031251760303400c54403004c803401c1c4101d4494000a00d8080742100844c4d000d13584 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 415893588 1250 415892338 415892363
    0x3180209070c1b060801032001081303030902040f020d06060f021e1e1e010501120f03090329060d02091f0b03070f02060615040b0a180f21 61
    0x2811900c6882e80001191440c0381503111404260201888000500c00c0d80d50303281183d819031030300c85a01038070310401e070503443c0202c2c401801603030304900d5030340d40603440d00150703408a03d007410103e001d80291900650803600d0300d03441c03540d200c00c02d03001401d01c0220000b040c01601d9451204840320740c0400c01c22401a0000182c801900109400c40588002082c04803400e0411300c0402401150410740700401e81c0d40113007070001c8001ca07840343d00384a200c40e0070001c0015614151407407480b8806400c1c010401c40c0680000d400b014001c0c0c610b94003841e04900c00608660905212030380c0010501c200f00b240140000008480789003640e02d280c00d0990203403502d2010748681880c1a0548805042c449046000c0500410300c0f00d101c101a500c00d440560301d844101001800c0a414024007416840c00740d40c14a00c00c9021603100e004440484000284440d6100c10345201140d07480e140b055405502c5507215070029081260500d09815078a81f0f0440c502c5271500c1241001c501502c906008024024003003 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 415894838 1250 415893588 415893601
    0x201051b0a150213120c03150f0c050a0e090103020d02060a120e100c050a0807050903010617060a0513050726030d1a04020403080316050408070f0603180209 69
    0x14901204210310800c84800106964800b400480816501001c00341e01058200e10380d84149034000c01000b003c5503480c200281c0c0c0c1c8404481707101c1ea0001800c501055403080042e0203440d4400c030b00420012404000521041000078003030b50050107110009150290b07048503a15003d0b0089040300e03801003403110121202c2e1701380011908036801c164107000880c640000038100d0343c040e00c254034100700701500100d0410f10302c1c0c07012103640c10b4940c0e0812a0600800c101c05401424850b004003ea080c41c079102d100c41000240907014039006503458250703a01741340740d00f6000028031300d000308600807050000399910004100b002d001000040c210b42d01c498001c1040c10442c501a0041111035000b602c025841a40824610350041d012076001d9aa500b030b00311443c20b140075154200780c2c1e00f10760543c5403901c0c5803129000d0b4000078008510f80000d440744038160900030350440d0b000340004030030388104554039580403450780910311941340401e060180003041503180011a2441a0317000384080b9542d02d468 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 415896088 1250 415894838 415894867
    0x91c05090607110a1e240e1201230a05060f060a03051012050a0311160504050c07050a0506010e062209020406170a02120d021c05130b0415020a020105 66
    0xa251304000441c4002c540c28081d44006400c0803003032642c00c9609480c21031111003204040071500c04181c1c2421403105103551001501d1081e00d1b040702c1c840651101070540303034010302d030112405d020500340580c00c000134040c0705501446001c00150401c8540d659105002d40c03c468442015440303001000350203886d9029500007600080103000c3d20703a40a484026001c5020b035009415142984621030714400c00d588440d000195070703454405000d03c4518a4810446d50200303000d101d2240da103031400075908405074002e88000e2070b005003c8034003034800ca082c0b03292a40c00a014100a000c10b110014040c2e040151aa1100125400d82c0d60314150812409200a0508003c226807050b1600d4000036404540a880e1000c10003a602a1910904c58410460940814148205150060000d2030074031500811180420401e100d0031244980340b010048800e8400c0c41803511140e4860b807000b0400001c02e42c080c0003030710740074101a288804d602d18183d0b610001500c1c028002541001a0401c840310f0 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 415897338 1250 415896088 415896113
    0x3040308030a060503190203011503080301090f110a0f110c030a0b1302040e01020901090609030203060601050a180e0f0106020105040506150f03030f09180108060402100e09091c05090607 82
    0x6002d400508142c49100090404c41c078080540542860420008154a000e20072405458496030742903004914550342c10129000c14411040c0c0c196683c4d031009002e454a0700000048225200001e6840e0724581025041c1100310351094005841d400d0654030103c1c0000d18061a810001c0c0203000012599481802c0c0c2d4200810060310701e040c1e19114801071b00e8070302440c06240408400541c840b80364900043c5100c0c107541c010b8003048444c2e64200003686021502a40060082c0b0b80a5038070210108240e034000c00b0010307020104007c2042c0042c1d170360080384100e4001c0481082da2034076640d80d0182203099940a0743c01504940040005c0760f07042c5840310f404040740201400c0342c010040030b100000d0075504413004400c0b55a00018040a00d4540007061503000c1c0103003002150f60754100190540e0b50a00100000c0c0101d0a0001c40c014450141d03020a481e104e008108400a1801d51a020349400a00f18507042c1d501c03603404c824441a00400540b591602d01520031810300c80b080d00e5400e5808074 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 415898588 1250 415897338 415897351
    0x20a0f120e12010615031a041104030c0b03060103051602030315190609050a06030603050a0b0c0f0714280b0604020409050702071a0a0e130615020c18090304030803 72
    0x510254600302e07203560711800d0b0b00072096000040c882d032918034440e41c0f0301c40003541d410030180740150f40c0c440c4420320105001030300c0041c0c0300050148180132506005200d20b41010f8940d0081110000c4d03554000700c001c51294200782e0b4180841d441d01444518107152991814001d40c0041c80050b1203040204d81003400d0100052464118910300c0711880070340ca1454100c40e0029460020034401c5080c02e201141c0148894501046060300d591210340d11f0711568a401801c820119020030b0003024107605503500b0741440c0b10410340c3c40b40d09181c03e410a5043c154041614001c0380c00d0140c51800382040b002c411456500c214003e40e906030b030303500070103c0000c0400c0d0340142e007400041075a41541c442c2c5481200c1c150005c22070903003031801c0000071461801462418943c100080940740d580707c0701411140605542800c2c40541d424541e0340505050340040001842140d0490714282e4009000f0502201c15916455004082c800b6203940cac2c4000c440030442c9600c00c1104000007010100119840301 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 415899838 1250 415898588 415898597
    0x70309060e090a090302070509090307030207080f030f03130c1401080f0c0a0c050a060504140601080703051207051c180b03220f0c030b040303060801140402011206050d21020a0f12 79
    0x1510381c03002440c09c02c400e484840c0b01d07038400320b104800c1640400400d0060076880c0b00038401032a007003421030740c4e80c801e180540d05c006401101080d000b418a049001c440303640103000485507a101c0c64040c2c1e0303118540c14803500180403c0d02003126810f0a01000e0b005a4140d80d04501e0005529019190171001c1c06040b0388602c1a02101804284c0c20b10030f04c2e00562040050349010340f5100304003481c041e0107801c400b40540008500b040000c8000503d01005050049550b0700c0d076410741402407c1c00040011402e410600c6201c0b180440e42c0101240541030206101d001090b03100d14401c581400102c58080166214842e040340102a4504030103a044c805c0000e2406912603a4442c03004580c0c56100322401c01642c018401015058041c410140c054075008010040301e01c0c14854001e074002c3c00190600c1301d4210110680f40280d0450800f406c006801c6030380401140c40e091014203024001c402509030b683c001d10b28002e03c08590440c44d2a0088100281c1801341d841380744082601491480170321 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 415901088 1250 415899838 415899853
    0xa050f0312070812060303030907050d080903100c180e0a18050a0b0403080c03041e05070801060b04031103120f09210109050d0305070507170d11070309060e090a090302 74
    0x654200080081030303c03841c2003503202da0818400311070010f409464180309400c1801044620007000860404903a4112461016000c0728149001e2900c40d00d000113806001d003800c0c001501070fa981044000d03400c2661810000c003600d034108001e85000340525010300d060f0001249542540d03030000102100340c400805c4840c4640d0341c60600d000c0c40380da03080341d040c000c4004201c02c0c180c2141e1500c1e0b0100c00a000e140ca1762030541e413008220b101441e00088913541803084141440800c01c0904042c00105d0001c009154a170881a04c07103801c2480120b890301c1d8804c084a00c9810003103483d803613000d102840b09042c248c9840399450940c0041d4905034000c2e641c0d29861205040c5180807134802c04040c0000100c0c214141451810505500040c03c189814a801d10140c0782d070000c11a003140d5040781b056412180c0b05060000d05100f0042034144090528042028030802c0c4802451205d01c65280d0304c980c56590340055a00881d0404140d50010341080080c4003070025030803c85460340310748103a400710f = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 415902338 1250 415901088 415901113
    0xe03071215021b060702010c080412080411040608011a1005090114090603040b0f09070e0604110c07030305030106080709060e130e010f060f0504050610030e0f060429060a050f03 78
    0x100070030040c200f049500c0070b01030241498083c440c10245008070718242500b860651600d14510001021203020000300c10009802c1c84008103030801d50040060051080503503425109028144200201c0c6000465424044151420b0303e41d117a9040f10903100c0c0b50500c4950001590f6031003001c2166400035100300a070840c96624240210304c01c0d40b05494003402402c10f8000051291401400c0c180035034480101030002c010000b09180c3d00840440700402d0001e90100c11150b18016104403c0c02407144903004810140c101d005181694281c3d0741d050021b540d0304100f2a0340048602c5040c010840d601741107019400d080c1500f1400304000c041c0030601c140d4608082e400c440d8001034078200380d80da4160a00c100101c5060358401000c044070203000700c0c205000000c5107015075400507414140d950000410303100d018030030078038810b030040f00740e804500c1e2504111011410390510608402240d100310021521181d010f18040c0c00701030a5454080d08010600079000c0c0e42403101a898400c090030001c4 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 415903588 1250 415902338 415902367
    0x10c021b04050c1b010c110307020a03060216080304300f0813120c0c091a09090a080f0306011206061b08040b0d0b030c03060402090a0b01030917030402010e0307121502 74
    0x1140302113000010302c4c04c00092000f040406021420303002d036001009204003580e51a0701d04820f40750803c0b03005907136151160400207040301c00c1c48014501c1758040100410f12101d4a81001038640c0d0b400c6000740090000c041103111503522484002150714024100034880c485d00c401c980c8a90030404441035040261a10f0030351b03200c00540c2c000095850180d0008201d0f4020490000b45a1201c062000903070b01c0c1c0c61034480da00f82c0141e00340a00510400145170780010060420010741040450341d42d002e000c00b64103010340c0121142404104c00c0c11031016440102c0c824481280c07125500c600c00d81410001ea0070440760340d0a0240c641401c1072001082051440c00104403064401c00d0020300b4403011000e15090001d004a014030a811130760030000584c03100110b9a900800e83c42001036001001001a001054202c9014002c81c90366912442c681c1c410600440c080c5000340c0780d000b65201008105540c40c5c2c070b01e008081d02c1e00f08040343c100010b2804106156001c3c8030400150030301e00c4100300d480 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 415904838 1250 415903588 415903627
    0x906010506211b12090706080114060d140112060b0f01080a0203070c0209090c120d0206130c0e070804231b0d0506100e0a020f071203090b0c0408010c021b04050c 71
    0x6000031038613040c0540301604001035401001103041c881e000c1d61628030580c3c10440890915809402c0005260340401c007654021a445114902240c1c66941c68240300c1668400d00d56040f43ca10386410751078902c51511a50042d01c00c80140d61344401ca41c0c41c450014080c0d04090522414480c01401c0e00c1c0041e61184982c1d485030a441c0000e02c03c2c026290208000503c13a295061880d40000480307851040e80440e0150b880701e61030100f40c84d20aa140750290500036250312804c400320301d80c030500105660100600740a036000303050340000707041154580202840b0000401119a00000450340e070442100303000300300b101b0000c050300c4881c54075484032402d080c8100ca00c02002c1c082c147d02030102d0080d01c015503802403060081103042200803203044200e4420340601034565801c0c09900d198162203500b101015a90240407100c89007022070740031200341c01038021f204143d402e043c0e40c0d0685610000b04602d03154401c01803102c128401c0002d000040002a04040c402a801c10600e000780d10041481d2 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 415906088 1250 415904838 415904857
    0x13020d0c02102703051605010f0507350606070c0801050702062a1812010b010f170a0f09050a1101020c0901050d06050621060906010506211b 62
    0x4040d00410410341e5803c4420504055886a03000300358503101891402180c5881940740c02c1841e0b4030405c84150b540c00118040d0018165030070001c02541400c090f0308814002c41d010780f62000c100d041c2c2001c0d00c0c40101c00100c0404100c96583c5442e45121030144895089500900924a0b0041c0740d200c0e28000c20181d0002c0c81c141e0344a4061001c4180c0c100700c1c556010409080300700501e80c0946013110080d00c4e40e00111070108001c10400d400200c050a61400303200010032542d00f409014841c940680a9100b00a000c5010240100c50b194050342d00b40b0011012289151540d90b2909500802054003140c000107240d518014540064420890142d4460103514000810300001000902c3c0c01e400328104c078055480c94004000d15140d8088000344c3c160f00c144082010b580e0710300401d00310300c407004201c4503821010607824002580814040d0042c0ea4101c1911980da03210303030034041107100d00400400f4070b00f060b007803002d050300080310410b07008100981110a06865480c1c1030921f60054280c070b = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 415907338 1250 415906088 415906093
    0x20f03010f0501170f0d0804110d03023403030c11040c090f060e06250c06090603110304080a080709091109100309150c140c030309070b04030b0613020d0c02 69
    0x500134808842a0349101528290041140d1216503440300c0c3c840d0325061124060040102c0400c0800400e54001200d4020117050b03044032000d00c0c00c2c001d40d50171910b41484082d403100c98881420b450f06003c0704c80001e64080800d0743e03a81c03559800f158101000101036404214041550005607038034011803001035941c1d511503180e0760070407880c9940700905a200d0014402d50030b0f009001c0707850708001e40c1c13100c0b215514480c800300502d0410082100c0e003080c0007028121205004681c0540222018054032110f0f5010004100018070441c080e1100b614040d00c00e40c001d00900004521511103640d02c0244c9281c514884c81d84c6680300d1082e141100ac512000d22000b061045440c00c00410190040c681881d00f8040140303107880c1d255521000001002d616a216840d1503000b902803628003a4010103000510303aa01c8140c09615120340041d500c1350f000b030084800c0062007444000c2aa41130700d8100183d480103481c0c40d82008404151030141c2141e03150203001e012041805481080c1c90b0030840d401 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 415908588 1250 415907338 415907341
    0xc05010905031815041802070f0f0803090129060c070e091507020307240902060d060305071502030a05181801090605150d050408160f17190309020f03010f05 69
    0xc20030210190090f44244e00c4003440100040c111113040c603218800364000050782d9400c203080c9595142248134024004081c149903503002c07c10490000d611400700c40e0003c00601c0300c540e04007044205d10b1036624070342c7c05001c421490980780520090140b000c1d00c00885054984d03426007003803001c00031150702030300341c00075046108032206181c041907000c0480d1001d50b2038040503607204802000340c0f64254a1403c00c00420300c070001310943c400402150005c000070389960052074404007510303085c00101c0c0e05d03020b540d0340002c00d00202040c1590040322a005141800101c580443e80f9800110500d01c10026044000c0e07036507110250062458035402a00f070003a907041034405e20544003294011070081490000c00b008440005050f907841801c030701d20210b8282c5460a0510b568040c20921404140403500207004029082608111244c0b1070640c1c2a241e06c032038002900c1901401945038001d6510f184c400c801c0910a510401e082d5200900445410032038501113400c4502c0b200c03030b09006503034650 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 415909838 1250 415908588 415908637
    0x171209060a110a020615190b04031a01050d0816080406030504140d021b030a0b13030f03141825080c0f012106181a040c0806010c0501090503 62
    0x2e8030840e41c50205480346400220748000790345960042c2040100034605801d201d83c1c0e0744900c004071060600700715146116403507500d140155070152108590050604913502c0c455404802914100c0d80002c269030340b15203d40d1698280d50380481c80601c0791300c40d1004a60001400311000c5c10251042c1c0d900042c240c0350510308045454034112900445034040e03d07103d14201d42c002128100700b6406a100c2925901400c0420320b08000c4020041400d40c0c03500802c803a0180140501c0001806941c4081d001e0345003907400d50855841c0e403283c02094046600007040740c1403144440500000070700481e00140d0006200d090f001200540c4014a50001c010403c1440300400c13034465107040842e2220760f000030b0440064070900079003e031911301c9030380d414400b081d050240d4424001464058800040b005130020b08100404204030806443d43d85840c040c0090705040c401c00340680980c0c0c031417503002d49a0b00010b540da030b040302604030359940d00c031009500018801e101810703413920324400d1a0301301c00000 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 415911088 1250 415909838 415909841
    0x11a01030e060103020a151205090312070309021c080c0a030806040b0a120b060a0314010b040507030e06040b0a0228080f040317040807060903090320060403171209060a 74
    0x32401c1100c50740c003400c014400740c1c3e1040c200408890f50b8180400c10ba001c0e03002d0035101060401094101240341c40200042640c1c080000c02411240d500802c0140c2e40d10b600a8084481d0700c807002c7e402400c0300c00a4040b80d56114981070f005ca0144801c14109101c0c0c0c241e03c1d1a050b6001c608034005114041444540c0c10180549205000102c1d032a2410504200040082c03440c0801d011341840400808124030391140c514800c00303590002c41c034092284a06d01000c3c068040d041c40349001c0ca15103000140d595200e07100c0e40382c0700003451001c2c090984441c0c440c0d100010024003074007034242d0708002070300e00310305000b83d1001502c00ad000500c22076510590080c0c00418024064201c0c0346604003000000b071751000415a80c0340c540896803415446508001d041e90007040c20081c042c0703161660100500d60050400c000b100c0c824020074141078202c03c036002102407400703003c540208003808284006100c03e140003207022810b58000d0b0600410324824800a80305441070101500403009000c3c0700c0c4c00c40d = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 415912338 1250 415911088 415911101
    0xa240513051903020a022701120b06040b01020c0108073c08040309210f050606040e07060909090812010303200d0e130f020307051c09020907050f0903011a0103 70
    0x1102102d10040e40c581c40c080d480b1410400c00034407902c0710211a41a042d50001e0a6403e442d140201401968640c0d900c0d45a001c80d08200b034a0030610040040c00c00c1c54180985181b030789040c1d01030404040c02c00c006403070402e0090103400034000300d084103007041140202e0345940058840914000950754908241c040282401c1d0101041604401c000110303401c64200412a4600c11000080844410a00850a08821009111503200030101301841400a801030142c00c044908114070140c00c0c000a0b0381d01c046209001c00b090980f042003040110302e620050ba001d02465003145401c0c40d1a905252a8509800850101e1a607140b41540c41c2c00968038154402c3c0200d0080140b03000805000e001d0210003900148101445c03e0070f0110715100790086501c0c2c03a014201507450f414003042c0a406600228420700c0000d03410007407104105c0081c004c0902107034010b0000c90294440791002c0710143d0010041c030b44159010407400c42251401d21039903410b407000d000da01e03030504010000102540c14 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 415913588 1250 415912338 415912363
    0xa08010f0506040e04030212121f0503100b0f060a0903150203060604050f060c0703050d0e0a0b030f04051609020d11191107091508060709080a24051305 67
    0x100e0242404240c4440301124180c0d00910080100c650f038038501280f0700001680c1e203642c0507101180008541303102e29201c0e805220281120868400211801820208148140c903032550284200350040307070140e44480300b10301c40036144103195804840481c074241e00400419002854404081081c0a038a0120301d49001c1c0c2402c0942c558201103000130384338002c03800b40510858212454951640e00e20089a07003c02d100010ba0310780e640c2d64200701b501e40300412400c2010401c169103000c01d5242000c0307000141d0340c41030905415030f155100540070480000300304490754485d46050110006000c1e103684000c003070810001da0388007000103072802500c07003048101e01220014805d0101940d0410401c101801d05032401d03810660a00402c90f203170000641c058800d4502c0c011034540d440300c20140102c16140103504650140d280c0440460f100304083c420707614540c07c008841400245801422840410680d01080d01c41e91303000c00d070b00d04541c02900c003019400c9240e8802c1d0300f0814140021084002d = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 415914838 1250 415913588 415913609
    0x3080703030b010813080a27060f020f0703060c11030f13050103090b0a0b01031d013e0c121c0b0609010512100305070312030b041806051009050c0a0801 67
    0x4003541ea80341e4403030001c034009014002c0441e61240d481c0c41448120300344c99100110b103100c8d0303050003c0a0b043e1500f60003901c4c00104010709000d0021300001d5161252081403008094882c80d503110703840244500711440b401c01071070321007012441504001411400035480c441c165031750500301601c502e400c05c81d40402e05044c20902c1c0c40000c540b2109280e80d218410354004130781d42d0700a000480c020710040710b24104007112420360b20b03a0148158445410b01124640b01c1143c50041e40c1c41c02d000c0f01d243c10300a043c00407030404910304600060040e110096100081f134581082001c0e032080d99411410242480c00700c4110300c11744041660090181c88039058034040d03c0e051502000805e5881010308608200c020b60002c910038003020f207180001550030500f5215815128039183c0805803460052000003070400c0701200362407901d0b01c18011196100d08060041303a40b141d482c030700900320003408058090641c0100040140c918041c262240c0080c4400700e50b126500d030009071034800183c1000700c008 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 415916088 1250 415914838 415914841
    0xf060f0d092d0218070306030501060f06090e010b030712023a0e07060c0c09060902090118050906010e010e0306010e0610180b0f0c01020409021b0a03020d0f0e060403080703030b0108 80
    0x6031580e40c440050100d4a80b0344844c1c43d51a041c1c180c0c00740c10341e40e00007003040d0310b055000180210101011006d40d0002d07500d40d420076554041007001c0400c20301030340080b85420004502c0b068014804403080345800c60015080c055017426828002c5080c1c5061724002e851096554041d102d40b40d00303640c1a040c081020060354014200075541c4003024000c840a00a400c6600c200f4030400400c24002003514038002d1040035124441c0d40040d4000301140340c0426441c00407081034484540061040e00c2c8003404c2003103c2c1d521680111102c072890301c84c06060224600c3c0c0c56a0300e441c10700034240648402c0c14a00c100342041000c0c402c8015a4881c1c078400c210710064800b007040e25100204c001c550420f900c26890321306c1440e40c80550320a03d0307102c0c030300d5610010b000180c43c61140c0103860b161f5900e002c4101c5003c3e403e40ca0340c0d150700207128000c0050304a111034000050060070341c03820070001841c189055102480210b01103a0107504181d440d0b090102e40031041681c14018101403220a1078215000d = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 415917338 1250 415916088 415916093
    0x605060a0807030506010c060f060e1008030a051315110d05040302180403031104060206060a050f280f1707061e051804050a02090114090f060f0d092d 66
    0x3078507018241c10101611400400c2041e84203000701001c0c15084034081014101c10110000280454461f402400c01c81200084100410340f480c20b04850f0018003642c5001c04003d412202588101c100c8040800c1c100c101046014103210300080080245e10f0b0110b50004548000c2d05d8103c0d00d071800380401004010a000684410400c00c80c880d92040d480e680c030303464615041d006480301165000c01c00301c020800041c2503500240305400f9800031344041041d140c95030180441c10b649030b81c0722500083c4110614114040418011903408440013070070100940340c2a0049000e101e40e485503000d0781c20001010f160a0085c040000184880d0600410346c0d07080744040e18505040300e010105100c004203039042074030144440c400ca2220000c004200c189081180c0c0380c001d4028a0240d400648400000000c402400085840c0c840d001400400d5404110003003041e1a0b1211121195407102800f2808500d10140942c03251940702d40c2000c4020003140500b08003c44504501c00413000c10301842030003 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 415918588 1250 415917338 415917347
    0xb0310050c0d020d0b090f160f050f09011403100612050403022e140108010c02011518020c0a0c0302130b0603040f0f021003020c0d0203040f060e0a0e04050a02040605060a 75
    0x10071409140240e140d0081164120017805200500c03900400c0ea0400c02c5079140d0540030452250000e0700004440366200c9600300c03043c0e0841700c100c0001c120708000b8410b501c05428040d00014005140c030300384002440030719000035042506c0611240c116807409000319600203c2c04103c5c1d082c6620b0821041c54242c4000b507480c1c803441d44286805030b41241c0c03030404d00124101c0341b000030030481040c46000c641e0503801064a17801d2041070010f51038039001d03030700300d500c18001c00981c02d0032420200400d0382004e00c44145000000b85191483c3e41c01c01030442c00b100d060043c0901c49010701c44490003103241d8010b104a0074141c0c450320354a03c2c0782002e00709031503840c0320640c5d40154020408030b5894076545411078811203c408041d5006415043d00603035268160000c0000c600880150707550014100b2082e640d90103140078103003010380740c14000d2103130341c0c0716124030303040c0f54002030500a00b580d94034210200280240c800742d4594010710040fa0960400340109001044140c80440ca0501d180c60020f0 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 415919838 1250 415918588 415918597
    0xc02030405210d210203010803030117010b01091e03060f090507080a0309060503060402040902030406092001080c0c01110f0901090614090f0f1302031b0a0c120c080d0b0310050c 78
    0x1c2c4040031054001c0c54560703800030b03210139a02d160115525611800081d940f80c009120b180da920005c2110100d00d0fa0f010300800000b0030040e1031b2544451b0420340c2c0c0b0143d809007103411008900c0e810783d001000c20400c1c06030400d1f12200f84800120700040d41080303800c018040d00220500d0740310040d02000283d20100700400c0312014070700581c903502c82100040213403040e6400303485054004001e1005024155000b0840310b4410399002040c021008640c541c007010080100d404110700800284c90180400c00621101907a103000141954905038261450342003c00c0008900e00c001c10701d0345c01d550b000b6000d200079000c181042c0d4180c1d140a24280c0d0341d0b1099076540d178000c8075414100c0d00c1a407100d0a181c3c05181d00106040c41ca4080b440600d80250002c5682070444200300f252075803c0e200d48000c40d2405040383d510600741040c0c9403590f00702c01a150644508100c50b0303080380700c00b01301040003820400c1016070000c60882e81a00800d0718107170300291160000f5103801c00f40000e42c1042d034200c4 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 415921088 1250 415919838 415919863
    0xe0109020a020303010e0703020412110405060f011b0503090d1203050a050613020a020c030304061205060603060108180a15051f060f031116050f0f0a05030706090212010c0203040521 80
    0x681b442d6034000c0110b01030b010300e074400c561074113801d1f044408006180f501452015400d56081007169941070420503000c8001682c54045100c0c2c0c005d0842d0f802c17038070003840c04c010701407011a842c196116000c6125139941000c00e4618546041c4103030121a80b5016103a0410f105c41d40510043c10b00000181194614010400c400e070380c00078081c111300e4000d0096855100b00103003541e845555071480501a00890f40c0d21507242417500c0d0000f4120b1800b841030301d00680b4180e441001e41c0c0e4035118400158122600318030002e12944c0c81c0702d4009050150044214503003404007040318104480301003001f0318004c00140103a0a01b68080c44071641c0003100d1140c1c40c02034540810b1071038017030300e8001162107011100700c3c1c2d821026403100140200000e840c019031a480084031603044000210b25214464a80002c0140e00b003003029001103401a0441801580021b00c50f03010503280007400d80c03c440301e01d40c103100540c1000c00d00b000245084000c04003002185201c01e0408040300c0034140d142d0340641c0c0308 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 415922338 1250 415921088 415921109
    0x1a060102280c090507030c050304080417030f07030c02090a0c0c200a030c050111061b18090a060806060307032a05060a1229090603010b0310060e0109020a02030301 72
    0x1103030440d2410300407481c04180c11a2a5806064890a0400150004941c4003010900b04414501024492411a882242c101c10054281030406000c2c0142206500c0108403901c028450180c11301040b10040c038005100b0749900a011807184103010107040c0041041c140c941c0381c0406a00c0342600450924107132580000101e03001110640030075240004448580e41184011030080208402040718000740d8800340c035090b00f0f920303550030b8650b0394000807101140320346101854462102c07085d02c09826070745400f03040251400c1c10b19000c145c5440040310402100ca844178400c102d24641404070503040b04040e0058031040e802c54442c174810b10000701041e40c0303481a05503000011514404100050100105008d6031443d441e01300070724101855521200040c40d05007595040b407100d0000031060500c6d5080102d40350440410004448001021035806540321144442c240c3da0501520040404d1064001481400e2007640d084a0340140c126000380361042114202d00c079000001d03281100e01e000007 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 415923588 1250 415922338 415922383
    0x506120609061f080402040f02040f180216110910083c070305062805090c0a0902070c051008061903081801020d090e0c090a0503070b071a060102 64
    0x441c6043d400e0549100702404501144250254403028940c05140202e80034000c0d680c40f102240200d1050b8464804c1c072555440c0304001d5003074040407912024540c1040141428600c4c0d401402c0d0f070b5000e8000300e803840d090303104c1190145000049a60040c3c02c41010308089820980f11a545081401900f00041c19801d00240c4110350343c0302800c0380992022030380105070508200c0913528a41c6020032a00e0740520000207518802052041d2900351101d00040104080721305028024413020303000ba00ca500403c9035000c2d440c0c4400394980e0062024640060760b4500e2414030080e0420b076a000329200d204610800c20b09a03600c000e00a0b0404011680008003540b210310f1185840c02070f07440108808404640c01c41c20300c4fc420082d0301091401c1c0c003034803048030720904101c2c0c200e00359018036508010181d002c00c003024441c10250951200140400110907104d0001a15198995001d5034200c400014a00e007004010040c2c2d4900c04003199500140b4101000007030b4584290b00b16005038146400c0 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 415924838 1250 415923588 415923601
    0xc0307050f0604080a050309030f0f190515100f05150711130504030903170c0a0809060903010905010204060f1b0305180d030215010b0f03011502030c160f0506120609 73
    0x1c215401420043c041740c07401511403420f643c072604030701c9034144203020702181e008030440b001c10103507245000c103005801d001c6080c20300d24202820701517003500d0902c185000d4070035000040060b41e002d4440000082195480c01800000112043c3c020038098240f1400d6551443d03044030941d0001175004000c080d280b0201d40228201010010700d5440c2d841c2044244070615030003d000c84160390081604170441e850114444200340b14681c014141580000d03880c90204040d58003a0500010051002c1d203010007203c0060300351600c0340f40940300380c4d45c000f8042040540111080c03100040f03d0502d8400701e1941203000090b50307007a14015041c0240001c22001400000720700c240e8000d4010000c1c0000409030400039a58241510002c00d0410f4100010034000102c000350f0301031000c280d13012440c581c2032259140003522540c10070802e6120500582008a1090100ba04407040030460749400713916000400c810040d0030350186001d000d080214080403480c2c44c42c00be0b0f11810513038040c0907a44070207 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 415926088 1250 415924838 415924849
    0x12060109063f02100e2d040c09080d1d1f0507060209090903190203091c0812010b1c060f050f0d1e150b010804030f140a050d0e0c0307050f 61
    0x307000a500001308041001c48540040311800940130907643d00c1020b4070191440c1c1e00c10122012240d160429100000910345001d030002d4a00d112585071440280340d80d18400c910345040c035171081d0b01088900242000c0301240a01d90900018100c3e0100c00046902c4d0b900c0b20000c8407031800000b00800042c0e01400d02c040343e011a00703a00f00203003440e00c0c586030007450b260702c9411017000c004d00c00341a1000c20100718800419981d000c20b001b000c00740170601440c1403020b1341c200d04070126402c0100340b0042164043c4566141d00800840c0c040c955642c0314690300440d10f890a070200da800303d01d80f01d014070035200c030300e40b1110a03140292010002550344200051500c40b13214801810b059084002c0700d1080303030385200444600c2c81000d124001c005011080c409407080740c04243c0c0045d4815000a000c28480c41c0b0b40b080c2c1c503545042c1081980b24400d0001c419074006c0035840007207000050220f82c50303005032007001041c0c410030700a816034650300c100007611544a0310032103216030b05202c410450b03942d030f1 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 415927338 1250 415926088 415926209
    0x105040b070516061110060b030a09050c130603030f020a080304060b03160b09190302030d031808040e04020f09040b010504050a0e010f0f05062403070903021206010906 74
    0x20202d03c1c058240d60704402450035001c0600843c9038045c14406603620b5a49015031001d817a80c000304181540e41c0c021103240107100c10542920240710304104c80840d0345454100724051080e00e030011826904604016100c401d24803071040865105c9c058000216111700c0c01e4a8000ea40114049500000075001a20b004d01d90b03880804d41810010000508821000044c0107002d01640c000c0e289598605801080d400e440c07002941580084031100c00c0d041c881d40c4441c03210421040150300101a40d12a0b618a4000e5040750030800d41d01002d22080d482d01c1c401d9000b038201c00320751540e03880c036060f40c036600100818072405001d543c444003c50300341841c681003206695180b100800640c3c0d00c1041403006810450342d4004218a0040454aa03052030740b4104881500444001c2c0e800d000b110f50500341ea8070017417079101040050800400183e441040307071455000008000e003810350600b040f0004440c2c85901042150710b2400c0340c8480f40c4d03890040d4600c1c540d100520303507010011421091010851 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 415928588 1250 415927338 415927363
    0x22110150e01030605191a0c07030b0402190f05010314090a140f15060a0501020c09191b0509040c03020306010f0509031e0a0c05031506060702040b030708101a0105040b0705 76
    0x1542e03040361303d06d40c007007100b190484440b0780b1040d0801000340c40140052281d00c21104842d00a45424004038111050707580c0c009101800b50314011441c0500803240120035008581c0020050700c0800280da8503014034081d29901c0908030309181080c800d03150b034a60341d480b40200ba815040e2000981c0d00c406111039150380038441e09456500b008460ba10011500482c0d00d14070a42c644079020459502c00a0350b01007a880150003070315640c4039503100c00303000d145c913076901111240c13544001518a12201000d0920b41c51a03101c0c0e640b2080c604082000ba5030120a400301054414070401145030381c80503080860488608000f41d4500f02040420b007010703400c065151000041c500c07800f1070010001905001140581c1306000344985a00825881e010388441038400c1c01c0f0920040b0303050345031880c0140320891000740b00040541132040401d01b003940513030080107aa08500060342a501d46409407044850141d07428400c4180c4020000c1c16030b01581c00303001c45103080426500d040020810071101100d1 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 415929838 1250 415928588 415928599
    0x70c0b18010e071d01050a2714070f0e030c101701080d090b0307090608070e040e03030a1a0d0f0807060e0a0c0801290310022110150e01030605 63
    0x8030b8030040a40d40c040c1441404400400310b82a5540182c0c3c0200c840e060340d100900e2404018075210380060700030744c0100381d54a610300010180c00c403040c003485046203000320080a5105407900b01d00240c400d44031030384094280040101442e1496501058000109c1800c03101100c03071440d0303954100c0f4881c1550710301915083c981d000214400d84005800d103080034055480c00d04007038591841070f003d0300094450001040c0030120600c81180564030b05030784100a40344c80e1148040c402c00080c1502d016010551040c8c200009009840c24075004081102c41010218180d00842d400800d01c030030048207015020012000c09c14003080101d40869103034541050040c0800144820607644030354180f8400c5030220400c10001070300c0401030103a03064600c0301c4c09243c10841040c200d1010385002c00c94007264180030b00015417142e140300e44081e14908501040350540894019001518183e029000305540c0742002d00030413154500c404070f02225041480d050f10300d0807440b00143c019121070f802066109 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 415931088 1250 415929838 415929851
    0xb060c03040326040317161a0601050408060c07080702030d02151e280e1b0d0b0a020c011512121b032006041505010509070c0b1801 58
    0x506000028006681c040c40e1400495203039150f01d03070194450441d4039038000405010401c0451141521040480181d0f00c0c0203141009107244102428000c1c203080f43e04658060580c440c0c140403030801d99003c202030a02d14909410040c0056480d9030007014000c040710b0001e4007030b04000140c42178580441d4058121400d6502003600a511480d0400341c401c5008003400000e010200c00145184559008501881440e207400b8000010f0220850000c2d004003400c2e1051284071415104400701c0e10f0302e100c060072101c03045101e00c16010328a20205442030303035030341c116202041000c007507a17070841c029100040c0ea4910725124a07016103020300c4135000869200d03100099450030200c4000c030491145052000d114040441581d41d14148926400c403102d00c1011000000e0080c400084003103420080c2256004403102002d2400004036000c4505025210306404070304603034061304c1d02410088a842c0d85900e041d00004013100c1c50418094210710310750001c58010030b016403004210705501802403014 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 415932338 1250 415931088 415931107
    0xf07032d0b030a02100903030315050607020d05010b0603160206090609060106080414010510052e0c030201020403140d0906020c10030c0e0409080c0c010503160e27010e010501020a03210b06 83
    0x46d541e20b44000d0700440c0c28450b82580040c610a402d40540d08002e02046c1000d110760280001c03503016480856180d075a030342d00840c15542d06005141b1604181e20321088084803d24000e0030440d02030700301c0d401544042c0078480104000314209041d11100e14003801241d13501c2c180220401005c0102030380552030041071140c080001c0b003070034040c0c80090714807410b03642002039100da1031800344000e484a03c0080b2051030748684074043c12043c03039000784005801e054486c0c0340c000011104c2c1b854007a199001500d0301c440b039908004580001c283d40d0019180751200a000701d8050074000c403205040603503680743d0449290090841d80b0100c0b4014008110341510740c6031a42155010702c0381e54000d4400c00500700d15540c85070741200d1244261203025062904000f0043e90362100c0201051b61125854142d42074a21100341d001c0e55407440079030a95a1949801040f40c0b4244040c0c00072411500108450000300780c01007004e2a0005151500a003400007000e100e000424040744110351190002500c26074 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 415933588 1250 415932338 415932347
    0x1403010b0a05240424110c06030606040302120705040c1e051b03030a0c021b03070902070609081215010801050102060f07030f0606020c100305040308040602030702030405090f07032d0b030a0210 85
    0x7048070b10302110f1045c50b0707404e000076500444603000044071584000000d619900380400915003007900904410b04007501c0340e000400c41004403031219100c0d80094810055450980a01c0c0f40814a83c2014103030000500110451407a414a242084c0000002c15007104a080303051841c11641c2b2006580d00c07420071210100190404030040e000601c2130103c2025105800403855149501c0200142a100e15000c1004069000000f05482e4582d9400d070303600c04614814010040c0844000700c4800300d180000a1440d4030b440f03010880d040140c820010300042e60001050364100c010206001c00641c0c51150480107844000185080c01c1d0501400152494002a6112446104490808204104003c11400c680c001c43e0003400203100701d004200420010740c001c51b0840d02030302c141c0c5d03d8540c654010a421901c140c074009606484802004012681b40c400c41c0004d00750108510b12a0000e0700211f03402c01d8880c0d4036010b0b82c5541e110002e142d03039804c02c601c904456014050704550001c8501c042c0 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 415934838 1250 415933588 415933619
    0x3121905150f030706020706031a0303040806010e010b040506030109020318191a0f04080a0c0b13020301150605250f0303200406020709180f0b011403010b0a052404 72
    0x14016002a007865100d0f00e4082001c106840c550f40c02485184d1a102c01140505421500300036076540860740000903032070510003000030f01701c600020040c81d4940700030030a01c1c140581c081e40c14180280f01c203201c00da40d45d0080b80c0c1110b100e00c10140c8c6a0301d4072000c40c2c0d241c8560302980b100602c00c8000280808007135141c02c600080c06821400100d42d0403482c1200a01400c4504400d0034150400184c0042c01510141908040c03a10b412910960140e5620955540550380c1069005417250380c00114a424040c1d00c07603071030300680342080603880d1200241080c000c90364007190100c001059000d0300380241c00904040c82d00700030380141c0100c0e9424003400801070801c051400b00300341206101c060b002171088908441c46980280000d5240c5a0418010720200241c85804201c2403031a0780840c10160030b088103107014004110840d4074101d070f200700f020440e4860318003c3e41040c00440140c0c1d02c6581581c11540144c0354178aa5610303014035240d482c000190402e24260000c94041000381d940104803 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 415936088 1250 415934838 415934881
    0x409080c010e010b1e0d031b05010e0625300f020c16081c09090504030314010f21030201060e0406061d062d030307060902130e03121905 60
    0x903150195030300e1790300160107115100182c100661081200010384900b000c1c0240d03001903581900c18448556030f241c00c2d114000b140ca00c00b40d01c18800c0c00400843c2c2642c01c6200ca0b04182030441170040000050603840d900307500000041c400d0304070082c524800c0c4460382c680180c801410092100b040d00210000c3d0084034114246200d9942c41040c0c0403036601c080000ea40140005200300d0303e038002584103001110050408221003010300169215480c01041d004034420344011070999640c2c40c41e0580c00700b059108418080170750004001c0d03c20302002d55145601d00c588001c052002c81d0805074054545030b0b1014036002004d00800044c48840e80c0b003002035520114070803000e0903004031015000740f0203881440e445600c01c00e030b403542044c0742150102d00368501101440100105000a402d641204405645060b02c0b403803a00d08520703000f010100c9080e40c841c0b041002c3e00340007030302680e6030140c000c030240d06e02c2c000c10115114030506400040710b0f00031043c0c1809145064428000b9489098000 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 415937338 1250 415936088 415936099
    0x601030e0f0106121a060a0b070606030b0c2d071e050a1401060e07080c0309120c0d08091605091e010b0918090325120503010f1a07020409080c010e010b 67
    0x85d01c2c03040c8844542d94000c4030003c0107c6402c40c205503107010980e10641c1e04480f22543c6010005c00100d08404151040b2a60040725440c1c9184002c0360605115980c0c960040340007004030160224500c03016264042d4105080301c0c980c4442c6925010034003038100d000b070403604c01d014241c010081c80c021240c449003184002802150390f00e0242c4100b800d8141c3e410070103c1e1140c0f0006542d8490207001d183c0c0565180120303035515030f1401210407194007521404803590881d985110a031134222100680000c4078600401d0005031022541c0080101130186030303c80c031140e9020031805010b11090440c0d0314142c03500f0201559641180c20483d5002c40b03034860050040390003070f00085148108092040705c00d04041e5281140d40c0348460b4084101204404049a120000700c003c100650300388415a4240e4036900d03500d50512480d42d8228840780d00c00704017240c04014108d40002100c068500e16035040d54040b0f1180303a5803525002ca4090084150840d41c40c000c0a1301650b2815040886000b809489 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 415938588 1250 415937338 415937363
    0x5041a0403120e0f041a0a08030c070e01080a06020703021230070c141011031503070b07082b060608070512010e06030309100f1b03080601030e0f010612 67
    0x40640340501e0303c80590703900c245408500c4815052640201208001c0c0f250a03c00c280d88200000305584602d030001c0c00d150748045a1a40008000c10502e800f070724070451012015031401c1815580c908101c0401031140390082081e40415000b04045003460215041090b1203140040d040301900c003803003952110240b10900089440340c400702216002d036059a4810404403641c0c0c494900044179070207408400d2080e030008241c0d0104910400c0c080404035001e07650780b400d01d8410400700007404030401d8405c0c0c024000c20499403803c4d401b200c100350ba0045055486040d07141017241304039501701e120403245c0c200032503008210015a0004003500c455864030180c40e100c0c06c0b0200d5150207132541e0500300000010040c8602c2e401000e884e070744100c00030100ea16203044000403030b03050041b4072684400b00300c2c0786039050389050700441d2020700d40080c2244441441c106444c001d241c010050040c1d8145540c0e4550701010300000d2142121514000000b40906650740000c408515001c000c02da07080100b011 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 415939838 1250 415938588 415938623
    0x70822210510051501030c0509130207020f03030f180a030b091f060612150512150a02090a0909050c03011a0102070f0e0103120c0c030c14010806100f05041a0403 71
    0x102d09070003183c00801d04c610082002005600800280d0720500901c034007400012026501c02100140b005006040940c0300c07031140c4140f00107002030ae0768080c0b007500180508001c1d0504034040d0f03180b0f8180324141026401e2000040f421440c829040a13121810040c00c000c4079407000a00c02c0c034510700b0340823100b0680004070140400ca4085004001c001140c000300c0d05904000c40d045005880c05084424103083e90751000604202560040502c464204100114901840c20b0501d03a111442c440c01303515054030300001078580e40c91030003540070240c0d40d0b50180052190802c40500c07070340c002900805c50f0004034650b404000e07040c6001140144a0030302d0219116450410364011220440c040d1900d0f40d00f560341e0318254000e20f1041c00c1c10041d1200c6e080c0b0101c0c800d40c81c550010340c010300185a400341412420440c0c0c002c4c1411040c1484000828040e96440d116071102c4c51a00c82e02d0060070240ca01c03a402ca40521542e403003004020300341c088160201c00301c0402001143d02c01c40c1302d52055078012 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 415941088 1250 415939838 415939841
    0xb180606150306060d060807030317070e011704030507060c020c1e030d1407050102131a031b031e0f07090e010f090b06040810050417070822210510 65
    0x21072140d00c28840c280003280e071500704007002e0030f0a8544d605002ca04107807a0010345240000c1640150b002400c18810004000b00b0301aa01d40c0000302850402a0a2640c1c80044c1050441011070001c1a100f40d00181c10b051245054850040d841003051010540741c00b0003e544d160a01da206100c0d200d002000c07089000802c51003041d02e01c021340644144091241e00b9980041c004000000403d0304115000014800388001c1c060404280d07203e07844a41040c88807904001100307111015100b0400c24049807007a80b030101104031107c07020981d520740d904699984440303070001030b020160311410180704107584052207036807050b007540d0354043c00b461780c80b680c00705409800c0c40303546250058020244421143d07600440c500c8580501028945695541c62078070340a030004001c41503a5880b0706100c100a40904100407500b0030000d281d08080b42e5441d4038000744a02c81041071403146480b0f52180d400c2c42010b003c00109110002c04440b0a541d0302042d14960704400200da050213040f00040072070a09 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 415942338 1250 415941088 415941109
    0x2060c071106120f160f14090f150301030303061a12041e0b01091a0d0308090307080706050612120f07020a050a0e0906090a0b01030f031709030a1101020309030a050d090b180606 78
    0x594440d4440c05500059007c9079000d04502c0350020070810b919010f41d1078118248900c40741e0a1041c40d81c941c5135003401000c40d6490340100707221074111107201c08083c0300d1100751183c54800b800505403a890703034034011500d107420030380d07500303400c81080050b07000c2c828850304850481d1100c40051200d45408014405030a0840c40d905034445030b60b21001c40427a20901c801030348030848108076807405030b0644401c1e0090700249021103c16031030700200720850811210403102004510000c2c46225801d0032000d02d0b41c0a4082c0d414083c40001c500d50082d969942d25420007043d0280ca0342c02c4064a402c14251804d2049501d426640711711408140c4800f000206041c142d42c100514051a90955076442c03418a102c80d410350402c02d00405c036015604080741500d00407403940c802183c2e0303500200c0019021440758420768003a03900c144100300700100302004480c40184185403180d80c40050031101001001984005841c10300e40c0010881b0341150710f00444a60040c83c0d0071030742a0390300c03c0100030311001c2 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 415943588 1250 415942338 415942367
    0x306090120040f0b0c0703061b0e030c2d0621010609150e030102130801060812070c1a0c0102180103060e040c06030f02090910090c02060c071106120f16 67
    0x3d2002c410420701c2c0c0e000b13026202c00000c25040d80c0740d2a0703803500d500b8292054882c0e502c0d000400031302c03015002600041100100c04003500980400e5034004009034070014a2503207665014545585045004116010700054000c010400c030340f1a400300742c1d080c8421064051925060070a0b80002c00d09900488803042200d00c80304004248000d0544100c0c0c07449003400409405640911030020001841c24000020305207030800002c40c01c0c40e000809107000804503031040a607804100003000308884070380c01400c1d29151141c003218801e10544070304141c800c08030210115480450305030070310900e0000414940b103003640e013030041c10b44541889054001c10f0f1340003003c2c0b21103100c00300120740c005d40214801c2600641c0050501c0390860110f000c00c0300c00c8940d20513009001c48140100e0340305125002d907004503440102424a009548048a4840c150b006041102880d82c04041950b400b02251000150344110b600c00d070502c60480c0da80035005032264a0100d33070b490401c04506100d02c01602c440d11 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 415944838 1250 415943588 415943609
    0x81809090a0204151706070206060118090b0109080a06020903061819170a030203040b0a0204060f12020f0c01020a092103120b1c03030609060302060306100e030609012004 75
    0x8998200f03c020691881c90518548042d0b1000845882e1281280c1d00a00410b000d49464900040020b042600003001035040c41400074800701c080044180c01010b980001400140b002d0150307005940070420b580c04007050784181d20201041000301d4000d4852984242e00b22009510b5210005a02100350f100c08540d0364410015486101e9540e0890580207014100d007041221071100c01c0342d1640c0c4005844404aa00041404100301c5490040e0707921500c1000118140350a00200400c00d0704119070b20f01c10015540c82c8c3c480350512960403103d04500703900c65180e4510011484c80e010307401c00e6a0741008107229810018000c2500744042c01450241c2101c81402c559560b000d4030b4103840c0300c5404050540c0c660342282161140c5103003198030080018000f02e410158070b001410389010790031155003103080803020001604c601054a800c0002115400c5009605c888100e034900031003900941d0600c190414003071001c90641c4031540f2804000b0b150000140c100c54007a1481c4a2803081d030400030b = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 415946088 1250 415944838 415944853
    0xb07051e0316054504090f120e03070306050708060901140126040303140907081e0c030105040305030702070b0f030a0c020f01020d020315040c142508180909 69
    0x3d00c0380004044c5124100da04242c01074102d10684500107402803410504491183e4100d0b06481c2d0160700074403c001114180400701e600c1c0e84c0c0d0300c6510f150000080444188020080b0a98000c1c0114150500050200c0c0c004950381d06200b00a81f000780c03a41320208024001281e09400d202d088070313042c2c402e440b000f0005a0074200044031090040300d2000384c445910800c03081c8401ca500e140354000c9010f50340114949010510070f6a40b06005800c0349500e134041c3d00100701c400004204401c90b2407402004003410b2000103c914101418810860f80c95444c08003008105a00800594000c4100e5400c99604540f2000c00380c3d064807910044840418080c00040c0d0110801d400890301504c032441500e585d00001502a82647c1040c0c8c2840040c1ba0044100003c0c07d814600702c0014110444051110700c2c80c1c1c0c000500000c400288205824000252403100c45542501000345154100001065010b0034100740d1459004070b45164907121400740400c41628050f0801800303181c2c144050f0201 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 415947338 1250 415946088 415946131
    0x60d0b011a0706050405010203090717060f0a020403020306041a06040603030215270601060f0c02090414030f1b0d08040b0a0c20010903020601090612060e07030b07051e03 75
    0x34a141c104080d0700740200014800906070b03010b1580594821000580c49003808001142000920b402c58030400c201d03903e4100c0c4c10540050082d40205d503000140c41c940d15940c0713000010b40701c1c64001940502c19002030200b00604044103202e410b11001118a607919094200402d81e06940300280042c2c0c09100311200d8004a00081500914480310780e08840710b00341340c0c911603030580b40242c00c15600198010422642c1080a89020703084500e05030b8460310440d800a410280003610103015800d01003400780120800b00f08071014800e204030350907100d0444100342c440365159101248114012004600f840d1401030941500465100030500300a03911041c41000800d1101c080074104450f195402c2c64a400f2138141c424201c40000001c90000c3d02ca003800b0303281030f406038031146c40149030001c2000300c1d03003100c0b00554505502c13420124400f41451000d500e0a2259040502030714003c0c4207001d50181c0140061140104075401f2140c1d06804066000890000b00c40c500c10031400c2c004034000 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 415948588 1250 415947338 415947359
    0xf060c0c070509061c0c031203090308010605031003081911070302090c0c0106090903090e070f09060f0903021810060c0201051204060e060f071d0609060306010219060b09060d0b01 79
    0x1400f00d00a0300700f142403178034480c00e8181d007450240300340c03002038448000b03109000d0003e10a001080d0581020301482c4c01c1594000c0071980d0500c1000c0c200b11000c4007060746802d00540d500c0003980c110300c202c3d8031043c01c500b00b48808100c03280c00b800860074040c081e02804501041140840381c000b0103802c0039640b000f4411815a02051000c2099561a1004141c8403203030311840c0320440c000e503282d50310141000c0c0070150044c0701400728000d100c169500c102503a5031044102050751468a000000b00c040c4050684200301c16800007584084101d051805080715840418861070040010781e00b00350b43c82800f51524221814040d0000e81e04111910240000265054005214000000d40c82e4a40d1940f1803e0030b10580e1001b036520781c02d00501200e10350100300303160b800c1d010082d40ca2a60881400040c0d56100703084840703010300400307c00550140e0007800200303102d0b08101c1015110040d640390040051551120180c0b040c1415400301ea510308080100c4882140c0c0150103407220790030050086c5 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 415949838 1250 415948588 415948591
    0x20a1203020f0c0105130b090606030d0509120f010e07061e031d030a11010c0906090e0426040806010605041409060402190503060909061b0906090d050f060c0c070509 73
    0x2042d1108104080f041d100c01d1161605c250b5002c4002548100c4c0303031a01801891300917055031020b03032091050001981d0b0118140c0d400465900300999107900820100714060050a4110308c0350150142d0240740010640125050680d15030940b0b9405460b00c3c0150f0b2682e00c1d10300100c40310313440b00320300d9081d02d4020380c40f070380c01c0d55034503000c2c445143c18004102d491075101d4042d0000103095811103031222007003406004441c03021410b010341900d0501d00c0040c0034142c244181e5803410308000c049014400d000c0701c112071209103001520344500b40780360208902e0740140300394091071250b00300015031588520160340943c3c2c028506691030000700320411890700703005000e4a80c003644c01c0041e40d10581c6001145034002c481c035251241c4914041040041400005000d20740a80248040000001015080c21581c0368101c1c0b4480c2c50710310107800f00b2868020401615041030091207044248007000800c4402c190070303002101c030940c1d100307911012117004042d04003a8a40c00502c040c041480c0009080b07 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 415951088 1250 415949838 415949857
    0xa06051908370f0501320d0c030c09110409020a14041d0c03040f020112060b12041101030923161d010e04080307080414010e100606020a120302 63
    0x142d003801c2103078441d150005585203165840691104021108000d6005000b01e0307140090040050358501620816540d4501101c1120b50000101600000d0101d001c1400041c2c8007800c075846001013886d1640c44400e10b0701069039842c0320901d000454120602842010b000380b40c1e891800c25140c480300c40041c0d0402140d920034050481002d0840c2c14040000e80010f00d0b500c01e01660001031031a0400d842c420142405003140005c00030030020903400061b030031080da4203203400f80d0019071885074800203040f0307034110400c0c2c3e040004640308100038480403540140d0094040d09004240300005404480a0040c02030882c8800300c4015074440c41c8028040250b810001510311260035081002d00210440d00700a040c01c410b5080c0541100c2c0310f8030403a000d801c290a0001e2541040d40343c04260f808018045801c0103520000a4104011154490000107518000b482060310650545d6101c00c941c12009000c1494120005492480082d509643c10f0300108240c10054004500310060750058118 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 415952338 1250 415951088 415951111
    0x130515090903130e0448150513170a0209070f0206010303030f060f08010603060e030f0d0209040204090e0105060906030d050421050712201e010e04020408010b0a06051908 75
    0x8541c0d03070000050301050110b03200c00288514003044004486e0141c0a140742d040e0018184c1e5040c040c1c04e1120344949901c460343e0502c59114400340071190501031054000030038070900c01c14101c0000d940054a508002e02c02ca83d6161b070ba94803685d0403074018621052480040e40140010004a80a0b41c0640380107000780001140c00c940b039075162a000c40555100c0161699219020020710038a032003068104224040a54a4070f070701100308091034001d501032003584650020705c0302d805a43e10f504071001003804020070700190385114062402020221780b002d000e01075072030004110b4600455115a41801345e150207050909040401941c0c180c140e00b03007061515441d0b0212301040d8200031030001403400107020403800700940f40980f1030301a0702640401c950740e0aa000000c0d5950444041070280c3c003005000f610880801c0100c590181102d220380d0018030015010410500c19001025912804d840c8a00d00b10ba58000484651141440f044842c0240e0b0300001c140511541000380c2040500c000e = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 415953588 1250 415952338 415952363
    0x206070c1e23120a12092f04062607081507021b13090c1a040e180304050904150614040c020a0c14130515090903130e04 53
    0x1119540070760310502510046040d8511803010030320444030310480810000600080c00000c240c10080f8000c4200740c0050040c00e05070951118401c0e03229015041e0031800c2d080810181e682884030203003100c0c00042d0071580a2500c510242090702030001100d109210300391010b19008402080d603080c00002d5000c6000308070000030381705e0782001540c0d0613000c0d10244c001142401d10740686000c0d00c8926604102d6417920b544030055541d5582070401e000042008102916103203003001d580c0a4540240c4045000307100500c6200d600e00020713000795040c00400d0b4a440d2a507000c00b803504c240880305401030f9801004140b02d542040308096400501c9040065070b8a260100310340251140c80d0818410200680e0780284c952419005003683c1301064009460131441a03100c40c2c45048060103500c00c185041d81c4110748036120a494134036144469007082005080c0171120000c05011400b01611070080c000c0401c22054000c0100d411406104880b01d02070f9190045002011200030700c00d64240a4284c1c = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 415954838 1250 415953588 415953623
    0x1110109050307030f090807030c06051b0703080a14040b090607150507020606010914150a051e03010e072a0809090405070510050a020c060c070302060a0c031d010206070c 75
    0x2020b803400c2882601c175298003040d04040105079184030303400f00d0480d0780070503030420110340440d034440280c65081c0780c02a60343d040070390b02c0c020003009590f4007c0741e8400c0e00303000010720441d04040c10320540b141d41c4800010004000c500040c2c00b0703502800201c1c2900b0402c0c2e001c9442c100004001c8184502c04a0844010703103130100c0c003112404c5400e000585c125004000856070302a444001400001120b40200c04405011a128112404140d02d42c00d8000130203508890007101920b801003200c80c2814140d141e80d0b45150810380080c421001300c1841f42000c070f882180140e0846041100382e542c0f452802c21443d44041c1c5080d0106801c3e03955150800140c622506c50000b02d03440740740500001c00000e4900401d2142000c3d011100e00700b003040c180020802d842e030110380c0078800f5004a030210346416070340020a0604400340d0000390f1150002031803928003a00503880220350b5001e611561300a100921780e12004500d0112000c2c01604100d00084180e406121014102c900a507084403554070002e = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 415956088 1250 415954838 415954843
    0x409021912050118031d011b030504080d031b0f0e04110909150109090504051c0815100804031b080a020a0b0a0e0601120f1707120c0503090111010905 66
    0x60304442049504500c0e0703007080c400c007401440b034113100b4001010741c003440030344006056206555407035402c1d1008402c00f42d202d80c8100901130541000b03943c8584009601d00c2e000e04998054400c080e0240108400a6a983c0c081d219920700c0094503a9058000f890300b0b003045440c1000500f41c1c0c014800d0907a6a900c0c95200c0c0d00c81c50008011310f9668951b902c04800800c0141400200361030359600b00104005820790b40315450f403044400350030020034140c5035440d045041046004a1040c070110030341c41c0109050b40004110300418042410150004080042c0a0100d042001d4035000c2100c82012030000392280d200d00003410214071502d01e02c0c00c0c01d80c1c2c42010760f038003540d1001c0c01a03010b1385800003030003e002c44140c1c000203949410008001d5154146848910500c00c460740484607038550b07400d0094421461060550100384c02e802c0040d5000304220642010348141d0f00700f15130140341c2050a019050105145422400440c1041600c000458451030400500301183d5207411010000034000c = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 415957338 1250 415956088 415956139
    0xd050312100303030b090709090e0f010509060f0c030c0a200d0216050117010b03060303190f0905060c0c04020901050f03011202041b0507120e0d141605010e040902 72
    0x188000400720391031818003d00b6500c414043e00c4c840e0401400703200000d0b4200502808a40c960b140102c2c0a5100d10340e11420501544112040c1d07500b401e040004038040410074a00c1082100307202d402c42d454050100c2c690340800c4a000021540800c10070455034000c1c2c020b03505214002090f1420b001d4846040b40c02c00d00b1400701ca40169101c0c50042c5000031600501c00c000d0714007031a1542402903122014180748006226041c1801000004030b8401c1c1c80a0040782c0503920307489081d41110000e14002481520001d102200040c0c5c0a02c0200301e900c2e0000842c3e481c0015440200b074121240c00800009500608605041c404100444160300d8110b102843c000c0208620240c2c090000d40107000641c0c48014014584440c1103005141c0c0c1a000350544100ca500075100003ea01e04014041d103140400c0076495512204070f22490003001103400e8903004224041d01034a85c80c0e000e080300c2d400101181c0c000d188c00b08003000608003007030078664443c445144c001042a03a02251000c20300350003051 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 415958588 1250 415957338 415957351
    0x4020d0f0f03030f1a0d060507091a0309011803020a03080709050d11040c2c0103090213020d110921100501060207031205030f0705070f020a0b071e03020c0d050312 72
    0x44420b41c5035a0004c052003070003001403000b42081761aa0065001900d4a0b24030540108103d584101040f09580300306110405441d0071003111070741c10100415003110b9027013200d03224000d600b0b0020b43e5466118180c2505803417a8150010445000329a8003034500c0300740201100d040202c42d44c80001c250342c668043c03404250080d0184180c0715200307800e2100795032040e94040c05004048903804491a940c00001c0070310340b80807060520001924004801030480541e000c1e40c003280d0341c62880c00035202d541c0182500f005088040051022200103c690381c0503844d90300e0340c0500d02c00e1454010301980c2c00148601a0b0560541d1480803007002d5890488a007a0030103001a40102824400c00682c281a512181c070941005821494603900d44640d80d00001c1000301040300101c1c020b410008810000582c82d03600812840c0c420391206405800764214500030b460b10100002c00d410a0a4000045040c0c2505940605121810b8105111003141401c0c1e04444a1008000b0300d50b11221401407d406040c = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 415959838 1250 415958588 415958591
    0x110f0315090712140108070608070509130b1e060a030f0209030703060504020111060f060d030216032004020903030d11040e0702030a08160206180a06061d0106020601060804020d0f0f0303 82
    0x602405001c003114200f84a020340075104c28014408004000b41020450b8190701c1e00c00c9103542c4640c0c01b1035040c01035000e902c0e007020b8218018400219141c210100707108042c0c8a21080e046042540c6900c010302d40c1703040750042c00c100f0056100602c6900400b8002c9008034002d4139265480c00800c0ca024032170b030b0003602c04c0e550b01e034140411981c2c400007121228002d200100030b80d041c00c00045021900203030565224140d1040003004250083c0030180580350101c80d48401c25999080c4100b0040c01e0b404290003440b1510720301f2290746424401d44441d008043d00071400c0150b05241200100284c8450200c041000c4c88005540100f43e0407c034490102035001e141c440c5100b01c0c01421400d4054102d02d002184801d003140039030341c000340c066400010b4a0051080040040c0c110341070000c600320281c111401c016020511030700014180b90401414010301752903aa03214030498490350b080c002e0b140040c100d0804a0058545500704113403503070040d05004001e030035550b00c00c2000c3ca0110340881c0030a = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 415961088 1250 415959838 415959857
    0xc0305090102012003042906010f1101020309070602010501050102030a12180212010f0c110d0c140304060513050402120a021e0703020c030705030f0a0311010b040c0504080705010201110f03150907 86
    0xb078502d01000f00300b4040c22680e408104200c043d0003540c0102300d141001404102030718841d118541401e842d1540500031556424040c641c070741c07284490300501c009036003428000a07942d4400002c4810521059544101c2400c580d54042c001c0d01c20600c00780d00c0e0004103d4680050f07503807030801e2480c941ca144000aa0110309048210030b40380c8800000b424042c9041105442120100700c0c0c030320821040c507085203d070007146820b01c05040300c20401001480301040200307907550400002c01e101c0741c00c40c405041d07031139031401004168859007014002a0843c2400310301d024181e60040c01d1403881c1040c00414400d00003640c00b081e074000320780039001680b084140e807915007000d1003803101524042e009030460030035001e011544e07140329910003003c1208442d90200800130a40c49011100030007041072002d80620100107080c0e42150007014180e00640c03c0001d420b40c014403900d0624446808403504040305000c607031109402c021318805e03445002d00c0206d0030554a0702c0c0081e100c2e0101c1c0d110700140c03 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 415962338 1250 415961088 415961093
    0x20a030e0901030b060f03100203102108090d05150f22020a0b0c07051c29040f020409020301052401170f10080a0c03060f0c0c030509010201200304 65
    0x103680c0220a0601800c107030300c01440840c00e0000c00903888a0b0a8400f4500400b03004082450101040b09000c039051005c401d11400e43d4000714180115808004201a5220840c02c0044405004040188100e004101c0c4000508215003610170705805001503900b8a5601c0d105c00e00b2400084401660b80320300981003000c180b58100215072101d034800c029206890081e40401c50750a0315000d200d51a103001301e62100030f44401c00840018020141004003010743e84800300f41e82d005484021600d090748140704880400c41d1041071042c0518040c0c03d01c00c542c0b526104d4000c01c00c54031805907005a110800074001d81c4017400381c5800f404802d2840c2900c007800c1c1c20b141c0303940214040d81904204110b51090001c94180b14203a40026030340c0d10b40d840c1d9440c0c4083c0c41e0908219a03000c1410f41c09140741600c1409018202607044070301a407000c0c0814003440c0e02c0402160f201c410440013060600706030301d001c24803a8000d85003840e0103000010740c00b0641c4d005140a0841000650280ca0000040004 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 415963588 1250 415962338 415962347
    0xb1903060501052856030f010501050313060c0c03260114120d02030703080a0e060a1a030f0a060f02120c03040c030b090c030c0a081005060a080d020a03 67
    0x71480e03c131a03400301d0b0650b092007040c1101d40d143c1c4144044030f101841c100f41c81d0f800c11032441800b841e204100c019511842509106100485c140445842045c010b81c40d4100c0d8104003242c0c0300360403405032124160700700782c01500c07140c0001d4140310700d160034240f034040010454416604500358540319a000c480f0320740f5005001ea1002c001c0d420542e10350082190103071146658090665100c1c44441e40d840304031001003000034a6486080c0602c0c49038001401025070044003c2140c50f0090b65880303010f130742d040c41c2c102c2130384c05944151095074014800140b00510681c000d100c3c44040c04910000a807101000038039100403141c000003680c106910390010050184101501008511030641c10040d0390070682000040040c40d24204010000014080000c5c03604c16030007031540034030710400b07034207107542d686594040c02e220315030091150a401c0c0d551450054640011100d0940c0240a075104680f01c1c507028140c06008280c00c00d01201c0c0c0450318079014030906420701d400ea4001d00f005038035400c0081 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 415964838 1250 415963588 415963609
    0x70b150307093b031306030b030610060e01090905070f18060906260403030506030c040506030c0609030c03030d02120a020a0507060b1809011b0201140a0b190306050105 74
    0x4504510300b00146208107074114148001e0040118001040f42510103500110007842c10321850b02d01000a01988481c503106480c400d8952994041010034800412300d5510801601d0205070250400000c1024602c030744040d4110346010f14240e0300032a940d01c8600300b40c4405851030720110302280640300e10141d0141405001100400c04444080d00c0c021000d003007613805011b100104101c55800d001c20100420b02c06070744a0708580c182e040c900d05410010001c3c00140c4e0071a00c01d00890b40740300c01c10329007409003501815004000c0c02c0282200810407845078052248030380c1500444216920a80d4284003404061001030000360340c0301c0ca00c0154000f40000101680125813060041c2e0307500640c0041912582c81d03014800150003a50200051440d844081101c2c0074070090720208010814190072100c039420700e035412104c4207411500164241c44c034800b1900c0f5800c02c9100011800210b5410003000c1d4a00989034002c0052031742c11140552500d03030000d41d00c030b41e1280010013082c00c0000d0800c = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 415966088 1250 415964838 415964849
    0x140f03040f050f062116020a0201020c0111011413021804050601120809031608060705072d050a060203060a0b043f03120c17010b0c03070b150307 64
    0x218502414075814018659950240e40c1c010a4a41c00e881400d4079444219401c40d48038110201e07080005080c1804210003c94403052140f40300c40543c0c80312030000900d5500c04e0b80c160054080d4070040ac00455100d02c40444500135503407030320280341c140220f152055005d00ea801020b0103095034107006101104e01d1a00f10564410507450420001c0780011a90038192036000303034090405842810401c00354016000c1c07241e4140250740c40010070308442c100c8181100c4400080e034945584201040d038090144d02d0340030344140036a040040c50440058020142c0c0d081c84000303a803030072020740c4449203815440d0200325000741e4004103102140ca0311a5911009045007141d440c03900c1d0410b207100e012513800d06071502c56030525035050804100d94500301808500ca02811980010030380c00c0041140901d001200b214070310303144040701200d100310005803480c6101104181640d18290740c0f20460f0b0711049004180e80401d020002c0064080c9514a00a0620b80101c031001040d020815080248580c0034 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 415967338 1250 415966088 415966093
    0x110102300c0f042106181406150105090315040c03050c220c030b100f1421040f020a0f030201121407110c19150c0b06060d0b0904140f 59
    0x441c10b49003102d00848040e25040c5500000d889510106000c0c1e0010a00d4018403142c1003031403009006c0b021503030791640c1502030a440310810036241c00752074071000c082d27455000040610844c50360a50281c00100213150f0060f045414542d061454040d05080954080b5940481d015041052100810403081154004c8800c0720407407600b001184c3c00990348203e144401e0740c84200601800d400303503000300070425000d80011040790f00d12a005084d003500f910303032101241901205600302458141526042d0f00002c40d50154400203072131103056900010300486c3c6050290010400684034040044000d051225030101054210310014101011720b93f4401141490015803060b41e48402d580380360010128240308100305103405149080001c0c0440341ca4002d0b90780c1c3c100301e0714105050400012039640d00b100b100d01500d204412038081001481c090980c4c1c040e04085006803230154000d124040e504200007a1100300000441c65105080f01c00f03540c110805054202a030754203122030149160604003 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 415968588 1250 415967338 415967347
    0xa030e1225050c04110a11010501050d03030e160801061a120123030f030a0f2c0a03060f05012c01230a03050a021009060f110102300c 59
    0x212600600301d6900c0740d0001a040072031001803000a00c00481e0252019100703200c0070100403403c01003a40000b40e00800104500400190f0040601c9041e0580702d00500c0702585070000d8404601404070010800042e000305d03038901700f0b025125440507006114500c004268945840e4407000c1d20280c1016010980804120040030010664012070546403905a00c0a410340242a1406280c85c0d1500340c942611134000641708988000000c0c05110303540703a4841a2070150a18102c41100e12b80342520401d01e41c00140305407440e904186041c0c00c8902802c5402d401d5640d486000c1900c001048034860990341b60010700040000c65080c2d800080e21101c080804240041e04980144052043e00c101441c2c2d09061290109243c441c80444c50b402840241801c0e181d040080d11a68141012486203481c00c80c1913802c140510035000440b0700c0c030380350600c03501400702040c0c481052160300814255820420300b012000400103400d020a54201c510b4400000c01c3d6000e04d005502a00c4803203417903c00e00 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 415969838 1250 415968588 415968607
    0x91203090c13020f04030c090c030e0307060209150d02190807020c09060406051503091b01080604090507090f020c010524060a1704030c0b060111060610050f0a030e12 73
    0x9000c164418040da03020001107503600c28a0028010300301c84c292070703d07070018001050102d42e0412400340d542c41c07842001b01c0c1c220302c503050341141c070000859020354105000c100c02040075030780504100c0c0d030064510102e1421420050803d940b2139925000881d07800700d080d48640b1800340c0600c100205500b803c01a40c10400c0c0069501c54104407d103108040c2e040004034a51610b0f00028020500501400d03a240d00860b01038400b60411034003052039100315011046058505480c0c0180343c07204ac0c5641c2c50303c3c2c1307031074042c0b1001e0180314505840328800d010000604000b07030710405040d2040a8001a1100300211480f400c0d100c01610f500c0c0d40c8803503003030800c01d900f81510380902043c2d400c40e01076954a803150b070103503a03c0202c81120302402e41c4042c100410316400c81c600358122442803400e0155a91800019902d5802d218a080f00f03540c8201d0000d030719800e04e080c5e03401300021280cc050f07007409100d1503507061980c8460302c08000a501d640681c2010642041613821003507020fa41d583c240340584 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 415971088 1250 415969838 415969843
    0x721082a070c0303121503110301090b04080918100b031012030302030114010813060e0a200a05030d0806040c05040b0a0201050403120c020c0906030f1509120309 71
    0xd040300802451000035200d1400400000c065082550300e80c03151640c1441c200804000c031140700507004221800800403180780144200a8a000121200038010317003580c44107400304101d800c041d41c156590340c1318903002c50100360703905104520070600b19690340711800a108010030125401e01c04483c080080c400c200740f0300501042901d0a4002c0070742c40765101801c900c955205035001c07005080510302140289070f4103070000c0d41a035100c070315039420300d41403000111800901142c240100850018900f0005030050f044000d003004030500320351a44d10b0700d8584041500c00c0c540e08841e022610580c602041c2010448200184411006807400562241010f800000000d05151117565500c030440100b5001d8000d030b41c00f500c92840895218002c118000c0d0080c0805d850507004100000d020202800e0300d40601c410000c020341c090401c0940e15400e11101c10360103170849034075004040d84521380000c20440d020141d060b1620322280c90411001c02c5051103400c1c911040c0d090f03420401c00c41440c100 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 415972338 1250 415971088 415971091
    0x5012102070f0f120207050a03020112091104020c1507020a052509060e0a05010b0f070305070c091e18021806011211251e050106081002072108 63
    0x1800359031140035280ca807140c400c1d80c8400505000b100700240050120030000400c003100603400700c5684903200d0781040060603551000a0001d500d4031201c107000003d940042c2e4440d4481c1007010a200c400000090581c0c100d94548103095120050000a62011b065036980095003400075048405103134582580303891502020170810103408041140081c000b0850800030060307400b00708400754581506140d580825186210024100000802d180d0380c440c0031110098021035582d40350010903a000c1d541c036040004107440d10034005c0f01c000703a2800316001d54110040d41001400030340266100100071200b0b441404c0f0b00b01d4246601c407500503110b101150200c031640c03d020b03440d103a8681e0012607922030ba4401d00c200103401c007050a07040758207034001707028484043d50030302544035465010174258454041028016501038154100000300701710b074481d9118001c000100d80d10b500c4440251501c1544101111000d078005400024880c44160030030200d040e42c80427005d6900700c40e5000781310200 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 415973588 1250 415972338 415972397
    0x91b0304021009080a08190f09091802060a030e1605060301050f03100f0b010917030a030903090914010f0506030f01180603050111130f0807120201111e070501 70
    0xb54000d80184581c003e0100400500e5424101c0b00708018501d0200c0782074004061000e0403240f03542500c0300c00da01507200c4a140c404540d489510300351416450001506041c00703002e1000c080c4030840805078868400400d40c43c406628007082401204041e140b8010035500103d11391401c0170818044c0d9522001101d0444408603a40810b04aa903000a41464419002002c2d01840d15070340d07250b0b524081e080f0340e104041c01d8880407120350f038401e002c0c581e01c07101d8111500250010050400700074000d500684841d4080e01c1c2100d40d07e0b031a8000c41d405c96454800c00c15410b00c140004110210018000c4405417005036240b9013907052205050207004418000d182c0341d40c1d41442101c0c201c03241c9502820046400cc0006c1c00118038801d160855540190304c45201500b07000008942020b040b40440c0840b20841d0041450f503141c110010b45111003101b089040004071700318141c80030b0f810040c0c40342151a0254012540d4000c4000700d207030080ca540410b0601c0007100603100383c0c0402000360b001e244c0707 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 415974838 1250 415973588 415973599
    0x8060412030b0103021b07090c030e190f02060403060501050906010e060306010c031116030b0702010506100804020402190e010e0102160e04081e030901140c040306021305060d0902091b030402 84
    0x2c4000059010740220b49058840b90340c0c621100e10000400602002160444181040307031603080c9000301c042d1182e42802c0070543e4400ba1030b01c00001c1c01c0180814549014040510000d1103030390000d403655001e070f402603689580715001071203249008000503070803002c2400c00000c040300001c0420041c0c0401040c182c1032280c0300070034809041c001c0c40c0d01d845c03580140e0141c5401003407884020840d0f0426000682d80c1a1707170480001ca0540c014801c8034003c4d1002812030140240035039040740d0803180240100e030416024800611030801d09011440b1000ba1034581c000309100c0d01000526104106404504541c4400c0400c0d80e07811284a0b401d056815111841e202d079611820300383c0c1c051081015000c1513000c413480122020401f10040c41c024164100280110a0400183c081d032030b600f80c0c0e14002d400400c0008200180e000e178001e00014849910b0f12200076035890020784a40c01c000e0030b400069490300d100c00118074203801801c3d40244c0d030007600b030310701c7c10002c405030302e5030000910090180 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 415976088 1250 415974838 415974851
    0x140c060f1b16030311010b04060909050c04140f0403030b0d230a1112030403050610030209160e040f1404080a0f0302120106180f0b1804020702030d1d06070f030206010806041203 78
    0x105170030340004046040c042e02c1404040e84e215081c02c01402e1200041d1118000c0c42610442031030705014842c4006500c0b03803c01171548440380000c80c0340502501c210b0500d5a1158407060503101c1c14903288006000304015411440d00804040740d0300707603881110415820200d008800500c4807070003c0000b04080d245003140030411a20b5502e98820b503000982103118200400062654a41d46041a40e00c29901501940c440c010b4400142301c1011641c0081800c8010a10b180c0c189903004c50300e0745402d100049170b164250038940e001c40703805407030039100014001040d1241c607400c4a0f1b5008920f46925046113024145805070802400600807041042810801500c41966940d5060050503407080c0f80200d040d6119001e50881e44006003c7c60401c0d845040e01e142d80c40d113482514200ca4014015000c004c00341302084440d41c10541d024014009030411241580d25031170042c2c42d0852040401e800c0a56103030401a14081050380425682c3c0d0003081000b0000c0e0312f42801c0d200082040c100030445 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 415977338 1250 415976088 415976117
    0x103140a060f0b0f06040807030201031e09030804121d06090301021209060a1a01021b0303041502061e01030507060c0611180a060806060403140c060f1b160303 70
    0x100103a512000d840300d402c1495004808440354001c0810443c01c03952151340300f000f0000d1180c1c90045101f010f8458200070700400141d4000d800240c409440c00070fa014101046031750b000102e03070480c0c009800156a0300100410030050f45003580ca44800c1d803d0866245810603c4501c0110107844040d0140c0c2e4007140074840303030301c00350140c400c11102040420400c1c82d010208964400e01100d0f41c0e5121401c050850346100b0810008401004061340505100b00d2a0900d003800c030042844810703050321040100140002c00b001480381000704031343c042d10650421102050b18541522444203080d50910010000103030001000d900b2100e041c101840c103e42641092002850120711403443c140e40042c164684100e150712030780c000b03031046417207034206e989072a404c986d1503404590a0340c01c890100021301c04200240c1010500005d1201216207248a600100d04160001860007005100104420002001e10611188410704400003031052002c0c040300c80560102500c030280c10700050100303100f00c = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 415978588 1250 415977338 415977343
    0xf09071a0f0309150c120112050c13060920070f1109190507030c09120f062406030207080a4a01080105150a05070f052a09010314 57
    0x2941400489040c2e100e20b0309415090710340c04520758041041803910005120f510064040d40da19803041c180c2030710140c1c00c11010301c03403034610103100783d4452007000208081c40d5600b14003010706400c030300d4010580d0b52816090906444014260304501c01e9020409a80c0240c40702c150b03448190450300c1c01a10b040075040408107640c242d088190030545010401560000d00301ca481c01c104001c4901300701e1a9035100c011411115082092000190000e008112004240391405007460041072400f15081c501c0d03584004541424070304407036101d0644090740300d080807002008002c00c00750a0030f5151980c05da50743d103801d00c10750860006120303c00f259070400e050000c424010120b40780e8208000c400000f01205025984034000c8401e1500b45508a0740551050b40b109040f00c601030210003c5002411400715150401410401000024003425020802154015004a0040c009415040d80c0c60030500340549022083c01481c1c0380c07080c1e00043c240c5482082c5411290440421803007211301c11511070 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 415979838 1250 415978588 415978597
    0x1e0d0206160606141c050606010e0307090608010506150f04091e0c03051009110f220f05030d09120b060604170106050f09010b042102040c03140f09071a 67
    0xa111928001000ca0451358210b051290340c1422603112801c1c20740b00b0701e500c50340d50408100a0150304008041403441d4099035400c03500701d500805507140c030354440008108981a5074400c0409030345440901143d0b0920782040740701452000d00c618a06500f15400034807500c00c03481036001c038590310075028120701d4444038120f07080703070700340da0244082c854080c40180030b0401030f5044c0a4020701c43c0000114283e2502c40e82005075400681c20b03080940f0035641c40c65a4100c82c5001607590748200d00100e000c3e0004a0f00300103000c400822007080c609200625140560701417615081c844441014041c0e410603421030320400ba40b050a08103944d4484020682038041c9610212401080204080d031101c01900144240e43c015a8030f410b4200010041044601e020b101d0355500160400081c4450340382501141c0080c0003101c8042092400c1d40e02181c200c541e4900e000f030009940c0c45c04d191894050040b0a90802038011501e400747c2464581702b070f200c2c80c04c0d11883c184002011600e4128407120701c140c4 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 415981088 1250 415979838 415979843
    0x30a02060304261801080c070606031b0e010b0d0c0c02030706050c12040303080708130219060809010608030d150e0906090601080118030c030509120c1e0d020616 71
    0x140c0741c0c140b924140076903c1d000d01ca002000c10001c1c595071480108a070607507400150000040f1030f0701c91070074015211140c02030181e150100c4200f140d000030800d84c1c00307100000d501c00c5000a4200c4c90004074001c4404060b001780eaa6680400010082c1241c11020ba030140b1944040001307410502d800305455948001c40000d400d4040c401c0c00084035a0410090615620408169a00003c191120040c1d511031800300070080f5040704041500c640c41452203650210035080c5c1460300c410140c0009240c030034038101010392122100030034050705900c0512a900049080020f00020782420603c94490140c400006206569400001e6082c80000c41c0301d4018500f00c110982070381400204070792150400c441c14015807040000010b880e085c144a14075001c5504a510042400c0300c0d40c00700e03162034030700d0700580402c40e0501807400700b07945280c0c500c50180b034050000c0040e12188410b00c01c45d110303240007406882d809507220200c1c03512000508a00300d80d0499003141d5418248481000954000002 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 415982338 1250 415981088 415981099
    0x11412010609090f060302030312060d061a0f0409170d0b060c0a11030303190c030605060c010509010c020d0215090111040611011406030c040506031e0a12051e0306030a02 75
    0x240c01c98000360500d0a0700c0c0210350611800080c100c0d1002921240d1000941551040100d10f5220503030814840d000400104000f4200c2044d803181c0c0c041d60300d6007400c00d60b10030184155100515202201104119003510207102c06100741e140d0420f40c0000540520640000080da0f0080000981c004210040020003203910340094800c05a604e40c0c0c4d0703050444102c07402c001c03010354038a00001541c2c445d90500d00d02109450086076984050444404403909241d10350700045910f5460b800a01040c4184200008840c50400e812600303403500e100170001950080c11410940750f60128580c0303049a01b10103d10065100d0410990043c20800881287c4c5c00c00410b000c00e0450b40810701c009204895402070254003518101591505400c0d200f269040d80800610701c100d00389031300003552000004050701c9410038680071303819007036002d05900c81003600300041c01e404010b004c1c1076080e02c116562138078500b812a22202d00205042c8040403600712400800095929603041040d80003060b8080c01 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 415983588 1250 415982338 415982341
    0x10f0e010e060409050f0106140a0f0f120f020d03030203190605010e0d0c0f03080703021203070e0904020a180b04060902090f090c0903030f0d18051009060b12071d090c011412 77
    0x45211842d2500c1803c1ca105c1c1c0ac1c2c02d540003502c0c0d80340e0320020040e10a4001c880716002c0c5060720707561802c500d83c0d204940301c0391032801d070201598452142c08980c034041d40300941d803450101d0b00c48041104c150109000e66140c10801d11185e6030000000d00045019075420b0340490842c200158010510307484010b504c8800306005c010440640b0140c9180d42c826021106041c1b80d8400c000041c0c041203508a00190307281040b4000c52904591f07040d0004d00203403d40400d00c3e19014001030170300360288001c1d400781d11060058407904185c4103100040420b0f010840c101007402000900020702c011403135214030382d40030101c0d400111040c1103454405004084a6441001460095039504903400314005a0325240440d2034000443c0414000e1f10346c890b001d881d03c070107031000e284010a5480d1095034507644d26103040740d0b50344480e0a140150000b440040840741c0c030b0102061020f9207062864601801c0d00f0041c4494440001800c04070701c18242040104c40103046010301d03d90082c810b486105005030380 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 415984838 1250 415983588 415983599
    0x9060c0118020909070315050403050c0109140c040504020d0602030c04120303060f060807080f07020703140c04051f0302061c090c170111040506030a090c090203010f0e010e060409050f0106 83
    0x19081107502d20a030b4248049039140d10300719480380300c81e1001400244950340d07400b032500c42d1a03111f03d034858864180207040030294850f0f03d0840c3c0d6201c20440d0700e50328078448840030000800030f140e6104030442e8280000e103032503404103071307032803030310300008001c02c0e0044017140d22114108260b50140c00352a08a401d1030129080082c080c0c6134600c900d002c0640741031000b00e4070b20b20a50080d480f881050301c420b180360310340210082018000408a6046015684003c00002c0c102820640c4051040d0024401d141c3c001080008982d4003825020115206101440a0700e8035110b00f041201e80440d000d686840c41840d100181e0801d4400215109182ca00d118041103802a101e00c242c030506441c9180c4540c0c2c4409035400c9800c0c000350b002c810705080c0410006448c10b40c00842c0c2c4070b8103031076000c550b030005075840881440c925004201c00723035000301c014004084040f052000901d03010610341203551400c0ca60701c0807141d002e0600c502803520788850788107015041000048074a200b030020451980d440 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 415986088 1250 415984838 415984871
    0x40c170a060e07082a062d030c0901270602010207050c0118060e06040b0d050a05060102121602030f1c020111040509040f03170108010b03010f0218060309071805041109100b09060c01 80
    0x182c20501159507040c4202c6d001005d171fa01504e1082e02d80d89001407a1091840041d140c0ea0380002001c00c24882254001180380c041141c024000c100b80e400240e1203440703910f04103060404000c180c50400c00101d071031003003180d503520f81c0c0c0302229050b08001c0407116030304000c0350551069411900000c00000f81c940d804a200f50300440c41071440210030800e42d1145401242c44080c030099032443c862040c000e0002180c1c4455a566450b480201110200c2903c4101c2c81d05129050104a070304081d40c483d00c00780b0755020300035401074100d26221185850704040020304800d9001e00040e081c00390b032204000400d0700038514100444041c441d0f00c501c541e581d280041c043c1100c000d0941c013950a040384581c01c0c00007030080d80d00103000c54402901c045c80603400c0c02000d030802001c40001c1e00c19520005110349141e40603005510804c000400e682c541030a09103410803940a070103028030051020040d515911080b0001a81c000f07000c0c059031030215100080c0140194000c4c481c09501e40b103075211454400 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 415987338 1250 415986088 415986127
    0xa020f01091a090c01050d020c0304080a06051605040303050a271502010606140a08041a01080a1202030a09091508031603030e0a050d08040c170a060e07082a06 70
    0x112054200b0b6644641c001910b5003207000d00203010600c1070000d2509408560003900e544100482100e0410741d59440e110704c1c004059806603216680c803400d0202c03205038444009003040d501c2c01c1044c80d20740382d5030707005040f40700710010a0704004201854500808002406401d25000117a90070b41560f1140c40c850381c080742d03400550000d5864140005009809a940410a003250703640b182d0a004140009035940d150041040794018000044009203107908075425011701902c400501115040e440e141444400b0189440c0941d40300b1700044820079405030540050702d0013042c01150301c48248840c0ca01612064111302018040400e47e040e402021242840803035000b9503003404090340c107640139511104404409000380c1c226082884210b801021829045480340d0244060240d0700e1082c1c001410b0403825501c1c2d01c0d044400d0207002d128450103181307200120341020300826454040034582d50b1003062000c02c550210285807034800c5c044040b00e10a0300f103011702142c0d81e40d8042c07403414140014 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 415988588 1250 415987338 415987373
    0x12f010b0301150302090604060f0e04020108070e0306070e130207050102030613090c091e020a0e04050610020a0215070501050c04150c030c06180602180405060f060f0a020f0109 78
    0xe4402504518a4140603d443d0ba529890710009500c0c196020310102030b01c01016290001c0d2100c1000034020b1408103000c0c02090070000c0ca80007420b00b0b1000400300c4601a250804000d00003603aaa0b00e5900400d00b950409403d04200004121010109400444890f4911400b070310108441c0309004043d00118814102140c41c0c00c030070301d10070814400300d6144980141528200a5080c000f000d00c0c2d40c07045806503540c44809060351705104080c42039030300901c4070a000590140200c030a44c01e01d401a650081c008981641c1c036071100785002907860003940d0010b0b100ba2280b6281d0960340f0071000844495540040080c0654901820380c004554002d1143c1000084064200d100451217800d48125203a0315548800741302404d91904c0000d80079100110b0b4004508114100000e4000e100030480d0031650303060052015540d41c10001113440080029000f040c0200b9401615030711041280c0810b00c140802c0c03902c0d105c1c0e003c0100e02d0041d03150b00402030380d0f10780a445000d0000c03400411b003d000 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 415989838 1250 415988588 415988591
    0xd111c060501050303310819030e0a03171c02040905010614030405030405010e030c0306071d030106080c060310030b09030409050a02091e06070c0f03021005071e02012f01 75
    0xb41c0e203d040c540d5903c00c144800c032074150350944200b040c0807680b4007070280402c560000751040d6113a00c00b507400c1c80c1c060840314032041c4424005104141e00292001101007003141ea8103001f074950f864404030150350084000e282000000d000805004a4a410183d0f00da90f41007103444644480080006000a0040c000444c64514247d45409a5041102c8c41164007102543c01c0c9480c120054410b154241036941d0b150290011000140c0c07008c0080c6482100c5230f582d40c44101450f0006142c0b80030300030710b40d9030080c1d0500005000c4c500c800500348050040940300b0540c0c80d56212840070105006402c020500341014080c408601400000f4006035218408204031a0f210440d41e0b00c220300ca036070b101c2a0011a801c5110048083d10b0401d220707c440d001d01301500c1d040b880c0e90703801c5410045c2e4000800c0354050035028030a500702110900902d070614240b46142090a40f14942c0b050381e0a0f1307071000341d400c002c82884211b92154018103581c008841000c00c104c00c2900c10500159031400c0c8603085903 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 415991088 1250 415989838 415989841
    0x303060a080a0312231513060e13020d021e09060402090d0201121b081b0903070e190203010905070e030106320a030f030e01020106140d111c0605 64
    0x11202090002c10305905071903100265010700d9494002c2c01644849441d15848040100c00002c00340701900c2c442d2030741040207101c6110150411130701c0c2d122007200030480342c80c3c0042403105958400341d07903800c0a6007000d010558401e40c03001690300c8244801c02500940c042e03002045040071440b034044880000c41e11404141d035035a09201c01c90140c00600340c1e02c0141181c0c240050350050128072984614010049100200022032620b2910518403400000320f2900800a00c400404031180440102ba50b00d6807410150b00e00180d0768121900511031248480004039150000503100c114803d4000384003903449680d107542001c0100021180703070002c103502800550040c0350610942d01500e4007081030000d008140c0c1014a0341c0304031040501d640090001c10303d099903880d41c00c08002144185a0380f00d00001603d0010080220a00303503605584c14140284803020311001d07507200694045e07030b8540e151041800c02c00d0440040000d420f400c280740c1c90461240240c02542207440030b0060f241072000f03 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 415992338 1250 415991088 415991099
    0x70308070201050609040f0605040311031602090c030403020d0f020f0a06020d0e1c05070201050c1e120a0e120c2805150d0b030a0507061d01030504030c0803130f050303060a 76
    0x101744040320001c1183c882c0403401c00024250b5803100b60054003a28103030000406252301d01c5d14691062a05400b200300000d6103104500d46244100d41c0400c402c41c1caa0704500f09650081e40d0340c24051282014031840389002448107108009007840322030050100c440304116410150000c1d800000703036160f001c4c20140040c3d5010000505014440c40b50f8040000302d0303400f800d00700c0e03d81d00010422810001c040000c899441420007040301070b201042e9621b2482e04091207d60301d0040c00d250340901c4c8500c2407081030492a04183c1c131400111054503040001445c40348203d040c4640100d03000d03404040c1d0000440000d40310403200405001842c3e441c040301d511381c000c00084108140c00003910b130000f00005040c002c21034004003000725000d070403201040140c1d590f00f4108200e5400250000c1d08001c00d00d000c0011500081d2143e8000303080802180c01c03d910010305601703543e20050650003001010901ea07050704805510042d41240090362590762030303c0c1440d240d42c0181c071018412140044003140 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 415993588 1250 415992338 415992349
    0xc070918051f0b06070203100203070302040b130e07020f150a09060f0b01230d0921020303150f030d08100909033504060c03060b0c030a0201050702030903070b0f09060703080702010506 81
    0x2180d8001f002000210712040304403020b948020441810140c0034000062000c80b064040c204001e400c03210f41d1809810b00540c00c0680a00600d1942190300008c5204c004080204402c070120202000b000c00035a100342c0d102c4040c0900140007824035141405010000700d00342e01070900010241c5c0c84048981c80e41e40c0d140b04580500000241c425420044180f0f00760b12a408030890030300ca0000c14818281103a41d0300303002060f6191200150300000104980c9032400c00c24010803403402c1b0340030310b4022200c0c8046951018a4400720062014000108105070515082407000740324030141400044410315008000c1003a02c0642c0c0075081d1101c14048583c1c0c0d90244030713900502e204030038040e1543c031a16480050103410b1910350a042d0b407941c0128050300c0c80d4000b132001d954003000455a964208600901f1907200074000e40454000b0300800c05030381c2d0041082002c8400164003140c49000d04a988040c910645440c954060070000b0924101908113042d507100701b1294000300030a0360360000f40071 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 415994838 1250 415993588 415993597
    0x1170408070f121d031b0d02031c0206011e240c0b090a1a01080a080f0708030c030405100504020102120d060b030a0617030315060c100906051006050c070918051f0b06 73
    0x15051442400540098103200d611f45000d140010300300e0743c01180d22282402e808410316140300040c0c0000c80144052145d000c1140e0313007060030500e800c2d6014502500d042000081081805018540c160300f844900e1213518928031240d00880800301a08010003599618130303850004039500d0f1000807001d003a80300c120750390070704880d0355901500c0d9542c107170754407490706a00040c2c4c0802621814812100442d854402640c42600b039a06034030340da824541419841c00440c04141201141040d0812005076804680312503800b0002c0070140d01e440150f40d112004d002141c00041d1184404410000c05600d96002030044407141401d80c00c0e802c3d0000d5025451348000c890801070f1010804090742c0c6400c1001c000d0420441c03140954000805030708030b0f0402c1e5020414292400b94503101800170030380007030710351301d000740224108646042c0310703e521662030b20110b2140d2483c091f80c1d07000203110303880ca801c0030709045a4818243d0b07082407961003044603501d032141c0c1c6100d049490420168418100b410458 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 415996088 1250 415994838 415994863
    0x5030f070e2a0a03060306060902030405071a0d020d02070308100605070210030b030118020109051806090402010c150f0b0901120605070201020415170601170408070f121d03 76
    0x11107203a480039080100b1001454240a002075140350390301c100d00b405009070141c00480daa01082c0d10703295007410320a40b84a03410000c000b80c07042090100090700016120115a1000d070349003d00e60544c0c0091401d4011501015011030001034208080c00c0035a0080080714401d4440c00c0c003d0301c2c0d0f80c4004020310075a0041e400400c01c1007000c2070244c58204401c1400320198600414408041000b0030b003560f440c0b5482c0080b002c90300e03008004568000002030090b08050b01c8080001209100389400210050030541c0100341242c00b050a6910406804030402c5d00480f07481812842c44003a40000c024044a4050580c03400c00d1082072032074181d044070304031030001901c0341c00e105c10b54950800602e4050301210a5640c02c100004041c0746601810148140d1a00c1e42014403055003012026030000a1006042000d061800c8400720721240a050300103030484081601c40384c0500c0c0c08003010071a07420251402c5e02c4403005040e0310b9070000d01e002040e0319641c84030324004c0d006010301d55100ea00e83c645 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 415997338 1250 415996088 415996109
    0x6070615080a020d080f07020d0302060901060e0601090b16020904140105010905010302060d05070c1b0e0a050603120703090b0d0f0e0606010e0111030d090b010503070b09030d08150a06030605030f07 87
    0x4c0d0400b158600010f0081b010184008501d000425030018182c49891503041700960007007820018209420312400c1c005280d5811200f21030710307001000805211090054110605011074031075503098005441e100010b6001e05035030315504060274215408801405090003d40c00c0030000306540030f01d400303400d04803a4060302082c28049400c5400001c1c1800401c45003c00021000880120301804110741c0c49200340d800d00da000c5401d04080502020000300160440740c18003080c040203450000317000030224401450306071901c00074034003210f0743e01959001c0b40b0a5440403c0005160410340e00c01a417561108004000749a0700160f16521488225009404100c650b802c03030030b255024007079511030b0407802006d803413030103600461820841e142c0c03040550744208080e0052210342420060740c0701410b2140b00c00e07410b181032100000d548240c1124145c041015100120b925500141003804490900409010352103466400040052913a4890b0620a2054810300d0103100e2010945009440e4910b40 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 415998588 1250 415997338 415997359
    0x22080409050921030a140108070509091c020d030614011d01091d070206010f23040b0612040507120f06180c0602010c0f110303131106070615080a02 65
    0x605008004240b03c0c000c0b0381c0860b224a101600e49242e540b500d9045580f40c0c188a080d49089807590710100340d40f020680018000450002400000c4410403140d241881d0b035010b810f1401d11440d8501e20701900c0301c003800b104400d80c01060b000c0700c140582d5010440981c2d80c5044001c0303088031817242804501e400740020041946005917a08c807003018100640203559440d284c0c0ea080300640d812903000342e0080c1c00d000305694107110103401032000440040a035410300345440403d03a43c01d0125143d6613002c00b905c031400d446a410034480100000c01031515900c0c1400d059a072144220b804603150b010f03040340454800c020344041098035070001c51011043c95941c0c3c2c1c50004020081c201e1351031484080120000500c40420080a40580da0022403c5083d068015003440010b440035410302070307c00c1441202d0100041a42da1024035842c8000c502c845d90300308103c0b1003c8401003103400c01400680c0c0c1d4207000d83c40c1c202c981240c4200700c46441e05a5603056244e20340d08000402035000442c41d4 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 415999838 1250 415998588 415998599
    0x5010212030f040f060b060f0c10141303090b03040b0405010c0f021510030f0f030305090a020f040b0a0504060602071e0503071a0f0301032a14010f0c1703220804 71
    0x1114081c44e24860040014100c3d0120006005070b044007030440000c6000182d0300d00810000d002388a41100700110610130610940001c00705404010030262142014507402d000345446a40e102c4000c0418a0f58642e80e410715050020308050200d0701078595608001c0c400c00c00c2c91044000180d444107a5001c4c04607001280c116126031800a0240200140c0080d00880490400208a002240b10702c0d404142800c4624018099810091124801d60044046400903071140c092201402d0412a40010f04802840001c0c107c500c0b103810568100340341c84000700d6141e030001740c210151541405c3e041810702300350f00140d204501c98064540c00d500042003c1141044500c01e0300c3d1050102d070713480c0742405002980800560801d074006d5804580300b110409080c80b446031720060044101d0996041942403203005401c1c0090408402d040010049410340014400e1400708061075000b03401d20046554040300d845c09030800e440c050b0031f044080b400d100c2301c1a120039440304480d0340145013904003403400c07 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 416001088 1250 415999838 415999853
    0xd09061b060e0f0a0b0a020a090312031404080a0908210c0717060601030c26180109060b1c0c09021b01020a030618020703050301050f011e050405010212030f04 70
    0x180e20841d10340c0d4440345021010360091001510540691008040740481c604100e0090400549064a4540304210480416600003060360a50ba0001c40c04400c0c5014014104c0051500c8000c91100e0441c0c8014402003203140340080007035058039581c078005d076074651880030784466001a420f0682c40300c000140710480d880c0c0d009840c0d140c54481c1a21103040d5222502c01e82c0e0310503010f4030a0b164000f0b0003000a90b60f014450a130407584c0620f13041110000c104181e184880c2d800c040d10111096003000a06206401203070b901040304400009c0c000c1d906507250100c09400f29114591040002c3d410304040b08200d104000d4100350004203030340540e8500544d240082d03000e0021400410020345207601c500000340000d2a0341f02050b6030006a140ca06148201200c2485580700c10031801008808082648074050300d0546000f01c409519180021006a901c54a02e0f00d1203043c6149040c41420020340140241c03089480a8003540c400701891071542c0c800344130071504603241810580110340444d400 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 416002338 1250 416001088 416001137
    0x15041704120b1f0806271011092d1203180f0405010b1306030e070e0a02070c170c01090e0f04020111011503050c060301030302061f0f031101020d0906 66
    0x40308008880380190f04074882c02c4605030340105220794004028080b0445400f031079440e0345085460003142c818001c1e2a0161101c091090140101d80c070750107500075020036103040351801c0c040200482c805042d14036045041c0400c10303070419080030a0200350109030500300607440104001c88013651070100d0700d01e0b040d40200303802c1c40c50a401c51800140468a5210f5104040c0030308040c51000d07444800314401100d83e1038107500048101828892004000000007904005480b600324100380311b60349101c96400240280c1c07101500c994040c040c0016009070f0070704014203150828081c1d0302c07801e20b400010b480450451140b83c82500c0100009080b1003224003a00e60010b20500d0900b88180840600c01d003511008420700d40da040313a4600c01c00801200b04444800914150382e01ca00b15031460700d02940384c0f9002482040d400fa4000042944500d10b810420050516540c030b8014441d22410040d0280514501c61801751044005100783e02d8002c104a8084039001d9075114014080a40141e40b00c0c1c0e43d = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 416003588 1250 416002338 416002351
    0xa1119020c03010203190e0a0203030307050c0a06090305070203070f0b12040f021305060a090908030a0905031204060b040b04050402030d0f260403031d0604020d110315041704120b 79
    0x9020048016503000e000a50041074103501d002c6c0e1800d1044801002c0341d03080d03c0110313402d51044034603400684010041c0c95100134281002500c030412142d0050170310300403000043c181c6103442410010550000301030030200d03000b0b9040f240b507640c0322144070401d500140900222103c041c003514610340d02c4041ca01e076020b03204001100400169030b0208807c400d0016078402c0d61034442041104c64205074602800a001464051080511076200c1410a12026000e40103d0741c5034501d800620004204581a000e003441d800e8009140608114004100903040c3c036214904028001515207803501940317000b25001800307030068442d03079201900c00100310410b85d410310900032040301c80010158101c40c4004081074007150546000d2800500711030510142d501000e14110424030319030000120745a02c16415a108803c502e40b500384006007681d0291055403500c188501203058801b4510064042d0b4442e00c80e250881e00a900c12008034001c03030045014200079094018003142107100120340200 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 416004838 1250 416003588 416003593
    0x20607080409020c2a010509100e100203190f120c1202040905040218010f06050a0c0804060507050106050907120b0402090306010e041104050f04120908010203090d080a111902 77
    0x81e6038242e104281e8000106003c001e40141c100b010380340c16100c4c040382d0610044044410b14888400010b000750154001060165202e16040c1d01c60700d0041540300d132500c1004164038841c03614458000d540750700c20030500c0e6220242142660119000740b00b40950b5110f01c0d22140d0b40c03017508020800082060582440030003015008991010080c0d00c0103101034a0308002c0450903141034010310142049500f050150003c40d0001042030301c2c0403030b007214156102131525a0703480044c01c104a9000807901c0c000b0f0300c032001c001400103440341c000b0001c201d000e100c0c6009004803a6a04208441064115011004140c0200c42d58450044580c000101c515008000609029806002c280f4100c001d070020100703001488140414805248400075070304d002100c080c41146800c2e040109005006040201312400034400d500086003e00740c0e50019000140003151a443d1440300e50360b4543c040c17811030011481080204c1d904004900800d185030340c0b013031482e6282000811861051000c0100e3320801c50 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 416006088 1250 416004838 416004847
    0x1507080703021e0d0606020c0603041a04030e1c02030618070b0906070b0a140a05010308040e060402090d0c06110c030c01050a0c080a050414010f080f06030109050a0c15050f0702060708 81
    0x41c1c00d032001400303444564410004140341040e0007c1d28010410710000c0c403607101071041200054104240081c07406200010406540b240d18040ea107003045812040d42c4030050f0b4080c0c10306280fa403802840c205000710b04a8117170b500e0308503003494803030184260224507411020040c00b00c5c07401280200116540904010719018441e22000c00020090b207440389103a440703402d50600c00c12603100780d039004410120b080220354950360700c40c1141d202d0f500c101111004200000390365907031203505a03203030b914010342002024a0107160200b4144440e028401c08140c04d890400940c440c001100f160303540c2c01400810444010381e005581c03640150b40110308110310040c00c040020b001001400c90b8080c1500e0f403903180d07030424000c4483c446055196a042084560f0040701d01980005031980100c010b45085080e42c40d0080803c0c054504030401424a10804c00101c0c1001503c800c040103d5141104180440304840c4040750503219400151700402010b22010000d440e05100410314113102d181d206260 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 416007194 1106 416006088 416006137
    0x10c0216030f03030906050f180a020d112206060f030b13050406180f120c240b0904150e060126030f0f0309150708070302 54
    0x502041c0485074003814000d80c0700100300c5da003021052291386810300e025410036009407800c901c402031402941112500c041090a4015802000020f880c45152104407a00c0c15201c5900c0d400561040c17101c0d000c090020308202e02000100f0042007451901348082c003540c404c50039180506003441a041d809075101c14003240c04858180000445884a08100000703201c6014804030980e030010300c06003071005020008104d41e11400c1200040094844101c9180c098041c0041010001e007a0300e05040c403d03041c64800001503888002000007980000504045041d1070540c2c3c500002c14117140300075076600400c001d40d1031000042503194034040c03a01014007d038045c400045482060060f02190f024400c031540071803000c0c69a0344072045000c1110942e0301c150b46201203807241c44421505444c01e29100c61045100c1d03110302c58550745070341c4150003a50150b1740d00381c071280c820300302c0014 = true := by decide +kernel

theorem cover : BRFrame.Cov 415827338 416007194 := by
  have h0 := BRFrame.cov_init 415827338
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415827338 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415827338 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415827338 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415827338 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415827338 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415827338 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415827338 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415827338 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415827338 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415827338 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415827338 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415827338 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415827338 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415827338 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415827338 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415827338 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415827338 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415827338 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415827338 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415827338 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415827338 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415827338 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415827338 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415827338 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415827338 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415827338 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415827338 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415827338 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415827338 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415827338 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415827338 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415827338 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415827338 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415827338 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415827338 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415827338 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415827338 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415827338 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415827338 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415827338 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415827338 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415827338 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415827338 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415827338 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415827338 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415827338 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415827338 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415827338 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415827338 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415827338 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415827338 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415827338 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415827338 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415827338 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415827338 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415827338 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415827338 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415827338 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415827338 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415827338 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415827338 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415827338 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415827338 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415827338 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415827338 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415827338 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415827338 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415827338 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415827338 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415827338 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415827338 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415827338 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415827338 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415827338 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415827338 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415827338 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415827338 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415827338 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415827338 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415827338 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415827338 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415827338 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415827338 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415827338 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415827338 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415827338 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415827338 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415827338 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415827338 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415827338 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415827338 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415827338 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415827338 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415827338 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415827338 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415827338 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415827338 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415827338 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415827338 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415827338 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415827338 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415827338 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415827338 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415827338 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415827338 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415827338 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415827338 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415827338 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415827338 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415827338 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415827338 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415827338 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415827338 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415827338 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415827338 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415827338 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415827338 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415827338 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415827338 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415827338 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415827338 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415827338 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415827338 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415827338 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415827338 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415827338 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415827338 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415827338 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415827338 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415827338 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415827338 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415827338 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415827338 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415827338 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415827338 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415827338 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415827338 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415827338 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415827338 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415827338 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415827338 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415827338 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415827338 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415827338 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 415827338 ≤ n) (h2 : n < 416007194) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
