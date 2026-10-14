-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3266
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T09:09:14.835227+00:00
-- url     : https://prove2.me/submissions/ce933006-3792-4654-ad9f-7759662a3cff

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 587230215 ≤ n < 587410071 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 587231465 1250 587230215 587230223
    0x501061d3015010501020715030c03060905041128030f081201080a02030105010911030a0b010e03011d01060501030b100e012f0124140402071e0c270903020a 69
    0x40c03421090904000c03420900042d080a4070100583e80c0700012039440c800342c030508086000e180a00b0301014465040042820fa1038200464510b03a10140807007180d4088405039801d24107100d00e01a6890329034804d604c081001d246404880b12410381407110301029100091031803a406c81c3ca502081500c0d01511014407110500444660703480000d00e485101e6020203d02c44d51a02c800072421072107500c6148020040c164a2608580e0740c80011402029902c074145c0c184005080d2900c00f6960034003c4200700d03009505001004905603140c01d095481030342145051600f000e81e0902d40b81c0715602e41d12409005450917851034080c440c01070701e07030503074a07100e070052290b441c80c5401c0800d40c51844860709009200003002486248452141e4448030300c0804aa08402c400040141714140c1120001c50320008000628180e600c0d512010070002903488075002000c4403858800b03001501000c1402004030007181003a9058032452680300d241c0c0300c908a03059030b0b558042c40050510800584c4091544 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 587232715 1250 587231465 587231539
    0x603050a05031908130809011e02010b040e240406020403050102070f11010c020102030406030c05040b0a020d0f050301060c2904050102030114150304060e03210106030501061d 77
    0xd400c12035202ea00a1540c94909030300841d004854500ca581c881703108290081c0072402d0030116a80b04110350740140c0c0414100f000090018039140440c42d10203003c9045a00002001c8001724140f1064604058030250250030400000100c01900740310f43d40106212000b000f2240c0c1caa00c0d1080c004d000da038201920075031011850303208006404c0b85140c2000d005d07260941600700c4440c0110381034070b40c1c00703c000e005030000d1108001d61402604100900c40c3d00b400c140c0e00305900c0b0719518000360040a4082c2c0164403201309042c9160300814a01d00d4007000d803500521390340c1090300261411025407402405c041d21603400c6080000c43c7d058400c0303601004a52402c4500341801e016001c0d4000707000c0c40e202156018900041881c0c407030300843c20501d95101003429a55641c031100010401c5000c24040b0340002c003e80c0c80c61410414242c001412101c14800c059414101d00a08460058000800307100100080d4001c2d02c4070400c030744d00c2c103c200301c80520100c08402c000c5060130a4004903008a80b01b = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 587233965 1250 587232715 587232733
    0x120f0415020301060c150b010905040e031e040303030501170a121e1d0102070501170901060e0a38040b0604170102090907020a080d0b0d08030702060609010603061d0a060305 76
    0x5407010910f08030501600310b5071b03a21808400c51344102c807280341d05580031443c11070040109042640007140000491801da90070940c03c1101542407524030610344a1078080020305004068151080302e000d804040110350540e0071030700c0034541e104201d080140010801800c2c1503032017841112422084800300c0300612200d208101d0180c0386a65500c00c6513409110300d44209940e520005024088801c142c0d1244081220422100015440504065099500e4184c041642c0355a0035071503004031402c03d00010001043c21040d80645401d2811848000c000300781152406a5003411034400f500441300010314a200d400003503641d100d0340c1d0040720700094181c5c281c0390009040d4050550f0101c1134601c50303050380c1c07203803807c0b40c80385440c80c001030040d0030521490400502a0b40540354003000505212980d520f95200c00326690000c940000c0141d01000801006040007002c00703004103140d040a11009040500045642c000b2520303c0d446000e021000070f11041544e041040110380040c141c0d68512 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 587235215 1250 587233965 587233967
    0x50904200a020d0503070504030b10030b040b07030f0b0603012c091f0b091306061e05040c0e09070e030c0a03080a0815030c0f120105010e1b120f041502030106 70
    0xd041092010058050f03441e1501c83d0381c0c012400c1724030030300e00e61f515245003034290794565140020260141c040c01c4201c40c4040005402900c48501803406905010720502c4e04140003001c3e107007070480c4e103070b10a030509155100030740324001606e05449800000800d281c003099120f01150310006103030710055142c40207001c248180032800c0317100705915495144a12208107814021b84080c4200e00d508240340030300041c0c014114440c8121790038070480b03010459955a052888001701c0e40858100011301000c01000180351500c00c140e41d2407080c0c1020120000d50100041c0419070041105061110042d0310421503070342032003481000c10006111581458803810403200b250440380f60319001c150b050f80400c00918103140d051a900c40d005000b021440441c0c010b2207420140900d0440c1c0003143c01c0380541082c402809081c0c06044083c458062902e08080c1e01003a400c0c0a01014a04180801680c0c880071503103140d1035400783e58080b07011165100d178038000b0303d9040c85120001800c0e10120000c5041 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 587236465 1250 587235215 587235217
    0x30e01150510050301080307031803080409050a0501170c06030601030e032a190f061805010903090506070506010504092a091d101a1e10031401030305090420 69
    0x2844003554080d9400b00103180a0350030348828010700c070080c1d000b8044100040c0c0f003102100003560b0441440306401d0307038079501c0b018660802e8020043c129201c03020040400100c1c03103594018107031289908418101c07400c210f038844405035a0607014600000c0050001d90080e040007408020600c1103950783c10f0f055100c00704403020300100c04aa0f07140b10a2030406032100103101c01d854201c01008425600390fa40e54031840c44020311003102c00c2502c0c0d001074900d80203481204502035001c0c0f4004500380910740f0b03000b4254019500310500c5000c0a0103c50301080c000602c45064070010b07030b0002505030a41c101040e40d092200091040c08200c14003134101e0044000c4198200d03840003c05000850000f002c0020050300807004002c3c82e0b1000151580c0d1701e003540c00c012115980046601c282e008480701140f01c0d5100c02e61170707400e840800e0002c40414201a010800c4d040c51a02e02004442c0e4642895180d81c0f2040c80003400300701000c40d10b0500740e502e550100c00b60741151000c1c074001101e124103600f21 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 587237715 1250 587236465 587236469
    0x2030c130911030f07150216091523090c0906070f120c2a260615180a021309061404060b030105060a0c0501150f0f03020a1401030e0115 60
    0xc421625610010b440c2400691481343c0f00a410180543c1070500c4001c40102e80b0f9030001500718885d6041d000c07500001c2e01c0302040602a004c1c0301107500501d08509a12804450340032488201c1940401d01e070710680340c1101d1400c01030446410100703855003030441c145405503000140d401240001e1200030004024850b840741481010008803000c40c042c0305a80100c440580640307803440e02070240b2140d0021504a400601e80d0240d45500141c9a100800c4440155005a00e07004110382c0003401c0e030030080282c3d652043d90f1007009103030f81c0303517a4021540c14524501070a44071594480411400609038040c2d91070140302c182d0800c1c50a0740c0f500c441000d401c0721f206a4051811288880e2900c4c01e00b0f0246000b940e240d412441d180d64600020f100c600c0e44030700800002c00441c8002c00700010402e00030241502d01e00040c20a061741071492400b40d01002394000f03150b03460130810410041c1c59009601c411039000748600462060b00c08010b80252011b40903000d190b518112100d01c40017030403071141c41 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 587238965 1250 587237715 587237723
    0x1b090e1806150d0203010f0203011d0408030604091a0c0c100b03030d0902011b0b070f020f0a020f01050702031c2015100e04060e010c02010902011d0102030705070e0106020d0903020f0103050402030c1309 89
    0x7226001041001000302e010341d0037800f02041000000c032642400c0d080880c4062142131139103500c10b86010700380705003d8255003c60004600090304800c010041000040045150104010a0201c0000241c0e031b4410400b03004e02041e1103402c5101903a0003000c1e41d900003291580b00064010161622210a00044403202c01150451480890075031000446003a032219103c01828080c451780c00300b01213900d4100c0aa410031608108a00051f1424410324001c0c0c4401080c1f40100600e0302c0f0064041c0814045100c144130340d0021240a04c18002003400da81c000c000750240c00343c0c0751020804480c0000c0d8008400400a204c140400c0102c2c0da40040002e03403a4000030090140c0d943c0c4102c3c00e80301d0382403001e8005410040c501e810070116410942801c441401100e28200b41c07a5503031400c0138859400380341d040c2054001004103640600004c001e692262900701d01c2141541c1c00190903000382581141019074560015085413070401c50960081e00080504105071500001240640542e020842d = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 587240215 1250 587238965 587238989
    0x30302070b1506090d051f050610210b010c080703050909010603060b040b1b010e0a0308060114040902070215040906050103060504091101050705011b090e1806150d0203010f020301 79
    0x40c644080e00c024030001407000600f0149030102100401040b0312820b6802d81e0b80d07014207015101001c86212807103481c00203a040214113450400300300300e2071030170310100325051081030170f030751400043c03069101080700f1200000083e84125810049452040380c41c0c5c0100090f0000944c03400340360b00702001c0c168840d821941c1d4001d41c1e8880600b1000e50741c140c4105145000c0170700003405005a400041c02c503035904444e8050f00010050442400c3d42c8440d500c1030f003960001c0e51001305265004418503071082081c20710614a01c400000074503180301d20301c215202d4940c00f04642c1e0840d80c44051290800114000068849454604542c0100241e00c66103000c2490a500003e8506141c000c40c0b41440d0004206100c40710402c0040d10182e01180048500755039a00f842081060040e4000400c02111754480904500709a1481c00401001d411600c4c0c2100d010202103401c00c0000d81c1950010005000c0400b00080101080f004c20400c0750080d415401e01c414100c248a403680618100c4036104514 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 587241465 1250 587240215 587240221
    0xf020a0e15042c03090d26120403080c0c07060207052d01050f070602071101030c080906010303200709020915040602030717040b03040f1b0b0717040f03030302070b 72
    0x8100c56090041c10032202c100303d200c140440300c4410600c401202c04098034641100e0800142400302840c608880d0745074581201c65501d11700112114001d0b010746686442c0009502d200c1402c400001c20003020003141c81c0006111943c034400f500c1207280c0c0082124102521a10043e468034803a004031806450101100c0e050181d00e840400f00c9402c011813000d0910072040011a0168404482504800000c00c01d100018403103200400109002e200082a85a00c0c04001000d444001d1a11000c101e411024030120341c3c004125141140c1e4142000d4405120302c0c4146240030400c2e4806c00f0351802070b01800200300c00765800502c21fa0320220380d10707503d240101e06510843e00445c021480180d00c00e0080700c2c006400c66019000036040c3c90a401d04240d6203440d211303031544c800c490444200c8843d8503c98100724000c4001c50508005e8000b000c066803c20b50f40500354000c403d0054030015003c010030706404015000c450140440c086510100c5440b420085c000e584050022544114a5400 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 587242715 1250 587241465 587241469
    0x140f0c09090c240c07080a1b081c140c0a0b010504060602070e0406090210030c1101020315190302040c020f0607050313030518100903050f06041208040f020a0e15 71
    0x41d0280038000412140d603d1440c0740e0384240002e89100c070340e080400c041040650311101040f500009010b010010246600d091a21449107003070020403031000c0d02081000d100000c00420200c0020011a80e41c10301c0244000007110307903898480481d02c3c401c40005140c0042ca46c0410140d51280c0174096007086c6903610024001150342c3d40c4140f200580100c42c0c01c0c0a060501c0a005400c280a91000700d416560340d00054034101c0004c140d200461364a00e10606c0c903a800c481e103c00e08912400085085140202d0030200e101d2104140c2403041102d004404410024042e1000c06990080c001300700a40303a800000c1c1d070b14040224004201d00c80d5000007500c01d03100c2c40c00c4074418440c80004e0382d00c00000c0e81d0140e615801079070321040780c05a4011a0341c1e094680c48180700c8124841e0343ea03071100d149507007091402d02101b444104400c0e0088000c000100f40070b007103088103064071451b000d07009507194100a120f5103824600250b1219101800141840c8182500780c0201007070611042c081001c0e1007 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 587243965 1250 587242715 587242723
    0x910051f0b0a1713030e0a210c3c0b0f1c0603030e190e09030306090c0a140307030f0f0f0c02010b09060906130203011d01080c03060109150503030705010e010e120f07140f0c0909 78
    0x21140b480c0c45e14ac005180000760b010040210b6030718022021030305541c41c2d601742030032608640c0081d018117001140020184010f41c400c844004481c034070800602d401e5803401002c181030490580d001d20300020545480c20390110404004250941c5c08940768180364402d40e40340e0380182c40b0340d8499507072100880e00c010b03840411650341040340c1e255040400c81d00f44640c500e60f0130041540b400d066680001c1481da000740d018602002900303100002d90000d4103008030040711034001d0404216031616215032665100c08010a802035811101d00040355601c20000b808603d022004500c51800480005440c01c2e04440c1705007400b5650400030142d80c0c0b0389000981e00e9001f1541c0c3c07507040d03109000411256080b980880e18a130101546548029203440c0403a20b1940191000c40c1c4a80d035449032507580038002c2c030480e00981110310280c0000c114040040b00e00e8001d801c04961407120018030300c03081143c1038040c0ca10000020041e40c10490410250a4030780c03011904050140070400d0004c0c000170700101e = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 587245215 1250 587243965 587243999
    0x609051c0b04020d05061f09091e020f0d0c030c0512060411010210110417030316031806090b1b030910051f0b0a1713030e0a210c 57
    0x858100c15040a580307070080c11040c040d0080c2d07048811a511500491028410140300d6416030852588070b1001000351526800c0070b0b4030202c03078103180188460000302ca07503c0300307070801420203100c0174110454000a00103140e861420b65101502888400c10404036100060499001d880061503403941c8409018102a10074280301d06600010000740010700304950080380c119062044a04560705c00c10760300700716485d100410b811880081010800c46c04006004500e040c00d01002d0f41c01c40c100015494400707400d500c0c0038401c0c182c0b136040d030422025542100750381c0d04e60004000d000011017410045002c00081e152900f0600c2890f03001c040c40c6903103408481c010380711f0b0030007440410909004100203083c042c001b020303096582c0e514149103001c2092a0000b5100706440e099450800b03c4c0c014180300084081c941003111803204001c0784258840d28802e4607509401c0101d00108140c0001d150281c0070f41140011240e014a1400940304160840d0b1f1564454420013261036210404941d0b0302c1041 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 587246465 1250 587245215 587245249
    0x905090604020a0e12033f1801062606010b040513110d0e0609060601120504150e070518010308041401051204050c0117070c080309030708040807060905 67
    0xa0100314607040c40e500030500c0040904d0711400d41496a0000381da0400c2c0d240f08a01c01c2c0d03001056184071004070111900e082c0180ca020401483d10512288180c400c01c200710302050340482c0001542c41c0c4143c00c540c0c0031141520020043c843c1c5440100443c6014080800c282e1001c02d40c2100c41c6000c00650141603807102e40c1a03d0509150201300718503248400856030740c00ba10703003c0b003031209014540940321850b6200808641e02264164980c51f00e0320041018441d94443d1307040c410141d80010850866018405001c99166258180308003401443c43c2c00f02d44003031901088107283c503c082080010780e6411a20469054002401d2429402c0b00780400b901c0b10004000410040c00322a40000041e0010706216045c8415400100c070200300031141a9201e8110b031148484641e440105d801030f01c903440c038a122003820021340007440f0000c0c19000070103209000000c01c42006041080d039540b41ea0203480a42d49544030703000c2640f01c090604c141d0001c5a500c4501251500e414071400351b5034002 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 587247715 1250 587246465 587246479
    0x5010e0610120b030a0b1501080c1303020405070903230709060f0b0d1b0305010503060a0507020d2a15050a09080a0c0c050a230609062a010e1c0905 65
    0x1840b40150010701d800c1c0780d01c5503d84980d20542002965880b159449503002c12084500704d1680c20000d02483d0307000300311201c90f01c410401003080c02c0c1c90200800c00e0383c1e010756000685a031400d00654416445801c003424000b050388446414401c4202440540a001c4042c1d8542c00c0e0307103d050b542981c0003405098090f564420050107000d2884000c0c01d003c800c0b206e000301310342280328103d070499120702d43c10000207070301d820040c0518141002025049105e84204201914018400035116184060700a04020340c10000010042401121024100282ca04c101d00600c41b0324000500c4e5100340c80403501d007801c2c403001030300150203841844451500301002515000401ea0304031942c0c820103401321048509407101150360388512030f2600c0900710302900c89a190201e84c02c10300300803d2092210f81b284804220540e929200d80f400e50701105107040f02944200e0446941c2c1c5050300b41d05122041c1580303080801121284001368040d1500180c030720f07420442c00d00403021224000c9030702440303401c016 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 587248965 1250 587247715 587247737
    0x2d0c10061d06030a08130305070503190206031f09020d05010905070903150204091a1c021e0f04020307021e1203010e090c1306180204080705010503040f140105010e0610 74
    0x3000000050303002c2d00003401e4940910031070783c03611456088034070f02034038820a01c001401040340800c0303c00d01030724007140103256400e4803005441c00b25071403c40083c01b9010110108690880282403101c1d2034490b00d03a4040580d842e545010001e4000352044282141058000110b40c0c3c068410b160245001e0f549002c5420f0a5440341912100351609428080c0d500704000107050b909442001c05040c48404d4040110410804010131092a040509451040d002c00000169200b9102c180c40418089150550b0002e100024103440d085c1c00c4003641141c000000c200c90aa03010070343d03201f00b00ca80d040707022094041d50b10b8681e44135548041c1d140158410070040c03120b407941e0341c046c690222180c070848520300205004140c0700005e800ca0840ca0035280e000a010502aa5001d00603400c1c0c524011824507240c0160199a43d81078030555040c4400003000c14148210600703005c02454000790b44803003114481c000c1c1402840248604040e000144012400c1c0703140150000c18060682d0740c1d0350201e65 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 587250215 1250 587248965 587249009
    0x10905070909140f180d081605030601081f0b03040c05031501030305030a1512050a0b070e06071203020906030c0712031103040b07050417030c0f0c0a0303052d0c1006 73
    0x150042c081c0c50501702d64488009151000300010b1802d4262030382c4640c890b040c0600050000140d40303050400b0720009000f0005d090740d2020841ea401210b00c0c0607400c00a00c00720b0810b1034501320307410540d900e20001040209110034010183c0880b001036086408003d14021200180c0e4028017009000613010004a20880020382150702d0054808001410103950b84d00a80007000b100e00381141c040d04010041c10a00c406800001d601c4042414825800c40c801000540d041c890010300070090000307a00026111403207076050310500c007005441c0e143d0b82d04024885442d15088000215030b0f031400c2d62030b0340f4000d61089c000d450940c4406001203041d80c440e580c40492040c0002c0c00107041050034000050b064a641c030341071b41800a1000650b40e251440c074405402c3c01c1c40d1041800c180e5121558100c080d845800205089075007510b0507030348400c102424441c0c05035100f0580c0d074107c098001103c90920016008140958032041260700b9080c0c900848000e482d018492010a2180c203c60ba40b005 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 587251465 1250 587250215 587250241
    0x140102012708040f0801050610020f0c0d05190f211d031c090e061c03050c010e1e0c0906090a090206071407080d0c08030c2101090507090914 62
    0x424400c0b04158182030322489070a820340e0541e8400003d0307039103c50921171242408200c5480c054594405005603900d0313100310070350351000c1384034560080c0c003501c14441c2072000510800380351a08101041e40141c00505000304d03500000d00c029902c9200704102c0c100c6c0c00e01e41c03c0000305018244c1d2a002c509003441c546064014030000c10090b00b601844495064081c104000c4017402c0f100d681368451038a0600f201005132001c0100501c0c00344894503000400384d891001d001c2c064944c145415a6101078140805014040060403e666885081070a280380069464100071503410310044904d200e666108002c1121001c1e602c1503040a00b500105074034064940016500c14005445146808400d80e42c080140170120080100e90b0010407043c4070032001482601c44046491a06485c6624141c9501071a844094080c0c204142c000841419102d0110380c0c1110744800c0b140b448000f90ba561a04002a100489001000600386980420514058403030704615003403d52080e4626a40c00a9002030 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 587252715 1250 587251465 587251541
    0x40203101503170904091b050312220b031303120911040e0313090603060e03070c09091406070201061511060f13020312090f040501050d1b0f0f14010201 67
    0x1803050801202d056a121740c00388031b00c1e052041c07150301c440c1050b034110501e08008a4200030b00c01d802c0300074090400742015040c3e6142c4458030700580b03245020118180c0a00c0a140e0040002d04404020070024207038034031000001d03038000d031a00030070004825501821202100001021591100f41410090601d58807810805500c00201c9207005003005222406004590102000341e480d90000e104101040c003400103210012001107040c55919540d1b000302c03940301d00a0401031a42c0c2d51032101403141c05000d90014491801c02d40780c0900f070502c0000c2c0a000785004041c83c0842d03120640081c00d204884040110175001c01a000340d403241c1c0300700982030f003002d000006a2044030080b0f00141e6018000041030000105c415590313452400144040302036011038152040e0f14040c010001d503210342010b14513643d0b005907100504101d5111a5201151941000c1d0074490000d40201d04501d60103185400d454584840d580141c4081004900b0798800c88090444000318081a0150082815903062 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 587253965 1250 587252715 587252753
    0x10c0b04060e07140a0510090306022107050d1d0d03110712050403030905010801270915140903030c0f070f12030603140f42040203101503 61
    0x60003200c2d03a42040e16280890308502442050204c55400c075103400c4074a07400420080e1012544056030000c0030b051a000d47c40080c21450b0001000030405502c4c2c0d1154113034001c00901d030030340d40c00d041c50f001b492600710303021010100d85810502200b0f00b03016800c10001c0a0b000d4006c3c0703400c003003403a412005000c1c80c590b1004015000d000d410001084809440d0b0401e400d40d850b2601c4514505009004d0041036001c941030060210040c0a803080421042c0381941c454229003500201c903194160003400d081c003001c0e082042c203190a80d41e41d0050b40000342c0d18a044d000e46081c1c0e44452003078a07102c0c0700540d001c1c140d506003049007460004204011b0034040d400340d8450b60902c926a1a140c4d80e101201c2d240500003559854148100b00d07002403000040840070000b002244012310310b4a07903c01340c05000c8000030009484120046103450319010302d8102405200302d0502d403502e054140c030403066800300d100340103160780300c0d018880e00c0c0b00b03181c5010041901420343c1361454446001100c4d40149100c = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 587255215 1250 587253965 587253971
    0x310052e03021f0810061e17040c050117090334030201060504060b070c030b060a03061107031e0206070c06020d1d011a01020c060d0e060c0c0d0e010c0b0406 69
    0x243c0d0755880d0a02d2104070f8106036a4255820501c000c28045008180b540e034503884d4081440000e9100300d88106140540d00c281c907101e20315800a66088000700160034001450608100c10808521900c000f2a442030721103003075081003294240320018080310b80b82015403092040c3c0101c0d01011008007035000600c800b4089001c01c00009003401d0608035030560150b911b820b010481ca0800703100e40c0004104046103203062049555440c3c880620b1440090607070004800032410603510244080019544a1020411818140740c1c0c400e15412100040c1c1c003041042085404440e810005840c00034456809040544d5030b0706000e40d42c0e9601c0580a891140e401d0080030307074400b0703540328601688024002110050000e05202425103100942c1411405900312150308640d80010707585032000360403590281c80300f048481c01402000403c4c49082c140c4114414000d000080c0c000900780410450709440c80001e290701d00369044c5510300032460005021842000205007242d0307840d034020744202c17408 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 587256465 1250 587255215 587255219
    0x151d01090302120f0c09061f0504080d17062407030302070c060c170c03090f150304120914060d02030603010e06180105010e01050108010b0a1803060b0310052e 70
    0x1c40d50007100310f0120340c1a50301090820424400812050101c8582201e02c200300d4540200402e001054100d800c030b810005945400072407600a8040d03030007030400c0c5401c4500e290345003100242458502c1c0d240d420101800e001149181c2132010f0113007070110303403c00ca6414429520101045550007940c06504059090002400040400e10301c03500418007603941c1c004ca5800c0f070403c2046400200180f482000c02000940c0b0f40d8100841130b02e4402c1000c940b400c030564808408100124000601d0480451002041008120511440c551070050580d601000c5986500b100400c282500c1d4485601c820188281c040d07100007500295449000500040383c40d440855a26143c90410380d80d001800101a050700e0341c1040c01d00c10180100114210384000354075040028041500c180a010b1555100042c40d0700541c4c0110000c1d4980b56206041c420a02d6a074149880146110b40066209002c0d400c200e04015140340907480c0a11460a2848495a00c41407540c8540106045e0300b400280e1036000 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 587257715 1250 587256465 587256469
    0x703061809030507031110150602010e0c0307150c02031203070801080a0503030606160b070806010e060403020a0e13050d0c030e0420160b041a0f010e0601050706020c060916151d01090302 82
    0x1a003052301041c07902d01d42050f402c240c0701a0961340410300e2040c00b540625041e40c03555800080d424201d81c0c0c000c0300241b00d400b9003802110ba44405c800040d4161240401c800d560301d9800000b148200b40304d41c2c4440590362a0700c640e503107505600700c1c00303051a0f000380041180d5281100c01030810383c01648104210400c05d69402054600c2180c48001040d9100c0410910b940c1000d8199032400c01241c95a19040c116030008030108018010280401d002400050030701603008201901660400202c0b4010403d20600070b0410303a2000c03007100010380d400016040ca091502428001d2200a200c42e602144c840343e20360425001269280014500c00c10400003188075000c50074040c600903d92240300d280c1d102038070340c80600701a10868001d52504010010192010311a682041091174801d9a98042e4108034001e405480320841c1c08bc01030400b400342801002454104284084404030000c1e95070f00e1031180c5591101c28100f0114480391580a03016803401e01803d485007050400b00101916600 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 587258965 1250 587257715 587257721
    0x3090b0310270c180909150903050906040905090c012c190801020306091305100e030409110a0809010c050d0e010204030b041a01050307060e0d14060703061809030507031110 76
    0x203062404078284044e00420078070003140c4600940710011041c030034103545a41e94541044040c866039100d540e100350754000c040c8181d0840382207520040c082030301d60341c40c0e076074183c01440d040d120000c5510403022002d041e540981000c10b80c41200c1c201545c42510036141d00b00300d0881080328264022123814036220b11940a0001c440642030745000141c40346040000d20803468070240c12080d80700400e1100c000000e50000728440010b061110104030300c0c188100c00c3d8a18005d907041018264100f442c0203650428410191148100b01d03543c448081e2921a00b5508030707200c0504000c0060030801004100303846a80290014010000005140980d2501c1e024500802900e08440c0080a1800c2002d1100f948550501408013240603104041c54090058504002d00404074058621003400303c06005044010080c418414415503002d8900004001d004141a01034540e03403807000305144070924098032400a403103a040d22180e1030706803c3d440030346400f0200f95044080d0700c504c0c881c008109500b40 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 587260215 1250 587258965 587258981
    0xf031501090e06090c06071b0305030a0503093903070314011e0c0203070b04060e0604050c0307090902030a080c070824070302160b0615030408030403090b031027 71
    0x1d900146030b903014440c0d203007001009094000983d0003000c4c101d800355244001c40d00f00b542c0c04990519018044c12041c4500043d507070000c1d00741c1c0400b2402e1110a5001402140f1508030b0f01c09803000441c10164491071200f0840b4000d4811120000a82e03030842c101560704643c25008085940301540c0ba59003804013a000355140d200c0340d44a400b25142d00b251480b0f5008003544010087c400d0403c07404c4001d54a025010340038024540d01d002007814003105d0f5112840103003144082e90300e00d1800e03081049d5a214204c1c101c50091140751000903105400748031310400c0583c024090300c010403180c0c8407005250080c0c0c00003104c5014034000000c480c1010000000f80b11924100d0107103400c4074580c850103102004009006050040200b40d21602c0a1509401e242c0e910502ca001940c46010204440300d1b040604198091000020320050020620281d4401c9210760354000c0a240c07513007800e890342e00042c2e4061002d8103034035600744114440c8008441c81c078501c11915503203e2150b10404002d0f12111 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 587261465 1250 587260215 587260229
    0x1020c011a0d0510090606080d020607090f08070e0411030f0d020d08130f1502040e06040c26150603070512061002210904023f060f031501 61
    0x562024801060820300700c0d040c410085810000c1c890803034032029111004190003804c91561482c1c03180c00c001b10b0760b00c28805810038a0407504090726030180691785810039251940800d24a40d00060368424411800c0d060700c1900740a410034070324040d401e00900801810450300b0101100900c0841d481c01c1000541003100e000003010504d500348000b07030500380840403d8040085042c00c005c021444e09540c91182c951001b0860103030511420300b1040d00340300d40440c010003400064006258046a80c402d8001c280072941001149840e40d401d44c3d62b8507000105841410301d03003141c42210849904000c0c3e1010f01c42100152034011180054181d90084600d175005c5840864081442140d561740c5a912080559010380000346450340079554035591001201a000d09016840902d000007082d94648007000e0410754440c01c80e9224881c84205504000036a204062108940b01c410000e9030841c20b401443c1c01900c030344031360051005110050242c2c80d05071084900c0c03000d080e034038406c0b00c0c3d00810b84 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 587262715 1250 587261465 587261471
    0x1050a062c09430507030c05010606030c02071d040318030f0b0a0b01031103060409082502012c0409051507050309121306210e0c010807112d01020c01 66
    0x1c1c0181181580c01c00c2c40b00c0000f1224500000a2484011048a102c2014a0811300d03100d041c180f80c1194620a190001003103542480310010b80e050b0035411a640201c41c940a46000d69100c0300300074034101158000500e14441d05001c200440d008a0001d2a04044800c5914440c0d4480d207840c0e040f0491010100c2d5081ca40004002c00c456440c414518079090034641440403080c2c24030f11136500c5c0000b40c882e0380b24503076951050301003001d08011642405124003005061110a04001200061080c41a40440c24940c241c0c20b0803010703003503082c1c103083e07031b44070000a00c4100030207201c01440c0e1041e048484d40f0401283c07c03021960003040d980708039400da0320965686080d8580c03a04005801c240b152030a6024081c15601c14055030f00701007525000e150039060400d45044501c090000304d49103030105442c0001945030b58001080e112480310007a21044034036264514100c40072641403802e03408a42040041414040090201c601003e07010ba00600704083c0460505007240d22040c0409017580d5 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 587263965 1250 587262715 587262751
    0x51c09120e041a0f01020a300f0c060f0e0a0b010f060c02150c010b060c010c0e0906180703060b13030c08010b01050a0c0c09050a0b0901050a062c09 65
    0x1501c01a48040e2241c240d40a000b401005006000c215654103e0780b44034030b2140d45a00703001d9108110b442509600b05c4642101e103083d40803a103806020f00040e00303184009406807907803da0300400d8105000700c0260344601038000d05440d200000d103505041181e4490322038400996900f02001140c80c1c1030300400303c030002945011011000005e0582c4000d00f80080d05840c5400350340d0702031341c181d0240200848503503610360749001103005100d0160718035484480454038840507101580a10001d40e410380341d60310308907142c004120b041e490450714aa40311042d0101400e580840c2840c0c0e40d0440c14a08010a03c9901d500c10100150048410030075082800300082080c4209200c2e51401000001c0007000100c080d01d0000301244600ca55031070502900c16410020002c0a176010701c0186045c11082081d0b06010122101030601140356a20845a0030700100b00c511f4110039074802c68245480d0411050142501c0c0045010680d9440c1504810919546050344842002901c5003201c03034400c1c48141 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 587265215 1250 587263965 587263967
    0x14040b0a110f030a050d0b06040b0309101119021011121e060618060d0902031539120412090e06210708060106020c031b01051c0912 58
    0x106809103804680d0249a400501c02ca000c0300320b4818078071074a000b564a02002e0b45c15405400783d880490b800220006001410545141c044c50040d40000155008480c0c1d0351140e00a0302c100f001076100315441000794011162118001c1c2c1140b0601d801a52318000c001c00d00c10044607407140800016600014504c0c40304000c16801c40d6200c50b107421148020304c03482903514000e16000b001c2c02d005a03000100c9103002c100110060201001c005c04003540d406000ea4548080c1c0302c2c01400301d000340314402d407600060303d603980fa1510500d52241da14a04401c078180c42d464005400d4402000c0c01000d505800580441100804031032229268540c001e0034030340341c0541034540f041c0b0314070100848240c0c140301c0d00703a0556034503400210490301c10b21030b5028070030900c10050040240c08120321400350001515000410218101c07641a001e440d4003521140500d602e850300440c0c803003020f103090703012401107600450103881024007210318860040103521400040300c0c1c03280b46c00d441140b0395074424a011 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 587266465 1250 587265215 587265227
    0xb0a033b01051003021011060a060e06120d050d0e10150b041a2a0609100c1b050a120306050f010c02030a0201031a06040306060504150614030714040b0a 67
    0x41000c001c100038a07116460620010481c00700a22400705412038014440c410203043d40c180740060305490300c90520311903c10080460b17220310010002c10500180e802d10b04401525120070740d0314040d0546400051007258170303512400002c10f80c030b90b503480311280f404d40401801c8450100c0c0c54001803000d080c08c2040080d11501d80c0181c424590421081c0035540c0200c003680c0d01451511242920784080003910180d100c801c40c41ca13420a440c00c4640208507000046042c02284018190b50340140d52000303950640b100960072101159800b0b141040c00c4ca044011403203102c0c001c60170381d03100281d1581c810a414490b0601c081c0040e0300e8440500031407420071007609040000b400c010b08110040d50111317485982c080c2010f0b05056131400340b034254031b6003546c0380b01440000901080d51075840e0b00d0100b000301400e00405024515003003508115203c89200e940907203409131a070081c8010310b001c2c0501d03c0e42c002070000007084025040e12451030000e42c09080a0401d1071540e0b0389466800100400b6 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 587267715 1250 587266465 587266571
    0xf040c210507090c02031e1612080109060f03082a0304060207050f0109031509050d05040e06120a26030a090b1f060509010203120702011509050403090b0a03 69
    0x50382e01c1c103c004c00c411500002202d048801d103185521803100c0712451f2400324005c2030100707050b8080319641c440801172140ca40f1940c0f501691220b0110f41d0329441040c0c1114151f01602c9911804600b0a001240707407000503064582421180c1090031141500c0c41d10741a00d00b04503206980c1c40490140000c98050080030b015140680d8143d10300c4c40d00c2000244298010b1001801d003454040109045401c06d82000c08496080340448007104100ca0004085502a10400b0008640c406c00700d011440d00865200c00c1f6042000140348a20058444050342c081640002151301070910880080d2120b14020350311038940e4110000b4002c0f04c0d403d0040c19800000c2800c440050211403149011504032080000e407450303858125207511400c5d006138a98881c60490300b8003d40400c0030012142c0d81500041d12084050210140103aa1f40302c440c1e0681c0ea0594000b0041222040306020030346c80c49010300350304d90f114a40171421000e100c40403c0c1000080a10340b03180c0507000c00440503003009000c203800b = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 587268965 1250 587267715 587267729
    0x5040e01060b0d1b020d0c020f041410080c12071406040e090304030606150f03050603030f191e0c0b040c090507110606060c0604020d0c0e090607020c040c080f040c210507 75
    0xc8101b820720040041c00035581c0248116114030341c154017602c0356801440030f0740c5820340c1e001140c2041e0000c909034035003510072a1411b07c2045d012540c0b80c10305050081c0300c921000b000b4094141410f20204240e100401c181f0b03080503007803000050342006440020f00480107113015503030741d030300390b00741070b0181c1d21207801074081001b02e200c40b01072041d407154803807030011042d1600151075218440080d041d4400c203100d05c0c4c80c01300045156541e440423041d520340d5600c016215001070310400007030070540c040c2e912100000310ba800240803022a8403515096403040c85008c258521980300c26110085900685280d00020303081103c8040c044010081c1303a4010404403274880c2010317855456503a8980006100901074480740c0905000c11003601440d00c06030488080e203040c146807078881b80341d03244800c035080b000510440d07030b16042900301440351351034141e0300d0f55603040c031542d404440010b4440c024004a40c0140096030003c1c10084c030310156010300700303010050743e000758981c14031514024550300414 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 587270215 1250 587268965 587268973
    0x305070f05030a0c1b060b0910030f0311012003061e0d030e030109020a2c01030b070305060d21090f060504050d080c0a0b09012405040e01060b0d1b02 66
    0x2642141c100003030383d5009031000c401190b181041c0342e04a4040000252441032a5007882480c000c000b11900014035441c01504c444800b9503c100341d8111440745072101616210603114803101080c411070014110b10f440400100f40c0d20442c80c0310311102c1d4480e01204d10303c0880071081c45660b00c0c0003a02c00c82c040c0d206842c9420703500803c1c400145844c211946c02018410302c10840b5040303031000c2d04000801c680040031500c50039a648052110004040048009104586420441ea0402e51200382c142d0750040110310182d03681c810181d0080070003800d500c1d03200311150390180015140d40d88031510b000007500704001c5040d01d1040640141c06607000521807540c800010301820754081c0640d0200c400442d03a80b0380d08011410300b41d00502c107003222000c07207018032041c00052001d241c0c07450f40900d0b040b4008201c200c0191112011044600164058102c040c5c0c03001c02951400390045003602d0180e4000051045d51012003a816a0082020000468554807002d1a002e01c9070400220040140060 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 587271465 1250 587270215 587270237
    0x150801080c1203190903020a03050313060c1109070215040c050f120a03030b060c0f031e0c0a03201504060b01050f0a0c08120a1b1809020307031107060b01030507 71
    0x1041c0c89006441c80d4104815130b141c100d1001c588a41d50250065802038603a00519490b0304040f41c503648094004101d00b207844100080f0240304101e844080d0f5004008425100182c00c100080c07450b010345080c045101c1c4254480010170a50b0800f03001d58801e2212201c3c0390310f024140103600031204101482640e10211590342c04401090000322680d252600192103207000c03000031402c0c001c541c0c941c445407160508a45050000200600d01c14401402074002519910780781c1c14a84501200c16009400841d50800000e0051100c01e000c100c5210410070301644880001e032410802c0300410100c0f04c0f10b10180018000c15100710f0114070000e11f81545032200401071600c442c030400385414100851b51405c1c1003804104c1703080ea0442291b0341c00d024914248150b070f00c40a820809007a000c0c080301070360700034640d6006200f101041d03280d0305020305d005450540c0c40c20094100402d124241074840300004e69508101c0700411f03101d03124100000d10b100040000408840000344910140103680c40070f = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 587272715 1250 587271465 587271499
    0x603070b0414061e04030204150503152809020907080709152001090b15100804060603060504030f1d090c13081b0f0a05090408070c150801080c 63
    0x454054440b840d442070102d02251002c1000c52280140b200c2e40740990a144a8540400c10020021240220341c01c1c0052440141070b8040c0302194400c00da4594818400456000d101b06855030b4004115151924401140c031034090900000304c13000982160303500c00171400c52030081d1040d03403c0801494400b116290111000e060f080042c003440803440c801034000a03002d0300c1100b0a60380300180340d20002d68401d00c070316801c1c06000210742c12249401601e00087ca0300c4d8400c242d51812071401400c200c000d07003031640240c681d000054001d4520315102c00000c004101d9900900f40251b00c02d948482c0416291140104141405601445545120b000d500e0030350303331012421500400040d40c610b070f49803100c00d900c80364240306a200449078041d5002d01da85401c3c61101c0324186103002e4401d002d0410a10041013400300c114015650b1200494000c6004101c2c00c001504a10307201c1c0c0384050b40701c3c2e140c41e070601d92054500c40b0100081d006e040180507408051100c003d9818007a22001510107000342 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 587273965 1250 587272715 587272717
    0x1e01080c091008090c1806120d2304080102070807020306150315090f10050a0e06160305090f06190b030604020a060f05041e0806101818060f060503060603070b 70
    0xa0058100b00c3c0d5840402e8401ea014010001c900c1c2d00200162404d0294411100100030100c80c800e1040c2c10742c10700c04032000d601060001304500c2a0b503038110090036000002c81d501300c0a007840c810000d028480860f01c082e00344000d145d0306004001c41621803445204141c0750010003003054441c038080a0103000071b42c0380012140e00030803020803090a5540c401003224034206502c1d141000b180700b181101d4900445560080e0300601041c241480520210554650b88442c140c030544201c032030305285070402500c203a1180ea00b007243c00c0c00307640842002e01900e524048064620194141b00800600f6401200303124445120700c0030380180085143c280c00180d4130310010311418081c8483c00e800285a988182c2c102c501820301c25560407242c0c08010400f502d41d2440b406080c02034840c4d98046030a112018050324203c400d10010040c04600d001040005022880c2c020001502008da28000080c001d01880500c1c15425000141c4185094105032500340084c00160013600040c405002000e8010 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 587275215 1250 587273965 587273989
    0x18030d152108091203030f0118092102070b03040506060f0d030c020f121203040c060203120a0b240309010f02160b100803030f09060705041d04060b1e01080c09 70
    0x1c4009440d01d540f4408100f1500904400d01c41c1808008200020035402018581c142c0700c08080508240a4001440e01180c80f0800081c00c60342e1600c04480300039200c0c032108050380c00c0074415180c02c0d42d50741d055140c180d00300380c03012640c030b80240081159500340380d41d07010380d4104226071581c1030000c03644014007007040b04000030740600c00c64401c084a580f221b4490f2440e000001d4200c401d5195141004a4150815a02110194030701e40001481c98400000d42e144240a462620300980341c940000d001019841d884940241d110303180c612442c03c80840500381b0200c0c5500aa55900e003c00c415070031a200784c2c6031502031030f10601c8050442c04503c2041031409034808161411a200d40740d81c41e1814219a01c14100e6100c000f04021018590310140e5000740318078011542c2c0d81d10b6006003562140224081c800178150341c2c20956178048000303049150414000c0304000b480000342008246506856060350b40403107801940a01d2039640550720310741c000c0108000c0f5007040304500010700c1c00c01c072203 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 587276465 1250 587275215 587275223
    0x21809070c0c15030e06010503070b070f08040905340311040f090b010f02240403110f03040f060801121b08060910060b07021818030d1521 61
    0x100000d000940100a0301006940000c903014915030b8550300900700810014240d000681080128403810b100003c605041e100c00902a01b002414a030900d0310030f03000201d003074490040d0300c626080482e0f40c100003040070b00391907000420137181401c070460135001608500240c050250402004810b1000300a145e44903c83c500850075955102c0418414002c0741c009890981408030300084a4409030b000c0612594283c0301c1c2d0f42c0d03500d4003400c00d0f030300e800303c1c5030319a0703501c1207010703090030102c2c030000356059000344207082c002d00701c00c03691184602e000010240c1e1803060b400020b003407003030b12044c15203103000740034a29003450158100140c24201050f0604010206a00c0c0104040c0003100400313079502410110045803003600d4010840b0362344440c03070840042418500700c404140d0302c000300c0c215048190080c150311580c01e0381d035030a00041c08004040e004800c10020089084010900040c41194203102e40840c595041040008036850310b40e1201c200c0703c580c08109401c10f5048102c203440d650300 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 587277715 1250 587276465 587276479
    0x203030f19020f04120218070c030806041404050601061d03072c040305130b0f09100e0a090207062708030a020d0203041407150e0d050316030809100218 67
    0x810601c980a405450070031451a1800b1801103a102d50322014811034900807200441041903d0801d02c0e07141c1c2c4182d800e800001c2e448801800801d010303039203003600031402600004048444007422001e202003507404540a03001480100b280aa100551010300403d0040740f4603003480c210300080e82c2c3e8000b1b100b141a82405c0707545101400645007042d185a190204000800d49001c2c44c0c020000e90100d0f030442202514000e02107203c95000055407204d101d580a0245420360b04010001303a041c12003004405c100c0c101204010035151104290000c281c200720160700c880303241c0351040c2510418100b801c0e83c001c4401d141403100108103e10340e81c1c10380248903140e89480340340004007e48522412908410b0000081c001001860040301c100402030400b50741303c1e01c2d00c6850700403907220322041e001d0001d104c801e4003002c1460142c06102546200d50308503458002561540000041200c5003607020406080c10420901000d008110210480c0003046162507141c1031005244d554030903080f80103040d = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 587278965 1250 587277715 587277751
    0xc090f27030810090212190605010503061e03010f09021e03060c03041104051008010c02010908180609030f0328050d02090301020c1e0d090308040608042409030f0203030f 75
    0x800f8008038002c1c0c01e40ca0415581c070340c840c403d640f031921401c0d500c4080780c2c4052002c0300c010130420700c640015500c2c142d440030300d0354075440d04000001075030301c40540301c00c00b00184080d150fa600b4071075085118400c2c240410305118a00400503014039103004155546200191400e60b9a40840d0440e48a130034000281d840761510300f016550b0404241004d82c1180c5008144810300714031102150880b10041c1c000e1105040520b012407d86aa0307810080098006100c40d6181030751180100b0140c01018104a09120300e03000007074507108000800d02096003000a15210300c10840080920140a03004000c06c00c004030800104a40304590005a41d5580400c00752220340e030170340442e088481010121080901d42101607100b0728102180c140c0c3c1480380c900030f141c0c04c6020304440b104980e00041d1040c00c2500d803a10998002000800403141d8407840d20700003040381c601d202a401c1c01190706000160710762452501905000c80000300b94107541c014030130085000c40038440c442d80826a0b5001c040014 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 587280215 1250 587278965 587278981
    0xd0e0f03011b03180c06020304150f09140105090301050109090210081506030604180501050f060a0303020a1e080708040e1b180f03071e12020a210c090f270308 70
    0x200000900405c2e0348030403140000c0c0380c2e074004050320640b108034035a80b0301c02c24603010a403510b03c0100c072100045960172030100884004105446444071041c10041d00d040c404100103400c544c400d8100c0c2c00720641d203c416409509015501c2c1380321149a00f0450b203103041c140280c550010020400c0c1e44501c10000c002030f400d8a40e40c000040e12054a06c42d6907a180301e6185c4603000e441d040300c0140060410400140709445d0064540c0f0480f501900030b00340c2e00249840780110100c0e81c0d8041107003101d61080c6003000403c044000c5c00441c2c050039641d070300c4900b80590030740b440e003001c1c3c0b80c17900304400104c0ca85140070281080780c20004060404401195245000c9074100400a01c00c50b458068403600283c1880074250681d142003801d401d8180741505d9000e6248850040c0d0b00c040d4000030408010f109038052106a0701300d21a3315050740b02c10030500ea448c41042d0009400c0021a652220014041c02d82c032070165600b05800e000491182800d2000703048410415a90041d04224803d030110303840c0 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 587281465 1250 587280215 587280251
    0x1206020706020304060507080619181803090303020706090f0b07030309050f070521060c030925080c01080c27064e07050c0d0e0f03011b03 61
    0x86a018500b5034a80c0b9040c02c2ca01c0061600701c41d00b801041802c0300294903031a02d4481d81000b0040d1140c0c841080d0304240202c00e02003481c0c5d612801c600da4906a84241040820142c500f0a11aa540d04a020304600d0004e041840980c404800c0c41000301302404602c21b02440c140c00d4500c01c0445039110040c0341002c0300a00080000a0301d00d010b039030001042d01802007000030654409541e403146110350120260080a0000100c1190307400ca04003188880794100c1c010f40e040a50700c000c941d4108900300001d04100051860107003e4840100d081010b0b41e0144140c00f5014004d0034506e14515180e0170080561041e40402c091071300d25104240c0e05030444002c001504c0f1f6014200680b100c0c00d001002d01c000305480c0c88040c3c4180c10740103c034440040e400740a84100d4008444819041c0300d5110700ca411000030b0b1660701401003d01050210038402c2194a01c081c1450740d03018100403040301400b80d5411146403003402039041084008e0a80f9001d1482c04d2881c455180000320301440103c10785035 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 587282715 1250 587281465 587281477
    0x901021501090e010e03090303070816050607020102130918061806090f02043608041508180c060304020607030e1203090906040605030c010e060f3001050109120602 72
    0x180e018000022400c4480c5510015a22070a00001c1009544024849569004805460754554010002500003074619030280110010483d903406c1054407d0740c506040c84012142240142e5000c6985d0145003900e0464500400d00418204000c01c010000c02012061018011704955143c0b40e60042600c0001d00b0a5a401c0d0070003010403003200d56160189400c0740c00c072002d07031040d400c05242d552200360402450320036511504000d90901d141080100c4581c1c00b03038000b0b48980c40e00b840000343c4e107401c4401c10402c011460341c0390402841c0088076035910107004040704003180c0c49044411455200c1e0340c1229041034045511356100c038a146800c80b04500305403c5250001d2100340294107040002004e003001c14001c13502180103036501c2d002d100c2124074512659a166103e040c0300c1d41154082c28041c40c03048400361225282062500150707071a40d01402600a0080444195500400e601c0390341ca10305214440c04482c01e07515000008080c1c2c2d51900407809500c51f0f2154540400c1480d41c11214 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 587283965 1250 587282715 587282743
    0x90f0815070e0409140c030c01120506030a120f021e1513140a0b0c031003020409050a121706030304080d0503070201020d0c0302070b09011b050f07062409050c0708090102 75
    0x7040c4805d141ca0400400801d800360010321801c2140300c030030307e40800c0914040d2010313905d28262040340b006280c003070080580119007600030303e80d0500200310b10009200c0801080c0e151103445003a02c0c08001d140c41600e00120980a9010103240c1022001041004100800c07078145100c51300d400900380d90901c06000d00501040c4110680020714401244110703905000c0c0d0b00c103594541d41c049103c2010710045a610080f5151400e046c0014501503000004c41da0282007200d1000d0903580e15807407420281181003001c181603c5035503a010700b5000120303510000c103802544c1400e2400fa0f80341e990b4800914014144a0f0106c0020f4a940c401d5058600a8111013414015a501034601038001d50003110706a924020b01c1000a0405105004101101c08400c80c443d0380f08130809000c903007a4020840150a118003000500d01207115405010308046e1a11100702050b488002100c00d80c82003903110b00c803d14205010409118000d00c1512000c9400002055480e084100101d00304040059410 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 587285215 1250 587283965 587283971
    0x402070c1508100f080d0807030209040e010b030c04110703030908070f1505061c0312020c100501090e0a03020c06030c040321020f01200c07120b07090f0815070e04 72
    0x1c0001d50b40034080034065000001d40207005916009001080d070658094031210f940300c001a11200785c4604055544000c071850010b0400202d10b0008090314900a0400d5581e9116006a250b5113000c0c0641d4150341d108540812150a036029454418010564094245a540c3c3c04080900050904844946501c0619042114030500e0030103c140c514840b40c00c0d101c2e00c2c0800050341401d191250303402880030407214241e04001d0b40d42c21950007640c0c61171150030039002c1c041070760440b104201003080d0700340861010030720358104107071041200e0302140401c40c0c55008806101c0800c2d004600d9484902e4192041560b030f0b9074041400d800340c441d65000400c028040c036100f84400b44452503400c821401c82e400d88040030340f291000b03820385607803a0b81d0340d0400311031110f101d05081d00c0d4070003040340e0a9903506665034266180580c0e08049030098054a880d0b09080810140f6a1701c1f014442c09003224500100c0141e0805d90129661101c2499103280030218001240c00c260003402c4090190000800034 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 587286465 1250 587285215 587285249
    0x60306011412040611070206030a0c020f0111040e0a11162d020109060f09180f0509030a090504060f062001060b070b0108010501060c150b090a05061906020c0402070c 73
    0x702c4080111419100c540c035059504540304e0220003100d80480d001003055042d40c0301c40003c10010251005504154403c000100d24081c2c030038058a4403c0500032015915240b81c10b0060611803402062461624600074991035035402c0d000a40300c0c000c90011030416644840d1502c0500c00410351194145003181c0044c01ea120302003099440e6516100381d03a0031510b40e03030b80e210680b14040c100114a011401004041c45407003442c004004030340c15030b1000407071901203a40e01c010440b0400c1d1814040c070303000069605041a000354072180103140c03e850030007020f0f103480c0b03c180c21544540039007006c101c002e241c001400800664410380a1601000030031132643d81c0c4480180c00d520004040ba14040c1800000078002c0c4107101c2d00f03048a8880c1c88154074144244d071500d4803494000c090b0b0920340c5c2c0d541c00009541c2c4410006c907100e103480c12000641420503900304400490b02864004400e0040001440344035400300305d03442c0c25a401e40e00541c413076440740303006600c040240d00444500a0b2115038 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 587287715 1250 587286465 587286487
    0xf0304050c06070c0302010e09060112200a0e0114070809061c060f06030f0e060601051b1b1804170c07030206160c0f06021213120302011d0a0b060603060114 69
    0x7130000300d038400d80f10401d5400c2e6841c00d10240420403603045000c41c811a205984640b840d0b000300440841d0a05c018034210f4a0a40480c07907900919a00000540c5144881030b1550b040603085000820341050706041c0904c0d551840c4103441f9161189004100104140d0304c8e00c01c4000c088182180b100d035040c00035580302e0640f100ca41c00d1038441d42c1e000900700b40d1041c00d40e070090310a8407000305000c4040c120954541d00107551a03403007400042c09004e03a541c000c5940f81010300c010950711410401c001200d080c004100002607001c810004078221030001031000207800302e0b08402002c902043c1c2180c41d91205041c1c242052817aa0000c1d40220002490003104a0802e03152040da03840703907540585560b150760940921041500490016034000004880e210b4264406088d041c4441c400154600351613001501540e051350f0310490160b911441a000407440c2120755500c60100040241030044554848243c1c8503006080c82d8010080000481c0706079110358544a417140311040f400da0b459150b04030f = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 587288965 1250 587287715 587287733
    0x71707081204031b1e56060f010203041802041a0306061b010f061d09030c0703080f1917010510050306040f060509130312020306060f0304050c0607 65
    0x2504034005141811200c070f011034212400001507801076003a581c0c01020501c012800411114182d0306242d210072003c2080001e000c4203001a1542480c02115240781b0b00c1e42c005029a10301424040e506141580804403540300801e540840c1c01c454889491104000507030445c403c0d41c00c6400b0081d07010f14001342011480d0010002c82c0d6059600b03082207241d580d1a110300e80801c1da41541e0040b400c01a07405a9440ca0700d90380200d0b4541800000d01440781c07411081100c0313080c0e10510160801800001620030460300e10b640c1f00d00618081c6103002076004a258076450140001031440201041d02902c118900d02a030b01c898951590080ac450301c1003074007816068014154003551000440003103001d0a100c400403070001200c4c1c580b9811512034200300006002080c2c4448200c980c0c80000003229a16a032015010310001582801c0d0140c460130700802d40c0d05a20071940c2664010403e0120549a09007100d81c96070301da000642d100d0703c552901c641080c140818080d80031001040704810300002d40 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 587290215 1250 587288965 587288971
    0x1207033b0a0906080c06030711151906050919020c0601090e070b04050105090603130b01090213050d0b04020d080d050403020d091422020c031812120717070812 70
    0x7296111101e5031000c07400c0903a2064000c1c54103540080420304000c0c2800c00144d50001c4a90030640e203043c1c40010403920f403081c280304442c0c203420408188860398403070004691412600342000e101c00c50a1002007283c03030001030300950b8608900c0d444000003da56038195800c2c0401c040a1b1040e55035209120000780c800a43c010b400380c06034410000d5040c411b80f08417021200107865060a140305a4100700380c941000381204459401107011a0021721070550080c013a20f41008010384484912071180c2000340310742c00a6000b01e0007540e2403004681d20554199003d64104d80c0402c0c00c04951500e0480b40c000d5400c100000760900082c8010160003203250440095940c0d04d0340301059031152264180e1040d03125240d04841e4012510410501100013001101200341001d8581440e605074541340d503100e100030b4184540e48542d4140300c2d15080e1030601c8011a80c000812042d01e41d03650790b80052103461401006000144252001203c0c110280c030030068025440e9070b03c81605203003000f1507d1f012 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 587291465 1250 587290215 587290219
    0x200102070c2607050d021f27060c080c01024006050a0f0e03070b07020405010b0a02030a05070519030503041101180501050304080d050907030c081207033b 68
    0x116200300d40311095103100d400303030b405a800910140d8603100c1841100d120620050b604402c00c1e21500705502c0080e42049252075071070b0355404c00d03800080f42c00c6c11f00d01403050f11001d184055038800c01100760300400c0c0a05447c1c02034445540c41900070452030081c818070140901020350180704004080e03002991f100424a241c840070b0000c0041642c10003408494060000411801d2103030301081c92103a012032141c1c60a40c21306540c0382c100100020300d00600c6a10003500c6400000d040c404506041c0560f5005050f07000201d403d01403500c0d00603440740911003015042040c007055a8090000c00c01054090b150407400e0450000c4850a008240b94021202514441c0840e0621116540f20315401a076005100720fa600c049428400115080e0f88003400640b811001480b14640d10a81b0b07110b503c2c01551044010000302d80b440c40c120045400c3ca50011085420040b4441d0501c1e240708100c480c40c40e1b041c84c1c61040250303401c05100c484801001070401541140c00f410f03013500341c400760490541c042 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 587292715 1250 587291465 587291489
    0x8030a0b0102010c08130c03141609050925030606060305070e1504121412070302210f0c0f01090c0620030d0b010207031a040b06041407200102070c 65
    0x100c0001a030030380340001d00c40d000080c46900022260342d444045000803e218400340074070343e5902d0311072404074140100181d101e9004600d9001c045e03c0790402032001408505d2081c85a443d19903007450b10b4403250000d607501c42e00781115400c006900c081c0e000c000f86602c07540810010b9201c10004000b0082128081c01040d42244900c00501e0312120124a040c510403802d407a1038207180e5001c0264055010454071200c4900f803c10107140f040c82003d88804110300d1440c3c84090505000b480c04115040300000340201ca0312000740c02c2c119204643e0b501510f072851950300c1c3c0300c050311035150140903d03448400e03501c0d1a40c10b41c100703c04811004100da040d071740c0e5a01081110266007400e51480e41103c81598800c000c00c1c401c485950b08003900e5440140141c401c65940c80d00e481c650000401110b4200d030b040c1008000030050034600b55500000280c5003040307078010202c15110910300207032840d0b050144505241c0440e42754006c3d458180241a0700a5464a400f0300d09a8000303000c500a280d541c040c = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 587293965 1250 587292715 587292731
    0x2010203071b12050912060f092b0309020d02130b0f15031311030d021c080412080411062803020f03041212020c0313060e060901050f0706060308030a 66
    0x710110311202c00d0340c01c02c10700d90042c0d90440c802e44095020b01444e541186c403007a10707144011420b00c07038140300c0e4070820712501c220328128240d242404101202c0e60341013409100d40241c1100d04500c0308890740703150f00700014400e610340001104613803841030003940803540740c0024494420941003210280002d036640038401c10014100a60100e0088592059090a10000c0c00508444002c0c2c48424010107481c2514104040401e051072101c0200d5005a4408142c2e41040219094000d240341850310740403486003000e5442c070f00c0a25065003450b007000440c0c8049001e000540c0c00e00b950380c020040c512962040300c2001c3c0c1003106000d17000703a040c280d007002a5903c40f500900845084144041035145540c0e29a6500c5109066101080e0100b050480031421101c42c2c520040c00400c404000031500c5442c0b410307034a955a0410707000f201c20003500213501c40d141c4d00c0e41000d44810350703401d0074125202c1c4100e40d8020050700610070060486420f094000044c004188025401540001c00c1881010 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 587295215 1250 587293965 587293997
    0x907170c010f021b061809010e1501030c0f1d030d03090302070b040e0112031103030a0209280b090d020a060c0209100b040608180a0b07180e0a0b0a0e04030201020307 73
    0x70302401c1120b002402c404100b800342c2c0c90300030024512441b6040020150748131510115840720740036001810310380110030602600c0c4000000c111080c8109103800d01c8070400c0144010501144070940405201100d20b000502c03258001c6084c502c4200901207440c03248030340c1d4008010b801e40030410380160240308404104849240f080b101681d40fa941f410319030b80d103801d502001507036042e9420740030000c2504d902e81c400d0300d06100840c024441c1440168a03144280100036134540c0140800340c43c420706401c2d0498065800740054115980f04c1d45980e100d01900011420203135100e100258044010f030800700f607040d040310070010350b1070003030710151100c1d5242901e00e50b05184901910030992000e2100300101c0303201e19540c0382d0042e0035078000440702218820f190300d09642d100c001c850302c034110401c000c074170f40d4442080300207038400200e800c0b212417a00c00d100b02c1c0d10f0f00241c926142d09403103106c2c05505071141c0240100500b1040c1c0d419440e4681420000e00030340059491800165440c0180882c207 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 587296465 1250 587295215 587295223
    0x10140d02121006080f07151101140115020a0201020a0308091e030301090b06070c0902161e11040b1c0c0e0703060509060402070203100507110d020708060a0c090e0907170c010f02 78
    0xc0c1030720b03030006c0c0001401c10300c0014500c800044004108142c0103610310180100703000d01d10281c035080c45030058035414240003e41044080510004561081d40c5000143c4e0780081c41e01e00c0d032905400c111030b0301d864502285040102d0203103c6055900c62f022485081700b4000019412648040e004001d008403000c01c2041a10950201810400e8a100280320006840e4010040c0f40100700b0a20124985a52005208070340c00c580c91121404003228101801a0341042031100c01040310100b040e202c182e400190042843e44903100a843c3d001c040808012001140da4050314501460312800c1c50070100c0100905280d00a0318080c506803c0498503900f030500aa5042c541e005015010034030f910070f2288002c02c1e0051070700c0108540001c2600c000d4506000c0b640c1c103415164017606145040200d510310300f040c05046a00380c58034202161000991048041d02a205904801c58880d140e207180c142c98464507404c8802007401648003403801910006500307800c1c400c2a280c02103405400380d4145c1c0c031 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 587297715 1250 587296465 587296483
    0x30c06130c03060203250f020c01020c2b050a0c031202070b0d020c01060b0a090918020a030311030c070f06180806070f180b1c0510140d0212100608 65
    0x3204075100c1c03041c40000c82079000f80d03074017580b0030074076407400004200134080100090036a100400d00109000c48059410301540c40e046c0c900380002d00c044510b103008600c0004070b0000400950115141900c0c607540c2c420798905006410404030748c440504d506024145003036504c002c803500020324400890780c030700201d800303400c488003008020300707020341019040043d510010381e46549558646000c90702000481c05490300e6021035031120b00300d5007807886590445d000480840c040d03d142c10014001640c2d034050078029640d051504181c400e0301042440d1541c015500100500d0241e0100840c00b042079805100c1210340554950380c0c8100040c64885510f4202e01070740c6401d81218001415150103040404035040d480d14051030200c0442180380403808058000030420200000c003090f8410f0314041616900c80d10040803c0070b800d00f1700d50448800003a10070030342c040035100556520f9640f61078060b95804d8015240500340001c02e000c80e0386a9135000c1030305010519001c0c0204e45408006042c81d4 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 587298965 1250 587297715 587297723
    0xf0603082802031801020c0907020d0905090c18010512010e0402040b06070309030201180b0c34050d06020714060a050c130e060301060f0e040302072c04081308030c0613 74
    0x310384020342c02e02c4c0c90444058030035103041d8400c0d004000d10681b00c4099a44c0700d41909da0181400d001d91000040c400020b85c3d100d00d20900c944030510644440b81070844401e10f03080d48034071014043c51001030301c140c010200900aa511607200024195080c0016684154400c842c100714130304070301c0100081d60141c2c000c00340014180520900c019405011007481c00c000b1000c41000b401e40c0c40c5211107503640b250b845000c080c0c100d5881d19010070110079410000075002c4450300940c41d48194005826241485518444d2140c111007900744112a4125203042e50020905299289510050707130340c0301c81c1510f03201c4600d8076000004040c2021032094480b03100c1c0c1c1181c1500380c10f1402d01d00745070301c40d405801c05506560720200040d110040c180703000c00030b0901d009100010315080c14040c0c10640c49030b100e41903510840c4070b03000c241d901500030920100412001c240480c1c4590034440010b01464000304220300d81d441011038001000006010744010450440e03450b03990304c010303469802108005c014 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 587300215 1250 587298965 587298967
    0x150b010912060b04021e04032303030c030a0b0d08090f010809031204061d15010b0703120e010e06010609030c150c0f080d2307230d0f060308280203 65
    0x80002c103103800c034401c101c03c020400f50604004101c480f0501103245088032003800c0c00a020020010b01848001444040e81c1c00501d04960001e07801d522072000501c40d81c0c42c85400000104140c0c540e238040e003003408010345904803d00b01c62030603030a66405000e00602c00d000e0320098140310340c85096803d10403212070018608041c134008600c01e803240080e008486654a420100900d000c08454005494010307800400c400c003601003c0210307030070701030b08199510182040184003082d0015504155001c0100c00007071003d4042d000e150050000341410003460061000000b4a241e02c03161030303425030b4020090810901e0b038070181c107881813040c0d031041d0002c154030b5166180490282c0b09502040c0b40105552071800101000d0761088800400d405000318218011802c03150600c00240e507400034640c00c010029103a200c5800c0c0203140340c401941c4080a00040c0f80c48915501e801070000e6548038038040c03201c55203a250842c4c464010101c1d4859100c40c075044607281c074401c0c071440345041030f564000d1 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 587301465 1250 587300215 587300249
    0x501110703030c110604080d1806050a020a270e04050c100504050a090905150606040e0a02030f0a0504020114030702010f1802031c050403080702270a050a060302031c02010e0703150b0109 82
    0x4002408020340410640391114276400041001409a10b116100803c40183c0e240c81c0c413607000d8000101d00c42c1c3c0284c41004141b00240020f601c8152200ba035000c0c041c0031100f50b48501d0710600d858003194500f500311444001d121417058102004d0b0003035600c116801403a0a491304103a0b4110f40300080003801d2a48036410121100e06049022600800003401c80f501e025180e40041100c950155801441203a0000c2000306500410652541110905034140034606213500001c21907000b05501c829000c6000001c10b10590003544200ea0000e01032900b80124014003130461030000d0302400503802030085c40140c1c0a520740701e02a41040c906143c40d098145421919041050303001000c04980180286403201a0904515510403a1044800e00f040840c5000f08819040d0358016204541c107c0c1089018030069401254406400c44a01c0840921f041c44407070403800340458040c1003026004050010041c40907030b801c200c0c8480e6401c40c0c1405059000001140d40107254415404d182a0352004 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 587302715 1250 587301465 587301487
    0x605130807080f0417030a021e0a0b0604020c15061302030709060e060904180330020d020409050f101e060e0f04060902070b01080109020d020105070501110703030c11060408 76
    0x26000301c0d00c1c3c0c00051400c103501c1c1c481070f00241101020394820313944007050b240840c0d40d040000410440d025140c42140d210b244076596a1115a2800244146205000940b82e501e690381941c0d020480103048481c00c050102210861007001d403821402802d4198044400400500031203010318403640c2d820702038614050040310036907081021980d1000d0700b08100d18580e6250b004104400000c0c0a2882c42c2c102c3e0307441c0c060200b0340c07500c2c14003010ba0401842211a41c00c0310700090001d0150354005079403080d0840300302e0000d2140d40c100840007450b00b018000280740680b01244554052600c40f00c03615195a42081400f0298100003441d490f03d12040c130000b0b10030034054191400203000c00311340c0d10384000018280d502542048200945c045280824401d54020f194011301d1110f008002c0d01880c2e4020820ba4140480080d0612800041d5403003084425409543e4030064580001d0b00e03140079140003170140402081c000000740300501258020323080410200d003e160711812007407030429a034503 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 587303965 1250 587302715 587302717
    0x100f0b0c0703200409060c0e0a05011e030b0315060117040c05011407140309150c0307020d0219150e0906210309030102042402070e01030b042d060513080708 69
    0x115083e40b5004500000030503403528000c0a880d04c0c481c01c0e02081c50401c02c94005c01d4803110481d03244c46440040c00030806660050920a0322b22300340400703001004043c002c00d030060000d06440907090301c44c030b0264152603600d82e007580e40181805d0369800040c42e1000c0d01c8071a0700005680c06403e424181c58100080d602826143ca00e8581821039241408096110503440807903004071100c540c1c0002510761040e250124500b42e0102c808202d00e4144240701400694038025403d000f4010342c0605015001d55458244105a02300c07a450031103d00c43d00d543c442d03003d80d41d09481d003002068064a604046140041413603114101c0038200c1003081c140001c0c56080382154000c80a8180000c11029860740c60a00042000e095081c070b600c003540c40030224001d481050b880c03c00007150410350b414002c0c03e150021082c112900f10614031000d031114103140c0118100c03c07443c1c0c040c084001c01c022454001d2134a07819071150080701c041000da91107407514031140b01502070051441c202004240c0000b004c0380 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 587305215 1250 587303965 587303993
    0x305011a0a050a0309140601080706111b0a051203070605130803130618050303010e010602070e010614040923060301050601051b07081e0d05040f060e010e09100f0b0c0703 75
    0x21501140b4614152540e40b00760301a8580e006d903d400c40c1d0014840302504200c1e9500600840c1341807103e402102d81c0d41e0340c480314280c00440c45014405100503203662006800d0300a80340051000822840303081c8038a6690703100300c80441e0450700b08800151038880d1400800720182d040300d00c0500e5540c510642f4485a62a5407084071040e550f05e01c40540900149000030540d4440c10082d550703541080100c03190400141d1041085611030741e0b040c082d140f40f403943d150440b100c40c10950366500d8080b100c0c803a5400b49400039000e40c1c0c600007a0103140e00100e002245000d81100041c101034907941c0030f15003039a804a40050106204100e003a2224545d0056250f4240b928801c0c3c0303800c0d036151103015040c0981c3d80c1c44095080c195a8415012031020711030540301207010300b820f0789018541600c00c242c0314058030a65040c8000c2d90384220761a4090800e68240c417070010303c280c1c65860610111344040c3c0480c0a01005061207180100f44182c100c0102c880d8100310000030420b00d41b0350f41e80c011414a06c0 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 587306465 1250 587305215 587305217
    0x608060406080d0c05010f0e0c09070311130303030b0123090d050f01090201121e020d0f0603031d0402070c0b07171c0b010c030f23190305011a0a050a 66
    0x1d00d00040e00a0707081c8400104401c2541d941800c0c160720342041c90a6450480070070f2842ca00d0104615044800043d285c840c0b01d00039244a0f80c5592002e00503030040000a06c801d441035000140c1c00c40c861002c605102c15244291010800c82084c140111041c45606d0703c4909900c1c441d000c0740c405403581070050940350704004c103614034904107650b805003007400b0110039802c940c3d1075202000866070003002d4408404040c40b4100480c0328841c01264988000e804a0504698000307110302028501c2e8008004a145401080c092a90342e86802040840040003103c454401244011090310302030007100d0045e500003144000385400d050b2a55019804804101ca20703120f00070000c9082a046c401074543d02c010060482084800300410a0559020404203410003038122032100020744c20030040741c3e0141c030303928001685c0c64040700d601c445448142d040242303007580402c06010807201450301505140b419078061180b640d0f030303059403680c2000d40d10340540004000e00c05c5191080c8650040d0001680c9 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 587307715 1250 587306465 587306471
    0x111010f09050105071407080405090a0603060e0c150909010506160f0c240219030905061c0c0207081c0504211a070c030c050304080102030f0115030c0906080604 71
    0x30349440d00311209044111501c2e519041084009070304521901c50b00780f00c000070a482d1411a598010481c82207004951260303078844d01103400c081d03c0303510030300c0610380c0040200540034034411800e9550181c9450a845032591a00b41d242c40103001080d241c491a01624118550342000108052031300016100303118016a12103c2d400300322050f4169240c1c03030040031a40580c0c1c0c1800354800c0c240c69031040741401c00c58548002c144280e80011141c3e6881d04030502c0b000443d00c41c0c5801c6420412952029510440205a201d0645050820170134120844001008100e03036000c0c0680e158000707840381d42141e07003010785907000c44440015032075107520103450014a0107895040b4a0390034030000401460700303403100c2d6032401003025040f0202e6220041e04040380355490811002402e2300d038142c1c2e00404000c0080080c1c0c0c108001001078034054003044000790b40343d2400d507008040d9150240310310302441c0312080c40d00d01000d0207880340c400142d14a40d1510003043c18148152595a0040d1099400660b = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 587308965 1250 587307715 587307731
    0x9210a150f06170705030601050d200406090e160b0a080c190e120c1302130308030901090201021905060f0601020a15051e06030604121404060305062805011101 70
    0x40d040c0b04070006410000450b003801c0c05074000c11840c2c02034907041341c2d00a62107a001070010b591007540d2908110b13032041c624011304a1034414004452814461260000d08040001c1000141c941100c41e00c1d6000000b01c9400010302c5880780c8100b102c601c180850100304000403080c1da8801c400507507000d500400304624000d6020301244100400130303507500016164040051881c680b0f404101000007501006150100018000443e2000d0111841135480d42c009901d2456010008281c00150b40001070030707459291005c9864003801070020121b005001c1d170140c0810320341001d83c0d90004990807000401c1290741e1082c20160060000e02101e044d84569070f10350001400d074500d0069043c2d045100441c80703087c80340061205d402145400c084a20801c2d0812002d503d000a541e80d029800001003810840031400035201003143e04010a03c0710400580490303156051f4124074020641074506440c42e01000103200e0030940261561087c480080c241007085611030202e2000c0c14135000e0000130038603 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 587310215 1250 587308965 587308991
    0x603060d08130b0d05071805010f09031707020a06020a0803061003111314030d052d03090f060c0315011116061706030c010203040e1e0c09210a15 64
    0x200d00c59000f5075600c2c0300080d84410640701030041581040d41810401c0c008800c010840703900718000c2c0146410492804541440b00348180000d00040d030304014115040c061124800b200e0760310642050303008045000000401b9031001820522543e000300e459420b5031140c4080005080b994125041090344400c0c400b03010342c000100500b554442c105483c440d1740d142010258650041d07000b03840c401d4024850f444619a0400100c5260648500110092405d000a420360a8030a4075845003000004410816800000102c0c5e07241c0f551035204860741b0390748010500c042444102c851801d000030300701d1b0410065000d07000602020b1080c0b07003600d9207100007003101d42e4080103580c0008001010340745a601c07200c00707010707100390815016000b904200c14098000b07962071040b40300b0105055504030008120202f50310844016449001045a040c14503001c2103d083e04030068480c07241c4075148c2c03020320461002001c0904100c44130081c04c8909169125844003544000110000c60703100c5815150761 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 587311465 1250 587310215 587310247
    0x509030717030406051501050702060c01020c010606180f0f140102010b09241206040b070504150306030312090c0501030906022101060807020105041e1103010608010501091104050603060d08 83
    0xc8441c1031042d12403506003403a4041e640c01900c1c4c0184078920412032426070740d111080f108041d805644455682c890641e800d402807081070f804a4440d4609400480c103160b22065101c002070030701c2002c1c40200c2d22000c01c0b44401080384034250119074060400c1001c1c505031910b80b250ba080c1400009424450f01020a101140c100d41040c0009802e803141404280843d800c1c1c98031311001c4da415881281806015175940401500190200f40d403000080ca000d4400d000315009008005a14444440c2e4154040c020709514002180850280e0102d40c0403003200e4410402d5860b000140b1500701c034a4440190b0007000c0e044020381d8030319006c01420036086030f001c0b81c0c0301020791800c0070020310b90324100c2c004000c0036014000000f1a4101414000400c41201d10300758000104950350082c200e4510b80380745100c8081d80140d17055400e00c48002030b101d0041d408207040301c00c060018030030040034090a407181e00c0745005495100e01c0a00104005080503080900010310070380030389140c016910010120 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 587312715 1250 587311465 587311493
    0x910030605040c020a0f03050c0a08040915080d0c0305031017060105090c030f0f1504090c06020f07061710050a08030702011d4b0f010903020306010905090307 70
    0x826226902046641410b1050080b06030161004d010b10358110b65448400e00380da118003801300540415441c9081c80c0510484003250341c01024955500d548003411406841d5820780c10711a00d0703a40c040010040c0d40841c2d18907420170166504401003030195421b40e00c45d0009490841a0b00c207050000c20081c00320b10004450850020007420158906400c000070088001c00340d5000d40300030f2003444904e03840e0f10741498100c081c9000e46c901c00e5803010015032032000041c0c01180e1090a01c5100401d10030b1032007005041d03410540c261842c80c44280880c40e079070107152148000240d2a640d0141d8a55448c1d00030b250481d0144260181c0503a4601c000343c3c0440550b00301e003100c0e410000e9000d0456070001c0c1000308100861004100880184d030000c0d8200043e210003901d00003240c0300b1000340321f4190340c0340c0c0d006070314003110410391100007580301d442d141424a015004210701d949251140d80682c28440840381c3c0200108256070070450171901030034026006107a1403100740400c800142107085c079011 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 587313965 1250 587312715 587312717
    0x3090f030f020a09060b030a0f09020418050d05090607061805031909061d1e030105010906141207120c080304060309061811060903250e0912091002030910 68
    0x1181c0080740c010060281c079a644080315443c1380c5001001400c49200590307a202410342000548044e0f10041c410203060b5280c4003c1d030180c64a08490310148480c60811800ba024408855849002e0001500c482c8640e0072542e0740124180140d60024031301d43c04c09621100500741c0c0c5016040d1070341e1590725542201d036a50158011414808a5265003d11200e004201618149440e4101c040b01030303098018101c83d650140d081e95000141c0e8500742d005440201c207003e0b008015a6944a100e6001400d45000d0003003469820aa4000d880c41e19040c1c899940c0c03580d5001d00406858002c84007022550f01c01d045030304803c1140b0000398110140098402801d858070040b91a69981c40c01d0400c507002090807001587d840c07030208000c102840600b500000040d03e0345944e600407200024501548404940e8690b00104d6000c1050b501c4001030108441403951000300c0c5484441c0e84544400b05000f0550001206004c0d400b0a4944459881d00105032801500e20300300c40100400e48521420103204 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 587315215 1250 587313965 587313983
    0x9010c051e06090d0f0e0301090209040803100b0f040608040c030602070501021c2a18032d170a0c080c0a03021605060301170708070e060103050604090201021903090f03 74
    0x40680c90003070104581c4100d914029105205101c04c000e0416144405104c08000c2500d0600140f51000d40c400c0000e03e4000f411044140f605152040490f40107c0711107407440450903000500f0601c40d01610012036800081700c2c1884e08281084980c218024001d0ba2425202034000002c141103100801882d030141c400584e0329402820b40070b146804802d2841d082d01d240020800d100842846030207005110408141e4a915140c04100d88110300c03100711588461041c4030020030000303121801061740d100c02e8110301e583c81c0750915a0624400307145010b061640c45505103401d180d488402400354900724106500c00304855226121590884130745002258002c503034040515404100b807004129030b422100d05011300b805c0c0420600e000600c5404845000c41040200c444003e21980000c0d100010440b40b185d40c1d9603041186024090341c9850100c1d03d400301050441c2002d005142216070103130018194440210041e80d040c01c0e0200d010b60800103020b0001c030b07511010390044001036001f17114803 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 587316465 1250 587315215 587315263
    0xb0a0618020909160f12020d060f1d04120f12020a0c26040b4005030706050301030b100806100305100c090605160605011706060a03020105030c09010c05 67
    0x120094820262007a5010202c010300b0f40400340d0f010400e20005221440d06c50512030500340c00002038000c400410650f6030610b0310100e0840488426181141c54030707812540c2c921a52681e10f40648825070300039003460740781c03049690100e010b0600d20900c50050b15100c0d1110400c544002c08a070400d241c1d96000801001c504014403d154004903021007c0010080c1ba043e070300260b01c200e92049124041e0f5603640850981c2c20645494082154041c2d888c5c095142100549035000c0c41803035041d1900b001c01c411510100c0c4070b00300052460140c50594407424030350390842d2680629504020582c00b1500500310001c107001d401030003000d000b4140f07403500040b12400c61034428207051515608207c054500106041c0d81680404018104c03501030602c65617a40e101032071202449264030002d4000e0b405c090000039048020203400e00300c10030540c19200562103c10402a0341081c0b07100190000d442030011070709040c6060000c10b515041410080c134250740035682ca9060620172030b00c0341c031031240003446 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 587317715 1250 587316465 587316469
    0x30209280507081807030b0114100509100318060f0f0e011401150c050d0806010e030604020d06050910050108030703080108120d0504031b0f05100213030b0a06180209 73
    0x500036104451090074081c0e464034900007440308200504000102420103807035204c225040c40003030043c6400601c6003110350f8480707003c0c51004200b0300919010b110310407158441c43d44034009660740c5803801855400e0a00c002c0c9400c50140076138520351441c0102041c881400034400b8842c52004803880c03c00802d20303100409004084802130780404002c0d90600543c5041b40884d050b4041c1501d81c074881d1410a1011460101c640700d0b5000d02c000c100c0c2c802c84103011030f0541c012101d5440780c0300980c2d42c0020340241c00107140d01c40406680083d0010001f0504e00e0014000b0381040ea800310801040b0b8130319076445401002519800c1e401800c0036000002c030380307050503408004103015190358001840100c0b8142500c2c17a40788611880100425074a00100703080510a1100c0d0084506421200709207048070700b000d1301c840380c80d0582100c05101d600881342c9108000d00036190840442c10390a0380581c0340d44c4424501500007001c4880c50b40c0d0b030b4800440c0501a08a0000c60006083c90050726611f0400c2 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 587318965 1250 587317715 587317771
    0xa080601080a02210705070506090604050c2b02040e12030105040b0d080a030908070b0c0901080106030b01020316050f0106030b09010b0a0308090f01030608100c120b0f0d0507030209 80
    0x20030b0300c0c002d00400041121080100001d0101c0c2071990311041d40e80e842040443d42d038018403600900601803c4180151402c4c000351541c003450007101525054040d00081000e42c070015100007183d041015454107402c59410740200000780040c1020413000c0404000a0414140d4420001050340210062281d803c6c54403034802c00c848143e440c80d02ca1a0580c41c4c5051a0241e44010410140c544811100700084242038070240c0741d2001115400c2c1c182807510540d00e80010b000d041c001440d800002640300e2085c0503082c010a0183c015501c1c0c44110603400341507009081c01507845200d0985070700400c0305c0c03d2203800000e500401e5842e9403818401c0042e03013901c0300606181d02c00c1a03400c03024804950070f60119a031000c4101e900c4882c034003460006034082c00c202c1d84500e14500404417002007d90161300200d681c0c3c10196100c0108042d81c804075000c1300c0090b1079243e003120340308404030b846003098606149468001d4044400c5180c0e43c2e40040c1043c002212010740c4203c2c20744540c80900da48032 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 587320215 1250 587318965 587318971
    0x1617010e01110403080a050d050a2910050c0708030a020c030706080108120306040b03100203150a030b0403050f1b100c02030a08060402090a03060912140313260a08060108 75
    0x100003409902e2080104101d14080d900010b042c0400c0000c00544084c01501102c280c0d8a0114060000d4580f40000d80001c01103045942e4215850001d800800c1c0c01c0c05102220b00540104401c40031450310701c084a1980144c0c1c0d00c007006214003000400d12040400240542c0311565000f0401104844203050404685500803010f0202c0744006000100020840070036011142d4045510396a9010010b00034040404549815004411240c0e0f001620b03138009520811640ba103401038265590b051005406517440b014086030407a10108002a01c84c400030301003400c242040c541002d1143d810208080900a90209103138801c4140d02c0210185005100d102d0740140055424501009000740002100420051156038006400d45a07503031048a908007454201c5010000942c9074a020b140440005c24502c010800740ea80282e00d400070301e421244160881440c0040e1010541d0381c0400c1000c5000f40442003807000ca003100e5201d82d000000d8000e000c880d0b0b84e2045c00e810300e4000940701c55006 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 587321465 1250 587320215 587320241
    0x90405160e03031201062d122702040c031d030a090f0513090206040f0b0414121b0a0b0c030d060e280b190f0902032502161701 56
    0x1440b601c04c00d55204003d2071304442c00f9041080d50819a42c508a0b1203801c01601460b4040d4600d90b0f1f00165130303010081e0501c403005004100034804003041007c11150f003142c00c0d20307074540d2490703031090050400703400003e08084a8180840d01e103840c1c010319420400403a915454035400402c00c40900784e445501c402c0240300d000c00c11604541000d000c143e070010600174940442c3d4130b0712020411134440000b2600100032403154081c5140e00d80141106503841032080202221303a80c4084031851078801c0e010b080c15250403008060402c0c50389420752041091140e490741c0007520031000038004603440014075603945041c010b5a5600c0010424208480c00c40d00541d07201c6809808002140c00340d0102526000e0151800640ca481e0215211002d000440e03403050300540d15000d9030f0001c0c03200350070407401e4807103030401c103650301c1c3c0c84211000407400200e501c000b41410131401c80310558904641c0fa002c462261050310003000010049406100c01c560104c14180031b81c20b14403180310001e201e901401d0400c = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 587322715 1250 587321465 587321467
    0x1b190605120a15172b09170a170f030408030702060f010501020c060c0106120c030c06030c090e040317040b091203040b010b090d1401050f010512070e0c090405160e0303 74
    0x12840900f420721040c2d000728507841001c0c0009203d018010050174882401d4a0b61044000005940c52194145d903078180301e010581011011841a51022561800c0c1507070344010b002080c1d4507184d600744203000c440c0b00c0500900400c890038250954100640c8524001c948503640e80c1484000203140c0305005028224050f209030050200b6a800310340360264110841c0d0468492080790401401070149911007001b041902d800141003048000d10001224060540141d090360344100a03410341e1511004900003640d80d070010320003440844241a0440e000b03140c400e0345180171070b0001415404c10f45040d01c40d040b8110411010070300410010b0780d0b45540c50403d90031400d0598401030f6001040c0200d111411021800e800c40e45c80315000c8000d05070304070fa1054507520072450518024401075134048010041c0c0c0380081000d01305802180c04007102d4100801030307689000240351f0b14040c05448140e01840c1040001031560302c03401a14040c0142020710480001480c2d030284c042c460b2014a031b4001d0708 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 587323965 1250 587322715 587322731
    0x801080303071e030e150702120c0604060216020402070b0901110705032a060f040b010b0403020117070302092701080109020112240303050a090501020304081b190605120a 75
    0x20340f02142c2101604071280c840d54a224036402a00500004814690305100c0c641181c0d0610139400d800d140940d090b0f8003901c088001c00c0490b00024032410034a0302460780700401041c00903046030300900010382942c0c481a55000e8030360016083c0d9101e02c0c02a103c1404040601c581c0490a105201001040040c128034100580d030358140c6170f000e40c01c1000c00700760307884c51300700a4420041c0d680c55030000043c0664045140c40e00321103580840c1990140c503200c11250010900c9502c050486041d80d4058641820002d10604007070351062000700114100368003440f2840c07540e12900021241c0c0200240c07510400b0180140c03062266405901103151a03051880800150760000c500740079401020b040800c172411804007040300901007440325002c141c2c0c2c0020000c01e05501501900b4032412581e00c0034003c50343d40d80126500d010314014002c8580000b03800920110310750020303500441c00a40103c2001c2e001850103030419220f9130000001c113000141a07c3c00300703050045558014643c5001700507003e = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 587325215 1250 587323965 587323967
    0x6182409100b07080c0d020604050c01020601140904150e0a0201030b030a110603090a0803040b040320030f0901020a120801030b07090f030b060612090d1b0b060d0206070605040f03080108030307 85
    0x402244140790b1448000101d200a01042c40110b81c6120300590842d4000290881e000303544140841d030942d101d004841003101d4540c4017240c050304848c28424024034452400d820000c200e0809882110b20740724a2a01c2d90002680d4020340000b60b4000010340b00c504d40900000d819600c90b440c507544a900042868000a107103005c443d90003210980e48182c5036924102501c1c5014005400a44601c40210800040100c2c021055105a12a948190b502d59030b140d10b000000080d10440c80b50754005200000c0000421405004804814412201000d4461300c584881c4212241c4070800540c1807001402401282c0c1c1c0704507005842890300385038041c03900c01c14407080441c5000003840721010308041a500c0d07440c1d40c1680d102850240001d201d80c20500382c041d58070710500301c622000c030703090103040803069a620403d0049603400c5106000b00c1d5480104000641d42044003c980c031000c107020f2180404c0302031040c45d1049105840d121002d01c01800d01a10f400416030140044d90b200b041042415 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 587326465 1250 587325215 587325241
    0x30f091a0a0309080c06040b01051c030225030b0108070e070c1a07050d140402121501030f030c050307111c02030309011805030313091503031706182409 67
    0x7a00e00040c0050062070103c4452050b20004d00c22480b0308010700062041c0081014100c4504036207280d00040071294607074241c60851000340c05a00465104a900000b140c0d00c0d000c044800b00380d400d40541c40c2c3d03552200c0e20702d0a07082846d03250b00c402c0f001d200c44c154a9a0f11904a41d5504140d44503d00c203603603e41303903040191170344003201c94503201051592340a501601d2504240c0301041c00503d0025481614440c0202d4090348514402034554140e207a000c1030384100300c0d041c0036441d40b00c0e030b09644601e59080e0360410b0803810091900c1d00b140c00301d00c0600c050806144198130301140110b031001000410140300d16500c0c60410100403040c0143da0020460300b144200b801c1001624004030070b0b044000b80c1c01e0b400035805000c005050300d00c0000a03080101641d00008003040180c0d03c0c03104240f4030020034000240031402140104042a1500c010b2a034001001000d031008000e440070304a030305020a6410190441d0b201605910740341108001c0b8040c188255556022440e0040d994a11 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 587327715 1250 587326465 587326477
    0x70f0c050a08100207050c060f0903010b0108070c1103030f131706070801030b0a06030c09140a0b03070b030c0d0207140606030a0c060c11060304050c131104090b040f09030f091a 78
    0x28180e1300140342010050148260988050024409a20b800c4124442c0c40140c1c00b0341ca0f4184254a808110180c0c0d60040c540d85001d2040765541485400b81c139134074400b00c10940780c5c000d0b5240c40180500410441c6c000001c03d0f000a0180303600410f10b1070074110041c00e0008543c51581c64100000b0014000e41c40b1903542c0c1100c0c1c012405080341c0d2500400c8000802c01a00041c0480e01c1445010601c0300450304042c0d2a41c2e1002d482020b155641c1c0800421128003a44044c0d040d042900c082080e90103400265401c055940c94462030075142460740412a400441c044030a4400e5042107580c0c00c1b018030980364800001d901401e500c8400c0e82e19210550300b01e0007a40c0a00c82c1094400c418403c807582070601500025200c01d6803400d15061281ea04d03c2460481d038820641c901d003c500c0d02c580d90090030800c12120040b10700300350070201d4003c0545000c41565400c5a5164469201071059000d6048040c0c003070707101c55802c1d42c0c2c06240100146c1040c0c010010748400c1c1c5501032800c205090450301 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 587328965 1250 587327715 587327743
    0x4110904020126070e27040c0f0305060117010203040308160203040e090c040605060406020307030f0c150b010e03031e090a080609030307172712070f0c050a08 70
    0x61a03559a100580340541690318100c0c1d905907104220007011104a030082c01081207442c1c8034407480c100e81c10824441c60003000390f0003c902d1010390701a450710000f0b009400c80e1180401c41400344d00c50030644440d056950098a0643c000001000310407100c0707042c01d1188078414025072540c5002d031000307040c3c44005401c0403545010310395540202442030065502030041800c034043c281c14100c16003070362074000400c210300c41c078a0041c0c006840e15040d0101c904446054024604040d01c0d42c0702034403406110340ea45414049100c8000001424400b00e04404a4140c1000584170110200040c04030040c0b034a501c4c0258400c000120840c10400d031b0040300100000e02d110f541e203442a01082e0550b0b0240c0c0900c0070351091400340020614040041c602c601b0f655907a04070071914101e045101a841a07880c2d03100c072030444004025442c2c54000e80000082c813802201e8526803e8803c00141e54001c0c1d20986041d021410350b90204640010180000d1100311260300310141484890b6494500d000b0f00d80c0 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 587330215 1250 587328965 587328979
    0x2011e1112090309030114090105161e05090a09050f0703051b0c121908100312051308120403150605060a0f020c1c2f0103021b03130e010b030411 64
    0x41e0003040420413600b00c2c1d08054024885000030100412101e0002d030355a140c03035400c081c0020300c00c4070140c0010201003040d0703a03003030f40d10300d0410140c03c0c402c1440740c803003001c20504100101c6192203190b5031300000c046042c0001031a286c4a4400121140d000d06034001305810300341480008201441c850240001d035a00c0c00303aa914004502600e45000591710300d0b44c09401250141c140450003140c50b2015400c0c1d100c5003015640c00a4003540000d083c00018040c803140c3c400c0b034040902c1170010f4444e50580800c525040c82d2188911458441100c001900c2040c0c0007030b0130710070401c44607080a02003908800c24005182824000b130a580510b00341c041c00c00019150407684184200540c0c111aa400380c500c0d020040210300c580c60b500c2d42e002c0281e6000740c50f80c1c80b401030b2801403070098401200b0032040b49600701102004401071344c0081664a00901d804003001c800b450b0500c02846040c44521684401e21b1620384040202c0700140d01464111340144104404a580c40d80307081405030301100c01c0 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 587331465 1250 587330215 587330221
    0xa09020a0501030b181e071b0f0201052701020c01051608220603050103140a03020a11060c16142202090a0b070b04140f0c06030c160302011e1112 64
    0x200c2c221290021005e0890310b100e4003440761543c114120f901c102100106904815a1070302d10643d441094400322904460300020340d04042111902405000352052410300e2034461030034840c0700c0d0203d881d001c0c1640c0d81c0c01c098904041e90380410040c6000d09081c00c1403402c04107a0a10f5107103824540c00050011003000400110748e0558500e11102c0c20303c44103082d40c207952114001001404240412202043c0c400700c441c0000c40c000a0140c002d96060307000386800b5405a450407601554040e5142e00103105200f2401500010303c0320010f14210592803155152502c0e4180422009020310140901d541c501481104d01100400b800b405070420409a03440c0801c6020400742106030380f1a004e140c0000c82e58408010401003014001c074040c228070b01e42d0b150031503042621000030016200d860350000000c02001d0519402955000340040c1c0181d0030030880018003d0004c3c1d0907501200143d550b2034805125801d00c6683c216468140034040201e9260041865418800d683c02195060028000 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 587332715 1250 587331465 587331469
    0x804033305090115031703061c0516061b140f0a0302060603060a02130b0a0c020604081b0402130603050c0c07060206010303030501061403040305071b0b07060608010b03030f0d141e0a09020a0501030b 87
    0x70201300c503512400311051601d400c2c11a20303084c01100f245103d1310452f00020f00540b065030481000c2404207103289104440b9910f46d4060400000004190b000383e1490f070600701d10500006000034000c1d006415140b601104042c2080030042039810071910520400c0000c4011103524010307a014401404d964403241c100c00e41e00400c05440013035004d840085c0100d100344000c140401d0510131181034928106544040200307034001c1ea5002258440126010014140309410980e0441c0141e800c461500401917501030410240d5007004003d60310202c0100101989031003458018880e070714183d46001c496075110141d620020b0006400c00c180400c01c9810302407041e100380c00030000d100e80782201d241c0d81c0134080c100350048442071303840c0c2b450400c0015410b030044c0610009100000c002d5032a010290483c1501038000802598150380e564559203040313000c080c2d12a014060882c84000720503005550080180d00007801d0441441c100691000141c503a01d0040703044c0c1d142400c001c42c51007207004c0 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 587333965 1250 587332715 587332729
    0x10b040b030a0b0f130b07030b04050615030a0902010302070501020d05010617090606060c15091c090e040f051903020c090108010e0a080f121303080f04080403330509011503170306 79
    0xc02402d803860000c240031219230564003500d00310200395400e10859a40c08104070441204107400401494100700103103071000c0e00c1d0320800d10244141001411700e01c00340c80c0e6600326003020800309429941caa00600c4215045484408507c9001081c01002d117001200280c9803840034140501880703001c2104d07008010240600f1550f40c1c64861540c0e0036180a80c031a03aa518044048460728001504006071b04a105501000c291000b604880082d501c0b199900902d003d1105c40c1904c3c50b0113456800750505043c0c1c0b800a40c49802a80101a241d10007001c00c110078106901c803540c0350307141c0240040240c002180c414105074100250645a5000031202c000910a400c40840803006940401201c0f41d694103080c80b220340240e0324044e1340d58a034180d1801305801a28040c025040030f1004000080c098260802d192003c401e9464040e0350f02c001108131103003141a8055115101c00411865143c00d200c0c40c40d0081d0b0080004020a2540d207039403000d40740344a25400c011400000065803501d8885c = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 587335215 1250 587333965 587334001
    0x504060506071e030e12012004030c0e060f0603070305060f0a0e040605040203210c010e0f0307080d06050a12050615010f033603021b01050d0509011d010b040b030a0b0f 74
    0x1b81c0410140080140080c1c02410310058210203030078030900c1583c2d4083c0c8001620191303644899008007640c1481e1406901c040300806095200d0200d034207840c01611800301840c0180c80903140443c0785c0c01c080c030400000c54900d07000341e170241c0e1582c8420081000c4080200741c1043d04028002200d840f10b0001c04d090018401c20340c03651002e03940702e119401c0d225000600c0c0183c0203c1c000c0200351a205100c640f500103107201110694070500c00e11003c11580c0c0c0041260010003480000c12075502c00220703000d01001c0d8850400d00d19040d00c600b061200602006500c101944110381d100c800504c001382281400c051071804141e031728800c414074180c1911050081c0f00b4000300b02441426003081c854884010700800302c00501428080701190b414040c400d00e100700c4145c403180d06241c5030848901c010310004200303d9141d0749842c01c2203214400c5480003c3c800c54420b00125280542170309010581d010007440b035019600c0190304202040c041b80b031240e00201041107000c42c9440300007030801d01306014 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 587336465 1250 587335215 587335219
    0x61d040e0307050c0604050a05130219030e100e1e0109020409140d0f020a080f0d090818060906030f10150507060b0909100b0d17040504060506071e030e 67
    0x20022940d2a80e1000010b424000c0c89034044503840d910140a014075400b46200385034102c140c41394140a0b80c82c00e04074102e80c00f80c03201c0303005081441d0300606502604400203410f010956401e90000000c1c0180515031070b03100045020b04c8540d800106080c0d0700d00e4045a0b08411220640551840c14000e4202140094000b042800485a1410144512903245220310071a00ca040220702015010b44000410b01100e9000307012100c16548900c5d800e540305018200d01480e0030446502e00007030500c14010740c1c3d4042c501e46031301d074200d41c407540540318080c8141e240302d010180b20080700c55030380c03104480e4407048120107811543c860743c520b4002c10400760412041080b031080c09100c00c0d684400070702400d42c01940b003400700d50201018080c00da83c0903102c2c881103800c010200d815080e0361b50040c000e0b0890103081d2000d510710644411a0401c03000c1c1100c0000c040000d010481480e160040e4030141400300c0e070480c07038081c2581d141080e815a00c20f045050b50b01c40088031040c50300030b83da000002000 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 587337715 1250 587336465 587336471
    0x2130504020c010b0a0308030711150109050c071b05040f27080f0703120506120604030309030e030a051005060f030a0609020a0b0415020622060e19080315030a0b01061d04 75
    0xc91410b83d895401c2201c9d03010014801c9480d01d24288400200e540d54001c2d0300b8040b030300076401c0082000180030010710803c41104c0400c480c500148d42d10380700d82102c10322044c00e6000c41d0708280c20801a20070301e0716a02000381c240104a03c045410464440c103504440b1005910102c1e1890940c11038011141c5404071300c8000b01d8410141904180002d800014100080286541d503e080201d41c00300d250008036598001c00014000a02a030302c400040c90080c14641c9a0444410000e4500310b06000c0445d0705412414819201c200310b07006e219008801240c145c1401c1c105100426076455041a003e42480d842c3d154220640d26410242d002900742c4296503030382d0340c2e251000b2450400003e01c009005208071000241020703400710f44065a02c0441100340000c1c58241c60b884058001c840010701a4090700c0080324401105000c03184409119801d102d46902d07124203001c2c407070251013031902e01a0b00118000f00005c0c1141000c203066540c2d9040c62208450a200300507411032502e206a90400e00e = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 587338965 1250 587337715 587337719
    0x30f01020f131a0307111507030e0106091107030f030e030a0905011d06030606070602040b070f020a0b0306061c0209030a142116031107090504030f020102130504020c010b0a 76
    0x9460004200c1003031100600c000b010b036241e0071481940c11503200c003160024240041040366109800e40030011402c14200d0f81c007901c99200542071613006071042070100e03035a10015014402e0a0040c10001c00c400c001c00c2040785034001503c4201d200b840da00400b040404203c1030340c0345000341c0c4004024060042100e4841c2800d107009802d49d200750041501107000304d503040c10ba801400c021100d121038041d02560550700c0e0360050040790f0b00440b030120380c416000c0c013005c0340101100e4060301240b80664480a500d16541c01480507405d000e0700803003039011f41001040a0b607290300f000c076004500701e40800109181c6410400c2c00074041c0c441110b506000d81e505035803d1007504c401d02c1a06409210680c0c2a10380c1d0a0482d9890a40041802d601300790144568507500100500300f12505000303041c400b4000080310500b50a142440c1c1100c49690707900d00601050562207190480c014040340000c524240c030400042c07680880744e102d000e20850300054501520003080d000840c640030090940440c240d = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 587340215 1250 587338965 587338987
    0x8090a0516051f0f03020c010b06030f01140a06020d1206030221070807081c1407050f010b090601050d050402190602100b040c080a020304060b0a031401050f0105011409030f0102 78
    0x81e45115543c4541002c03110300451041200001c1c0120049440f020300b40c041075030040d006500441841101951391350764040d844e4589000842c401e51348001000161b60402503190341c440e0700b040d07032031b40240d00c0200b080c003810b0780000384c0c121003544038207290760342d11400b02030100a05030035003000b50001d11204002050007050350300c034034814400c0c0c0140c0301e505485a01c015540c6401d4400c44070540d0100202c0ea83c00d480c40400d184d401451403416504041d01c1525800580d4050001261903911801d11081313808030030301c2881d420302c0d0b084a6800041c00c060300002c1c0b06006040441540c1e030f607540042811541c03048004014a009089507002040c0d80b004040d442d900d0b4000540d80c680d00340521824545818840d0309607820240d11038182070303110020f25100a4100070000c580747c941c2c40c0b4065a00b0340d507202d41d03032000b588102c045040c811240c426840c00d48402501189000882c0001805a40c0e040b0851038220b0b514105140d0701c03211180300092802c1c1940c200a0901e510000b0500c0401d = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 587341465 1250 587340215 587340253
    0x5030a0e03011b05090102010f1109120309040615030c0c0c15030b0907090303020601051f080c04080318100c0b0703230103060501060f140a08060402070c0e0105040605040204120308090a05 83
    0x2540091f0000c100c0014030f0440c003416103041d2210324480315000c019001c040d00d040030751008004020011030341400f1014020038100c91141d001504901c5150f8440a14250f0600450581c1d1301c0764034005103e0903d40d83c0c0d2849422440c058845121411100c113843c4030b06c07a07481402581c000801110050808074405003640810b808294014040c400012659040150701601c041d0300c540c20080b0004015107044405a130301610000d00104100720018450000700060481c0d44803403416070300700c11440360411015001c95544a02800300740360040d0045070045000e103070b1200d0141004141d0031201e81031100402060112610b24010002c00403040c06066031100303040e2462601c03980c1c0545a00700301500c1e8102140d4500ea8080c80030889941624810f00510f500180040e20143c10030f80259910200200c0c140c000d214642c2590b40100440d01c0c043c020103001b440b041d1011454103040c11113035a1100c1a121b4054203006088000c20742c05001000703812003a68000e4241c1c1d59040c00075014104c0 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 587342715 1250 587341465 587341477
    0x1303020c0a061d0a0509060402071704030804090513030e040209010504030804170d0810090911040f050709171b1c15050705040501081324062105030a0e03011b05 71
    0x2c501c0c074a0b0428103041c01c84c0c201d000d0300c0300200040e1165540c141000045e60009004817010b03911071a41d00011690324015201440c0705400346921507080c00c0040b012030360014107140b4080e0007100f411003c0ac0d00000340071198281901c0c0580c0d110210b100580e1244190790005049180000b070000b070401e4504160f03601509002c040d2040980c400c0c50455000109807404250140c0b001c0041101c0585548219207452041e0414406190741c6800142100c082100210724a600d031004c2100d8545c0c424900c02c0500240c000031840000401d030703c29039807900d600c0c6256504111681140055913101e00d0130684540700302c2070f0200b5088528000d20040408038010300098108408501c0c00e90041054805407441030f03448035104d0b541c21f641c0e551220b1541c0720035900c1d84510b46c0c10640b08400301508a041070320711900407840d545803100304118141e9205180c000c18500356540d0001550200450760781d0501c0e480c009004405102c0040e005010005900c0918410074241c0d4804d00c2d0448041c140c = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 587343965 1250 587342715 587342747
    0x180e010606050901120c0903060203040503090120030a20013e09091306021308160e06060304030905030d0f110a03020c04021c060b0c0d020d02061303020c0a06 70
    0x550707807050250303030034018400d07880e010401100e2030307680309245039000d029681d6891818502d81036407a01c80740100e9100313440c207480c20703040040c208610307582210b500b00707074100b4000000207104560414280c1340d0050710707941002c000039045120708071102d0114080c0510030001c020050784201004e04481d41e15259102d222034400100c240d0720715031351460000d5581d599049100d02c0d044604007006403446004103880091035130a0068408240d8910240903194540701e0160130310380c208000300389005402d0400220040c1c09440902500e10000d5110350003400c1a0750325034581e11f0340e1809681c498a507410041d014402c0301c82610816600030344195881c020303505d50151894030100125240c0700c0c45035018025a101201c04612814142d008065200c00c0c0c000d0f010f01020440810b1090b26032540c0a40c04946000c1145c6403100c4003484200302c86c403202c0c0002d02c0590240300000c0d4a6010041a48081c83c00c0d840054051500030711052703003c0e81c4000e120300c0d00d96480d048090070b43c00c000e0000030 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 587345215 1250 587343965 587343971
    0x804081501081c050c0102070c03080903070b0906040302090712022215020c0105030604180506040201110d090302090a1b0201051501021609020c0f190b06040b010e010810180e01 78
    0x30415808100c141c089043e543c0d01d0407003c2000301d000da4031070f485445c400900399400c001074808211480000f0014500c9002519642c801c100105403801c5241d40008140328000c00162020340c2d103d0003203800b10707075064a01d020716649500d010780704000d05d07486001d43c03180002401161300500300f84010f2803400a00803104940d840d20343d60141a9170300002240540e010f65044512903020702c02039079208800800c0400d03a0b2000c480b440c04884000780302140e081e07001100340001c6681110402d0302d4202c0080c014049140303010402840c2c0b14882c40081e0042c601280070501d901200e40154001c0080302c1001da0041d060554028000c000445040c41d240c030080f22851001c0d031000c94000d031000d0b45982d00034812410301034204000e500c00108061184180302045024050a104840c810580c078913002c42c450386281001c0d483c0d000c008081c50310440ca0501c01d403c940c1c2c0c00c01c0900b80071860a1802d24403d40d00c0d251900e441700d03e9500403071954084090300003191111a0840052000b00c40e000b4 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 587346465 1250 587345215 587345219
    0x170705030d0f27080102070302060a180b180307060216020f121b0a0f06020a0c050306040807030309230d0215010b041721180a061209030c0804081501 66
    0x8981c60000ca44000e030004103000a20110100700c48aa003c42501030a0980340142d0340e11161802c84c1e011141c1240546c01c104104042d02d000c7d03220340f02c0c0303401c1d4007005601896840d640350b000d038020042508a071050041c024100a9000b081074508403a405801150b5031448003071035111540600604031b1081c00109a5802c4a0070640703005400f9038903620081c24279a00300719060351004403517202d854125100074000911003036800c02180c0148100c4c1c0242c9500c9105003051a01401c1700d4110070f00a41c4088141700000f01d24000f160406505882d0010310341d2071920704506d40400a141206032a5900120a62107600201359229105074a8007100c00e2195089150000d100e001d1158083c00c2400340001c2140d180b8400304c040003658640b003078034001d10102c0d00b003c0c1c1000c242c00440da028580424030b0b025042200c08659060320b02140c00442803494000028800180007000f417590075114090074081500501d204e050859000382c00302e4032161201c60f01641d80001c2400508105008000 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 587347715 1250 587346465 587346467
    0x130c03031d0a0b030426030114130c090501080109060506091512010308030105030c011706100507080a020309130203040209070509040f020d0b030d090e011e08190311120304020415170705030d 84
    0x401e1b0328820400004600390387c60006c142da41710001000190b00310001c06600038058034184a4504030102c04d84a40c200d140c1000001070003600140c02ca1962a49011828445591441c00b55420030308111a10103c05800e8100003400c0d00410444005150b20071001104019040001d907050f10800c0e0f00711200300724400c0c0110b40340700c800b00311030700c10b03610010105010381004001d918201105040c0113107011111741d0380300150380c000303d0000c0041c0c0002c507031304005281c00d07208143c200001400035421402e0540000c0c83e0f202003d0305140622000184e0f0740250784454001c20304005c3d090380c0454940b1402c030307881c41c0544405843c0303034032030b010321558002410f00501591080c0d86010001c0210340c1c0c00d02550044030340d0300e409100c4c025108400005101c045c20401c902d00381001030105200e00806203000307422100c22070074030580f0b504490046c41e80c224444066a9104e60100e0f800301e20050b601342e4134003420256400801c0421140c00ea96901c00c1c0000072060101c85054045078151291298 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 587348965 1250 587347715 587347763
    0xf0e0f0c01180506070602090102010207050d090e0609091e07090609060f0e01080d11101e050121020f0d02040501060801030b101508060f030f15130c03031d0a0b0304 73
    0x24071940144c00348413000100d180c0358060314048030180001850040503460300c40c42c2420b01c0100500042c4500c500303126030134000d002250001c070151030b101018100386001c152103c0500c494810004904e02000c155010100600e1000304080385080000640700d070f0445015060f40c1c011504403400001001402c0c0c0c050382c404038100d450100c060a92009403000c1161804071968888007544240361018840070014072924080f0700c2924030140364183d0b00c41402068503416417210390301c03076900e040c40e200c2040403091103e429681202e00e01800944140040d820a03218207000e50054134040011035050342142506058902816a82c050b641d1020380701c1c00cc10403e80a29450340130803843e002100341c019041d032a00002c0003015100013604120100b4a4800a46050045079020301d91000340c80590441d05604400c144d0a90100f4a4840d15400f5500c507603071100900b0020000da031241e038110189203045513040c00926061840c1d5031040d2040c040c0e04107aa06880c00e91000310300c0420620408 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 587350215 1250 587348965 587348969
    0x30c06120509030a0c0818030106090e010b0d020102070501050f1b1e06130f050c090c190311070807050f0105090102190e01080f06010c021503070e0a030f060f0e0f0c0118 75
    0x5030701c004140d16903a45000041e00001900c20703001c1f0000914450703664081c01414007030701e141e05001551080724000e035400c0d1403840111600490b039003010344000d40d034041400d00540700207080180c0c0e50391224010b44039a104e400e8009907480c00211072580c080202003810200030302e50b40c1640b892501d003102400d849900c181c4880c0c030071100c4441d09000040010500008603405082907550840c0b181002c01d00020040b103a0803400a800901c19001880b04442d03039803110980e2a080103032200ea60b031011020b01c10210040e000910114804040140c10480001030020080007030010b0300b011a00c080c01b0b90004510301000b00c0c0c000d9110518140724200d10103103140c0582d140082520f840c66100c000110150402e0b04004980a090015071220044100c0b911a01800195203241c5a04000c0504942404c003a10444401008001242c03042c0700c1c0c2c411540c0c201c00000360440054407010010014422600d40500a0750501c042d49140441d91075071411003a04c45c85c0c5261003074140c00007902d050b4 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 587351465 1250 587350215 587350217
    0x1050c100b0a081b04180215030a06030f08030a061d0712110a26090d05160b01060309051c020a03230f190c08041e030c06120509030a 59
    0x11444114010510703004111140c40c060716101c1c5141e1515030301402e0030030300074510005103940c188298a90400344200701800204042002400990364009220380e6020303d141c500e003803408000f00d10600019404500119441030b903113810128245400340e55038004840c040342c00d40c0341c00030016000650a054118110990780200c070155107045095402e141411a03c1e280e0f9503882c508012400d0b4040002c003403600ca00c0d294524541c8030f0700c81501600c0706070058401641420070070310a504600003006203070f5070110f0500035228241150b049141101c5d00c038004d480300f0402c1e400007426a405a0001076914001e905881e0451809881181d0f80903241880000503400b417141d00c1f001c244a43c100a60054200d40041d400740018914250250041001e82d605488000380048481c001c1c0a821010a82c95007444018110b0039210f9034201d004a00c0385000406200c0c0c0411204d0b0241302e1080040c56101c2001c055140e29018000c16a1001c1c0c22040016440c2201055800000100340d4047c0b400c1 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 587352715 1250 587351465 587351473
    0x60f1c05100911220c120e010213060809160e04060b030a030e28240309030e090403120c050c070501020303100306021605070b07151a010813020d060e060601050c 71
    0x61200340107401080250310000100c20180d44131034003165010300b9a04032050b594140751548443c6440040700d010380024071880c6c0c41003140f6006d81d0f408c14280c4084407031a040150150395041c01140c108003005801000302104510042082c15a00320414082c1c0e004600070492040c0351000d05944904442000e40401c01d0300c07045d9075680c0b0f00302079045184425a2503a001e00d28690010044051442d0441c01c884100d500385a107039200034100841c1a400c0900e42400021100e0320094008100503480d103000b880c85a0014085c103001b80800105d4001c10b9204019442d5403d0b0000c0c1541c1016400400f5400f502d803000900758400820340b40501042d82020043c01d2855880c80001c0d8841800005001000c00b26032002c9001800110010000c101e20b0658800013460803200306960050080c14903847c1c86510200c0d614440c1c01c0c080d061400782410b10650304d40d401c4040d01c0700a40100258011151000481004001c0c1c20520781703a001c1030101c60046d11100700544141c01007d40e01319031640 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 587353965 1250 587352715 587352743
    0xd03051e060906011101090807050d14090f15130510030603050606041503020607080711150702130f020c011d01020f03071412090313060201060f030308060f1c051009 73
    0xa0030749030300b43c0c00c080b05050406032070340c5100525080d25420fa105855004011900c0003e00a00744880341d00071081d45000704601c60000e120039581e00a00c420540501142c8401142c1d035140c9207080325011403060b4116845504040c107444503c8510b000d41da0081580419008195002c0d000701410390b94440e001c0d2105030b4030641804020040301c1c02aa00001d810040000940c54600041c4000307030103040c0303440d03490030340f810310b103550407038031421140600e40c450700c1c1082c81850041030311801135040396520b400c1c407070844c5000050190b5030407001a0502c006039440d01c13001d055001d012221900d6501410160599804500302e02440c001c0f1401d4200c20030004100034425207003500e514142c02c2c05c0500741036041b458694585001c0b0b403c003050341d10005d034060004034449541b4009000c42d00c000d001e030740d051020040100c103251200800340103020000c40c120307694842e541c9001c820050900480000114090225903907502010b4440303000d0303c0003004c8950900d008152a0640100340390f80404 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 587355215 1250 587353965 587353969
    0x8041211100e190902040308030703050907142112090405060d0206030c03040807150f0b1230190822020f0d0c08010b0a1e090507020a140d03051e06 65
    0xa610045540c3c0c0080790090041081c12080c0b025101560103480c2081c0ca81c034002e000503080303810250005003ea030021b0070030001000c0c240318240c21348805031011080691500c02c0f400d85005d903849901c1d010f024403440f8201c0b40d24010050207107030700d04650034040c41c0c560406112101b008860069001482000041c2203040140002c1d60011b1080a0492a018180e1101d00c01c2c1e0b1020b05501c0100e940312141d454000c10385004081042c0c4c1c0854588030454400e011965480000000160491940502040d0320051114481c0c51400c5040d047c2039854440458680381c0008010703402c00403c1c10003010507104c80c90001116106200c0030600271842005808104103100c086500c0c0b54030038400350a5500140c5034600340e2000381803200c00400c0c202c04100400c040c18100750842050b480c8030742d0880450301c0140e40a01c007210380d1040700007032541394004101d00344161500040d2107200500b40303541c1d00400000e00b008a000f0647e40400442d10f6611907603241031602c0c445000310246041c003186140c = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 587356465 1250 587355215 587355229
    0xe0a06090e030301170709020a0e0907210b19080f1c0906030f24090b030307031b0807020604140a0f060c2d05010501090b0a050907120908041211100e 66
    0x905141800c4030f06151f95103807414160fa1040c0956030025040b001d040c082410b01460260f00b001c298184040c60b1a42c1c2c14018284454420035203041e980c40c1c025043d4142c60700e8681c8c600404190002001301381d10380a000380d58500d0003291184038401c041100c0340320f800c03401c401e5600302016550118168a07050085018041702c0040300030a95171484c0b0b00b0b030f00724000a240d8070b682d4a804401903e25290081d000111020b4840c0e6502030340040001d03400281e0320030800c000148104244950700519824003080fa401030b400002e410110010f008034a81c84d003151040394483c0111007800101d512800000003074500d41c420000428805d001e888000348c0c1454000303450606114002005400544560403119203840b029642650345a00500004015005d8507004000940c1c2002d1103e00d007001080e07088900400c0d0350f041142e00c8003035000580e032036004030f0740c0285c002124940380c0f80c17204c90350031000d007442508417404405652040d4603820002e940031402c50282d1125074800400105020783d03 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 587357715 1250 587356465 587356499
    0x8030c18040501060e090f15210307030c0605131505061504090f2f030702120714100509060a0c0c050106080c0109080109050307080706150e0a06090e030301 69
    0x401910891800d03400d031030700e01c01c681c028030056a800e194500303a5070500c0380c411409007180140243c03900421075195404041e4a0300020240d544800d0010882d002c1c0d0011341641030150303680c4c040012a5414590b010070342c5501c060091004200b6515088482603824041a0001300068003080c0c200d00b141c84150b002d00d51000d405060103180c1032154250003130326801a0032000d00030396182042812a80141b0958180058402240720498030307408026002980454002c0f040000000007c0e040390b1082c0003056030507404440c0345450760180d2810f1444d8800d2240903802d0762107800c0d2602c4010302180100c5019200c884090289900c0340400030011782110300841090014040150b8001070007445501d0060030013070047d104004401c400101580c07420790060348244c0c101451440816004801c1703904080d400002c3d80c0e940c0e81c0d207203050000b4010395071a00e2400030702650300091840f19449158482c211a040401c40251524461030031218210310404070ba82c030038401401302000030030030480 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 587358965 1250 587357715 587357737
    0x70501080a0c110a0c080708062424091c230c030f0c090603150c03040614070908060c0a0207030b0a060b04120312090837030e0d080408030c 62
    0x9110650310729194680080500d08650b408900401000206c0d814003032000501026006820300d8100000d182840c100c100b0504070240a5407503500d0096510342003c2168030b101446040e0295509078400086900b00000160080400000c0200b007888000d1200c240d0583c4120800c140140711000c2100304a250940c03e2950320424001036030319a000c001215404c1208002090358100102c2408032985002d48140d001303500c15103181040e82c1010a023154403140c03510004d5125a282e041000140017440c01d002400c000c404140036800b980010414191418502203071016110f40030030380d407a0b1090800c3c4800680045a0034030014035140d000ba078001c000710601003080b0b9200d003039050441d4040c0d480720440c110048810810160000f18501801e6900c41082041c07190548a801440c0300764044a91486650175840c0002c907000b840c4944d00c0002140c000741c07481d00000780070340280b400d042e5410040c0300e030400e10680e4034460301200340710725400260b2501790b48074054441040c3d000b43d41440 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 587360215 1250 587358965 587358977
    0x81b0f040c2010021201080c0d051b0609150711061801030f020f03090a050f031e09010201060b03070c0b15180712050412120501061b060209040207060e0f070501080a0c 74
    0x200f00072580050309040e400c02114001ca0752610782000e1a0080c0f00305560b009207a04180403005c40c001007035080307e0a40221041c0c1d01c21025400080c040d104030440203610044041c85c140840c000d02e406459581d02c220f020b100b20a09940810405005262038407201d407050303d01170a01940f00344c203c070022031131485025040156524880b4226001103405400a41c040c191003002d011040000e40f41582825029503e40300407280905011900b40c5107841d0f040f140040d806035164800d51141c0300070310a0008450b01d90070040001040c1013180c41c0c003654849038240106110716884101c10b82c045800800c2680201046a5941030345500140040103120707069007681c022002500075544540d00c0740004030041d4070281005842c4502c1440c0c0030082910703000040c00f009400500504024200c3d14003580f00c0c0b9007516004000c4d10840110301d4009001058000401416400c403414112900701500c040c5400d101003280e42c0c11326440743d140011039800211342c150000307600040420000b4036101e = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 587361465 1250 587360215 587360233
    0x12040909020a0e180d080402180c1308030d15080312180604030f17040c0e1003080d05010305070509090d050f071a06100c030c080c0304081b0f040c20 66
    0x450060125213135021001c0d003a940c03646025040c000c4801d20386807400c10003514142a004588004450748180c0d010107948000724801c0c0303c0c000305032030400c500c40211003c0680c690b09480c2d1250842d04002d030040b03080014818680b1651210300d41943c444070300843c101003448070070510100000d07040c2c0c440010568599405c0e02c0307007446118840c9010307480d0808a40b100090040c244418000304c41d00e0881001c00340400104000c0f82d01d802c440d542c01d400c69490b01d80c86110341c4c09404950004010000009120510600c1c036003240f41201d01650603211201e40c1c036001d02c0311600c0b04581e800643d4100805850103540500003500c1210114940e41d0b050034441d680744240d810203401c00c841c14980c0d44040114074548040147ca481c2c03043e2800403880e07142654040e0038080b5942c0300070704c08040841c4d180902d080030016a8000c0418800722402d803e0080c1414207000d0b03014652a0040c9a05440d016003404c140c0240c2c440004241da6008103403401c00454401d603007010311340d400c00e80520001 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 587362715 1250 587361465 587361479
    0xc0b0c0405120d09050d11010c0501020904140609090303040822031e023303090f01050103080d0c090506040b070f02130e0106050307060827030406050a0e010212040909020a 76
    0x42d121095a200242030b101c4860801a28a109581c4807900c00e40c9a941c42c003000070200e0701c4601400c0001e00340041c000c003562401c00d0190080c4880b0b207402a140c004148c10350180d0718210307401002d0590360b154658403070240c40382c0c89204c1101d016110340c10401071612921880e19028000c90300351000141102e07101d03a248100d4190501d4821201c80d0f440e001e2200750319181d40d082e41401c11000c001a84013003101071000b01d8005001010010b01c0020001500c0303108180040c2c2c8182400d24001c0060f0360710f9281c03903001e41c0c20a003030100d045858103000342c00d0742e4050340f40042607070b100500c0c4508051824000340c3d49540000d4080715003000780f4106200586031210800542c246040c00400c0c40d41d012280a400c44045c2c0c0d101a10070350003044200000c42e0080700480e00008420000d103103e003106100b00c0b0000f40c1001d800100743c4000a000a00240d00c64003a100d0f02106a40345404420807a00499803035070098070f2501c04060400040050400d50b0b8092081244090802c2d8105c640d03400e6 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 587363965 1250 587362715 587362729
    0x108040b040f05121801020c012309150c0d02011812030e011506030f0501030b0109050c041a0a0306080f06180c060d0c0e03060f040f08090303130801051302010c0b0c0405 75
    0x34031420640303400b1445c0c1e40c507140e00140582e10701710284000d02032000d0620000b004081e014002c552800e4041501c01c52118101d070840d9414030b0054088220388801e803541090341d510980c41200240102000301600714410300440b0652642d49200501154031134440d07403015480241c0810a0503603440c8041004842802101c2d41c00d900c1032a03142c2601d182007c09001d03118510700101c5001d140000520008034051a058151015000c002807940d03a2031500740c01510998005000d003100203215042c407000084000c1c90010416581480503507500c040f0143d803007404060502c0d454100380000380842d00268540074026400e041103425040e03982010600540c810a68503c10640310306202c0e0056401226402c00300d00c040d0014551885d04140541d242c040c00342c40200210004440306044c0b1010340185d942c80500241580d44e94130b8a0150f1020540243c03042034030b0323035081c0310000d18000c030088100b054940d0103841d204400303112682c4012100000800c041d5081809000209454607141 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 587365215 1250 587363965 587363983
    0x70b0c0c0105090a02240316030e150103060b0603041101030506010201060f061e020d0c0f06060e010b03060306010f1215060305190c08070f1509051906080906060108040b040f05 78
    0x29018101000b8680141b2018900003403030b102034030540075505d880703007002081203903405000c011900d450441c1e0040704401608860b0360070744003449100c3c04042c0c10155000d09a040300e11a100400000c400e003014092203010071500035113010000b030711040080d4080c3d0446540300d0014400001c0290b03c030203a1032130f12800c0d50419800207942051400e40090760520030407800d0b113240014029141d00c80d4004100707080790711008000d502028011010482660044005400c0050103107140e90f071a154200320a40003219014801e1103500000600b0001d0300c600041a200790703407196000c041d010349038059a684003201210381203070744280000124400384414492a002d40800d664038003400c0c10070a0076409103400030349298115a40400004012100d568103e5400c000ea00700d691200c088140c1e8440d482d9440690412038107201038041801a06803072050740c5060f15a0000354484c98500e541d03500040311040e01013078180001c10045800c03100c4440e405845005842603941d0309950f9641012458 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 587366465 1250 587365215 587365231
    0x61306080d030204080606061e0a03060906060509032506111609240e01091d100b1305040b1302061605071401020f102714060714070b0c0c0105 63
    0x104060201181c2803005a0300a0300c01c62305542804092440903411240e440c00240d030706180041c1018405010f9080100109a400c80c01c2200940d18600038140e5800303080d40c14424094400c28000860485030315014111a054042e0001e5081c14010b48000c1c44070090581c580c4100340340d800c0140e0310030300454060421030001180c240150025048510840460480c07407031070014040c0030024132000c0c0c00c0d0440b140c88a002c280c803001c04030404041c030340c40d1119200030302842c6071010814020b900300c40d84000c5c003501d406500c4190000901c00711034081d900180700c0c51602021800b000300ca100314000d250300040c14180340002441c0d01f05558030710807a0898550b00706000030401d1f812002141c6004500a0024242840d070408505898420113400c0c1014581e8562940f0300710710030a14842520081c140315403c0390219420200034620030a86404a2445120000344104d072081c402c0d09020392524004505220107a41c1c0d002d0030480c000c7c500d07030236074405100381c05e842802405418060199 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 587367715 1250 587366465 587366467
    0x901140412030b0603070f0f030608010504110112021806070203010e0706090807050109031e05010b12100c0207120f08090402030a0c0e0f06040e0c12040c140d030503061306080d0302 80
    0x4018080e090f0b03a50224058420401841084409600700400040101d03281c6840c01205820a0301900209a1034110301ca19601c1c05040004204d0620b900c000c108200740c0352469111410410326040e0301c6103031901c4000c20300c1080020520f0a140c800741c5801340c4020004184412200700c81443c0400390352160300007494042c003c2100030414007420003d03080a02c2c200384d1071421a11803d50090b400c503d46c0c100f15840441c038138180300c800c2d0b03c1018203810060075550b0120100c40d54507581d60702075040e005224603042822070f070580009a10030880d20b206190143c0c40c000b07074460341c0c0598460082590208070411a14003107984500c000d602c036100000b0000340244510f0f00003410b00242035803040c0104512504c500d480d55447c1e041c3c0c0c2c02ca03402c010a07182e041d5a0b9606c0d100880c05510030076250304650b01c0500042042c613003404001d464400d624808039941c0c41080149010343c5410240114000300003185480c145075510740c0c691040340202081c6c1c1030751003820300d18000d507150200f00044c1d4 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 587368965 1250 587367715 587367743
    0x80d050d060b1204120302070209010e06041401090b1c110907021606030e06070f052a030d050619060512060102010b1807030b01050c0c0405041e030810060f020c0909011404 76
    0x340480c0000c05c1c00c02e8a00c0c046040464030b9010078801e031018001c42030381c5150715000078403982c0c59402055220040101c03090495940b07058580c090900007103030354401d0702e81c41036010001d061034042490140e00500c81405a042e49028090f03100f402826040c114001c0d40640304a200d0138102c180c00070810750368006003031008000c0305420b102010302242c04106000e01402e54066010054071a480041c20714401d404042c1034204c0d0300349c41708890540d511b000100d030705241e01002c0c1e88480d11030041610824400a07030503c50301c0b4800903c1c09580c02090051080c0903c41d012607120551015060000160080034040016000c5120f142100d46116181003041034003540b601511400003800e0900a06103210094200e8490721850b007e28091541e40c00080d040c401c042400d03c40c00070014221010283d8181401031045604071640840764680c000000340c02c1e480344c00840d078149500d03406003d81070300c8030007080000a00034000c56029074039107034105101000301c000349001d5481480700544c0ca603 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 587370215 1250 587368965 587368973
    0xf02120d021617060a0e03120406061e081c090806090d0915120207020d0f0b06150f070b04110604090b0907020a0503040306110706050a020a0e030304080d050d060b1204 74
    0x440725048480c0025580c000f0350044440010840c5e0403002c69030340480c00319801a40703d40341d03002d01003491030701c0003864043c003082c08140c0d4085001c1d00d1b4044441c88070200340c0c039040d07498a5054841c800140d8403180e1540b8001c07801c00e9803844644154501050302c41e0b5a4a003151403d50142d9007000c1507000107800004460b08072408000402100c8108402c0684465001c0d0568056085589285800080301c404558800300c0d41550035070320141c4071940300b007241040007203200102e0306103015803024042c1c1c0403005180410f8a94160418081902c2e0280e2942d407100c3e502e2000d041202c2d9200c9030340c90060b1070ba503004041c0015203200080000e004005404008100c400604020159089050344401240c00441224156500548007003402010868129031a208410b0b0207070500e0718110a003d00d14540360001c0541c402280e545115003200c260030580c480c8181d2103131010680c48900550380c56405200500002600e9a40010b1440d555241c80d0120740d1004400c0034200300c151041100700 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 587371465 1250 587370215 587370253
    0x40e150d1502131a0406201903020d2c030705221a0306042301020a050d0f0b0915010c0b07111203040b01050d1509151d0a0f02120d02 59
    0x20083c0d8819030130004941e90b990074107442640500e00c00c21003032494140d46840c2c2c0c000842d000240c044210340b035640000403407030482c200f07540c01100140903980310494464444c3c03070080c505c1d410011250903400c1d4001801051503800c88403803038050061000000d19980c074080d80f02c0c8500c15040402c03030800e240e140d03810100c2c0c0e1494000d03c450380c135010340d100a03030b00d0000d1096403083e40450100b680d801c15070900301070901210721800003980001a5016031583c480050009641050740600105091620390419103c5196801e60400308000000b000c040b612446816030390300c1070401d02886541c3c0d0b01c405d00181400c84e05080480e400c0c800c00518050108501e0356540d4001540c9411420140e88103d000c0c0d4040c440c0c4d03407194003018280d1b030500116210001d016080400d0800002002c0d103480d000c83c959880d8001645481c240000328902c507422401644081d04a000c1e1405451a96449034079403a0744100342e80280c51060200c00b281010071041c194210389070024958014446a14040 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 587372715 1250 587371465 587371469
    0x80d1b0b0c04090f05190b030a0b04080a0e01111b0a03080705070e07081006030b120123070903020303041e150314100602150402310b0105040e150d150213 68
    0x4d180b07400200b042403e921804180d070382080c030784081407030341c50710002038070307088800034054120780e90344081c4002c0000782c50007441156406e40f1040cac1401c5010006448a01c207a40040c80350b900403502c001000c0341e00340d1400e00e4040c0001c003070705116030b103c5e140d40461303420800302180c5a40c40414188480e00c1c046602c82d80c00390300b44c40d0601d2989040b403076461145050f849028185a120b0504401c0c50340c90140410845181d10000c00ca952825401d170000300000c0741a4903800c1c0c9840d800324075218414600d07002680d801800944c90b2030316000e42c00f20040000e62404402c01d040d0b09010855154011004c00550407990740841d0b8520100790b5480712400251a407002070308030110800259030041020824004c070400f07076242d1a074890002c1000b0941201140043c0201c00e0205003807901d00113040d03c50512000c0041000710002c01c010340c1e00344900d0040c1c004075800640040e0009141c102510740c2d0a901900c55511041155203080e107605000b06a010416000b0070b2800c0220032000140300 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 587373965 1250 587372715 587372741
    0x210705120a0909020904091202060609090d200c0a0e011a0403020f0d05101d070807060806120102090303070303060306150509061201020405181b0301080d1b0b0c0409 73
    0x85800c40510010307000c070b0454481c0108082d00882c9194007076941d84e012200d0389400505100300c0080030031b00251514800c4171403612601051011074000380d40056100c04401d0181c45080407242180c281c14805081001c00301c0407031141510000003515003206620051061400d10849541004000024501c5605c80561410400d010800159592483c00c5003004015a50f410030482203042070750510395031800b049069403c00220034011410b03500340304107000620050b5418507841d41c4195441c0c903502e1003040d0004e20800302107850761400e505604c1ca03a41700c1380001458580d10034042411600080410b40110b6a00c0c0400c1040c0320240c00b42103141d582c40c4402d540c21900b400001441e0a901034002d9018022190019110a00c250f04440c040c2100604401942080b0b00060000720360407662440000116410051072941c9802564140c0f81e0010182c40040c0000100b00c0341310103814040301c6086070804081000c5980c80f54028022000f41c0f0417141d0310360030300900101703031910030025903 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 587375215 1250 587373965 587373967
    0xf070e1003020411070c0f2303150709150906031802030d05180604090207060e030304050d0f140d0c0e030f03030121120e0108130809040e21070512 65
    0x60924104100c001a65411900050780d48800d48121000e8001c0c01001402004001c90220300e0030035401808040380c40070280d024403044250700301c01d04a84000071a9816601005d40e401c02c0c091245c0302541d001c0c2c45e81c80d040540300e030341d8481544d0307a1308401c2801000c01d80080341400040d61502805205140c03004112140c0c0000f94003181e5500306c10010082080804203002c408603445800750104004000c2c80076846685860342500254044070003143c41500d455049801d403540401034034407594000001d000c1c41c40403484251004121110040108507045004050342c825038006810740c0d9546600005407080c1c030340300c041c2824074032214041c441d51250f540360165282c00001c490541d5000c40440200c0b20224600e001241900710006041380755820312500c1103540400b840c00c0c500d0099940d100306458108c1800c81d4001c0007040074011000402c1002030905141e042412070040c2c0b07404035a86401260203200301805240302e20800c00c2000208101800340401000c551522005005 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 587376465 1250 587375215 587375221
    0x50406020615130f0b04050601081006050c030909090114060411090120070303270b04061b060e0705030709051006120902040f05011e0303080c07021c050f070e 70
    0x6591800001c21202c1c140261030328018071903d51110500e001032101e003062100e4007650b60014050801261154000c5142c0700015041c3c0d803045428500132524402d080c0500c50618000702c1ea194405100010188410014841c80751104020103100383d042800004064074500c008410301c1c1006330245102c3c9042042c200301c1c1000990840340c0c110000d00b440c0303034000050704161418a8200522004601030840004185030700060b4005003000d00d0702c500107400705518400398a0140d1402560b220100601c070030302849000d1100d512002c003002c103110300b900c642c540e03410f820b64410514403000c41c0c01443c0c1c10401e0b0304042001401410316818180054504880001d2204078244a080104418600f413117442005c554071000140c1d130041e20500c00a1265035103840a05001c1c40f90008215203c2010b421442031a4050401e40350702d80e40341115502c0b902c0c0035204a03040044140d80c07240503038640000d0005024200c0d60a81c0c0305401a08206030546070590401e40240c6c400581c4201c10300c10 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 587377715 1250 587376465 587376467
    0x201080f0408030604090f06050106050c070603060605070312020c0618011404021c03050d020f1b030a0e190b0412060513210e04020a0903053d180602070203010c050406 74
    0x103403603010310185c0e0000380000650501c40f15042c2c146101410203494540080b44d2240e00400800b4200d440300c0803501c005698103000c070102c03aa184141000580d0500111002a03c10403c511080803800303170140c01c104079000c80b28104801a04c0780d940c500119482d01608400a01404c9240400710600c18454070306070300403a02c916410540c0c2c8010322003205500d4205400b800644a00107083c2c83c085486407190801c85031264480100c03841c44081011038142c51980000807944140015501c3c0417103600b0002c01d018480f00c1c0ea64049030740e00e800c1c0300041042c44ca01e1001d0001881082e80c0c0911607181400c0c190110b41c0003402c20400b445551400038003140c50502d049e12120804609580300028040040381ccc0780006000d0660f02c20b000146911406601541610039640280107071150001e40b114165403140c002c58258043d08c10031180c050030454640d0600c2d0b4580000310000c54440f164005004021504050480c0c85940c08200306003503003000d12459844404a0070414541420940 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 587378965 1250 587377715 587377717
    0x332070e10050a2105030d0c0e090405030d09080d0f020d0608010c020d0f030b0a150807030203090c1e03010618060b040302010e06130f0801060314010908160602250201080f0408 78
    0x14130320f40b144c407448190103200c40201041d4816078200d016641c0360b040c0c4418031005040031200140c0020425a01c1c00e6a51400040490140340d00c50001c40c6060011103907100a041c1c2c042054924400a001005810782030340a208040205010010b0f0ba8405400040382201c1881c0c11a0810303030700d000e6110356000d070001540004a080390600725000d154220084004c2c00c01a00a150828002c5000090030450240b031030310f1a450a40f0303040c45d5903844645c03c030101c1c0801c40740f1144550050302c2104590030024001c42c001c003130020308041800403400120707083d91030b84d500c0b01c08030600d40360f0034464440d4075110700000350504c414040c0c50301c0d20703640000b4115407512480601c28071000880d0180b011941e0342a600900b9031017010750082e07030348a84540c0200f000e072000b83d03105035030249200d80010040c030914522952140c80b5a00b402d211034003034070305840071000031034569901300401e04021454190401d40680c100d80c462820601900c0010308951015100840c018040c5040c080021402c01c = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 587380215 1250 587378965 587378969
    0x50c04062d0b041e090f0506010201050708100b130f06260105030c270702010c02010b03011812140c0109030914180901090b0906060f060a02070332070e10050a 70
    0xe064541108602c80c451100750707507294400360b13a0700c2c503280c0400351b000010382145101e040c09800820080d502c0d00b03010b4404d1402210340e1241700c8003031300040c407164080d240a00725841e10001c0d4179110b241c990720102c0418800e42c010f24007150f64140c0303041c500001720040e03000080460506007415403508010a6072a4080195a880341d81c2800301d540380003140ea104081c0380c0910940c40c04c40c42c14001b0002e8024541c42e0401001035003405c08004d220300701406040314101c0c001c4101040003a1581f10b00f21100c030301c40c0c41e00040000910003c00302c81e07070720006422600e080d08000107100c0c0c1b0924025007200c20580c001540002d5403035810313400fa80c94142c4c0520b5007076108404041a40c0360002c60b40117003003041005210035080024820a01e03000105c1d284121025109c4139072080c016801c0000f140611030040c4016408048144001280c02e00e5006044001c0207030a14415859219808000c0889440c07181c9540168010082c007400c0640c41600040e6009120001c181040040f031440382d094 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 587381465 1250 587380215 587380229
    0x30a05040204090503181302070c140d0507030507061d0d1b050d0609020907050c0316061b05070302060f1b03090709021603030e0318010c050c04062d0b04 68
    0x90800a4195240d81e000000c0c026407141c196580c865210400956003040350001600401040c550030103104024400c540000b604030004100041c90529100803101500d0300c540d0704880c080040380d0005800f0445040590322590151840d6070804e00000c020707013032034280302c002c84c00203c184071020b403103070b04602401c150492003424040304034198070800611564020354005920b20000720504c50268030036540741e4400c440c403010584802130212214050a850030310140c0082110342e124017407003441540c429124040200302c1800c00d03e0844407403981003c4000c080303000060340104259040c4a416481002c184295203142000000584250b241705078078501c00034004085507800c00d007040b1110081c003040c0815135851403130b41c066203803144180a00320080b80c20207600320118a80801900d071505a600c2e07103114441340000046a03c01460081981c140c052401d9402c11500c60b4040c030000ba181803103030020700b41d900701180c06028101011f0300c19056413829040c4103003020f44013128211090 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 587382715 1250 587381465 587381471
    0x1060c0803042f03100504050d230f0309061305060c0711040507031b030b180a0905010e070f0b04080d27080a0215070210030e030909270d0203030a 65
    0x32031410000e03400b52560300284500301c0000e1000c540c15548450f501880301030b030603122080300150f104810b440c8140c40050240c1c1003580041d1540784101d1141c048860300d012611043e0748213a451a007254030a20700e149008200008003e0003030020048260001148882250310b101d540e110141c1b0307020058602410401d002408074107110212040c0800c10078010410080d9080c0303003501a0040515603074112a0981640c5000744460103440381088664000d001540d5001d05c4590704d80f030508008048105850382c401d54000414803d210300380d6000c2c3c64100034482907080c44454280201e040d0300402c80040c04000c28032621101141c1e949080301c40381488a801441c1c02100000700c82010900e026100050400058100700000d00100e118020344402600959480b0a250203110b28000039410410740601c0100081c842d9000c610120480d1041d40d080608404c0051006401543c209042005050f441c03502c20030040000710070325807090000d01c5a90740000b0302039102d0200509404155075 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 587383965 1250 587382715 587382721
    0xb040305030603010e06010b0c0105100b040612060914040c080304060c20030a0f1716030819020c0f0705010302070507030605060102031603021501063605060703081e01060c0803 78
    0x42c05d421401c0034801c41c03004d40e1520f40e11203d03003520a42107018101165030800c00450518071480c1d02c498144e0303d0011881c1d140030b06002090303405e050040f088200c120342e11103002414105500c1000c143d036100c80004100b5050501f404011102c43c5c0e0060800c5070810042007000ca0b8002c24001101544900034944800c3c61417100203074040c0c1011500d03014001c2582860421034001c00321110684a1034000c0c0c407c0912038071081c03082c01403003103489055107844a1784000c00d002d1560182d00c640c1e0702200e01c1b41034803240984001da0700494404c1c01550b02c162840f0700b00c0d003014481c4074050a03080c80c0460418400b41c880541d514494403011b0300c802c2c0e0f180089020f0346d10034011582d81e1010303015855124841494000c2d074802041407245c140c401040c0010a41c0c074400c0d2540040303100003508145451680c40300301150000e54821012030801d506c2000101611403030003500e0228003d8071240c40b6494100c4144490a040c0d0b101341045c55500070041c0300c16074114040320881c0f504141001c0e120341e = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 587385215 1250 587383965 587383969
    0x30c07030c05240a050114010e04090c15030204030b011a09060708190e0910083406180b030c030c090f04050a0e070602010e0c12030d02031501080903070b0403050306 73
    0x100a00fa180703008001c01c40c40380c40610403105841806105502010410f50307903110b1081c3d202d01800880c1030300107246080b0a0005190603040101600d004c2c01988400e00d40d039400074140803a100e8030030408280c004c50104207010300cac00c1c0d40c240140080c0045100f40591070301c01d03c020f0722446062512508000c504141489554010340d441c0954402c14405500700d44403025044582014555124102090005484107070344d1420800302c688405c01400ca00021400c519103203544081c00e00e444600442aa00f004100510002c1c01405140c0325582c941c041521028021545608548400c520810600070040cad41041202c0d40204130348582501c0740d14140006100b01011031005501508020521019951640c0f10141008090342203a100300d40c0c5140c00da0980e0041c2c0709a81e0b541d00141d41540681c2452000702146c5090101568a060078900d402400ca8106440c141189a1000715080351940c011803a00c3c0c104105100035400d0610301d946040706034000030700c000c3c10030a0100110b0a40d03 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 587386465 1250 587385215 587385223
    0xb0714070803031302130911040203070e180109060602070605161e06050a0507030b03060f0601090302180a11090f150d0c0c020315010e1f0e0a09020114030c07030c05 73
    0x7400d07620007620f55a04120144944c00a0a00c4050380f1840c140d1041290301c038030742c0c4501e101c01940b0006000b110040c2c402048002d4000603c00303410700c41c42903043c45090b580c01100313501000c8c944407002000d50405942804031501900198103640c004034040c4038140c0c12006940c1c00301050f10111050558524045030ba64039000100600500201804003c01140380c1100b4412405c1580820459440c01011020345840c60351041c0c241c0c00c008045001c2c584590038072580040181000c0d0911035403940480e920100c0031640c1c0c51902901000c1c4500078165000e050701d01ca000c51009800c0528400c0020303034070585503210074860a00084004507800c0d034401901c44031400480300f00701c1e2a28a51014140003074240049100b0f0140404420f0b0794184c41c7e0b2014140c401326214040305658420511420000940c00f181c02180f038150001260319082c1d50681c030070b0102c0c90012401ca0611700c0054002c000180641c54420b8081c010046400d480105891426801d86000d004610084c14402e0030 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 587387715 1250 587386465 587386469
    0x70b03040318030503220f05040203090c03060c0d11040501050f3709051806060705030d060312080a061a0d021306030b010908010e06040b0601053a060b071407 70
    0x1000200402c0081801004400f40083c124030740b9041d0403600060120f83e0203002c040c000c022110310065000c1c0520304050303018560009868040303450b00da649200007450f10804031000301581000040b003132289101c070b000e8000304038a550b860a0426082c04000780280c0520011021290300c04212184228001034014038503102c190a0104207a841d1000c1458081507105c00402044d65104001601d003001500d03181d0550b0f103042d100a080d00d0340c3c41000603603800396006403424030050007810035420310343c46002c00851140c0241200340c1c981103c042e111820003845900114949181001a200c3c81c00c05c0340400d1040c601601e5651031800c5030038000740102c20341d00503d45070b00140898600c0d0140e0144107072600c240c03240e20115649111042c00c0c2e450f440e0720361a41d900000003080004e15802c458039003150050412508014040c0c403e09400103484a89100d0b0103a004944400d00300c40d0900304580c03895200c01030040c1d40c1400d0310044184100c6400900d000640c12941400c40814050200 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 587388965 1250 587387715 587387747
    0xb0412080724050a0b0108010308090103110f21010e1303030e120c01020307200a03080604090b040f1506061d0105070b090c0328110a09060e040506090708070b030403 73
    0x300800c030212070b0300003c0c101100c070194103d1910760501e6507980103010040c100c99101585d585020088401140130b421003082110013002c00b4099001c0c003254050150503105c0204140040585c60a14800c01035041a4094810a801c178030a01041c0041c042d86202140e403d8280440c1a401c0182003d140030040000e045003003c001c43c26448000040d0011800780986031b490340e030000c010f603499001d55034030a20b8107056980030400304c1002a000b1242180e0040c40108000360f0030a09882c2c1540b8041c04450490344440c05e4030003e0204110428131540c44c0740d071018200200da0500c80050014810fa14441e80c2c10803040d4209003007030f0720560441e0000d40d0322a05400301e03810920503880e50354800300211442400381001610f1901c48120140c80c01160340303540300c000640d0b203032100c0d000c40199503007440e00f1420b808000703c0e04d00d040313000b00b100901420b1003c0c4090f01e803904100d4200700703010307002a6194001c50000c0000100005601d8144c0e180080440d98903111440d040d0b58130301400903020 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 587390215 1250 587388965 587389013
    0x181b020a06114f031b12060507021009080903010f060f0608040f050109050d080c12061215090309090f01060203030f0a0b0a03080403021f020616020c030a0c030c0b04120807 76
    0x8074644000c141c00f8400c5905c0b50802654034844085d80302a150042e020b0020340000c02d020150105129402c0a43c0150060055501d2030300b00b41003410540b0b08000c13040c0c521031800a07601d05203007024840e155010b180b01a04002c8035040c21038000410007a4419002007110b081c010400780549007012440c400c1d4050000c0004883c0741c906a030703e07455003508a9000c542e0b108002824801340d0350440d01d10341140c010318081503480c0b0040000c03c059104e0544468440e0941181641480181c0207006034141c000031a1511204010051550801006a203944440303a00400c00a07800009498100c000010b40d8081a550050044014181182c11690000070341c0400414048010020029280240c3d01d61400301803000c0b040c2cec2d100c00d071801880016844240040e41681d00c06200b02e02c0e40e0320301d2040d01d440404800c0001d00e002c80307030f4001b44d4406191400400802c21006900d400400503160428201441d040900800002c02075004d40076241c001400e50400191510414010144044c61 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 587391465 1250 587390215 587390347
    0x31a090903090d061116151802010c1b030302070911040e060f13020406030204051216060f0210020d0c03060806040507060c02060415021b0409080301181b020a0611 72
    0x1400c0b0032482650a48060300b161001d070141f403005024540b20300c3d10103042011400801e40c01150360b96840f076000d07641c0c1c412a81000f69086201180b00c40154040e60081c031809081c00412011940710803c1c1c2c1100303c0c0c3c1008100b21012403105081c0d405101150358480f00081a00494440e65811881501c0184005004a9800d40560180055900544982094240040085070f076a080c480100e517124200d800d040042601c1051003c03100e0075a44162404210b0024000d016a00314070502400d580d00c842811100980c03512a04000b821071500410300c9062607214140ca0325142d025800c2000300324020710055480b030204440051440f0084c100d0510b980000003502e0b41801e281018a007604042005200d19050080b80e02d0b188e0030209240c91079182c901c0030340d00760710418011140c8a8503072041244420f0034042900c200d5001e034000d4000c585492038601c0890f031a030501c07440c0b02581405080c07202c04481e81e91b90942114480710366119107103001c1034004400c19114a480101d001100 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 587392715 1250 587391465 587391487
    0x305031210060c0b0a0506030c04090f02090c041a0a05070b0106080a0b031209040e15091507090e0106030e0a0215040e06101407030e10031a090903090d0611 69
    0x114850395a01c452441e10507100c810845088040050281c140e1114001040150800e079201c990841801011114080c07108000701b401d0302d41484058404202805080d420740c00e1000000e58810701c00400c00b8649414000c3d142c84000e0100b18240203c0c00c041000d52425000f0400c446002d5003061a0403659a52854028031803202224a11680c1c1d007488545031823814000b030000c007080c000c950701d80d00344516001404000c1c081c1d402d03102042e100704100c40e551501d0703c24001d401000814050205042c116026540b9424007070f00c1c601c2000500c007410030800128285c8a03055500500e008030301c00502c00502072070070304000340103503014404001449a0140c81e60089c01100c9209c02451803d54170389082003603c0d5480ca07920408281c000201c035503124105001420498440e080640e08441501c010625480d003100610011136960180c030107044994110200e02c0d148100d42e0b1000034504030091940324044c0c000c50030f004560702c004010402a254005031101a12040040d403204d0700001 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 587393965 1250 587392715 587392747
    0x6012d0e01050f0d0302030a0302210106050306090f04030804020f0103020d050a1a060f0909060307080609011e0504020109060f0e12100b0306040f080703050c1603060e071a0a030204030503 83
    0x442e01d885501c460303400300030600f0007050f01c080c000d8250300518180040754a06401035230040b00488071503d01545905030407641080c0701d034040c0281e541c0303041d100e00d4050103000c0c4450b005040300c032054008008110000c0c0e0710003160b641c0107605507a003604040c3da4a0041c5c020b8000c5200b07000f4113a04050402c801201c1d2070707200030060404042030041414020b801d00142d84a1400030300c900030b100b00444021070800d48681504404041c00b1a5545540d9a5400c2e007840002c1e80c502180d40d444040b031042104800c8044268601c48407002c010504113070340064840a011303c66102801804001e45115501451101c10840e131f001d0110501d42858643c8651108001d07562400f020340b0700a1190394508002600c5403290f070f0310200420141030551074000081d04103060817001c000e401c2101805401003400010791a01071503011001032400c41c034010040d26814412011154031000c000c10004840e144007201101c0c00040c03155580c0c1070580220041d118075007020b00325120000d81c07001c0f9140307850 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 587395215 1250 587393965 587393969
    0x90201021615201e071a040504020729010f050f010c060c11070303090503010501081f11090a06120e0309010c03201e1207081801090509010902040305010f02070506012d0e01 76
    0x36017a0f52103942c44a20414480005400a07684a203003400240154101a40145280c0307000d01101d4611040c07418800703800c000202c0b4003140071541640100020004104c440f030140c2401c440c041c24528102c40003c0840da0703605405000561944940038506000f4500c030b2034400d030f08900f5100310030b0f01c4c0d00340642010110710400b4040e40c03030700c000060042004100008c180c050800703c04080340c5507880300d8000d444100b40d080d114080c204100680c0340d88031980ca200034441c0d44c4a03590285c10503031421048804807507110b0b0240e00304010080e01682c0c00a81c43d965103500d0b04110b02500c0e103a800600d104480d0040782507492141b007400f1007401c03410a13989e4280142030011034030400b204100a21141c061204028503e140034003c500349442512001c03204800306261420915a550002500c0d020081c0e0140800560018003407081c000b01303000d0910500006d55065113002c40a54906986190520440c45800c00c176040303160b4501c0042d00902d001c04503109500040d00e485d00b92480b8406028 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 587396465 1250 587395215 587395273
    0xf0509130c0b1303030210051006051e16020f01020708100e010204030506010e06091501050306040f0b03060a0c09080a08090d0f1a07030c1e0815060d09020102161520 73
    0x1003440e0245c0700030700d03000302449074000380d49c04580300c1d14055060301d02ea04104d00e000c201c949560b01e02d5058500c04005403c1d04040c0b000c4907600c500d910300601000514070101507046400030881806141800560150740c00b041020001d10030641100c000d009001d1508010154000d0200002c0c0b0702d055810210301611013182d80c1000398640d10100c080c90080030078540d012480500c0024228074003030384082602540c500d40410141c44180000b03061001c02c0394200c0d451956440c85205140d4809140d80150000c0c4004190303a0410740c40d82c500b640620300120744200c0b41b82d5801c02c2041004080e00010b141e1000c0c0355070702d150a0b2454004540811a40400000d181008049030144a00d4004607404540340000008107070040040341e03801001840d8238000445440004c490b0303200c05c40200402c0225020003d14100c083c80028203001042d800e00524404c080c03420b0101d4031a1030060035086d0701c241080607172441d0450903581803840d842c5c5050b10601440219040c0c00603c001e02a08075011 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 587397715 1250 587396465 587396473
    0x20918070f05090a03020904050d120c09030204180804030602070b0a0b011d0102011d10051609062f01020d24050123190305010f0509130c0b13030302 66
    0x109880812010008544103000180e1491520030340303074003401c020850502d015025050300b5482e41c0229803128001e8400b156194000d48010700355951144a0104c40c00010100380160902020002d016045034040079100703607915240c042c010301c40c174034107242d205a006100c41e4482d81c4c0c07030516000039003001400f500c00003050340c009a04404580700b19079450105840e1310b010142c030540344107021040c2940b01e905540da14003051070f0032030070202e00800c0c0039442002450000811011241610405490001101d0001044072a19900710314107809807000b80c50800c1382c001b07400b007101005001c000084440d00d102460305001001043d0007c12200c5807204052025881c1014128150401c4008412030800c00c0c1d80107006542c070402c65011201d075003004500c0000000d2142198540c8145801d59807108075041307202080790580201801004002c0d60010a40c2c5050086443c0e00f000400380c009207407151000104200100707504102800101102c0f42d240c01b4140c0310170040a94900040c0c004d489 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 587398965 1250 587397715 587397739
    0xc15030a06030c06230a08010618180903020f28030e0d0f03081501050d0e0708060f0f09030309070324110a2706140f070501050105010e011d060f040906090209 70
    0x5e598040b210040c3c0c082e9038203010b40e884d05208480703181d003d0201250300d5110b96000117840003203c84d034080300c4605d001c0c0000c0104d15443e02910301036903059240c185403c10100700030300079040c083c0d00074105c180032107030a01c2660b640390450380c60300104200c5903ca0030030620802801416842d008505110b619403e415440c0c242c02c404404030b00704040b40c00500f00300300309041072096030841008528800100c562454032481024180401101d111b15151400020804100110405a070300300820001852450903d040c15640755045804040d02205820498840c1118000e080140d0540351b880c0400c007824001d0100d601540c450320003a00003464182d80c644150301050141c5041d100e5003d0039403441460480140ea045e600003000307101c800814850010146040c000400b102c3d4407130800003540750304200c00581500158880390b81003290f20000c4440742c18402c28000641c030012100d05813502d250b000402120311954000104140c00c0481c0081d0b00b15058010b4001130908580c140d481d64 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 587400215 1250 587398965 587399027
    0x507060c05030907050f010e0603310503390709050c0f120406022106130506060921010c18171c1b03020307050d020c15030a06030c06 59
    0x10000f80c0e000305440d0840360040000b41307885001080c0c0c4000604100c000140d0341c10018400ba0000c99001c55031031043d480e9200b401044081020450207160380130740003081c0710b0300c4130395480c040c1248003055150511012480090a006542100808010399241c101201014161642203d1191340442400c00001c41c0800580c275050b0342040381030710380309810022030f0240b800381c001d0041d01c1a5001d0f0b074200301641108003181d9031400e0f2218200c0c81140c8904000341800307202c0c0b6032018051706a92511060010030f42c0c0d40000c5552420f8101e8040340f00111412030318103040360f0010b80003c15868150303180599600b0120311500041060607030310f0420b0340ca0032002140102e6492150490300540448680790725076692002c090a2180382034a010700029042100c03461000205801691001c6005010402c08000828113800140b002d464000210004180e2619088452081101d40070001951032000c80c1d000c0001941c0210300c01400f9943d868015110045608545440c4444804402001 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 587401465 1250 587400215 587400217
    0x612110901080a030302030c0c07080a0510140103060506210c04060f0501020a230a060b030d11030a03110d0606170f160305070e1509041d0712150c0507060c05 70
    0x3641035002500314090f080d07404030025480102101080342e000c0c0304001800000f0400c52010700b044c0307c0200910034150034550326050105072100e025608102c52460155a101400390450760311440c007080903242e45000801030400a0113864621501c20704503071400d0300014045154080583c1c0403c00551642c032401c5004000b0301038140075031700c411840400155580145d01c0072001059030a0402003002c0d090b6030074801d0600c803d4070f4680c0c8485884449140a020290029460f42810940044987c2c0000c0e01e0303005d0114804203240e514005000014080c5007154001d85804400300a055110350002d0905503800ca107641ca02050400000c183c1c03d01101124007a80880c1540c04020203103807002c40141038014209020008181c146100380e80710b02800c0c850f01044034038071a07124860b000070f02023220b0030301c1c200050701c00107100e1045540304080740841c15590340e1310100c41640c2003070030040003005000d8038810300705140c10003800b841c59204000d4a94244100b00070301100019540440711 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 587402715 1250 587401465 587401469
    0x801210b0c09030f030c030d1a030a171216111f05130602030708090d020a0206040317040503030c0703020306060d0b060f040f0e03030a061508010303031e0612110901 73
    0x1100c0244000c10a4220350001508500030010b04403214a012250700a04680001810482980c00800c049001c0107450284e01b60507a440e0441d15808a5100000f0b540e9840c0000064030b0210948160041c2d04500350407111040085c240b284401e0600c98150980c100710000018001071031101000482c80011800300e1413802140018a12401c62a280400905000d031a1820424565541c4400105035002845c4208003a032141440d40c9804510141001e031911201c104642000140c00010b81e111029502525007050740482601041d00240195100700e80000342e2500c030105814204c07400c001130a0007070b00d01c02e505550068640d0002c1c04800c0840791320040ca0075107803c00081c90342c04c110901c1c0723041070070042021940c08080c1c0d43d80c01c200d4903500c41c03102c0a50000400c2000401f00c07401008005c3c07642c0c44c402c0c40e4030316510500400d254810b0000808140e2075000158401c074100c1d10f180e641001180e003c20800e036030b4005204403001007600480c0c104004031411001c0340fa100d00c001d41 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 587403965 1250 587402715 587402723
    0x3010626071a0306040609090602070c0806071205100308040b1c0b061c11130815010303050307050307030f020f04030b090105060915010c0c060f1e120c021c080121 72
    0x1042d40c1d1034418204094000903c095000b55852900044240d01c50107140707070b6580200c0d0011707a40c3c600780c00d00c01c01d0240d040d040502c1e83e078002c0b428046950f034484075414000740c0314940010151200400b080c8102081d60000d8180303a00450013042c1440100c0c0100004040355081000d49a54059504144c810000f04640d10010a0000300c4000c03080b200ca43c0d0065914200002c2c44100c03007111201c00380c1200302849868000c0030814407801408101018540c02100071440c4250f1450707070b00030200e01c8001d02c560108034003c0080f501040c001d406c5030a41c600611401d41d20f4640082c400303071250b0421300c000d40707102c03103264041626200b041c0301e014011007001e4203483c420341d40c2000102d03110154188030750400600b40170660209040064440142046945138400c00001c8034004004904581c0004c800003141c507610041035400c0300c19040c24441c194000310350f00744251026420071102005034490b1812546941b00503580c001c20741816600084403044000700c900f5400825000b851030010 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 587405215 1250 587403965 587403989
    0xa11011107030804031209050d0e0612070f02190303050714091003110405040f0603020405101d07050d1404350c0102070c080f0d030b0d031206050301062607 69
    0x70300407038850728a0310f600038003e061034880e1100465000c2e0469982c40300565094210310700000300c65900c042804100c10040390000d0401c114454070310344040015188805105500c02d002a90030300900080070400102e0703c8401814400c3d05014014090849000d80064011405a0075843e008019114500c402900520000d14a100281e00410005540003a212001c0c800003e45540f2400351641d10144500c003c508185188144025114040c2c07480030300300030500051221210701c0d2034001905215104120b801d486090003030b0b865114040c3c8580781e090038001c204e856000c0d40c40007903010f01e1084500442c2281d0491014a020440107607030078a00c0014a20441001c480c0340181c1050108800014a441039542e1034035030081199101d10f01a400102089000c04402c1c0005420b0003881d0030180040c8001d0b100042e6000d1072003a005061150298249000e5240355001d03030701900018008002880e140e1103449502c02c00141600910b00c804442500100404134602040b01d200880007 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 587406465 1250 587405215 587405227
    0xa0b0f0910111b012705030a050304020f090103052103010f090b0f0303120109050604090c0b07050f1b0a091a0d080904090320060105092e03080a110111 67
    0xd024052007038000d501e480c003c0c0100031460700c6089000c0d40000841000007036850881640c90320301c06807100c10005500b149008031010a2010003140c400503094546a07a0300e0b915880025111120003507010b40014650b0000300400c4000100c1e06070641044919103513a40e24103404010381c0c8424000c5088840f1148001c01480c841e0381c000c00c100202c0103004206460f10741011903e182c214110700144808640300400500c1a079119540d0001c0041c0c805010000003030319070720040c180d50f21403803d5a200002d100c5051000a10001582c100c0d0001070310224807116400d0060a06100525485441c00d10030001c2d0042240c8180c1a50015041c0003000040c1c01600700b09560403c40802e07949036030700f0800c04a40c0d5845109008501c1d00caa1100d640324024030100d0719a035940c840500030709030f000e42c005000a54940c14204c5c0e0180c42c588003207031110300c40c0ba0300c10414107038012940941410a10040300f041403042c0039028007c0c56a40d0203001c42c03200804142681d4218507001d103c80ca0170007030 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 587407715 1250 587406465 587406493
    0x80613120e0612040b180d080c16051506012c0d03090801020301060c17120c0d0b03120903010c0c1a0a14100501090f0f0b090f09090a0b0f09 62
    0x151400d56000300442d08001e4450740910f48600110f90864035030306250200103503051606a103100c1d64804c4002015203440c1c1c0d410140008102034013840c1c10900214815203841d2945850810300f81e842000c0d43d000440000c91000064010340e00305012481160031040441d03806030b2200c14240c000612201c1350040030041c000b0202d42610260204031600b00302141484003400258000c004a648829140240c0d060070b90340c1003180d60b442020300c2002c0009191402e40081400d8001001900c0a40c3e0784408007140d00c01025554007542c0c041c003401050314003101c08400030741a12901035000b071264944c40c6404507285403111400420080101d0300381d80200c80780c0039009500c040f099a0015041c00500200c28609800703c4007200d2000307803c81c0502c020359010721404010a811291070b1080c0d800c101600200c52094098002000da010801c4506540d1703280380c2d107114580c090001400ca040a01d5142d4035401580010f5401c40341c208040340c4c407100113942c018410341000018206840800e50 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 587408965 1250 587407715 587407727
    0x6010306020c010e0a1109060d120f030204081f05061f030225050c040c02120a0c0606050603070512070c080d0e0a080c0109031205151207031502030108061312 70
    0x400c9040c0c0f90350700c108803007448404001c043c103110b0288484c500342e0b0040e001085400400281980c0c09130310580b44500003c0d80000245c02481190b040c20f640b842c51900d001c030000c0c000da0380080001d1090014241e80e1080c0c2c031101e03124240004000b405155030b60810700c115004002d1050151007005010048004e00c60307030145c5000182e40217010040d5140c80c2e98080508200507064901e03030442c81054480d4581031103010004401070000d0102d44030030981c40e8141d03016051041c0c2c2407164124000040000541c804000b80200a11f40c58490821800040c01c0b0b411903100c04800c0c9540f0780101c5c01c00c0e0b00429006118035400300c1100c4c038100e03c3d00320480140c07103801050720151107412442c400040700000545081040d05000040e40503036414000d0046100c030188200162410081c44880340480368056110141580c9902c030008408110310301d890103a41c000382014400d04031451990720240c005504841d0070b10206c42c155100d0301c2400c4429aa0031030300a001c0412914510101c40c0101 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 587410071 1106 587408965 587408977
    0x507030504260408030d0209030d030608030a0c060b0306010b0a0905091e0c13150f030b130b0d0b0a090201080108060709090b220f0c0c050601030602 66
    0x3844000c40702e001e0140b0088016452151401c40e81c01c40c0007194000e00000040b259180e8000446400941005500c40d1090283c08001e01b48240f103070003500191a480000b461414520900a0303942c843c0c28038003103480719201d801c42003043d501405014002c0800d03070100c560320400381034004c20006041c0c2040c0d2241c64098140580b8011030b0406112400002c0b040203101d03224040510001d01904400300c12040c0c050a0100780d40c8031143c074156402256854002d110703161100164280ea0b19070012603000f1100f828813610b60301c005d82003241300050142404900460701d444504081c1000c0340c030042e1840d25040318208559010807198010948500a0002410014001008440d042c03062924954070b1301078a88880d40d030002c9942104841d0340780104440c922174000c90150421000c0816401c0c90010614901c030b01480d819068107078850007614241e030859481d840290404 = true := by decide +kernel

theorem cover : BRFrame.Cov 587230215 587410071 := by
  have h0 := BRFrame.cov_init 587230215
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587230215 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587230215 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587230215 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587230215 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587230215 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587230215 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587230215 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587230215 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587230215 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587230215 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587230215 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587230215 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587230215 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587230215 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587230215 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587230215 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587230215 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587230215 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587230215 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587230215 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587230215 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587230215 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587230215 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587230215 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587230215 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587230215 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587230215 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587230215 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587230215 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587230215 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587230215 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587230215 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587230215 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587230215 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587230215 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587230215 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587230215 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587230215 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587230215 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587230215 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587230215 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587230215 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587230215 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587230215 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587230215 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587230215 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587230215 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587230215 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587230215 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587230215 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587230215 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587230215 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587230215 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587230215 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587230215 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587230215 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587230215 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587230215 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587230215 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587230215 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587230215 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587230215 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587230215 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587230215 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587230215 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587230215 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587230215 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587230215 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587230215 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587230215 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587230215 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587230215 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587230215 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587230215 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587230215 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587230215 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587230215 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587230215 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587230215 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587230215 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587230215 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587230215 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587230215 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587230215 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587230215 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587230215 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587230215 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587230215 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587230215 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587230215 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587230215 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587230215 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587230215 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587230215 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587230215 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587230215 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587230215 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587230215 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587230215 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587230215 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587230215 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587230215 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587230215 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587230215 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587230215 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587230215 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587230215 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587230215 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587230215 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587230215 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587230215 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587230215 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587230215 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587230215 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587230215 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587230215 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587230215 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587230215 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587230215 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587230215 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587230215 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587230215 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587230215 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587230215 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587230215 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587230215 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587230215 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587230215 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587230215 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587230215 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587230215 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587230215 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587230215 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587230215 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587230215 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587230215 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587230215 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587230215 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587230215 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587230215 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587230215 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587230215 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587230215 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587230215 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 587230215 ≤ n) (h2 : n < 587410071) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
