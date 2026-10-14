-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2172
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T05:51:58.210205+00:00
-- url     : https://prove2.me/submissions/f2eebf97-8751-48c5-8395-6c4710677c7d

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 390467625 ≤ n < 390647482 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 390468875 1250 390467625 390467663
    0x10801240f1202070f0615030b06040c1103071a0a020a0e06070f02090f06010e040509030412021306030c090b030f06190f1b1b05120a05040314010b0a080307 69
    0x81104529500d400c2c01d900c0d400701030078402e0b6400603c04940380480941c2c0d032424042c00c0d20032a5100d244290300180c0301455038841b0498003c000e08010310890352451110400f80c01510780010202c40101507940390ba80c0c1741400001000384584510444016000095010f1030510071111070f9266512604020b8060401b4440395412400f4200c841910345010310f00540d039480a06032241100700807440c1c980c580305000520360f5082c030380c405004901703003018851011008400d80d8291041840e002d0361010450001075007903001a89121413551078180080140916115804181d51044106104890101d02455a03030035455007911840d400400110f4007405c42d04030350040c800d00c103c5010400b840400841c0f002c5a00d244440410116402245175120790014508840c4605042c003850201d041c41d03c41d592100412282c000c5941c42c0022a450100e00980c00d40e0040c6811501d041350342c5980c0c80e601070081c00d5800c2414410b5010b46400a20510000200c4d15120b41c4206000444000200 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 390470125 1250 390468875 390468887
    0x70f0203071203022a0c0303070b04151806060509150d030e12030d061503090c210c080a05060f0106090608100510050711030102210603100e0c01080124 67
    0x42c030101015001c21450000c101c403003603206103407982c13a440031111071707000c01c2000d1411070503245042c0250001e1010380702007060002403940c0140c021110844000c003c0c44c000c070082410f844680c00c1d40645400d5241400540c0d4403e40c00d40710b0a4440b400c0c5600c811800000d848280080b4641c03054102d10280000782c0300c0c0400c440d4920000d82115800183c44000600b1030f0819072104c84040e0b5140c90030070080c0009150703801800d80d40d0408012440c0700c3d440d84124003070309000e00d0b818141328000c40e608920b40b45044401d010703008202c100c0d095803a035021540303c5844090540301c0744140408a800c500d01c41c15690704070340030350b01d401e09021f00d404019224aa00288050b420301c1241c7c3c0002040c0e00d0b041ca01d00152070042d680c035962080246429003010006030181d178001da2041c030250010b1400c064041c1c0361118012081c0307030303180c0d1070303500013480c0c42d00315245c42480707d04002a00c0259000011103061030300d401d07201d160040e0788503510f280c10240e0305500c04640817014801041c03007900400c = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 390471375 1250 390470125 390470153
    0xc0103060e06040e0c0a120303050a0501050a0303231612080c030105011803170903070b070c120f021306090c26040503040b0301060c150e151008010609090b070f020307 74
    0x10341740500c00000000b100303240b042e030112811080c180c074503404250b4036104099200b0150314040004d0750521000c01c401428500000b0184182403018003000004074030400000d44843c14250f40c0c40c03002122441c0c076041c8500c0110cc8450700103040b80b01080c09019650b02c0388003a0305510341180e18000c011a0080b0000c00e9040c0b40760b00482020010030399407103145104694644145542c0c82c0d140040c18504540c9070311014120381e080c040c3c4400505120300b000704035400100001c104003100e0810510351500300310001c0d84480600c000052110442e000b460032214000d404105000078070310141c6084008541134452404114014100200c840b24503d401c10700590459007828dc40e4040e041c03441e4070030307042440494540341c054010450140c1041e100c2c141540d030244100380c40c161000d80e69541040d084c0c50303c000c01c0d0300091641c140d00c21880001b450f24600911a09a980c3c031400001c010b02c5d402550b216007400006180c03030303011301c4042e040300301c2c1d55008500d062196100c4140309882c0f5 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 390472625 1250 390471375 390471401
    0x10c060f06170f0c0a0303090303081504020a090f050409150905120310080610063207060203150301050c0706180b040503090102010c020c0102100e01090b010b0c0c0103060e0604 78
    0x81e41c00424001511909502c500e590800204815039010701120310340250a4400c601c1840f00c01400c1c40000d601c604c44008880d49420706d820079031034814443c2c0d05101c10035040e0350007900c00725044a03125440404074007214010b96030240c40d2600c5106000a455a2040180425074407541039403142000c0c1d404821a540140181d9500f41807031021720704103510907551420002a20082444101000c2c004650490500c040410851f880c010300502940316541e00c0413801605e468004440f07078540e00e58000400d00c10b0003069541c0705c0c0b91030690000d40059170200c041d403098581c0424682814400c0c1c83c018200202c0c0c10341850703015600c00026200141e80303c8590fa0f41e142c95180055108201c50b130045100b58083d6840e10030003c002130846140b40015821903020314115070f000e98020480710180b520b942c0c40800e4001d00402c0b15405003100f150010681c026141c00040d4030009140504048807001c41595a1403001e440110144c42d228012050052009000320b540c6150075408980761000c6 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 390473875 1250 390472625 390472631
    0x90402040b090112050f03070320100510080105090304050a031509080f030411030622030903141c090803090603061c031101180b0408030919030e0901060e010c060f 72
    0x281038003081003042c080c0d00c1200712032900e1114508000b802d02c5001e0112200100560602131140c500811b00e40003148039010896400759402d0b0075203800d002074800d42c90a64820b209a0408a8014500c51410320a060407540303814085010324402208039801c4442c0100040c41030750840c3c039400b805015901d44682c8040e42c40741041d0024814101a00400043c01059902d03440c01d410061440d2071300e000c2c420f1080e0440e60400c1540c1c00a010711038401c42144491941c0305106280640c2c0002c031a42000d003111140d0f0409071855040061211800000c3c519042c8c0c68110545060f80c14248074010540250000e1201c1c40c511700740000035543c02030004082c4494808000c00d0401c0381c0071090401e5000031503030f03490000b51110034026616040f070303c03414180f0498a580c40d03421074868040e00090000c800080481e900e51020813403116005405900301c1000c4400380f034080c01406108010902840b184000094420301030302d814840300784180c40301014a9025a01d120040c10300c1c103644404196 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 390475125 1250 390473875 390473891
    0x5090613021c140601090914180a081305150c06070c11180a050105030706020604020d0602070210020f0d030605130e010f060914061203070b09011d06042102070509040204 75
    0x10541c014490680c85010f490741d00c42c00d002c40014400c5c0c505030844040a418848500e03c26180342d1685030b032007505080103400039240b2002c0c1d18100004d041d0007502841c4041001482d40412024460844000302c4030f8540642521034043c21a029911000d4110303000000007620039070051412501f221300c24011805225400b5001511400c00240403d2080304058100126403000b446200d0142800324001c142440c940b083c025641d14000380000d00804103c102c0b80e0801015805a84d29541e005200300d2030710800800082da40c01c590050381b01c040c0301e4001c00c00c240303d000b0b2140d10709585001d00503900d001415035411025060b002c0c1075070401e40d654a50342c24000100d00c40c1d003000d401082d0000c207000c04103040e207200780c10010741a5445007401c0103005007000b06c0042141e4106070b02500207000741d5500141c181c0107000c000d1217082040007294100c640e419021680c4c0344640d214844510240b070007035100042c0c2c816029146005640f050390300b071285141c091441b03031744584010000f00380d5036 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 390476375 1250 390475125 390475177
    0x13120813170c0705010509032d0d050315101b151a040b04050702060708040c080d05090315040305032e0308090112020a0516030e030a08130509061302 66
    0x901e5105080c10450100c0c6888890200307000b24002842c0c01d281050405891030300280d02d6101128112503070700c80010410000020308280c40c011000120156003102440c40e00180c000d5200716100d601e1134004100780786003881c018448001e074001e29544e0955205925108444222454009950945581c1040000c200c072a02400c030014103500c201076141c00144080c0000d075070039840031a106034280000c120100d030340003a41c070b070703000402c2e28040d01c0c40d85480c2080e07103104105801410303103030051200300d0b0021a0408000c0c0011030050b812104003d5200190454482d0203450040003e5010004940c40420f880c4c1805203c080e130b0b00941c000e0080c10000040e149a50381c2c412100c14030003042940840d80c11600c2c01c00078040300007080d807500c191490000c240d845122214103100310300500c40410301d40b14041d1548a420b01030110f03030312030300241050541500003259100601c6665080810b460030b10040c064007901c40584000c291140380e0b00340070003035040001d03501c2c0c00001e0800d00f0310600d = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 390477625 1250 390476375 390476393
    0x3010f230112030f0e0904120e010c120c02011103041203080c0327072106110a020d0c030e06120609061516020d05030a05070c09180f080417060a0513120813 69
    0x245114050351023200c140c00201a101c4070900b144c4905101400b0304c0200800c0b01110108644101d91601070744152280c80140c03040c0141c0d9002e1070407407001180101c0c6145410501030041802a22010244d948820501e4080e203c00c41e8520525004001d54400001d034044c1103002207000c09c000d496544d900c510440c0031500e80d000210000740c1ca0729045c0c40034003500d840b0301c00d0b8001106400a1a05881c044080d548142091040d810055503491440a240c0b14410110b50001c009049036501d14041300081009503040c0c8529203c0c1c45041c0205465190480f10544082850302c105420701c0511900c0b1180da04030850103a8016000404104c0003a4040c4020540381c80d0701e407107158aa9000d0301b41041c1f05449900300d150917900d4451018039881034807003c920070503404031500340044030f00d207000002800f03268841c2071040310510b103c84000700c000c60f87d80d12500081b0400c015031340d1140106040030540720000b920601d99084a5000e1500c540d8149a00510007403000401090b2952280c0030 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 390478875 1250 390477625 390477631
    0x807260a0903140304051008040807060c0e010f020d0c020418050303090a1b050906040c1202031003140105010302010c0f03021507030209010305100b030c130503010f230112030f0e09 80
    0x20700403810a0042001c2d2038005080061900000d50030642448041200740300f4091080081c000c402d4001010004264201e44440c0d0b480902070003441c0f2884030107040000c3d20f80400c0c1c017041c80e0712000d02c8010310014181d2600000c40c0d5800c03c55030060740900c801008007042c3d03180503505d6035080d000420b504000460140b0416801007106c110941401d240d00c04810f60758407820401710808200d03903910881d0035900110121000281035124080656000b64403103140c1e54a07130b0001c0100040050001500c108407030203071060500107011050707864200c5209000c020302040000a42c0300100300c1a04148498620030f004031a803003410004182c642e00001c541400001c2d40006d4494403e507818083c0c1508219403518240742e550510304480400c0c00001c2010040c50000700344c3c44171020401d070b280c00c028040a402004448202099900606940442c211902c1141a59030b0070100b03120700c030281201c4803507002584170f50b244d9030210345515109003540100858100c1e41c0444d50341c1c203a41540 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 390480125 1250 390478875 390478877
    0x5040305030f09070303020d0311090409051e0c090c1608030a1506030b0f010503060301060302090a0203101e060f0c02040f0c08070c0b0103021903080301150810030807260a 76
    0x922881c103030101c2c0e0100c440052110001c0c1d0010001000020b800280124068083e4100460f011a04001c010b400c0d01541030031650241c20701d84040103201011412101c0b400c1c00c94661140410700c001480e40d2791075628995600301c40020f000404905484018080801507419443c3c2800482d0312040c81d160800d1717030350700071307241c0d986040c0c0100341260860180144641e08080c0000b030000000151031400f00328056040c8800000052400c2c4c0d03082d0f1241e0091580103101402d1810040c220100035003040b6060295100c80301c41c0800c03450b036108034000414999000000c109800c003002120040c0c040c500c4e40c1c2c10320a00b4180700005903160700a400b80443c80d8800000c0300d204c80e000050003070001038044000c0c008290314000208102c4040345040d00d4055071201c07851041800410f042c6d0400c0d910113803002c00c000c4004035000c60200c140100e000410f940d84441502c4641c07402043e5230440c07100a260303000c200034a800250719146404038140c86407042905205034581424000d81c000780d0180 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 390481375 1250 390480125 390480127
    0x105220603140903070605060339011701090c140d020d1104140409080c0102030709090606051201170a0512040602060c18091302060703030b011709070b1b0105040305 73
    0x8460107a0500c641400500d0307800e030702c11181c10005940d6844e0300c602c0d400504600c2c1c850b800503000751000c02c196001e1030521880c40407201500402800f8030071a078508080e694042c00155484c07903104125241d90303050740c0d580a01c0746034a0721048100600d40c0f844000280b0920001815080320400c01410319802c483e2405070f521950558458200c1340c8810580b1202e41d800d00003401080c103c0b401c001440c40c01a00c0000d0007944c00d0030108400d01604003515003c0d8000800c000311664001c0700d01c011159120001d2020035110306003980c4034051259290b00407405100100300c0700a0340181c4150100100e4280d0b548a80c541d22054203200164445190850000408200c030550401042c0d0703114213140c40f250704110a0001080c0791034850402e2520aa4121003c40c040d2141c411183c0765081c3c1c010030881c1d4589842c90094040c001a281c041d002c10390791030410807071403c908644c5101d450b4580c003810b600b03400c0100000c110340021520f140201500c1c600d1487c0d1030300074070940d80035502917145c40d = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 390482625 1250 390481375 390481379
    0x10603030e0907140405040c1b03050c15011a0d0914070f080604120804020102030f071109130c17030715140c07030c06050612100507110a0f0206030402010522 70
    0x840b003600009044041002000c03820a0040c1030240306480c03e40d44202c0d4085003400306040110744003101040d00490103004941088201504000101f80130031443c8199117042202c420003100c81c40d4248140e42803110345640c800d00c207440440050003c04509000021440455250380d00034038120203028040d0b911401e0300b4070006070a81c00d180000c103680e000a0406207406e0f40c502034045010641c250a215101d0040340441e0300038802d4941c00900310800039221b40290400c0d030681c0c0d2041191b24010405900400c1e0f8a40040500c0c0004540244d40240501c0c80c00a9000a07040606000d010a00082c04441d001444208407020a00c200b84800b01e800c0c1d080c00c0a28005000c0030b040c28034154810899040040e800403103520040341c01000000352a605d950100d040f2114601d441c180500903070405580c200c0042c2e220368001d56103940c403401c40707034002020180d031466142d002411a03407090444100616016000310f50062041c50b00b14100442182d0054285020304030004a0240000003 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 390483875 1250 390482625 390482629
    0xf170a0c03030516090306090812090706120b01080417040506130f050a030312020d061221091a0c0a060507020a150203041e05011409031c0b0901150c0203010603030e 73
    0xa000e0f0018900c0515401a1303242002c0a06110050301c0000c009648812100082c00b640d82d040e14015542001082124a0310050580c0c95036854040c001c0070071043c89104100c00950b10600003501d1040c0c5513410a88c985498501e1880c61030404c4008501c0100004151500c0300782c05030119041c142c0c8210030490400d8041c00c1075030000d4001c81e0244030700c00010030202c0c6d407200441034504080c000044e510010000208060002070304040744403009030640d4010001e0340c0d0084480700b444c010074648520501d44040324505014465040700b44266003607540d2014107000205080c503240380413a244580155136070030564000302c542002503041100104c09019111000807403c00303841800310b195280903030b5440e610b900c403c1525900058440f203180d04000b425409071048070b14140c500c0d002c6261000000d81d581c0d01400a4801d103003051660241040460302075600d41010003080401e441e0300740355000e1140480101d02c3e50400042d00416409a02d003171103840f005d580684d950351420940041 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 390485125 1250 390483875 390483881
    0x403050106050312070201080907081c0f1107060f1701080f070b070b0f180709020307030f0605030d0e0121020706050f240102030f0412050c15070f170a0c0303 70
    0x120250107034101844c4001d5210003203084a04256090a02c1c010b240c0351440140d20345225500030b0031403840303048264040e402d14880403070610007581e074902403250807808045810701c1d5280111f100e941c1c8040130501181d07019140800c0400c1c0180361054420803040189408180d00381d03c40007094000300700c0040d0116040c8400d801030060703040841c0c5091a40d0f46c42c60ba0304c03c1c0c01000b15100760084e00210302c0c1c1c92030882c0340c540407048000807500403a0716045450300944c811b40b100030100346890380540b4486d805000350002c89a004000d04262180d1280955410213184401030410001c0e1b218bd4096030003004030f490707892a15407801612074006140c80740840c3c102a02d4140032034680f03020000c2003010008100301040d06c46030fa00e00d608140d800141e1443c000e000802e103109001180100e044a000003191f940607001d05c1c00c4550460880041c0200b00d03101e03150440d0180c104102c00001b248083c40d0800c02c1921901007401e031344040364945110f03a004101c020000410a28110040c186c1c940 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 390486375 1250 390485125 390485129
    0x809030d091406130510030510080708030f09060f04030803010914040b13050c1206060a0608091c0203040b07050d140406050a030f0b041e110901050a0c05010f0f020403050106 77
    0x205103803080d103080c0001c0800800d18140301c2c0e481180005859410703180c09518140090401508130740d110140702c90003a018100c1203d01d136115980461000516880000700c201c1107681c9040030f903260804482008549902c00107046400c102d08002800e842010140100015030090b030356503031a94103021680c000c4c0c0d0740140500030410154014000890021801950400040c00f0801d0f80c48206182c42030a0803100041543c0c4040d803010082e140703440202d0201d100f2001142e03104c4e6102d440344d5044d2024041668214002c1d440320044402c00903003050814105002401220b00b0641d480c550b0101d10b5006010456290b00155000c10320580c00111001d601e46a44528500340780c10008010224001c04841c1e904260711074540100c214460340c050b802c409000ba200380b0100d900a10118400c04807000500c0c5014070307142d0040b8084c01e200040c2c0769001d00580d03540e85060219902240c1c0000081410f840325581c2c2c1140b02d11003440c600c00c00d164101440000b50710346103141001821036500d6 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 390487625 1250 390486375 390486377
    0x3150903050d05090c040e0a02031c021507020703020324070327110409050c011409030a0308063c0301060e06011b05060705090f1221090306040809030d 67
    0xa4500000e411100b510000a0b510034000303090b50310078910178544502d140d00d1541003860665070104d0782d280480c1e200d2984d03000f64101d480c98000801e201c0007104801c5079503401070b00644a071142031002d001106810081510445510b2a00c07500080e09042c00014103c0c41c2185001900c500170407405521640280e81d810704002d840540d071401c41141816228141003c030f060000300c000c001e90021005481d11015000b000703400f009250480c1e96484440425010031094088442510314a20071a071501201401600c003c4200ba50103890030007000d480076078406004178101c03038940c0115600b8000480828000c440c050400b00700ca50020f210b000e000b50082e41018828000800c0508481c0d4000c2c0d030a00c2c2c8003a18030709201004a42401d000780040a50280200f8841c1d03c4c0d80c020302400e05902d00b02e0301c8400c003001807030401c02c1c608200c2000401680104080e1480300d100034141ba0080c034000000c180c43c10800b00002400c208084800721082c01c0e011800c00801d040421182c00d0b0a03102d = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 390488875 1250 390487625 390487631
    0x6030b01061803120c050f06040308180c0d0609080703020724021e01020c0a03080105041805061605040f0b030906010801050105130c0302090603040f0209070206060d0303240e010315 80
    0x80940e50310b00e507000c64080649001c81d580c0c1e061203240d104094520341030f034020050300c011803004800c2e01d072a03290664060b00050441e5001c61150088101d043d00c207628594010988941c2010a20a448080410565107a555140f0000105039001c0040c00f01a11030b90240c00c5d45800c2034084a00390301c035280c0620040c1d4610030748542250300000c1716030f00c510140d800c8058803035000c40790b24068401c14480c1111070103070080181c105a005440e0505a0f0303400c0314144050741c000226500d0881d020300c8041d003103134046d50202d40b00082c503881021803405249030840c0f03000e4803840e440300c01025582c0003030f101110000800422f6082030210078050041d0000030b00c080e51400b000031741000740c06242201c44591300c10901106500a50498800600190601303032645004d042021503a000e90300300b64040c0070b24a00040049201007001d0b407140d071000b4241826011503440850040503205400c0111001600c83c049010f00c3e03080000f00200022001c0c45c00035811840c001038078880c051030074280582 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 390490125 1250 390488875 390488897
    0x6230c1c1107020409020604150f080a0c1403060a030215070203010b0a060905061b070f050f03070513020d090204020f0a091203020607030207061e0b04060503060606030a1e0f06030b0106 82
    0xa0340078111080c09404450205080d00c0314000500c29114a40c015000d082049410316640c80d00441150f0b11040c80c2d0f1522210340c0e44041ca00e400ba100a0400350b400101001c218940d88000301c2e02035034011034040c09801c01140c42e640452942044071400d02002c2c4000b14110f41180303030900546051000a40359290741910301500500044118058548102c0d004502507200d070340040c140034990607200c01103801e91a9506807800059880e402074a000e803007102840255030400050160407540040d1040c03000d0720604207128002c2d0458018041c1c480d403240c42c0200583d03258009460501c0981582170b40d14040000c000e444030030b03154001c1890720108203008012030b8000c21415845089800d02503a00c2d0851b01c2c2002c018024100d206c101c1a4081640741400c0d0034651002e050104d045e5002c1104075141c1301055607400023210315a902c5801007000580c0742400781c0140e204d21055802000015001c0082802960b103e08021032000d69568020001e03c01d9605c9118010301040c28051710800f = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 390491375 1250 390490125 390490151
    0x806090d1d22090f14060f070f0311040902130e16081003020306090d02060a0e07120813030809100905060a201203090c0306060d06230c1c 61
    0x1100703111414030481c00021403046103812201c80700b04220000c030080007100150b24041204201042c000e076a080100c503454450480002600d03130281481400341069550b076124110740001e6550780701000c040d12803401c4a014030052010b00003038a6400c5016844104003012403828854a40c06084c0c03d208201c20700c56810b40c0004024101045031500703000a907602801c4843d901003a500094061060401b001001c1c0808100f902c071744403082e0709a0b015070b1100001c54040da04003070024081500000800c01026030300d10f41c0301d10403c2c420780c01541040802e100915400006910075995030200203260a11460070350035804080080f0b0a1070f0710054284004588540503040c03102003880444242c0b02c400c440000104228020254226200e03804c450007000c1450308103036990842c6120360b0041042d540350103d1821f01c20580a00703980c00f203070a5500d840000c1c06100501c08420751603c0260094400c0050185228403c2d10a0696903115485041c0048418491a8044151a0046030580c40c = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 390492625 1250 390491375 390491417
    0x14060f07120509060d021809060f010c02030106030512040f0b040f0311130e0307020910050105161b1d070f080c0d0b18071e0c1202160806090d 63
    0x1040d0403455200761a00100c5040d10340748605604158000300200e6846a00e4405400500b1100e90300700e030600700294500f007400315184064900c82d5100394240444042948034500b0901118001400860845e60b2602c845041c40812030003505107880000e000d10144140491520003000c01c410028502494402c1003544c0900a0100030309031007011420360100e6132072559541488504d820104420400c42d400960740760701000049004d080d0400c0016545152101e080e01182c0301a104c175841c20301c0c07040120296640d028800c94100003210008290310650000e8000030300034129586105150400401d0756841000b015601000703002011707100d0030b0b980f003001c954003e000000915101d0400011a4000c0c04260291a0b00060b4800380d9800d05070005a240d405403800c0c1c0c1f1000a00400c80d8032656a000030803240344082070a94008000103200402441c0ca44246481592040c3e2309000343c20104485551004e440b91b4082c6080c0000103d0038000700b00100b00604089900443c0410b0724411 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 390493875 1250 390492625 390492637
    0x150c1a040303020d0f0609150807090507021006180f0e070510020109150f0e0307051203040c03080703081005060a090902070302190515010501210b0114040b0414060f 73
    0x19214184081400c16002c0d80607958500340e221001d104242a40d800740c4020700c05886105499801d000d003680100c412040e240f0280c03401c100c0680f030345c03504010644000d4200606108118850b1800841e200e886506c1a00080e250810044590b141e00c1c240e03200a8801d98200f4519461901c400e44400c02c400007100303006c40301d080d201140030904115003a4010041c00d0340160040840c02d0034801444542d9100010b125600d0f0400c01240c800041020b07038034014480c0007002c540c0400703003500301d0740d005201656200c0d11a0840b800701603280c0c0e940d008141c01c2003508a0108401206110342c041c3c034000010003820080c0c600310700341803620400030094102e52181e11119507000650006041c0f0034041960743d664420481203a2054602e450342d1782d440c2106010b99000e08540001c6603540c45007a402d40e0074141c240744602c1002400d1800c10040c245041d209046c00101d11240d074150305a84064001000c1c55110681c0390b40c60411603442400040b04040c2c072807802004001840b034402d00543e42 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 390495125 1250 390493875 390493913
    0x303050304150507201002040902070203070807180902030a0807030f03050a0c0917031e07060e03120109020c07050306161409030a03140f040e04030f030623030a1a01150c 75
    0x1a040d04070001072428420301c42c194006d124000500851180c20b107400900f040ba1083d000c84540da41da607030003d42c80d40b2a5008d030402402c606220300e948030043e0380040b6030040c0000e041d104086a560b82c2c5000a40c0f040c0011400f090020746804200c0c1c0d09031240701c1c2d200c440302c0700c140302100c4156002040c0a140d03000301c03600c0682141c2c411500c440c08100b038450404c910507142400d440c05484581881d04095011200b05040c84240000e4003000b2040d242d60000000000f0010b03401c08010002075049003204001900c1450000201d50b90100a000d0048009444000e00c810f030240c0c0007400c40d2007035090b8200c4054100070790b4003544c400203505a2820b4151800c01c1d0605034035804441070b807041d4001010966000b15021558070b03094407846015a21944960250b1456180294107075042446100108051140003041c605103c5030351041200d40202521800c02031992846004204000361034008420302c0010f110007000c1c103200c0c0b041c8004a0400c0480820b80e81d81c1e2200a13002116410 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 390496375 1250 390495125 390495167
    0x906030513170f0c010908071b05032a0301050a020309012a0315170304090f090c05060904020412060207060c080c071e0510151208040e060f0a0303050304150507 71
    0xc929070f40090542d00c004280d44c0c0240140c62190600403442d411008041e00c1d000110003015941c40e103225603540807242d02902620051014544500300441c100f0301606d4000b0945921085c10b0740d085c4039462082c40340640058803402c00190fa1801c4031003100840e0540300c24003140668100d028510301c00c181c031071440e000c00c20a1854160201400d403d42c032414081222500d840c981031004400b03003086ea5a12402001360700744100310101644d012560103450f10021043c1840542000b030004e2200c420098000b500d003070381c0c640f542310130350b07201101c1558800c1e8080303045010817840d4041e100030b04081d49801d0b81c803420554014001482501402801c02890504004000f04100343c1c00c0c107401d402109031550802403081210241c124000503080305290030320081a02003854180000c01904206514100360030700c07107080c0342528041c0c412036108004d040400403941c0e81100c182c01070b5200750740300c0d40c40341040d24101c003842601c074a20310304045c1030000308008a68449010042c0941306121070b = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 390497625 1250 390496375 390496387
    0x1b030c13020d060f06020a051c0c140c100207030c050922170f130605040b07140f010912030f060e0621030310060210060b040b0315030706090603051317 67
    0x24020b00c010341c4602c1c6000c06001002680940200d01880f8540c0940103450141049c0b490000201c0002409000406c44d18150076001c40c0802d82d0107501090014101c841114603d40040c2506040030414401640b04010910800c040720350b90718014581902c8800709410301641d182c854142070003001103140324504104003032084640407170042592174036806940303080c0c184040403164844c0c050320070145614000001c0c01d0b0701c18012030302161001d860003400c0020654601c80c0d00c4440c4100306800303120311f9541244c2c0c118284100c007902071040021010799440030b040030741520040c94842e20120300d0550304020554a444900742e11540480f5003200404290400d8180d0300c8070802d0841fa180b00c00300821403a010001142000c1d00c4003502140c0a4490700e0102200791503050040c801d4010041c0810002908010044c50300000320a180c00440c00380c00020a10b49240f40d070100000840740c000803c10680c00d480355a0b00b1041004500e0711304056512480d060715240280340400c00000141 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 390498875 1250 390497625 390497647
    0xf031b0a0b13050d0c030c2606040305090f041b20030405010f030f2c010b0402070c330509040b1f081e1006020f0a0b04080904020f0307021b030c1302 66
    0xa11025580c0111f02240580e02c807020369aa03002c881d50022881482d20384c1c0c4540010340020b0030b610039a855501c00f40742c0f074020304c2405900124a1000c640180d19480c2002c0c681c08110040400740000b5034642c03000c140096144a0007a8060000403603a4100300310610035030340d12851101c43c1e00000d0801003608041c107000c1600522089510000f0070b00314484842ea401c001c0d00310b240002c03c00b44000d005908030b000c00c00040748256038004061400d5500c0401220102c18001d802880e1513070091000200004402903041e50484003600000c0d40000711500070b403400c3d21600050090a5442e100b004002c40407030001c800d0381c007400b45e042c01640d0000850b14288200b0070180d43c00d226800740d980382404c0098040300710701406200050f014080800701b15000008880020b203403c0025060b0a44558030307200203035403010845030340080d000c02010003904900750096000f10415401084080c3d01400002d42010101c4031451098000b4191603c0640d00c06c10600c0071400501801aa10200b03455 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 390500125 1250 390498875 390498893
    0x30a0f1407050d110c06090d05010b031c031404050d0e04060f09091716060e241603020c0c0915040501080a03091d01090b0f031b0a0b13050d 62
    0x4a5100d031408005046020440081000c581c1011242c4a5403060004011403d0703d4912903045690801005e10001c0118900078040c2e0100e80d00a500000e003049400b0080790030120000420300312800d45004100c01640c1c584610084a0350708002e4042a080c659282030300c0d00b07503034001081000781c240c41a2001e5030301d90f0b1005009000c0801c5855031a640d0b00e14007005010042401d0b180303e0210001401c3d142e00c00e00488121202c648260b10f201040c2d44c0d00d4070000c0446450b44495031050170300b8089054041e01003544880c3d4000d130000d81c0c0b85040c0c90b445140903140894901054010701405400d0540003501c542c001a040308c12036031507901c503090b1140d14484c2c1680070342d10a0170140001546c400100d2600207903030103170780c0d00f0f20b086407076050f45c40603100503050390845040e9441c0108903090b215072104103420802403d5101ea2500c020011b0703d098451401e40c000301103020840c40d12450000007401c0100030039a503003418441e070002400c42000152040c2c5001b840f14441c210100403d00d8 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 390501375 1250 390500125 390500147
    0x6120504021f030905010501120302032d040b1b0c030c040b030c0613050a09140402040504022823090619030606080d0311070203060a15081b180702030a0f 68
    0x307407251440c0080c0e1000034060a00d440082d17903154a030000103e0b17113040c00400e045030a03415030011450300d000c50b0050600e160300b2000720315040f80305180c40d0302c4880011000b4001031007000e990545800441c86040100d11048680c0c801d140c4c4140101c4107039803004244102245802c9a0015410381c50201180c1014454207030b1a601110000c2d40203618800540da140039100d05903508244940c030303004000200c0e144842e40404900c0342100050062910380c1045a00c10310142010100301d414016102200781b020010071050366034850140070018800b04440000c81c40005081c42c40301d50303940894184400503101c1030084006580b43c50f901c4121504540c000d40e8040e20421489540c0e14800d0b4480240007603000010b410300c0c4100641e24440000c0d035500ea03400801403c00360b11402903401c01800044454290926940c0c030001d280007050040c178616906e07000f212191800e6400400031489404111510840c0080082c00941c503030000c25203400c94014140035501203442041034650300c2c515 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 390502625 1250 390501375 390501409
    0xb0a030b06181303030b100203040911040305030a03141f0e040204021902070806060a03030f0c032a02040f05100605030408090d0503090a0801020301060f14040305070608090f03040612050402 84
    0xb2005102994002c880c02c0e010003402541c04000c06a80c001c10025405d42e10001500164800c0c00280304014541d80422106100d459629243c40d40d82c0c2c0d0740034299089546030a01080e40c408001000320100c141c0305030311840401011100952900b60b4403129505c5015003001000703030f41c000804540301c9504a0318280c1c021340600c45c0440d074140c1b009680386241e000700e160714014400420100d00701080050b0a80358035440c0c060410180b00000c0b56140c00c00d803c03d4007004108042d030290002054604822441c043c0d44040030302c01e090043c442a114550790349440385181c4401c1112074031100d801c50069426070b28120b0707070365225030138048c0c01405403841c42640001368003800700801400100801d8580d030305984a0450719030300c02c61036080307010921a000101302190614404e5a00c10112110945c541c1c4d82004e043c25265140d072440c00000744c0003540401d17064ae0030b2250680c0d00308a04411454030307400451529040c00300c01003000d98140891180c042c0c951021400b15611246811200841c2c = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 390503875 1250 390502625 390502669
    0xa12110909090a031215060c03140a020f1605030a080a09030b01090207060b01020a0b0c07080c010c020f0f0a02060d05040809040504060203100f030c031b0801060b07030e040b0a030b06 81
    0x68221551076114050b411000b24440a0010811708200c0c0501c280c44c102d03842c24030244c18544502134419a00103a0b0807410080510444150385c0f420f240a060450401e500416020040000b030b1864018054004001c500c1384100410055500194910201ea840151192140301144c026503400e6425040141081901c0002103145103507a809820100e004030018421b5500c054016a00e4a00890002d400c048810001070070014001c4010101c1502c2014020719000d00c0b20300b403608648606454200580115800e14914207082110300420036131000a420702c40c1c1d05600284143c801c001803803103660b1b10340f40050144245c102c00d80e144010090005d008602c1d0628058001354400c4a65400f82e80c1608400300340314800200107000c1d2644045071040071742c1580c0340c0105c058945118007038107200403203020407089000e024a100810040e21131548607200382c0303000750203254410b00060140d0700d851515500340d683c84890500b1039802020081c11902c1d85e00c045280d00400a40c01074103404 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 390505125 1250 390503875 390503881
    0xe1309080306040b190b03150918060c0c0706081801020307200c0f0904140706120c1106060d08041505130b0c03030403080702150109150503030a12110909 68
    0x44400300552150004a904000444d8840100b0048050101c1591034003e868030081c4146c6100e1001180c001003a2024248407010150000f800080205e641d5600c8074001e40d510810590f080100320341108214580b1402c0002401085a6484041c4610300412042101103101403a03590b140c103696914001c025540d07450710220260115064002c9403200f038203d1107640001f20004160342803031180041103500d158580100f04010610b010b0f0051325a035807240745410705443c040000f03000800503600c801c202101d041c4200402c0300d510340d03800c105104a0100303020b60400c000c10110b030b004c54100d90843e662255400c10741041c2c01650010b104002042060300b590b81c0c2c200c40903007901c0320b400d82204e08281e2207500380740103409400d0602c9016441030000c58002800751869035489200f9204544140c0c40328880d822124000703a00c5200156a108c44c10740421465448581c09800e007600214582140000f000f0048080080c00c0d00070140c0e40c1d402c0304c4040980e2000c0310b00c80748000b464540a41 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 390506375 1250 390505125 390505133
    0xa030903230c100e1b0a051801230f060d09081c0f0c020c091506070b0906060d050c220f06050913080403110301180303020d0e0304080d0e1309 63
    0x35101c0c611000b02032180c03041c0008120914000c0300300e2201c1c08009010303076019405c0e00c114a40d50400c43c40e40e025450800106407521088a203001c081d802c0360b1f4141d195403400180342c030802c0c14000d2109040c1ea9900100401c1c0d02d4060300c100e1124000e40b1030326551032031010014010101e0580050000600042e00d90812160791407903000c1c8241a642003225a40381e44400c8126111b14180d84d016030410840c05200780303404003466a1151541c0307080006000503c00043c4190f1007403c0803079a108940007406007405007000035950000c810b5580c100031840a07100c040d075604030001d809200d5a8074009440c1c0015254000080724920442c05103c1d070403500c003140019220500807280a2160b101c0040c0204614400003260b09802c51045072519003180c039800d88a0032640300350344d01592220766008880744400c4282c65014066503005841d589010541e03410354010305030100a07a4002c2c48240080c100100d040e00886040d82000c901c04103c0c03c010540c0c000018051045040c078003001c0400340 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 390507625 1250 390506375 390506377
    0x6040b040e0c0a1e140a0f1503112a030421030206090303070c02040c030b0d0c0e060f01021905011d0313060305010305150a021e091002120a03090323 66
    0x100100c4242890544130a0000c0484c5850701c40b200da91154070348200010020f000d072281030310343c014010800300d80d1101000484500694044400740c54503041d0b0801840d07040c0f1030300c44180328013420540f810848081e030301e40d981d07210382c5019164160b2050442426008000b2900100381d600c00c002e102c400000c60072040707640d0500302034001d8003900340000c5844d003012040740e101d10300d90f440c0c110080d0328640a1000514540b0144420300d075881015404590b54a058003450740d2160700780e00b000305c0c1025903001024201130100b82c010a9504c0c440e0560741e801141102c01c18010a505002c50003140c1880c5014010380100d080e5100d485d035030481e0315444040018140d641c000d40c50b006901d59500e408030115074003484042c3c2190460324040c14101c001c1c14501d500120042000742c103001d29080030111500e0b1a103801c4a855100040104540c24120000300d01c0343c8060028003081744071140c000391a4841e01d000481016601c40035039041600070101c100300700d02240c0d1950a014a009048102 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 390508875 1250 390507625 390507643
    0x324050906060a232802010b0303030903040302060d060b07051501050102070f0b03181207152a1b0b0108160501121a0d030203041811030403050306040b040e 69
    0x24100040040d40c5400c00c80700b141d4080d1104d540f10061319074001e040c1800080490001c07040000c2c100301040180807121500d0854807100c540d041c0c0c0c040e4550a0180c00c540c00704d52214000c1c0c00038020010500c402100340d80803290107030b801d1540c0b4038000324024000c016a41107212840c401042c0f00c805d00000040c6602180e82d0b412040b10903988400069985030550f1140c810a01543e2000b844554400c001a581000909140d41c020076106208582003a01d20000d40c010a1800b158107070600c085945103031100e50002000300803040380444400644512010070307500518500081c00000c9105040f020b480f0300900317105a8010803d80ba10200c004c40130311034005603203d01501c60640d00c002081c2c0b8811100140c5860301141034004200018011041107565080c032080d8034240503454010410080314400d0f40915552070404a421051034803020201042c6440d000d20384004191950480307406c40c1d00750500355200d0751914001005480d49100745500300b0306099042c2aa01000503061341 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 390510125 1250 390508875 390508879
    0x30e1c020c09010e0603060a18120509010306060801080d0507020d1203091709010e090901060b041712070807080715090b010306050112020f0f0303190e0a0f0e04020907032405 77
    0x220380d81c0d41d030503216400000c1d178017144d258118001281080106034800a000c1507400310f800703605001070702c81800802080302340d007010440024125085690610400c4003070419410f064800e941000352140c1e59480031000c10301072040c001011400d541c0d0310351000c0c900c513910540141c8121900c040c010081c000721003040324080020f08441644400d040207944040f40306944407900819031700c0c100816664058055000c95507074242c082460442403008001034206810a44440120711118903d000c454141e03413155050288083c0c00090742d5001210000c0d508580c69549858060405001214040601814851600162804212030721b9030f4107040340d000396000c0107181c4c1c2c0e91401000c1d03510003040080d84410001c285070704900d07013060a025034140c007804503030900141045a99102500383ca1020128559030b00a02d4a81341104a54010b1b055151000d030400b07207040d5a481c15010054802441540d003000080c5106201ba0701c0426407820743e100c1001d445003100c002c0c034100c00940c05a80c0c = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 390511375 1250 390510125 390510139
    0x60305070f050a1d07081911030f1e1303050f0315030c090105012c0303030408040f05010504030807060e0c131a0f03060103170f0a090e0f0405030a030e1c020c 70
    0xd450700c280c8144034040c040c4d0b1085403400d56140002194a205d0080c01c04c1c240100070200000b20206a224a040340310101c64607566034180805030700e02422005011000350f0354402c0e101507800a030910010313041030081240705011921883e058480c0d0054007035281c0c1d40c10b404000c000446d245070040e00480401039003a81d1040d0034800500680b0003090041a02044183c2101c0841c3c0d551926011030f0640003640d034110500601c4002821544180c0e0180c0c1c01110116090004100c00c1c2e101c40000e04003402e1041c5440c0c80c40d40c4030001401084000b8081c242d0b5001a2804901d040c0005420414000c004000200c0d500c01d200000707103207060004d4032240d48000d540c01c203030070b01c030542a4050700010018a1160f113155240045183d869032442c1340c501051041d61400c1e02c6080c050a440701c130580380d60621a0600d0725a0070f80707032002040b0b038441c006203005000c040f40d004011100211001e14000c284030105107c02468418003207420320442da500004544855804580400041030031030340300d = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 390512625 1250 390511375 390511379
    0x2190c0e0a0c050313020415031b0605030108190218072106030c1e0308040e06012607180f080c010905031203130201090b070f051e06130303060305070f050a 69
    0x54007102d0740d40c42c07000301107a810000f19000c20342c482845040c00f4401040490159494108401c105e0041e41c41101c6000300102c0c2c5404040c62411018003900315071600605545c50400000d580f0309009224a4106803544200c809644440710044160810341d00b882c00203040c10350004001d0301745552540400d0000d9019005072740404d016513021607801041c1c0e080900d050000c00450100e108216101c0c1801e8880000001030340745018200818a00e5444620345c0381020000d00a90408521008510000c40724001c50300200d4100541103105884c001d010840022464030a035030321074101c5105030f0122100052191000140310b2035014003a6520044079940320289030ba203144120001034082e034148002241c1c090003400c0e0703e051500501d0720314074590343c07501c0c007400a0340007482c2070341c1c0b2100c0000c056080c030004000d10020f00c210529018205032601803003e403a01c00140c11025110440b0301c0640070325110360001d90266411030181e5500b243e44418080d402c54191090900030b4035440c3c40 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 390513875 1250 390512625 390512641
    0x1b06040b0a090c05130204080d03091203051905090709020c0705030d02030a020d0f020c060406111e120c0114160e010807090902090406081911060405100f02190c0e 72
    0x141c1903520743d220b02c10b00e5000c0e091030100034542810190010800e5404d200005802600700211070300d94141c4d440010390082c8600700700e055a408441c43c1e0050508240c144000322a801d410000c58601c8041c0026007600c850016074105407082c0d0110070003a00105601d801048089904021941c0c102d013211690a03500c0c100760b840e03000715910711025030002c03944804214054004040240c08603c151840640f8490010340c09801c2600b0403400903104071034010381890100421041c00c400440303070f0340d06200121146541d80d00138820107030748a18080790350360100c1e0f4250051005040e120b012205140303081e4101e251582c094100d460001062444062070550103400b01c2c50241e40075a0f200c5041c5810440d1800103940400c003465001070781c60100080080f010304c10140842d007407011800482000b2300b4500ca441c081519960f03ca5032007044200250703641c42c440802c941141e030424104000d02e501060381070024243c04051460b543c02e80070380c10864000701020903540c01901c803514685911038 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 390515125 1250 390513875 390513881
    0x215120a06060c02091b0406090e07030e070506130504022206030203060a030605040212010e01020306040c02070b1e0c0d0203030a11270d05010e060a1803020c04020f1b06040b0a 78
    0x1040c10b010075a1980c0c91005402e01100841d40310b0344c11454440141800d5403060740c281d01c654030000010710302007014004204a000866001502031500703010340304c107020000c0e849a09a2190b644601000a002036020101e042040000e04000f04215100c000003001c0c0c5d03501d555042c005030b5030843c040b2004038a0070701034801d490052401814080310541940d5a800051030041c106a0b48052505202c800811090080c003200e13558180c000f58807400c0c0003040c0300584520000040554000c41c0050100b10110302c192805615500090354840070302c9142c00a0600c03400a9980301c90155040400d20103400100070b40c06a103c01c0c0c010882d8550490b000c40042c0250501c140007140b542592442d0404015001600c0d070500034142290310285a88003403c5846d111800d48890f040b61080011460341031180750001d004020840828107100c1e50000e40314240d41c0a040d1103103034049071350355800c1c205800340c840145030886940b104206400900f03a40301c8084030101d604003800d0002602912648c0 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 390516375 1250 390515125 390515129
    0x31812090b1c09020103090203010504200a030f080307110a060c020c09040809040b1207091a010309051510030803130c091505090c070c0f06081b0301050d020d0215120a06 75
    0x644a0401815802e6420081c0840c03003410790415460366030160140c0d03020700c50b8038000da1003101c030038090001d001d2100d42c82c80d8108008600c107010b005002c002180818001100c0b0b5070703110b10b40950b80d5a86403001da5410910f2800000980f01d1071903043c041050304e41c0104d0046140d50220760100035113000b0498080c4084600424034035040c4031807002410250403080842800520a003d29009039400c01d00d840003990010442c07035154414100b08034035400c69051602c07401c0c0707024442c0c80002d440f8241d80d0b007207140ea071140a00c448400101e1a0b4000119031001d90303481840c090b56030400e41841d00010002010950f20181c0320240003610a00741d220708c20030700c191800e0a2000340c3c509400c05c40c080100a00448444804000c03810000c2c0180c0440c401800603007600c41c0c445400e209008102e8079000700010034100e00102000b100242c0c44080d40c1c11031b1011101d801c689161480070a0703200485002c002d402070030942c12030401045ca600908400350400d2000c01c1c069649490f240b054980314 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 390517625 1250 390516375 390516397
    0xf0601031a13120e09090d08090c0d0f050a06050c04261207080f04060c0318060903080c0f0f0718110904020903161d01081b04020a031812090b 63
    0x8156842c000a60b068000082c0541506141018845140200301e000504807a0701d800d0380c21032083c1c0080103800c40c01203a04a801070000b01030b8811010003280f40b1842c80140034114114140101741004000c100400b05580d0181c01401142080f401d210100d800c10b000c0d01080e4072003030404800303505203d0001741c00072540000a00801c0030002c0741c42003e500415040c3e0f4841e004110448914104c1c0005000500c0a540c55050158803404c1c014008245a22001001514150304001c1603034003a8103002503a800c082c0f45a5911040202a4640b003a01d500802d40c07030182d106152180c013030205401c0304840070312034103850100b20000e425048811004d628100c1030010300c0207028505056024090340c00e00a02196002008a2007504007000b10b0b0b400600c2d00d100c0030100400f6103c1c5402d0035401020300000420130040010440300d03003203c0c0360f0211405258049a01444244aa00800328910342840c002c2c2100004d400c1c542c1c1e021000048203008a00c0c0e0a60000c0e01c42d07200400c488040b9a0 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 390518875 1250 390517625 390517651
    0x501020c0a0b0c1002070c08010c050315041d1b09070c0302070e280c0e0405040f3e1e060d0e070506040b0c10020a020318040e0f0601031a 61
    0x2020b0105803103800c4502600100e100b41100e40f910890140300400c2028019440d450b0f00c14a800d90023070030343d44004d50305001c0040c00d0040c0892010400407541210b042114089070106819890801e408051121080d40f4811075000c680500076014100540b0748013500c40d41c2e4030b47d489a90a0783ca4007003004005005a01c59842000101c8201e0055a00101c400110411544000f0400050100d103004401d051a0365041d442001031b40204e021045560260383c10f0000d85020b80300c160b070b803800304030019221401d8580d040441d21081c0118034107102807a0019000c009158200d008440a01102c65005d2251a402500c00c802000d1818103c800300920304d030314201645861a0141c007007280320940510070391703401140959170503000d880940701880000d40c40f500c070b21007139a260041083d19885002d1040000c1c002c1a6404812200d00300f0a50700208001141e103030204000303000e005c110b50380078000c0c04043c015610011038402d04036070040022945100641e02900d1603a54250346020120768 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 390520125 1250 390518875 390518879
    0x604090c02010506090618060a151223060d02120706030c0809150606070f080d0b01120509070b0f04170f060702071d04060f0911011b0f02150403050f01150501020c0a 73
    0x847d00c2e600a13401107001e407400c5c0155030341e1450145820715500e030100c045800041c40005003000c0d0310580c180134484000b90000c0e41c01c801c051080e00c540140c1461b0185404206007400d6481d03c1040014100c586000c8030802c940d6140300500500e8034403000c1002960b40004240304c4000000d4524500c02d403440400f00c00c5d2248001c0054a134481101103640c0150011001d01059288021342800c8480050120f40a54200001070120b80c0e00100030034075900e08024418408800100300341903030a0f4040c400e990b12098400601203002d1070340709408004000311a4402d10402140102e01c0c00ca40d001290001d4540d0300040c0c0e2664403600071111070780302d40c505001841481c00651074119004407400500d6051020010301924000c5c030342030b0f4a02c0054400c07960746590010181c0d1001005607a20340c2c001e1030942d155101000c003210040d2003a48002008110361550b00c003154000d40c7d01500701c40074140100786e218007030803204082c00a1441c11441c001030a5002054184800400070a0807584d03034 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 390521375 1250 390520125 390520159
    0xd0c021c09052d010c140a121b050601090c0908072309070203070308060d02040c0804030f05130b0904020c030412060615020307120e060a210b030d050a0c020604090c020105060906 79
    0x2074900101b6643d06184202c8011101d90900620300f41a000d40ca26091b101020710000d82100c0c010782c040e10285002d01d11000102c0c2010a006041d42e0003000c3c0480d4018005100300c90384c4c1a10780140101b8000c0080001d818054055401d070701f00c3d818402c101c80c0980350b41c2002801c0d0002c40d40c84015030001c2000d840001e00c160300f0554021030040070391100d86801c0d00450100c8500921100114241d8800c1c8403d064101111b4120383c4400c0ca000e0b8501a00c0340502110035105100b2102030401c0481c04134943d584640540785c800b0020022030362541d03030307035200c0c1c034a500305644c0c05590082c580800410754444e181442504e400c405c0d00214035050040d0340d62002c0d44112080003003005210005030300d041e0754202c010b04000401e42d44030f03940c0f0070100444100b03040040404003021442c1c52103441090320007140c0480c5040c0642000703900c80b4070150707080d03440005682c1c0003540714000281c007240003000c03680115420318040e4000c1002e80c7d46c2c4814071091000c15113415038070419420440c0444 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 390522625 1250 390521375 390521387
    0x150903010c03020c33070c031101051006111507090911040b0304030c061d0c031603030804150f0c030c020d0810120c03061107050f0a080d0c021c09052d01 68
    0x1001c4544030a44c0800ea503820010528417040c0d59035400100b0025003c0d09260b4011401001060b4010080000b41421100400c441a0b41c2c41018103100d142392800e68040018011941112855941d5452501e000302c0014400200350041c01501d6151800284400c600d02c820b507020f41c1c9101190030710355110703074030141c2e410384051404841c1c440e02c0302c048800140d14840c1e1103043c58003c10082c005180520105802c00804034005036811111810410219a0203c0101c1d04160851090400ca001404420f0302600e1840d904071420360400c0314400a4643c907a03c41480034685500f9581005800117013202c0d08101a01c0d00c0094600303201040c40f0258030a02071450251080f82000203060f500c0e9210020ba9440704030501004a02146080502c2001c0c418500a0310044020f4041029190307210035460080726141c0509940d10382000d130f11940200601d506489403201c40c540300d03a5918070300902c0b0326424060340e4000c543ca00c01c0b6103028241c65460b4003060080e685440f4030142c48030011100 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 390523875 1250 390522625 390522673
    0x6010c020613060f110307080906030402190b04030c080615152203060b031c0c02042717070305090d0f0f06060503060615030a1a150903010c03020c 65
    0x80314000b00300c82c42680002240c00c034002c007502d40300c90300681c60900b4007901c5011441114222508100601c0c00000c07100e4084640074a82241d003503840343c44900110304182440704039403141e0714a040c0045541076090000d08100d07842102d08100064842c00681d84440e0140d441459003034800e0380c003511307500e013882c0400c1030300c0c140c05030307443c10309000701d50007c0c0300d034041c1c104000c001c4403180043c000c4c0326160190610b003680c00c0e002003c0c2c0340036041404a0503a0701d41340c400100f10702a41443c08550301c80d04641ea0501e4000500c04e110525804a202c411448120889602c04440740841e00080701e5001c0d60f50f0303a501600d55508198105041c0407000e141208101c2d031181610b800540014280f03c5003210417405214005115400c0c44145840d1880203850300d1310174070710701640403040000d10045130707845400d0310004071340a19000d14889460300124015035100712524080880b030b400361400380002c2e40d01240241f0010180100590403032003001030420650b08035500800200c1c40410070110 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 390525125 1250 390523875 390523879
    0x18010e030c01080702100c0c141c030e07090e01020d060f0602030d020f0c120a030609020403110f010207090e0d08011e0b030702030717092814120609010e0f0a050606010c02 76
    0xb60f1b01035a200035011102e0310040d4501080c070310b580070000d000c3c0344602840c6011241c3d000304005a1821030307248484080002c0384c0c0405440e00346008451400380a40d900a10302060203220249080381c0d001d000c1d40205e80003840c05482c000d000604900e446803c03204840c41034000d1413802d8007034000d800281d8402118001310860070401d003040384204000400290301028402e0b80c0b140f01071800103040c0d6100c2c1d806401e01a0060109001180b644c0101c05510302c000c650146042e1681c1006034203000d02513001055080c5444410303000481d004c50080c80315141982d600031242e81381c8205800c044c90340600003180031410700b02400b410150100850300140701c1e004807400c5c125540e551100125401c4a031444480f008038400106040c0711003500041c0d40e41c0190352185100d81000b49051405902c1401e5012076000c10381000d03a2100d00319800c28201890655550349052465a030107884a10303891000740c03040f070405041e43d07500801c08074565644400a01403c0d00c410307004461108160030181d03 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 390526375 1250 390525125 390525133
    0xa0606030218100612240e0709050604210b0c0301051003050c03070e0d1407090c050c211b21191808010219030b01030915020f0408060c18010e030c01080702 69
    0x101c405804021862206ca00d841c480d100c0c03180c10030b5041d07600170b0340240440040c041d4003203080c8075664403c01500d0540704034200e681e984030f44030394946101ea50000c0740a0076042d0301714203006540090030002c6041c1d42003664800d41d1440c03601000c034111107044a0140c41c0b001c050021880d040c2c419520015802c800524034610000c168032000030b00302007580072010301d41c03101c4410030541070b032805400114505070402d2030405410051142c3c031090240f18903521100c2118654a17541e141100340e40501d81000c100342d18010640041941d10076209910801c10b561181e400150a149401180d021104010356050186410071090740c06900b000f484240c5403010030000310b00c08000b403020307148000600c503000c80000040c9002504031038418020380e040501f040024408550101c0710100c0300c4420107001665012900300000701400359030080025409000c0600c084465500302420301010807040c10b01ca0075200310019a105000c40003c40d0b0590040c0103410510342c06441c1aa40c4520140107032 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 390527625 1250 390526375 390526391
    0x1c050a0b03030a020607030c08040302030d0903050f04090e10110d0b010302040e0a0b10051317030702031203041e0b0c031b04090606080a060f0e15030a0606030218100612 75
    0xc2c0c11a00460203900050b80003070100202680e00d4094840204d0050a0100c40e90500d0384000b0746038410707442841485507ca800c60810984140120342807138080d07101d19519142c803500c0074000b602400b040340c00c0500c07900259402100040c0300b803507201042c002140d440d0100015140f8040c022101c5000d05144d42030000180081c0e40c1c1e040d141c440c20400000140c807490100c100110001c81d1a068010803409111180d2401c487c000b4660542c2d81c0c0c44003a12041d0060a0b54034698820110000d401d4040c014080c845034611002540c00381d842180d40c0100c11116008144034890350381c40280a80c3c86800101d000307190120002c54000030100c800c0f10f0450b04c0b800217030065902a40c46240496550f0004001c419804103041c7d4224200741014002546043c501d04a1446107010707642c500d072200e0001c900b144c0c011001ca00d444000150903034205c1032483c140000103080601c404d034081e40740d030b41d00c1181c01944001d0300b910a20015010422042c01c00808440740c6150421a880c019605c00c00 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 390528875 1250 390527625 390527629
    0x50f010302130b090f041b030201020c2b030521060d0b150d0c0501030b0301020c0a11010c2a051801090506060d020706050603011527021215010201111c050a0b 70
    0x24911030001031705508480c3c1000d103485000040c0703100d071a40315486000d10a00040c0c1c0e000c150049080000c442681d5000f0204903c1480d182c1d81b80901d0555490f1102e02104040c0c008010f003903115481600da195800a255208000000440704260301c81e061118a500141081034010341012085000085008280000c5161100070b920700f0344603001090000c1100e0369142c00703101d10301a8150005e6081034007903081142e641c201c41400421280802c3c0a500322a4480e60b10240720702e07004002c03c41122038940403e0a2503102d15420b00106c41221301c0424181807a8400001c0c1c10a03040041d550f603131900034008004d18000e4000c0368407100802a07580d44c80c00d05c2c0050041c09000b04800620ba04092041508440c0f14404004207060740c488200310002031258581c1203880580302030010224000a0400288500c05c0b80c405403c54107400d0003c0d4102101c402041c0320400c0c2c000300071609140103070f40158058038600f03803513444060348c01c409039440b2070700001e801006003900841d00e4042500 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 390530125 1250 390528875 390528889
    0x6210213080d030902040b01020c330f040608010f1211150f12070e0a06050d0b040204120209060405090d0c1103010c02061b0a0c080a020c04060611010609050f010302130b 75
    0x2600302e0009031501030580c103500e85842407811201d070034001445111903000c0800e41040d0880018041000c242054180b030082403000104240500c501950b501d03012404010201d40090203004000f40f1058000f150440600b5502e1040d19400d812001c601000c40d96201e40042d07420400581003151000031401c081001c00180c4021350f01c0034155034450900034121410746000500301070801407101c1441a10b0744807170200c64152034070b41c9041965403002d4466000035001d03160307445230030a03c0050300148200c5403403000001079201711040117080e10361604000170380e2800d6801500b6071b04821500031005000e0820718ac00c0c50710651132060720709100000682180c90f05150080540c121001700400704903500c0e54592183c2111680358100040f111004190783c0300240010501d030000921014003900800c414261004010300c2804030b50b44070407009205050b6540c041d41150301b040760100d9140d2751401070520615852441142c04c0c3c2c6141c0800c0707044030320300281d111100e0341c0d01d0402c001c2d501d842c0 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 390531375 1250 390530125 390530143
    0x2130608061306150f0614040e160215070f0f0c05240106050415030b0f090c0408010b06071e14030a0201020a26180c03030d090c0621021308 62
    0x10001018a5990800c0c0701503864040380c0808038500f900060006245d2903c0c5038054480300d1602013400f180641c0102960300c5660045403420020b04c08004a1030100c400a89001040790300340c80380e80381202458191448180c40c0c55002c5481c83e01c918244900c100da00038a40d075018a0105250348141c2c85007800c2060140102e60605003004100e48170604011100340100b10614205103024904106440e5011550704c02804142c0c982e80a05050794806079040c42018008040514a0400c84605000c540c001e1041c11855401e10b8800600b5142c80340a880030aa0403d50210071048011003030064201a04002c64110460441079411100c080000c0d00c850702481c0c000503510720455a01502c1c513000150040c0c0f17140641800705000011071040250021020b0b0010a2800303a040d8000f8103010150384115098880031480d0000802c0c9a00000d0281d40500d1201c80c0041d1600c10890780101d51420700300f1407002c46100b400f00b9000c2540103245410080400d044441c0c0c56141c1a81401150 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 390532625 1250 390531375 390531391
    0x3080c010f1404030f080c0403060203060105041d0601020c0103060305280503030708040b010f080d080c0405040218040506040905030f090301200a0201060b03101e091508010510050d0213060806 85
    0xb8001c100c101504184901d1000c6910f051117012882e00803115512031141e408010001034001c002303c0d010364060410349000c0c00c1008041410b030600400c00f4075074000c08a030342b14010f1154145416055009100e41e40a0f680c0040c05001000d4500e0040540d03000d090b0b00c3c191010713451340203100c0880c1e4184040e60050001d951110158202400e00035108801a0068070440050200820000c01c0020302240f240030941848980c564401035035000754027540d072055803c5400002c0420190076074070300504001710125410043c0791600d009010803078030b0112004003a60300400c6101c403114000340c054a9860740080c000729110550030445680817542455501440b1408100e00c2041070f0280181000f0749a200d00407801d5291111003100c0c0c20b08607204080c501715800320710b045081e2480440601800501c24180048802c003d815598900d180c862914a5441d08020840503900c460644040310401810143e0015a43c0c003007085802d0f05131f80c8400101e650311000240c481043c01418800c04175 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 390533875 1250 390532625 390532661
    0xa020d1506061707110a060f0209091302371511010b09010b0f0706140702070e06030a03080606090406091a190308030912130504060e1003080c010f 65
    0x2481a00c0c007501d0841d0091824810f214034008070541050202d16844a02442c2c15180d03120300d14907850804110f40d501a1200d03003402180340000713400d9002401c1c03e9001351050311417079503407452020580d203550300003e50101601d01284c0140310740000c140b4040c04d00740d401841110030501901c0f0661255800b40400e0300d50b99103001351082c1c000e6042981050b40000a0040034121000a0501241400b91928a400100c0e03c41c80394907440054811199000d06c04106c00c0d400503c0d0350200742005c54100c170043c0319580c004a9614040410700c5d00608001e0020301040601d6582901e04a90007000107070041414410b0031115030b128025030005294840c00052036110841003045000c50f030400f50b900400c4508280000d00400c8240081125002030502d80c9a4a42c0c01c1d0303450510308100c19581c2c185001156540030050310990100031a00101c0b004c000d100e80d00d02103400ba03100121000701414004420401c04511200018810b43c825180001441c901500007a0100c40c0c0d03825600d041298 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 390535125 1250 390533875 390533903
    0x19201902040b0405060a030204050a0f0905011d0f031c02090603070309020405090c090a050601022505100f05070303150521010c0e090a0f15171506180402030a020d 72
    0x70580306500e8210340c191002e002928041c2c010944142451000034066650707040045c03840c05140d400481418030b001800d10400742603003000c6001e40b4000d407030240b2004c6000f1089400c100c0001d0307451054001c48015609022403e00d0341810741841407040c001c801e0f0204001191591500c2c001c5100711001d84001038110140d00610003107520003481900c1541c4042c0c100180c0d0303a070310504154000c0358104046150358a8500403803c12112400e404c100c3c504441200c00701c040705020003820782d2401c3d200740c075801c003070b40500320b070b041180c1410b0b81301046040202c00d010a100e40c00020b000c60042401116141e41c41010410400c0514081003100c1d1882d014038401500c20301408811001031310b040c2ea040000c40001499030a4082c100c1c03115030303666141d1003410110940110000203402c00100407055076600352619140540101d01810380540c00c450b2100080d4900003d01032030f00504490754007031001140384011880a403059030305110b00740e03440300140d944164181c041c910513001416404 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 390536375 1250 390535125 390535129
    0x601260603030424110106080c0609040f1b1101020306010c1b03080f07030201060510020d12060504090f050105060312031b0d05100e0702010207080f070f020306091b0619201902 78
    0x303039984480003106e0741030010800c071100c030004213010900d5003100c007283c2e6060708000140003025150700214405040580e1104500c104d03056245028416407910882002c3c1c0401c91804c0b848201c5100e40400c040c044204040340e0f03c13952128026004041c1290038545a482d0500c0580014240f050340c0b03100010b01004040e420301076940100005d9405081e0421040006503c4880c03c180301010011485402034504907183c1001d00100300c0076104111581b100e0914650103070801c1c40580d40b660804000c01d24504000511181c40e5081d4403845055441f01c1030f22000c407188164000e0f03a1004180089032128200b485510f000307440c0700302c420350780918204414880e250014100707800e40e40705000610108840104031000039491040b401c0e96403140d443c040107000c0621101075054031a00c1c04100d0740100001d118400b1056460206d40c07800813600401115100d500c0c41e803404108a807140e40c404502912945008881100442c2a50305007403001914000114181c0600c5a0011000700c083d4 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 390537625 1250 390536375 390536387
    0x90108010e07052205130812010603050609070917150c19090e0109180605070804060e0f1b0d080c030301140108090a0f0c1a0c060601260603030424 65
    0x2002c00b074a03504c80c4410200000c00742095100ea074016815103600c0061092a01d03203c061408075030000105807200e050310255481c0d10300900446020070b203814003282451a000085034403524850f6aaa1800c41c148003000b0b51091104141c02082e2082c0142c4402c2d686044900d5449103076051801d58a6941c4a16022080c8003428048810f0080044091202e00243c03c1840e0540309a0316001c01c100140c5141008213070b40720300b0041e00d210f141c0418009072a034094101d0340654010f20b4103200c8540c1038908191107110b031914040300c1343d10100004980d500c030040f40e01c4c1c82000c000d0150b550548552540f0750f10394070141d0010a0360304004014000f03202c10b1b00d1034130810102807a0001880c42c28158942d0b0382c5001c04405004102c1000070300c020001c6d83c1840390090300103a800a10281d41c52414800070303800101864001c1d015107000a0781c1d40d44100381680d841c8011b1001c403004074104003a0010101006000107406020800c4041210b02c0c2d8814403900842c591708460a051514032001040 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 390538875 1250 390537625 390537629
    0x40209130c110d170a020405010917100203070f0e0a0b0717090301020a05070308010f18050a0608030a0201060609053705040513020102010b01080702120903010b1002010e190b07050a020a02090108010e07 89
    0x500c6c4140014001a68071028032410348a07000003255074094609900303490248502e01074940c00380004100600b0603407048a00080300101e4481c40442c1c0628010044e50440c940160a01c09100b0701c00000442c0d03070000c81d240400010b40f026403074900784d000401c1c20780c0d022246010204000007240010075a000e04498010080145280461424000c0d0724010b08102e081061403251030b8400f05683c0c01069006400425151080700c1d036802d1380c0100a070103003001d8820800803401c4984000f5907030500802040950400750440c3d110410305039220302852040214403c000444118045803644542c4101805448403410032a9540298400242528202d544040c1000320a00500100c26000070340d4a05d00840018115143c0031540082401031908a05541c1d10000700c20703400d042c20f5019809031101003611f4050700da00f85074003244140d8085500000410300704240d40040e02d594410000b134030002e01c0da4419a03c1d244070640004074090801c1c1c01110081e5595685d002c500c20b010010040 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 390540125 1250 390538875 390538891
    0x3110d0c0305011a0906270910061103040b0a050703140304060b04050108010e060402100e032d0718020a0306031a01090b010212030f0702030c060c0a0905040209130c110d17 76
    0xb18150000e00865401d00907050410854807c0c0d00005040d4104901800c0c002000074000400c24549499500042592840b0741000b080205030031818114000c000c42c0e0580300741c90700740c0d03142600815003180c66a0111030180d0400c841c202e07007404100d090100440c0294001d81010400903000020002101c0069110940d0780c0e00d08404280c040700045403855009030115203000d101c03c49010241e074a410035666080d8940217445150f05001c1011810000203e0608803c244500305000301503550703034280c054500101022600e440208981e0380050411929514010401035030301e0780c694040b841040003072100220103100610208845114501804100740b000b01800f41190340703490b03420700c0003400200c04800c0140006500c41e0080003103c80a01201c0211542303840c0c5550716001e9600f000000100240c403250b00000d4515290090310707100c55000300003c40c0c0150300041d000c01000621450b40501403240322001402c10144400316070044030f81ca0741d50028103408004d444500d4000e0540d0 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 390541375 1250 390540125 390540127
    0x3020c010c0f0605060609060a020114010f030b0c0f19020c12120d05101208070501050c0306101110020f040e0a0e070302060a0c1506051801030b060103110d0c0305011a 74
    0xa4046244544010811500f002c000135460b150a0b020907094443c3c1c0203010f400c1a8001120000c0a505500c4000d01003545050a005644c0302e003030805a40120b0721000d00301e04079040c080b810031a004c00003130404009002003180b4050961400003102c020f00651000907800c0240801d0303040c100702c240300c2d008001510182000090325170444074640501489022019030f140001045840b082d44864090401c0c0c1800e028500c8140c03601e68030030b50004100720b030154240340c08514410941010740e4001c520040c4803120342d0514003003c50f44010081101d201c41d209400711441d0390001840107006904440940c0307603840e400c000754500c8020780074204082940c41e01030340030029180030172200c0c25680d04561150781c81c038140360116050744035035070060205541c40700d030003040712925489082101c006907114912440810314618508009100260144200c08001142036120b03602c89484c0340b681d900694103020744403600b030044498070032001d00800d94550042c4200005503602551000c3c05a001c9 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 390542625 1250 390541375 390541397
    0x1e04120c05011d1f0c0503030c13080105040b370204150e10080601120f1406010813032a06060e010b0a0203070308040204290909010603170d0219030903020c01 70
    0x108070005400150410b0040e200000b00c40e42e107105e2001c50307200b2504031040b240c40703040c180d4084245500040b100c522850312404009071880c03041c0101441036070071418451440d503401800b2620f01500c22102002e445091641c1c0005258a14000d04a24217021005840e80d0600c0002c0a044c0b184031421014460030155180e125661008502d1018040d031600d0b51242e04c501d030050710007600211f030f264022810407900c0880498682d01003042c00d42002c6c681e50301601c4010041d524850207840030001400c07000b0803200404d0156001d4100810000c3c160340240040c26451400e450070280215a500e0b00c9410070081179914004850140120b450001d1a140400001a5491080d01001020b0155410014040d9500d1394445144018080e119207281b0081d26110b12698020009062041e55a100458928801403140c0c4040c0c80d4420b88803065150750722030070040d03a00401055602c1030303001c00c09023180074140306910140c3c06641d04c01094400c400c0c82d0107800d204002034101d040103445102 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 390543875 1250 390542625 390542629
    0x1902010c1b02030703060c02030c070602030705060121060c050c01020a021c11030403120306030c0e07031518020d090c0e1015050909070201090b010f1409040201051e04120c05011d 79
    0x408200c5e035020000141c0c0d0090180305a05500410104c01d80c5401042c000180d02c98000c002031041c54030640c20b448423030f078031440100102007201118080b001440007407040060116030101d06520a02c6c1031160074914140c080c0c0d03082e03901c40e11420005800109500a100144291620710008907080001c02500d80703c09456490180744806440500001c403c40b005070b000340e00c804081c40c0c201c030704911081c1e203401010810380300540364600082c1c40c11600c1000600200111804d5640d4916115a1044c2065200c0d0207500082c0c40304641d01e40d00c1950200017010380660324020306180c2c043d00d4080c03034583c0c1c007a1403902d415405000035620480c454240700358450202c2d591498101d5039420359441b44403081f030060800c2000101820362050000c504031910158030012a00040d203050504080a420300094030000c1d100280410402d110a100310300020000700481020800c0241c209030b9180300c402500e1038280001c0d90340c4401181d040c070880d6880b048500c00e00071243e01c008070300421540 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 390545125 1250 390543875 390543883
    0x32205030a170d06080a060228020d03020705010f0912080a05040c03140a050a0309210b01150c0c060e010813020102070b1c02032502070609090506061902010c1b0203 73
    0x640000c1110002440a61000a070f43c01072004d0b000c0c5c003007194545d1101d1f151800084d40084000124151541c0c1e010782070118030f012080310419550b02900e103950388420150003075001030300115055500d0300090280701d100741c85002c6071580a070204e4110120f0240e00078000e500c02a190803400d500304010000443c00b0b9841e0101102c0d40848003502040d0480e0389281480c8150314006c00c0c03030052000e0380f001c1c194017114001c1560f42804503000e01c0d400000301c6402c5030400040040c85200a8801000291007040031100d24900300e05080030441c8c2c482e694034034102002d40051011407400c46241c022542d100c030301240d21144403c90300060408580010759600242e00c501114040c0010703c00305081c0b80d85107203039600316600314103648034201020070b08020000c01d55003094155802541c4408648002040d100310b481c40d8558070007a50400321040090300000b0101e03a0886420002c4d694840e04900d00f907400c4810799400015122070f403242c02428280a042d44051002c8480244170241e60086 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 390546375 1250 390545125 390545153
    0x80c030417070503030a0504060b01020c090103080c030405060408030a080703180b0705090d05010e0c0303040323120301030807020a09060501050f0903010e1603060c0807080103080702030708032205030a 89
    0x140d07951880c4480500c0e040064464218001c0c001d0201005104031404103420840c0501e100d09e105214034032030345004a030f68000112000d540482400010400709a15000902c000c400170815203240075110300c0418601d9100390f0101382c031342c0c0c00040e41c9402c10b82c0c001356141c1c01c03e4003440c1c14015500136203410700400380190009008c070f09000d00440c15542c080c4c02122445a0042d103009031312917a0741071131802440d54105404e182d01039203e0300c0d49245800300485094a03406101040840341e030720303188036a0f8008214000024030500d0049030f00c1d0b05400000d54021480340010300c2e41c03014913206000b407d01c0181c0c0b00e42081130400342c043c4000d030303044019546030740c500202c50786e00c40b84103a000902400301ea21418040380140400148040180c00c140030659000c0c000500c11064041c0003246d0340b040c200c80f2580002c9020005100080700c0301c005188550000301110038040d2a000d400741958413140682c10654140190101d840304020310080040200f103014044400c580d07107460181640003 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 390547625 1250 390546375 390546383
    0x120a0305100e0a020403022404030b0c0d060f051c150b0a03060c050c06160c0803072c0a0f08060f18030c100e0d0207260a0c0312080c0304 61
    0x80d40028800c0110200407030002d05010390155154140440d141000b51310601061380941c42d504941400c401c45c100740000c440700d5030141689084d185803103c900d000700c00751030752149890400c8920340d036440328081c3e40003078000516100704040c6082d0400105c4062405402400101c141200d40455001c3c1c8507241101e0072440d0100f5036411000002d583d20310640c1000381500c0c900014400016400b2010300344810350780c2c003124565200d4407000b8510548051000c40000d081146020020b0010005181c10805505210140031001d064101d40110704c0c0290300082940040c000345c00d4500003a0000003040882d4403440303080d0504403600e469990080a00c650301c920b070008907007070200c60094082c0c00c01c2200300b40c1c1c2e00c0f05074038690305840d03204013042c807004541820301803401c09102080c800c1860744650000d00005140c0300c4070070346213000050007001c5400304c000d40c151680000c1c071054000611800042c92103600f180781c40c00060040b00414020410310208101b9004205000c0729041500 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 390548875 1250 390547625 390547631
    0x2060601020729121f030c050609121506030d050a0e0405220602040509160c031119031101150e010303110a0c1202091602030711030c090c0c010b03120a03 68
    0x841c0500480c41c050210220000d60f40000e0190b2500442200060040310f420525100203008040740289014550002820050020400300964a0705000800396800050b040c88003644400d02018208406104502014850f80b410030680f850203002c0f045104030305082c800c0c1000150070004003400c4107441d40b64003617a07451001c01c5c000000e541440d540c1d0066980d240031403010b20310b0114042d4100d0720416004030b07801c01c041014081c402441903034544c1155a8520000788548040b120440380c0d60915002c0e00901c2d00350401c58280104072200f040c080d460700896040300281e020300f1070b840314208a100d801d01e510240440303481c513100300341180d805240c1200f0000c2c201031003600304514000010b10004141d600001c1c104d00110540807628003c031017580741541d5203400c1d1044d03064546000001a00204007080001c0c015483c4052040300c06422680d0007511a40858002e99003070b50343c662200000306130510f1040d000d0041075244101030700a0a08980302000400007401406080000d040e1 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 390550125 1250 390548875 390548909
    0x9050c0901031a0301050910050a0c0c030f18080d0e31020d06270608032203050307030230040b0309010b0a03061b050906190c0b090c010e01020606010207 68
    0x914101c403600c20f0b10004008210900301810141e583c1c1c1500300e004003005042034005602009a4800d1035980d46d50342d00c6480d40d04040e80c0c2d04a604c0c12800c030b500000d210142c0d840c1d210310104c8000340006440c0c004000d041c0d203103003410081d1002d06100002c5110782c407201060701d20403688840708880c1ca16104030400701d040c00d90100340c4c003038000c0c0700803000c40a00d02100028500f05030513078502da02d203850f01ca020880d40d0400340c1205848442c0078040b00d0ba801002103002d007d0700b0050104280d0342c1c150f84945415120b035142c50030750b88804419801a40608180020003002c00b10517007076001e6000e91050301f15800446011107029510411034000d00100001d0b000c81c1003034001140c800e00007400c00219984910b8820001c114607241e230a441910860140c0070207014204403400782000800860401c0b503100d4003000300c03401c1048030204004c01c0c0344a150010360aa415203000301d0144002d46101568100010500010100400c0c11136100109209560760042074101c00d9581400000d51520 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 390551375 1250 390550125 390550151
    0x10503041502120403140c06060f0315040b0711060114010819050f04200303070f1403030a23010e061011072d0b12040609020a090903030609050c090103 67
    0x21107201821161a000240c51440390403002100e51046209450f24481007418600d0f402c414003a030314140c0c003264002008200b4500d007881100d01819402822500306810000c080300b181d0b0b801361011a44000078009101c0302c950040e02c2c013000c0701d49140c0107105940c5000380e4801a00c03a6802002e040c00040008100c101d00011840209000f201009101a0601c285040b42050b4100e405a411100b0f203101d8100310030700128184005d540050096081480540b00c0380c00b0031800305422900c0021500440090b00c0b41840030f14411002044001146200c0c000c1d040c019240c80c0b5006111a03d6107001404460400c1000ba0b401010942e80c00700e0b000d50a09042c1c605681c200c2d240364507882007110000b8a0700380542e08044a400b102e2074114400361282c4e01039082c000500034404170f81d01c10311114221826900715a1342c0a80140130110348d01c115500803a48452964119216058840f144001859098040c007402407140e03690800076440c1c4200900c466006840e5454100754582205221b24 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 390552625 1250 390551375 390551393
    0x4151503060b0a020609010e0d14031026120a09060810090f020702030f0601030b01121704060504031a0103020108060d0201020111160b09030703020d0e060c101e0203010503070501050304 82
    0x940740c09850a035641018400c00ba580c1d0b03004644a501960800d4080f48d00028089040501c111407511007000d800130352241c000d45900700824201c107008400c4d00002d2a07030300e001c607071041d5014000802d45e1021042802c0504002c80645840d80a01007040301c041155030200c4040c0031200b00e49858115a01c401d4000305060140f0f41c41a4113942c10718041803035081490307000303015040c800c40841d824102403910103502c0d50b100b403002510740b4514a0042110a072500c22410882e03100f0302044402031a1160140420741258006000044000c1014010000d00d41811125070043d4100f0582640c9903a00003000400014041d40c05482c4106202d01164000d400c00c44c1c2a000e2815515116410002903100c034080417141a6581003161021501016000c001c482c095900350f030140842d20007210f000e81c2d51640c101e401c103800c06420005400011014002010f400e20b0500010604040803403c10440422a035039110b21644108010001d50b900015500c007218407e0034807a845ea512400e101da08 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 390553875 1250 390552625 390552629
    0xe04110d0501180b030610050d0305210609010806090d0f02010b0303030103060b0f010906020c06090a03150507020f030c1b041107080307030f140a20070507140415150306 75
    0x80d04007000402e2003082403a4104503c105850104034665000c02010381c1c561040c1e0350100c1a540480c0188828105001c081c0b5000f80682022450100400280480d03001c0d803000c26002100704100b80016881c00303804850040100c0c1c8003e00c4281092a03d043d258128041004144560081c2d2030100038002e4210085044c0c0c0142626129039480c14481d024021012000d84682000c4c44512500d41c0182e07074039001e4440940c0141a202e45400611070b40750b02503a0340c56440741100000200040c1c00c4c0e203403d4035554403c5d401081c01c3c2031840001e031412000c081c0070b0a07150030501c125201c4620018440c002241001c1c2c060710300508900100b001000088104804600e00051000a01000f9030003903004004a6034100a100348801200e0704560103d02920040e00710b5201145080810390050581010303103060180443d000010b0481da55440340200716816080818100302811440100c014110804d807000d200301c510200403040140c0490107071003803c45920704034503000781c820340c06240 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 390555125 1250 390553875 390553897
    0xe0f121207051005160c0203030906030403050a0e040b181801050408040305060703060b090f0310050a14010b090603010b0307031e0f0c0c0c0b0705151807060f0e0411 73
    0x4115600300303061128903408801d055446100b503508400c003100c01807081902c206208102d561412400d40700403103031440006030a13a8184001e10001d802d6a0394900111b010314401d480d002d5075414103240103003c00101c081100d00c031310700d4400010f08549a40c2083c43c000c0a12007442c01c0381d50382d4018008107404055107070100300c3d03103008104010002c12000410907207001d40212041c03660f8007841207098a60074040c9900750b40c002e0108100c42e041c64555902041c500406a070048c40d086100311007111000c840d560321032500c0c0d004510010361800141400b41c555010801c0ca411811404900c0c64401071160611708000040040c0802d8801e50011104420249a403607482c4401040d440c0988510b03180103818501e881a82e5407510f004400d00c1c00041ea00c1030800b00110300d00084004c554100c00c0741a129400f034903402c010310a02c55100584140e060508070314142106030807051500101d9000740045c41000710001e414160003c0307400c252178404640106191100c0380c1c00c000503001c1d00300340f61 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 390556375 1250 390555125 390555133
    0x6030305090a0f0602120a1e0818061308091c0804060e042c0c0409120e0d0c051c02030307060509010510030f060f06051309060b010f0e0f12 62
    0x11041561140081010420407540c2e480d09549511607075003d04994441e07030016a000200303001d40039401c1400fa0000601a040902c1510700c54900d11070755412080030f80e40010850010441a0080f0048100116003224000c10840c07030210b081304000c03110040c001d0a43d00c00803404040559446280106084181800b03590038540c07072811200316003107400365401044528141000509092050342c03c0580ad4901d04d49003034487c941644078048100c18116290700039104101d8540d00d0364000c10000c9441444034106c84800c02400811180d9086901441254908541800b00b922581ca0200703a0384100c1e000341c224801003c00b030290300c1045000a401d8080480c1e108280300e0b0075488a0f12801100c40203000310b035a0b0090214400c4103501008000d0300318070343c01801140b80e0f50701844400c1089203000540a40b1203000070002604a110389040540300e500380d00400125000f4000c1c42102802c04020301c00e000003014042c0208140c0769801507510100b045025036440307a80c443c030072204a040da = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 390557625 1250 390556375 390556379
    0x3030f040c0305030703030f1b050d050c09030d0903060e0d1403101d0405010b01020d05070809060405120d0f180311150c010603300809030c1207060b03151906080106 73
    0x190180c030682c13585400307480c6407103034030b1047c0d0090141030f5503080f249d60f444078500050000707868020700c00035020080300b00041c02020482c0d14200080c540401094565541c00c0d0b142d46420410745088071180481d5401603204600110782100c5981e0240c40702d90f405c41c1e102e80d142950846405059030207041481c590700c0089060300c110a0915002d1405400203000c140103000059035201d40b0071000c5c10004104001d480c0c045078000001e4034002c00010129450308d0750f500005161b000781d03c000b6104680201d03440c1c80d19941c10620040c0d1a01c203904000000c02c6003018a00d800c502c4c07034407016114650300c40300307024282c0d508491400c501000034030035500e89503c0e5407010b0003490325010807a1034085110350307100349100d40081100746628902c117441e034180050100b1035990001910a103030314402404004141034051042141c4086c6042509460b4030036403d040041c3c45180003041d010f90040580011440c081841496120502d04290301c1c0750720400200100070099544549a0740d4a00f10780 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 390558875 1250 390557625 390557627
    0x11010b030a0c140108070509060c070503060429150f030102090901090b01110f07150207120b0f07030e06160e03010608010b0f0a080d14040b0a020f07090e03030f040c0305030703 78
    0x440c6080d82e0306514603460501031940103450044042d00c06c0c1011641c24440411140351890061449203400d00a440e1181d076500082854043c0c1030b281141c0e81032444001c681040d0410010724001c82401100303103441d041503140c2500c0d1001160840d8040c6102e908502c03a9610b00350100d480d00c42c2c000c0d10a1000c2d40e510301d0ad0300c000b00000315040b40059001080201c010a000440209182e0030001034000b0303518000d1178441030602c005d1000250300880400003400d200b01c40c000090103015040c28109450708950031034070344a0051080c23081c10300d8040980401800001c4031607000030801e01007241d0000310403003070343e2802c004586541d05600301072003c20907d80641041c0d8848000380d89000c20000540100300c1d070210113004c3e04090750300010740e19580320300c5000c07511805802c0600711880c040d00c0c3c460001c0c45a0040003c10051b038402d1041c80b441d0305080102c8001003050042c100140c080c0d8070001a22484090045071408449a0201c4c00b03000305803c2e40001560b00204482d510740007450 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 390560125 1250 390558875 390558893
    0x3050a0e1b03010b0d021525030306030c0b12160302042c0c0306030615011806030c181503020904060f081e150106030203070c02030d0e09100605030711010b030a 71
    0x410724040e508001e00f07480542405601001c8640d030003006058030b0100400e80c0743c4aa0403008941380c02d803015051040e0545042840c0e030071000c4c00b0317070360100e00c3d503066040c80d052415055000096101c010003c076041c010105c2d20b0542c10aa0012800307504c0000400220064011a004400ca501c280f0b0240602d441c000e00f001c400c10394004006020300c1c1c4d00c000c4048e2150004841e030781e8054100c50006900792000030b06080780520305040c142400380c002c4251b41102c92251304003074042a41c4400d2841100d41000c14401041840c50350101e400c0e00b842d000c42442c100c001e00007818141c0116411041d56910340018002c0c008038110185415500c00c44195111409010408039508100103e0000200441c180c10480ca22004542250b4a4000d0480003584000e04503803c00100040c1500141da0070b2213039103010340181e92400307142c090341002c0010304100079200704020680140c0c1040681d42003800d481d07020300f80f420602a40341d0040e036200d000d4000d02e00300325458010610b400c02000f00c440c07 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 390561375 1250 390560125 390560173
    0x15160201110315010c06060f090e01051b22050306040c0f060203120106261005031e190c0911130b0703020a0615050402120f070c0b01050103050a0e 65
    0x940248210003803000021094481600c541040e80703442d005090b06540101d130800301d168800c060008003160307960540d4461081c0d58008008040d00c90320103c440c11070034040c5603000300345110200380038546091016400d101c0c040050039841c00c641100010407542c4200f103801018040d0540c0c43c646007a10744200405158040c000300d10b90845008608148000146c0305c0c1d40340b2070310603c240c59090244c01e884000c2c841400d4103a17001106404400c45041d1050300c0e002d51882200071100d1810001050705080361544030720500300084000094a8100080304c200b5072000000d0403550a11605040b0b00c1d840258001802e1242445140400005220001d103119800007a08010181d19880701032402d2027403007000340041c3d000e4007d020106445501caa0030f14580003045944081e5940041016030300044500601e21860204200809c280f40095980c449d01e18502541224641c0d9100300211a06018040c1015602d900180d07050b1155840042c0d0040ca01c0100d40c031340141d002d2001d441900007 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 390562625 1250 390561375 390561377
    0xc0d0501150806070804061a040f06050931030c0c080a03020c060f0a0e030723040b1807030e010917070203100c0509010e0604050a030b0109050c0f0f03091516 70
    0x41da40024000e00d001c141070780603003220f60310040240c66607201d12018101e00d0100c101076004504500300c007039032207101c0c0c2c2079078205000300442e602e480d120810462250003850081c9407403d2154514040380c0503100000308240d101c26480c42c8505504040301d1294200c0d8009040f2041c800c0d000c14400030001d04815864400e070308079060080030205002c9503025148118031540d030103004400c0054001c082d6044001005021030340c4499449041ca558150840c91003c849010101e41c4641030a0501440d51204000e43d80d501c8054802c010201c00740c18000c114900b05562081348910b010020341040f104250044072100c610045440b6400d6998080c41e0124800d100b1612010b5100c040350240c0f100c02021074030380b6814a0103100054940c0b0b62884c400c9503004800f0840420240d942c0761500e8051405034a5204440d8109440907040b96805003030706048a0083c0b00d1070040342056003c6070380d03048030710b0301558881d05d900080e146040d401c5101c856100075020200522907920030451b201c50202 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 390563875 1250 390562625 390562661
    0x6141b1b03091c060608010218040b240c0f030708030412050705120901020114100b0c01020c07080a140c0a062015240a170319050910020606210c0d0501 67
    0x610b06d0550700703e10a10b405484001d002c50454041d51030a90310172030b030122001c0c02c6000500183d0042001580100d180d58000e1100841e170401a6101040b41c1e5210b1004840210301e0064a6102e003103881c08014070041c100f810401003205c48a210380d09803162203a201d82100c82031400341007561140e40020383c599005600c2c190f8941044031035050603074082c600d502e0440351000c2c24041584959030100c400c00d402c0c0e6408201300c561011081050200420412021b0000c60b50140ba1603020b923010244449510341c8410039411840e595800d1140855100d414003000200c50070b01e11046121050426040278010f40840818154420ac417451107040c0c0f90003103403c403160000c5140000071564003126001170139144284140743c840c0c921300c0c54a00010040361708005500314402203040395981c40c0000540017084030b00d42e81c1090380b94856090141e0015002600d042000300742c0451030740111003108100700b101c0b94049071043c007104841c0000034040007250603180c10854060200020345008840b9 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 390565125 1250 390563875 390563879
    0x806010905250807020111070b011d010609060507030309020931210c140a050709020306010e0d11190e100302090a0f060b040306141b1b03091c0606 65
    0xc6500385668040844440b5040d00094000045450280c001c1c54041959a40d49440440c40604030250072468490202d5500f1036040c40c075003e007404016804100300c40d660b0001804200e80081210064441916000d03441d45002d040c01c501810104070301075045409079040c0a9103100300819550605150b98814140e600308090503140304028010180c16054000c98030707030541c2000480701c41d41c0c071715900d00b825152520b0b4942c1d68011080120351070159102c07070300f02001c20106100420080220210450031882c000c0000b03882d80001e00000303440740c20800301c0b05003001003441020544c000c0c05800c01c586808401408068120940903404800d042080064005840b042c42042500d82c050038060403515000b860030080c08401d0003003016142c417950080303440075589014200035070082c24041124501c2c03405051000d90060912041d001a000c101140c080044048503403440c1544440390410031242980783c21805101d5105a000b01042803401192515000050020b0f01a100400c1029 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 390566375 1250 390565125 390565141
    0x305150a240e030a08031806070203030123090114030f010c02240c0f03040809092401081006141603210204051302160506090d020c0102120d02030c0706060806010905 73
    0xb0351500200d9069008000f080c0004040c41c02441e04440001c3c0001095010711a40a0400b5012103410300107074000b000407c40410040c54015140d03682e503100200c03c04551006c103544603c1400741c1c8070420882400070300151810409001582c40003402013205810341e030b81c000d44441d1950150324811403100807400f2003c80401416000b070b4100c0741c407980f40a14034070004901d600002c00c2595150720a0102009685a501c6041c2c1710b1a4400d100c41d0048041d000d2000350344500d6042c260400203103d041008500306088824281c800c181010500103206c03414031560340c0300301002510030144a00740e20003015000f140384244080050035000c01528160354482c01c85c0501e00c6050381c050104e1500e408003005603401084003261141840c0c1c525a40f0b41c5619203840c80507901c0d503000d903000582c8000c40d17035810700c070884c0408000d1000e800f009851411082040c0100350810148550000114010b180c48104541c3c0d0150301231000c0c0302050b9038681d03440e1103040c01d2080782442401c01d00083e40311 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 390567625 1250 390566375 390566387
    0x1506050f0a0e010c1b061403040b07030b210c010206090f0c010f030207050a03170105060909150103090f0c0608010e07021b042405031509030a0305150a24 68
    0x200030220065424800c41e0242201c0d0081012800703414400c8403460600451884640099400b00c1068026922840c116005014031400f800c0003005100502c144030010305a075641c990041d80510340400c0100386040041d9900606c1c00c41c4c0e010320080c41840240c0090046000380702004240c00755401c03603880c15000358803400c04059600b5550840c10494244e0741c001c0610426203092490018100f0f5034540d21701d49040c42605e800d6000c11549842c1b802009110280940900b0069607070714144005880843e80e005009403900d07202a01540d14035030240d21030343c04200d20a4101c8909411501d19007084a41a00da6000740700020b00000004600120040080f83c040d4595030f000382540c820320740b08040001f060200b081e42c041d441d00c0021403507007210b502d12a80c410040010741c40f10740c90041018904629030303074070401380b1504204220030800080292148110f85040c00304c1d0660b11082d41e842803290680600390f000b48044804940c0f070541040c18400724903110542d1189000900e0305544d1 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 390568875 1250 390567625 390567637
    0x1d06040b04080106081e06040308044d03070b030a0f0c0503100e250909020d02120a0b0a0b13080a0c050319050d1b02040905061b0702030a11061201030501150605 71
    0xc0c2d80c7c171403030100340024818044140d01500841d1010307144030500d140101205580980c0400705002148600a03203400d403111040d06500c003800c566207a42c0c2540209841d24154810403024070008030010741d6112141e008051862a03a00080104040030362028000c2c0e002600d03800704904801c2000f1901d5040b1404190040c00350424005009a12a031400c0000f003824603002d0800c058030790001400703a00c40c0050031444040c60780146c2c4900006086c09504e40d0010300003114ac0b400c095800e0140e0b190344c003504060310810b0100700e0b0b607005c9104107507110740099070001c0500c0c8200010b280500c0900300841050315421420b40f14049604030b140f41c0f0346e0b610401c014115070401014901c0f0f00b801945c00180c4001032922000219020b5000601110740c044c0003036900350080300c00c2100d40c545031030100c1862543c986200d4140812600440d07910950740314010409010804101640e80d81d10050700e0b146520841c420104c0d607100e1a0150280888246151107140da0700000300d2283e006000b5111 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 390570125 1250 390568875 390568933
    0x6180e0606090607021206070f02161a090d080f09090a1406012a1a0912040509060a0306050a090201030b060a0503040215090901060306060f0e011d06040b0408010608 73
    0x4104010300b02080b60680c4030110499000000c560307480700d00c03042030040911800340781e10b602d0550050341c60042d06200d50134102c0150ba07503e4074020302c10901000c440c000061080b04c03c254884503564089601c68159030000382c1200c9000c00d056403040e080000030700802105840000d6651034000784102074400d901d407038454203a0f41c0d10010341c0e81d502c900c1c108601004004601502c1041c0d55400241070b610400c025568610811900b200e00341607500c0017a04252080000c20500326030104004480c007840c00780d81d1141e600080400e0303040e0390380382291010313540006d0100010700b0600da4000050100c3d584c00c074042400c19018100501c0c0c0032003940e04626460311801e1035642c03507608100403541640c0708400304220903c07000300030f0f46906075114064006d9440001d00300d0700301100a002d8a15403010380c0104060384201e1f10f8240d9202c0180010040c901d0045007450b0589000030f9054051074202c2c14800318003040000304803005401c003a0499031110151104030400806010b130200c0c00a040b01 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 390571375 1250 390570125 390570127
    0x3071e11191206050f060a05010203160302010b1f0e0306011d0405070b0a2606130b0a0305030d061e050d0b090a1a04030e041a1e090106180e0606 64
    0x240030304140050000045501c035280d04665111031a012282184060540f809543ca008020138441c0c80110700350421000c40c3c507207816514140000399684180401000400e5406116008160003500000000341c002403003010404c0c10003507095850074203614000000342840002960508021840e141600c0148590710707c50030400c03129048262014004803007038417840c0f4002801c82c2d24207020344119066039640030401017400060192202402c00c502e52000d02d014140b1580e96900e81d100421803501010115251100d140058050105035001400e80d0000198040c49000158040816540034103141c44c400d00040172002040c040c03a000c0c4030340180c0702c80703001004564155840d07540550b01004540e1007100341e80e1842d00071000300000164640301d1000344400c00d50030201c0300900e01c5050311308024a07500003600d0b0091040102005001d60301032500d6069049031805650034056010708650b146503507030075000782010907868074003515501c1d8420100301d179080c4c080c1260096900500c49 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 390572625 1250 390571375 390571403
    0x905060f0a050409091110020c09192d1103010f1a04120b01051302030405070e060d06050c03090106050312031611100b03010e0102070317042303071e 66
    0x58a0356200e0490310050010601c00080d450940b806507652440c41090f2004070f135840c15081c08114201c13043e00c0400d6400415000120f40c036408500c0b039108004040003d56481604201c0000702030402d456107406a500c0100032030901c07480000341e00e802d0b010300c04100d00d111004448519000a0140700103000060b481000101ca08a40920304400d0f400300040c070300f0b80d6840346540320303942420048480c0c00104004001c54a030041c1440040107155038250b2440c03400d6919142c4401c045c1c0140b0810203101e001060568a0b88644501030b980e014008100c3e501303007864444800d030021030304816a90b080c842c02043c24100070a8221008643c480c00d00e095807a0491503d244050f080104800c1000624003154100c2c81002601000d0f400da00d0006000e198450501d070031341b544003254040f541c0c0100b2814000947c01407000403994213980f0074084544461601080403250035001c040ba545000400410082c80403000f408564816120324002e0319803042000c01c100035400000d00484541814 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 390573875 1250 390572625 390572647
    0x20c010905011b0204020c070e0a140c03010b07140f0a05011b0f140906090a030f03080a02091804050c062703060118020912060112140102090d03110c10050a02010c090506 75
    0x7e0010b200c811000d4414841d1079024001d02850101d038002e042c26100c410b0700d40003e08040d1387c15000300100e0011031446d810041d05a51700d210341e003401082200e031503010745640b041c1031104081041c2c05900b03840506c4a00c0c28003d02074000000b420742c05501c105102e01e0f00501403800c00740221619203981161400c008245001c98001c641c04c6500800304000344010741e910811102c0181d44504500910079440e810b0003408401c00a00369181a803040040b16031030b94a1603080360003808020700040c20f540d00c2c0e00d049070500f00c0f0044c44c103402c0100402d003a141b04101c8032551344164040d8501401080209040666900b028030901079940d8829000d40d612044580080a0060010340181101086160b132180381150036070106555100340b44001c030030070881d03501080a01c2c450000a5060180420010304803c0b0341a400800348a480e5444068070760040c4400c1e061401c009102c0d0340d00010014010b4210b9004840e424015480e1800e10b1968138000c801d11000d40f40d010780400e081c8024160 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 390575125 1250 390573875 390573877
    0x150207120f0e0a12060506030105061c020d1b0e0708060f0f030f1e071a03060d0213050406050703050c0309060712020f0c0109140708120706110a020c010905011b020402 74
    0xd400c0c0300700302084120b8400758845080d00d400828480082c40003862850515000f00c1d0001751120b880399050000380b040c543d869094181c1c0228144400115540311071002130000e00550f407006110b410303484590109100c481d40072208464924144a203595101501141c20801c206c844690220b880f201c18402070401404050360301101074212140403104005091400030120300300c0a00748102c00351100d52138011700090b001130039081c008202000e01c200d10102d071404010209402034090036611010355586401c0320918610503102003142c0d003000e003840d1001d0201154840003190600d40400c0d0035030b4000c8100d80c81264030030041c1c4902d44984c3c80840e058015201481c04a039000d124000c4e0784da030001d00034585001ca0741c00020b030780380c4245004007085104031010081034009103010001080c9c0400c6102010146d95030030b550b1181d0764502000200b1082240000104c0e001c1425130155400149804003a20242c0b5420041a601d10044807200072000b800110240c5645e00c0c4001414650 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 390576375 1250 390575125 390575147
    0x303070c1a090d050c040b03031204080a02070f09021314030d14132706030312020c0709020d0c0909050705180d050111070b090105010b0412020a03080d0915020712 72
    0x7500c586810300e80c80024403840303040c00080c2c070a03802c55110500381d442d0611695030502e006401031418101c00d42802da101000080024000810010711010f40d24428002d80c8017a003138208024905a8031303030842d5402504055000907250183d09000300351030740051529020340900070020300d1a400b09080841382d82c0a89007900302030513018401035901000710303182d00c8040d0280d4440c0580c461542d0300d001c03804140c00402d61140a1030582e0600c0400d80c400140704002014040140c2e03584400d400c003078500015070348858001c03403010130420750038011038201c003043e0b43c3e890340d03802442074503540500e0482d1f070155128008038004000c0b03c42d100131400851002c114000b8451000c0681035202c1e1400c0d5503d200700311525040004504080094a0100340c0c0c00c000140000c01c40c641c141090755007588a030740074010360007503c180100210342e41e80f46001c000c0c40d070022200e40c40d2030f849240d400150000c0d00b8100d0702041000814a04001a88240c6d0b4001c0c0d00f0040450141c01e10b10300c2550901d41d44 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 390577625 1250 390576375 390576419
    0x302040b190315080a0b0112020303040501080711010f0609150b1608160602042606010302010c08270a0803120c09120a20010305040c03140312190b0303070c 69
    0xe04480c5008544100303000000d0420070045c000403801440c0805100c98140c108180e01138000c1c982c0409600c00000342c405448007800c05a40c1501d5140d0190307001c22181e003c2000e44d600b0107840c580c6016254204000315104114244110102100e0816911000340211509000c3c140810160f07400f000009408090141480d10300e00800c100890301c070751080d03900c1914100d800260400006014844981c010303d00c4003400001100300c1c00d0160784136030040c400a410801481c10380d005222180c0102c03801e5802c01c207003801e40c0b0802198141d044d141c105c9103c5200e10442070000903a140080121209840f512400945942c0c60464052598120356001c40d0000c0146040600b440e400b0032207540e110303000e103041d92005e0600c40030784014241c412904d0750405050005010005142090344400e40380d125820301100c0440c00c42c01861402124078900c041c881110500c841c4400c00052003c24404c019070a0100741041028140d8a10880800401c0e2000e095020003658080340180003181c089 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 390578875 1250 390577625 390577631
    0x103020c07030b06030c0a0305060c0d0b0301150305100e03090d060908180411180111030c070b04030b0c0408030403030f031112100509090c04020c01090c0303020313060302040b1903 80
    0x862085145022407a400c1112099039200c00d010309850100700401028000300c40359007001d400e65441e030340c0311803001d00707010402c2c0804038002c514224a40c222601d8420050700820000401c0046154201900c3c80250383c0c0740aa04e01403a02d10503e4000c08104441d000001d601d00010782c800e1140900c0c41d407100741e424658130b0f00b1400c001034a640092201e500300e4103610740144410b00c2003108960310305d01080c100390300c10040320040e024602144001040d0900708020b101040349492030031445410783d0340342d16009015020400038070000282c401d40340140d070b01c1159030340e56038040e80740e034800c0d801146070552050000700300080c459030f41703460544500d140103e82400800e6040616030448114100b004c50304208020039441c02c024400c004000c110b1b107299035402c0003000c458681c0072002000d0702803038000031000c01101007500f09400040c0c1c4410f03030001c40c036642c0c1802034807034114004204d8804005400050b1301c40c464001d0340c0580c0c0b0040c129034a40310401955010717030182030f00c0700020305407 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 390580125 1250 390578875 390578887
    0x31406060a0602030a170c0d15180b181b3708040213020c060106050a17040809010309110303030106170f06090105012001051609060c0c14030703050609030a03060e0601080f06010302 80
    0x100c140580080c140580402c1102c160800f140c04cac200545100c40c5005c40c615184030741242e40e035002c42011000c00b150b050f20000d80c46100514005a00403509000c0b01d00c1c00180c2031094001103807001607100c2c3c00a5204074402c03580c0e610b14050500c603051030700002d154200414094900014820260700d05020018074000d00d03840c0507818050243e111102040c0c0c0802d01140c15500030418000c0c4d00c44500500d5124036240c1e54401d154000d81c1c1c03405040507a5503465008005c5030445181f20002e008085a03125030356400000c100030a45000344080914000129015012251030b050140100800030030280c1c2c00e02c03004440d1425101c0300c0084452031100c40d5920448284601801100004070403484074032200000790103000c090348004200410002c200000c0b0760403030880340503540070b110181200d12074400040d141100640000e0480c1c002c01c0d090111410000009000c0700a40d034409001e09640c134145541d010400b110380c180800e01d0000003a01e904420340110b0351080c4141001402d1003 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 390581375 1250 390580125 390580147
    0xc05070b040c0510031b11010e070e0a061d0402010318020d0b160f1407020f090c130b071a0402010216061d04020f0711010504031406060a0602030a170c 67
    0xd41a6801c0d142403624401c01d111506003000845806002e80c107003440001c441c80101101c0c0707101d400001c03040114082d00c65442c0e440c2034002d4602e501c1e51504854009440302d441d469031100030ba4076501d070f0a02e488400104041e603040da144078010b01d03000a80c402e9031550015005000900120708403407409070518001a55441050800140102c01200c41d40c17601c91008420250b41100880c2404a103031a50038060342c3c4011445100c04900703406d261103429600c08034014101245040f41c0c059900340801a00d00914400b0304800136101000c552181e0f650b00c40c007066441000302c060030b90f03c204640000b18040c0341c00004e8000c0c1c4107104407101c4681e207400349038041511390000c0c400034140c684400e8040c1c0c1900c220320380141046504615045101030641058031031003400401050010046180a030700030415100216048801c480c241e1182034541526001d048408511410b00c00c000854064400400d1300d40c1d0b209191100c0d403c0794071000c0300e0703042c40c0303402481c22001d488100b04c126134035 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 390582625 1250 390581375 390581393
    0x20a0b0708090102060906010f0302130e0f06070f030234020303031f050a05031915020f09130606081305030d1407021e03070b1312050c0d0915030c0507 67
    0x4580070710000c1d0340301d04180000a08000003d4a03200b0340da4092001400550003070352031b900403240d045504110100a10749120042d0411051401047c002c4034070850394100081406841003003503903210480800c41803800c0d800c900821080300d00400f40725078020816084101c4d0701140c06181c901c0701c82c4c1520150300103451503008071a1044085038003148141200081c1c108000940b80844000c0e42c6079040802007a035030000c0405072a007409038521900c00b8800c05200075903004a203c1070035540c58400910312141540105d101c58041e10740711503a0703d19103480e486004282c562a03540e4015680b01d8100780708070413050580c181d81900040000000d51f2500c1c0c880c01070045010500c0021a1818010213810a541000a8206408060307220700c1c0350040403003120401c640c88000200aa1204013514552055240740100460850290410303126002000380640c940102e0894501c80403910303084800700c0a0380305100303402242603800c80b5060b0181e00195414405480c0c418106403003500c41c40e00d5 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 390583875 1250 390582625 390582637
    0x12010603050706110111191701030c03030f020c0919141e01080d120c111509061305120702400c1b0c05190e10050603040b04020a0b 58
    0x20360b030000e60200b00c4150415030b1a00e955110800070041d0102d600125852440751110900485001842a4030414000c0071907220102402203808007541c1c4074a4001041030050200b036001c290002e0301600f0203403001840c4100c0100c040c164203510f440d422154601c1d2060801541030345030b2141d0209101c501d5006a1034801ea2034001d208034010b210b4100510b20b0303031040c0c104039003a41114901c41c2c40e00360000200742d20340c540b00c000012078a0b80e29100303c54004848a9085440c00f600381103030545203020780090301801c0004261005519108501c040c00b14010200074410b8000c044280c0d41250181c0142400d46c0c00600300541c0b81303c01c040c210800800380d00080780300c42c3d42440015450300e05403d22180c51a21000104050b4014000c060f00d5510078103814101020064271741c0b020070070400118001400082c0400d842c45501015454401140e4004d956071081072074006030801d0303045400d0301d00f01d403406852907246441d103446145c02c098000f0401c0c0d802420720500002d40017005402440 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 390585125 1250 390583875 390583883
    0x120311120d0516020309090103170909040501021b0105090d030203090c1c0c05220203072705010e0d030915140a0302091c05100905010f0222090204180b12010603 71
    0x2c00e03241186810042d01c0000d6500340c110b5005110f0a4040e49403000d03c0382c1526040f40d801c2c0c100b044029000c030614414103140319000314030801070008000c015000303000203a140c014070010701840400c00794202c0d40d044881c1802031b44241900380c8a51f010b51300440d04400250150760304000e10f4000720700d20804564021001d100451401d60a00941c0c1c05480042c05d8115146004041009c40946402e012031011141e86030f0300102240c4541d024440f06480018110802150034403107010740411200180b10749802b18041501c0305086c0e240007508001020781c15100c41d8810b40c10b04170a011002150003090003030084641100110f1035082003d4058520254dc02682d141199814444040085004a66844c010480c2440002d60205103544141c10401d00020404100d041c2a405171820428250392103200051004009040169400070b8251540c43d09042c0c0d42e43e003440c41d04034411071007032055514070304848502c8505260000c1c10000c00c010b200d0081281c03580e20086c01c5440343c1d03104035 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 390586375 1250 390585125 390585131
    0x90c0c02100509120607020d121503110406291e0d0f06060e0f15040902030f0115021515060c0105190b0406030f0215040e070206010816120311120d 65
    0xf811a107001140c0c0d1924020300e40140c02c01d410004030203503580200300d03600c409001481c111080302e0709081d4000898502c41c0019600415624244610701e520200d0805005e1810100c01007074481c0e1603d90b49445141d929aa458072119030a105902500b09161140501c84001460010105220040c00c5841c40d0303104001081c3c1c40c070300bd52908481c05035015401344004290744150981d0b41d05c00340c0b00320303200948104102540d4a4150036240c0314540008809901c08420f20000509602e002810b86201c1c640100700d010071820700b41e03617520504149900c0e100c202d1001600d640013000407103030000d8020f0001418010f4080c0218251030044540104038860500312042d03c001c0c500418031841004d84080100701c1c1580c898000c101c8003040e01902642e001e9030031074218031071002100d008017950310380d82d04903080268000351203007828031030544680315140c01d600d032450b41000d0207801c8600719500440c80349281e43d419920b08041c840103052500a064511700c40c400b219004000e05130b0081000 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 390587625 1250 390586375 390586387
    0x9030306040f0c0f140405060d0b030d0c08040b2104150b271f06020d0e0f0a09050a0f0507020c0a0e010608010b030c07050706031413030207090c0c021005 68
    0x440101c400101d01d21030b2260602040c40d5155401040c0d102003c0b81d6443c0c07605407035a003124500362912481d800950400c5001600c1c1488801550203143e0f0810200c040c0c40000301d0040048170345000030701c0003810340781d0100802c100100c6072000810800e01d110a41c80c40346515100210891036040302e0540b000908800102001142c502c0750640c403a20032508003500040c010034032684040360240d621905201c032004203d443c03200002c0c80f00e07802e00040381e40e0402c9464602c02034a4117503c2e071180000c40c2c0e840c0c4180c1c03520302d06001f90a8075080d0203030a03060369515011110015000c05468003101036030710407982c04030180d50b00031144100c080d03400074000038100384148112004107a01000c100c9650100502c03109a0000c40181154440d0320859140e8440ca01e64065502c50f140d80148103108540f000640d00d60540c000051780498200803542c0c03030350394031168003420100000050060300a03007402e200c10380d802d90246008000601d80a0500b180a90101d03542040f40180c82c80070400203d00c07 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 390588875 1250 390587625 390587629
    0xc0a02011e09260306010f1403040507060f05090f040504030516230c0a1509120605062e03180501110309061006021c051908010302031e0604020d05120309030306 71
    0x12502c540c2c192440480d01e10403000a043c0c02c035010140c0300354100000c00358a0b40c00140b00700506030707200300c403451416a0303410a45800c81c0d0b65130300742c460040401d4015851600d0305016805440e04500043c0c00d4400000e40c2c801000010030b0014401c0741800000c0c04410700310810000c1e0400e02500c102c020380407640205c2d010b1350714100038082461465010f144803e070300f501c03007c130340f0400c0302c0101c1040042c41d001e044055a24407000d400a041084415400c541441840d0300268002c0d1025100080064030311000807402c078080030020201c0c110b40381d0a82d02c0d80e5103c2c0d48811031041070303030380088440c50035580d4aa0a403020000c03a441001804400e020183e40140302a5030400c0401e05c0c00c0c00c60340e10b052406500e55418a2480440e05010120742031040d004404490155031380380b50341000700c501a00003500c00c150030300050340a480345c401c24100b0644d0401500c07108805880040131140d480b0707420040c00d0b2550000813a5107000b03441c1000781010903200614081e00441c1e01842d20780c074107401 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 390590125 1250 390588875 390588893
    0xd03140a0306082a040f020714010c080114030d08060a050d08030a0f0203010812030417040602010e120307050f0d06030606030302100e010203060603150a1703040306140702060c0a02011e09 83
    0x410013210510200c55000f007009016210314951050310081150040460044002e0051603806441260f000300c5244143c5419032000440c61201d40f128503490741c03501c01b00c00030001e511103c00d81542c8072100d6000a58000c0384c10580c8070700004c14820480c0d49803c0411800e47c0820802c0b5225000482485091031850040301c4000701282c41c11800c640c03604501e81d82c3da03081c015202c041654000003103418408480401500810810741441d540d581d507000c024000d0946101c402d0050047c0041002500b001d101180d001344010381e0740d00c0c101420b01e801e43c4000c2c3d00504122005030390382c040010000c0c819000c0d06000714020b4022340800e40c2c4040b11042501d858a40d920f0f010703441002082003550f260000d9a4020705050340703c200c404550300114540c4281d9402030842c114000c1d8111890a0000000340300b031b00d20441d0207002400360b203070307800c1600001603c40202503004240060f003440707022009001c441550b0310000c10709070750364907002150300ca2007404042d00540700e505a20500441c2e02d = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 390591375 1250 390590125 390590143
    0x2034f06090806061804030315141c03080105010f020f0a0b07021204030b04200406030506180102090d020108041b0602030702013011070b0c071a010803090d03140a030608 75
    0x2014203d03903d4079500141c0c2c1d840110585c1140e8a620320041000e051180d482401c04002022411400503100c09094070140c60751403060384503000d800c5000802810f410051442c0e6689078907242c031540d0811006446c50441c020300700c03046200b40d4400c84003054041008030300c098051a104004c3c6d00744004000c0c10200c1c4110070001506041004100160701d100645601c10781000146003a0b204881504250000c3c3e04440c40e80141440c0340401444000301f129802900b0b281c0a004400c0b01d8002070600780d01502420540c400400d69648000d07500500e407156001d031184902c08800c010084c511688001c1d2078010350010303440821803208550b08000c0a00c41e50055170381903c111010840005288800440350718802922111180c07199001c0e0410303680d070143d06c8400c1001d145440c00052540b600280026a451040c0380c5012040a04c1092210305079643e04001e10b207442c1480e000e000090b488020100c0801c50b0078030716070801344041000f41207141444e540120304a441c0c450103500d400210 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 390592625 1250 390591375 390591389
    0x6030c050f19031d1c030902030c04320105030d050304211809020d05062e0519020609060c030601020c01030f02040503070308030108010c02034f0609 66
    0x4101079101e984802003a98403406090036018160850110101d000d4404143c0c985115000680c031080b400c1c10104445003030402c0c04ca907030f1610160302c83d011000c1d24840300002e0b4268001d0a4104c2e050300f07140c0c0100e4102c8a1429103100030052901c8400c011060b08040e0b5020b82500500522a80c90244000070040083d85080343c19800d043e283c50740341001c10803920034485100080644c82e14002c0306081d10504581303032090449680c528024001e5031041c084486071525100005600d481c00c0307000000398540840700000e03855540a10000c0c40171408603810240a0b0501103031513012601142c03541d40d280d0340c0d40030b13002070305081c101d0a142000150050304840014810802c90f40d07800202071503038010034070b00030891344441341090300244602e4000c030b601030088503008401e2110020065041340c0b0300c0e80c02000707242591081240ca9015018848600c07071510100204003c01c1c0070140e104020002c1c00d103900f103001c6070320395014a01c1c5120f4103240200c000c510802c9129005000b00d0024144 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 390593875 1250 390592625 390592627
    0x33040e0604050606030f04030903060608030d0f0c0c030c03030209040203070504090515031b0d050712051c02150c12011e0e09190c080f0a11041428020f0406030c05 72
    0x3c110001209400010011340080c144400007505240c4a150814000d68009d0001c10900d52103030103640d00e951140701010031107401d10022049c2903843e4482c503d68001141d6030400c624000350349c01c603501205000280e003007540a220300b441c1036883d440194051402602c5090356113240000c0764050b10401004803e16040107102c0b07445c0c98901194000c40d5104c4200243c030603040c01800a142c035041e074080a0300c0780c460b42d81c0102e00c0e100344118850400380070f00200d034022020340c410600c041c4022141d900041c0c0058400325a001001d503c4c00350001c56600350141424144218000c55003003d038040843c2e0414500b0448a034068007800c41c015000403521001c552a088410560341c008140102c80c050300d00609140030f1004010b85e10b005020418240e40d60360840309500c643e144082c00c800c2d40c0361544100e501110345450b120b200080c140b1034042d1314070380e03442d44261920b84031400710442150250207410740f8003103e03c8c4000c19070041402e03d51034403182008802021514415180e41c24800 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 390595125 1250 390593875 390593881
    0x406140a05060309011401030b0609060306070e01050a12020304051f02130e0a06170c040c030204081b031c050304060b0105070302060a022215030b06130533040e060405 74
    0x31046840c9041e1801500c44507501d4513120311081c0142800c0501c45104503050300080708000503040c1c2d007405144116888101621802e080546072a0305851481c082408a00b005e403c550140000d81000550f5007400c061a062005c0000140d81c005c40c1c1c205c1c0c007500403603804560801c13030041038100c5060541046080001c80b00083e01000450f004e82507507100e80200040310304411342c10040c00380c82d1070020100c1400d8030001c107030398a607051160148201e05210780c2c1480390f4841d01c06d0300c0840b2410001442904210300c03007041041240c10450b03805001d45104500d15034000200d69100c141355a640958134609070034024111101d040a13136040103001c11050b400320fa800240e40760000078094005a584d81620f01c030395001055880031054800c0c0001e40000e00192502c0c41400701d03074440d1014000101d10301e040082c1803103a1000f001c1d46a00e25030b0240220700746070201c8290001891401007407031481c40d081d403580e8907080044032136410300001c0c180440d5085a41e0b103a0014002d88041c4071a007 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 390596375 1250 390595125 390595129
    0x916150c060902040e03040e0a05090303040f02010c1505010626010803071e0b040305030a0e01060e070f0905040204080a0c15050f03040320060a06060c0f0303020a050c1b040614 78
    0x40000001501d242d0701c541422082d50341c2c5030302c000c08400c0303064110b90b5516034500080003400c01c201c0d112119140f0b0000001c1c00d18602008880c400c0b6409994103080203410350040d030b61200480d01c1522051607076017140c0a03800d2540b00d92406002c0d142c4424180d1111307a000140d2120200c0c44901034260044010455890004190f03803596a11404108088824401081024650a0340601102d05010520080c10b030468021406802441e01c00d010103920728803132900740c942c213114400700719580c480003d0650b0700c0b82211080280f45440c1c19884660b464000400340d8210703030022a02c80c1c000c282d03c0001c2002c101c1c5200028084041240700c25002ca1901070190f005004490380001d1002002408040c40b50400e180f01c10f16030001c200b0b00550034900d80303507520012a4031800d020310740440031503010b009401489a0a900c040b05c031982c03442c0e0750f03000c8010790071100503541482014000d00b25040000d11609007080700e40c0f82c20810180e0300c1c03010030050703031001c0c0d20a0110300c0c8a155140015 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 390597625 1250 390596375 390596387
    0x70809120f030301090b0a21030e04060e25140d090602090303071401051302150903010e0d020f010633230301030614060105250b091615 60
    0x5620121041001511920011800c010940c14186424000007002003002001e41d441612005802e403500c02e16181c0f1084502001208002c144200901294200d40040d1007180c12080c19180a480446c2440d920004903203807680540340d1080e403000784034524883d00e0408010742c9600ea0701e071409100b101041c000144852103840113403886146c4034a403481c280318060301140c500c0c0d0f101804607941d40825080800e12080100b8055401c1d500b04000320300c4000e442c1c5aa120000e400038400f1b064130140c545204150b500210f4125019520342003140000c40c424055080d030905550040d081c10060204101d00b181d04580041c0360100051800301e8441a10040e50741d040c840982080c42041912030b030945100f00506280403000020b0154025801c0c00d91000c3c6040b04d105280c28040c18100901c60b00b8003600488000b400160b080c005450101940c0d01004041c048050702ca144103850340c0c403414815140bc0b50108140d610492605a03c42242701002d0010000d950800341102540c1030001c1003 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 390598875 1250 390597625 390597637
    0x90105151e0307030b0c2706040b0d0b04050c07030e010804030c0201030507031104080a0c050a060813031b06020705150103050304090b03030405040e010b101718010207230c04020708 80
    0x38110640a450303039440030010032000c0c540081485c085440e0400000b012a031051399241e0000c224001c50000113101d4403400302e901500142803505040c10814032540725003100740c114468035211007890100b62101d203e080c0c01955183c0e2142d41e03401300360034043c002d072010316a01410886d4100c10040400d40c0036100c03104003542480d007c1220b4a82c014110040c002c000302e01ca520010000b00000c1e94000041c0c00c0401b1807103440500794107969041044440002e0b0b00c00c020100e100d02000520300b21030301030f070200072500ca8100104440d4050000140002e004001110040d500141d071a0a01004000c00f0501e81443c0003400340760760441d510140c89000310b102d0541301d59201d601d850525641801541d01a00d0042d004110240404400901070f00c08203c0d658000e4030f801c410710750090302c038090707040101c40300001007582e507140d9014040c51001c0400500c00c030740d5402d0080c6400991400050300e07400496521505040d112800f0850a020600402c14400ca104002c204000352a000075288 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 390600125 1250 390598875 390598909
    0x201020d03050705090901060519080606030a0905120403080909160e040f060e0f01032102190c1e0e07170604151a0a030b270619030b09010515 63
    0x245544a6501c02e84c0e05025041e400c5a0040c40e000002c25042d0340400500001c1280104465040e40203120540d0f01c00f00907510641c01000410001c0d10303000d1039400c00c12866100e40300300e03008000c9481c1828110f82090700100d40c01c180004a07201245844001c03d60072030780c3c168440307440100c2094003a240002402c4d04034001c80d15041ca440c0d0281c40c50340600010070312103841e2030162030322042065405000340412540e1008159200141c40803503c0e40b00410b44164006040800801a90311208542c0303c40c01c0341e03a050454000b141200130782c1240f080c07142041a25942c0076003880c881000044004040f0420001c074980c224019400c0441d6882c3c03c1042030f2000240c0406008400000384400d4000e00c101d014050b0660000d604410000c204088069408100d0144114104148840c000b800c0e054003801c800f6102041d030300302e00c45207a0440302c01441a101c0c040100c544d4502d0f04a503600a90f03400c0144c1e01044540d900a0142943c0b00744094000c0302e0a03141e1000240c51600e06111040d = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 390601375 1250 390600125 390600131
    0x1b09180603280210090f2d030302160e060d021c0209040305040f05060f0a2d122a050705010e071518030506010506090a03060231030201020d03 63
    0x40c015850070700200b120100040a501107401070b000482d0940540580704901039080704150050f4548590560303815108001d0780c0300e6400345013450215407080c000d000f0341e15400303100700010000f0140410520044d44660040c22003d030301000c90445040950b03000600c60040e2104108140e03030b82200014290380d04490304007240c01004488015080b04980c000e4100d80048240024160000007074400c840000890b10b24883e03d481c28401540204001201c50300402e02150110703078083c2d440301c00b40031094000803801640304483e800c15542c0b10049030b004191046003500803e00c1a02403900c9a1100d680344011030079809112540c00070540e0110b000b00301e404140101080400e4021b04510000c010888104e5503e0307803482180c082c0720b000908040f8007a0204400e0640350440c01c00101c07500080900b0f401da00e04018410683c1c13181d80540d0340700941640200014001d8405003c141c420340d035000201c4c024241200411150504034820007403035440701040140c1e800152050a4001c1380303404 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 390602625 1250 390601375 390601381
    0x60703150b040f0f06020a12030b0d0c0603020d06060206061507081b01060906060804050606120a02030105010e011403122b020d09032006130201170a02031b0918 71
    0x26410200c2074101041e1990001000034400e0072441a41c02500e00503c2190310240d6500c006031380d41c0764025001401881100198040940640d00042180320043c1c0034a0865900c3d540b550701910294101c1408a903002c03d845441c102c00e4400d54003d40700c5030005050f0f41c20700400251191030301054100d0060f000140c1e00c0204400780041d40c1540540001d101e10080e401c08606002c1c241034001c0c035403000e29000340040c035544201c0c1101d006581044c0502180e40b2a542070000308982108401140d10400d0065030040e1801d00c103a41c001d000744100349101c0d5040c68280350031500c2c0c6500c6d4601c00c2d402814441c000c90034100484040f83c4400d4038545c203007055404408010242d80c203209041910105054007103843c190050b04442e0f00c2075840c140c4010040407005100f0514012405203070303120400054503006003010404903540141401002440260b02c0c0006108040750305001c51a0044144248400305950860b010f200300b4915034100901c000104156149507004031420540070404 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 390603875 1250 390602625 390602651
    0x105121213050a060507061802011e1412150607030f1809020c0d0f030203010f122d03081e070f0e150901110a02100c03090e0103140d020f060703 64
    0x80d000051501500a51070f9650311940034110740c00030081501c07190b080c08600d1141a510031400c4107196816103a42000804200c43d072030740b40203a030503098144a405005406103ca00c40c01030540b54100713018980e40c903d005100c080d60020001c42c0310b030050100344800c10000390000c07030b80031003d00c151a043c04441e400c085c0001c0c041d40503502507030815200151740c0082002c049004c00c001d0070503803150100c50388400d0085007207100034854101c410504d40400e0002040090b50340c4010380c06650700011100d08145090f0100f801c0803200c0503411004400a810503800607800d5922610742485002c00646c03242e60729141c550001d02841c05c00c540c2c09070814280e801000010541900034140c80c0440360b100d074001003a030f40b0984013140405c01e411b03107400c05813400050207010240d01411140740c1300b80058054803100d030307907960880503c4650351010410980c1403009e01d0007140665070301401c2810355546607081c2800124036004640203204140850030340003558540242c01450001601000408 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 390605125 1250 390603875 390603907
    0x271b12200d060c0314101809060218030708010e07060e12010c0801081b0f10140f0904240308031801020408100c020313030209130506040b090601051212 67
    0x518076444045061071a06000065220209a241c0383c0c90402a14107600c0c1900e0040004a5041a45201d501c03428040040d1081c0b101180c181c00c1400840d0040d92543d406080c1c0c1c200318110103802480701c0655840c2d00d000c0004400070003d4030003c101000b10b02d00c3c403a40382d40c0140101000d02101050708401030325001d1004100e41003801c001c012000c0841801480710300c0078800c00c01b852144281e1084010100508102c42d49001400c03220303018111400d10a5514400c540ca40502048160304240040d03150003d00800d601c450200f84c0d641440d00c00c11080fa90100e0000d028140300c0c6241d2548200c0010324101a250410f510a48a91701c0008031020a00d80c0c03901c1600700c0d4004140080c4581000a01964840c80d20380244800e1f00200b2041340da0b805100c8800c181128400ac041016060043d80107030070101c080c40c201e115913110f80390280b4092050302e086414240304030822541000034400907000d8801101c0d003140d542801c140c805d82d030f10688000c1241da01c3d400541d90403082c003406 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 390606375 1250 390605125 390605183
    0x70b0402060d0504060603021e060403120c05031606111c09150c0c0c05010f170702010b040c08060103141005011103070c03050f01051501120c0201271b12 68
    0x2c00240000d00d050b103005400b80c0fa00f0312040380141030026a0340798a402c4000b407407044c2e0901404003428103155440e0141d890300c0442c1003c0a014504038a04080360040c0000c003010303141141420103000042c030b0482c1c101d420002c080c0c0d000403420300403082c1074020322038132511031a0032601c081080c2e4164140501c10030b1900c090314414500c0c0025405403650801003201c813313405145807409040c1d40300b0065618000110100001850140407000500c0c52032040e280c0048443c800040e00c41c1c10400400c040765006500314010a000900304070301907a243c004c40710004d5001001e40b85038180718549158080c0d860069504cc44282c4031fa0003201d500c01c00c107540030f2540010b0100a1170b503030385c1001500d403410080d00400e15400c0038000341c903201c040e0340d40c61940700c010380d01c890400a42e420003c00030b11100400301d00b103549621160302c2c451030324804c0d0360b0704240c1004000c08604481c542140d1200c9121a00b204034640d80c00c040200280600500c0c80d601c2d0002a40000c078580c040c52000e0541d095 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 390607625 1250 390606375 390606397
    0x102010b060417070504020901022107020402121807060806150904050f04050d03023f0c0d060608150118030b010b031e06030a060f0b0418030206011208070b040206 72
    0x2c10001007103960030700c00302c00c1101d000003994a8140c403030007032006a20802d400f0710b02690109201100c44541d43c4130b030343c0d010f0844000060900710310b98005000da80c40070700e91101a1000c48288071384002000040300301c0c00805001000481e242c9103001d844880000d1107240700d402040004011405070400b01c0d520024000c04c1040580b802d501403224400781950700352150711626030040c00b05c034064801c5540341200c5c40c10062644540e030301c040d81c0d501d600c0c0a18980d03102c4041080c08620b4401240640184506c402c141c4c0c41d44043c11380e40d030860340c050b84203000708200c0c0c400f800080e00094403a0b0800c12401c1ca480072098070032074a034045220303040c0d000408801c1e07034000000e00613481c1000f9502176004005034030241c0060b1140c0a002420507500d042d803540041d0080030010302d0030760082030402c42480c000701f0000c01000005045a07401031280c030107004401000c03030030583e05010040c094560564507440758020342e164070880c0c1c02031700001000100e03140045000c0d0365501064401e40011 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 390608875 1250 390607625 390607627
    0x7050301060f0f0e010b03010e180607090e070f05030118060b181302040b0306040f1503031e080f0414070306050705070c14011202130e0c0301080712020109140102010b06 75
    0x284501d8034041c440b052084600200180c0303400309042e030201ca00c10b0304a50060440e0341c02c59003800980700d00c0d80e0700070b440428a64100c1c0703c3c4840d9604103010301846044140c488400041c41d1000440c1c49510090058040020344501034131442d0f0080156030641c0d010b01c1402980c1d502da9841c21b001000d0b04e4004030310205010901444170441e040071070700000c1301541c000007140e0101c40a40c007640600c1c000c96003000d85c140700243c07050529501405118511000c04117055940c0e0140070300d0703550541c00030b5000071644501c40c05d002c4000c402010507034410745001d00c128509000c126000a8001d0030051000c0360741103642c000c4001c100b080c0409150044002c1002d414099000340640c0e025100c21030f2107805980000801305180c01d65030944c140103840d11400d08010207070700070081d030002100902d080e0300701101040c10203058040e18030a580003810142c0c0c95040c4410940780c00e08541c40b4138454030f46452145c0060364841640000c40d110254400d55102c01080141d003d4480601800e801142c = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 390610125 1250 390608875 390608879
    0x1a1209030a0e06090906010f0e0613080606030712141f0e15070e060f1201032f0f0907020f1c17101502250e01140108180705030106 58
    0x18000c0001d065a01c1e1036120444210031950034070020b4094002d281d6840103900000030403a5000c0ca003101d90860b0b0503d400c0200340b80c481d0016200d074004034070318014074403808000d201400c4d00700319007600f01030102c00904203285001c410310810500e00c80c00500880700c082a03d148441c080065182000d014001d005609007885444001400321490504c0580300b40940420041941000c2501078456076135688421416a414013440750b001d60b03c0d0440c0310300b0402039040020b010301c12040c007840c0b027034804103100900a1141d038554800b550790002c9418000d1511803c0c0da80341500b00351400c01c1901d22601c1542c62003801d03818440d00e803040762024003410241411310300c000850b0500c0e00d030907a00c5d10590500059500420848225943c040204086a043c0214005071001c03410b094003030f1044640d208056038152150341002010040c1ca50b944100a02c501c1c2c0c0304040c854054030750000203544944441c00005e0264101609807900c16902032400c5c07043d010180030010140802600078040e1075 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 390611375 1250 390610125 390610141
    0xb070212060a051929220c080610080a0b0607051e0d0203250804030206040b0306030706051603120605030f1501060e1f1701091b030b0102071a12 64
    0xf00c2122001d1905456160b40e1080f00b031148a408803052034202ea892000c085203154111410409070b05c0d41d80b01ea060510507403c189003020075448204000d40124140a003803101070002a00500000d104030b07200300620b4041035110000c1544400b0400340802d01d01083d50200d550740c890400040c0ca28007500c5020001d1b01d0100c3e10482c10421400b08403192180703504800c0382c481c0224081445c000c0c211024180400703040301d00e075080c51400350301c20320314250741e80c1c1c0041c426601070742c081c05c0c40050110400800345000d1080b0b500030320441c140589040400d07a035002c111021100020f003401180280b210100c08207034000c3d005000d02800b101c564101d00a4000c5d130321511214980d00d607490705400855142d108018044035064041c00000e45940602103501a55070328210910801c06d440d08100c04007600e42c04e407103008055803c00045c616074102000942c1c4051030015200741030034024082d10590740002c0b580c00b214021107013075150b0844038907040140c2c440e0800a00d49100c3c14002e01140d1 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 390612625 1250 390611375 390611381
    0x30206040b0a060f030201051e0c060703140c0403061a0a06210902032e05041103010f0c05030109020a0219030206060316050d060c050c010905060109180209010b070212060a 76
    0x3140114554050360391070030090016542140524070031500080010030065001e81d000d01207282c3c6c0f4849902c0d81e2912140c5250494110b0380c1604480d511102c02e0028190f05841002501d00c0c207078107401c20a140c01e4400b00180d108911004200ca541e80340d05c001b0f82c4500c8403248a59103c0140200085541c0b16001803800300a02422105404081803010390301c15144620710100d81d01130054401a10141c40030046120681c400c900c2d043c24904070070340c030814140f16582c4203034803500414245c400784406260031188144000740c810b40c50300b80c0e0201c0e0f850b0440c00f980d04584100c1c01c096510030704a04100e0600e5a5134038003161410000310004c04150300861181d00c43c5600368100c981c2c1c200c014000514500d018130074280c00c80c2d030030f108000100c0c0e403540000b202208141130440c9444020110282182c220880070f0f03865402c1a401840000100e00900c0c0b40001c0321038102001ca011500003800514061041e204503003400101c0000715214840d0340032240224000361180303490008000e00c05 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 390613875 1250 390612625 390612631
    0xc02010c0314130b1009050f010e0703020c0705060c030d02070606030210081b03070c05100609050604020a051c140c07060605120a02090405070b2701020d0c0f0618030206 75
    0x400d003491901d10066040c00e4016200d202c0f030000784050b15401e0f071142011120050040304031541c1c0c040000c20306800c2c9001e594042c00c140d000d030410a614001004110000c0500b00030304042c01000b5400103001c00041001c25075a080761002e95444249800b01e2951041c0342c1c003c0c80860020520400b40032a40d400207040f030340281d0302c030755000100341c2c402c9400c107030b0444141400c0051240200c4081c001400034640c0408681040b9040e2461521418a850301320805100c8207515a00148142030450244907013040c001e86055040584116001d0202c0c01407081044e800380b0040c06910882c0c2440d000b4541c0800010015201d07070802c54400e40c1c8943c0032030070a482a0b07041c0307100000d103030034400c0d01c03211141e15080c0500903210080d0f080081403400500103440500ca220f5000c00c410300984000c0040c29000000c0045000d045c00c61000300ca250003000b035040d034020400821b031058000112524040d1701c0494640c503c10140b800d0402042d41040c014090752014420000b003540029400340 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 390615125 1250 390613875 390613877
    0x31e01050f400c18140307050d05010c0306080d051204060f02030103050f120a050301180f0509010c0e090618070c170403150603050c060703020a0b04050105010518040c1203120c02010c 81
    0x1042d0740a0964011002060b904c3c8004200034040090440c0e54200c22018a8000c068075515580c91000983c0825020f0041e180303a5903d099044480c0c5e014440d440080669401400c10131120b4070300900540a840d01c0921005180c80016042080340d40c0800d0b500b49200d40119142d586908200b580c2d42007200c3c900000303124480229005c4114501a030302c3e03128699440905d1603003041c102500d643e0f4804a9403140c01c4c0c0b2171041d900c0300b400f54098244a00302c003a000080300210442d0007413441030705e4902140205420400c0c81511389a00d007420481a841c0f2032a48095121640304840c4c11190040140459043d10071058120a503000200100c1b40241c1e006120441c168030300c0c6080710078034803008007642d0215070340c0e0b003960034000040c044081c06030054035150601901c8144610704103c904944d05c0c1d541b000140020310b07183d21403040c05889820001210300d03103a525454068072901442c0030120008003610201841604600440d14080c0130030702c0400740c080c2c0d0183c040c058090b2580 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 390616375 1250 390615125 390615131
    0x606090816080606040c0509040603031107050604051302090d2f010f0903060513060504050105070212070b1311040e0c0a12020a0306020d060f030503031e01050f40 72
    0xc0141c4080741604169020301c400741c110740d11040c0130040100300c1c800207038041c0704e4144007a01c1107079260721030380c401140a61180c041258217058403d0520903150402e911800c0180014811929003205c0c04a503400e03400b0006a9942c0c0ea0030000c0c65190080900401501028400d1507102e0b204000b51000714000b40c4000b404d94002c10300549401c3c0036440c60f800000c07410300080022800319042150003c0c00b2605891020300701c3d44a0f142541e20032101507d21740e443c1c0c0140142c0b1581000103c034044841c3c41e050f428185265500400620301500342c0c071040001e20540c50500010901207900c2071402042000229081009980c0311402a42c500c1d225610581d0f0010304100602179200e40c0c55402030103046124115900d55009401080311001d40d6566620045089420b2110344c1000d9030003100110340b80e14003200000042d01003488690310003907012004100c183c480c1e0034001000030003140c00c804890002d80004282607100100d180080e043c42414804a0242d1254100d60300f0b0b4a02043c = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 390617625 1250 390616375 390616393
    0x92701020703031d06040f0606150302040f0504111222120f080c12090a050307050f010c0e09131718130219120608030f03011d01061e110106060908 65
    0x11a0144040b1308199046403ca40300050024484080229405108601c00a100c1d0744801a03113405000039051400032a074000760030b00101000e50b0300c00c401403400300d03418001d804002d080c01e801c07400340520700100c01c403086010482540c50315005400c0c0081038410300c48562803d08000035420208000b202c0403503400540111154881e00740f5920512400b08202e2400c0e04604407031604013401007080220307025403043c07400011003c0c0020140a80950001c4ca8406080d4a8507421103086004440a1150400c60b02d40035860380107070284d201035010084c06040c100ea00300701c50118825006c00e0721440c00010720060016006450700c0280105540314034107400400c42c00c0c0d0483c40749528444140901001c9480740a209040c04108001120030111304241d54500c3c1600d540c110382d2103c0c603c5000480148421350954080c09018001e140b52100103515100380682000c1e0070044400110050800f0007482e24041c1d82620008069100200107940c1e50701002068201c40d0300803000f0354080d003491 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 390618875 1250 390617625 390617651
    0x50a1b0f0923090f01030209060d0303110403050a050607030615050f0909090d03140405060412120212250804060f090c030503040501030b01020f1c11150403110d050909270102070303 80
    0x104c20b060341e6015000402c50b40b9040c04000c40000e00c03600071020036403036107110424600034002410003144110002c08a041d807915007a4104000242007004251400e03604006d0300703079071040c1559a4541824141e0b610017540405141ca4800c148400342c00c8035258090002d0701400284040203002180c3d0100310911103c2c401d800040d00590380030b0681d40c08400418041181801c1b900303410700160a04a42881c51040500c050b0b0304400013140300da1801c2d0f403c10001811803003211900703015081410340900c0502c00c010309040000782000d0041c5648008141c4141c906030701c00304000d600210342c2c02c03d0340c1d600c2c6015643c0394040d0144a0000c1d0514800a19550000500c00d04c100e1440000e000c00204484e4030a04002820b5281010858005131080480b202070100c4180c0728840308280c9458685401c0c040c101c0840b921070912181d01000400391996403080540310407110450b940382c1d00c0d490f100c0b4609901841c0514000c91019000071150742030324154014400c2d94441e1300c09000c4500100d00c = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 390620125 1250 390618875 390618901
    0xf04091b0207081f2d06030506060f010221131418010e18030904020a020109050c010809030a08040c03050d0c0b0a0b09071206030b090709050a1b0f092309 68
    0x1045201c030fa900240340c50b0b0031480740c10030814103654121644c0c041500c0c0806013007520880550b14041795030b450051041c030000780440390384040180ca000403800030030f000003980ea23050b00314040710100002c0c002408291a0380203d07000901079800e84107990703840d500190b60003124591800d1041200b0032075941000c0c2e0030300500d8101c84032229411950381d60054001012405028031902da40402c02c188055079032103101421039800c842e800040c0e40001c51802a142c4010314011905101c6501c0c20044c0d005000802c41d5099001c92800400c66101c030301d403030040e01031150402403803801500c0f01905450741c01034213500d084d401000c2207401c54465900c213100f2207800c00d801c590060320000c00a2401ba002e0b00300d4148841864400181d1a41d880d1580001c034142aa151400381c1c105880402034828180143d40c3c0103500d820080250840b26002e800c112034010044900b84814405030b5480c0c10700415689004108035034450050300d0f01c0304665202011016542c0d403182101001180080078441 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 390621375 1250 390620125 390620143
    0xf070f080a02150d020706061d06030c030706030e0a06020c010c1d0a23090705031501081e06010c12020106030312140a020c0f0f0c0103140c030103080f04091b020708 73
    0x600401c001040d05143d002d040d511030780100b200340c0d17001c20660740040d00c0e9205100c01080b142d484015161036444107800d61f04009002684254483e054a2032580e4000c5240307405c555146c20300240800740e407081c5030700300780c10840050400c901c040f9461120420640004c0e611703100a64801c40d1200111011058240b003085103181c011802d540184105006045000612041000005201c0794000c0002c0c03515042110503200013503012003400030080320b45403140c090600908000e03030381d8504445000e800c1d81d41070031a03074010308840022a100364040c0500b030034403a8110458440840c95004042c2c043e152902c011800100d05a03440103540b007441c03150220381902019010001d4272003907000030203074000e8112a40103018001c95856103c8003080382c101a00f00510150801c00700700e0b000901100c16006484c880419603000304000e5141300c1040344e040d20b074040032007625200d51121031140380c000e941100c81c071280b4120340751041c005100c4183c190855660700b1213100702e40700c0004a071120f0000e = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 390622625 1250 390621375 390621379
    0x80f0c0712030c03050f04030609030c0308130809040b040b1305150402030c0d111902010b150c030403120903021503040528020f06090402040b040810060303080c0304030207080f070f080a02 83
    0x725034140041e100360002d2803006c40c80507545080c1a16074a40394103c9070031401c104c02141c0055141c030201038000c0b0b442c44d4031036540050040c40340010344030b0080303a01c92603280754401d580d9907070720003540c2e55543d014280e28034019140e0790030700e00b00368110001080140e50903403840022201954152500d40205c1e131244007600c0c0441d08180300b419001c1c000e0000d00c3c090b000c5e100c509101d4214012200c1c9180c2103c06200e030b0001c41c07020003020902058510103200c801118a042042c032a0b21440001240c00302d0758041d0108111291b0584200c0c3c140007590400ae501104403000d04841086c1c1801460040d80145d040d0360b4442082c001c041c00c00380c00c14803001000c00c01c40d01e0200c054680200b8080220801170042450702841d103000400300d0b40903402403068001c3c04142480700f581c04100007000303e140120100110783c216100940185001061203076280301c00400102050310a002040080065000319040311401403181a1214000d0141d04601b0f6101000045d403240e0000344100c4090300 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 390623875 1250 390622625 390622637
    0x11030f040306090c18021b070b04050d2a0510020615060904020c060705030117012c010b03100f0b0102150a0905070e1e091b1c080f0c071203 62
    0x80c50342c8540141410f101c0665070a089050000307800d103104010310341d5540d6207180059441502c244512816100b030f40d1903401039800845c0a1025078a68001c4405480b421511505044030900d00b41d1142110700c0e0140b05004000b00300a00c0545c2003081240603a18111545804403200680403660b9503c1242c0d0420005980ea400d00024203001c0000c080502c00903101510f44025405a60300e40942a142e450008000000400c13101c4d94400d42180c2d500901c800a10140c280c1c2044503440d04141070b01d00c03185a0200b441d050020409510241540c84040d05036a840350035215804001d04003810002043d600307050380c1000562010a14224540321320701e0104094441055000c01064a200221120f120305040450444895446c903882903055004c10220060140e48441d0a0800074062100d03d43c800a12030048a400c0c04401c0c20517002030b11401e15051650752546032102420703c01030803402c000561007000d614160020124445010211019155181c800e5865815942c1004e400190 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 390625125 1250 390623875 390623879
    0x60a06030e030702030303090a05160b0306040c05160506070908010c05030406091a13030f0f050a1404090c081e1b070c170d1e0210020309070f1511030f04 68
    0x2019038044903810600d40c0440f401c0c5100c40d40401e245130b1040d04c5144995000403101020005e040000c200d0760680c0052006016140200c2c0c07018134040500018422601c0340488444684500190b894102c11200342003440a410b041458070754070242c8501000500d00e0b900883c5030803050003141600041940d13420314540d1581ca96000810001d0300407205c0c2d1298104c000e04914240017280d014502041d01051103003500d00d00030380408008a0008144556403254204031a041010380d20f20340000c0c10708072140841c0002c115810b1140303800c0100104d20340441810201d40c08980f1b148501c1040c1119242d4400402c084020f020301210800d024040310802e4021941d00080030f0305409100d200c03210962511000701031500440013000c51220f44c00008406030f207a40c041054400c0d60058070044e07041b40001e0000030340781c05003041e208200c1600000850942c1e80d04000d0700f80180102c40340350030b81c13175120b01700c542041e201880380d10f000030701d08003031f03000d4400340401191030350035480182c940740034 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 390626375 1250 390625125 390625127
    0xe130e0d120f0e0d03180c05190b0c0718110406050706021e030a0c08090c0d21180e0c03010e0a090f05100c02062a0403080a031e05060a06 61
    0x40256640c1c0c4544400360700b681d044890050590501110014044031001c0c0100201103a0603c1055401e0740c0e030400c44040032030004252102a10710a584051058a400b81e800c8005102039000b901c121000040d90b010001001ca00c40044e1174208407148080308001c24604e0640b10802ca4491003c00200401c20046002d1801007210511600c809810000036105c030003080b4601c1504404105400010800404428884c8840c3d0b00f54030300b401501402c0103034039242d550040c450014000c503000140c03d010301c01d003040351780256110780c1c403240c00c400496000100020b0001c02540200c02d01e40e40007141d06454030700c0c0d036441800100c1ca144c1c2182c4c40c040150360788001c050441c3c01c41a60710b02101002c25110401c120005010f4401088604500c400e4441140c103003520007011034200c1420310034440900c40a0001070b5025170240c170402109191024024070460340300030840d4200051158186805802c50071000e1003680700324044211030786900d0155901207500d07035440904072030240009 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 390627625 1250 390626375 390626387
    0x51605010207080619020915160b1e01090506191508090d0c0204091106070b10061715030f06070c0618030f0c080d0e01091103011104170c0904030e130e0d 68
    0x200b10000d11001c1c8419004007800c240390300c04032446e0f002800740d4249c441805081e10710303507800c254940b210360109141e000240700141018003562802640354004515166a1400511406a0750702c00d01c5074100d9480c00d045600d10740e8015500e0201e0b900000041d541d04001c00c00a0300106941c0700c0200c6c1040319400c2000a0100b0038084130106c811951018003500c425003e04880b41c031a01881410b42003a9401d541d007640ca40d40904208446030070f0310150040300205c3c1036000701041e06000f8a035000000000d0501c40b500f400c1141c18415802004001d03940659038011140c02003608010f031481c0070554a00e048140301000e00032070065495900054031441340030300c040740594029030400008100304000da4944482c141c0543e91207103950020f0000b12440c2003142a4128020001e9820020140d1046e019610a072200a08040141c1120400920503000d038a8001040000349180916001e00380a002e10390640c02541803002c40c85440e05940b00301c6508603203501c001d120802e21118100ca103 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 390628875 1250 390627625 390627637
    0xd05090a0b0d020f0307080601021b100302070c091b1206060c08030901141006090504200c070b1308010507020a2604090c0905031005010b0f030603030705160501020708061902 77
    0x1c50b9038204a05821500c618000d140a040950340e00140340c00d03d00300082c90715201b49d41b80392400302c0c0034060300309039542e640410720002094200540c8440c3c040c242101428241c6d803165958600300001ca40603d5041a03542c913260b074864442404100344d400848089075014000c21000c07a84100d8640f010070494000745522000402c0082040d0081e034a2032041340b0300503180020311204c0c0c29018492a0b4200709940b02408040d10f0800900341da0700101601c1c038400b50004804444000b030150744650b0240b0441005e400c403009142e0390b034810004101249041407054844a510b0107000c120250b00c0420002c61194025020301c10401c004101c480c1024003c071040045804204000030700e01c81d40b03002d4007041d08155200d640c05d0034075210505041520a40314040c2140c9002d0060061141c10015111040c508111103500c0e0390f60707400841c1c40e43c0309605000e0218400c0d045a0902d0f0034200840c10140c175002c3c2d0079038100701e80d1161180d55407207050302d01e07400d807410074545402900c0650717000d880 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 390630125 1250 390628875 390628897
    0x30402060c1c02030301050102121c09080d060e060906010c020306040201030b190803040e06030d3207050a0507050402090303041e0f0906050103051803030402010c0201030e010e0109050d05090a0b 86
    0x10800b08030b8150080d242408140d4000358001100402c0b803503070107014001050101d11320813454000341c10480003260150641e180015907950f00030f00706100b40582902c0c0394102682d41044225242d111031400000200c602c1031090681e200011800e5100e100c0c0d50f0703100303607000d07004140301c0d01c40342c0c0158013070000c0980b5140c00c000e1000030131003440310300041440105404009159100e003440c481c0c101007280101031601903402460742c5201d182d4000110340700f480e0340a840c407040501c1c807141e40b21180740402d94100c0c1e079007000c6082c00a001003c540c0c02038951041d01107402c410340c0c401c140000d9019139101d459240d001440b08000302241c0140b40c504096041c00080364a5071240001000d68050b508990801962100c1c2484296010702c0b403180c1010004594110045185511980d24400104020b0400591041210440e402900507110810000000384010004031641c3d5000705084074065030749100d0925801e003070b507001e0f10490391002005407550344035606101e000003495201e032a80d50 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 390631375 1250 390630125 390630133
    0x5030319021e0c01060807080a06020a020c0904060c030f0c0504050409050c0d0f031404150e1f0c1703040c0b0c2508060f0f06040905030d020711010809060c030402060c 74
    0x101440041106042002c40791001d860300c04040741c2c203085451681080031340e5803101c8405c0c030110382c00107003466203103030b01400151f0351f100c400004074180300c0d218000c0354210180764180400c01059400c40b07100310b0515902000070200b149210b44c00d81e0110507505001c41e0007080240310300d08194008100c028026400c55240894070800f240ca005001b450a451302500d500100303040607804100304031a6501c00c030100307040504094a13154a03e080801c00d40c14824003540c45d103000d0300c0e10360b2195080001c01c002280424118600a04210150718080340c00d400784040e00a440c150761019607005d84d4200c08885078050400c060900d0a602c10340c200d00681c41211604c00703403240710360181d00904440c00311012840b480e151109240034000b4101c1924508400c04000901400b0b5034003075408841110041056045420154214860a00035407003460000030800144200e0000c1500c41103400c1c1d032034419907924540794030f1711107000f030751035a10702d40003040410f0161424038060030640704410251 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 390632625 1250 390631375 390631387
    0x105150d030221071208040203060c0a1707050c12040b12040f060207050c0f040b0d030f0c0602071109010605070818150c1015030201020a021201020c03121005010c0503031902 77
    0x80d110050040b48510181c0d100003080d5080100d5400c82c284a90000c2c1480c0c1b6450074030b50300090706d0300e000504140d03203040d01299100c2d1440c4101c8082000a41c10750305043e19040c4018000c0c0158071407003103440284210403501d40c031080d4950449007100c80780d4403500d04006025107001d00c550740c040c00a40700b00b1761613504030020624074801004014410300c000c2219000700403e2241202e4201d018a110742c0c60420b080205480c0d03041441c84403030341464500680c10301c061040d14400803041004d00301900c049030540810504030420072000c0000c13030b0b00340c0d080da0340e07070b4000c40b036521446100070000c40082c488150301055114040040c200000c0c039855070101c0750ba02060840d00014500003107907000c03260500e0090204d2040b680344210416059118500b0340e00041c1d60b4000081d802401014900c1c803001c8560020b505944006031114240c81d5030f4003094000e5500080151360703a000b000d07000d0000149075806482c0030729a15902001440c1941d44440c11607610991500802110540070400 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 390633875 1250 390632625 390632653
    0x260105090a1d010e060a14040f0c1211040b030d020a15020928050109050307030308061201050103030906110706120207020a0302030d05131e030206030703150b0d0e0105150d0302 78
    0x300744200e40c042c80001090b00c0c0456019240030009048800013600e04185400720303a032940099036000fa0810400028504140b400044012070303a441b0b02c960320003542e09441000032868010070b075410100c03818044081d20350101034460044003012405a882000048005035480c1c4400c061965030300c00050400c5081c00100c0c8141c0c050500000d052000480e0740c50b166007986051b803000d05820f2078400c03005800e1002007a5600424000a010b000303009000981554031001e407040044e032040000e00c4203582d6840d014010340707601e001702c2c80031840d0040b81400420780000d00038205c4400d942ca260500c90b01c0800303100290300190050342c0015480308080b0140c0c400300b0448405c892999202c56441c07a80c801c0044c0c0b2404960002080500030702000e040b0083c04070013050a694040307400d280d42e40c607490390075401000c2520340350301c00014060001540d0038505015041e942064081480715811200c1032a00302c51003100c1640180a00c4078208103241800b03050b010910344207004440480e104890 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 390635125 1250 390633875 390633911
    0xc11030303190509010608070b0d06030f0f05060c0901050403031d0a03141902060702010315030b0c040302040f05090a150e0601080a060b030319080a0b0603130201260105090a 77
    0x2c5000303401058802180031004644591079011041c070000708003007410903200603180d083d10310585028007008a00350601c0c409540c460001154000d4000c1041c185c640741028041d03e8503c42550940101e600245001c00220120307500048165540b0340340909650342a108000ac08254881d0452070048000741a11606160710185007c0e400c440c80e40c05c2900310103807a0001c1c025801380781c40e080c400e407000103031141001e50f21182e82c2403d000c266107454a540c503000007801e9102401564185061046040d0410f00420a60f0700944040c41003030340703164100d82996005c0d180b143c0580d100d40590008554410316070908400160008900e00c5140000c440c50110300f070b00b0100186d000201082e041100c1c034440d40b83c104006070051820481b0300c03000000085500e548210502c002880090300d510180c1d0312562007200001c0c90252030b0700b4003240c48142070200d220308a010a0b8440d280b45000004241000d212040b07030f802c00d010581c200014040d880402407c00c16a0a4568449164014200b0 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 390636375 1250 390635125 390635131
    0x90a020d0c02160803040815060f03100c1229060d02040303110d02061e07090e0705070204060f12200301050910060608060f010302130e0a090501140c03070c11030303 73
    0x64000c059040b02c0c00c803218011150366012403505ea00400c000c00481c1000304050391610041240c020740d0340c0e00c01021410b01008a440d080c1c0c5030040e0754030005030401a0303211100c03506036580c42610050100785000119145001200b810211a0844081a100804400d459a00e01810090800c0e80c0d0182c000284c0c1c01a03001100881d008800300c007071064040001902100461000b0085805d1284240e00c1651000402100644c800070019505e40d0041e288074008248114607226140b60044000300a41c1049004078466820a8000544013410a81070019600e0030260219040d034140d0703030b503a24900c589900042250f025600c4081b44d90b028414540320710076200240000c00b12200090003110708540000b0140403a41091014075142c1c070009180d03000c020300300160389050503c45a00003c000b581f00050140681c1c04206c0e0400c0640c00c881035041c42840203000000f40c66032000b83c0007104a40f0703464074540601c000b0b607416102c0d09141d032902e40501d0703140202441c410042411a4011 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 390637625 1250 390636375 390636377
    0x12030a06051201021201030308040503040f090608010c02070311011b1a040512070506040206030a090606081b0109050303030c0f041d041a060306062103130f0501080f06090a020d0c 79
    0x180c50070003060804044078240b01408200861420000031032071000c404040c08050100300c811000103042000400407030380130340003210703890807115039480c42c4070301420047c01404255400c081000200b14000240304003078a50000c0c040c00030070040001180d24144a40641001440c404c2c090000324100b1000e180322440036038080311242c07a050500340c0c0360101034540c103007808008000c90310114002040c40341d045941160f08aa407a01c9843e01740c409003203900d901916482c41d0a100080e684000604c00d210013103009040a1040021001503031a070b402449100d8054000f0000250a2104500280007281c204000c00782041d882d100c0c1c1090844682c0d0308140c14100e403a0070b203c280301c01c030200e140805c1e01110b0070481d1490030b00301080d11400054402e60050060000001ca01c4010150601d041070300761045a450302c01280d00446440a80d200d04140442c1400010500b948511304c41842050003100002ca161903103818030401420041091a03d160b09000341101c140c100d0050610751005 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 390638875 1250 390637625 390637631
    0x609050403021204150e060f0a0e0a050301092006040e070504030b150616020f12060a060806060d030c03170103230102090d0b1b030c040f0602060103110d0512030a 72
    0x5103400ba20740031a010f900d9944007030501c01009040d80d28000035109011034609503848007044c40108a00e40501c42d41e00f041c110010481c041c5855012505500d1030508030f0704488140e07030304c00900d4201c0c2e4100340080d04611066003104049200b10701900a080005090549815603610131400c1002040c0c0320306000071400a420014000d81c400703aa608a00d900e800701c2c0d03041141200081c2e0f54407460144810383e8040c1c00c0380406541e035542da44900881301800810030701c00892030242e00c80d14111040c00c0410314020001c103a882c000144d1038460b450107070018000d07182d03584043c2c034040f20a900841c00c000f01076042d4180c0c0d4aa80071114006d500c15146091242c9400ea40829024540230824003070360310500200540369640703100814600d41141d0b0307805468444642c0c1c4400d0070400b46e00c0d500c5502c400002e104c020010b2030000c0003107403000c19402d4009500d03614201e03203424003880302504400c441c0001428a240040502e103c940c422000c030707243e0081c11003500714240c000f00c40411007156 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 390640125 1250 390638875 390638881
    0x90b01080723041a03030f04051201020313030c051f02030411120601120206041a0a021b032e0e0304080d05030408030a0c09120620070c090f0f060905 66
    0xd0200001e5024100c021502e030003818046140781e0008540c4105280b007951901c0d503600c2030980006007242c0e48540030b402d4a42d101d9031015100036907403240c407076640210600c059152012606100b640e0003004889040401e5000d1030710102c40c41c240450068820f4028843c1d11040c468003c28184980080c008000d40c880c03415050a0081880d49410603010380b6180c290014035200124006041d200e03c40807032100c5c1c4090740089074040c001c680000caa19510220b2241c0d20303034149805071035000007a03800c9841c210083d181034240301c1e1070501141e826600c120140758150341c0d41d02031070740b81c5104200742131440488440d041007619881c41c0c03902101c1c2c100003828012850f0910024042c400142441480c40c00e0540c0c8a81103840700410301c0b85400d546030364100c02c80d841608290000d2001d60641c417220f10141c1454001003200030031650b0596061003000399448444000d4030712040d00880c08007000c528200120303001c0d24071400c0320940544c0c3c54982c0c4490081c14401c0720040e0500040001c1d00c0e00d = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 390641375 1250 390640125 390640139
    0xd050a051501020d140a051c14090a0b01060309020423010f06110c060f090306010b04090c0e031e19150506060702030a17040902070f0b01050910090902030a06090b01 73
    0x481e001407050454002588440f08542c0002a10038540c0782d0010540e17940f5088030742100c0c0c900800300d210211641d40c5207607034000d03403040d0414a40c034442c0941130506c0340c46180082c1d640360440440103104106900c010051240298031403289180050000b2410100c2141d0704034084000c20300d8641c000c09140018095504500440000f4180c01d05000ea90f40c90504602c1d030381d41025000087c82010001613a210035098007080d45e1227130740090119613039561940001c08094000307010700360404e8a0701099003080340c4038040611891a004d0041c00340c6600c0441740c80c2d40a4018148941a4811060074020788501c1d460310665850049142030745c1507000d265004160760700070340168480c800c24070514016a4010801508a40c0d110758540d0411103080408080d46c05154040c00b030191020882c20248554a10346041103881740c1c6464000e60303290307400c001c0c030000240c455055151489005103d650031075413140000c1030009040301c4c4500b6069561900391a61078404071781c0900e000004002203 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 390642625 1250 390641375 390641401
    0x3080901050603210403051c030b060f090d02040b13091e11090717010b04080120030a02090a0b0309011b0c02090f0624041d04050706050703050d050a05 67
    0x46000800244014242440002d6407040b07440103003000a000c1180444810b0102c804513001154000181d620007181000c0da92a1030100d1081440400d08041d21440381e4540304044a035400d03100000d66043c500c509040c030039000040c0f41c00300d030450703a600c03803515855680700000500584003c00200e1718807144d1800f00300303000310100320104802100240c11700040c45a0b141074a110801e603a040341a6030340160490701485003081c0200f200c004035002003071200b291b0340148191003001000341700c00c0080000380550f104c1c01080c21185c000003800407400e00308180d00144010400180340d040400d0319040c2214060740140d503a124a69955030079000e4001102c01d0603d40100607050009440030741da008203500d4140101103001c0e0318540e0700050b20680d40c41945400d291319001600c101c0d40109010781100343c1c00750281b405a400d42740c2010000440724540781e0b1146038020082c0c02c1c002e14002090f117041c6c020441c01c5043c04000e000c8580031386030b1741c45014070802c4170000c081010300f04042103081d4 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 390643875 1250 390642625 390642631
    0x1091113090203060109021303061a1f0e060a2f07080f0a03120905030304060f0e0a020a120c030b040605040314091f020309040e0c150412080708070b01030f0308 71
    0x109401d088410000d0380d07010808504451207100d01507038074007412003038429206050300020415480e00c0c0600440000c9180342d180b04007000d40346803841540d42c68081c0e01e00c4050502c0c940000e0b10030841c1204605084000e010f0f809001d041c200c828000708401030b0780d1200c203030f01c1c45840020345040c03d15010008000d07035001000c010010b03124200310280c040c0e0b01c0300480300f0040c0c103010b1222381c070600404440e0301018881e07400c58183c94a9007401d1400802501c12081d060823010306003170726030015400c042489481144d0003021510454500b506a0920320402803059032000445000000420521250b05100c0d034130a1400092615181c45d000c0c202d64442d0402504541040c40710106039161270f52407800e40c2c80b0b481446400c24903480e00880c95030bc44c0684098106082000385410f2410018813018501c0007220314040352a06510f1a003c035010314820605c0c0c2407a04000306010800f034800030f082283c082c0200070302d001295121202e941900707078411200a402802c4620903d94880d034004d030 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 390645125 1250 390643875 390643909
    0x110a0309060c03020a1d0f10020a03020721060e010e010203011203020f010204050d08070203010e100b010201050f07080708180111030108060f012306090d0302211c050c0c010911 78
    0x104101c0319441c0100703c200c4102014501c040d000040c030500d40c0d030764001f503145e2903001001400302d00c009a400039240d0712840c00032401341c0b05003500420484140c3c10041c3c810012089007a240118540381c41010b0551450001d2081d580c4611040041c07800b030000b54060b0400c000c02d00401a03140c03030020b24092180c81120748a901c10301040c03020340d4890720400801e940081d50755403680080c3c00000d004221030030b271400407482041c403022189030054028a540380c03001d030000c12140e40c0e03d0043c0c4101070012074014000403d100e00141c4c40c94058000c10340c003c14583e0003240182c001c20300050031550f0500c43d11880720004001004001810000b0982c00220045505c0c0107514182081d031320845d0207034102081d40903010804440303403902d4056035421740d40103082041c3da8405003006074882c2500070802a40c522001d40c101540494203084400c0c0c0415804022400c2c3d042d00801c0000b0080508105031510b000c0150701d0400d50300340181202a40200c0b805a501044841005405550441020 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 390646375 1250 390645125 390645127
    0x60f0509030c0f032a1206130602130e0118180203070611030f16031704080306010804030e040c020d111204140f03060103060501030506060108042004110a0309060c0302 74
    0xc0c08940740451101d8a0000a032a00d0076200500303400241000d507624281000460200090740c025125402c2180780c3d802c0c1a01d1001104014440e015156003044511030b900880c808201030000303003c2d50051412150403908001d03500d846103680049a0400e80c041612407241c0066802805420b100300c020115a0b48843c08043c03a0035808243c8950381407040c41d09118400c0c0b40341018003c18400ca40300c00d040e0760306082e510500342450410803480710006400081042e01200e042d1a03190f00e03250301690b0080c3c01c40c0d04598442004554141008000710100441e101c440e1146480c0d81c02800040f8599030040e003009144500e0080c10b1815048410aa5a01001c02d00803031002107000c40c0d06599104580c450040042c0e404030b20f00007841a0072036050300c9850000010f0001603802241601e106905071860340d110040111000e200a0ba405400c90036800a8207000004841400c0600c035000341012815001c50001500e20788c0180040c500800d0b10b40d001b42080000c548188065590740b0b003011 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 390647482 1107 390646375 390646387
    0x115022d0a03180608040f06020904020909070305061e1012020906040e011e0f0e090a020a170705030303330603070c020f030703030e040908040509040309060f05 71
    0x2080f021601d007010100740702e40300d03010b481d0056410041f120062601c90301d646009511004109030300541c200814801c07910740422440c80ba01054400080034602081071080d14060000e150b9900324555060300003036614503401605107589454030f021466902060302d002071180044069002c500481d00190740c11582408030706903002100106080c2c4415217444a4841d1180034409102c00312390f07400d0000e4414151400e034000018021030b046141c0c5600498002101c54000018007400c5120741101d010b07041203500c009042c10b5004501c1c61804180450042c200c00b01c0001103040c000e140078510341080000d800032220f00811443c0e6905090030301800500110700101d01540751031800d8100b0303140c003180d603c00312030700b5448a000b0f03140203004000092070984c0c41160301c00410300000c83c5580f92058998481d1b44203484001c03a607420400050a42086000b624003005030811032 = true := by decide +kernel

theorem cover : BRFrame.Cov 390467625 390647482 := by
  have h0 := BRFrame.cov_init 390467625
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390467625 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390467625 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390467625 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390467625 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390467625 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390467625 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390467625 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390467625 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390467625 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390467625 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390467625 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390467625 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390467625 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390467625 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390467625 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390467625 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390467625 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390467625 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390467625 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390467625 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390467625 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390467625 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390467625 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390467625 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390467625 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390467625 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390467625 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390467625 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390467625 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390467625 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390467625 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390467625 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390467625 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390467625 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390467625 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390467625 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390467625 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390467625 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390467625 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390467625 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390467625 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390467625 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390467625 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390467625 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390467625 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390467625 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390467625 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390467625 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390467625 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390467625 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390467625 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390467625 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390467625 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390467625 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390467625 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390467625 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390467625 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390467625 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390467625 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390467625 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390467625 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390467625 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390467625 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390467625 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390467625 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390467625 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390467625 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390467625 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390467625 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390467625 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390467625 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390467625 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390467625 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390467625 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390467625 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390467625 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390467625 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390467625 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390467625 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390467625 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390467625 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390467625 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390467625 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390467625 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390467625 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390467625 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390467625 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390467625 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390467625 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390467625 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390467625 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390467625 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390467625 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390467625 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390467625 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390467625 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390467625 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390467625 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390467625 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390467625 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390467625 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390467625 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390467625 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390467625 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390467625 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390467625 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390467625 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390467625 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390467625 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390467625 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390467625 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390467625 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390467625 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390467625 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390467625 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390467625 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390467625 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390467625 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390467625 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390467625 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390467625 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390467625 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390467625 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390467625 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390467625 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390467625 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390467625 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390467625 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390467625 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390467625 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390467625 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390467625 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390467625 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390467625 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390467625 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390467625 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390467625 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390467625 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390467625 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390467625 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390467625 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390467625 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390467625 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390467625 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 390467625 ≤ n) (h2 : n < 390647482) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
